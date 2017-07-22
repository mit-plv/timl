structure PostTypeCheck = struct
open DoTypeCheck
       
infixr 0 $
         
fun str_vce vce =
  case vce of
      VcForall (name, ft) =>
      let
        val ft = case ft of
                     FtSorting _ => "s"
                   | FtModule _ => "m"
      in
        sprintf "(forall_$ $ "  [ft, name]
      end
    | ImplyVC p => "(imply prop "
    | PropVC _ => "prop"
    | AdmitVC _ => "admit"
    | OpenParen => "("
    | CloseParen => ")"

exception ErrorEmpty
exception ErrorClose of vc_entry list

(* formulas transcribed from [vce]s *)
datatype formula =
         ForallF of string * bsort forall_type * formula list
         | ImplyF of prop * formula list
         | AndF of formula list
         | PropF of prop * region
         | AdmitF of prop * region

fun str_ft ft =
  case ft of
      FtSorting bs => str_bs bs
    | FtModule _ => "module"
                      
fun str_f gctx ctx f =
  case f of
      ForallF (name, ft, fs) =>
      let
        val (gctx, ctx) =
            case ft of
                FtSorting _ => (gctx, name :: ctx)
              | FtModule sctx => (curry insert' (name, (sctx_names sctx, [], [], [])) gctx, ctx)
      in
        sprintf "(forall ($ : $) ($))" [name, str_ft ft, str_fs gctx ctx fs]
      end
    | ImplyF (p, fs) =>
      sprintf "($ => ($))" [str_p gctx ctx p, str_fs gctx ctx fs]
    | AndF fs =>
      sprintf "($)" [str_fs gctx ctx fs]
    | PropF (p, _) => str_p empty ctx p
    | AdmitF (p, _) => sprintf "(admit $)" [str_p gctx ctx p]

and str_fs gctx ctx fs = (join " " o map (str_f gctx ctx)) fs

fun consume_close (s : vc_entry list) : vc_entry list =
  case s of
      CloseParen :: s => s
    | _ => raise Impossible "consume_close ()"

fun get_bsort_UVarS s =
  let
    val s = update_s s
  in
    case s of
        UVarS (a, r) =>
        let
          val def = Base UnitSort
          val () = is_eqv_sort dummy empty [] (s, Basic (def, r))
        in
          def
        end
      | _ => get_base (fn _ => raise Impossible "get_bsort_UVarS()/get_base()") s
  end
                    
fun get_base_and_refinement s =
  case s of
      Subset ((bsort, _), Bind (_, p), _) =>
      (bsort, SOME p)
    | Basic (bsort, _) =>
      (bsort, NONE)
    | _ => (get_base refine_UVarS_to_Basic s, NONE)
             
fun get_formula s(*vce sequence*) =
  case s of
      [] => raise ErrorEmpty
    | vce :: s =>
      case vce of
          VcForall (name, ft) =>
          let
            val (fs, s) = get_formulas s
            val s = consume_close s
            val (ft, fs) = 
                case ft of
                    FtModule m =>
                    (FtModule m, fs)
                  | FtSorting s =>
                    let
                      val s = normalize_s s
                      val (b, p) = get_base_and_refinement s
                    in
                      case p of
                          SOME p =>
                          (FtSorting b, [ImplyF (p, fs)])
                        | NONE =>
                          (FtSorting b, fs)
                    end
          in
            (ForallF (name, ft, fs), s)
          end
        | ImplyVC p =>
          let
            val (fs, s) = get_formulas s
            val s = consume_close s
          in
            (ImplyF (p, fs), s)
          end
        | OpenParen =>
          let
            val (fs, s) = get_formulas s
            val s = consume_close s
          in
            (AndF fs, s)
          end
        | CloseParen => raise ErrorClose s
        | PropVC (p, r) => (PropF (p, r), s)
        | AdmitVC (p, r) => (AdmitF (p, r), s)

and get_formulas (s : vc_entry list) =
    let
      val (f, s) = get_formula s
      val (fs, s) = get_formulas s
    in
      (f :: fs, s)
    end
    handle ErrorEmpty => ([], [])
         | ErrorClose s => ([], CloseParen :: s)

fun get_admits f =
  case f of
      AdmitF (_, r) => ([f], PropF (True r, r))
    | PropF _ => ([], f)
    | AndF fs => mapSnd AndF $ get_admits_fs fs
    | ImplyF (p, fs) =>
      let
        fun wrap fs = ImplyF (p, fs)
      in
        mapPair (map (wrap o singleton), wrap) $ get_admits_fs fs
      end
    | ForallF (name, bs, fs) =>
      let
        fun wrap fs = ForallF (name, bs, fs)
      in
        mapPair (map (wrap o singleton), wrap) $ get_admits_fs fs
      end
        
and get_admits_fs fs =
    case fs of
        [] => ([], [])
      | f :: fs =>
        let
          val (admits1, f) = get_admits f
          val (admits2, fs) = get_admits_fs fs
        in
          (admits1 @ admits2, f :: fs)
        end

(* another formulation of formulas that won't talk about lists *)
datatype formula2 =
         ForallF2 of string * bsort forall_type * formula2
         | BinConnF2 of bin_conn * formula2 * formula2
         | PropF2 of prop * region

fun str_f2 gctx ctx f =
  case f of
      ForallF2 (name, ft, f) =>
      let
        val (gctx, ctx) =
            case ft of
                FtSorting _ => (gctx, name :: ctx)
              | FtModule sctx => (Gctx.add (name, (sctx_names sctx, [], [], [])) gctx, ctx)
      in
        sprintf "(forall ($ : $) ($))" [name, str_ft ft, str_f2 gctx ctx f]
      end
    | BinConnF2 (opr, f1, f2) =>
      sprintf "($ $ $)" [str_f2 gctx ctx f1, str_bin_conn opr, str_f2 gctx ctx f2]
    | PropF2 (p, _) => str_p gctx ctx p

fun f_to_f2 f =
  case f of
      ForallF (name, ft, fs) => ForallF2 (name, ft, fs_to_f2 fs)
    | ImplyF (p, fs) => BinConnF2 (Imply, PropF2 (p, get_region_p p), fs_to_f2 fs)
    | AndF fs => fs_to_f2 fs
    | PropF p => PropF2 p
    | AdmitF p => PropF2 p (* drop admit info *)

and fs_to_f2 fs =
    case fs of
        [] => PropF2 (True dummy, dummy)
      | f :: fs => BinConnF2 (And, f_to_f2 f, fs_to_f2 fs)

(* remove all forall-module *)
                           
fun remove_m_ibind f n (Bind (name, b)) =
  Bind (name, f (n + 1) b)

fun remove_m_i m n i =
  let
    val remove_m_i = remove_m_i m
  in
    case i of
        VarI id =>
        (case id of
             ID _ => i (* forall-module must all be on the outermost *)
           | QID ((m', mr), (x, r)) =>
             if m' = m then
               VarI (ID (x + n, r))
             else
               VarI $ QID ((m', mr), (x, r))
        )
      | IConst _ => i
      | UnOpI (opr, i, r) => UnOpI (opr, remove_m_i n i, r)
      | BinOpI (opr, i1, i2) => BinOpI (opr, remove_m_i n i1, remove_m_i n i2)
      | Ite (i1, i2, i3, r) => Ite (remove_m_i n i1, remove_m_i n i2, remove_m_i n i3, r)
      | IAbs (bs, bind, r) => IAbs (bs, remove_m_ibind remove_m_i n bind, r)
      | UVarI _ => i (* forall-module must all be on the outermost *)
  end
                   
fun remove_m_p m n p =
  let
    val remove_m_p = remove_m_p m
  in
    case p of
        BinConn (opr, p1, p2) => BinConn (opr, remove_m_p n p1, remove_m_p n p2)
      | Not (p, r) => Not (remove_m_p n p, r)
      | BinPred (opr, i1, i2) => BinPred (opr, remove_m_i m n i1, remove_m_i m n i2)
      | Quan (q, bs, bind, r) => Quan (q, bs, remove_m_ibind remove_m_p n bind, r)
      | PTrueFalse _ => p
  end
                   
fun remove_m_f m n f =
  let
    val remove_m_f = remove_m_f m
  in
    case f of
        ForallF2 (name, ft, f) =>
        (case ft of
             FtModule _ => raise Impossible "remove_m(): FtModule"
           | FtSorting bs => ForallF2 (name, ft, remove_m_f (n + 1) f)
        )
      | BinConnF2 (opr, f1, f2) => BinConnF2 (opr, remove_m_f n f1, remove_m_f n f2)
      | PropF2 (p, r) => PropF2 (remove_m_p m n p, r)
  end
                              
fun unpackage_f2 f =
  case f of
      ForallF2 (name, ft, f) =>
      let
        val f = unpackage_f2 f
      in
        case ft of
            FtModule m =>
            let
              val mod_name = name
              val f = remove_m_f mod_name 0 f
              fun iter ((name, s), f) =
                let
                  val (b, p) = get_base_and_refinement s
                  val f =
                      case p of
                          SOME p => BinConnF2 (Imply, PropF2 (p, get_region_p p), f)
                        | NONE => f
                in
                  ForallF2 (mod_name ^ "_" ^ name, FtSorting b, f)
                end
              val f = foldl iter f m
            in
              f
            end
          | FtSorting bs =>
            ForallF2 (name, ft, f)  
      end
    | BinConnF2 (opr, f1, f2) =>
      BinConnF2 (opr, unpackage_f2 f1, unpackage_f2 f2)
    | PropF2 _ => f
                    
fun collect_uvar_i_f2 f =
  case f of
      ForallF2 (name, bs, f) => collect_uvar_i_f2 f
    | BinConnF2 (_, f1, f2) => collect_uvar_i_f2 f1 @ collect_uvar_i_f2 f2
    | PropF2 (p, r) => collect_uvar_i_p p

fun f2_to_prop f : prop =
  case f of
      ForallF2 (name, ft, f) =>
      let
        val bs = case ft of
                     FtSorting bs => bs
                   | FtModule _ => raise Impossible "f2_to_prop(): FtModule"
        val p = f2_to_prop f
      in
        Quan (Forall, bs, Bind ((name, dummy), p), get_region_p p)
      end
    | BinConnF2 (opr, f1, f2) => BinConn(opr, f2_to_prop f1, f2_to_prop f2)
    | PropF2 (p, r) => set_region_p p r

fun vces_to_vcs vces =
  let
    open VC
    (* val () = println "VCEs: " *)
    (* val () = println $ join " " $ map str_vce vces *)
    val (fs, vces) = get_formulas vces
    val () = case vces of
                 [] => ()
               | _ => raise Impossible "to_vcs (): remaining after get_formulas"
    (* val () = println "Formulas: " *)
    (* val () = app println $ map (str_f [] []) fs *)
    val (admits, fs) = get_admits_fs fs
    fun fs_to_prop fs =
      let
        val f = fs_to_f2 fs
        (* val () = println $ "Formula2: \n" ^ str_f2 empty [] f *)
        val f = unpackage_f2 f
        (* val () = println $ "Formula2-after-unpackage: \n" ^ str_f2 empty [] f *)
        val p = f2_to_prop f
        (* val () = println "Props: " *)
        (* val () = println $ Expr.str_p [] [] p *)
        val p = Expr.Simp.simp_p p
      in
        p
      end
    val p = fs_to_prop fs
    val p = simp_p p
    val p = uniquefy [] p
    val admits = map (fs_to_prop o singleton) admits
    (* val admits = map Expr.Simp.simp_p admits *)
    val vcs = prop2vcs p
    val vcs = concatMap simp_vc_vcs vcs
    (* val () = app println $ concatMap (str_vc false "") vcs *)
    val vcs = map VC.simp_vc vcs
    val vcs = TrivialSolver.simp_and_solve_vcs vcs
  in
    (vcs, admits)
  end

fun runWriter m _ =
  let 
    val () = acc := []
    val r = m () 
    val vces = rev (!acc)
    val vcs_admits = vces_to_vcs vces
  in 
    (r, vcs_admits) 
  end

fun typecheck_expr gctx ctx e =
  runWriter (fn () => get_mtype gctx (ctx, e)) ()
	    
fun typecheck_decls gctx ctx decls =
  let
    fun m () =
      let
        val skctxn_old = (sctx_names $ #1 ctx, names $ #2 ctx)
        val (decls, ctxd, nps, ds, ctx) = check_decls gctx (ctx, decls)
        val () = close_n nps
        val () = close_ctx ctxd
                           (* val () = app println $ str_typing_info (gctx_names gctx) skctxn_old (ctxd, ds) *)
      in
        (decls, ctxd, ds, ctx)
      end
  in
    runWriter m ()
  end
    
fun typecheck_top_bind gctx top_bind =
  runWriter (fn () => check_top_bind gctx top_bind) ()
            
fun typecheck_prog gctx prog =
  runWriter (fn () => check_prog gctx prog) ()
            
(* fun runError m _ = *)
(*     OK (m ()) *)
(*     handle *)
(*     Error e => Failed e *)

(* fun typecheck_expr_opt ctx e = *)
(*     runError (fn () => typecheck_expr ctx e) () *)
	    
(* fun typecheck_decls_opt ctx decls = *)
(*     runError (fn () => typecheck_decls ctx decls) () *)
	    
type tc_result = typing_info * (VC.vc list * prop list)
                                 (* exception Unimpl *)

end
