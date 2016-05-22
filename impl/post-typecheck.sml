structure PostTypeCheck = struct
open PreTypeCheck
       
fun str_vce vce =
    case vce of
        ForallVC (name, _) => sprintf "(forall $ "  [name]
      | ImplyVC p => "(imply prop "
      | PropVC _ => "prop"
      | AdmitVC _ => "admit"
      | AnchorVC _ => "anchor"
      | OpenVC => "("
      | CloseVC => ")"

structure N = NoUVarExpr

exception ErrorEmpty
exception ErrorClose of vc_entry list

datatype formula =
         ForallF of string * bsort * formula list
         | ImplyF of prop * formula list
         | AndF of formula list
         | AnchorF of anchor
         | PropF of prop * region
         | AdmitF of prop * region

fun str_f ctx f =
    case f of
        ForallF (name, bsort, fs) =>
        sprintf "(forall ($ : $) ($))" [name, str_bs bsort, str_fs (name :: ctx) fs]
      | ImplyF (p, fs) =>
        sprintf "($ => ($))" [str_p ctx p, str_fs ctx fs]
      | AndF fs =>
        sprintf "($)" [str_fs ctx fs]
      | AnchorF anchor =>
        (case !anchor of
             Fresh uname =>
             sprintf "(anchor $)" [str_uname_i uname]
           | Refined _ => ""
        )
      | PropF (p, _) => str_p ctx p
      | AdmitF (p, _) => sprintf "(admit $)" [str_p ctx p]

and str_fs ctx fs = (join " " o map (str_f ctx)) fs

fun consume_close (s : vc_entry list) : vc_entry list =
    case s of
        CloseVC :: s => s
      | _ => raise Impossible "consume_close ()"

fun get_formula s =
    case s of
        [] => raise ErrorEmpty
      | vce :: s =>
        case vce of
            ForallVC (name, sort) =>
            let
              val (fs, s) = get_formulas s
              val s = consume_close s
              val f = 
                  case sort of
                      Basic (bsort, _) =>
                      ForallF (name, bsort, fs)
                    | Subset ((bsort, _), BindI (_, p), _) =>
                      ForallF (name, bsort, [ImplyF (p, fs)])
                    | UVarS _ => raise Impossible "get_formula (): sort in ForallVC shouldn't be UVarS"
            in
              (f, s)
            end
          | ImplyVC p =>
            let
              val (fs, s) = get_formulas s
              val s = consume_close s
            in
              (ImplyF (p, fs), s)
            end
          | OpenVC =>
            let
              val (fs, s) = get_formulas s
              val s = consume_close s
            in
              (AndF fs, s)
            end
          | AnchorVC anchor => (AnchorF anchor, s)
          | PropVC (p, r) => (PropF (p, r), s)
          | AdmitVC (p, r) => (AdmitF (p, r), s)
          | CloseVC => raise ErrorClose s

and get_formulas (s : vc_entry list) =
    let
      val (f, s) = get_formula s
      val (fs, s) = get_formulas s
    in
      (f :: fs, s)
    end
    handle ErrorEmpty => ([], [])
         | ErrorClose s => ([], CloseVC :: s)

fun get_admits f =
    case f of
        AdmitF (_, r) => ([f], PropF (True r, r))
      | PropF _ => ([], f)
      | AnchorF _ => ([], f) (* drop anchors in admits *)
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
         ForallF2 of string * bsort * formula2
         | BinConnF2 of bin_conn * formula2 * formula2
         | AnchorF2 of anchor * formula2
         | PropF2 of prop * region

fun str_f2 ctx f =
    case f of
        ForallF2 (name, bsort, f) =>
        sprintf "(forall ($ : $) ($))" [name, str_bs bsort, str_f2 (name :: ctx) f]
      | BinConnF2 (opr, f1, f2) =>
        sprintf "($ $ $)" [str_f2 ctx f1, str_bin_conn opr, str_f2 ctx f2]
      | AnchorF2 (anchor, f) =>
        let
          val f = str_f2 ctx f
        in
          case !anchor of
              Fresh uname =>
              sprintf "(anchor $ $)" [str_uname_i uname, f]
            | Refined _ => f
        end
      | PropF2 (p, _) => str_p ctx p

fun f_to_f2 f =
    case f of
        ForallF (name, bs, fs) => ForallF2 (name, bs, fs_to_f2 fs)
      | ImplyF (p, fs) => BinConnF2 (Imply, PropF2 (p, get_region_p p), fs_to_f2 fs)
      | AndF fs => fs_to_f2 fs
      | PropF p => PropF2 p
      | AdmitF p => PropF2 p (* drop admit info *)
      (* | AnchorF anchor => AnchorF2 anchor *)
      | AnchorF _ => raise Impossible "f_to_f2 (): shouldn't be AnchorF"

and fs_to_f2 fs =
    case fs of
        [] => PropF2 (True dummy, dummy)
      | f :: fs =>
        case f of
            AnchorF anchor =>
            let
              val f = fs_to_f2 fs
            in
              case !anchor of
                  Fresh _ => AnchorF2 (anchor, f)
                | Refined _ => f
            end
          | _ => BinConnF2 (And, f_to_f2 f, fs_to_f2 fs)

(* The movement of uvars is constrained only by scope (not by [vce]'s parantheses, so some times a uvar can appear before its anchor (but won't go so far as to up one scope layer). We need to bring some anchors forward to cover their uvars.) *)
                           
fun fv_i i =
    case update_i i of
        VarI _ => []
      | ConstIT _ => []
      | ConstIN _ => []
      | UnOpI (_, i, _) => fv_i i
      | DivI (i, _) => fv_i i
      | ExpI (i, _) => fv_i i
      | BinOpI (_, i1, i2) => fv_i i1 @ fv_i i2
      | Ite (i1, i2, i3, _) => fv_i i1 @ fv_i i2 @ fv_i i3
      | TrueI _ => []
      | FalseI _ => []
      | TTI _ => []
      | TimeAbs (_, i, _) => fv_i i
      | AdmitI _ => []
      | UVarI ((_, uref), _) => [uref]
                                  
fun fv_p p =
    case p of
        True _ => []
      | False _ => []
      | BinConn (_, p1, p2) => fv_p p1 @ fv_p p2
      | Not (p, _) => fv_p p
      | BinPred (_, i1, i2) => fv_i i1 @ fv_i i2
      | Quan (_, _, _, p, _) => fv_p p 
                                     
fun fv_f2 f =
    case f of
        ForallF2 (name, bs, f) => fv_f2 f
      | BinConnF2 (_, f1, f2) => fv_f2 f1 @ fv_f2 f2
      | PropF2 (p, r) => fv_p p
      | AnchorF2 (uref, f) => uref :: fv_f2 f

fun intersection eq a b = List.filter (fn x => mem eq x b) a
                                      
fun add_anchors urefs f =
    foldl AnchorF2 f $ dedup op= urefs

fun bring_forward_anchor f =
    case f of
        BinConnF2 (opr, f1, f2) =>
        let
          val (f1, fv1) = bring_forward_anchor f1
          val (f2, fv2) = bring_forward_anchor f2
          val f = BinConnF2 (opr, f1, f2)
          val f = add_anchors (intersection op= fv1 fv2) f
        in
          (f, fv1 @ fv2)
        end
      | AnchorF2 (uref, f) =>
        (* AnchorF2 is also seen as an appearance of a uvar *)
        let
          val (f, fv) =  bring_forward_anchor f
        in
          (AnchorF2 (uref, f), uref :: fv)
        end
      | ForallF2 (name, bs, f) =>
        let
          val (f, fv) = bring_forward_anchor f
        in
          (ForallF2 (name, bs, f), fv) 
        end
      | PropF2 (p, r) =>
        let
          val fv = fv_p p
        in
          (add_anchors fv $ PropF2 (p, r), fv)
        end

fun trim_anchors covered f =
    case f of
        AnchorF2 (uref, f) =>
        if mem op= uref covered then
          trim_anchors covered f
        else
          AnchorF2 (uref, trim_anchors (uref :: covered) f)
      | BinConnF2 (opr, f1, f2) =>
        BinConnF2 (opr, trim_anchors covered f1, trim_anchors covered f2)
      | ForallF2 (name, bs, f) =>
        ForallF2 (name, bs, trim_anchors covered f)
      | PropF2 (p, r) =>
        PropF2 (p, r)

(*
  and bring_forward_anchor_fs fs =
      let
        val fs = map bring_forward_anchor fs
        fun iter (f, (acc, anchors)) =
            case f of
                AnchorF uref =>
                if mem op= uref anchors then
                  (acc, anchors)
                else
                  (f :: acc, uref :: anchors)
              | _ =>
                let
                  val fvs = dangling_uvars f
                  val fvs = diff op= fvs anchors
                  val fvs = dedup op= fvs
                  val fvs = rev fvs
                in
                  (map AnchorF fvs @ (f :: acc), fvs @ anchors)
                end
        val fs = rev $ fst $ foldl iter ([], []) fs
                                
        (* val urefs = dangling_uvars f *)
        (* val urefs = dedup op= urefs *)
        (* val f = bring_forward_anchor f *)
        (* fun hit f = *)
        (*     case f of *)
        (*         AnchorF uref => mem op= uref urefs *)
        (*       | _ => false *)
        (* val fs = bring_forward_anchor_fs fs *)
        (* val fs = f :: fs *)
        (* val fs = List.filter (fn f => not $ hit f) fs *)
        (* val fs = map AnchorF urefs @ fs *)
      in
        fs
      end
*)
               
fun to_exists (uvar_ref, (n, ctx, bsort), p) =
    let
      fun substu_i x v (b : idx) : idx =
	  case b of
              UVarI ((_, y), _) =>
              if y = x then
                VarI (v, dummy)
              else 
                b
	    | VarI a => VarI a
	    | ConstIN n => ConstIN n
	    | ConstIT x => ConstIT x
            | UnOpI (opr, i, r) => UnOpI (opr, substu_i x v i, r)
            | DivI (i1, n2) => DivI (substu_i x v i1, n2)
            | ExpI (i1, n2) => ExpI (substu_i x v i1, n2)
	    | BinOpI (opr, i1, i2) => BinOpI (opr, substu_i x v i1, substu_i x v i2)
            | Ite (i1, i2, i3, r) => Ite (substu_i x v i1, substu_i x v i2, substu_i x v i3, r)
	    | TrueI r => TrueI r
	    | FalseI r => FalseI r
            | TimeAbs (name, i, r) => TimeAbs (name, substu_i x (v + 1) i, r)
            | AdmitI r => AdmitI r
	    | TTI r => TTI r
      fun substu_p x v b =
	  case b of
	      True r => True r
	    | False r => False r
            | Not (p, r) => Not (substu_p x v p, r)
	    | BinConn (opr,p1, p2) => BinConn (opr, substu_p x v p1, substu_p x v p2)
	    | BinPred (opr, i1, i2) => BinPred (opr, substu_i x v i1, substu_i x v i2)
            | Quan (q, bs, (name, r), p, r_all) => Quan (q, bs, (name, r), substu_p x (v + 1) p, r_all)
      (* fun evar_name n = "?" ^ str_int n *)
      fun evar_name n =
          (* if n < 26 then *)
          (*   "" ^ (str o chr) (ord #"a" + n) *)
          (* else *)
          "_x" ^ str_int n
      val r = get_region_p p
      fun notifier i =
          case try_forget (forget_above_i_i 0) i of
              SOME _ =>
              unify_i dummy [] (UVarI (([], uvar_ref), dummy), i)
            | NONE => raise Error (r, ["Inferred existential index can only be closed index"])
      val p =
          (* ToDo: need to shift [i] *)
          Quan (Exists (SOME notifier),
                bsort,
                (evar_name n, dummy), substu_p uvar_ref 0 $ shift_i_p $ update_p p, r)
    in
      p
    end
      
fun f2_to_prop f : prop =
    case f of
        ForallF2 (name, bs, f) =>
        let
          val p = f2_to_prop f
        in
          Quan (Forall, bs, (name, dummy), p, get_region_p p)
        end
      | BinConnF2 (opr, f1, f2) => BinConn(opr, f2_to_prop f1, f2_to_prop f2)
      | PropF2 (p, r) => set_region_p p r
      | AnchorF2 (anchor, f) =>
        let
          val p = f2_to_prop f
        in
          case !anchor of
              Fresh uname => to_exists (anchor, uname, p)
            | Refined _ => p
        end

fun nouvar2uvar_i i =
    let
      fun f i =
          case i of
              N.VarI x => VarI x
            | N.ConstIT c => ConstIT c
            | N.ConstIN c => ConstIN c
            | N.UnOpI (opr, i, r) => UnOpI (opr, f i, r)
            | N.DivI (i1, n2) => DivI (f i1, n2)
            | N.ExpI (i1, n2) => ExpI (f i1, n2)
            | N.BinOpI (opr, i1, i2) => BinOpI (opr, f i1, f i2)
            | N.Ite (i1, i2, i3, r) => Ite (f i1, f i2, f i3, r)
            | N.TrueI r => TrueI r
            | N.FalseI r => FalseI r
            | N.TTI r => TTI r
            | N.TimeAbs (name, i, r) => TimeAbs (name, f i, r)
            | N.AdmitI r => AdmitI r
            | N.UVarI (u, _) => exfalso u
    in
      f i
    end

fun no_uvar_i i =
    let
      val i = update_i i
      fun impossible i' = Impossible $ sprintf "\n$\nno_uvar_i (): $ shouldn't be UVarI in $" [str_region "" (* "examples/rbt.timl" *)"" (get_region_i i'), str_i [] i', str_i [] i]
      fun f i =
          case i of
              VarI x => N.VarI x
            | ConstIT c => N.ConstIT c
            | ConstIN c => N.ConstIN c
            | UnOpI (opr, i, r) => N.UnOpI (opr, f i, r)
            | DivI (i1, n2) => N.DivI (f i1, n2)
            | ExpI (i1, n2) => N.ExpI (f i1, n2)
            | BinOpI (opr, i1, i2) => N.BinOpI (opr, f i1, f i2)
            | Ite (i1, i2, i3, r) => N.Ite (f i1, f i2, f i3, r)
            | TrueI r => N.TrueI r
            | FalseI r => N.FalseI r
            | TTI r => N.TTI r
            | TimeAbs (name, i, r) =>
              N.TimeAbs (name, f i, r)
            | AdmitI r =>
              raise Impossible "no_uvar_i () : shouldn't be AdmitI"
            | UVarI (_, r) =>
              raise impossible i
    in
      f i
    end

fun no_uvar_bsort bs =
    case update_bs bs of
        Base b => N.Base b
      | UVarBS uvar_ref =>
        (unify_bs dummy (bs, Base UnitSort);
         N.Base N.UnitSort)

fun no_uvar_quan q =
    case q of
        Forall => Forall
      | Exists ins => Exists (Option.map (fn ins => fn i => ins $ nouvar2uvar_i i) ins)
                             
fun no_uvar_p p =
    case p of
        True r => N.True r
      | False r => N.False r
      | BinConn (opr, p1, p2) => N.BinConn (opr, no_uvar_p p1, no_uvar_p p2)
      | BinPred (opr, i1, i2) => N.BinPred (opr, no_uvar_i i1, no_uvar_i i2)
      | Not (p, r) => N.Not (no_uvar_p p, r)
      | Quan (q, bs, name, p, r) => N.Quan (no_uvar_quan q, no_uvar_bsort bs, name, no_uvar_p p, r)

fun vces_to_vcs vces =
    let
      open VC
      (* val () = println "VCEs: " *)
      (* val () = println $ join " " $ map str_vce vces *)
      val (fs, vces) = get_formulas vces
      val () = case vces of
                   [] => ()
                 | _ => raise Impossible "to_vcs (): remaining after get_formulas"
      val fs = unpackage_fs fs
      val (admits, fs) = get_admits_fs fs
      fun fs_to_prop fs =
          let
            (* val () = println "Formulas: " *)
            (* val () = app println $ map (str_f []) fs *)
            val f = fs_to_f2 fs
            (* val () = println "Formula2: " *)
            (* val () = println $ str_f2 [] f *)
            val f = fst $ bring_forward_anchor f
            (* val () = println "Formula2 after bring_forward_anchor (): " *)
            (* val () = println $ str_f2 [] f *)
            val f = trim_anchors [] f
            (* val () = println "Formulas after trim_anchors (): " *)
            (* val () = println $ str_f2 [] f *)
            val p = f2_to_prop f
            (* val () = println "Props: " *)
            (* val () = println $ Expr.str_p [] p *)
            val p = Expr.Simp.simp_p p
          in
            p
          end
      val p = fs_to_prop fs
      val p = no_uvar_p p
      (* val () = println "NoUVar Props: " *)
      (* val () = println $ str_p [] p *)
      val p = simp_p p
      (* val () = println "NoUVar Props after simp_p(): " *)
      (* val () = println $ str_p [] p *)
      val p = uniquefy [] p
      val admits = map (fs_to_prop o singleton) admits
      val vcs = prop2vcs p
      val vcs = concatMap simp_vc_vcs vcs
      (* val () = app println $ concatMap (str_vc false "") vcs *)
      val vcs = map VC.simp_vc vcs
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

type typing_info = decl list * context * idx list * context

fun str_typing_info ctx_old ((decls, ctxd, ds, ctx) : typing_info) =
    let
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx_old
      val idx_lines =
          List.concat $ rev $ fst $ foldr (fn ((name, s), (acc, sctxn)) => ([sprintf "$ : $" [name, str_s sctxn s], ""] :: acc, name :: sctxn)) ([], sctxn) $ #1 $ ctxd
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
      val type_lines =
          (concatMap (fn (name, k) => [sprintf "$ :: $" [name, str_k sctxn k], ""]) o rev o #2) ctxd
      val expr_lines =
          (concatMap (fn (name, t) => [sprintf "$ : $" [name, str_t (sctxn, kctxn) t], ""]) o rev o #4) ctxd
      val time_lines =
          "Times:" :: "" ::
          (concatMap (fn d => [sprintf "|> $" [str_i sctxn d], ""])) ds
      val s = join_lines
                (
                  idx_lines
                  @ type_lines
                  @ expr_lines
                (* @ time_lines  *)
                )
    in
      s
    end
      
fun vcgen_expr ctx e =
    runWriter (fn () => get_mtype (ctx, e)) ()
	      
fun vcgen_expr_opt ctx e =
    runError (fn () => vcgen_expr ctx e) ()
	     
fun vcgen_decls ctx decls =
    let
      fun m () =
          let
            val ctx_old = ctx
            val (decls, ctxd, nps, ds, ctx) = check_decls (ctx, decls)
            val () = close_vcs nps
            val () = close_ctx ctxd
            val ret = (decls, ctxd, ds, ctx)
            val () = print $ str_typing_info ctx_old ret
          in
            ret
          end
    in
      runWriter m ()
    end
      
fun vcgen_expr_opt ctx decls =
    runError (fn () => vcgen_decls ctx decls) ()
	     
structure S = TrivialSolver

(* exception Unimpl *)

fun typecheck_expr (ctx as (sctx, kctx, cctx, tctx) : context) e =
    let 
      val ((e, t, d), (vcs, admits)) = vcgen_expr ctx e
      val t = update_mt t
      val t = simp_mt t
      val d = update_i d
      val d = simp_i d
      val vcs = S.simp_and_solve_vcs vcs
    in
      ((e, t, d), (vcs, admits))
    end

fun typecheck_expr_opt ctx e =
    runError (fn () => typecheck_expr ctx e) ()

type tc_result = typing_info * (VC.vc list * prop list)

fun typecheck_decls (ctx as (sctx, kctx, cctx, tctx) : context) decls =
    let 
      val ((decls, ctxd, ds, ctx), (vcs, admits)) = vcgen_decls ctx decls
      val ctxd = (upd4 o map o mapSnd) (simp_t o update_t) ctxd
      val ds = rev ds
      val ds = map update_i ds
      val ds = map simp_i ds
      val vcs = S.simp_and_solve_vcs vcs
    in
      ((decls, ctxd, ds, ctx), (vcs, admits))
    end

fun typecheck_decls_opt ctx e =
    runError (fn () => typecheck_decls ctx e) ()

end
	                    
structure TypeCheck = struct
open PreTypeCheck
open PostTypeCheck
end
