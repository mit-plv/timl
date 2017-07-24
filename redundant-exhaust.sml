(* redundancy and exhaustiveness checking *)
(* all the following cover operations assume that the cover has type t *)

structure RedundantExhaust = struct
open Util
open Equal
open Equal
open Expr
open Normalize

infixr 0 $
         
datatype cover =
         TrueC
         | FalseC
         | AndC of cover * cover
         | OrC of cover * cover
         | ConstrC of var * cover
         | PairC of cover * cover
         | TTC

fun combine_covers covers = foldl' (swap OrC) FalseC covers

datatype habitant =
         TrueH
         | ConstrH of var * habitant
         | PairH of habitant * habitant
         | TTH

fun str_cover gctx cctx c =
  let
    val str_cover = str_cover gctx
  in
    case c of
        TrueC => "_"
      | FalseC => "False"
      | AndC (c1, c2) => sprintf "($ /\\ $)" [str_cover cctx c1, str_cover cctx c2]
      | OrC (c1, c2) => sprintf "($ \\/ $)" [str_cover cctx c1, str_cover cctx c2]
      | ConstrC (x, c) => sprintf "($ $)" [str_var #3 gctx cctx x, str_cover cctx c]
      | PairC (c1, c2) => sprintf "($, $)" [str_cover cctx c1, str_cover cctx c2]
      | TTC => "()"
  end

fun str_habitant gctx cctx c =
  let
    val str_habitant = str_habitant gctx
  in
    case c of
        TrueH => "_"
      | ConstrH (x, c) => sprintf "($ $)" [str_var #3 gctx cctx x, str_habitant cctx c]
      | PairH (c1, c2) => sprintf "($, $)" [str_habitant cctx c1, str_habitant cctx c2]
      | TTH => "()"
  end

infixr 3 /\
infixr 2 \/
val op/\ = AndC
val op\/ = OrC

fun impossible s = Impossible $ "cover has the wrong type: " ^ s

fun cover_neg gctx (ctx as (sctx, kctx, cctx)) (t : mtype) c =
  let
    val neg = cover_neg gctx ctx
    (* val t = normalize_mt t *)
    val t = whnf_mt gctx kctx t
  in
    case c of
        TrueC => FalseC
      | FalseC => TrueC
      | AndC (a, b) => neg t a \/ neg t b
      | OrC (a, b) => neg t a /\ neg t b
      | TTC => FalseC
      | PairC (c1, c2) =>
        (case t of
             Prod (t1, t2) =>
             PairC (neg t1 c1, c2) \/
             PairC (c1, neg t2 c2) \/
             PairC (neg t1 c1, neg t2 c2)
           | _ => raise impossible "cover_neg()/PairC")
      | c_all as ConstrC (x, c) =>
	(case is_AppV t of
	     SOME (family, ts, _) =>
	     let
               val all = map fst $ get_family_siblings gctx cctx x
               (* val () = println $ sprintf "Family of $: $" [str_long_id #3 (gctx_names gctx) (names cctx) x, str_ls (str_long_id #3 (gctx_names gctx) (names cctx)) all] *)
	       val others = diff eq_var all [x]
               (* val () = println $ sprintf "Family siblings of $: $" [str_long_id #3 (gctx_names gctx) (names cctx) x, str_ls (str_long_id #3 (gctx_names gctx) (names cctx)) others] *)
               val (_, tbinds) = snd $ fetch_constr gctx (cctx, x)
               val (_, ibinds) = unfold_binds tbinds
               val (_, (t', _)) = unfold_binds ibinds
	       val t' = subst_ts_mt ts t'
               val covers = ConstrC (x, neg t' c) :: map (fn y => ConstrC (y, TrueC)) others
	     in
               combine_covers covers
	     end
	   | NONE => raise impossible $ sprintf "cover_neg()/ConstrC:  cover is $ but type is " [str_cover (gctx_names gctx) (names cctx) c_all, str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t])
  end

(* fun cover_imply cctx t (a, b) : cover = *)
(*     cover_neg cctx t a \/ b *)

(* find habitant
       deep: when turned on, [find_hab] try to find a [ConstrH] for a datatype when constraints are empty (treat empty datatype as uninhabited); otherwise only return [TrueH] in such case (treat empty datatype as inhabited) *)
fun find_hab deep gctx (ctx as (sctx, kctx, cctx)) (t : mtype) cs =
  let
    (* val () = println "find_hab() begin" *)
    (* fun sum ls = foldl' op+ 0 ls *)
    (* fun cover_size c = *)
    (*     case c of *)
    (*         TrueC => 1 *)
    (*       | FalseC => 1 *)
    (*       | AndC (c1, c2) => cover_size c1 + 1 + cover_size c2 *)
    (*       | OrC (c1, c2) => cover_size c1 + 1 + cover_size c2 *)
    (*       | ConstrC (x, c) => 1 + cover_size c *)
    (*       | PairC (c1, c2) => cover_size c1 + 1 + cover_size c2 *)
    (*       | TTC => 1 *)
    (* fun covers_size cs = sum $ map cover_size cs *)
    (* fun mt_size t = *)
    (*     case whnf_mt t of *)
    (*         Prod (t1, t2) => mt_size t1 + 1 + mt_size t2 *)
    (*       | _ => 1 *)
    fun collect_AndC acc c =
      case c of
          AndC (c1, c2) =>
          let
            val acc = collect_AndC acc c1
            val acc = collect_AndC acc c2
          in
            acc
          end
        | TrueC => acc
        | _ => c :: acc
    val collect_AndC = fn c => collect_AndC [] c
    (* fun combine_AndC cs = foldl' AndC TrueC cs *)
    local
      exception IsFalse
      fun runUntilFalse m =
        m () handle IsFalse => FalseC
      fun simp c =
        case c of
            AndC (c1, c2) =>
            (case (simp c1, simp c2) of
                 (TrueC, c) => c
               | (c, TrueC) => c
               | (c1, c2) => AndC (c1, c2)
            )
          | OrC (c1, c2) =>
            (case (runUntilFalse (fn () => simp c1), runUntilFalse (fn () => simp c2)) of
                 (FalseC, FalseC) => raise IsFalse
               | (FalseC, c) => c
               | (c, FalseC) => c
               | (c1, c2) => OrC (c1, c2)
            )
          | TTC => TTC
          | PairC (c1, c2) => PairC (simp c1, simp c2)
          | ConstrC (x, c) => ConstrC (x, simp c)
          | TrueC => TrueC
          | FalseC => raise IsFalse
    in
    fun simp_cover cover =
      runUntilFalse (fn () => simp cover)
    fun simp_covers cs =
      let
        fun main () = List.filter (fn c => case c of TrueC => false | _ => true) $ map simp cs
      in
        main () handle IsFalse => [FalseC]
      end
    end              
    (* val () = println $ "before simp_cover(): size=" ^ (str_int $ covers_size cs) *)
    (* val c = combine_AndC cs *)
    (* val c = simp_cover c *)
    (* val cs = collect_AndC c *)
    val cs = concatMap collect_AndC $ simp_covers $ cs
    (* val () = println $ "after simp_cover(): size=" ^ (str_int $ covers_size cs) *)
                       
    exception Incon of string
    (* the last argument is for checking that recursive calls to [loop] are always on smaller arguments, to ensure termination *)
    fun loop (t : mtype, cs_all, ()) : habitant =
      let
        (* val () = println (sprintf "find_hab on type $" [str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t]) *)
        (* val t = normalize_mt t *)
        val t = whnf_mt gctx kctx t
        (* val size = covers_size cs_all *)
        (* fun check_size (t', cs) = *)
        (*     let *)
        (*       val smaller = covers_size cs *)
        (*       val () = if smaller < size orelse smaller = size andalso mt_size t' < mt_size t then () *)
        (*                else raise Impossible "not smaller size" *)
        (*     in *)
        (*       (t', cs, ()) *)
        (*     end *)
        fun check_size (t', cs) = (t', cs, ())
                                    (* val cs_all = simp_covers $ concatMap collect_AndC cs_all *)
                                    (* val () = print $ sprintf "$\t\t$\n" [str_int $ covers_size cs_all, str_int $ length cs_all] *)
                                    (* fun has_false c = *)
                                    (*     case c of *)
                                    (*         FalseC => true *)
                                    (*       | TrueC => false *)
                                    (*       | TTC => false *)
                                    (*       | PairC (c1, c2) => has_false c1 orelse has_false c2 *)
                                    (*       | AndC (c1, c2) => has_false c1 orelse has_false c2 *)
                                    (*       | OrC (c1, c2) => has_false c1 andalso has_false c2 *)
                                    (*       | ConstrC (_, c) => has_false c *)
                                    (* val () = app (fn c' => if has_false c' then ((* println "has false";  *)raise Incon "has false") else ()) cs_all *)
                                    (* fun split3 i l = (List.nth (l, i), take i l, drop (i + 1) l) *)
                                    (* fun i_tl_to_hd c i cs = to_hd (i + 1) (c :: cs) *)
      in
        case cs_all of
            [] =>
            if not deep then
              TrueH
            else
              let
                (* val () = println (sprintf "Empty constraints now. Now try to find any inhabitant of type $" [str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t]) *)
                val ret =
                    case is_AppV t of
                        SOME (family, _, _) =>
                        if fetch_is_datatype gctx (kctx, family) then
	                  let
                            fun do_fetch_constrs (cctx, family) =
                              rev $ map snd $ mapPartialWithIdx (fn (n, (_, c)) => if eq_var (get_family c, ID family) then SOME (ID (n, snd family)) else NONE) cctx
                            fun fetch_constrs a = generic_fetch (package0_list (package_long_id 0)) do_fetch_constrs #3 a
                            val all = fetch_constrs gctx (cctx, family)
                            (* val () = println $ sprintf "Constructors of $: $" [str_long_id #2 (gctx_names gctx) (names kctx) family, str_ls (str_long_id #3 (gctx_names gctx) (names cctx)) all] *)
                          in
                            case all of x :: _ => ConstrH (x, TrueH) | [] => raise Incon "empty datatype"
                          end
                        else TrueH (* an abstract type is treated as an inhabited type *)
                      | NONE =>
                        (case t of
                             Unit _ => TTH
                           | Prod (t1, t2) => PairH (loop $ check_size (t1, []), loop $ check_size (t2, []))
                           | _ => TrueH
                        )
                (* val () = println "Found" *)
              in
                ret
              end
          | c :: cs =>
            let
              (* val () = println $ sprintf "try to satisfy $ for type $" [(join ", " o map (str_cover (gctx_names gctx) (names cctx))) (c :: cs), str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t] *)
              (* val () = println $ sprintf "try to satisfy $" [str_cover (gctx_names gctx) (names cctx) c] *)
              fun conflict_half a b =
                case (a, b) of
                    (PairC _, ConstrC _) => true
                  | (PairC _, TTC) => true
                  | (ConstrC _, TTC) => true
                  | _ => false
              fun conflict a b = conflict_half a b orelse conflict_half b a
              val () = app (fn c' => if conflict c c' then ((* println "conflict";  *)raise Incon "conflict") else ()) cs
              (* firstly try to test for concrete cases *)
              fun default () = inr (c, cs, t)
              val result =
                  case c of
                      TTC =>
                      (case t of
                           Unit _ =>
                           (case allSome (fn c => case c of TTC => SOME () | _ => NONE) cs of
                                OK _ => inl TTH
                              | Failed (i, dissident) =>
                                if conflict c dissident then
                                  raise Incon "conflicts on tt"
                                else
                                  inr (dissident, c :: remove i cs, t)
                           )
                         | _ => default ()
                      )
                    | PairC (c1, c2) =>
                      (case t of
                           Prod (t1, t2) =>
                           (case allSome (fn c => case c of PairC p => SOME p | _ => NONE ) cs of
                                OK cs =>
                                let
                                  val (cs1, cs2) = unzip cs
                                  val c1 = loop $ check_size (t1, c1 :: cs1)
                                  val c2 = loop $ check_size (t2, c2 :: cs2)
                                in
                                  inl $ PairH (c1, c2)
                                end
                              | Failed (i, dissident) =>
                                if conflict c dissident then
                                  raise Incon "conflicts on pair"
                                else
                                  inr (dissident, c :: remove i cs, t)
                           )
                         | _ => default ()
                      )
                    | ConstrC (x, c') =>
                      (case is_AppV t of
                           SOME (_, ts, _) =>
                           let
                             fun eq_constr_long_id ((name, family), (name', family')) =
                               let
                                 (* val gctxn = gctx_names gctx *)
                                 (* val ctxn = (sctx_names sctx, names kctx) *)
                                 (* val () = println $ sprintf "comparing ($, $, $) and ($, $, $)" [str_raw_long_id x, str_long_id #3 gctxn (names cctx) x, str_mt gctxn ctxn family, str_raw_long_id x', str_long_id #3 gctxn (names cctx) x', str_mt gctxn ctxn family'] *)
                                 val ret = name = name' andalso eq_mt family family'
                                 (* val () = println $ "result: " ^ str_bool ret *)
                               in
                                 ret
                               end
                             val (name, (family, _)) = fetch_constr gctx (cctx, x)
                             val family = normalize_mt gctx kctx (MtVar family)
                             fun same_constr c =
                               case c of
                                   ConstrC (y, c) =>
                                   let
                                     val (name', (family', _)) = fetch_constr gctx (cctx, y)
                                     val family' = normalize_mt gctx kctx $ MtVar family'
                                   in
                                     if eq_constr_long_id ((name', family'), (name, family)) then
                                       SOME c
                                     else
                                       raise Incon "diff-constr"
                                   end
                                 | _ => NONE
                           in
                             case allSome same_constr cs of
                                 OK cs' =>
                                 let
                                   val (_, tbinds) = snd $ fetch_constr gctx (cctx, x)
                                   val (_, ibinds) = unfold_binds tbinds
                                   val (_, (t', _)) = unfold_binds ibinds
		                   val t' = subst_ts_mt ts t'
                                   (* val () = (* Debug. *)println (sprintf "All are $, now try to satisfy $" [str_v (names cctx) x, (join ", " o map (str_cover (names cctx))) (c' :: cs')]) *)
                                   val c' = loop $ check_size (t', c' :: cs')
                                                 (* val () = Debug.println (sprintf "Plugging $ into $" [str_habitant (names cctx) c', str_v (names cctx) x]) *)
                                 in
                                   inl $ ConstrH (x, c')
                                 end
                               | Failed (i, dissident) =>
                                 if conflict c dissident then
                                   raise Incon $ "conflicts on constructor " ^ str_raw_var x
                                 else
                                   inr (dissident, c :: remove i cs, t)
                           end
                         | NONE => default ()
                      )
                    | _ => default ()
              val ret =
                  case result of
                      inl hab => hab
                    | inr (c, cs, t) =>
                      case (c, t) of
                          (TrueC, _) => loop $ check_size (t, cs)
                        | (FalseC, _) => raise Incon "false"
                        | (AndC (c1, c2), _) => loop $ check_size (t, c1 :: c2 :: cs)
                        | (OrC (c1, c2), _) =>
                          (loop $ check_size (t, c1 :: cs) handle Incon _ => loop $ check_size (t, c2 :: cs))
                        | _ => raise impossible "find_hab()"
                                     (* val () = println (sprintf "Done find_hab on type $" [str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t]) *)
            in
              ret
            end
      end
    val ret = 
        SOME (loop (t, cs, ()))
        handle
        Incon debug =>
        let
          (* val () = println $ "Can't find a habitant because: " ^ debug *)
        in
          NONE
        end
          (* val () = println "find_hab() end" *)
  in
    ret
  end

fun any_missing deep gctx ctx t c =
  let
    (* val t = normalize_mt t *)
    val nc = cover_neg gctx ctx t c
    (* val () = println "after cover_neg()" *)
    (* val () = (* Debug. *)println (str_cover (names (#3 ctx)) nc) *)
    (* val () = println "before find_hab()" *)
    val ret = find_hab deep gctx ctx t [nc]
                       (* val () = println "after find_hab()" *)
  in
    ret
  end

fun is_redundant gctx (ctx, t, prevs, this) =
  let
    (* fun is_covered ctx t small big = *)
    (*     (isNull o (* (trace "after any_missing()") o *) any_missing true(*treat empty datatype as uninhabited*) ctx t o (* (trace "after cover_imply()") o *) cover_imply ctx t) (small, big) *)
    (* val t = normalize_mt t *)
    val prev = combine_covers prevs
    (* val () = println "after combine_covers()" *)
    (* val something_new = not (is_covered ctx t this prev) *)
    val something_new = isSome $ find_hab true(*treat empty datatype as uninhabited*) gctx ctx t $ [this, cover_neg gctx ctx t prev]                                  
                               (* val () = println "after find_hab()" *)
  in
    something_new
  end
    
fun is_exhaustive gctx (ctx as (_, _, cctx), t : mtype, covers) =
  let
    (* val t = normalize_mt t *)
    val cover = combine_covers covers
                               (* val () = Debug.println (str_cover (names cctx) cover) *)
  in
    any_missing true(*treat empty datatype as uninhabited*) gctx ctx t cover
  end
    
end
