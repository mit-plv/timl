structure NoUVar = struct
open Util
       
type 'bsort uvar_bs = empty
type ('bsort, 'idx) uvar_i = empty
type 'sort uvar_s = empty
type 'mtype uvar_mt = empty
fun str_uvar_bs (_ : 'a -> string) (u : 'a uvar_bs) = exfalso u
fun str_uvar_mt (_ : string list * string list -> 'mtype -> string) (_ : string list * string list) (u : 'mtype uvar_mt) = exfalso u
fun str_uvar_i (_ : string list -> 'idx -> string) (_ : string list) (u : ('bsort, 'idx) uvar_i) = exfalso u
fun eq_uvar_i (u : ('bsort, 'idx) uvar_i, u' : ('bsort, 'idx) uvar_i) = exfalso u
end

structure NoUVarExpr = ExprFun (structure Var = IntVar structure UVar = NoUVar)

structure NoUVarSubst = struct
open Util
open NoUVarExpr
infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 4 %<=
infix 4 %=
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->
infixr 0 $
         
fun on_i_i on_v x n b =
    let
      fun f x n b =
	  case b of
	      VarI (y, r) => VarI (on_v x n y, r)
	    | ConstIN n => ConstIN n
	    | ConstIT x => ConstIT x
            | UnOpI (opr, i, r) => UnOpI (opr, f x n i, r)
            | DivI (i1, n2) => DivI (f x n i1, n2)
            | ExpI (i1, n2) => ExpI (f x n i1, n2)
	    | BinOpI (opr, i1, i2) => BinOpI (opr, f x n i1, f x n i2)
            | Ite (i1, i2, i3, r) => Ite (f x n i1, f x n i2, f x n i3, r)
	    | TTI r => TTI r
	    | TrueI r => TrueI r
	    | FalseI r => FalseI r
            | TimeAbs (name, i, r) => TimeAbs (name, f (x + 1) n i, r)
            | AdmitI r => AdmitI r
            | UVarI (u, _) => exfalso u
    in
      f x n b
    end

fun on_i_p on_i_i x n b =
    let
      fun f x n b =
          case b of
	      True r => True r
	    | False r => False r
            | Not (p, r) => Not (f x n p, r)
	    | BinConn (opr, p1, p2) => BinConn (opr, f x n p1, f x n p2)
	    | BinPred (opr, d1, d2) => BinPred (opr, on_i_i x n d1, on_i_i x n d2)
            | Quan (q, bs, name, p, r) => Quan (q, bs, name, f (x + 1) n p, r)
    in
      f x n b
    end

fun shiftx_v x n y = 
    if y >= x then
      y + n
    else
      y

and shiftx_i_i x n b = on_i_i shiftx_v x n b
fun shift_i_i b = shiftx_i_i 0 1 b

fun shiftx_i_p x n b = on_i_p shiftx_i_i x n b
fun shift_i_p b = shiftx_i_p 0 1 b

local
  fun f x v b =
      case b of
	  VarI (y, r) =>
	  if y = x then
	    v
	  else if y > x then
	    VarI (y - 1, r)
	  else
	    VarI (y, r)
	| ConstIN n => ConstIN n
	| ConstIT x => ConstIT x
        | UnOpI (opr, i, r) => UnOpI (opr, f x v i, r)
        | DivI (i1, n2) => DivI (f x v i1, n2)
        | ExpI (i1, n2) => ExpI (f x v i1, n2)
	| BinOpI (opr, d1, d2) => BinOpI (opr, f x v d1, f x v d2)
        | Ite (i1, i2, i3, r) => Ite (f x v i1, f x v i2, f x v i3, r)
	| TrueI r => TrueI r
	| FalseI r => FalseI r
	| TTI r => TTI r
        | TimeAbs (name, i, r) => TimeAbs (name, f (x + 1) (shiftx_i_i 0 1 v) i, r)
        | AdmitI r => AdmitI r
        | UVarI (u, _) => exfalso u
in
fun substx_i_i x (v : idx) (b : idx) : idx = f x v b
fun subst_i_i v b = substx_i_i 0 v b
end

local
  fun f x v b =
      case b of
	  True r => True r
	| False r => False r
        | Not (p, r) => Not (f x v p, r)
	| BinConn (opr,p1, p2) => BinConn (opr, f x v p1, f x v p2)
	| BinPred (opr, d1, d2) => BinPred (opr, substx_i_i x v d1, substx_i_i x v d2)
        | Quan (q, bs, name, p, r) => Quan (q, bs, name, f (x + 1) (shiftx_i_i 0 1 v) p, r)
in
fun substx_i_p x (v : idx) b = f x v b
fun subst_i_p (v : idx) (b : prop) : prop = substx_i_p 0 v b
end

exception ForgetError of var
(* exception Unimpl *)

fun forget_v x n y = 
    if y >= x + n then
      y - n
    else if y < x then
      y
    else
      raise ForgetError y

fun forget_i_i x n b = on_i_i forget_v x n b
fun forget_i_p x n b = on_i_p forget_i_i x n b
                              
fun try_forget f a =
    SOME (f a) handle ForgetError _ => NONE

(* val passi_debug = ref false *)

fun hyps2ctx hs = List.mapPartial (fn h => case h of VarH (name, _) => SOME name | _ => NONE) hs

fun str_hyps_conclu (hyps, p) =
    let 
      fun g (h, (hyps, ctx)) =
          case h of
              VarH ((name, _), (bs, _)) => (sprintf "$ : $" [name, str_bs bs] :: hyps, name :: ctx)
            | PropH p => (str_p ctx p :: hyps, ctx)
      val (hyps, ctx) = foldr g ([], []) hyps
      val hyps = rev hyps
      val p = str_p ctx p
    in
      hyps @
      ["==============="] @
      [p]
    end 

fun shiftx_hyp x n hyp =
    case hyp of
        VarH _ => hyp
      | PropH p => PropH (shiftx_i_p x n p)
                         
fun shiftx_hyps x n hyps =
    case hyps of
        [] => hyps
      | hyp :: hyps =>
        let
          val d = case hyp of
                      VarH _ => 1
                    | PropH _ => 0
        in
          shiftx_hyp x n hyp :: shiftx_hyps (x + d) n hyps
        end

(* find something about [x] in [hyps]. [x] is expressed as being in the innermost of [hyps] (so [x] can see all variables in [hyps]). *)
fun find_hyp forget shift pred x hyps =
    let
      exception Error
      fun runError m _ =
          SOME (m ())
          handle
          Error => NONE
          | ForgetError _ => NONE
      fun do_forget hyp x =
          case hyp of
              VarH _ => forget x
            | PropH _ => x
      fun do_shift hyp (p as (y, hyps)) =
          case hyp of
              VarH _ => (shift y, shiftx_hyps 0 1 hyps)
            | PropH _ => p
      fun loop x hyps () =
          let
            val (hyp, hyps) = case hyps of hyp :: hyps => (hyp, hyps) | [] => raise Error
            val x = do_forget hyp x
          in
            case pred x hyps hyp of
                SOME y => do_shift hyp (y, hyps)
              | NONE => do_shift hyp (loop x hyps ())
          end
    in
      runError (loop x hyps) ()
    end
      
local
  val changed = ref false
  fun unset () = changed := false
  fun set () = changed := true
  fun mark a = (set (); a)
  fun passi i =
      let
        (* val () = if !passi_debug then (fn () => println $ str_i [] i) () else () *)
        fun r () = get_region_i i
      in
        case i of
            DivI (i1, n2) => DivI (passi i1, n2)
          | ExpI (i1, n2) => ExpI (passi i1, n2)
	  | BinOpI (opr, i1, i2) =>
            let
              fun def () = BinOpI (opr, passi i1, passi i2)
            in
              case opr of
	          MaxI =>
	          if eq_i i1 i2 then
                    mark i1
	          else if eq_i i1 (T0 dummy) orelse eq_i i1 (ConstIN (0, dummy)) then
                    mark i2
	          else if eq_i i2 (T0 dummy) orelse eq_i i2 (ConstIN (0, dummy)) then
                    mark i1
	          else
                    (case (i1, i2) of
                         (BinOpI (opr, i1, i2), BinOpI (opr', i1', i2')) =>
                         if opr = opr' then
                           if opr = AddI orelse opr = MultI then
                             if eq_i i1 i1' then
                               mark $ BinOpI (opr, i1, BinOpI (MaxI, i2, i2'))
                             else if eq_i i2 i2' then
                               mark $ BinOpI (opr, BinOpI (MaxI, i1, i1'), i2)
                             else def ()
                           else if opr = TimeApp then
                             if eq_i i1 i1' then
                               mark $ BinOpI (opr, i1, BinOpI (MaxI, i2, i2'))
                             else def ()
                           else def ()
                         else def ()
                       | _ => def ()
                    )
	        | MinI =>
	          if eq_i i1 i2 then
                    mark i1
	          else
		    def ()
	        | AddI => 
	          if eq_i i1 (T0 dummy) orelse eq_i i1 (ConstIN (0, dummy)) then
                    mark i2
	          else if eq_i i2 (T0 dummy) orelse eq_i i2 (ConstIN (0, dummy)) then
                    mark i1
	          else
                    let
                      val is = collect_AddI i
                      val (i', is) = case is of
                                         i :: is => (i, is)
                                       | [] => raise Impossible "passi/AddI"
                      val i' = combine_AddI_nonempty i' is
                    in
		      if eq_i i' i then
                        def ()
                      else
                        mark i'
                    end
	        | MultI => 
	          if eq_i i1 (T0 dummy) then
                    mark $ T0 $ r ()
	          else if eq_i i2 (T0 dummy) then
                    mark $ T0 $ r ()
	          else if eq_i i1 (T1 dummy) then
                    mark i2
	          else if eq_i i2 (T1 dummy) then
                    mark i1
	          else
                    (case (i1, i2) of
                         (ConstIN (n1, _), ConstIN (n2, _)) =>
                         mark $ ConstIN (n1 * n2, r ())
                       | _ =>
                         let
                           val i2s = collect_AddI i2
                           fun pred i =
                               case i of
                                   ConstIN _ => SOME i
                                 | UnOpI (B2n, _, _) => SOME i
                                 | _ => NONE
                         in
                           case partitionOptionFirst pred i2s of
                               SOME (i2, rest) =>
                               let
                                 val ret = i1 %* i2
                                 val ret =
                                     case rest of
                                         [] => ret
                                       | hd :: rest => ret %+ i1 %* combine_AddI_nonempty hd rest
                               in
                                 if eq_i ret i then
                                   def ()
                                 else
                                   mark ret
                               end
                             | NONE => def ()
                         end
                    )
                | TimeApp =>
                  (case i1 of
                       TimeAbs (_, body, _) =>
                       mark $ subst_i_i (passi i2) body
		     | _ => def ()
                  )
                | EqI =>
                  if eq_i i1 i2 then
                    mark $ TrueI $ r ()
                  else def ()
                | AndI =>
                  if eq_i i1 (TrueI dummy) then
                    mark i2
                  else if eq_i i2 (TrueI dummy) then
                    mark i1
                  else if eq_i i1 (FalseI dummy) then
                    mark $ FalseI $ r ()
                  else if eq_i i2 (FalseI dummy) then
                    mark $ FalseI $ r ()
                  else
                    def ()
                | ExpNI =>
                  let
                    val r = r ()
                    fun exp i n =
                        if n > 0 then
                          exp i (n-1) %* i
                        else
                          N1 r
                  in
                    case i2 of
                        ConstIN (n, _) => exp i1 n
                      | UnOpI (B2n, i, _) => Ite (i, i1, N1 r, r)
                      | _ =>
                        let
                          val i2s = collect_AddI i2
                          fun pred i =
                              case i of
                                  ConstIN _ => SOME i
                                | UnOpI (B2n, _, _) => SOME i
                                | _ => NONE
                        in
                          case partitionOptionFirst pred i2s of
                              SOME (i2, rest) => mark $ i1 %^ i2 %* i1 %^ combine_AddI_Nat rest
                            | NONE => def ()
                        end
                  end
                | LtI =>
                  def ()
                | GeI =>
                  def ()
                | BoundedMinusI =>
                  def ()
            end
          | Ite (i, i1, i2, r) =>
            if eq_i i (TrueI dummy) then
              mark i1
            else if eq_i i (FalseI dummy) then
              mark i2
            else
              Ite (passi i, passi i1, passi i2, r)
          | UnOpI (ToReal, BinOpI (AddI, i1, i2), r) =>
            mark $ BinOpI (AddI, UnOpI (ToReal, i1, r), UnOpI (ToReal, i2, r))
          | UnOpI (ToReal, BinOpI (MultI, i1, i2), r) =>
            mark $ BinOpI (MultI, UnOpI (ToReal, i1, r), UnOpI (ToReal, i2, r))
          | UnOpI (Neg, TrueI _, r) =>
            mark $ FalseI r
          | UnOpI (Neg, FalseI _, r) =>
            mark $ TrueI r
          | UnOpI (B2n, TrueI _, r) =>
            mark $ N1 r
          | UnOpI (B2n, FalseI _, r) =>
            mark $ N0 r
          | UnOpI (opr, i, r) =>
            UnOpI (opr, passi i, r)
          | TimeAbs ((name, r1), i, r) =>
            TimeAbs ((name, r1), passi i, r)
	  | TrueI _ => i
	  | FalseI _ => i
	  | TTI _ => i
          | ConstIN _ => i
          | ConstIT _ => i
          | VarI _ => i
          | AdmitI _ => i
          | UVarI _ => i
      end
        
  fun passp p =
      let
        fun r () = get_region_p p
      in
        case p of
	    BinConn (opr, p1, p2) =>
            let
              fun def () = BinConn (opr, passp p1, passp p2) 
            in
              case opr of
                  And =>
	          if eq_p p1 (True dummy) then
                    mark p2
	          else if eq_p p2 (True dummy) then
                    mark p1
	          else
	            def ()
                | Or =>
	          if eq_p p1 (False dummy) then
                    mark p2
	          else if eq_p p2 (False dummy) then
                    mark p1
	          else
	            def ()
                | Imply =>
	          if eq_p p1 (True dummy) then
                    mark p2
                  else if eq_p p2 (True dummy) then
                    mark $ True $ r ()
                  else
                    (case p1 of
                         BinConn (And, p1a, p1b) =>
                         mark $ (p1a --> p1b --> p2)
                       | _ => def ()
                    )
                | _ => def ()
            end
	  | BinPred (opr, i1, i2) =>
            let
              fun def () = BinPred (opr, passi i1, passi i2)
            in
              case opr of 
                  EqP => if eq_i i1 i2 then
                           mark $ True $ r ()
                         else def ()
                | LeP => if eq_i i1 i2 orelse eq_i i1 (T0 dummy) then
                           mark $ True $ r ()
                         else def ()
                | _ => def ()
            end
          | Not (p, r) => Not (passp p, r)
          | p_all as Quan (q, bs, name, p, r_all) =>
            let
              fun def () = Quan (q, bs, name, passp p, r_all)
            in
              case q of
                  Forall =>
                  (case try_forget (forget_i_p 0 1) p of
                       SOME p => (set (); p)
                     | _ =>
                       (* try subst if there is a equality premise *)
                       (*
if false then
                     let
                       (* val () = println $ "Try subst eq premise" *)
                       fun collect_Imply p =
                           case p of
                               BinConn (Imply, p1, p2) =>
                               let
                                 val (hyps, conclu) = collect_Imply p2
                               in
                                 (collect_And p1 @ hyps, conclu)
                               end
                             | _ => ([], p)
                       fun combine_Imply hyps conclu =
                           case hyps of
                               h :: hyps => h --> combine_Imply hyps conclu
                             | [] => conclu
                       fun collect_Forall p =
                           case p of
                               Quan (Forall, bs, name, p, r) =>
                               let
                                 val (binds, p) = collect_Forall p
                               in
                                 ((name, bs, r) :: binds, p)
                               end
                             | _ => ([], p)
                       fun combine_Forall binds p =
                           case binds of
                               [] => p
                             | (name, bs, r) :: binds =>
                               Quan (Forall, bs, name, combine_Forall binds p, r)
                       val (binds, p) = collect_Forall p_all
                       val (hyps, conclu) = collect_Imply p
                       val binds_len = length binds
                       (* test whether [p] is [VarI x = _] or [_ = VarI x] *)
                       fun is_var_equals p =
                           let
                             fun find_var (i1, i2) =
                                 case i1 of
                                     VarI (x, _) =>
                                     (if 0 <= x andalso x < binds_len then
                                        SOME (x, forget_i_i x 1 i2) handle ForgetError _ => NONE
                                      else NONE
                                     )
                                   | _ => NONE
                           in
                             case p of
                                 BinPred (EqP, i1, i2) => firstSuccess find_var [(i1, i2), (i2, i1)]
                               | _ => NONE
                           end
                     in
                       case partitionOptionFirst is_var_equals hyps of
                           SOME ((x, i), rest) =>
                           let
                             (* val () = println $ "Substing " ^ str_v (rev $ map (fst o fst) binds) x *)
                             val () = set ()
                             val ret = combine_Forall (remove (binds_len - 1 - x) binds) $ substx_i_p x i $ combine_Imply rest conclu
                           in
                             ret
                           end
                         | NONE => def ()
                     end
else
                       *)
                       let
                         (* val () = println $ "Try subst eq premise" *)
                         (* fun collect_Imply_Forall p = *)
                         (*     case p of *)
                         (*         BinConn (Imply, p1, p2) => *)
                         (*         let *)
                         (*           val (hyps, conclu) = collect_Imply_Forall p2 *)
                         (*         in *)
                         (*           (map PropH (collect_And p1)(* [PropH p1] *) @ hyps, conclu) *)
                         (*         end *)
                         (*       | Quan (Forall, bs, name, p, r) => *)
                         (*         let *)
                         (*           val (hyps, p) = collect_Imply_Forall p *)
                         (*         in *)
                         (*           (VarH (name, (bs, r)) :: hyps, p) *)
                         (*         end *)
                         (*       | _ => ([], p) *)
                         (* a faster version *)
                         fun collect_Imply_Forall p =
                             let
                               fun loop (acc, p) =
                                   case p of
                                       BinConn (Imply, p1, p2) =>
                                       loop (map PropH (rev $ collect_And p1) @ acc, p2)
                                     | Quan (Forall, bs, name, p, r) =>
                                       loop (VarH (name, (bs, r)) :: acc, p)
                                     | _ => (acc, p)
                               val (hyps, conclu) = loop ([], p)
                               val hyps = rev hyps
                             in
                               (hyps, conclu)
                             end
                         fun combine_Imply_Forall hyps conclu =
                             let
                               fun iter (h, conclu) =
                                   case h of
                                       PropH p =>
                                       p --> conclu
                                     | VarH (name, (bs, r))  =>
                                       Quan (Forall, bs, name, conclu, r)
                             in
                               foldr iter conclu hyps
                             end
                         val (hyps, conclu) = collect_Imply_Forall p
                         val hyps = rev hyps
                         val binds_len = length $ hyps2ctx hyps
                         (* test whether [p] is [VarI x = _] or [_ = VarI x] *)
                         fun is_var_equals x p =
                             let
                               fun find_var (i1, i2) =
                                   if eq_i i1 (VarI (x, dummy)) then
                                     SOME (forget_i_i x 1 i2) handle ForgetError _ => NONE
                                   else NONE
                             in
                               case p of
                                   BinPred (EqP, i1, i2) => firstSuccess find_var [(i1, i2), (i2, i1)]
                                 | _ => NONE
                             end
                         fun foldr_hyps shift1 shift2 f init hyps =
                             let
                               fun iter (h, (x, acc)) =
                                   case h of
                                       VarH _ => (shift1 x, Option.map shift2 acc)
                                     | PropH p =>
                                       case acc of
                                           SOME _ => (x, acc)
                                         | NONE => (x, f x p)
                             in
                               snd $ foldr iter (init, NONE) hyps
                             end
                       in
                         case foldr_hyps (shiftx_v 0 1) shift_i_i is_var_equals 0 hyps of
                             SOME i =>
                             (let
                               val x = binds_len
                               val ctxn = map fst $ hyps2ctx hyps
                               (* val () = println $ sprintf "Substing for $ with $" [str_v (ctxn @ [fst name]) x, str_i ctxn i] *)
                               (* val () = app println $ str_hyps_conclu (hyps @ [VarH (name, (bs, r_all))], conclu) @ [""]  *)
                               val conclu = substx_i_p x i conclu
                               fun subst_hyp n p =
                                   let
                                     val x = forget_v 0 n x
                                     val p =
                                         case try_forget (forget_i_p x 1) p of
                                             NONE =>
                                             let
                                               val i = forget_i_i 0 n i
                                             in
                                               substx_i_p x i p
                                             end
                                           | SOME p => p
                                   in
                                     p
                                   end
                               fun foldl_hyps f hyps =
                                   let
                                     fun iter (h, (n, acc)) =
                                         case h of
                                             VarH _ => (n + 1, h :: acc)
                                           | PropH p => (n, PropH (f n p) :: acc)
                                   in
                                     rev $ snd $ foldl iter (0, []) hyps
                                   end
                               val hyps = foldl_hyps subst_hyp hyps
                               (* val () = app println $ str_hyps_conclu (hyps, conclu) @ [""]  *)
                               val ret = combine_Imply_Forall (rev hyps) conclu
                             in
                               mark ret
                             end
                              handle ForgetError _ => def ()
                             )
                           | NONE => def ()
                       end

                         
                  (*
                      (case p of
                           BinConn (Imply, p1, p2) =>
                           let
                               fun forget i = try_forget (forget_i_i 0 1) i
                               fun f i1 i2 =
                                   if eq_i i1 (VarI (0, dummy)) then forget i2
                                   else if eq_i i2 (VarI (0, dummy)) then forget i1
                                   else NONE
                               val i = case p1 of
                                           BinPred (EqP, i1, i2) => f i1 i2
                                         | _ => NONE
                           in
                               case i of
                                   SOME i => (set (); subst_i_p i p2)
                                 | _ => Quan (q, bs, name, passp p)
                           end
                         | _ =>
                           Quan (q, bs, name, passp p)
                      )
                  *)
                  )
                | Exists ins =>
                  (* for unconstrained Time evar, infer it to be 0 *)
                  let
                    val p = passp p
                  in
                    case (eq_bs bs (Base Time), try_forget (forget_i_p 0 1) p) of
                        (true, SOME p) =>
                        (set ();
                         (case ins of SOME f => f (T0 dummy) | NONE => ());
                         p)
                      | _ =>
                        let
                          val ps = collect_And p
                          val (irrelevant, relevant) = partitionOption (try_forget (forget_i_p 0 1)) ps
                        in
                          case relevant of
                              [] => def ()
                            | _ => combine_And $ Quan (q, bs, name, combine_And relevant, r_all) :: irrelevant
                        end
                  end
            end
	  | True _ => p
	  | False _ => p
      end
        
  fun until_unchanged f a = 
      let fun loop a =
	      let
                val _ = unset ()
                (* val () = println "before f()" *)
                val a = f a
                          (* val () = println "after f()" *)
              in
		if !changed then loop a
		else a
	      end
      in
	loop a
      end
in
val simp_i = until_unchanged passi
fun simp_p p =
    let
      (* val () = println $ "Before simp_p: " ^ str_p [] p *)
      val p = until_unchanged passp p
                              (* val () = println $ "After simp_p:  " ^ str_p [] p *)
                              (* val () = println "" *)
    in
      p      
    end
fun simp_p_with_plugin plugin p =
    let
      fun iter p =
          let
            val p = plugin set p
            val p = passp p
          in
            p
          end
      val p = until_unchanged iter p
    in
      p      
    end
      
end

end

