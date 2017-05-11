(* collect module references *)

structure CollectMod = struct
open Util
open Expr

infixr 0 $

fun on_ibind f acc (Bind (_, b) : ('a * 'b) ibind) = f acc b

fun on_long_id acc (m, _) = (option2list $ Option.map fst m) @ acc
fun collect_mod_long_id b = on_long_id [] b
  
local
  fun f acc b =
    case b of
	VarI x => on_long_id acc x
      | IConst _ => acc
      | UnOpI (opr, i, r) => f acc i
      | BinOpI (opr, i1, i2) => 
        let
          val acc = f acc i1
          val acc = f acc i2
        in
          acc
        end
      | Ite (i1, i2, i3, r) =>
        let
          val acc = f acc i1
          val acc = f acc i2
          val acc = f acc i3
        in
          acc
        end
      | IAbs (b, bind, r) =>
        on_ibind f acc bind
      | UVarI a => acc
in
val on_i = f
fun collect_mod_i b = f [] b
end

local
  fun f acc b =
    case b of
	PTrueFalse _ => acc
      | Not (p, r) => f acc p
      | BinConn (opr,p1, p2) =>
        let
          val acc = f acc p1
          val acc = f acc p2
        in
          acc
        end
      | BinPred (opr, i1, i2) => 
        let
          val acc = on_i acc i1
          val acc = on_i acc i2
        in
          acc
        end
      | Quan (q, bs, bind, r) => on_ibind f acc bind
in
val on_p = f
fun collect_mod_p b = f [] b
end

local
  fun f acc b =
    case b of
	Basic s => acc
      | Subset (b, bind, r) => on_ibind on_p acc bind
      | UVarS a => acc
      | SortBigO (b, i, r) => on_i acc i
      | SAbs (s, bind, r) => on_ibind f acc bind
      | SApp (s, i) =>
        let
          val acc = f acc s
          val acc = on_i acc i
        in
          acc
        end
in
val on_s = f
fun collect_mod_s b = f [] b
end

fun on_tbind f acc (Bind (_, b) : ('a * 'b) tbind) = f acc b

fun on_k acc (_, sorts) =
  foldl (fn (s, acc) => on_s acc s) acc sorts
                                                                        
local
  fun f acc b =
    case b of
	Arrow (t1, i, t2) =>
        let
          val acc = f acc t1
          val acc = on_i acc i
          val acc = f acc t2
        in
          acc
        end
      | TyNat (i, _) => on_i acc i
      | TyArray (t, i) =>
        let
          val acc = f acc t
          val acc = on_i acc i
        in
          acc
        end
      | Unit _ => acc
      | Prod (t1, t2) =>
        let
          val acc = f acc t1
          val acc = f acc t2
        in
          acc
        end
      | UniI (s, bind, _) =>
        let
          val acc = on_s acc s
          val acc = on_ibind f acc bind
        in
          acc
        end
      | MtVar x => on_long_id acc x
      | MtApp (t1, t2) =>
        let
          val acc = f acc t1
          val acc = f acc t2
        in
          acc
        end
      | MtAbs (k, bind, _) =>
        let
          val acc = on_k acc k
          val acc = on_tbind f acc bind
        in
          acc
        end
      | MtAppI (t, i) =>
        let
          val acc = f acc t
          val acc = on_i acc i
        in
          acc
        end
      | MtAbsI (s, bind, r) =>
        let
          val acc = on_s acc s
          val acc = on_ibind f acc bind
        in
          acc
        end
      | BaseType _ => acc
      | UVar _ => acc
in
val on_mt = f
fun collect_mod_mt b = f [] b
end

local
  fun f acc b =
    case b of
	Mono t => on_mt acc t
      | Uni (bind, r) => on_tbind f acc bind
in
val on_t = f
fun collect_mod_t b = f [] b
end

fun on_option f acc a =
  case a of
      SOME a => f acc a
    | NONE => acc
                
local
  fun f acc b =
    case b of
	ConstrP ((x, eia), inames, pn, r) =>
        let
          val acc = on_long_id acc x
          val acc = on_option f acc pn
        in
          acc
        end
      | VarP name => acc
      | PairP (pn1, pn2) =>
        let
          val acc = f acc pn1
          val acc = f acc pn2
        in
          acc
        end
      | TTP r => acc
      | AliasP (name, pn, r) => f acc pn
      | AnnoP (pn, t) =>
        let
          val acc = f acc pn
          val acc = on_mt acc t
        in
          acc
        end
in
val on_ptrn = f
fun collect_mod_ptrn b = f [] b
end

(* local *)
(*   fun f acc b = *)
(*       case b of *)
(* 	  Var (x, _) => collect_mod_long_id x @ acc *)
(* 	| Abs (pn, e) => *)
(*           let *)
(*             val acc = on_ptrn acc pn *)
(*             val acc = f acc e *)
(*           in *)
(*             acc *)
(*           end *)
(* 	| App (e1, e2) => *)
(*           let *)
(*             val acc = f acc e1 *)
(*             val acc = f acc e2 *)
(*           in *)
(*             acc *)
(*           end *)
(* 	| TT r => acc *)
(* 	| Pair (e1, e2) => *)
(*           let *)
(*             val acc = f acc e1 *)
(*             val acc = f acc e2 *)
(*           in *)
(*             acc *)
(*           end *)
(* 	| Fst e => Fst (f x n e) *)
(* 	| Snd e => Snd (f x n e) *)
(* 	| AbsI (s, name, e, r) => AbsI (s, name, f x n e, r) *)
(* 	| AppI (e, i) => AppI (f x n e, i) *)
(* 	| Let (return, decs, e, r) => *)
(* 	  let  *)
(* 	    val (decs, m) = f_decls x n decs *)
(* 	  in *)
(* 	    Let (return, decs, f (x + m) n e, r) *)
(* 	  end *)
(* 	| Ascription (e, t) => Ascription (f x n e, t) *)
(* 	| AscriptionTime (e, d) => AscriptionTime (f x n e, d) *)
(* 	| ConstInt n => ConstInt n *)
(* 	| ConstNat n => ConstNat n *)
(* 	| BinOp (opr, e1, e2) => BinOp (opr, f x n e1, f x n e2) *)
(* 	| TriOp (opr, e1, e2, e3) => TriOp (opr, f x n e1, f x n e2, f x n e3) *)
(* 	| AppConstr (cx, is, e) => AppConstr (cx, is, f x n e) *)
(* 	| Case (e, return, rules, r) => Case (f x n e, return, map (f_rule x n) rules, r) *)
(* 	| Never t => Never t *)
(* 	| Builtin t => Builtin t *)

(* in *)
(* end *)

end
