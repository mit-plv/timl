structure Elaborate = struct
struct S = Ast
structure T = NamefulType
structure E = NamefulExpr
open S
open T
open E

fun elab e =
    case e of
	S.Var (x, _) => Var x
      | S.Tuple (es, r) =>
	(case es of
	     [] => TT
	   | [e1, e2] => Pair (e1, e2)
	   | _ => raise Error (r, "Do not support tuples other than () and pair")
	)
      | S.Abs (abs, binds, e, r) =>
	(case abs of
	     S.Fix => 
	     (case binds of
		  Typing (x, t, _) :: binds => Fix (elab_t t, x, elab (S.Abs (Fn, binds, e, r)))
		| _ => raise Error (r, "fixpoint must have a typing bind as the first bind"))
	   | Fn =>
	     let fun f (b, e) =
		     case b of
			 Typing (x, t, _) => Abs (elab_t t, x, e)
		       | Kinding (x, _) => AbsT (x, e)
		       | Sorting (x, s, _) => AbsI (elab_s s, x, e)
	     in
		 foldr f (elab e) binds
	     end)
      | S.App (e1, e2, _) =>
	(case e1 of
	     S.Var (x, _) => 
	     if x = "fst" then Fst (elab e2)
	     else if x = "snd" then Snd (elab e2)
	     else App (elab e1, elab e2)
	   | S.App)
end
