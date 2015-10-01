structure Elaborate = struct
structure S = Ast
structure T = NamefulType
structure E = NamefulExpr
open S
open T
open E

local

n    exception Error of region * string

    fun runError m _ =
	OK (m ())
	handle
	Error e => Failed e

    fun elab_t t =
	case t of


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
	    let 
		fun default () = App (elab e1, elab e2)
	    in
		case e1 of
		    S.Var (x, _) => 
		    if x = "fst" then Fst (elab e2)
		    else if x = "snd" then Snd (elab e2)
		    else if x = "unfold" then Unfold (elab e2)
		    else default ()
		  | S.AppT (S.Var (x, _), t, _) =>
		    if x = "inl" then Inl (elab_t t, elab e2)
		    else if x = "inr" then Inr (elab_t t, elab e2)
		    else if x = "fold" then Fold (elab_t t, elab e2)
		    else default ()
		  | S.AppI (S.AppT (S.Var (x, _), t, _), i, _) =>
		    if x = "pack" then Pack (elab_t t, elab_i i, elab e2)
		    else default ()
		  | _ => default ()
	    end
	  | S.AppT (e, t, _) =>
	    AppT (elab e, elab_t t)
	  | S.AppI (e, i, _) =>
	    AppI (elab e, elab_i i)
	  | S.Case (e, NONE, rules, r) =>
	    (case rules of
		 [(S.Constr (c1, [], x1, _), e1), (S.Constr (c2, [], x2, _), e2)] =>
		 let 
		     val ((x1, e1), (x2, e2)) =
			 if c1 = "inl" andalso c2 = "inr" then
			     ((x1, e1), (x2, e2))
			 else if c2 = "inl" andalso c1 = "inr" then
			     ((x2, e2), (x1, e1))
			 else
			     raise Error (r, "constructor names of sum type must be inl or inr")
		 in
		     Match (elab e, x1, elab e1, x2, elab e2)
		 end
	       | _ => raise Error (r, "wrong match patterns for sum type"))
	  | S.Case (e, SOME (t, d), rules, _) =>
	    let 
		fun elab_pn (S.Constr (cname, inames, ename, _)) =
		    Constr (cname, inames, ename)
		fun default () = 
		    Case (elab e, elab_t t, elab_i d, map (fn (pn, e) => (elab_pn pn, elab e)) rules)
	    in
		case rules of
		    [(S.Constr (c, [iname], ename, _), e1)] =>
		    if c = "pack" then
			Unpack (elab e, elab_t t, elab_i d, iname, ename, elab e1)
		    else
			default ()
		  | _ => default ()
	    end
	  | S.Ascription (e, t, _) =>
	    Ascription (elab e, elab_t t)
	  | S.AscriptionTime (e, i, _) =>
	    AscriptionTime (elab e, elab_i i)
	  | S.Let (defs, e, _) =>
	    let fun f (e, def) =
		    case def of
			Val (x, e1, _) => Let (elab e1, x, e)
	    in
		foldr f (elab e) defs
	    end

end

end
