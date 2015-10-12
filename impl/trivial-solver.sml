structure TrivialSolver = struct
open Type
open Expr
open IdxEqual
         
fun solve (ctx, ps, p) =
  isSome (List.find (eq_p p) ps) orelse
  case p of
      BinConn (Imply, p1, p2) => solve (ctx, p1 :: ps, p2)
    | BinConn (Iff, p1, p2) => solve (ctx, p1 :: ps, p2) andalso solve (ctx, p2 :: ps, p1)
    | BinConn (And, p1, p2) => solve (ctx, ps, p1) andalso solve (ctx, ps, p1)
    | BinConn (Or, p1, p2) => solve (ctx, ps, p1) orelse solve (ctx, ps, p1)
    | True _ => true
    | BinPred (EqP, i1, i2) => eq_i i1 i2
    | BinPred (LeP, i1, i2) => eq_i i1 i2
    | _ => false

fun solve_vc (ctx, ps, p, _) = solve (ctx, ps, p)

fun filter_solve vcs = List.filter (fn vc => solve_vc vc = false) vcs

local
    fun passi i =
	case i of
	    BinOpI (MaxI, i1, i2) =>
	    if eq_i i1 i2 then
		(true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, BinOpI (MaxI, i1, i2))
		end
	  | BinOpI (MinI, i1, i2) =>
	    if eq_i i1 i2 then
		(true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, BinOpI (MinI, i1, i2))
		end
	  | BinOpI (AddI, i1, i2) => 
	    if eq_i i1 (T0 dummy) then (true, i2)
	    else if eq_i i2 (T0 dummy) then (true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, BinOpI (AddI, i1, i2))
		end
	  | BinOpI (MinusI, i1, i2) => 
	    if eq_i i2 (T0 dummy) then (true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, BinOpI (MinusI, i1, i2))
		end
	  | BinOpI (MultI, i1, i2) => 
	    if eq_i i1 (T0 dummy) then (true, (T0 dummy))
	    else if eq_i i2 (T0 dummy) then (true, (T0 dummy))
	    else if eq_i i1 (T1 dummy) then (true, i2)
	    else if eq_i i2 (T1 dummy) then (true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, BinOpI (MultI, i1, i2))
		end
          | UnOpI (opr, i, r) =>
            let val (b, i) = passi i
            in
                (b, UnOpI (opr, i, r))
            end
	  | _ => (false, i)
		     
    fun passp p = 
	case p of
	    BinConn (opr, p1, p2) => 
	    let val (b1, p1) = passp p1
		val (b2, p2) = passp p2 in
		(b1 orelse b2, BinConn (opr, p1, p2))
	    end
	  | BinPred (opr, i1, i2) => 
	    let val (b1, i1) = passi i1
		val (b2, i2) = passi i2 in
		(b1 orelse b2, BinPred (opr, i1, i2))
	    end
	  | _ => (false, p)
                     
    fun until_unchanged f a = 
	let fun loop a =
		let val (changed, a') = f a in
		    if changed then loop a'
		    else a
		end in
	    loop a
	end
in
val simp_p = until_unchanged passp
val simp_i = until_unchanged passi
fun simp_vc (ctx, ps, p, r) = (ctx, map simp_p ps, simp_p p, r)
end

fun simp_s s =
    case s of
	Basic b => Basic b
      | Subset (b, name, p) => Subset (b, name, simp_p p)

local
    fun f t =
	case t of
	    Arrow (t1, d, t2) => Arrow (f t1, simp_i d, f t2)
	  | Prod (t1, t2) => Prod (f t1, f t2)
	  | Sum (t1, t2) => Sum (f t1, f t2)
	  | Unit r => Unit r
	  | AppRecur (name, ns, t, is, r) => AppRecur (name, map (mapSnd simp_s) ns, f t, map simp_i is, r)
	  | AppV (x, ts, is, r) => AppV (x, map f ts, map simp_i is, r)
	  | Uni (name, t) => Uni (name, f t)
	  | UniI (s, name, t) => UniI (simp_s s, name, f t)
	  | ExI (s, name, t) => ExI (simp_s s, name, f t)
	  | Int r => Int r

in
val simp_t = f
end

fun simp_and_solve_vcs vcs =
    let 
	(* val () = print "Simplifying and applying trivial solver ...\n" *)
	val vcs = filter_solve vcs
	val vcs = map simp_vc vcs
	val vcs = filter_solve vcs
    in
        vcs
    end

end
