structure TrivialSolve = struct
open Type
open Expr

fun eq_i i i' =
    case (i, i') of
        (VarI (x, _), VarI (x', _)) => x = x'
      | (T0 _, T0 _) => true
      | (T1 _, T1 _) => true
      | (Tconst (n, _), Tconst (n', _)) => n = n'
      | (Tadd (i1, i2), Tadd (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | (Tmult (i1, i2), Tmult (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | (Tmax (i1, i2), Tmax (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | (Tmin (i1, i2), Tmin (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | (TrueI _, TrueI _) => true
      | (FalseI _, FalseI _) => true
      | (TTI _, TTI _) => true
      | _ => false

fun eq_p p p' =
    case (p, p') of
        (True _ , True _) => true
      | (False _, False _) => true
      | (And (p1, p2), And (p1', p2')) => eq_p p1 p1' andalso eq_p p2 p2'
      | (Or (p1, p2), Or (p1', p2')) => eq_p p1 p1' andalso eq_p p2 p2'
      | (Imply (p1, p2), Imply (p1', p2')) => eq_p p1 p1' andalso eq_p p2 p2'
      | (Iff (p1, p2), Iff (p1', p2')) => eq_p p1 p1' andalso eq_p p2 p2'
      | (Eq (i1, i2), Eq (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | (TimeLe (i1, i2), TimeLe (i1', i2')) => eq_i i1 i1' andalso eq_i i2 i2'
      | _ => false

local
    fun solver (ctx, ps, p) =
	isSome (List.find (eq_p p) ps) orelse
	case p of
	    Imply (p1, p2) => solver (ctx, p1 :: ps, p2)
	  | Iff (p1, p2) => solver (ctx, p1 :: ps, p2) andalso solver (ctx, p2 :: ps, p1)
	  | And (p1, p2) => solver (ctx, ps, p1) andalso solver (ctx, ps, p1)
	  | Or (p1, p2) => solver (ctx, ps, p1) orelse solver (ctx, ps, p1)
	  | True _ => true
	  | Eq (i1, i2) => eq_i i1 i2
	  | TimeLe (i1, i2) => eq_i i1 i2
	  | _ => false

in
fun trivial_solver vcs = List.filter (fn vc => solver vc = false) vcs
end

local
    fun passi i =
	case i of
	    Tmax (i1, i2) =>
	    if eq_i i1 i2 then
		(true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, Tmax (i1, i2))
		end
	  | Tmin (i1, i2) =>
	    if eq_i i1 i2 then
		(true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, Tmin (i1, i2))
		end
	  | Tadd (i1, i2) => 
	    if eq_i i1 (T0 dummy) then (true, i2)
	    else if eq_i i2 (T0 dummy) then (true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, Tadd (i1, i2))
		end
	  | Tmult (i1, i2) => 
	    if eq_i i1 (T0 dummy) then (true, (T0 dummy))
	    else if eq_i i2 (T0 dummy) then (true, (T0 dummy))
	    else if eq_i i1 (T1 dummy) then (true, i2)
	    else if eq_i i2 (T1 dummy) then (true, i1)
	    else
		let val (b1, i1) = passi i1
		    val (b2, i2) = passi i2 in
		    (b1 orelse b2, Tmult (i1, i2))
		end
	  | _ => (false, i)
		     
    fun passp p = 
	case p of
	    And (p1, p2) => 
	    let val (b1, p1) = passp p1
		val (b2, p2) = passp p2 in
		(b1 orelse b2, And (p1, p2))
	    end
	  | Or (p1, p2) => 
	    let val (b1, p1) = passp p1
		val (b2, p2) = passp p2 in
		(b1 orelse b2, Or (p1, p2))
	    end
	  | Imply (p1, p2) => 
	    let val (b1, p1) = passp p1
		val (b2, p2) = passp p2 in
		(b1 orelse b2, Imply (p1, p2))
	    end
	  | Iff (p1, p2) => 
	    let val (b1, p1) = passp p1
		val (b2, p2) = passp p2 in
		(b1 orelse b2, Iff (p1, p2))
	    end
	  | Eq (i1, i2) => 
	    let val (b1, i1) = passi i1
		val (b2, i2) = passi i2 in
		(b1 orelse b2, Eq (i1, i2))
	    end
	  | TimeLe (i1, i2) => 
	    let val (b1, i1) = passi i1
		val (b2, i2) = passi i2 in
		(b1 orelse b2, TimeLe (i1, i2))
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
fun simplify (ctx, ps, p) = (ctx, map simp_p ps, simp_p p)
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

end
