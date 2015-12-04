structure NoUVar = struct
open Util
type 'a uvar_bs = empty
type ('a, 'b) uvar_s = empty
type ('a, 'b) uvar_mt = empty
type ('a, 'b) uvar_i = empty
fun str_uvar_bs (_ : 'a -> string) (u : 'a uvar_bs) = exfalso u
fun str_uvar_mt (_ : string list * string list -> 'mtype -> string) (_ : string list * string list) (u : ('bsort, 'mtype) uvar_mt) = exfalso u
fun str_uvar_i (_ : string list -> 'idx -> string) (_ : string list) (u : ('bsort, 'idx) uvar_i) = exfalso u
fun eq_uvar_i (u : ('bsort, 'idx) uvar_i, u' : ('bsort, 'idx) uvar_i) = exfalso u
end

structure NoUVarExpr = ExprFun (structure Var = IntVar structure UVar = NoUVar)

structure NoUVarSubst = struct
open Util
open NoUVarExpr
         
fun on_i_i on_v x n b =
  let
      fun f x n b =
	case b of
	    VarI (y, r) => VarI (on_v x n y, r)
	  | ConstIN n => ConstIN n
	  | ConstIT x => ConstIT x
          | UnOpI (opr, i, r) => UnOpI (opr, f x n i, r)
	  | BinOpI (opr, i1, i2) => BinOpI (opr, f x n i1, f x n i2)
	  | TTI r => TTI r
	  | TrueI r => TrueI r
	  | FalseI r => FalseI r
          | UVarI (u, _) => exfalso u
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
	  | BinOpI (opr, d1, d2) => BinOpI (opr, f x v d1, f x v d2)
	  | TrueI r => TrueI r
	  | FalseI r => FalseI r
	  | TTI r => TTI r
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
          | Quan (q, bs, name, p) => Quan (q, bs, name, f (x + 1) (shiftx_i_i 0 1 v) p)
          | RegionP (p, r) => RegionP (f x v p, r)
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
                              
local
    val changed = ref false
    fun unset () = changed := false
    fun set () = changed := true
    fun passi i =
	case i of
	    BinOpI (opr, i1, i2) =>
            (case opr of
	         MaxI =>
	         if eq_i i1 i2 then
		     (set ();
                      i1)
	         else
		     BinOpI (opr, passi i1, passi i2)
	       | MinI =>
	         if eq_i i1 i2 then
		     (set ();
                      i1)
	         else
		     BinOpI (opr, passi i1, passi i2)
	       | AddI => 
	         if eq_i i1 (T0 dummy) then
                     (set ();
                      i2)
	         else if eq_i i2 (T0 dummy) then
                     (set ();
                      i1)
	         else
		     BinOpI (opr, passi i1, passi i2)
	       | MinusI => 
	         if eq_i i2 (T0 dummy) then
                     (set ();
                      i1)
	         else
		     BinOpI (opr, passi i1, passi i2)
	       | MultI => 
	         if eq_i i1 (T0 dummy) then
                     (set ();
                      (T0 dummy))
	         else if eq_i i2 (T0 dummy) then
                     (set ();
                      (T0 dummy))
	         else if eq_i i1 (T1 dummy) then
                     (set ();
                      i2)
	         else if eq_i i2 (T1 dummy) then
                     (set ();
                      i1)
	         else
		     BinOpI (opr, passi i1, passi i2)
               | BigO =>
		 BinOpI (opr, passi i1, passi i2)
            )
          | UnOpI (opr, i, r) =>
            UnOpI (opr, passi i, r)
	  | _ => i

    fun passp p = 
	case p of
	    BinConn (opr, p1, p2) => 
            (case opr of
                 And =>
	         if eq_p p1 (True dummy) then
                     (set ();
                      p2)
	         else if eq_p p2 (True dummy) then
                     (set ();
                      p1)
	         else
	             BinConn (opr, passp p1, passp p2)
               | Or =>
	         if eq_p p1 (False dummy) then
                     (set ();
                      p2)
	         else if eq_p p2 (False dummy) then
                     (set ();
                      p1)
	         else
	             BinConn (opr, passp p1, passp p2)
               | _ =>
	         BinConn (opr, passp p1, passp p2)
            )
	  | BinPred (opr, i1, i2) => 
	    BinPred (opr, passi i1, passi i2)
          | Not (p, r) => Not (passp p, r)
          | RegionP (p, r) => 
            (* RegionP (passp p, r) *)
            (set (); p)
          | Quan (q, bs, name, p) => 
            (case q of
                 Forall =>
                 (case p of
	              True _ => p
                    | BinConn (Imply, p1, p2) =>
                      let
                          fun forget i =
                              SOME (forget_i_i 0 1 i) handle ForgetError _ => NONE
                          fun f i1 i2 =
                              if eq_i i1 (VarI (0, dummy)) then forget i2
                              else if eq_i i2 (VarI (0, dummy)) then forget i1
                              else NONE
                          val i = case p1 of
                                      BinPred (EpP, i1, i2) => f i1 i2
                                    | _ => NONE
                      in
                          case i of
                              SOME i => subst_i_p i p2
                            | _ => Quan (q, bs, name, passp p)
                      end
                    | _ =>
                     Quan (q, bs, name, passp p)
                 )
               | Exists =>
                 Quan (q, bs, name, passp p)
            )
	  | True _ => p
	  | False _ => p
                           
    fun until_unchanged f a = 
	let fun loop a =
	        let
                    val _ = unset ()
                    val a = f a
                in
		    if !changed then loop a
		    else a
	        end
        in
	    loop a
	end
in
val simp_i = until_unchanged passi
val simp_p = until_unchanged passp
end

end

