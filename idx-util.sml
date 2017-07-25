functor IdxUtilFn (structure Idx : IDX where type name = string * Region.region
                   val dummy : Idx.region
                  ) = struct

open Idx
open Operators
open Util
       
infixr 0 $

(* some shorthands *)

fun ConstIT (s, r) = IConst (ICTime s, r)
fun ConstIN (d, r) = IConst (ICNat d, r)
fun T0 r = ConstIT ("0.0", r)
fun T1 r = ConstIT ("1.0", r)
fun N0 r = ConstIN (0, r)
fun N1 r = ConstIN (1, r)
fun DivI (i, (n, r)) = UnOpI (IUDiv n, i, r)
fun ExpI (i, (s, r)) = UnOpI (IUExp s, i, r)
fun TrueI r = IConst (ICBool true, r)
fun FalseI r = IConst (ICBool false, r)
fun TTI r = IConst (ICTT, r)
fun AdmitI r = IConst (ICAdmit, r)
fun True r = PTrueFalse (true, r)
fun False r = PTrueFalse (false, r)

fun PEq (a, b) = BinPred (EqP, a, b)             

(* notations *)
         
infix 9 %@
fun a %@ b = BinOpI (IApp, a, b)
infix 8 %^
fun a %^ b = BinOpI (ExpNI, a, b)
infix 7 %*
fun a %* b = BinOpI (MultI, a, b)
infix 6 %+ 
fun a %+ b = BinOpI (AddI, a, b)
infix 4 %<=
fun a %<= b = BinPred (LeP, a, b)
infix 4 %>=
fun a %>= b = BinPred (GeP, a, b)
infix 4 %=
fun a %= b = PEq (a, b)
infixr 3 /\
fun a /\ b = BinConn (And, a, b)
infixr 2 \/
fun a \/ b = BinConn (Or, a, b)
infixr 1 -->
fun a --> b = BinConn (Imply, a, b)
infix 1 <->
fun a <-> b = BinConn (Iff, a, b)
                      
fun combine_And ps = foldl' (fn (p, acc) => acc /\ p) (True dummy) ps
                            
fun collect_BinOpI opr i =
  case i of
      BinOpI (opr', i1, i2) =>
      if opr' = opr then
        collect_BinOpI opr i1 @ collect_BinOpI opr i2
      else [i]
    | _ => [i]
             
fun collect_BinOpI_left opr i =
  case i of
      BinOpI (opr', i1, i2) =>
      if opr' = opr then
        collect_BinOpI_left opr i1 @ [i2]
      else [i]
    | _ => [i]
             
val collect_AddI = collect_BinOpI AddI
val collect_AddI_left = collect_BinOpI_left AddI
val collect_MultI = collect_BinOpI MultI
                                   
fun combine_AddI zero is = foldl' (fn (i, acc) => acc %+ i) zero is
fun combine_AddI_Time is = combine_AddI (T0 dummy) is
fun combine_AddI_Nat is = combine_AddI (N0 dummy) is
fun combine_AddI_nonempty i is = combine_AddI_Time (i :: is)
fun combine_MultI is = foldl' (fn (i, acc) => acc %* i) (T1 dummy) is
                                            
fun collect_BinConn opr i =
  case i of
      BinConn (opr', i1, i2) =>
      if opr' = opr then
        collect_BinConn opr i1 @ collect_BinConn opr i2
      else [i]
    | _ => [i]
             
val collect_And = collect_BinConn And

fun collect_IApp i =
  case collect_BinOpI_left IApp i of
      f :: args => (f, args)
    | [] => raise Impossible "collect_IApp(): null"

open Bind
       
fun collect_IAbs i =
  case i of
      IAbs (b, Bind ((name, _), i), _) =>
      let
        val (bs_names, i) = collect_IAbs i
      in
        ((b, name) :: bs_names, i)
      end
    | _ => ([], i)

fun is_time_fun b =
  case b of
      Base Time => SOME 0
    | BSArrow (Base Nat, b) =>
      opt_bind (is_time_fun b) (fn n => opt_return $ 1 + n)
    | _ => NONE
             
end
