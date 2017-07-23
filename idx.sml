signature IDX_PARAMS = sig
  structure UVarI : UVAR_I
  type base_sort
  type var
  type name
  type region
  type 'idx exists_anno
end         

functor IdxFn (Params : IDX_PARAMS) =
struct

open Params
open UVarI
open Bind
open Operators
                        
(* basic index sort with arrow and uvar *)
datatype bsort = 
         Base of base_sort 
         | BSArrow of bsort * bsort
         | UVarBS of bsort uvar_bs
                           
datatype idx =
	 VarI of var
         | IConst of idx_const * region
         | UnOpI of idx_un_op * idx * region
         | BinOpI of idx_bin_op * idx * idx
         | Ite of idx * idx * idx * region
         | IAbs of bsort * (name * idx) ibind * region
         | UVarI of (bsort, idx) uvar_i * region

datatype prop =
	 PTrueFalse of bool * region
         | BinConn of bin_conn * prop * prop
         | Not of prop * region
	 | BinPred of bin_pred * idx * idx
         | Quan of idx exists_anno (*for linking idx inferer with types*) quan * bsort * (name * prop) ibind * region

datatype sort =
	 Basic of bsort * region
	 | Subset of (bsort * region) * (name * prop) ibind * region
         | UVarS of (bsort, sort) uvar_s * region
         (* [SAbs] and [SApp] are just for higher-order unification *)
         | SAbs of bsort * (name * sort) ibind * region
         | SApp of sort * idx
                            
end

functor TestIdxFnSignatures (Params : IDX_PARAMS) = struct
structure M : IDX = IdxFn (Params)
end

functor IdxUtilFn (structure Idx : IDX
                   val dummy : Idx.region
                  ) = struct

open Idx
open Operators

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
                            
end
