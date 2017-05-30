signature IDX_PARAMS = sig
  structure UVarI : UVAR_I
  type base_sort
  type var
  type name
  type region
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
         | Quan of (idx -> unit) option (*for linking idx inferer with types*) quan * bsort * (name * prop) ibind * region

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

signature SHIFTABLE_VAR = sig
  type var
  val shiftx_var : int -> int -> var -> var
  val forget_var : int -> int -> var -> var
end
                                                      
functor IdxSubstFn (structure Idx : IDX
                    structure ShiftableVar : SHIFTABLE_VAR
                    sharing type Idx.var = ShiftableVar.var
                   ) = struct

open Idx
open ShiftableVar
open ShiftUtil
       
infixr 0 $
         
(* generic traversers for both 'shift' and 'forget' *)
         
fun on_i_i on_v x n b =
  let
    fun f x n b =
      case b of
	  VarI y => VarI $ on_v x n y
        | IConst c => IConst c
        | UnOpI (opr, i, r) => UnOpI (opr, f x n i, r)
	| BinOpI (opr, i1, i2) => BinOpI (opr, f x n i1, f x n i2)
        | Ite (i1, i2, i3, r) => Ite (f x n i1, f x n i2, f x n i3, r)
        | IAbs (b, bind, r) => IAbs (b, on_i_ibind f x n bind, r)
        | UVarI a => b (* uvars are closed, so no need to deal with *)
  in
    f x n b
  end

fun on_i_p on_i_i x n b =
  let
    fun f x n b =
      case b of
	  PTrueFalse b => PTrueFalse b
        | Not (p, r) => Not (f x n p, r)
	| BinConn (opr, p1, p2) => BinConn (opr, f x n p1, f x n p2)
	| BinPred (opr, d1, d2) => BinPred (opr, on_i_i x n d1, on_i_i x n d2)
        | Quan (q, bs, bind, r) => Quan (q, bs, on_i_ibind f x n bind, r)
  in
    f x n b
  end

fun on_i_s on_i_i on_i_p x n b =
  let
    fun f x n b =
      case b of
	  Basic s => Basic s
	| Subset (s, bind, r) => Subset (s, on_i_ibind on_i_p x n bind, r)
        | UVarS a => b
        | SAbs (b, bind, r) => SAbs (b, on_i_ibind f x n bind, r)
        | SApp (s, i) => SApp (f x n s, on_i_i x n i)
  in
    f x n b
  end

(* shift *)
    
fun shiftx_i_i x n b = on_i_i shiftx_var x n b
fun shift_i_i b = shiftx_i_i 0 1 b

fun shiftx_i_p x n b = on_i_p shiftx_i_i x n b
fun shift_i_p b = shiftx_i_p 0 1 b

fun shiftx_i_s x n b = on_i_s shiftx_i_i shiftx_i_p x n b
fun shift_i_s b = shiftx_i_s 0 1 b

(* forget *)

fun forget_i_i x n b = on_i_i forget_var x n b
fun forget_i_p x n b = on_i_p forget_i_i x n b
fun forget_i_s x n b = on_i_s forget_i_i forget_i_p x n b
                              
end
