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

signature SHIFTABLE_VAR = sig
  type var
  val shiftx_var : int -> int -> var -> var
  val forget_var : int -> int -> var -> var
end
                                                      
functor IdxShiftFn (structure Idx : IDX
                    structure ShiftableVar : SHIFTABLE_VAR
                    sharing type Idx.var = ShiftableVar.var
                   ) = struct

open Idx
open ShiftableVar
open ShiftUtil
       
infixr 0 $
         
(* generic traversers for both 'shift' and 'forget' *)
         
structure IdxVisitor = IdxVisitorFn (structure S = Idx
                                     structure T = Idx)
open IdxVisitor
                                         
fun on_i_idx_visitor_vtable cast (on_var, n) : ('this, int) idx_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
    fun visit_var this env data = on_var env n data
  in
    default_idx_visitor_vtable
      cast
      extend_i
      visit_var
      visit_noop
      visit_noop
      visit_noop
      visit_noop
  end

fun new_on_i_idx_visitor a = new_idx_visitor on_i_idx_visitor_vtable a
    
fun on_i_i on_var x n b =
  let
    val visitor as (IdxVisitor vtable) = new_on_i_idx_visitor (on_var, n)
  in
    #visit_idx vtable visitor x b
  end
    
fun on_i_p on_var x n b =
  let
    val visitor as (IdxVisitor vtable) = new_on_i_idx_visitor (on_var, n)
  in
    #visit_prop vtable visitor x b
  end
    
fun on_i_s on_var x n b =
  let
    val visitor as (IdxVisitor vtable) = new_on_i_idx_visitor (on_var, n)
  in
    #visit_sort vtable visitor x b
  end
    
(* fun on_i_i on_v x n b = *)
(*   let *)
(*     fun f x n b = *)
(*       case b of *)
(* 	  VarI y => VarI $ on_v x n y *)
(*         | IConst c => IConst c *)
(*         | UnOpI (opr, i, r) => UnOpI (opr, f x n i, r) *)
(* 	| BinOpI (opr, i1, i2) => BinOpI (opr, f x n i1, f x n i2) *)
(*         | Ite (i1, i2, i3, r) => Ite (f x n i1, f x n i2, f x n i3, r) *)
(*         | IAbs (b, bind, r) => IAbs (b, on_i_ibind f x n bind, r) *)
(*         | UVarI a => b (* uvars are closed, so no need to deal with *) *)
(*   in *)
(*     f x n b *)
(*   end *)

(* fun on_i_p on_i_i x n b = *)
(*   let *)
(*     fun f x n b = *)
(*       case b of *)
(* 	  PTrueFalse b => PTrueFalse b *)
(*         | Not (p, r) => Not (f x n p, r) *)
(* 	| BinConn (opr, p1, p2) => BinConn (opr, f x n p1, f x n p2) *)
(* 	| BinPred (opr, d1, d2) => BinPred (opr, on_i_i x n d1, on_i_i x n d2) *)
(*         | Quan (q, bs, bind, r) => Quan (q, bs, on_i_ibind f x n bind, r) *)
(*   in *)
(*     f x n b *)
(*   end *)

(* fun on_i_s on_i_i on_i_p x n b = *)
(*   let *)
(*     fun f x n b = *)
(*       case b of *)
(* 	  Basic s => Basic s *)
(* 	| Subset (s, bind, r) => Subset (s, on_i_ibind on_i_p x n bind, r) *)
(*         | UVarS a => b *)
(*         | SAbs (b, bind, r) => SAbs (b, on_i_ibind f x n bind, r) *)
(*         | SApp (s, i) => SApp (f x n s, on_i_i x n i) *)
(*   in *)
(*     f x n b *)
(*   end *)

(* shift *)
    
fun shiftx_i_i x n b = on_i_i shiftx_var x n b
fun shift_i_i b = shiftx_i_i 0 1 b

fun shiftx_i_p x n b = on_i_p shiftx_var x n b
fun shift_i_p b = shiftx_i_p 0 1 b

fun shiftx_i_s x n b = on_i_s shiftx_var x n b
fun shift_i_s b = shiftx_i_s 0 1 b

(* forget *)

fun forget_i_i x n b = on_i_i forget_var x n b
fun forget_i_p x n b = on_i_p forget_var x n b
fun forget_i_s x n b = on_i_s forget_var x n b
                              
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
