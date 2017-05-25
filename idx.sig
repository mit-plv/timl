signature IDX = sig
  
  structure UVarI : UVAR_I
  type base_sort
  type var
  type name
  type region
         
  datatype bsort = 
           Base of base_sort 
           | BSArrow of bsort * bsort
           | UVarBS of bsort UVarI.uvar_bs
                             
  datatype idx =
	   VarI of var
           | IConst of Operators.idx_const * region
           | UnOpI of Operators.idx_un_op * idx * region
           | BinOpI of Operators.idx_bin_op * idx * idx
           | Ite of idx * idx * idx * region
           | IAbs of bsort * (name * idx) Bind.ibind * region
           | UVarI of (bsort, idx) UVarI.uvar_i * region

  datatype prop =
	   PTrueFalse of bool * region
           | BinConn of Operators.bin_conn * prop * prop
           | Not of prop * region
	   | BinPred of Operators.bin_pred * idx * idx
           | Quan of (idx -> unit) option (*for linking idx inferer with types*) Operators.quan * bsort * (name * prop) Bind.ibind * region

  datatype sort =
	   Basic of bsort * region
	   | Subset of (bsort * region) * (name * prop) Bind.ibind * region
           | UVarS of (bsort, sort) UVarI.uvar_s * region
           (* [SAbs] and [SApp] are just for higher-order unification *)
           | SAbs of bsort * (name * sort) Bind.ibind * region
           | SApp of sort * idx
                              
end
