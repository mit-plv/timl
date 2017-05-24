(* basic index sort *)
signature BASE_SORTS = sig
  
  type base_sort
       
end

signature IDX = sig
  
  structure UVar : UVAR
  structure BaseSorts : BASE_SORTS
                          
  type long_id
  type name
         
  datatype bsort = 
           Base of BaseSorts.base_sort 
           | BSArrow of bsort * bsort
           | UVarBS of bsort UVar.uvar_bs
                             
  datatype idx =
	   VarI of long_id
           | IConst of Operators.idx_const * Region.region
           | UnOpI of Operators.idx_un_op * idx * Region.region
           | BinOpI of Operators.idx_bin_op * idx * idx
           | Ite of idx * idx * idx * Region.region
           | IAbs of bsort * (name * idx) Bind.ibind * Region.region
           | UVarI of (bsort, idx) UVar.uvar_i * Region.region

  datatype prop =
	   PTrueFalse of bool * Region.region
           | BinConn of Operators.bin_conn * prop * prop
           | Not of prop * Region.region
	   | BinPred of Operators.bin_pred * idx * idx
           | Quan of (idx -> unit) option (*for linking idx inferer with types*) Operators.quan * bsort * (name * prop) Bind.ibind * Region.region

  datatype sort =
	   Basic of bsort * Region.region
	   | Subset of (bsort * Region.region) * (name * prop) Bind.ibind * Region.region
           | UVarS of (bsort, sort) UVar.uvar_s * Region.region
           (* [SAbs] and [SApp] are just for higher-order unification *)
           | SAbs of bsort * (name * sort) Bind.ibind * Region.region
           | SApp of sort * idx
                              
end
