signature TYPE = sig

  structure Idx : IDX
  structure UVarT : UVAR_T
  type base_type
  type var
  type kind
  type name
  type region
         
  (* monotypes *)
  datatype mtype = 
	   Arrow of mtype * Idx.idx * mtype
           | TyNat of Idx.idx * region
           | TyArray of mtype * Idx.idx
	   | BaseType of base_type * region
           | Unit of region
	   | Prod of mtype * mtype
	   | UniI of Idx.sort * (name * mtype) Bind.ibind * region
           | MtVar of var
           (* type-level computations *)
           | MtAbs of kind * (name * mtype) Bind.tbind * region
           | MtApp of mtype * mtype
           | MtAbsI of Idx.bsort * (name * mtype) Bind.ibind  * region
           | MtAppI of mtype * Idx.idx
           | UVar of (Idx.bsort, kind, mtype) UVarT.uvar_mt * region

end
