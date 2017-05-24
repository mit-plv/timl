functor MicroTiMLFn (Idx : IDX) = struct
open Idx
       
       (* kind *)
       Inductive kind :=
   | KType
   | KArrow (b : bsort) (k : kind)
   | KArrowT (k1 k2 : kind)
             .

             (* type *)
             Inductive ty :=
   | TVar (x : var)
   | TConst (cn : ty_const)
   | TBinOp (opr : ty_bin_op) (c1 c2 : ty)
   | TArrow (t1 : ty) (i : idx) (t2 : ty)
   | TAbsI (s : bsort) (t : ty)
   | TAppI (t : ty) (b : bsort) (i : idx)
   | TQuan (q : quan) (k : kind) (t : ty)
   | TQuanI (q : quan) (s : sort) (t : ty)
   | TRec (k : kind) (t : ty)
   | TNat (i : idx)
   | TArr (t : ty) (len : idx)
   | TAbsT (k : kind) (t : ty)
   | TAppT (t1 t2 : ty)
           .

end
