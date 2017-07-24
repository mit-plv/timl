signature EXPR_EX = sig
  structure Idx : IDX
  structure Type : TYPE
  sharing type Type.var = Idx.var
  sharing type Type.idx = Idx.idx
  sharing type Type.sort = Idx.sort
  include EXPR where type kind = Type.kind
  sharing type var = Idx.var
  sharing type idx = Idx.idx
  sharing type sort = Idx.sort
  sharing type mtype = Type.mtype
  sharing type ty = Type.ty
  sharing type cvar = var
end

