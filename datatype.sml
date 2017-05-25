functor DatatypeFn (structure Idx : IDX type var) = struct

open Idx
open Bind

type 'mtype constr_core = (sort, string, 'mtype * idx list) ibinds
type 'mtype constr_decl = string * 'mtype constr_core * region
type 'mtype constr = var(*family*) * string list(*type argument names*) * 'mtype constr_core

type 'mtype datatype_def = string * string list * bsort list * 'mtype constr_decl list * region

end
