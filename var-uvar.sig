(* variables *)
signature VAR = sig
  type var
  val eq_v : var * var -> bool
end

(* unification variables ('uvars') for indices and sorts *)                  
signature UVAR_I = sig
  (* all uvars denotate closed entities, which means they cannot be instantiated with things that contain variables (even module variables) *)
  type 'bsort uvar_bs
  type ('bsort, 'idx) uvar_i
  type ('bsort, 'sort) uvar_s
  val str_uvar_bs : ('a -> string) -> 'a uvar_bs -> string
  val str_uvar_i : ('bsort -> string) * ('idx -> string) -> ('bsort, 'idx) uvar_i -> string
  val str_uvar_s : ('sort -> string) -> ('bsort, 'sort) uvar_s -> string
  val eq_uvar_i : ('bsort, 'idx) uvar_i * ('bsort, 'idx) uvar_i -> bool
  val eq_uvar_bs : 'bsort uvar_bs * 'bsort uvar_bs -> bool
  val eq_uvar_s : ('bsort, 'sort) uvar_s * ('bsort, 'sort) uvar_s -> bool
end

(* unification variables ('uvars') for types *)                  
signature UVAR_T = sig
  (* all uvars denotate closed entities, which means they cannot be instantiated with things that contain variables (even module variables) *)
  type ('sort, 'kind, 'mtype) uvar_mt
  val str_uvar_mt : ('sort -> string) * ('kind -> string) * ('mtype -> string) -> ('sort, 'kind, 'mtype) uvar_mt -> string
  val eq_uvar_mt : ('sort, 'kind, 'mtype) uvar_mt * ('sort, 'kind, 'mtype) uvar_mt -> bool
end

