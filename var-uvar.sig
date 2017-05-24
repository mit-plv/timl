(* variables *)
signature VAR = sig
  type var
  type name_context = string list * string list * string list * string list
  type global_name_context = name_context Gctx.map
  val str_v : string list -> var -> string
  val str_raw_v : var -> string
  val lookup_module : global_name_context -> string -> string * name_context
  val str_long_id : (name_context -> string list) -> global_name_context -> string list -> ((string * Region.region) option * (var * Region.region)) -> string
  val eq_v : var * var -> bool
                            
  val shiftx_v : int -> int -> var -> var
  val forget_v : (int * string -> exn) -> int -> int -> var -> var
  val substx_v : (var -> 'value) -> int -> (unit -> 'value) -> var -> 'value

  val int2var : int -> var
  val var2int : var -> int
end

(* unification variables ('uvars') *)                  
signature UVAR = sig
  (* all uvars denotate closed entities, which means they cannot be instantiated with things that contain variables (even module variables) *)
  type 'bsort uvar_bs
  type ('bsort, 'idx) uvar_i
  type ('bsort, 'sort) uvar_s
  type ('sort, 'kind, 'mtype) uvar_mt
  val str_uvar_bs : ('a -> string) -> 'a uvar_bs -> string
  val str_uvar_i : ('bsort -> string) * ('idx -> string) -> ('bsort, 'idx) uvar_i -> string
  val str_uvar_s : ('sort -> string) -> ('bsort, 'sort) uvar_s -> string
  val str_uvar_mt : ('sort -> string) * ('kind -> string) * ('mtype -> string) -> ('sort, 'kind, 'mtype) uvar_mt -> string
  val eq_uvar_i : ('bsort, 'idx) uvar_i * ('bsort, 'idx) uvar_i -> bool
  val eq_uvar_bs : 'bsort uvar_bs * 'bsort uvar_bs -> bool
  val eq_uvar_s : ('bsort, 'sort) uvar_s * ('bsort, 'sort) uvar_s -> bool
  val eq_uvar_mt : ('sort, 'kind, 'mtype) uvar_mt * ('sort, 'kind, 'mtype) uvar_mt -> bool
end

