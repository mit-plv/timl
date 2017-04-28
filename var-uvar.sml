(* variables *)
signature VAR = sig
  type var
  val str_v : string list -> var -> string
  val lookup_module : (string * (string list * string list * string list * string list)) list -> var -> string * (string list * string list * string list * string list)
  val str_long_id : (string list * string list * string list * string list -> string list) -> (string * (string list * string list * string list * string list)) list -> string list -> ((var * Region.region) option * (var * Region.region)) -> string
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
  type 'sort uvar_s
  type ('sort, 'kind, 'mtype) uvar_mt
  val str_uvar_bs : ('a -> string) -> 'a uvar_bs -> string
  val str_uvar_i : ('idx -> string) -> ('bsort, 'idx) uvar_i -> string
  val str_uvar_s : ('sort -> string) -> 'sort uvar_s -> string
  val str_uvar_mt : ('mtype -> string) -> ('sort, 'kind, 'mtype) uvar_mt -> string
  val eq_uvar_i : ('bsort, 'idx) uvar_i * ('bsort, 'idx) uvar_i -> bool
  val eq_uvar_bs : 'bsort uvar_bs * 'bsort uvar_bs -> bool
end

