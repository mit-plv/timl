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

signature UVAR = sig
  type 'bsort uvar_bs
  type ('bsort, 'idx) uvar_i
  type 'sort uvar_s
  type 'mtype uvar_mt
  val str_uvar_bs : ('a -> string) -> 'a uvar_bs -> string
  val str_uvar_i : (string list -> 'idx -> string) -> string list -> ('bsort, 'idx) uvar_i -> string
  val str_uvar_mt : (string list * string list -> 'mtype -> string) -> string list * string list -> 'mtype uvar_mt -> string
  val eq_uvar_i : ('bsort, 'idx) uvar_i * ('bsort, 'idx) uvar_i -> bool

  (* val on_UVarI : ('bsort, 'idx) uvar_i * Region.region -> 'idx *)
  (* val on_UVarS : 'sort uvar_s * Region.region -> 'sort *)
  (* val on_i_UVar : 'mtype uvar_mt * Region.region -> 'mtype *)
  (* val on_t_UVar : 'mtype uvar_mt * Region.region -> 'mtype *)
  val shiftx_i_UVarI : (('bsort, 'idx) uvar_i * Region.region -> 'idx) -> (int -> int -> 'idx -> 'idx) -> int -> int -> ('bsort, 'idx) uvar_i * Region.region -> 'idx
  val shiftx_i_UVarS : ('sort uvar_s * Region.region -> 'sort) -> (int -> int -> 'sort -> 'sort) -> int -> int -> 'sort uvar_s * Region.region -> 'sort
  val shiftx_i_UVar : (int -> int -> 'mtype -> 'mtype) -> ('mtype uvar_mt * Region.region -> 'mtype) -> (int -> int -> 'mtype -> 'mtype) -> int -> int -> 'mtype uvar_mt * Region.region -> 'mtype
  val shiftx_t_UVar : (int -> int -> 'mtype -> 'mtype) -> ('mtype uvar_mt * Region.region -> 'mtype) -> (int -> int -> 'mtype -> 'mtype) -> int -> int -> 'mtype uvar_mt * Region.region -> 'mtype
                                                                                                                                                                                              
  val forget_i_UVarI : (int -> int -> 'idx -> 'idx) -> (int * string -> exn) -> (('bsort, 'idx) uvar_i * Region.region -> 'idx) -> (int -> int -> 'idx -> 'idx) -> int -> int -> ('bsort, 'idx) uvar_i * Region.region -> 'idx
  val forget_i_UVarS : (int -> int -> 'sort -> 'sort) -> (int * string -> exn) -> ('sort uvar_s * Region.region -> 'sort) -> (int -> int -> 'sort -> 'sort) -> int -> int -> 'sort uvar_s * Region.region -> 'sort
  val forget_i_UVar : (int -> int -> 'mtype -> 'mtype) -> (int -> int -> 'mtype -> 'mtype) -> (int * string -> exn) -> ('mtype uvar_mt * Region.region -> 'mtype) -> (int -> int -> 'mtype -> 'mtype) -> int -> int -> 'mtype uvar_mt * Region.region -> 'mtype
  val forget_t_UVar : (int -> int -> 'mtype -> 'mtype) -> (int -> int -> 'mtype -> 'mtype) -> (int * string -> exn) -> ('mtype uvar_mt * Region.region -> 'mtype) -> (int -> int -> 'mtype -> 'mtype) -> int -> int -> 'mtype uvar_mt * Region.region -> 'mtype

  val substx_i_UVarI : (int -> int -> 'idx -> 'idx) -> (('bsort, 'idx) uvar_i * Region.region -> 'idx) -> (int -> 'idx -> 'idx -> 'idx) -> int -> 'idx -> ('bsort, 'idx) uvar_i * Region.region -> 'idx
  val substx_i_UVarS : (int -> int -> 'sort -> 'sort) -> ('sort uvar_s * Region.region -> 'sort) -> (int -> 'idx -> 'sort -> 'sort) -> int -> 'idx -> 'sort uvar_s * Region.region -> 'sort
  val substx_i_UVar : (int -> int -> 'mtype -> 'mtype) -> (int -> int -> 'mtype -> 'mtype) -> ('mtype uvar_mt * Region.region -> 'mtype) -> (int -> 'idx -> 'mtype -> 'mtype) -> int -> 'idx -> 'mtype uvar_mt * Region.region -> 'mtype
  val substx_t_UVar : (int -> int -> 'mtype -> 'mtype) -> (int -> int -> 'mtype -> 'mtype) -> ('mtype uvar_mt * Region.region -> 'mtype) -> (int -> 'mtype -> 'mtype -> 'mtype) -> int -> 'mtype -> 'mtype uvar_mt * Region.region -> 'mtype
end

