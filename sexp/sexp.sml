structure SExp = struct
open Region

datatype sexp =
         Atom of string
         | String of string
         | List of sexp list
                      
type reporter = string * pos * pos -> unit

open Util
         
fun str_sexp e =
  case e of
      Atom s => s
    | String s => surround "\"" "\"" s
    | List es => (surround "(" ")" o join " " o map str_sexp) es
                                                              
end

