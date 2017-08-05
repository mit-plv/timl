structure ToStringUtil = struct

type scontext = string list
type kcontext = string list 
type ccontext = string list
type tcontext = string list
type context = scontext * kcontext * ccontext * tcontext
val empty_ctx = ([], [], [], [])
type sigcontext = (string * context) list
type global_context = context Gctx.map
                                     
end
