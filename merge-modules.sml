structure MergeModules = struct

open Expr
open Unpackage

infixr 0 $
       
fun merge_module ((mid, m(* , ctx as (sctx, kctx, cctx, tctx) *)), acc) =
  case m of
      ModComponents (decls, _) =>
      let
        val acc = unpackage_e_decls mid 0 acc
        val acc = unpackage_c_decls mid 0 acc
        val acc = unpackage_t_decls mid 0 acc
        val acc = unpackage_i_decls mid 0 acc
      in
        decls @ acc
      end
    | _ => raise Unimpl "merge_module"
        
fun do_merge_modules ms decls = foldr merge_module decls ms

fun remove_Top_DAbsIdx2_m m =
  case m of
      ModComponents (decls, r) =>
      let
        fun on_decl d =
          case d of
              DAbsIdx2 (name, Outer s, Outer i) =>
              let
                val () = println "Warning: can't translate module-level [absidx] yet. They will be converted to [idx]"
              in
                DIdxDef (name, Outer $ SOME s, Outer i)
              end
            | _ => d
        val decls = map on_decl decls
      in
        ModComponents (decls, r)
      end
    | _ => raise Unimpl "remove_Top_AbsIdx2"
  

open RemoveOpen
       
fun merge_modules ms decls =
  let
    val decls = remove_DOpen_decls decls
    val ms = map (mapSnd remove_DOpen_m) ms
    val ms = map (mapSnd remove_Top_DAbsIdx2_m) ms
  in
    do_merge_modules ms decls
  end

fun prog2modules p = map (curry mapPair fst (fn TopModBind m => m
                                      | _ => raise Impossible "prog2modules")) p
                         
fun merge_prog p = merge_modules $ prog2modules p

end
