structure MergeModules = struct

open ExprVisitor
open Expr
open Unpackage

infixr 0 $
infixr 0 !!

fun collect_names_expr_visitor_vtable cast () =
  let
    fun extend_i this (sctx, kctx, cctx, tctx) name = (Name2str name :: sctx, kctx, cctx, tctx)
    fun extend_t this (sctx, kctx, cctx, tctx) name = (sctx, Name2str name :: kctx, cctx, tctx)
    fun extend_c this (sctx, kctx, cctx, tctx) name = (sctx, kctx, Name2str name :: cctx, tctx)
    fun extend_e this (sctx, kctx, cctx, tctx) name = (sctx, kctx, cctx, Name2str name :: tctx)
  in
    default_expr_visitor_vtable
      cast
      extend_i
      extend_t
      extend_c
      extend_e
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
  end         
         
fun new_collect_names_expr_visitor a = new_expr_visitor collect_names_expr_visitor_vtable a
    
fun collect_names_mod b =
  snd $ visit_mod_acc (new_collect_names_expr_visitor ()) (b, ([], [], [], []))
    
fun spec2decl mid (sctx, kctx, cctx, tctx) spec =
  let
    fun V n = QID ((mid, dummy), (n, dummy))
  in
    case spec of
        SpecVal (ename, t) =>
        let
          val n = indexOf (curry op= $ fst ename) tctx !! (fn () => raise Impossible "spec2decl/SpecVal")
          val e = EVar (V n, true)
                       (* todo: use [t] to add type annotations *)
        in
          MakeDVal (ename, [], e, dummy)
        end
      | SpecIdx (iname, s) =>
        let
          val n = indexOf (curry op= $ fst iname) sctx !! (fn () => raise Impossible "spec2decl/SpecIdx")
        in
          MakeDIdxDef (iname, SOME s, VarI $ V n)
        end
      | SpecType (tname, k) =>
        let
          val n = indexOf (curry op= $ fst tname) kctx !! (fn () => raise Impossible "spec2decl/SpecType")
        in
          MakeDTypeDef (tname, MtVar $ V n)
        end
      | SpecTypeDef (tname, t) =>
        (* we don't allow [datatype] in signature for now, so no special treatment of [TDatatype] *)
        MakeDTypeDef (tname, t)
  end
      
      
fun merge_module ((mid, m), acc) =
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
    | ModTransparentAsc (m, _) => merge_module ((mid, m), acc)
    | ModSeal (m, (specs, _)) =>
      let
        val names = collect_names_mod m
        val mid' = prefix "__" mid
        val decls = map (spec2decl mid' names) specs
        val acc = merge_module ((mid, ModComponents (decls, dummy)), acc)
        val acc = merge_module ((mid', m), acc)
      in
        acc
      end
        
fun do_merge_modules ms decls = foldr merge_module decls ms

fun remove_top_DAbsIdx2_m m =
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
    | ModSeal (m, sg) => ModSeal (remove_top_DAbsIdx2_m m, sg)
    | ModTransparentAsc (m, sg) => ModTransparentAsc (remove_top_DAbsIdx2_m m, sg)
  

open RemoveOpen
       
fun merge_modules ms decls =
  let
    val decls = remove_DOpen_decls decls
    val ms = map (mapSnd remove_DOpen_m) ms
    val ms = map (mapSnd remove_top_DAbsIdx2_m) ms
  in
    do_merge_modules ms decls
  end

fun prog2modules p = map ((fn (name, TopModBind m) => (fst name, m)
                          | (name, TopFunctorBind ((arg_name, _), _)) => raise Unimpl $ sprintf "prog2modules: $ = TopFunctorBind ($ : ...)" [fst name, fst arg_name]
                          | (name, TopFunctorApp (name1, name2)) => raise Unimpl $ sprintf "prog2modules: $ = TopFunctorApp ($, $)" [fst name, fst name1, fst name2]
                         )) p
                         
fun merge_prog p = merge_modules $ prog2modules p

end
