structure MicroTiMLExPostProcess = struct

open MicroTiMLExLongId
open MicroTiMLExUtil

infixr 0 $
         
fun post_process_expr_visitor_vtable cast () =
  let
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_EMatchUnfold this env (e, bind) =
      #visit_expr (cast this) this env $ ELet (EUnfold e, bind)
    val vtable = override_visit_EMatchUnfold vtable visit_EMatchUnfold
    fun visit_EMatchPair this env (e, bind) =
      let
        val () = case e of
                     EVar _ => ()
                   | _ => raise Impossible "post-process: matchee must be EVar"
        val (name1, bind) = unBind bind
        val (name2, e_body) = unBind bind
      in
        #visit_expr (cast this) this env $ ELet (EFst e, Bind (name1, ELet (ESnd $ shift01_e_e e, Bind (name2, e_body))))
      end
    val vtable = override_visit_EMatchPair vtable visit_EMatchPair
    fun visit_ELet this env (data as (e, bind)) =
      case e of
          EVar _ =>
          let
            val (_, e_body) = unBind bind
          in
            #visit_expr (cast this) this env $ subst0_e_e e e_body
          end
        | _ =>
          let
            val super_vtable = vtable
          in
            #visit_ELet super_vtable this env data
          end
    val vtable = override_visit_ELet vtable visit_ELet
                                     (* todo: add a simplification for ECase where if the two branches are identical and don't mention the local variable, combine them and remove ECase *)
  in
    vtable
  end

fun new_post_process_expr_visitor params = new_expr_visitor post_process_expr_visitor_vtable params
    
fun post_process_e b =
  let
    val visitor as (ExprVisitor vtable) = new_post_process_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end
    
end
