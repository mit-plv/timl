(* micro-timl extended *)

structure MicroTiMLEx = struct

open MicroTiML
open Unbound
       
infixr 0 $
         
datatype ('var, 'bsort, 'idx, 'sort, 'ty) expr =
         EVar of 'var
         | EConst of Operators.expr_const
         | ELoc of loc
         | EUnOp of expr_un_op * ('var, 'bsort, 'idx, 'sort, 'ty) expr
         | EBinOp of expr_bin_op * ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr
         | EWrite of ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr
         | ECase of ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind
         | EAbs of ('ty, ('var, 'bsort, 'idx, 'sort, 'ty) expr) ebind_anno
         | ERec of ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind
         | EAbsT of ('var, 'bsort, 'idx, 'sort, 'ty) expr tbind
         | EAppT of ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort) ty
         | EAbsI of ('sort, ('var, 'bsort, 'idx, 'sort, 'ty) expr) ibind_anno
         | EAppI of ('var, 'bsort, 'idx, 'sort, 'ty) expr * 'idx
         | EPack of ('var, 'bsort, 'idx, 'sort) ty * ('var, 'bsort, 'idx, 'sort, 'ty) expr
         | EUnpack of ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind tbind
         | EPackI of 'idx * ('var, 'bsort, 'idx, 'sort, 'ty) expr
         | EUnpackI of ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind ibind
         | EAscTime of ('var, 'bsort, 'idx, 'sort, 'ty) expr * 'idx (* time ascription *)
         | EAscType of ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort) ty (* type ascription *)
         | ENever of ('var, 'bsort, 'idx, 'sort) ty
         | ELet of ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind
         | EMatchSum of ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind list
         | EMatchPair of ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind ebind
         | EMatchUnfold of ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind
         | EMatchUnpackI of ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind ibind

fun get_bind (Abs (Binder name, Rebind (Outer t))) = (name, t)
fun get_name s = fst $ snd s
                 
structure TextToken =
  struct
    type token = string
    type style = unit
    fun string t = t
    fun style t = ()
    fun size t = String.size t
  end

(* structure PP = PPDebugFn(PPStreamFn( *)
(*     structure Token = TextToken *)
(*     structure Device = SimpleTextIODev)) *)

structure PP = PPStreamFn(
  structure Token = TextToken
  structure Device = SimpleTextIODev)

fun withPP (name, wid, dst) ppFn = let
      (* val saveStrm = !PP.debugStrm *)
      (* val _ = PP.debugStrm := TextIO.openAppend("debug-out.txt") *)
      val ppStrm =
	  PP.openStream(SimpleTextIODev.openDev{dst=dst, wid=wid})
      in
	(* print(concat[name, ": width = ", Int.toString wid, "\n"]); *)
	ppFn ppStrm;
	PP.closeStream ppStrm;
	TextIO.output (dst, "\n")
	(* TextIO.closeOut (!PP.debugStrm); *)
	(* PP.debugStrm := saveStrm *)
end

fun t40 () = withPP ("Test 20 [C code]", 20, TextIO.stdOut) (fn strm => (
      PP.openHBox strm;
	PP.string strm "if";
	PP.space strm 1;
	PP.string strm "(x < y)";
	PP.space strm 1;
	PP.string strm "{";
	PP.openHVBox strm (PP.Abs 2);
	  PP.space strm 1;
	  PP.string strm "stmt1;"; PP.space strm 1;
	  PP.openHBox strm;
	    PP.string strm "if";
	    PP.space strm 1;
	    PP.string strm "(w < z)";
	    PP.space strm 1;
	    PP.string strm "{";
	    PP.openHVBox strm (PP.Abs 4);
	      PP.space strm 1; PP.string strm "stmt2;";
	      PP.space strm 1; PP.string strm "stmt3;";
	      PP.space strm 1; PP.string strm "stmt4;";
	    PP.closeBox strm; PP.newline strm;
	    PP.string strm "}";
	  PP.closeBox strm;
	  PP.space strm 1; PP.string strm "stmt5;";
	  PP.space strm 1; PP.string strm "stmt6;";
	PP.closeBox strm; PP.newline strm;
	PP.string strm "}";
        PP.closeBox strm))

fun pp_e str_var str_i s e =
  let
    val pp_e = pp_e str_var str_i s
    fun space () = PP.space s 1
    fun add_space a = (space (); a)
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    fun open_vbox () = PP.openVBox s (PP.Abs 2)
    (* fun open_vbox () = PP.openVBox s (PP.Rel 2) *)
    fun close_box () = PP.closeBox s
    fun pp_pair (fa, fb) (a, b) =
      (
        open_hbox ();
        str "(";
        fa a;
        comma ();
        fb b;
        str ")";
        close_box ()
      )
    fun pp_list f ls =
      case ls of
          [] => ()
        | [x] => f x
        | x :: xs =>
          (
            f x;
            comma ();
            pp_list f xs
          )
  in
    case e of
        EVar x =>
        (
          open_hbox ();
          str "EVar";
          space ();
          str $ str_var x;
          close_box ()
        )
      | EAppI (e, i) =>
        (
          open_hbox ();
          str "EAppI";
          space ();
          str "(";
          pp_e e;
          comma ();
          str $ str_i i;
          str ")";
          close_box ()
        )
      | EMatchSum (e, branches) =>
        (
          open_hbox ();
          str "EMatchSum";
          space ();
          str "(";
          pp_e e;
          comma ();
          str "[";
	  open_vbox ();
          space ();
          pp_list (pp_pair (str o get_name, pp_e) o get_bind) branches;
	  close_box ();
          str "]";
          str ")";
          close_box ()
        )
      | EMatchPair (e, branch) =>
        let
          val (name1, branch) = get_bind branch
          val (name2, branch) = get_bind branch
        in
          open_hbox ();
          str "EMatchPair";
          space ();
          str "(";
          pp_e e;
          comma ();
	  open_vbox ();
          space ();
	  open_hbox ();
          str "(";
          str $ get_name name1;
          comma ();
          str $ get_name name2;
          comma ();
          pp_e branch;          
          str ")";
	  close_box ();
	  close_box ();
          str ")";
          close_box ()
        end
      | EMatchUnfold (e, branch) =>
        (
          open_hbox ();
          str "EMatchUnfold";
          space ();
          str "(";
          pp_e e;
          comma ();
	  open_vbox ();
          space ();
          pp_pair (str o get_name, pp_e) o get_bind $ branch;
	  close_box ();
          str ")";
          close_box ()
        )
      | EMatchUnpackI (e, branch) =>
        let
          val (name1, branch) = get_bind branch
          val (name2, branch) = get_bind branch
        in
          open_hbox ();
          str "EMatchUnpackI";
          space ();
          str "(";
          pp_e e;
          comma ();
	  open_vbox ();
          space ();
	  open_hbox ();
          str "(";
          str $ get_name name1;
          comma ();
          str $ get_name name2;
          comma ();
          pp_e branch;          
          str ")";
	  close_box ();
	  close_box ();
          str ")";
          close_box ()
        end
      | _ => raise Unimpl ""
  end

fun pprint_e str_var str_i e = withPP ("", 80, TextIO.stdOut) (fn s => pp_e str_var str_i s e)
val pp_e = pprint_e

(* fun str_e str_var str_i e = *)
(*   let *)
(*     val str_e = str_e str_var str_i *)
(*   in *)
(*     case e of *)
(*         EVar x => sprintf "EVar $" [str_var x] *)
(*       | EAppI (e, i) => sprintf "EAppI ($, $)" [str_e e, str_i i] *)
(*       | EMatchSum (e, branches) => sprintf "EMatchSum ($, $)" [str_e e, str_ls (str_pair (get_name, str_e) o get_bind) branches] *)
(*       | EMatchPair (e, branch) => *)
(*         let *)
(*           val (name1, branch) = get_bind branch *)
(*           val (name2, branch) = get_bind branch *)
(*         in *)
(*           sprintf "EMatchPair ($, ($, $, $))" [str_e e, get_name name1, get_name name2, str_e branch] *)
(*         end *)
(*       | EMatchUnfold (e, branch) => sprintf "EMatchUnfold ($, $)" [str_e e, str_pair (get_name, str_e) $ get_bind branch] *)
(*       | EMatchUnpackI (e, branch) => *)
(*         let *)
(*           val (name1, branch) = get_bind branch *)
(*           val (name2, branch) = get_bind branch *)
(*         in *)
(*           sprintf "EMatchUnpackI ($, ($, $, $))" [str_e e, get_name name1, get_name name2, str_e branch] *)
(*         end *)
(*   end *)
    
type ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor_vtable =
     {
       visit_expr : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort, 'ty) expr -> ('var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr,
       visit_EVar : 'this -> 'env -> 'var -> ('var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr,
       visit_EAppI : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort, 'ty) expr * 'idx -> ('var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr,
       visit_EMatchSum : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind list -> ('var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr,
       visit_EMatchPair : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind ebind -> ('var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr,
       visit_EMatchUnfold : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind -> ('var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr,
       visit_EMatchUnpackI : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort, 'ty) expr * ('var, 'bsort, 'idx, 'sort, 'ty) expr ebind ibind -> ('var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr,
       visit_var : 'this -> 'env -> 'var -> 'var2,
       (* visit_bsort : 'this -> 'env -> 'bsort -> 'bsort2, *)
       visit_idx : 'this -> 'env -> 'idx -> 'idx2,
       (* visit_sort : 'this -> 'env -> 'sort -> 'sort2, *)
       (* visit_region : 'this -> 'env -> region -> region, *)
       extend_i : 'this -> 'env -> iname -> 'env,
       extend_e : 'this -> 'env -> ename -> 'env
     }
       
type ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor_interface =
     ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor_vtable
                                       
fun override_visit_EVar (record : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor_vtable) new : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = new,
    visit_EAppI = #visit_EAppI record,
    visit_EMatchSum = #visit_EMatchSum record,
    visit_EMatchPair = #visit_EMatchPair record,
    visit_EMatchUnfold = #visit_EMatchUnfold record,
    visit_EMatchUnpackI = #visit_EMatchUnpackI record,
    visit_var = #visit_var record,
    visit_idx = #visit_idx record,
    extend_i = #extend_i record,
    extend_e = #extend_e record
  }

(***************** the default visitor  **********************)    

open VisitorUtil
       
val visit_ibind = Unbound.visit_bind_simp
val visit_tbind = Unbound.visit_bind_simp
val visit_ebind = Unbound.visit_bind_simp
                    
fun default_expr_visitor_vtable
      (cast : 'this -> ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor_interface)
      extend_i
      extend_e
      visit_var
      visit_idx
    : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor_vtable =
  let
    fun visit_expr this env data =
      let
        val vtable = cast this
      in
        case data of
            EVar data => #visit_EVar vtable this env data
          | EAppI data => #visit_EAppI vtable this env data
          | EMatchSum data => #visit_EMatchSum vtable this env data
          | EMatchPair data => #visit_EMatchPair vtable this env data
          | EMatchUnfold data => #visit_EMatchUnfold vtable this env data
          | EMatchUnpackI data => #visit_EMatchUnpackI vtable this env data
          | _ => raise Unimpl ""
      end
    fun visit_EVar this env data =
      let
        val vtable = cast this
      in
        EVar $ #visit_var vtable this env data
      end
    fun visit_EAppI this env data = 
      let
        val vtable = cast this
        val (e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        EAppI (e, i)
      end
    (* fun default_visit_binder extend this = visit_binder (extend this) *)
    val visit_ebind = fn this => visit_ebind (#extend_e (cast this) this)
    val visit_ibind = fn this => visit_ibind (#extend_i (cast this) this)
    fun visit_EMatchSum this env data =
      let
        val vtable = cast this
        val (e, branches) = data
        val e = #visit_expr vtable this env e
        val branches = (visit_list o visit_ebind this) (#visit_expr vtable this) env branches
      in
        EMatchSum (e, branches)
      end
    fun visit_EMatchPair this env data =
      let
        val vtable = cast this
        val (e, branch) = data
        val e = #visit_expr vtable this env e
        val branch = (visit_ebind this o visit_ebind this) (#visit_expr vtable this) env branch
      in
        EMatchPair (e, branch)
      end
    fun visit_EMatchUnfold this env data =
      let
        val vtable = cast this
        val (e, branch) = data
        val e = #visit_expr vtable this env e
        val branch = visit_ebind this (#visit_expr vtable this) env branch
      in
        EMatchUnfold (e, branch)
      end
    fun visit_EMatchUnpackI this env data =
      let
        val vtable = cast this
        val (e, branch) = data
        val e = #visit_expr vtable this env e
        val branch = (visit_ibind this o visit_ebind this) (#visit_expr vtable this) env branch
      in
        EMatchUnpackI (e, branch)
      end
  in
    {
      visit_expr = visit_expr,
      visit_EVar = visit_EVar,
      visit_EAppI = visit_EAppI,
      visit_EMatchSum = visit_EMatchSum,
      visit_EMatchPair = visit_EMatchPair,
      visit_EMatchUnfold = visit_EMatchUnfold,
      visit_EMatchUnpackI = visit_EMatchUnpackI,
      visit_var = visit_var,
      visit_idx = visit_idx,
      extend_i = extend_i,
      extend_e = extend_e
    }
  end

datatype ('env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor =
         ExprVisitor of (('env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor, 'env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor_interface

fun expr_visitor_impls_interface (this : ('env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor) :
    (('env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor, 'env, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx2, 'sort2, 'ty2) expr_visitor_interface =
  let
    val ExprVisitor vtable = this
  in
    vtable
  end

fun new_expr_visitor vtable params =
  let
    val vtable = vtable expr_visitor_impls_interface params
  in
    ExprVisitor vtable
  end
    
(***************** the "shift_i_e" visitor  **********************)    
    
fun shift_i_expr_visitor_vtable cast (shift_i, n) : ('this, int, 'var, 'bsort2, 'idx, 'ty, 'sort2, 'var, 'bsort, 'idx2, 'sort, 'ty2) expr_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
    val extend_e = extend_noop
    fun do_shift shift this env b = shift env n b
  in
    default_expr_visitor_vtable
      cast
      extend_i
      extend_e
      visit_noop
      (do_shift shift_i)
  end

fun new_shift_i_expr_visitor params = new_expr_visitor shift_i_expr_visitor_vtable params
    
fun shift_i_e_fn shift_i x n b =
  let
    val visitor as (ExprVisitor vtable) = new_shift_i_expr_visitor (shift_i, n)
  in
    #visit_expr vtable visitor x b
  end
    
(***************** the "shift_e_e" visitor  **********************)    
    
fun shift_e_expr_visitor_vtable cast (shift_var, n) : ('this, int, 'var, 'bsort, 'idx, 'sort, 'ty, 'var2, 'bsort2, 'idx, 'sort2, 'ty2) expr_visitor_vtable =
  let
    val extend_i = extend_noop
    fun extend_e this env _ = env + 1
    fun visit_var this env data = shift_var env n data
  in
    default_expr_visitor_vtable
      cast
      extend_i
      extend_e
      visit_var
      visit_noop
  end

fun new_shift_e_expr_visitor params = new_expr_visitor shift_e_expr_visitor_vtable params
    
fun shift_e_e_fn shift_var x n b =
  let
    val visitor as (ExprVisitor vtable) = new_shift_e_expr_visitor (shift_var, n)
  in
    #visit_expr vtable visitor x b
  end
    
(***************** the "subst_e_e" visitor  **********************)    

datatype 'a cmp_var =
         CmpEq
         | CmpGreater of 'a
         | CmpOther
             
fun subst_e_expr_visitor_vtable cast (shift_var, compare_var, shift_i_i, d, x, v) : ('this, idepth * edepth, 'var, 'bsort, 'idx, 'sort, 'ty, 'var, 'bsort2, 'idx, 'sort2, 'ty2) expr_visitor_vtable =
  let
    fun extend_i this env _ = mapFst idepth_inc env
    fun extend_e this env _ = mapSnd edepth_inc env
    val add_depth = mapPair2 idepth_add edepth_add
    fun visit_EVar this env y =
      let
        val x = x + open_edepth (snd env)
      in
        case compare_var y x of
            CmpEq =>
            let
              val (di, de) = add_depth d env
            in
              shift_i_e_fn shift_i_i 0 (open_idepth di) $ shift_e_e_fn shift_var 0 (open_edepth de) v
            end
          | CmpGreater y' =>
            EVar y'
          | _ =>
            EVar y
      end
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_i
          extend_e
          (visit_imposs "subst_e_e/visit_var")
          visit_noop
    val vtable = override_visit_EVar vtable visit_EVar
  in
    vtable
  end

fun new_subst_e_expr_visitor params = new_expr_visitor subst_e_expr_visitor_vtable params
    
fun subst_e_e_fn shift_var compare_var shift_i_i d x v b =
  let
    val visitor as (ExprVisitor vtable) = new_subst_e_expr_visitor (shift_var, compare_var, shift_i_i, d, x, v)
  in
    #visit_expr vtable visitor (IDepth 0, EDepth 0) b
  end

end
