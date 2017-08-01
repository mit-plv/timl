(***************** pretty printers  **********************)    

structure MicroTiMLExPP = struct

open MicroTiMLEx
       
infixr 0 $
         
fun get_bind b = mapFst binder2str $ unBind b
fun get_bind_anno b =
  let
    val ((name, anno), t) = unBindAnno b
  in
    (Name2str name, anno, t)
  end
                 
fun str_proj opr =
  case opr of
      ProjFst => "fst"
    | ProjSnd => "snd"

fun str_inj opr =
  case opr of
      InjInl => "inl"
    | InjInr => "inr"

fun str_expr_un_op str_t opr =
  case opr of
      EUProj opr => str_proj opr
    | EUInj (opr, t) => sprintf "($, $)" [str_inj opr, str_t t]
    | EUFold t => sprintf "(fold $)" [str_t t]
    | EUUnfold => "unfold"

fun str_prim_expr_bin_op opr =
  case opr of
      PEBIntAdd => "add"
    | PEBIntMult => "mult"

fun str_expr_bin_op opr =
  case opr of
      EBPrim opr => str_prim_expr_bin_op opr
    | EBApp => "app"
    | EBPair => "pair"
    | EBNew => "new"
    | EBRead => "read"
    | EBNatAdd => "nat_add"

fun str_e str_var str_i e =
  let
    val str_e = str_e str_var str_i
  in
    case e of
        EVar x => sprintf "EVar $" [str_var x]
      | EAppI (e, i) => sprintf "EAppI ($, $)" [str_e e, str_i i]
      | EMatchSum (e, branches) => sprintf "EMatchSum ($, $)" [str_e e, str_ls (str_pair (id, str_e) o get_bind) branches]
      | EMatchPair (e, branch) =>
        let
          val (name1, branch) = get_bind branch
          val (name2, branch) = get_bind branch
        in
          sprintf "EMatchPair ($, ($, $, $))" [str_e e, name1, name2, str_e branch]
        end
      | EMatchUnfold (e, branch) => sprintf "EMatchUnfold ($, $)" [str_e e, str_pair (id, str_e) $ get_bind branch]
      | EUnpackI (e, branch) =>
        let
          val (name1, branch) = get_bind branch
          val (name2, branch) = get_bind branch
        in
          sprintf "EUnpackI ($, ($, $, $))" [str_e e, name1, name2, str_e branch]
        end
      | _ => raise Unimpl ""
  end
    
fun pp_e (params as (str_var, str_i, str_s, str_k, str_t)) s e =
  let
    val pp_e = pp_e params s
    fun space () = PP.space s 1
    fun add_space a = (space (); a)
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    (* fun open_vbox () = PP.openVBox s (PP.Abs 2) *)
    fun open_vbox () = PP.openVBox s (PP.Rel 2)
    (* fun open_vbox_noindent () = PP.openVBox s (PP.Abs 0) *)
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    (* fun open_vbox_indent a = PP.openVBox s a *)
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
      | EMatchSum (e, branches) =>
        (
	  open_vbox ();
          open_hbox ();
          str "EMatchSum";
          space ();
          str "(";
          pp_e e;
	  close_box ();
          comma ();
          str "[";
	  open_vbox_noindent ();
          (* space (); *)
          pp_list (pp_pair (str, pp_e) o get_bind) branches;
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
	  open_vbox ();
          (* space (); *)
          open_hbox ();
          str "EMatchPair";
          space ();
          str "(";
          pp_e e;
	  close_box ();
          comma ();
	  open_hbox ();
          str name1;
          comma ();
          str name2;
	  close_box ();
          comma ();
          pp_e branch;          
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
          pp_pair (str, pp_e) o get_bind $ branch;
	  close_box ();
          str ")";
          close_box ()
        )
      | EConst c =>
        (
          open_hbox ();
          str "EConst";
          space ();
          str $ str_expr_const c;
          close_box ()
        )
      | ELoc l =>
        (
          open_hbox ();
          str "ELoc";
          space ();
          str $ str_int l;
          close_box ()
        )
      | EUnOp (opr, e) =>
        (
          open_hbox ();
          str "EUnOp";
          space ();
          str "(";
          str $ str_expr_un_op str_t opr;
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
      | EBinOp (opr, e1, e2) =>
        (
          open_hbox ();
          str "EBinOp";
          space ();
          str "(";
          str $ str_expr_bin_op opr;
          comma ();
          pp_e e1;
          comma ();
          pp_e e2;
          str ")";
          close_box ()
        )
      | EWrite (e1, e2, e3) =>
        (
          open_hbox ();
          str "EWrite";
          space ();
          str "(";
          pp_e e1;
          comma ();
          pp_e e2;
          comma ();
          pp_e e3;
          str ")";
          close_box ()
        )
      | ECase (e, e1, e2) =>
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
          pp_list (pp_pair (str, pp_e) o get_bind) [e1, e2];
	  close_box ();
          str "]";
          str ")";
          close_box ()
        )
      | EAbs bind =>
        let
          val (name, t, e) = get_bind_anno bind
        in
          open_vbox ();
          open_hbox ();
          str "EAbs";
          space ();
          str "(";
          str name;
          comma ();
          str $ str_t t;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
      | ERec bind =>
        let
          val (name, t, e) = get_bind_anno bind
        in
          open_vbox ();
          open_hbox ();
          str "ERec";
          space ();
          str "(";
          str name;
          comma ();
          str $ str_t t;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
      | EAbsT bind =>
        let
          val (name, k, e) = get_bind_anno bind
        in
          open_vbox ();
          open_hbox ();
          str "EAbsT";
          space ();
          str "(";
          str name;
          comma ();
          str $ str_k k;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
      | EAppT (e, t) =>
        (
          open_hbox ();
          str "EAppT";
          space ();
          str "(";
          pp_e e;
          comma ();
          str $ str_t t;
          str ")";
          close_box ()
        )
      | EAbsI bind =>
        let
          val (name, s, e) = get_bind_anno bind
        in
          open_vbox ();
          open_hbox ();
          str "EAbsI";
          space ();
          str "(";
          str name;
          comma ();
          str $ str_s s;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
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
      | EPack (t_all, t, e) =>
        (
          open_hbox ();
          str "EPack";
          space ();
          str "(";
          str $ str_t t_all;
          comma ();
          str $ str_t t;
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
      | EUnpack (e, bind) =>
        let
          val (tname, bind) = get_bind bind
          val (ename, e) = get_bind bind
        in
          open_hbox ();
          str "EUnpack";
          space ();
          str "(";
          str tname;
          comma ();
          str ename;
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
      | EPackI (t, i, e) =>
        (
          open_hbox ();
          str "EPackI";
          space ();
          str "(";
          str $ str_t t;
          comma ();
          str $ str_i i;
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
      | EPackIs (t, is, e) =>
        (
          open_hbox ();
          str "EPackIs";
          space ();
          str "(";
          str $ str_t t;
          comma ();
          pp_list (str o str_i) is;
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
      | EUnpackI (e, branch) =>
        let
          val (name1, branch) = get_bind branch
          val (name2, branch) = get_bind branch
        in
	  open_vbox_noindent ();
          (* space (); *)
          open_hbox ();
          str "EUnpackI";
          space ();
          str "(";
          str name1;
          comma ();
          str name2;
          comma ();
          pp_e e;
	  close_box ();
          comma ();
          pp_e branch;          
          str ")";
          close_box ()
        end
      | EAscTime (e, i) =>
        (
	  open_vbox_noindent ();
          open_hbox ();
          str "EAscTime";
          space ();
          str "(";
          str $ str_i i;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
      | EAscType (e, t) =>
        (
	  open_vbox_noindent ();
          open_hbox ();
          str "EAscType";
          space ();
          str "(";
          str $ str_t t;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
      | ENever t =>
        (
          open_hbox ();
          str "ENever";
          space ();
          str $ str_t t;
          close_box ()
        )
      | EBuiltin t =>
        (
          open_hbox ();
          str "EBuiltin";
          space ();
          str $ str_t t;
          close_box ()
        )
      | ELet (e, branch) =>
        let
          val (name, e_body) = get_bind branch
        in
	  open_vbox_noindent ();
          (* space (); *)
          open_hbox ();
          str "ELet";
          space ();
          str "(";
          str name;
          comma ();
          pp_e e;
	  close_box ();
          comma ();
          pp_e e_body;
          str ")";
          close_box ()
        end
  end

open WithPP
       
fun pp_e_fn params e = withPP ("", 80, TextIO.stdOut) (fn s => pp_e params s e)

end
