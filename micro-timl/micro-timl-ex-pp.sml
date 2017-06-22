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

fun str_expr_un_op opr =
  case opr of
      EUProj opr => str_proj opr
    | EUInj opr => str_inj opr
    | EUFold => "fold"
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
      | EMatchUnpackI (e, branch) =>
        let
          val (name1, branch) = get_bind branch
          val (name2, branch) = get_bind branch
        in
          sprintf "EMatchUnpackI ($, ($, $, $))" [str_e e, name1, name2, str_e branch]
        end
      | _ => raise Unimpl ""
  end
    
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

fun withPP (name, wid, dst) ppFn =
  let
    (* val saveStrm = !PP.debugStrm *)
    (* val _ = PP.debugStrm := TextIO.openAppend("debug-out.txt") *)
    val ppStrm =
	PP.openStream(SimpleTextIODev.openDev{dst=dst, wid=wid})
  in
    (* print(concat[name, ": width = ", Int.toString wid, "\n"]); *)
    ppFn ppStrm;
    PP.closeStream ppStrm;
    TextIO.output (dst, "\n");
    (* TextIO.closeOut (!PP.debugStrm); *)
    (* PP.debugStrm := saveStrm; *)
    ()
  end

(* a test *)
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

fun pp_e (params as (str_var, str_i, str_s, str_t)) s e =
  let
    val pp_e = pp_e params s
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
          str name1;
          comma ();
          str name2;
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
          pp_pair (str, pp_e) o get_bind $ branch;
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
          str name1;
          comma ();
          str name2;
          comma ();
          pp_e branch;          
          str ")";
	  close_box ();
	  close_box ();
          str ")";
          close_box ()
        end
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
          str $ str_expr_un_op opr;
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
          open_hbox ();
          str "EAbs";
          space ();
          str "(";
          str name;
          comma ();
          str $ str_t t;
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
      | ERec bind =>
        let
          val (name, e) = get_bind bind
        in
          open_hbox ();
          str "ERec";
          space ();
          str "(";
          str name;
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
      | EAbsT bind =>
        let
          val (name, e) = get_bind bind
        in
          open_hbox ();
          str "EAbsT";
          space ();
          str "(";
          str name;
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
          open_hbox ();
          str "EAbsI";
          space ();
          str "(";
          str name;
          comma ();
          str $ str_s s;
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
      | EPack (t, e) =>
        (
          open_hbox ();
          str "EPack";
          space ();
          str "(";
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
      | EPackI (i, e) =>
        (
          open_hbox ();
          str "EPack";
          space ();
          str "(";
          str $ str_i i;
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
      | EUnpackI (e, bind) =>
        let
          val (iname, bind) = get_bind bind
          val (ename, e) = get_bind bind
        in
          open_hbox ();
          str "EUnpackI";
          space ();
          str "(";
          str iname;
          comma ();
          str ename;
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
      | EAscTime (e, i) =>
        (
          open_hbox ();
          str "EAscTime";
          space ();
          str "(";
          pp_e e;
          comma ();
          str $ str_i i;
          str ")";
          close_box ()
        )
      | EAscType (e, t) =>
        (
          open_hbox ();
          str "EAscType";
          space ();
          str "(";
          pp_e e;
          comma ();
          str $ str_t t;
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
      | ELet (e, branch) =>
        (
          open_hbox ();
          str "ELet";
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
  end

fun pp_e_fn params e = withPP ("", 80, TextIO.stdOut) (fn s => pp_e params s e)

(* datatype ('var, 'idx, 'sort, 'ty) expr = *)
(*          EVar of 'var *)
(*          | EConst of Operators.expr_const *)
(*          | ELoc of loc *)
(*          | EUnOp of expr_un_op * ('var, 'idx, 'sort, 'ty) expr *)
(*          | EBinOp of expr_bin_op * ('var, 'idx, 'sort, 'ty) expr * ('var, 'idx, 'sort, 'ty) expr *)
(*          | EWrite of ('var, 'idx, 'sort, 'ty) expr * ('var, 'idx, 'sort, 'ty) expr * ('var, 'idx, 'sort, 'ty) expr *)
(*          | ECase of ('var, 'idx, 'sort, 'ty) expr * ('var, 'idx, 'sort, 'ty) expr ebind * ('var, 'idx, 'sort, 'ty) expr ebind *)
(*          | EAbs of ('ty, ('var, 'idx, 'sort, 'ty) expr) ebind_anno *)
(*          | ERec of ('var, 'idx, 'sort, 'ty) expr ebind *)
(*          | EAbsT of ('var, 'idx, 'sort, 'ty) expr tbind *)
(*          | EAppT of ('var, 'idx, 'sort, 'ty) expr * 'ty *)
(*          | EAbsI of ('sort, ('var, 'idx, 'sort, 'ty) expr) ibind_anno *)
(*          | EAppI of ('var, 'idx, 'sort, 'ty) expr * 'idx *)
(*          | EPack of 'ty * ('var, 'idx, 'sort, 'ty) expr *)
(*          | EUnpack of ('var, 'idx, 'sort, 'ty) expr * ('var, 'idx, 'sort, 'ty) expr ebind tbind *)
(*          | EPackI of 'idx * ('var, 'idx, 'sort, 'ty) expr *)
(*          | EUnpackI of ('var, 'idx, 'sort, 'ty) expr * ('var, 'idx, 'sort, 'ty) expr ebind ibind *)
(*          | EAscTime of ('var, 'idx, 'sort, 'ty) expr * 'idx (* time ascription *) *)
(*          | EAscType of ('var, 'idx, 'sort, 'ty) expr * 'ty (* type ascription *) *)
(*          | ENever of 'ty *)
(*          | ELet of ('var, 'idx, 'sort, 'ty) expr * ('var, 'idx, 'sort, 'ty) expr ebind *)
(*          | EMatchSum of ('var, 'idx, 'sort, 'ty) expr * ('var, 'idx, 'sort, 'ty) expr ebind list *)
(*          | EMatchPair of ('var, 'idx, 'sort, 'ty) expr * ('var, 'idx, 'sort, 'ty) expr ebind ebind *)
(*          | EMatchUnfold of ('var, 'idx, 'sort, 'ty) expr * ('var, 'idx, 'sort, 'ty) expr ebind *)
(*          | EMatchUnpackI of ('var, 'idx, 'sort, 'ty) expr * ('var, 'idx, 'sort, 'ty) expr ebind ibind *)

end
