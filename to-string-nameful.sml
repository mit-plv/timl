functor ToStringNamefulFn (structure Expr : IDX_TYPE_EXPR
                                            where type Idx.base_sort = BaseSorts.base_sort
                                              and type Type.base_type = BaseTypes.base_type
                                              and type Idx.region = Region.region
                                              and type Type.region = Region.region
                                              and type Idx.name = string * Region.region
                                              and type Type.name = string * Region.region
                                              and type Idx.var = string
                                              and type mod_id = string
                         sharing type Expr.Type.bsort = Expr.Idx.bsort
                         val str_uvar_bs : ('a -> string) -> 'a Expr.Idx.uvar_bs -> string
                         val str_uvar_i : ('bsort -> string) * ('idx -> string) -> ('bsort, 'idx) Expr.Idx.uvar_i -> string
                         val str_uvar_s : ('sort -> string) -> ('bsort, 'sort) Expr.Idx.uvar_s -> string
                         val str_uvar_mt : ('sort -> string) * ('kind -> string) * ('mtype -> string) -> ('sort, 'kind, 'mtype) Expr.Type.uvar_mt -> string
                        ) = struct

open Expr
open Idx
open Type
open Region
open BaseSorts
open BaseTypes
open Operators
open Pattern
open Bind
       
infixr 0 $
         
structure Idx = Idx
structure Type = Type
structure Expr = Expr

structure IdxUtil = IdxUtilFn (Idx)
open IdxUtil
       
fun strn_bs s =
  case s of
      Base s => str_b s
    | BSArrow (s1, s2) =>
      let
        fun default () = sprintf "($ => $)" [strn_bs s1, strn_bs s2]
      in
        case is_time_fun s of
            SOME n => if n = 0 then "Time" else sprintf "(Fun $)" [str_int n]
          | NONE => default ()
      end
    | UVarBS u =>
      str_uvar_bs strn_bs u

fun strn_i i =
  (* case is_IApp_UVarI i of *)
  (*     SOME ((x, _), args) => sprintf "($ ...)" [str_uvar_i (str_bs, str_i []) x] *)
  (*   | NONE => *)
  case i of
      VarI x => x
    | IConst (c, _) => str_idx_const c
    | UnOpI (opr, i, _) =>
      (case opr of
           IUDiv n => sprintf "($ / $)" [strn_i i, str_int n]
         | IUExp s => sprintf "($ ^ $)" [strn_i i, s]
         | _ => sprintf "($ $)" [str_idx_un_op opr, strn_i i]
      )
    | BinOpI (opr, i1, i2) =>
      (case opr of
           IApp =>
           let
             val (f, is) = collect_IApp i
             val is = f :: is
           in
             sprintf "($)" [join " " $ map strn_i is]
           end
         | AddI =>
           let
             val is = collect_AddI_left i
           in
             sprintf "($)" [join " + " $ map strn_i is]
           end
         | _ => sprintf "($ $ $)" [strn_i i1, str_idx_bin_op opr, strn_i i2]
      )
    | Ite (i1, i2, i3, _) => sprintf "(ite $ $ $)" [strn_i i1, strn_i i2, strn_i i3]
    | IAbs _ =>
      let
        val (bs_names, i) = collect_IAbs i
      in
        sprintf "(fn $ => $)" [join " " $ map (fn (b, name) => sprintf "($ : $)" [name, strn_bs b]) bs_names, strn_i i]
      end
    (* | IAbs ((name, _), i, _) => sprintf "(fn $ => $)" [name, strn_i (name :: ctx) i] *)
    | UVarI (u, _) =>
      str_uvar_i (strn_bs, strn_i) u
                                 
fun strn_p p =
  case p of
      PTrueFalse (b, _) => str_bool b
    | Not (p, _) => sprintf "(~ $)" [strn_p p]
    | BinConn (opr, p1, p2) => sprintf "($ $ $)" [strn_p p1, str_bin_conn opr, strn_p p2]
    (* | BinPred (BigO, i1, i2) => sprintf "($ $ $)" [strn_bin_pred BigO, strn_i ctx i1, strn_i ctx i2] *)
    | BinPred (opr, i1, i2) => sprintf "($ $ $)" [strn_i i1, str_bin_pred opr, strn_i i2]
    | Quan (q, bs, Bind ((name, _), p), _) => sprintf "($ ($ : $) $)" [str_quan q, name, strn_bs bs, strn_p p]

fun strn_s s =
  (* case is_SApp_UVarS s of *)
  (*     SOME ((x, _), args) => sprintf "($ ...)" [str_uvar_s (strn_s []) x] *)
  (*   | NONE => *)
  case s of
      Basic (bs, _) => strn_bs bs
    | Subset ((bs, _), Bind ((name, _), p), _) =>
      let
        fun default () = sprintf "{ $ : $ | $ }" [name, strn_bs bs, strn_p p]
      in
        case (is_time_fun bs, p) of
            (SOME arity, BinPred (BigO, VarI x, i2)) =>
            if x = name then
              sprintf "BigO $ $" [str_int arity, strn_i i2]
            else
              default ()
          | _ => default ()
      end
    | UVarS (u, _) =>
      str_uvar_s strn_s u
    | SAbs (s1, Bind ((name, _), s), _) =>
      sprintf "(fn $ : $ => $)" [name, strn_bs s1, strn_s s]
    | SApp (s, i) => sprintf "($ $)" [strn_s s, strn_i i]

(* val str_Type = "*" *)
val str_Type = "Type"
                 
fun strn_k (n, sorts) : string =
  if n = 0 andalso null sorts then str_Type
  else
    sprintf "($$$)" [if n = 0 then "" else join " => " (repeat n str_Type) ^ " => ", if null sorts then "" else join " => " (map strn_bs sorts) ^ " => ", str_Type]

datatype 'a bind = 
         KindingT of string
         | SortingT of string * 'a

fun strn_tbinds binds =
  let
    fun f bind =
      case bind of
          KindingT name => KindingT name
        | SortingT (name, s) => SortingT (name, strn_s s)
    val binds = map f binds
  in
    binds
  end
    
structure TypeUtil = TypeUtilFn (Type)
open TypeUtil
       
fun collect_Uni_UniI t =
  let
    val (tnames, t) = collect_Uni t
    val tnames = map fst tnames
    val (binds, t) = collect_UniI t
    val binds = map (mapFst fst) binds
  in
    (map KindingT tnames @ map SortingT binds, t)
  end

fun strn_mt t =
  let
    fun collect_MtAppI_or_MtApp t =
      case t of
          MtAppI (t, i) =>
          let 
            val (f, args) = collect_MtAppI_or_MtApp t
          in
            (f, args @ [inl i])
          end
        | MtApp (t, arg) =>
          let 
            val (f, args) = collect_MtAppI_or_MtApp t
          in
            (f, args @ [inr arg])
          end
        | _ => (t, [])
    fun map_sum (f_l, f_r) a =
      case a of
          inl v => f_l v
        | inr v => f_r v
    fun strn_apps t = 
      let
        val (f, args) = collect_MtAppI_or_MtApp t
      in
        sprintf "($$)" [strn_mt f, join_prefix " " $ map (map_sum (strn_i, strn_mt)) $ args]
      end
    fun collect_MtAbsI_or_MtAbs t =
      case t of
          MtAbsI (s, Bind ((name, _), t), _) =>
          let
            val (binds, t) = collect_MtAbsI_or_MtAbs t
          in
            ((inl s, name) :: binds, t)
          end
        | MtAbs (k, Bind ((name, _), t), _) =>
          let
            val (binds, t) = collect_MtAbsI_or_MtAbs t
          in
            ((inr k, name) :: binds, t)
          end
        | _ => ([], t)
    fun strn_abs t =
      let
        val (binds, t) = collect_MtAbsI_or_MtAbs t
        (* val () = println $ strn_int (length binds) *)
        fun strn_bind (c, name) =
          case c of
              inl s => sprintf "{$ : $}" [name, strn_bs s(* "..." *)]
            | inr k => sprintf "[$ : $]" [name, strn_k k]
        val binds = map strn_bind binds
        (* val () = println $ strn_int (length binds) *)
        val t = strn_mt t
      in
        sprintf "(fn$ => $)" [join_prefix " " binds, t]
      end
  in
    (* case is_MtApp_UVar t of *)
    (*     SOME ((x, _), i_args, t_args) => sprintf "($ ...)" [strn_uvar_mt (strn_raw_bs, strn_raw_k, strn_mt ([], [])) x] *)
    (*   | NONE => *)
    case t of
        Arrow (t1, d, t2) =>
        if is_T0 d then
          sprintf "($ -> $)" [strn_mt t1, strn_mt t2]
        else
          sprintf "($ -- $ --> $)" [strn_mt t1, strn_i d, strn_mt t2]
      | TyNat (i, _) => sprintf "(nat $)" [strn_i i]
      | TyArray (t, i) => sprintf "(arr $ $)" [strn_mt t, strn_i i]
      | Unit _ => "unit"
      | Prod (t1, t2) => sprintf "($ * $)" [strn_mt t1, strn_mt t2]
      | UniI _ =>
        let
          val (binds, t) = collect_UniI t
          val binds = map (mapFst fst) binds
        in
          strn_uni (map SortingT binds, t)
        end
      | MtVar x => x
      | MtApp (t1, t2) =>
        (* sprintf "($ $)" [strn_mt ctx t1, strn_mt ctx t2] *)
        strn_apps t
      | MtAbs _ =>
        (* sprintf "(fn [$ : $] => $)" [name, strn_k gctx sctx k, strn_mt (sctx, name :: kctx) t] *)
        strn_abs t
      | MtAppI _ =>
        (* sprintf "($ {$})" [strn_mt ctx t, strn_i gctx sctx i] *)
        strn_apps t
      | MtAbsI _ =>
        (* sprintf "(fn {$ : $} => $)" [name, strn_s gctx sctx s, strn_mt (name :: sctx, kctx) t] *)
        strn_abs t
      | BaseType (bt, _) => str_bt bt
      | UVar (u, r) =>
        let
          (* fun str_region ((left, right) : region) = sprintf "($,$)-($,$)" [str_int (#line left), str_int (#col left), str_int (#line right), str_int (max (#col right) 0)] *)
        in
          (* (surround "[" "] " $ str_region r) ^ *) str_uvar_mt (strn_bs, strn_k, strn_mt) u
        end
      | TDatatype (dt, _) => "(datatype ...)"
  end

and strn_uni (binds, t) =
    let 
      val binds = strn_tbinds binds
      fun f bind =
        case bind of
            KindingT name => name
          | SortingT (name, s) => sprintf "{$ : $}" [name, s]
      val binds = map f binds
    in
      sprintf "(forall$, $)" [join_prefix " " binds, strn_mt t]
    end
      
fun strn_t t =
  case t of
      Mono t => strn_mt t
    | Uni _ => strn_uni (collect_Uni_UniI t)

fun decorate_var eia s = (if eia then "@" else "") ^ s
    
fun strn_pn pn =
  case pn of
      ConstrP (Outer ((x, _), eia), inames, pn, _) => sprintf "$$$" [decorate_var eia x, join_prefix " " $ map (surround "{" "}" o binder2str) inames, " " ^ strn_pn pn]
    | VarP name => binder2str name
    | PairP (pn1, pn2) => sprintf "($, $)" [strn_pn pn1, strn_pn pn2]
    | TTP _ => "()"
    | AliasP (name, pn, _) => sprintf "$ as $" [binder2str name, strn_pn pn]
    | AnnoP (pn, Outer t) => sprintf "($ : $)" [strn_pn pn, strn_mt t]

fun strn_return return =
  case return of
      (NONE, NONE) => ""
    | (SOME t, NONE) => sprintf "return $ " [strn_mt t]
    | (NONE, SOME d) => sprintf "return using $ " [strn_i d]
    | (SOME t, SOME d) => sprintf "return $ using $ " [strn_mt t, strn_i d]

fun strn_sortings binds =
  let
    val binds = strn_tbinds (map SortingT binds)
    fun f bind = case bind of SortingT p => p | _ => raise Impossible "strn_tbinds shouldn't return Kinding"
    val binds = map f binds
  in
    binds
  end

structure ExprUtil = ExprUtilFn (Expr)
open ExprUtil
       
fun strn_e e =
  case e of
      EVar (x, b) => decorate_var b x
    | EConst (c, _) => str_expr_const c
    | EUnOp (opr, e, _) => sprintf "($ $)" [str_expr_un_op opr, strn_e e]
    | EBinOp (opr, e1, e2) =>
      (case opr of
           EBApp => sprintf "($ $)" [strn_e e1, strn_e e2]
         | EBPair =>
           let
             val es = collect_Pair e
           in
             sprintf "($)" [join ", " $ map strn_e es]
           end
         | EBNew => sprintf "(new $ $)" [strn_e e1, strn_e e2]
         | EBRead => sprintf "(read $ $)" [strn_e e1, strn_e e2]
         | EBAdd => sprintf "($ $ $)" [strn_e e1, str_bin_op opr, strn_e e2]
      )
    | ETriOp (Write, e1, e2, e3) => sprintf "(write $ $ $)" [strn_e e1, strn_e e2, strn_e e3]
    | EEI (opr, e, i) =>
      (case opr of
           EEIAppI => sprintf "($ {$})" [strn_e e, strn_i i]
         | EEIAscTime => sprintf "($ |> $)" [strn_e e, strn_i i]
      )
    | EET (opr, e, t) =>
      (case opr of
           EETAppT => sprintf "($ [$])" [strn_e e, strn_mt t]
         | EETAsc => sprintf "($ : $)" [strn_e e, strn_mt t]
      )
    | ET (opr, t, _) =>
      (case opr of
           ETNever => sprintf "(never [$])" [strn_mt t]
         | ETBuiltin => sprintf "(builtin [$])" [strn_mt t]
      )
    | EAbs bind => 
      let
        val (pn, e) = Unbound.unBind bind
        val pn = strn_pn pn
	val e = strn_e e
      in
        sprintf "(fn $ => $)" [pn, e]
      end
    | EAbsI (bind, _) =>
      let
        val ((name, s), e) = unBindAnno bind
        val name = Name2str name
      in
        sprintf "(fn {$ : $} => $)" [name, strn_s s, strn_e e]
      end
    | ELet (return, bind, _) => 
      let
        val (decls, e) = Unbound.unBind bind
        val decls = unTeles decls
        val return = strn_return return
        val decls = map strn_decl decls
      in
        sprintf "let $$ in $ end" [return, join_prefix " " decls, strn_e e]
      end
    | EAppConstr ((x, b), ts, is, e, _) =>
      sprintf "([$]$$ $)" [
        decorate_var b x,
        (join "" o map (prefix " ") o map (fn t => sprintf "{$}" [strn_mt t])) ts,
        (join "" o map (prefix " ") o map (fn i => sprintf "{$}" [strn_i i])) is,
        strn_e e]
    | ECase (e, return, rules, _) => sprintf "(case $ $of $)" [strn_e e, strn_return return, join " | " (map strn_rule rules)]

and strn_decl decl =
    case decl of
        DVal (name, Outer bind, _) =>
        let
          val pn = VarP name
          val (tnames, e) = Unbound.unBind bind
          val tnames = map binder2str tnames
          val tnames = (join "" o map (fn nm => sprintf " [$]" [nm])) tnames
          val pn = strn_pn pn
          val e = strn_e e
        in
          sprintf "val$ $ = $" [tnames, pn, e]
        end
      | DValPtrn (pn, Outer e, _) =>
        let
          val e = strn_e e
          val pn = strn_pn pn
        in
          sprintf "val $ = $" [pn, e]
        end
      | DRec (name, bind, _) =>
        let
          val name = binder2str name
          val ((tnames, Rebind binds), ((t, d), e)) = Unbound.unBind $ unInner bind
          val binds = unTeles binds
          val tnames = map binder2str tnames
          val tnames = (join "" o map (fn nm => sprintf " [$]" [nm])) tnames
          fun f bind =
            case bind of
                SortingST (name, Outer s) =>
                let
                  val name = binder2str name
                in
                  sprintf "{$ : $}" [name, strn_s s]
                end
              | TypingST pn =>
                strn_pn pn
          val binds = map f binds
          val binds = (join "" o map (prefix " ")) binds
          val t = strn_mt t
          val d = strn_i d
          val e = strn_e e
        in
          sprintf "rec$ $$ : $ |> $ = $" [tnames, name, binds, t, d, e]
        end
      | DIdxDef (name, Outer s, Outer i) =>
        let
          val name = binder2str name
        in
          sprintf "idx $$ = $" [name, default "" $ Option.map (prefix " : " o strn_s) s, strn_i i]
        end
      | DConstrDef (name, Outer x) =>
        let
          val name = binder2str name
        in
          sprintf "constr $ = $" [name, x]
        end
      | DAbsIdx2 (name, Outer s, Outer i) =>
        let
          val name = binder2str name
        in
          sprintf "absidx2 $ : $ = $" [name, strn_s s, strn_i i]
        end
      | DAbsIdx ((name, Outer s, Outer i), Rebind decls, _) =>
        let
          val name = binder2str name
          val decls = unTeles decls
          val decls = map strn_decl decls
        in
          sprintf "absidx $ : $ = $ with$ end" [name, strn_s s, strn_i i, join_prefix " " decls]
        end
      | DTypeDef (name, Outer t) =>
        (case t of
             TDatatype (Bind (name, tbinds), _) =>
             let
               val name = fst name
               val (tname_kinds, (sorts, constrs)) = unfold_binds tbinds
               val tnames = map fst $ map fst tname_kinds
               val strn_tnames = (join_prefix " " o rev) tnames
               fun strn_constr_decl ((cname, _), ibinds, _) =
                 let 
                   val (name_sorts, (t, idxs)) = unfold_binds ibinds
                   val name_sorts = map (mapFst fst) name_sorts
                   val name_sorts = strn_sortings name_sorts
                   val name_sorts = map (fn (nm, s) => sprintf "$ : $" [nm, s]) name_sorts
                 in
                   sprintf "$ of$ $ ->$$ $" [cname, (join_prefix " " o map (surround "{" "}")) name_sorts, strn_mt t, (join_prefix " " o map (surround "{" "}" o strn_i) o rev) idxs, strn_tnames, name]
                 end
               val s = sprintf "datatype$$ $ = $" [(join_prefix " " o map (surround "{" "}" o strn_bs) o rev) sorts, strn_tnames, name, join " | " (map strn_constr_decl constrs)]
             in
               s
             end
           | _ =>
             let
               val name = binder2str name
             in
               sprintf "type $ = $" [name, strn_mt t]
             end
        )
      | DOpen (Outer m, _) =>
        sprintf "open $" [m]
      
and strn_rule bind =
    let
      val (pn, e) = Unbound.unBind bind
    in
      sprintf "$ => $" [strn_pn pn, strn_e e]
    end

end
