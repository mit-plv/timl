structure BasicSorts = struct
open Util

(* basic index sort *)
datatype base_sort =
         TimeFun of int (* number of arguments *)
         | Nat
	 | BoolSort
	 | UnitSort

val Time = TimeFun 0

fun str_b (s : base_sort) : string = 
    case s of
        TimeFun n => if n = 0 then "Time" else sprintf "Fun $" [str_int n]
      | Nat => "Nat"
      | BoolSort => "Bool"
      | UnitSort => "Unit"

end

structure Bind = struct
open Util
infixr 0 $

(* a series of dependent binds ({name1 : classifier1} {name2 : classifier2} {name3 : classifier3}, inner) *)
         
datatype ('classifier, 'body) bind = Bind of 'body

datatype ('classifier, 'name, 'inner) binds =
         BindNil of 'inner
         | BindCons of 'classifier * ('classifier, 'name * ('classifier, 'name, 'inner) binds) bind

fun unfold_binds binds =
    case binds of
        BindNil inner => ([], inner)
      | BindCons (classifier, Bind (name, binds)) =>
        let val (name_classifiers, inner) = unfold_binds binds
        in
          ((name, classifier) :: name_classifiers, inner)
        end

fun fold_binds (binds, inner) =
    foldr (fn ((name, classifier), binds) => BindCons (classifier, Bind (name, binds))) (BindNil inner) binds

fun binds_length binds = length $ fst $ unfold_binds binds
                                  
end

structure ExprUtil = struct
open Util
infixr 0 $

datatype 'a ibind = BindI of 'a

(* for a series of sorting binds ({name1 : anno1} {name2 : anno2} {name3 : anno3}, inner) *)
datatype ('anno, 'name, 'inner) ibinds =
         NilIB of 'inner
         | ConsIB of 'anno * ('name * ('anno, 'name, 'inner) ibinds) ibind

fun unfold_ibinds ibinds =
    case ibinds of
        NilIB inner => ([], inner)
      | ConsIB (anno, BindI (name, ibinds)) =>
        let val (name_annos, inner) = unfold_ibinds ibinds
        in
          ((name, anno) :: name_annos, inner)
        end

fun fold_ibinds (binds, inner) =
    foldr (fn ((name, anno), ibinds) => ConsIB (anno, BindI (name, ibinds))) (NilIB inner) binds

fun ibinds_length ibinds = length $ fst $ unfold_ibinds ibinds
                                  
datatype base_type =
         Int
           
end

signature VAR = sig
  type var
  val str_v : string list -> var -> string
  val eq_v : var * var -> bool
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
end

functor ExprFun (structure Var : VAR structure UVar : UVAR) = struct
        open Var
        open BasicSorts
        open Util
        open Operators
        open UVar
        open Region
        open ExprUtil

        type id = var * region
        type name = string * region

        datatype bsort = 
                 Base of base_sort
                 | UVarBS of bsort uvar_bs

        datatype idx =
	         VarI of var * region
	         | ConstIT of string * region
	         | ConstIN of int * region
                 | UnOpI of idx_un_op * idx * region
                 | DivI of idx * (int * region)
                 | ExpI of idx * (string * region)
                 | BinOpI of idx_bin_op * idx * idx
                 | Ite of idx * idx * idx * region
	         | TrueI of region
	         | FalseI of region
	         | TTI of region
                 | TimeAbs of name * idx * region
                 | AdmitI of region
                 | UVarI of (bsort, idx) uvar_i * region

        datatype prop =
	         True of region
	         | False of region
                 | BinConn of bin_conn * prop * prop
                 | Not of prop * region
	         | BinPred of bin_pred * idx * idx
                 | Quan of (idx -> unit) option (*for linking idx inferer with types*) quan * bsort * name * prop * region

        (* index sort *)
        datatype sort =
	         Basic of bsort * region
	         | Subset of (bsort * region) * (name * prop) ibind * region
                 | UVarS of sort uvar_s * region

        datatype kind = 
	         ArrowK of bool (* is datatype *) * int * sort list

        (* Curve out a fragment of module expression that is not a full component list ('struct' in ML) that involves types and terms, to avoid making everything mutually dependent. (This means I can't do module substitution because the result may not be expressible.) It coincides with the concept 'projectible' or 'determinate'. *)
        datatype mod_projectible =
                 ModVar of id
                 | ModSel of mod_projectible * name
                                                
        (* monotypes *)
        datatype mtype = 
	         Arrow of mtype * idx * mtype
	         | BaseType of base_type * region
                 | UVar of mtype uvar_mt * region
                 | Unit of region
	         | Prod of mtype * mtype
	         | UniI of sort * (name * mtype) ibind * region
	         | AppV of id * mtype list * idx list * region (* the first operant of App can only be a type variable. The degenerated case of no-arguments is also included *)
                 | MtVar of id
                 | MtSel of mod_projectible * name
                 | MtApp of mtype * mtype
                 | MtAbs of (name * mtype) tbind * region
                 | MtAppI of mtype * idx
                 | MtAbsI of sort * (name * mtype) ibind * region
                                                          
        withtype 'body tbind = (mtype, 'body) Bind.bind

        datatype ty = 
	         Mono of mtype
	         | Uni of name * ty * region

        type constr_core = (sort, string, mtype * idx list) ibinds
        type constr_decl = string * constr_core * region
        type constr = var * string list(*type argument names*) * constr_core

        type return = mtype option * idx option

        datatype ptrn =
                 (* eia : is explicit index arguments? *)                                         
	         ConstrP of (id * bool(*eia*)) * string list * ptrn option * region
	         | PtrnConstrSel of ((mod_projectible * name) * bool) * string list * ptrn option * region
                 | VarP of name
                 | PairP of ptrn * ptrn
                 | TTP of region
                 | AliasP of name * ptrn * region
                 | AnnoP of ptrn * mtype

        datatype stbind = 
                 SortingST of name * sort
                 | TypingST of ptrn

        type type_bind = name * mtype
                                                
        datatype expr =
	         Var of id * bool(*eia*)
                 | TermSel of (mod_projectible * name) * bool
	         | App of expr * expr
	         | Abs of ptrn * expr
                 (* unit type *)
	         | TT of region
	         (* product type *)
	         | Pair of expr * expr
	         | Fst of expr
	         | Snd of expr
	         (* universal index *)
	         | AbsI of sort * name * expr * region
	         | AppI of expr * idx
                 (* other *)
	         | BinOp of bin_op * expr * expr
	         | ConstInt of int * region
	         | AppConstr of (id * bool) * idx list * expr
	         | Case of expr * return * (ptrn * expr) list * region
	         | Let of decl list * expr * region
	         | Ascription of expr * mtype
	         | AscriptionTime of expr * idx
	         | Never of mtype * region


             and decl =
                 Val of name list * ptrn * expr * region
                 | Rec of name list * name * (stbind list * ((mtype * idx) * expr)) * region
	         | Datatype of datatype_def
                 | IdxDef of name * sort * idx
                 | AbsIdx of (name * sort * idx) * decl list * region
                 | TypeDef of type_bind
                 | Open of mod_projectible
                             
                             withtype datatype_def = string * string list * sort list * constr_decl list * region

        datatype spec =
                 SpecVal of name * ty * region
                 | SpecDatatype of datatype_def
                 | SpecIdx of name * sort
                 | SpecType of name * kind
                 | SpecTypeDef of name * ty
                                 
        datatype sgn =
                 SigVar of id
                 | SigFullList of sig_comp list * region
                 | SigWhere of sgn * type_bind

             and sig_comp =
                 ScSpec of name * spec * region
                 | ScSigBind of sig_bind

                              withtype sig_bind = name * sgn

        datatype mod =
                 ModProjectible of mod_projectible
                 | ModComponents of mod_comp list * region
                 | ModSeal of mod * sgn
                 | ModTransparentAscription of mod * sgn
                 | ModFunctorApp of id * mod list
                                                
             and mod_comp =
                 McDecl of decl
                 | McModBind of mod_bind

                                  withtype mod_bind = name * mod

        type functor_bind = name * sig_bind list * mod * region

        datatype top_bind =
                 TopSigBind of sig_bind
                 | TopModBind of mod_bind

        type prog = top_bind list

        (* some shorthands *)
                                           
        fun T0 r = ConstIT ("0.0", r)
        fun T1 r = ConstIT ("1.0", r)
        fun N0 r = ConstIN (0, r)
        fun N1 r = ConstIN (1, r)

        val STime = Basic (Base Time, dummy)
        val SBool = Basic (Base BoolSort, dummy)
        val SUnit = Basic (Base UnitSort, dummy)

        fun VarT x = AppV (x, [], [], dummy)
        fun AppVar (x, is) = AppV (x, [], is, dummy)

        val Type = ArrowK (false, 0, [])

        infixr 0 $

        (* notations *)
                 
        infix 9 %@
        fun a %@ b = BinOpI (TimeApp, a, b)
        infix 8 %^
        fun a %^ b = BinOpI (ExpNI, a, b)
        infix 7 %*
        fun a %* b = BinOpI (MultI, a, b)
        infix 6 %+ 
        fun a %+ b = BinOpI (AddI, a, b)
        infix 4 %<=
        fun a %<= b = BinPred (LeP, a, b)
        infix 4 %>=
        fun a %>= b = BinPred (GeP, a, b)
        infix 4 %=
        fun a %= b = BinPred (EqP, a, b)
        infixr 3 /\
        fun a /\ b = BinConn (And, a, b)
        infixr 2 \/
        fun a \/ b = BinConn (Or, a, b)
        infixr 1 -->
        fun a --> b = BinConn (Imply, a, b)
        infix 1 <->
        fun a <-> b = BinConn (Iff, a, b)

        (* useful functions *)
                              
        fun collect_UniI t =
            case t of
                UniI (s, BindI ((name, _), t), _) =>
                let val (binds, t) = collect_UniI t
                in
                  ((name, s) :: binds, t)
                end
              | _ => ([], t)

        fun collect_Uni t =
            case t of
                Uni (name, t, _) =>
                let val (names, t) = collect_Uni t
                in
                  (name :: names, t)
                end
              | Mono t => ([], t)

        fun constr_type VarT shiftx_v ((family, tnames, ibinds) : constr) = 
            let 
              val (ns, (t, is)) = unfold_ibinds ibinds
              val ts = (map (fn x => VarT (x, dummy)) o rev o range o length) tnames
	      val t2 = AppV ((shiftx_v 0 (length tnames) family, dummy), ts, is, dummy)
	      val t = Arrow (t, T0 dummy, t2)
	      val t = foldr (fn ((name, s), t) => UniI (s, BindI ((name, dummy), t), dummy)) t ns
              val t = Mono t
	      val t = foldr (fn (name, t) => Uni ((name, dummy), t, dummy)) t tnames
            in
	      t
            end

        fun constr_from_type t =
            let
              val (tnames, t) = collect_Uni t
              val tnames = map fst tnames
              val (ns, t) = collect_UniI t
              val (t, is) = case t of
                                Arrow (t, _, AppV (_, _, is, _)) => (t, is)
                              | _ => raise Impossible "constr_from_type (): t not the right form"
            in
              (tnames, fold_ibinds (ns, (t, is)))
            end

        fun collect_AppI e =
            case e of
                AppI (e, i) =>
                let 
                  val (e, is) = collect_AppI e
                in
                  (e, is @ [i])
                end
              | _ => (e, [])

        fun collect_BinOpI_left opr i =
            case i of
                BinOpI (opr', i1, i2) =>
                if opr' = opr then
                  collect_BinOpI_left opr i1 @ [i2]
                else [i]
              | _ => [i]
                       
        fun collect_Pair e =
            case e of
                Pair (e1, e2) =>
                collect_Pair e1 @ [e2]
              | _ => [e]
                       
        fun collect_BinOpI opr i =
            case i of
                BinOpI (opr', i1, i2) =>
                if opr' = opr then
                  collect_BinOpI opr i1 @ collect_BinOpI opr i2
                else [i]
              | _ => [i]
                       
        fun collect_BinConn opr i =
            case i of
                BinConn (opr', i1, i2) =>
                if opr' = opr then
                  collect_BinConn opr i1 @ collect_BinConn opr i2
                else [i]
              | _ => [i]
                       
        val collect_TimeApp = collect_BinOpI_left TimeApp
        val collect_AddI_left = collect_BinOpI_left AddI
                                                    
        val collect_AddI = collect_BinOpI AddI
        val collect_MultI = collect_BinOpI MultI
                                           
        val collect_And = collect_BinConn And
                                          
        fun combine_And ps = foldl' (fn (p, acc) => acc /\ p) (True dummy) ps
        fun combine_AddI zero is = foldl' (fn (i, acc) => acc %+ i) zero is
        fun combine_AddI_Time is = combine_AddI (T0 dummy) is
        fun combine_AddI_Nat is = combine_AddI (N0 dummy) is
        fun combine_AddI_nonempty i is = combine_AddI_Time (i :: is)
        fun combine_MultI is = foldl' (fn (i, acc) => acc %* i) (T1 dummy) is
                                      
        fun collect_TimeAbs i =
            case i of
                TimeAbs ((name, _), i, _) =>
                let
                  val (names, i) = collect_TimeAbs i
                in
                  (name :: names, i)
                end
              | _ => ([], i)
                       
        fun eq_i i i' =
            let
              fun loop i i' =
                  case i of
                      VarI (x, _) => (case i' of VarI (x', _) => eq_v (x, x') | _ => false)
                    | ConstIN (n, _) => (case i' of ConstIN (n', _) => n = n' | _ => false)
                    | ConstIT (x, _) => (case i' of ConstIT (x', _) => x = x' | _ => false)
                    | UnOpI (opr, i, _) => (case i' of UnOpI (opr', i', _) => opr = opr' andalso loop i i' | _ => false)
                    | DivI (i1, (n2, _)) => (case i' of DivI (i1', (n2', _)) => loop i1 i1' andalso n2 = n2' | _ => false)
                    | ExpI (i1, (n2, _)) => (case i' of ExpI (i1', (n2', _)) => loop i1 i1' andalso n2 = n2' | _ => false)
                    | BinOpI (opr, i1, i2) => (case i' of BinOpI (opr', i1', i2') => opr = opr' andalso loop i1 i1' andalso loop i2 i2' | _ => false)
                    | Ite (i1, i2, i3, _) => (case i' of Ite (i1', i2', i3', _) => loop i1 i1' andalso loop i2 i2' andalso loop i3 i3' | _ => false)
                    | TrueI _ => (case i' of TrueI _ => true | _ => false)
                    | FalseI _ => (case i' of FalseI _ => true | _ => false)
                    | TTI _ => (case i' of TTI _ => true | _ => false)
                    | TimeAbs (_, i, _) => (case i' of TimeAbs (_, i', _) => loop i i' | _ => false)
                    | AdmitI _ => (case i' of AdmitI _ => true | _ => false)
                    | UVarI (u, _) => (case i' of UVarI (u', _) => eq_uvar_i (u, u') | _ => false)
            in
              loop i i'
            end

        fun eq_bs bs bs' =
            case bs of
                Base b => (case bs' of Base b' => b = b | _ => false)
              | UVarBS _ => false

        fun eq_quan q q' =
            case q of
                Forall => (case q' of Forall => true | Exists _ => false)
              | Exists _ => (case q' of Forall => false | Exists _ => true)
                              
        fun eq_p p p' =
            case p of
                True _ => (case p' of True _ => true | _ => false)
              | False _ => (case p' of False _ => true | _ => false)
              | BinConn (opr, p1, p2) => (case p' of BinConn (opr', p1', p2') => opr = opr' andalso eq_p p1 p1' andalso eq_p p2 p2' | _ => false)
              | BinPred (opr, i1, i2) => (case p' of BinPred (opr', i1', i2') => opr = opr' andalso eq_i i1 i1' andalso eq_i i2 i2' | _ => false)
              | Not (p, _) => (case p' of Not (p', _) => eq_p p p' | _ => false)
              | Quan (q, bs, _, p, _) => (case p' of Quan (q', bs', _, p', _) => eq_quan q q' andalso eq_bs bs bs' andalso eq_p p p' | _ => false)

        (* pretty-printers *)

        fun str_bs (s : bsort) =
            case s of
                Base s => str_b s
              | UVarBS u => str_uvar_bs str_bs u
                                        
        fun str_i ctx (i : idx) : string = 
            case i of
                VarI (x, _) => str_v ctx x
              | ConstIN (n, _) => str_int n
              | ConstIT (x, _) => x
              | UnOpI (opr, i, _) => sprintf "($ $)" [str_idx_un_op opr, str_i ctx i]
              | DivI (i1, (n2, _)) => sprintf "($ / $)" [str_i ctx i1, str_int n2]
              | ExpI (i1, (n2, _)) => sprintf "($ ^ $)" [str_i ctx i1, n2]
              | BinOpI (TimeApp, i1, i2) =>
                let
                  val is = collect_TimeApp i
                in
                  sprintf "($)" [join " " $ map (str_i ctx) is]
                end
              | BinOpI (AddI, i1, i2) =>
                let
                  val is = collect_AddI_left i
                in
                  sprintf "($)" [join " + " $ map (str_i ctx) is]
                end
              | BinOpI (opr, i1, i2) => sprintf "($ $ $)" [str_i ctx i1, str_idx_bin_op opr, str_i ctx i2]
              | Ite (i1, i2, i3, _) => sprintf "(ite $ $ $)" [str_i ctx i1, str_i ctx i2, str_i ctx i3]
              | TTI _ => "()"
              | TrueI _ => "true"
              | FalseI _ => "false"
              | TimeAbs _ =>
                let
                  val (names, i) = collect_TimeAbs i
                in
                  sprintf "(fn $ => $)" [join " " names, str_i (rev names @ ctx) i]
                end
              (* | TimeAbs ((name, _), i, _) => sprintf "(fn $ => $)" [name, str_i (name :: ctx) i] *)
	      | AdmitI _ => "admit" 
              | UVarI (u, _) => str_uvar_i str_i ctx u

        fun str_p ctx p = 
            case p of
                True _ => "True"
              | False _ => "False"
              | Not (p, _) => sprintf "(~ $)" [str_p ctx p]
              | BinConn (opr, p1, p2) => sprintf "($ $ $)" [str_p ctx p1, str_bin_conn opr, str_p ctx p2]
              (* | BinPred (BigO, i1, i2) => sprintf "($ $ $)" [str_bin_pred BigO, str_i ctx i1, str_i ctx i2] *)
              | BinPred (opr, i1, i2) => sprintf "($ $ $)" [str_i ctx i1, str_bin_pred opr, str_i ctx i2]
              | Quan (q, bs, (name, _), p, _) => sprintf "($ ($ : $) $)" [str_quan q, name, str_bs bs, str_p (name :: ctx) p]

        fun str_s ctx (s : sort) : string = 
            case s of
                Basic (bs, _) => str_bs bs
              | Subset ((bs, _), (BindI ((name, _), p)), _) =>
                let
                  fun default () = sprintf "{ $ : $ | $ }" [name, str_bs bs, str_p (name :: ctx) p]
                in
                  case (bs, p) of
                      (Base (TimeFun arity), BinPred (BigO, VarI (x, _), i2)) =>
                      if str_v (name :: ctx) x = name then
                        sprintf "BigO $ $" [str_int arity, str_i (name :: ctx) i2]
                      else
                        default ()
                    | _ => default ()
                end
              | UVarS _ => "_"                                               

        datatype 'a bind = 
                 KindingT of string
                 | SortingT of string * 'a

        fun collect_Uni_UniI t =
            let
              val (tnames, t) = collect_Uni t
              val tnames = map fst tnames
              val (binds, t) = collect_UniI t
            in
              (map KindingT tnames @ map SortingT binds, t)
            end

        fun str_tbinds ctx binds =
            let
              fun f (bind, (acc, (sctx, kctx))) =
                  case bind of
                      KindingT name => (KindingT name :: acc, (sctx, name :: kctx))
                    | SortingT (name, s) => (SortingT (name, str_s sctx s) :: acc, (name :: sctx, kctx))
              val (binds, ctx) = foldl f ([], ctx) binds
              val binds = rev binds
            in
              (binds, ctx)
            end
              
        fun str_sortings ctx binds =
            let val (binds, ctx) = str_tbinds (ctx, []) (map SortingT binds)
                fun f bind = case bind of SortingT p => p | _ => raise Impossible "str_tbinds shouldn't return Kinding"
                val binds = map f binds
            in
              (binds, fst ctx)
            end

        fun str_bt bt =
            case bt of
                Int => "int"
                         
        fun str_mt (ctx as (sctx, kctx)) (t : mtype) : string =
            case t of
                Arrow (t1, d, t2) =>
                if eq_i d (T0 dummy) then
                  sprintf "($ -> $)" [str_mt ctx t1, str_mt ctx t2]
                else
                  sprintf "($ -- $ --> $)" [str_mt ctx t1, str_i sctx d, str_mt ctx t2]
              | Unit _ => "unit"
              | Prod (t1, t2) => sprintf "($ * $)" [str_mt ctx t1, str_mt ctx t2]
              | UniI _ =>
                let
                  val (binds, t) = collect_UniI t
                in
                  str_uni ctx (map SortingT binds, t)
                end
              | AppV ((x, _), ts, is, _) => 
                if null ts andalso null is then
	          str_v kctx x
                else
	          sprintf "($$$)" [(join "" o map (suffix " ") o map (surround "{" "}") o map (str_i sctx) o rev) is, (join "" o map (suffix " ") o map (str_mt ctx) o rev) ts, str_v kctx x]
              | BaseType (bt, _) => str_bt bt
              | UVar (u, _) => str_uvar_mt str_mt ctx u

        and str_uni ctx (binds, t) =
            let 
              val (binds, ctx) = str_tbinds ctx binds
              fun f bind =
                  case bind of
                      KindingT name => name
                    | SortingT (name, s) => sprintf "{$ : $}" [name, s]
              val binds = map f binds
            in
              sprintf "(forall$, $)" [join_prefix " " binds, str_mt ctx t]
            end
              
        fun str_t (ctx as (sctx, kctx)) (t : ty) : string =
            case t of
                Mono t => str_mt ctx t
              | Uni _ => str_uni ctx (collect_Uni_UniI t)

        fun str_k ctx (k : kind) : string = 
            case k of
                ArrowK (_, n, sorts) => sprintf "($$Type)" [if n = 0 then "" else join " * " (repeat n "Type") ^ " => ", if null sorts then "" else join " * " (map (str_s ctx) sorts) ^ " => "]

        fun ptrn_names pn : string list * string list =
            case pn of
                ConstrP (_, inames, pn, _) =>
                let 
                  (* val () = println "ConstrP" *)
                  val (inames', enames) = ptrn_names (default (TTP dummy) pn)
                in
                  (inames' @ rev inames, enames)
                end
              | VarP (name, _) =>
                let
                  (* val () = println $ sprintf "VarP: $" [name] *)
                in
                  ([], [name])
                end
              | PairP (pn1, pn2) =>
                let val (inames1, enames1) = ptrn_names pn1
                    val (inames2, enames2) = ptrn_names pn2
                in
                  (inames2 @ inames1, enames2 @ enames1)
                end
              | TTP _ =>
                ([], [])
              | AliasP ((name, _), pn, _) =>
                let val (inames, enames) = ptrn_names pn
                in
                  (inames, enames @ [name])
                end
              | AnnoP (pn, t) => ptrn_names pn

        fun decorate_var eia s = if eia then "@" else "" ^ s
                                                             
        fun str_pn (ctx as (sctx, kctx, cctx)) pn = 
            case pn of
                ConstrP (((x, _), eia), inames, pn, _) => sprintf "$$$" [decorate_var eia $ str_v cctx x, join_prefix " " $ map (surround "{" "}") inames, str_opt (fn pn => " " ^ str_pn ctx pn) pn]
              | VarP (name, _) => name
              | PairP (pn1, pn2) => sprintf "($, $)" [str_pn ctx pn1, str_pn ctx pn2]
              | TTP _ => "()"
              | AliasP ((name, _), pn, _) => sprintf "$ as $" [name, str_pn ctx pn]
              | AnnoP (pn, t) => sprintf "($ : $)" [str_pn ctx pn, str_mt (sctx, kctx) t]

        fun str_return (skctx as (sctx, _)) return =
            case return of
                (NONE, NONE) => ""
              | (SOME t, NONE) => sprintf "return $ " [str_mt skctx t]
              | (NONE, SOME d) => sprintf "return using $ " [str_i sctx d]
              | (SOME t, SOME d) => sprintf "return $ using $ " [str_mt skctx t, str_i sctx d]

        fun str_e (ctx as (sctx, kctx, cctx, tctx)) (e : expr) : string =
            let fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx) 
                val skctx = (sctx, kctx) 
            in
              case e of
	          Var ((x, _), b) => decorate_var b $ str_v tctx x
	        | Abs (pn, e) => 
                  let 
                    val (inames, enames) = ptrn_names pn
                    val pn = str_pn (sctx, kctx, cctx) pn
                    val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
	            val e = str_e ctx e
                  in
                    sprintf "(fn $ => $)" [pn, e]
                  end
	        | App (e1, e2) => sprintf "($ $)" [str_e ctx e1, str_e ctx e2]
	        | TT _ => "()"
	        | Pair _ =>
                  let
                    val es = collect_Pair e
                  in
                    sprintf "($)" [join ", " $ map (str_e ctx) es]
                  end
	        | Fst e => sprintf "(fst $)" [str_e ctx e]
	        | Snd e => sprintf "(snd $)" [str_e ctx e]
	        | AbsI (s, (name, _), e, _) => sprintf "(fn {$ : $} => $)" [name, str_s sctx s, str_e (name :: sctx, kctx, cctx, tctx) e]
	        | AppI (e, i) => sprintf "($ {$})" [str_e ctx e, str_i sctx i]
	        | Let (decls, e, _) => 
                  let val (decls, ctx) = str_decls ctx decls
                  in
                    sprintf "let$ in $ end" [join_prefix " " decls, str_e ctx e]
                  end
	        | Ascription (e, t) => sprintf "($ : $)" [str_e ctx e, str_mt skctx t]
	        | AscriptionTime (e, d) => sprintf "($ |> $)" [str_e ctx e, str_i sctx d]
	        | BinOp (opr, e1, e2) => sprintf "($ $ $)" [str_e ctx e1, str_bin_op opr, str_e ctx e2]
	        | ConstInt (n, _) => str_int n
	        | AppConstr (((x, _), b), is, e) => sprintf "($$ $)" [decorate_var b $ str_v cctx x, (join "" o map (prefix " ") o map (fn i => sprintf "{$}" [str_i sctx i])) is, str_e ctx e]
	        | Case (e, return, rules, _) => sprintf "(case $ $of $)" [str_e ctx e, str_return skctx return, join " | " (map (str_rule ctx) rules)]
	        | Never (t, _) => sprintf "(never [$])" [str_mt skctx t]
            end

        and str_decls (ctx as (sctx, kctx, cctx, tctx)) decls =
            let fun f (decl, (acc, ctx)) =
                    let val (s, ctx) = str_decl ctx decl
                    in
                      (s :: acc, ctx)
                    end
                val (decls, ctx) = foldl f ([], ctx) decls
                val decls = rev decls
            in
              (decls, ctx)
            end
              
        and str_decl (ctx as (sctx, kctx, cctx, tctx)) decl =
            case decl of
                Val (tnames, pn, e, _) =>
                let 
                  val ctx' as (sctx', kctx', cctx', _) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
                  val tnames = (join "" o map (fn nm => sprintf " [$]" [nm]) o map fst) tnames
                  val (inames, enames) = ptrn_names pn
                  val pn = str_pn (sctx', kctx', cctx') pn
                  val e = str_e ctx' e
	          val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
                in
                  (sprintf "val$ $ = $" [tnames, pn, e], ctx)
                end
              | Rec (tnames, (name, _), (binds, ((t, d), e)), _) =>
                let 
	          val ctx as (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
                  val ctx_ret = ctx
                  val ctx as (sctx, kctx, cctx, tctx) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
                  val tnames = (join "" o map (fn nm => sprintf " [$]" [nm]) o map fst) tnames
                  fun f (bind, (binds, ctx as (sctx, kctx, cctx, tctx))) =
                      case bind of
                          SortingST ((name, _), s) => 
                          (sprintf "{$ : $}" [name, str_s sctx s] :: binds, (name :: sctx, kctx, cctx, tctx))
                        | TypingST pn =>
                          let
                            val (inames, enames) = ptrn_names pn
                          in
                            (str_pn (sctx, kctx, cctx) pn :: binds, (inames @ sctx, kctx, cctx, enames @ tctx))
                          end
                  val (binds, ctx as (sctx, kctx, cctx, tctx)) = foldl f ([], ctx) binds
                  val binds = rev binds
                  val binds = (join "" o map (prefix " ")) binds
                  val t = str_mt (sctx, kctx) t
                  val d = str_i sctx d
                  val e = str_e ctx e
                in
                  (sprintf "rec$ $$ : $ |> $ = $" [tnames, name, binds, t, d, e], ctx_ret)
                end
              | Datatype (name, tnames, sorts, constrs, _) =>
                let val str_tnames = (join_prefix " " o rev) tnames
                    fun str_constr_decl (cname, ibinds, _) =
                        let 
                          val (name_sorts, (t, idxs)) = unfold_ibinds ibinds
                          val (name_sorts, sctx') = str_sortings sctx name_sorts
                          val name_sorts = map (fn (nm, s) => sprintf "$ : $" [nm, s]) name_sorts
                        in
                          sprintf "$ of$ $ ->$$ $" [cname, (join_prefix " " o map (surround "{" "}")) name_sorts, str_mt (sctx', rev tnames @ name :: kctx) t, (join_prefix " " o map (surround "{" "}" o str_i sctx') o rev) idxs, str_tnames, name]
                        end
                    val s = sprintf "datatype$$ $ = $" [(join_prefix " " o map (surround "{" "}" o str_s sctx) o rev) sorts, str_tnames, name, join " | " (map str_constr_decl constrs)]
                    val cnames = map #1 constrs
                    val ctx = (sctx, name :: kctx, rev cnames @ cctx, tctx)
                in
                  (s, ctx)
                end
              | IdxDef ((name, r), s, i) =>
                (sprintf "type idx $ : $ = $" [name, str_s sctx s, str_i sctx i], (name :: sctx, kctx, cctx, tctx))
              | AbsIdx (((name, r1), s, i), decls, _) =>
                let
                  val ctx' = (name :: sctx, kctx, cctx, tctx)
                  val (decls, ctx') = str_decls ctx' decls
                in
                  (sprintf "abstype idx $ : $ = $ with$ end" [name, str_s sctx s, str_i sctx i, join_prefix " " decls], ctx')
                end

        and str_rule (ctx as (sctx, kctx, cctx, tctx)) (pn, e) =
            let val (inames, enames) = ptrn_names pn
	        val ctx' = (inames @ sctx, kctx, cctx, enames @ tctx)
            in
	      sprintf "$ => $" [str_pn (sctx, kctx, cctx) pn, str_e ctx' e]
            end

        (* region calculations *)

        fun get_region_i i =
            case i of
                VarI (_, r) => r
              | ConstIN (_, r) => r
              | ConstIT (_, r) => r
              | UnOpI (_, _, r) => r
              | DivI (i1, (_, r2)) => combine_region (get_region_i i1) r2
              | ExpI (i1, (_, r2)) => combine_region (get_region_i i1) r2
              | BinOpI (_, i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
              | Ite (_, _, _, r) => r
              | TrueI r => r
              | FalseI r => r
              | TTI r => r
              | TimeAbs (_, _, r) => r
              | AdmitI r => r
              | UVarI (_, r) => r

        fun set_region_i i r =
            case i of
                VarI (a, _) => VarI (a, r)
              | ConstIN (a, _) => ConstIN (a, r)
              | ConstIT (a, _) => ConstIT (a, r)
              | UnOpI (opr, i, _) => UnOpI (opr, i, r)
              | DivI (i1, (n2, _)) => DivI (set_region_i i1 r, (n2, r))
              | ExpI (i1, (n2, _)) => ExpI (set_region_i i1 r, (n2, r))
              | BinOpI (opr, i1, i2) => BinOpI (opr, set_region_i i1 r, set_region_i i2 r)
              | Ite (i1, i2, i3, _) => Ite (i1, i2, i3, r)
              | TrueI _ => TrueI r
              | FalseI _ => FalseI r
              | TTI _ => TTI r
              | TimeAbs (name, i, _) => TimeAbs (name, i, r)
              | AdmitI _ => AdmitI r
              | UVarI (a, _) => UVarI (a, r)

        fun get_region_p p = 
            case p of
                True r => r
              | False r => r
              | Not (_, r) => r
              | BinConn (_, p1, p2) => combine_region (get_region_p p1) (get_region_p p2)
              | BinPred (_, i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
              | Quan (_, _, _, _, r) => r

        fun set_region_p p r = 
            case p of
                True _ => True r
              | False _ => False r
              | Not (p, _) => Not (p, r)
              | BinConn (opr, p1, p2) => BinConn (opr, set_region_p p1 r, set_region_p p2 r)
              | BinPred (opr, i1, i2) => BinPred (opr, set_region_i i1 r, set_region_i i2 r)
              | Quan (q, bs, name, p, _) => Quan (q, bs, name, p, r)

        fun get_region_s s = 
            case s of
                Basic (_, r) => r
              | Subset (_, _, r) => r
              | UVarS (_, r) => r

        fun get_region_mt t = 
            case t of
                Arrow (t1, d, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
              | Unit r => r
              | Prod (t1, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
              | UniI (_, _, r) => r
              | AppV (_, _, _, r) => r
              | BaseType (_, r) => r
              | UVar (_, r) => r

        fun get_region_t t = 
            case t of
                Mono t => get_region_mt t
              | Uni (_, _, r) => r

        fun get_region_pn pn = 
            case pn of
                ConstrP (_, _, _, r) => r
              | VarP (_, r) => r
              | PairP (pn1, pn2) => combine_region (get_region_pn pn1) (get_region_pn pn2)
              | TTP r => r
              | AliasP (_, _, r) => r
              | AnnoP (pn, t) => combine_region (get_region_pn pn) (get_region_mt t)

        fun get_region_e e = 
            case e of
                Var ((_, r), _) => r
              | Abs (pn, e) => combine_region (get_region_pn pn) (get_region_e e)
              | App (e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
              | TT r => r
              | Pair (e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
              | Fst e => get_region_e e
              | Snd e => get_region_e e
              | AbsI (_, _, _, r) => r
              | AppI (e, i) => combine_region (get_region_e e) (get_region_i i)
              | BinOp (_, e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
              | ConstInt (_, r) => r
              | AppConstr (((_, r), _), _, e) => combine_region r (get_region_e e)
              | Case (_, _, _, r) => r
              | Never (_, r) => r
              | Let (_, _, r) => r
              | Ascription (e, t) => combine_region (get_region_e e) (get_region_mt t)
              | AscriptionTime (e, i) => combine_region (get_region_e e) (get_region_i i)
                                                        
        fun get_region_rule (pn, e) = combine_region (get_region_pn pn) (get_region_e e)

        fun get_region_dec dec =
            case dec of
                Val (_, _, _, r) => r
              | Rec (_, _, _, r) => r
              | Datatype (_, _, _, _, r) => r
              | IdxDef ((_, r), _, i) => combine_region r (get_region_i i)
              | AbsIdx (_, _, r) => r

        local
          val changed = ref false
          fun unset () = changed := false
          fun set () = changed := true
          fun mark a = (set (); a)
          fun passi i =
	      case i of
                  DivI (i1, n2) => DivI (passi i1, n2)
                | ExpI (i1, n2) => ExpI (passi i1, n2)
	        | BinOpI (opr, i1, i2) =>
                  let
                    fun def () = BinOpI (opr, passi i1, passi i2)
                  in
                    case opr of
	                MaxI =>
	                if eq_i i1 i2 then
		          (set ();
                           i1)
	                else
		          BinOpI (opr, passi i1, passi i2)
	              | MinI =>
	                if eq_i i1 i2 then
		          (set ();
                           i1)
	                else
		          BinOpI (opr, passi i1, passi i2)
	              | AddI => 
	                if eq_i i1 (T0 dummy) then
                          (set ();
                           i2)
	                else if eq_i i2 (T0 dummy) then
                          (set ();
                           i1)
	                else
		          BinOpI (opr, passi i1, passi i2)
	              | MultI => 
	                if eq_i i1 (T0 dummy) then
                          (set ();
                           (T0 dummy))
	                else if eq_i i2 (T0 dummy) then
                          (set ();
                           (T0 dummy))
	                else if eq_i i1 (T1 dummy) then
                          (set ();
                           i2)
	                else if eq_i i2 (T1 dummy) then
                          (set ();
                           i1)
	                else
		          BinOpI (opr, passi i1, passi i2)
                      | TimeApp =>
		        BinOpI (opr, passi i1, passi i2)
                      | EqI =>
                        if eq_i i1 i2 then
                          mark $ TrueI $ get_region_i i
                        else def ()
                      | AndI =>
                        if eq_i i1 (TrueI dummy) then
                          mark i2
                        else if eq_i i2 (TrueI dummy) then
                          mark i1
                        else if eq_i i1 (FalseI dummy) then
                          mark $ FalseI $ get_region_i i
                        else if eq_i i2 (FalseI dummy) then
                          mark $ FalseI $ get_region_i i
                        else
                          def ()
                      | ExpNI =>
                        def ()
                  end
                | Ite (i, i1, i2, r) =>
                  if eq_i i (TrueI dummy) then
                    mark i1
                  else if eq_i i (FalseI dummy) then
                    mark i2
                  else
                    Ite (passi i, passi i1, passi i2, r)
                | UnOpI (opr, i, r) =>
                  UnOpI (opr, passi i, r)
                | TimeAbs ((name, r1), i, r) =>
                  TimeAbs ((name, r1), passi i, r)
	        | TrueI _ => i
	        | FalseI _ => i
	        | TTI _ => i
                | ConstIN _ => i
                | ConstIT _ => i
                | VarI _ => i
                | AdmitI _ => i
                | UVarI _ => i

          fun passp p = 
	      case p of
	          BinConn (opr, p1, p2) => 
                  (case opr of
                       And =>
	               if eq_p p1 (True dummy) then
                         (set ();
                          p2)
	               else if eq_p p2 (True dummy) then
                         (set ();
                          p1)
	               else
	                 BinConn (opr, passp p1, passp p2)
                     | Or =>
	               if eq_p p1 (False dummy) then
                         (set ();
                          p2)
	               else if eq_p p2 (False dummy) then
                         (set ();
                          p1)
	               else
	                 BinConn (opr, passp p1, passp p2)
                     | _ =>
	               BinConn (opr, passp p1, passp p2)
                  )
	        | BinPred (opr, i1, i2) => 
	          BinPred (opr, passi i1, passi i2)
                | Not (p, r) => Not (passp p, r)
                | Quan (q, bs, name, p, r) => 
                  (case q of
                       Forall =>
	               if eq_p p (True dummy) then
                         p
                       else
                         Quan (q, bs, name, passp p, r)
                     | Exists _ =>
                       Quan (q, bs, name, passp p, r)
                  )
	        | True _ => p
	        | False _ => p
                               
          fun until_unchanged f a = 
	      let fun loop a =
	              let
                        val _ = unset ()
                        val a = f a
                      in
		        if !changed then loop a
		        else a
	              end
              in
	        loop a
	      end
        in
        val simp_i = until_unchanged passi
        val simp_p = until_unchanged passp
        fun simp_vc (ctx, ps, p, r) = (ctx, map simp_p ps, simp_p p, r)
        end

        fun simp_ibind f (BindI (name, inner)) = BindI (name, f inner)

        fun simp_s s =
            case s of
	        Basic b => Basic b
              | Subset (b, bind, r) => Subset (b, simp_ibind simp_p bind, r)
              | UVarS u => UVarS u

        fun simp_mt t =
	    case t of
	        Arrow (t1, d, t2) => Arrow (simp_mt t1, simp_i d, simp_mt t2)
              | Unit r => Unit r
	      | Prod (t1, t2) => Prod (simp_mt t1, simp_mt t2)
	      | AppV (x, ts, is, r) => AppV (x, map simp_mt ts, map simp_i is, r)
	      | UniI (s, bind, r) => UniI (simp_s s, simp_ibind simp_mt bind, r)
	      | BaseType a => BaseType a
              | UVar u => UVar u

        fun simp_t t =
	    case t of
	        Mono t => Mono (simp_mt t)
	      | Uni (name, t, r) => Uni (name, simp_t t, r)

        fun is_value (e : expr) : bool =
            case e of
                Var _ => true
              | App _ => false
              | Abs _ => true
              | TT _ => true
              | Pair (e1, e2) => is_value e1 andalso is_value e2
              | Fst _ => false
              | Snd _ => false
              | AbsI _ => true
              | AppI _ => false
              | Let _ => false
              | Ascription _ => false
              | AscriptionTime _ => false
              | BinOp _ => false
              | ConstInt _ => true
              | AppConstr (_, _, e) => is_value e
              | Case _ => false
              | Never _ => true

        datatype ('var, 'prop) hyp = 
                 VarH of 'var
                 | PropH of 'prop
                              
        fun append_hyps_vc hs vc = mapFst (fn hs' => hs' @ hs) vc
        fun add_hyp_vc h vc = append_hyps_vc [h] vc
        fun append_hyps hs vcs = map (append_hyps_vc hs) vcs
        fun add_hyp h vcs = append_hyps [h] vcs
                                        
        fun prop2vc p =
            let
            in
              case p of
                  Quan (Forall, bs, (name, r), p, r_all) =>
                  let
                    val vc = prop2vc p
                    val vc = add_hyp_vc (VarH (name, (bs, r_all))) vc
                  in
                    vc
                  end
                | BinConn (Imply, p1, p) =>
                  let
                    val vc = prop2vc p
                    val vc = add_hyp_vc (PropH p1) vc
                  in
                    vc
                  end
                | _ => ([], p)
            end

        end
                                                                
structure StringVar = struct
type var = string
fun str_v ctx x : string = x
fun eq_v (x : var, y) = x = y
end

structure IntVar = struct
open Util
type var = int
fun str_v ctx x : string =
    (* sprintf "%$" [str_int x] *)
    case nth_error ctx x of
        SOME name => name
      | NONE => "unbound_" ^ str_int x
fun eq_v (x : var, y) = x = y
end

structure Underscore = struct
type 'bsort uvar_bs = unit
type ('bsort, 'idx) uvar_i = unit
type 'sort uvar_s = unit
type 'mtype uvar_mt = unit
fun str_uvar_bs (_ : 'a -> string) (_ : 'a uvar_bs) = "_"
fun str_uvar_i (_ : string list -> 'idx -> string) (_ : string list) (_ : ('bsort, 'idx) uvar_i) = "_"
fun str_uvar_mt (_ : string list * string list -> 'mtype -> string) (_ : string list * string list) (_ : 'mtype uvar_mt) = "_"
fun eq_uvar_i (_, _) = false
end

structure NamefulExpr = ExprFun (structure Var = StringVar structure UVar = Underscore)
structure UnderscoredExpr = ExprFun (structure Var = IntVar structure UVar = Underscore)
