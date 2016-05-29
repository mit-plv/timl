structure BaseSorts = struct
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

structure BaseTypes = struct
datatype base_type =
         Int
end
                        
functor ExprFun (structure Var : VAR structure UVar : UVAR) = struct
        open Var
        open BaseSorts
        open BaseTypes
        open Util
        open Operators
        open UVar
        open Region
        (* open ExprUtil *)
        open Bind

        type id = var * region
        type name = string * region

        datatype bsort = 
                 Base of base_sort
                 | UVarBS of bsort uvar_bs

        (* Curve out a fragment of module expression that is not a full component list ('struct' in ML) that involves types and terms, to avoid making everything mutually dependent. (This means I can't do module substitution because the result may not be expressible.) It coincides with the concept 'projectible' or 'determinate'. *)
        (* datatype mod_projectible = *)
        (*          ModVar of id *)
        (* | ModSel of mod_projectible * id *)
        type mod_projectible = id
                                 
        type long_id = mod_projectible option * id
                                                  
        type 'body ibind = 'body bind
        type 'body tbind = 'body bind
        type ('classifier, 'name, 'inner) ibinds = ('classifier, 'name, 'inner) binds
        type ('classifier, 'name, 'inner) tbinds = ('classifier, 'name, 'inner) binds
        val unfold_ibinds = unfold_binds
        val fold_ibinds = fold_binds
                              
        datatype idx =
	         VarI of long_id
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
                 | Quan of (idx -> unit) option (*for linking idx inferer with types*) quan * bsort * (name * prop) ibind * region

        (* index sort *)
        datatype sort =
	         Basic of bsort * region
	         | Subset of (bsort * region) * (name * prop) ibind * region
                 | UVarS of sort uvar_s * region

        datatype kind = 
	         ArrowK of bool (* is datatype *) * int * sort list

        (* monotypes *)
        datatype mtype = 
	         Arrow of mtype * idx * mtype
	         | BaseType of base_type * region
                 | UVar of mtype uvar_mt * region
                 | Unit of region
	         | Prod of mtype * mtype
	         | UniI of sort * (name * mtype) ibind * region
                 | MtVar of long_id
                 | MtApp of mtype * mtype
                 | MtAbs of (name * mtype) tbind * region
                 | MtAppI of mtype * idx
                 | MtAbsI of sort * (name * mtype) ibind * region
                 | AppV of long_id * mtype list * idx list * region (* the first operant of App can only be a type variable. The degenerated case of no-arguments is also included *)

        datatype ty = 
	         Mono of mtype
	         | Uni of (name * ty) tbind * region

        type constr_core = (sort, string, mtype * idx list) ibinds
        type constr_decl = string * constr_core * region
        type constr = long_id(*family*) * string list(*type argument names*) * constr_core

        type return = mtype option * idx option

        datatype ptrn =
	         ConstrP of (long_id * bool(*eia*)) * string list * ptrn option * region (* eia : is explicit index arguments? *)                                         
                 | VarP of name
                 | PairP of ptrn * ptrn
                 | TTP of region
                 | AliasP of name * ptrn * region
                 | AnnoP of ptrn * mtype

        datatype stbind = 
                 SortingST of name * sort
                 | TypingST of ptrn

        datatype expr =
	         Var of long_id * bool(*eia*)
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
	         | AppConstr of (long_id * bool) * idx list * expr
	         | Case of expr * return * (ptrn * expr) list * region
	         | Let of return * decl list * expr * region
	         | Ascription of expr * mtype
	         | AscriptionTime of expr * idx
	         | Never of mtype * region


             and decl =
                 Val of name list * ptrn * expr * region
                 | Rec of name list * name * (stbind list * ((mtype * idx) * expr)) * region
	         | Datatype of datatype_def
                 | IdxDef of name * sort * idx
                 | AbsIdx of (name * sort * idx) * decl list * region
                 | TypeDef of name * mtype
                 | Open of mod_projectible
                             withtype datatype_def = string * string list * sort list * constr_decl list * region

        datatype spec =
                 SpecVal of name * ty
                 | SpecDatatype of datatype_def
                 | SpecIdx of name * sort
                 | SpecType of name * kind
                 | SpecTypeDef of name * ty
                                           
        datatype sgn =
                 SigComponents of sig_comp list * region
             (* | SigVar of id *)
             (* | SigWhere of sgn * (id * mtype) *)

             and sig_comp =
                 ScSpec of name * spec * region
        (* | ScModSpec of name * sgn *)
        (* | Include of sgn *)

        datatype mod =
                 ModComponents of (* mod_comp *)decl list * region
                 (* | ModProjectible of mod_projectible *)
                 | ModSeal of mod * sgn
                 | ModTransparentAscription of mod * sgn
        (* | ModFunctorApp of id * mod (* list *) *)
                                                       
        (* and mod_comp = *)
        (*     McDecl of decl *)
        (* | McModBind of name * mod *)

        datatype top_bind =
                 TopModBind of name * mod
                 (* | TopSigBind of name * sgn *)
                 | TopModSpec of name * sgn
                 | TopFunctorBind of name * (name * sgn) (* list *) * mod
                 | TopFunctorApp of name * id * mod (* list *)

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
                UniI (s, Bind ((name, _), t), _) =>
                let val (binds, t) = collect_UniI t
                in
                  ((name, s) :: binds, t)
                end
              | _ => ([], t)

        fun collect_Uni t =
            case t of
                Uni (Bind (name, t), _) =>
                let val (names, t) = collect_Uni t
                in
                  (name :: names, t)
                end
              | Mono t => ([], t)

        fun constr_type VarT shiftx_v (((m, (family, family_r)), tnames, ibinds) : constr) = 
            let 
              val (ns, (t, is)) = unfold_ibinds ibinds
              val ts = (map (fn x => VarT (NONE, (x, dummy))) o rev o range o length) tnames
	      val t2 = AppV ((m, (shiftx_v 0 (length tnames) family, family_r)), ts, is, dummy)
	      val t = Arrow (t, T0 dummy, t2)
	      val t = foldr (fn ((name, s), t) => UniI (s, Bind ((name, dummy), t), dummy)) t ns
              val t = Mono t
	      val t = foldr (fn (name, t) => Uni (Bind ((name, dummy), t), dummy)) t tnames
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

        fun eq_option eq (a, a') =
            case (a, a') of
                (SOME v, SOME v') => eq (v, v')
              | _ => false

        fun eq_id ((x, _), (x', _)) =
            eq_v (x, x')
                 
        fun eq_long_id ((m, x), (m', x')) =
            eq_option eq_id (m, m') andalso eq_id (x, x')
                                                  
        fun eq_i i i' =
            let
              fun loop i i' =
                  case i of
                      VarI x => (case i' of VarI x' => eq_long_id (x, x') | _ => false)
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
              | Quan (q, bs, Bind (_, p), _) => (case p' of Quan (q', bs', Bind (_, p'), _) => eq_quan q q' andalso eq_bs bs bs' andalso eq_p p p' | _ => false)

        (* pretty-printers *)

        fun str_bs (s : bsort) =
            case s of
                Base s => str_b s
              | UVarBS u => str_uvar_bs str_bs u

        fun str_id ctx (x, _) =
            str_v ctx x
                  
        fun str_long_id gctx ctx (m, x) =
            let
              val m = default "" $ Option.map (fn x => str_id gctx x ^ ".") m
              val x = str_id ctx x
            in
              m ^ x
            end
              
        fun str_i gctx ctx (i : idx) : string =
            let
              val str_i = str_i gctx
            in
              case i of
                  VarI x => str_long_id gctx ctx x
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
            end

        fun str_p gctx ctx p =
            let
              val str_p = str_p gctx
            in
              case p of
                  True _ => "True"
                | False _ => "False"
                | Not (p, _) => sprintf "(~ $)" [str_p ctx p]
                | BinConn (opr, p1, p2) => sprintf "($ $ $)" [str_p ctx p1, str_bin_conn opr, str_p ctx p2]
                (* | BinPred (BigO, i1, i2) => sprintf "($ $ $)" [str_bin_pred BigO, str_i ctx i1, str_i ctx i2] *)
                | BinPred (opr, i1, i2) => sprintf "($ $ $)" [str_i gctx ctx i1, str_bin_pred opr, str_i gctx ctx i2]
                | Quan (q, bs, Bind ((name, _), p), _) => sprintf "($ ($ : $) $)" [str_quan q, name, str_bs bs, str_p (name :: ctx) p]
            end

        fun str_s gctx ctx (s : sort) : string =
            let
              val str_s = str_s gctx
            in
              case s of
                  Basic (bs, _) => str_bs bs
                | Subset ((bs, _), (Bind ((name, _), p)), _) =>
                  let
                    fun default () = sprintf "{ $ : $ | $ }" [name, str_bs bs, str_p gctx (name :: ctx) p]
                  in
                    case (bs, p) of
                        (Base (TimeFun arity), BinPred (BigO, VarI x, i2)) =>
                        if str_long_id gctx (name :: ctx) x = name then
                          sprintf "BigO $ $" [str_int arity, str_i gctx (name :: ctx) i2]
                        else
                          default ()
                      | _ => default ()
                  end
                | UVarS _ => "_"
            end

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

        fun str_tbinds gctx ctx binds =
            let
              fun f (bind, (acc, (sctx, kctx))) =
                  case bind of
                      KindingT name => (KindingT name :: acc, (sctx, name :: kctx))
                    | SortingT (name, s) => (SortingT (name, str_s gctx sctx s) :: acc, (name :: sctx, kctx))
              val (binds, ctx) = foldl f ([], ctx) binds
              val binds = rev binds
            in
              (binds, ctx)
            end
              
        fun str_sortings gctx ctx binds =
            let val (binds, ctx) = str_tbinds gctx (ctx, []) (map SortingT binds)
                fun f bind = case bind of SortingT p => p | _ => raise Impossible "str_tbinds shouldn't return Kinding"
                val binds = map f binds
            in
              (binds, fst ctx)
            end

        fun str_bt bt =
            case bt of
                Int => "int"
                         
        fun str_mt gctx (ctx as (sctx, kctx)) (t : mtype) : string =
            let
              val str_mt = str_mt gctx
            in
              case t of
                  Arrow (t1, d, t2) =>
                  if eq_i d (T0 dummy) then
                    sprintf "($ -> $)" [str_mt ctx t1, str_mt ctx t2]
                  else
                    sprintf "($ -- $ --> $)" [str_mt ctx t1, str_i gctx sctx d, str_mt ctx t2]
                | Unit _ => "unit"
                | Prod (t1, t2) => sprintf "($ * $)" [str_mt ctx t1, str_mt ctx t2]
                | UniI _ =>
                  let
                    val (binds, t) = collect_UniI t
                  in
                    str_uni gctx ctx (map SortingT binds, t)
                  end
                | MtVar x => str_long_id gctx kctx x
                | MtApp (t1, t2) => sprintf "($ $)" [str_mt ctx t1, str_mt ctx t2]
                | MtAbs (Bind ((name, _), t), _) => sprintf "(fn [$] => $)" [name, str_mt (sctx, name :: kctx) t]
                | MtAppI (t, i) => sprintf "($ $)" [str_mt ctx t, str_i gctx sctx i]
                | MtAbsI (s, Bind ((name, _), t), _) => sprintf "(fn {$ : $} => $)" [name, str_s gctx sctx s, str_mt (name :: sctx, kctx) t]
                | AppV (x, ts, is, _) => 
                  if null ts andalso null is then
	            str_long_id gctx kctx x
                  else
	            sprintf "($$$)" [(join "" o map (suffix " ") o map (surround "{" "}") o map (str_i gctx sctx) o rev) is, (join "" o map (suffix " ") o map (str_mt ctx) o rev) ts, str_long_id gctx kctx x]
                | BaseType (bt, _) => str_bt bt
                | UVar (u, _) => str_uvar_mt str_mt ctx u
            end

        and str_uni gctx ctx (binds, t) =
            let 
              val (binds, ctx) = str_tbinds gctx ctx binds
              fun f bind =
                  case bind of
                      KindingT name => name
                    | SortingT (name, s) => sprintf "{$ : $}" [name, s]
              val binds = map f binds
            in
              sprintf "(forall$, $)" [join_prefix " " binds, str_mt gctx ctx t]
            end
              
        fun str_t gctx (ctx as (sctx, kctx)) (t : ty) : string =
            case t of
                Mono t => str_mt gctx ctx t
              | Uni _ => str_uni gctx ctx (collect_Uni_UniI t)

        fun str_k gctx ctx (k : kind) : string = 
            case k of
                ArrowK (_, n, sorts) => sprintf "($$Type)" [if n = 0 then "" else join " * " (repeat n "Type") ^ " => ", if null sorts then "" else join " * " (map (str_s gctx ctx) sorts) ^ " => "]

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

        fun decorate_var eia s = (if eia then "@" else "") ^ s
                                                               
        fun str_pn gctx (ctx as (sctx, kctx, cctx)) pn =
            let
              val str_pn = str_pn gctx
            in
              case pn of
                  ConstrP ((x, eia), inames, pn, _) => sprintf "$$$" [decorate_var eia $ str_long_id gctx cctx x, join_prefix " " $ map (surround "{" "}") inames, str_opt (fn pn => " " ^ str_pn ctx pn) pn]
                | VarP (name, _) => name
                | PairP (pn1, pn2) => sprintf "($, $)" [str_pn ctx pn1, str_pn ctx pn2]
                | TTP _ => "()"
                | AliasP ((name, _), pn, _) => sprintf "$ as $" [name, str_pn ctx pn]
                | AnnoP (pn, t) => sprintf "($ : $)" [str_pn ctx pn, str_mt gctx (sctx, kctx) t]
            end

        fun str_return gctx (skctx as (sctx, _)) return =
            case return of
                (NONE, NONE) => ""
              | (SOME t, NONE) => sprintf "return $ " [str_mt gctx skctx t]
              | (NONE, SOME d) => sprintf "return using $ " [str_i gctx sctx d]
              | (SOME t, SOME d) => sprintf "return $ using $ " [str_mt gctx skctx t, str_i gctx sctx d]

        fun add_sorting name (sctx, kctx, cctx, tctx) = (name :: sctx, kctx, cctx, tctx)
        fun add_kinding name (sctx, kctx, cctx, tctx) = (sctx, name :: kctx, cctx, tctx)
        fun add_typing name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
                                                          
        fun str_e gctx (ctx as (sctx, kctx, cctx, tctx)) (e : expr) : string =
            let
              val str_e = str_e gctx
              fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx) 
              val skctx = (sctx, kctx) 
            in
              case e of
	          Var (x, b) => decorate_var b $ str_long_id gctx tctx x
	        | Abs (pn, e) => 
                  let 
                    val (inames, enames) = ptrn_names pn
                    val pn = str_pn gctx (sctx, kctx, cctx) pn
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
	        | AbsI (s, (name, _), e, _) => sprintf "(fn {$ : $} => $)" [name, str_s gctx sctx s, str_e (name :: sctx, kctx, cctx, tctx) e]
	        | AppI (e, i) => sprintf "($ {$})" [str_e ctx e, str_i gctx sctx i]
	        | Let (return, decls, e, _) => 
                  let
                    val return = str_return gctx (sctx, kctx) return
                    val (decls, ctx) = str_decls gctx ctx decls
                  in
                    sprintf "let $$ in $ end" [return, join_prefix " " decls, str_e ctx e]
                  end
	        | Ascription (e, t) => sprintf "($ : $)" [str_e ctx e, str_mt gctx skctx t]
	        | AscriptionTime (e, d) => sprintf "($ |> $)" [str_e ctx e, str_i gctx sctx d]
	        | BinOp (opr, e1, e2) => sprintf "($ $ $)" [str_e ctx e1, str_bin_op opr, str_e ctx e2]
	        | ConstInt (n, _) => str_int n
	        | AppConstr ((x, b), is, e) => sprintf "($$ $)" [decorate_var b $ str_long_id gctx cctx x, (join "" o map (prefix " ") o map (fn i => sprintf "{$}" [str_i gctx sctx i])) is, str_e ctx e]
	        | Case (e, return, rules, _) => sprintf "(case $ $of $)" [str_e ctx e, str_return gctx skctx return, join " | " (map (str_rule gctx ctx) rules)]
	        | Never (t, _) => sprintf "(never [$])" [str_mt gctx skctx t]
            end

        and str_decls gctx (ctx as (sctx, kctx, cctx, tctx)) decls =
            let
              fun f (decl, (acc, ctx)) =
                  let val (s, ctx) = str_decl gctx ctx decl
                  in
                    (s :: acc, ctx)
                  end
              val (decls, ctx) = foldl f ([], ctx) decls
              val decls = rev decls
            in
              (decls, ctx)
            end
              
        and str_decl gctx (ctx as (sctx, kctx, cctx, tctx)) decl =
            let
              val str_decl = str_decl gctx
            in
              case decl of
                  Val (tnames, pn, e, _) =>
                  let 
                    val ctx' as (sctx', kctx', cctx', _) = (sctx, (rev o map fst) tnames @ kctx, cctx, tctx)
                    val tnames = (join "" o map (fn nm => sprintf " [$]" [nm]) o map fst) tnames
                    val (inames, enames) = ptrn_names pn
                    val pn = str_pn gctx (sctx', kctx', cctx') pn
                    val e = str_e gctx ctx' e
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
                            (sprintf "{$ : $}" [name, str_s gctx sctx s] :: binds, (name :: sctx, kctx, cctx, tctx))
                          | TypingST pn =>
                            let
                              val (inames, enames) = ptrn_names pn
                            in
                              (str_pn gctx (sctx, kctx, cctx) pn :: binds, (inames @ sctx, kctx, cctx, enames @ tctx))
                            end
                    val (binds, ctx as (sctx, kctx, cctx, tctx)) = foldl f ([], ctx) binds
                    val binds = rev binds
                    val binds = (join "" o map (prefix " ")) binds
                    val t = str_mt gctx (sctx, kctx) t
                    val d = str_i gctx sctx d
                    val e = str_e gctx ctx e
                  in
                    (sprintf "rec$ $$ : $ |> $ = $" [tnames, name, binds, t, d, e], ctx_ret)
                  end
                | Datatype (name, tnames, sorts, constrs, _) =>
                  let val str_tnames = (join_prefix " " o rev) tnames
                      fun str_constr_decl (cname, ibinds, _) =
                          let 
                            val (name_sorts, (t, idxs)) = unfold_ibinds ibinds
                            val (name_sorts, sctx') = str_sortings gctx sctx name_sorts
                            val name_sorts = map (fn (nm, s) => sprintf "$ : $" [nm, s]) name_sorts
                          in
                            sprintf "$ of$ $ ->$$ $" [cname, (join_prefix " " o map (surround "{" "}")) name_sorts, str_mt gctx (sctx', rev tnames @ name :: kctx) t, (join_prefix " " o map (surround "{" "}" o str_i gctx sctx') o rev) idxs, str_tnames, name]
                          end
                      val s = sprintf "datatype$$ $ = $" [(join_prefix " " o map (surround "{" "}" o str_s gctx sctx) o rev) sorts, str_tnames, name, join " | " (map str_constr_decl constrs)]
                      val cnames = map #1 constrs
                      val ctx = (sctx, name :: kctx, rev cnames @ cctx, tctx)
                  in
                    (s, ctx)
                  end
                | IdxDef ((name, r), s, i) =>
                  (sprintf "type idx $ : $ = $" [name, str_s gctx sctx s, str_i gctx sctx i], (name :: sctx, kctx, cctx, tctx))
                | AbsIdx (((name, r1), s, i), decls, _) =>
                  let
                    val ctx' = (name :: sctx, kctx, cctx, tctx)
                    val (decls, ctx') = str_decls gctx ctx' decls
                  in
                    (sprintf "abstype idx $ : $ = $ with$ end" [name, str_s gctx sctx s, str_i gctx sctx i, join_prefix " " decls], ctx')
                  end
                | TypeDef ((name, _), t) =>
                  (sprintf "type $ = $" [name, str_mt gctx (sctx, kctx) t], add_kinding name ctx)
                | Open (m, _) =>
                  (sprintf "open $" [str_v gctx m], ctx)
            end
              
        and str_rule gctx (ctx as (sctx, kctx, cctx, tctx)) (pn, e) =
            let val (inames, enames) = ptrn_names pn
	        val ctx' = (inames @ sctx, kctx, cctx, enames @ tctx)
            in
	      sprintf "$ => $" [str_pn gctx (sctx, kctx, cctx) pn, str_e gctx ctx' e]
            end

        (* region calculations *)

        fun get_region_long_id (_, (_, r)) = r

        fun set_region_long_id (m, (x, _)) r = (m, (x, r))
                                  
        fun get_region_i i =
            case i of
                VarI x => get_region_long_id x
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
                VarI x => VarI $ set_region_long_id x r
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
              | Quan (_, _, _, r) => r

        fun set_region_p p r = 
            case p of
                True _ => True r
              | False _ => False r
              | Not (p, _) => Not (p, r)
              | BinConn (opr, p1, p2) => BinConn (opr, set_region_p p1 r, set_region_p p2 r)
              | BinPred (opr, i1, i2) => BinPred (opr, set_region_i i1 r, set_region_i i2 r)
              | Quan (q, bs, bind, _) => Quan (q, bs, bind, r)

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
              | MtVar y => get_region_long_id y
              | MtApp (t1, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
              | MtAbs (_, r) => r
              | MtAppI (t, i) => combine_region (get_region_mt t) (get_region_i i)
              | MtAbsI (_, _, r) => r
              | AppV (_, _, _, r) => r
              | BaseType (_, r) => r
              | UVar (_, r) => r

        fun get_region_t t = 
            case t of
                Mono t => get_region_mt t
              | Uni (_, r) => r

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
                Var (x, _) => get_region_long_id x
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
              | AppConstr ((x, _), _, e) => combine_region (get_region_long_id x) (get_region_e e)
              | Case (_, _, _, r) => r
              | Never (_, r) => r
              | Let (_, _, _, r) => r
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
              | TypeDef ((_, r), t) => combine_region r $ get_region_mt t
              | Open (_, r) => r

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
                  Quan (Forall, bs, Bind ((name, r), p), r_all) =>
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

        exception ModuleUVar

        fun package_long_id m (m', x) =
            (SOME $ default m m', x)
              
        fun package_i m b =
            let
              fun f b =
	          case b of
	              VarI x => VarI $ package_long_id m x
	            | ConstIN n => ConstIN n
	            | ConstIT x => ConstIT x
                    | UnOpI (opr, i, r) => UnOpI (opr, f i, r)
                    | DivI (i1, n2) => DivI (f i1, n2)
                    | ExpI (i1, n2) => ExpI (f i1, n2)
	            | BinOpI (opr, i1, i2) => BinOpI (opr, f i1, f i2)
                    | Ite (i1, i2, i3, r) => Ite (f i1, f i2, f i3, r)
	            | TTI r => TTI r
	            | TrueI r => TrueI r
	            | FalseI r => FalseI r
                    | TimeAbs (name, i, r) => TimeAbs (name, f i, r)
                    | AdmitI r => AdmitI r
                    | UVarI a => raise ModuleUVar
            in
              f b
            end

        fun package_ibind f m bind =
            case bind of
                Bind (name, inner) => Bind (name, f m inner)

        fun package_tbind f m bind =
            case bind of
                Bind (name, inner) => Bind (name, f m inner)

        fun package_p m b =
            let
              fun f m b =
                  case b of
	              True r => True r
	            | False r => False r
                    | Not (p, r) => Not (f m p, r)
	            | BinConn (opr, p1, p2) => BinConn (opr, f m p1, f m p2)
	            | BinPred (opr, d1, d2) => BinPred (opr, package_i m d1, package_i m d2)
                    | Quan (q, bs, bind, r) => Quan (q, bs, package_ibind f m bind, r)
            in
              f m b
            end

        fun package_s m b =
            let
              fun f m b =
	          case b of
	              Basic s => Basic s
	            | Subset (s, bind, r) => Subset (s, package_ibind package_p m bind, r)
                    | UVarS a => raise ModuleUVar
            in
              f m b
            end

        fun package_mt m b =
            let
              fun f m b =
	          case b of
	              Arrow (t1, d, t2) => Arrow (f m t1, package_i m d, f m t2)
                    | Unit r => Unit r
	            | Prod (t1, t2) => Prod (f m t1, f m t2)
	            | UniI (s, bind, r) => UniI (package_s m s, package_ibind f m bind, r)
                    | MtVar x => MtVar $ package_long_id m x
                    | MtApp (t1, t2) => MtApp (f m t1, f m t2)
                    | MtAbs (bind, r) => MtAbs (package_tbind f m bind, r)
                    | MtAppI (t, i) => MtAppI (f m t, package_i m i)
                    | MtAbsI (s, bind, r) => MtAbsI (package_s m s, package_ibind f m bind, r)
	            | AppV (x, ts, is, r) => AppV (package_long_id m x, map (f m) ts, map (package_i m) is, r)
	            | BaseType a => BaseType a
                    | UVar a => raise ModuleUVar
            in
              f m b
            end

        fun package_t m b =
            let
              fun f m b =
	          case b of
	              Mono t => Mono (package_mt m t)
	            | Uni (bind, r) => Uni (package_tbind f m bind, r)
            in
              f m b
            end

        fun package_kind m b =
	    case b of
	        ArrowK (is_datatype, n, sorts) => ArrowK (is_datatype, n, map (package_s m) sorts)

        fun package_c m (family, tnames, core) =
            let
              val family = package_long_id m family
              val (name_sorts, (t, is)) = unfold_binds core
              val t = package_mt m t
              val is = map (package_i m) is
              val name_sorts = map (mapSnd $ package_s m) name_sorts
              val core = fold_binds (name_sorts, (t, is))
            in
              (family, tnames, core)
            end
        
        structure Subst = struct
        open Util
               
        infixr 0 $

        (* generic traversers for both 'shift' and 'forget' *)
                 
        fun on_i_i on_v on_UVarI x n b =
            let
              fun f x n b =
	          case b of
	              VarI (m, (y, r)) => VarI (m, (on_v x n y, r))
	            | ConstIN n => ConstIN n
	            | ConstIT x => ConstIT x
                    | UnOpI (opr, i, r) => UnOpI (opr, f x n i, r)
                    | DivI (i1, n2) => DivI (f x n i1, n2)
                    | ExpI (i1, n2) => ExpI (f x n i1, n2)
	            | BinOpI (opr, i1, i2) => BinOpI (opr, f x n i1, f x n i2)
                    | Ite (i1, i2, i3, r) => Ite (f x n i1, f x n i2, f x n i3, r)
	            | TTI r => TTI r
	            | TrueI r => TrueI r
	            | FalseI r => FalseI r
                    | TimeAbs (name, i, r) => TimeAbs (name, f (x + 1) n i, r)
                    | AdmitI r => AdmitI r
                    | UVarI a => on_UVarI UVarI f x n a
            in
              f x n b
            end

        fun on_i_ibind f x n bind =
            case bind of
                Bind (name, inner) => Bind (name, f (x + 1) n inner)

        fun on_i_tbind f x n bind =
            case bind of
                Bind (name, inner) => Bind (name, f x n inner)

        fun on_i_p on_i_i x n b =
            let
              fun f x n b =
                  case b of
	              True r => True r
	            | False r => False r
                    | Not (p, r) => Not (f x n p, r)
	            | BinConn (opr, p1, p2) => BinConn (opr, f x n p1, f x n p2)
	            | BinPred (opr, d1, d2) => BinPred (opr, on_i_i x n d1, on_i_i x n d2)
                    | Quan (q, bs, bind, r) => Quan (q, bs, on_i_ibind f x n bind, r)
            in
              f x n b
            end

        fun on_i_s on_i_p on_UVarS x n b =
            let
              fun f x n b =
	          case b of
	              Basic s => Basic s
	            | Subset (s, bind, r) => Subset (s, on_i_ibind on_i_p x n bind, r)
                    | UVarS a => on_UVarS UVarS f x n a
            in
              f x n b
            end

        fun on_i_mt on_i_i on_i_s on_i_UVar x n b =
            let
              fun f x n b =
	          case b of
	              Arrow (t1, d, t2) => Arrow (f x n t1, on_i_i x n d, f x n t2)
                    | Unit r => Unit r
	            | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	            | UniI (s, bind, r) => UniI (on_i_s x n s, on_i_ibind f x n bind, r)
                    | MtVar y => MtVar y
                    | MtApp (t1, t2) => MtApp (f x n t1, f x n t2)
                    | MtAbs (bind, r) => MtAbs (on_i_tbind f x n bind, r)
                    | MtAppI (t, i) => MtAppI (f x n t, on_i_i x n i)
                    | MtAbsI (s, bind, r) => MtAbsI (on_i_s x n s, on_i_ibind f x n bind, r)
	            | AppV (y, ts, is, r) => AppV (y, map (f x n) ts, map (on_i_i x n) is, r)
	            | BaseType a => BaseType a
                    | UVar a => on_i_UVar UVar f x n a
            in
              f x n b
            end

        fun on_i_t on_i_mt x n b =
            let
              fun f x n b =
	          case b of
	              Mono t => Mono (on_i_mt x n t)
	            | Uni (bind, r) => Uni (on_i_tbind f x n bind, r)
            in
              f x n b
            end

        fun on_i_kind on_i_s x n b =
	    case b of
	        ArrowK (is_datatype, n, sorts) => ArrowK (is_datatype, n, map (on_i_s x n) sorts)
        
        fun on_t_ibind f x n bind =
            case bind of
                Bind (name, inner) => Bind (name, f x n inner)

        fun on_t_tbind f x n bind =
            case bind of
                Bind (name, inner) => Bind (name, f (x + 1) n inner)

        fun on_t_mt on_v on_t_UVar x n b =
            let
              fun f x n b =
	          case b of
	              Arrow (t1, d, t2) => Arrow (f x n t1, d, f x n t2)
                    | Unit r => Unit r
	            | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	            | UniI (s, bind, r) => UniI (s, on_t_ibind f x n bind, r)
                    | MtVar (m, (y, r)) => MtVar (m, (on_v x n y, r))
                    | MtApp (t1, t2) => MtApp (f x n t1, f x n t2)
                    | MtAbs (bind, r) => MtAbs (on_t_tbind f x n bind, r)
                    | MtAppI (t, i) => MtAppI (f x n t, i)
                    | MtAbsI (s, bind, r) => MtAbsI (s, on_t_ibind f x n bind, r)
	            | AppV ((m, (y, r1)), ts, is, r) => AppV ((m, (on_v x n y, r1)), map (f x n) ts, is, r)
	            | BaseType a => BaseType a
                    | UVar a => on_t_UVar UVar f x n a
            in
              f x n b
            end

        fun on_t_t on_t_mt x n b =
            let
              fun f x n b =
	          case b of
	              Mono t => Mono (on_t_mt x n t)
	            | Uni (bind, r) => Uni (on_t_tbind f x n bind, r)
            in
              f x n b
            end

        fun on_m_long_id on_v x n (m, y) =
            (Option.map (fn (m, r) => (on_v x n m, r)) m, y)
              
        fun on_m_i on_v x n b =
            let
              fun f x n b =
	          case b of
	              VarI y => VarI $ on_m_long_id on_v x n y
	            | ConstIN n => ConstIN n
	            | ConstIT x => ConstIT x
                    | UnOpI (opr, i, r) => UnOpI (opr, f x n i, r)
                    | DivI (i1, n2) => DivI (f x n i1, n2)
                    | ExpI (i1, n2) => ExpI (f x n i1, n2)
	            | BinOpI (opr, i1, i2) => BinOpI (opr, f x n i1, f x n i2)
                    | Ite (i1, i2, i3, r) => Ite (f x n i1, f x n i2, f x n i3, r)
	            | TTI r => TTI r
	            | TrueI r => TrueI r
	            | FalseI r => FalseI r
                    | TimeAbs (name, i, r) => TimeAbs (name, f (x + 1) n i, r)
                    | AdmitI r => AdmitI r
                    | UVarI a => raise ModuleUVar
            in
              f x n b
            end

        fun on_m_ibind f x n bind =
            case bind of
                Bind (name, inner) => Bind (name, f x n inner)

        fun on_m_tbind f x n bind =
            case bind of
                Bind (name, inner) => Bind (name, f x n inner)

        fun on_m_p on_m_i x n b =
            let
              fun f x n b =
                  case b of
	              True r => True r
	            | False r => False r
                    | Not (p, r) => Not (f x n p, r)
	            | BinConn (opr, p1, p2) => BinConn (opr, f x n p1, f x n p2)
	            | BinPred (opr, d1, d2) => BinPred (opr, on_m_i x n d1, on_m_i x n d2)
                    | Quan (q, bs, bind, r) => Quan (q, bs, on_m_ibind f x n bind, r)
            in
              f x n b
            end

        fun on_m_s on_m_p x n b =
            let
              fun f x n b =
	          case b of
	              Basic s => Basic s
	            | Subset (s, bind, r) => Subset (s, on_m_ibind on_m_p x n bind, r)
                    | UVarS a => raise ModuleUVar
            in
              f x n b
            end

        fun on_m_mt on_v on_m_i on_m_s x n b =
            let
              fun f x n b =
	          case b of
	              Arrow (t1, d, t2) => Arrow (f x n t1, on_m_i x n d, f x n t2)
                    | Unit r => Unit r
	            | Prod (t1, t2) => Prod (f x n t1, f x n t2)
	            | UniI (s, bind, r) => UniI (on_m_s x n s, on_m_ibind f x n bind, r)
                    | MtVar y => MtVar $ on_m_long_id on_v x n y
                    | MtApp (t1, t2) => MtApp (f x n t1, f x n t2)
                    | MtAbs (bind, r) => MtAbs (on_m_tbind f x n bind, r)
                    | MtAppI (t, i) => MtAppI (f x n t, on_m_i x n i)
                    | MtAbsI (s, bind, r) => MtAbsI (on_m_s x n s, on_m_ibind f x n bind, r)
	            | AppV (y, ts, is, r) => AppV (on_m_long_id on_v x n y, map (f x n) ts, map (on_m_i x n) is, r)
	            | BaseType a => BaseType a
                    | UVar a => raise ModuleUVar
            in
              f x n b
            end

        fun on_m_t on_m_mt x n b =
            let
              fun f x n b =
	          case b of
	              Mono t => Mono (on_m_mt x n t)
	            | Uni (bind, r) => Uni (on_m_tbind f x n bind, r)
            in
              f x n b
            end

        fun on_m_kind on_m_s x n b =
	    case b of
	        ArrowK (is_datatype, n, sorts) => ArrowK (is_datatype, n, map (on_m_s x n) sorts)
        
        (* shift *)

        fun shiftx_i_i x n b = on_i_i shiftx_v shiftx_i_UVarI x n b
        fun shift_i_i b = shiftx_i_i 0 1 b

        fun shiftx_i_p x n b = on_i_p shiftx_i_i x n b
        fun shift_i_p b = shiftx_i_p 0 1 b

        fun shiftx_i_s x n b = on_i_s shiftx_i_p shiftx_i_UVarS x n b
        fun shift_i_s b = shiftx_i_s 0 1 b

        fun shiftx_i_mt x n b = on_i_mt shiftx_i_i shiftx_i_s (shiftx_i_UVar shiftx_t_mt) x n b
        and shiftx_t_mt x n b = on_t_mt shiftx_v (shiftx_t_UVar shiftx_i_mt) x n b
        fun shift_i_mt b = shiftx_i_mt 0 1 b
        fun shift_t_mt b = shiftx_t_mt 0 1 b

        fun shiftx_i_t x n b = on_i_t shiftx_i_mt x n b
        fun shift_i_t b = shiftx_i_t 0 1 b

        fun shiftx_i_k x n b = on_i_kind shiftx_i_s x n b
        fun shift_i_k b = shiftx_i_k 0 1 b

        fun shiftx_t_t x n b = on_t_t shiftx_t_mt x n b
        fun shift_t_t b = shiftx_t_t 0 1 b

        fun shiftx_m_i x n b = on_m_i shiftx_v x n b
        fun shift_m_i b = shiftx_m_i 0 1 b

        fun shiftx_m_p x n b = on_m_p shiftx_m_i x n b
        fun shift_m_p b = shiftx_m_p 0 1 b

        fun shiftx_m_s x n b = on_m_s shiftx_m_p x n b
        fun shift_m_s b = shiftx_m_s 0 1 b

        fun shiftx_m_mt x n b = on_m_mt shiftx_v shiftx_m_i shiftx_m_s x n b
        fun shift_m_mt b = shiftx_m_mt 0 1 b
                                       
        fun shiftx_m_t x n b = on_m_t shiftx_m_mt x n b
        fun shift_m_t b = shiftx_m_t 0 1 b

        fun shiftx_m_k x n b = on_m_kind shiftx_m_s x n b
        fun shift_m_k b = shiftx_m_k 0 1 b

        (* forget *)

        exception ForgetError of int * string
        (* exception Unimpl *)

        val forget_v = forget_v ForgetError
                                
        fun forget_i_i x n b = on_i_i forget_v (forget_i_UVarI shiftx_i_i ForgetError) x n b
        fun forget_i_p x n b = on_i_p forget_i_i x n b
        fun forget_i_s x n b = on_i_s forget_i_p (forget_i_UVarS shiftx_i_s ForgetError) x n b
        fun forget_i_mt x n b = on_i_mt forget_i_i forget_i_s (forget_i_UVar shiftx_i_mt shiftx_t_mt ForgetError) x n b
        fun forget_t_mt x n b = on_t_mt forget_v (forget_t_UVar shiftx_i_mt shiftx_t_mt ForgetError) x n b
        fun forget_i_t x n b = on_i_t forget_i_mt x n b
        fun forget_t_t x n b = on_t_t forget_t_mt x n b

        fun forget_m_i x n b = on_m_i forget_v x n b
        fun forget_m_p x n b = on_m_p forget_m_i x n b
        fun forget_m_s x n b = on_m_s forget_m_p x n b
        fun forget_m_mt x n b = on_m_mt forget_v forget_m_i forget_m_s x n b
        fun forget_m_t x n b = on_m_t forget_m_mt x n b

        fun try_forget f a =
            SOME (f a) handle ForgetError _ => NONE

        (* ToDo: just a hack now *)
        fun forget_above_i_i x b = forget_i_i x 100000000 b

        (* subst *)

        exception Error of string
                             
        local
          fun f x v b =
	      case b of
	          VarI (m, (y, r)) => substx_v (fn x => VarI (m, (x, r))) x (const v) y
	        | ConstIN n => ConstIN n
	        | ConstIT x => ConstIT x
                | UnOpI (opr, i, r) => UnOpI (opr, f x v i, r)
                | DivI (i1, n2) => DivI (f x v i1, n2)
                | ExpI (i1, n2) => ExpI (f x v i1, n2)
	        | BinOpI (opr, d1, d2) => BinOpI (opr, f x v d1, f x v d2)
                | Ite (i1, i2, i3, r) => Ite (f x v i1, f x v i2, f x v i3, r)
	        | TrueI r => TrueI r
	        | FalseI r => FalseI r
	        | TTI r => TTI r
                | TimeAbs (name, i, r) => TimeAbs (name, f (x + 1) (shiftx_i_i 0 1 v) i, r)
                | AdmitI r => AdmitI r
                | UVarI a => substx_i_UVarI shiftx_i_i UVarI f x v a
        in
        fun substx_i_i x (v : idx) (b : idx) : idx = f x v b
        fun subst_i_i v b = substx_i_i 0 v b
        end

        (* mimic type class *)
        type 'a shiftable = {
          shift_i : int -> 'a -> 'a,
          shift_t : int -> 'a -> 'a
        }

        fun shift_noop n v = v

        val idx_shiftable : idx shiftable = {
          shift_i = shiftx_i_i 0,
          shift_t = shift_noop
        }

        fun substx_i_ibind f x (s : 'a shiftable) v bind =
            case bind of
                Bind (name, inner) => Bind (name, f (x + 1) (#shift_i s 1 v) inner)

        fun substx_t_ibind f x (s : 'a shiftable) v bind =
            case bind of
                Bind (name, inner) => Bind (name, f x (#shift_i s 1 v) inner)

        fun substx_i_tbind f x (s : 'a shiftable) v bind =
            case bind of
                Bind (name, inner) => Bind (name, f x (#shift_t s 1 v) inner)

        fun substx_t_tbind f x (s : 'a shiftable) v bind =
            case bind of
                Bind (name, inner) => Bind (name, f (x + 1) (#shift_t s 1 v) inner)

        local
          fun f x v b =
	      case b of
	          True r => True r
	        | False r => False r
                | Not (p, r) => Not (f x v p, r)
	        | BinConn (opr,p1, p2) => BinConn (opr, f x v p1, f x v p2)
	        | BinPred (opr, d1, d2) => BinPred (opr, substx_i_i x v d1, substx_i_i x v d2)
                | Quan (q, bs, bind, r) => Quan (q, bs, substx_i_ibind f x idx_shiftable v bind, r)
        in
        fun substx_i_p x (v : idx) b = f x v b
        fun subst_i_p (v : idx) (b : prop) : prop = substx_i_p 0 v b
        end

        local
          fun f x v b =
	      case b of
	          Basic s => Basic s
	        | Subset (s, bind, r) => Subset (s, substx_i_ibind substx_i_p x idx_shiftable v bind, r)
                | UVarS a => substx_i_UVarS shiftx_i_s UVarS f x v a
        in
        fun substx_i_s x (v : idx) (b : sort) : sort = f x v b
        fun subst_i_s (v : idx) (b : sort) : sort = substx_i_s 0 v b
        end

        local
          fun f x v b =
	      case b of
	          Arrow (t1, d, t2) => Arrow (f x v t1, substx_i_i x v d, f x v t2)
                | Unit r => Unit r
	        | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	        | UniI (s, bind, r) => UniI (substx_i_s x v s, substx_i_ibind f x idx_shiftable v bind, r)
                | MtVar y => MtVar y
                | MtApp (t1, t2) => MtApp (f x v t1, f x v t2)
                | MtAbs (bind, r) => MtAbs (substx_i_tbind f x idx_shiftable v bind, r)
                | MtAppI (t, i) => MtAppI (f x v t, substx_i_i x v i)
                | MtAbsI (s, bind, r) => MtAbsI (substx_i_s x v s, substx_i_ibind f x idx_shiftable v bind, r)
	        | AppV (y, ts, is, r) => AppV (y, map (f x v) ts, map (substx_i_i x v) is, r)
	        | BaseType a => BaseType a
                | UVar a => substx_i_UVar shiftx_i_mt shiftx_t_mt UVar f x v a
        in
        fun substx_i_mt x (v : idx) (b : mtype) : mtype = f x v b
        fun subst_i_mt (v : idx) (b : mtype) : mtype = substx_i_mt 0 v b
        end

        local
          fun f x v b =
	      case b of
	          Mono t => Mono (substx_i_mt x v t)
	        | Uni (bind, r) => Uni (substx_i_tbind f x idx_shiftable v bind, r)
        in
        fun substx_i_t x (v : idx) (b : ty) : ty = f x v b
        fun subst_i_t (v : idx) (b : ty) : ty = substx_i_t 0 v b
        end

        val mtype_shiftable : mtype shiftable = {
          shift_i = shiftx_i_mt 0,
          shift_t = shiftx_t_mt 0
        }

        local
          fun f x v (b : mtype) : mtype =
	      case b of
	          Arrow (t1, d, t2) => Arrow (f x v t1, d, f x v t2)
                | Unit r => Unit r
	        | Prod (t1, t2) => Prod (f x v t1, f x v t2)
	        | UniI (s, bind, r) => UniI (s, substx_t_ibind f x mtype_shiftable v bind, r)
                | MtVar (m, (y, r)) =>
                  let
                    fun make y =
                        MtVar (m, (y, r))
                  in
                    substx_v make x (const v) y
                  end
                  
                | MtApp (t1, t2) => MtApp (f x v t1, f x v t2)
                | MtAbs (bind, r) => MtAbs (substx_t_tbind f x mtype_shiftable v bind, r)
                | MtAppI (t, i) => MtAppI (f x v t, i)
                | MtAbsI (s, bind, r) => MtAbsI (s, substx_t_ibind f x mtype_shiftable v bind, r)
	        | AppV ((m, (y, r)), ts, is, r2) =>
                  let
                    fun get_v () =
		        if null ts andalso null is then
		          v
		        else
		          raise Error "can't be substituted type for this higher-kind type variable"
                    fun make_AppV y =
                        AppV ((m, (y, r)), map (f x v) ts, is, r2)
                  in
                    substx_v make_AppV x get_v y
                  end
	        | BaseType a => BaseType a
                | UVar a => substx_t_UVar shiftx_i_mt shiftx_t_mt UVar f x v a
        in
        fun substx_t_mt x (v : mtype) (b : mtype) : mtype = f x v b
        fun subst_t_mt (v : mtype) (b : mtype) : mtype = substx_t_mt 0 v b
        fun subst_is_mt is t =
            fst (foldl (fn (i, (t, x)) => (substx_i_mt x (shiftx_i_i 0 x i) t, x - 1)) (t, length is - 1) is)
        fun subst_ts_mt vs b =
            fst (foldl (fn (v, (b, x)) => (substx_t_mt x (shiftx_t_mt 0 x v) b, x - 1)) (b, length vs - 1) vs)
        end

        fun substx_t_t x (v : mtype) (b : ty) : ty =
            case b of
                Mono t => Mono (substx_t_mt x v t)
              | Uni (bind, r) => Uni (substx_t_tbind substx_t_t x mtype_shiftable v bind, r)
        fun subst_t_t v b =
            substx_t_t 0 v b

        fun on_i_ibinds on_anno on_inner x n ibinds =
            case ibinds of
                BindNil inner => 
                BindNil (on_inner x n inner)
              | BindCons (anno, bind) =>
                BindCons (on_anno x n anno, on_i_ibind (on_i_ibinds on_anno on_inner) x n bind)

        fun on_t_ibinds on_anno on_inner x n ibinds =
            case ibinds of
                BindNil inner => 
                BindNil (on_inner x n inner)
              | BindCons (anno, bind) =>
                BindCons (on_anno x n anno, on_t_ibind (on_t_ibinds on_anno on_inner) x n bind)

        fun shiftx_pair (f, g) x n (a, b) = (f x n a, g x n b)
        fun shiftx_list f x n ls = map (f x n) ls

        fun shiftx_i_c x n ((family, tnames, ibinds) : constr) : constr =
            (family,
             tnames, 
             on_i_ibinds shiftx_i_s (shiftx_pair (shiftx_i_mt, shiftx_list shiftx_i_i)) x n ibinds)

        fun shift_i_c b = shiftx_i_c 0 1 b

        fun shiftx_noop x n b = b

        fun shiftx_id x n (y, r) = (shiftx_v x n y, r)
                                      
        fun shiftx_t_c x n (((m, family), tnames, ibinds) : constr) : constr =
            ((m, shiftx_id x n family), 
             tnames, 
             on_t_ibinds shiftx_noop (shiftx_pair (shiftx_t_mt, shiftx_noop)) (x + length tnames) n ibinds)
        fun shift_t_c b = shiftx_t_c 0 1 b

        fun on_m_ibinds on_anno on_inner x n ibinds =
            case ibinds of
                BindNil inner => 
                BindNil (on_inner x n inner)
              | BindCons (anno, bind) =>
                BindCons (on_anno x n anno, on_m_ibind (on_m_ibinds on_anno on_inner) x n bind)

        fun shiftx_m_c x n ((family, tnames, ibinds) : constr) : constr =
            (on_m_long_id shiftx_v x n family,
             tnames, 
             on_m_ibinds shiftx_m_s (shiftx_pair (shiftx_m_mt, shiftx_list shiftx_m_i)) (x + length tnames) n ibinds)
        fun shift_m_c b = shiftx_m_c 0 1 b

        fun on_e_e on_v =
            let
          fun f x n b =
	      case b of
	          Var ((m, (y, r)), b) => Var ((m, (on_v x n y, r)), b)
	        | Abs (pn, e) =>
                  Abs (pn, f (x + (length $ snd $ ptrn_names pn)) n e)
	        | App (e1, e2) => App (f x n e1, f x n e2)
	        | TT r => TT r
	        | Pair (e1, e2) => Pair (f x n e1, f x n e2)
	        | Fst e => Fst (f x n e)
	        | Snd e => Snd (f x n e)
	        | AbsI (s, name, e, r) => AbsI (s, name, f x n e, r)
	        | AppI (e, i) => AppI (f x n e, i)
	        | Let (return, decs, e, r) =>
	          let 
		    val (decs, m) = f_decls x n decs
	          in
		    Let (return, decs, f (x + m) n e, r)
	          end
	        | Ascription (e, t) => Ascription (f x n e, t)
	        | AscriptionTime (e, d) => AscriptionTime (f x n e, d)
	        | ConstInt n => ConstInt n
	        | BinOp (opr, e1, e2) => BinOp (opr, f x n e1, f x n e2)
	        | AppConstr (cx, is, e) => AppConstr (cx, is, f x n e)
	        | Case (e, return, rules, r) => Case (f x n e, return, map (f_rule x n) rules, r)
	        | Never t => Never t

          and f_decls x n decs =
	      let 
                fun g (dec, (acc, m)) =
		    let
		      val (dec, m') = f_dec (x + m) n dec
		    in
		      (dec :: acc, m' + m)
		    end
	        val (decs, m) = foldl g ([], 0) decs
	        val decs = rev decs
	      in
                (decs, m)
              end

          and f_dec x n dec =
	      case dec of
	          Val (tnames, pn, e, r) => 
	          let 
                    val (_, enames) = ptrn_names pn 
	          in
                    (Val (tnames, pn, f x n e, r), length enames)
                  end
                | Rec (tnames, name, (binds, ((t, d), e)), r) => 
                  let
                    fun g (bind, m) =
                        case bind of
                            SortingST _ => m
                          | TypingST pn =>
	                    let 
                              val (_, enames) = ptrn_names pn 
	                    in
                              m + length enames
                            end
                    val m = foldl g 0 binds
                    val e = f (x + 1 + m) n e
                  in
                    (Rec (tnames, name, (binds, ((t, d), e)), r), 1)
                  end
                | Datatype a => (Datatype a, 0)
                | IdxDef a => (IdxDef a, 0)
                | AbsIdx (a, decls, r) => 
                  let
                    val (decls, m) = f_decls x n decls
                  in
                    (AbsIdx (a, decls, r), m)
                  end
                | TypeDef (name, t) => (TypeDef (name, t), 0)
                | Open m => (Open m, 0)

          and f_rule x n (pn, e) =
	      let 
                val (_, enames) = ptrn_names pn 
	      in
	        (pn, f (x + length enames) n e)
	      end
        in
          f
        end

        (* shift_e_e *)
        fun shiftx_e_e x n b = on_e_e shiftx_v x n b
        fun shift_e_e b = shiftx_e_e 0 1 b

        (* forget_e_e *)
        fun forget_e_e x n b = on_e_e forget_v x n b
                                     
        fun hyps2ctx hs = List.mapPartial (fn h => case h of VarH (name, _) => SOME name | _ => NONE) hs

        fun str_hyps_conclu gctx (hyps, p) =
            let 
              fun g (h, (hyps, ctx)) =
                  case h of
                      VarH ((name, _), (bs, _)) => (sprintf "$ : $" [name, str_bs bs] :: hyps, name :: ctx)
                    | PropH p => (str_p gctx ctx p :: hyps, ctx)
              val (hyps, ctx) = foldr g ([], []) hyps
              val hyps = rev hyps
              val p = str_p gctx ctx p
            in
              hyps @
              ["==============="] @
              [p]
            end 

        fun shiftx_hyp x n hyp =
            case hyp of
                VarH _ => hyp
              | PropH p => PropH (shiftx_i_p x n p)
                                 
        fun shiftx_hyps x n hyps =
            case hyps of
                [] => hyps
              | hyp :: hyps =>
                let
                  val d = case hyp of
                              VarH _ => 1
                            | PropH _ => 0
                in
                  shiftx_hyp x n hyp :: shiftx_hyps (x + d) n hyps
                end

        (* find something about [x] in [hyps]. [x] is expressed as being in the innermost of [hyps] (so [x] can see all variables in [hyps]). *)
        fun find_hyp forget shift pred x hyps =
            let
              exception Error
              fun runError m _ =
                  SOME (m ())
                  handle
                  Error => NONE
                  | ForgetError _ => NONE
              fun do_forget hyp x =
                  case hyp of
                      VarH _ => forget x
                    | PropH _ => x
              fun do_shift hyp (p as (y, hyps)) =
                  case hyp of
                      VarH _ => (shift y, shiftx_hyps 0 1 hyps)
                    | PropH _ => p
              fun loop x hyps () =
                  let
                    val (hyp, hyps) = case hyps of hyp :: hyps => (hyp, hyps) | [] => raise Error
                    val x = do_forget hyp x
                  in
                    case pred x hyps hyp of
                        SOME y => do_shift hyp (y, hyps)
                      | NONE => do_shift hyp (loop x hyps ())
                  end
            in
              runError (loop x hyps) ()
            end
              
        end
                            
        structure Simp = struct
        
        local
          open Subst
          val changed = ref false
          fun unset () = changed := false
          fun set () = changed := true
          fun mark a = (set (); a)
          fun passi i =
              let
                (* val () = if !passi_debug then (fn () => println $ str_i [] i) () else () *)
                fun r () = get_region_i i
              in
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
                            mark i1
	                  else if eq_i i1 (T0 dummy) orelse eq_i i1 (ConstIN (0, dummy)) then
                            mark i2
	                  else if eq_i i2 (T0 dummy) orelse eq_i i2 (ConstIN (0, dummy)) then
                            mark i1
	                  else
                            (case (i1, i2) of
                                 (BinOpI (opr, i1, i2), BinOpI (opr', i1', i2')) =>
                                 if opr = opr' then
                                   if opr = AddI orelse opr = MultI then
                                     if eq_i i1 i1' then
                                       mark $ BinOpI (opr, i1, BinOpI (MaxI, i2, i2'))
                                     else if eq_i i2 i2' then
                                       mark $ BinOpI (opr, BinOpI (MaxI, i1, i1'), i2)
                                     else def ()
                                   else if opr = TimeApp then
                                     if eq_i i1 i1' then
                                       mark $ BinOpI (opr, i1, BinOpI (MaxI, i2, i2'))
                                     else def ()
                                   else def ()
                                 else def ()
                               | _ => def ()
                            )
	                | MinI =>
	                  if eq_i i1 i2 then
                            mark i1
	                  else
		            def ()
	                | AddI => 
	                  if eq_i i1 (T0 dummy) orelse eq_i i1 (ConstIN (0, dummy)) then
                            mark i2
	                  else if eq_i i2 (T0 dummy) orelse eq_i i2 (ConstIN (0, dummy)) then
                            mark i1
	                  else
                            let
                              val is = collect_AddI i
                              val (i', is) = case is of
                                                 i :: is => (i, is)
                                               | [] => raise Impossible "passi/AddI"
                              val i' = combine_AddI_nonempty i' is
                            in
		              if eq_i i' i then
                                def ()
                              else
                                mark i'
                            end
	                | MultI => 
	                  if eq_i i1 (T0 dummy) then
                            mark $ T0 $ r ()
	                  else if eq_i i2 (T0 dummy) then
                            mark $ T0 $ r ()
	                  else if eq_i i1 (T1 dummy) then
                            mark i2
	                  else if eq_i i2 (T1 dummy) then
                            mark i1
	                  else
                            (case (i1, i2) of
                                 (ConstIN (n1, _), ConstIN (n2, _)) =>
                                 mark $ ConstIN (n1 * n2, r ())
                               | _ =>
                                 let
                                   val i2s = collect_AddI i2
                                   fun pred i =
                                       case i of
                                           ConstIN _ => SOME i
                                         | UnOpI (B2n, _, _) => SOME i
                                         | _ => NONE
                                 in
                                   case partitionOptionFirst pred i2s of
                                       SOME (i2, rest) =>
                                       let
                                         val ret = i1 %* i2
                                         val ret =
                                             case rest of
                                                 [] => ret
                                               | hd :: rest => ret %+ i1 %* combine_AddI_nonempty hd rest
                                       in
                                         if eq_i ret i then
                                           def ()
                                         else
                                           mark ret
                                       end
                                     | NONE => def ()
                                 end
                            )
                        | TimeApp =>
                          (case i1 of
                               TimeAbs (_, body, _) =>
                               mark $ subst_i_i (passi i2) body
		             | _ => def ()
                          )
                        | EqI =>
                          if eq_i i1 i2 then
                            mark $ TrueI $ r ()
                          else def ()
                        | AndI =>
                          if eq_i i1 (TrueI dummy) then
                            mark i2
                          else if eq_i i2 (TrueI dummy) then
                            mark i1
                          else if eq_i i1 (FalseI dummy) then
                            mark $ FalseI $ r ()
                          else if eq_i i2 (FalseI dummy) then
                            mark $ FalseI $ r ()
                          else
                            def ()
                        | ExpNI =>
                          let
                            val r = r ()
                            fun exp i n =
                                if n > 0 then
                                  exp i (n-1) %* i
                                else
                                  N1 r
                          in
                            case i2 of
                                ConstIN (n, _) => exp i1 n
                              | UnOpI (B2n, i, _) => Ite (i, i1, N1 r, r)
                              | _ =>
                                let
                                  val i2s = collect_AddI i2
                                  fun pred i =
                                      case i of
                                          ConstIN _ => SOME i
                                        | UnOpI (B2n, _, _) => SOME i
                                        | _ => NONE
                                in
                                  case partitionOptionFirst pred i2s of
                                      SOME (i2, rest) => mark $ i1 %^ i2 %* i1 %^ combine_AddI_Nat rest
                                    | NONE => def ()
                                end
                          end
                        | LtI =>
                          def ()
                        | GeI =>
                          def ()
                        | BoundedMinusI =>
                          def ()
                    end
                  | Ite (i, i1, i2, r) =>
                    if eq_i i (TrueI dummy) then
                      mark i1
                    else if eq_i i (FalseI dummy) then
                      mark i2
                    else
                      Ite (passi i, passi i1, passi i2, r)
                  | UnOpI (ToReal, BinOpI (AddI, i1, i2), r) =>
                    mark $ BinOpI (AddI, UnOpI (ToReal, i1, r), UnOpI (ToReal, i2, r))
                  | UnOpI (ToReal, BinOpI (MultI, i1, i2), r) =>
                    mark $ BinOpI (MultI, UnOpI (ToReal, i1, r), UnOpI (ToReal, i2, r))
                  | UnOpI (Neg, TrueI _, r) =>
                    mark $ FalseI r
                  | UnOpI (Neg, FalseI _, r) =>
                    mark $ TrueI r
                  | UnOpI (B2n, TrueI _, r) =>
                    mark $ N1 r
                  | UnOpI (B2n, FalseI _, r) =>
                    mark $ N0 r
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
              end
                
          fun passp p =
              let
                fun r () = get_region_p p
              in
                case p of
	            BinConn (opr, p1, p2) =>
                    let
                      fun def () = BinConn (opr, passp p1, passp p2) 
                    in
                      case opr of
                          And =>
	                  if eq_p p1 (True dummy) then
                            mark p2
	                  else if eq_p p2 (True dummy) then
                            mark p1
	                  else
	                    def ()
                        | Or =>
	                  if eq_p p1 (False dummy) then
                            mark p2
	                  else if eq_p p2 (False dummy) then
                            mark p1
	                  else
	                    def ()
                        | Imply =>
	                  if eq_p p1 (True dummy) then
                            mark p2
                          else if eq_p p2 (True dummy) then
                            mark $ True $ r ()
                          else
                            (case p1 of
                                 BinConn (And, p1a, p1b) =>
                                 mark $ (p1a --> p1b --> p2)
                               | _ => def ()
                            )
                        | _ => def ()
                    end
	          | BinPred (opr, i1, i2) =>
                    let
                      fun def () = BinPred (opr, passi i1, passi i2)
                    in
                      case opr of 
                          EqP => if eq_i i1 i2 then
                                   mark $ True $ r ()
                                 else def ()
                        | LeP => if eq_i i1 i2 orelse eq_i i1 (T0 dummy) then
                                   mark $ True $ r ()
                                 else def ()
                        | _ => def ()
                    end
                  | Not (p, r) => Not (passp p, r)
                  | p_all as Quan (q, bs, Bind (name, p), r_all) =>
                    let
                      fun def () = Quan (q, bs, Bind (name, passp p), r_all)
                    in
                      case q of
                          Forall =>
                          (case try_forget (forget_i_p 0 1) p of
                               SOME p => (set (); p)
                             | _ =>
                               (* try subst if there is a equality premise *)
                               (*
if false then
                     let
                       (* val () = println $ "Try subst eq premise" *)
                       fun collect_Imply p =
                           case p of
                               BinConn (Imply, p1, p2) =>
                               let
                                 val (hyps, conclu) = collect_Imply p2
                               in
                                 (collect_And p1 @ hyps, conclu)
                               end
                             | _ => ([], p)
                       fun combine_Imply hyps conclu =
                           case hyps of
                               h :: hyps => h --> combine_Imply hyps conclu
                             | [] => conclu
                       fun collect_Forall p =
                           case p of
                               Quan (Forall, bs, name, p, r) =>
                               let
                                 val (binds, p) = collect_Forall p
                               in
                                 ((name, bs, r) :: binds, p)
                               end
                             | _ => ([], p)
                       fun combine_Forall binds p =
                           case binds of
                               [] => p
                             | (name, bs, r) :: binds =>
                               Quan (Forall, bs, name, combine_Forall binds p, r)
                       val (binds, p) = collect_Forall p_all
                       val (hyps, conclu) = collect_Imply p
                       val binds_len = length binds
                       (* test whether [p] is [VarI x = _] or [_ = VarI x] *)
                       fun is_var_equals p =
                           let
                             fun find_var (i1, i2) =
                                 case i1 of
                                     VarI (x, _) =>
                                     (if 0 <= x andalso x < binds_len then
                                        SOME (x, forget_i_i x 1 i2) handle ForgetError _ => NONE
                                      else NONE
                                     )
                                   | _ => NONE
                           in
                             case p of
                                 BinPred (EqP, i1, i2) => firstSuccess find_var [(i1, i2), (i2, i1)]
                               | _ => NONE
                           end
                     in
                       case partitionOptionFirst is_var_equals hyps of
                           SOME ((x, i), rest) =>
                           let
                             (* val () = println $ "Substing " ^ str_v (rev $ map (fst o fst) binds) x *)
                             val () = set ()
                             val ret = combine_Forall (remove (binds_len - 1 - x) binds) $ substx_i_p x i $ combine_Imply rest conclu
                           in
                             ret
                           end
                         | NONE => def ()
                     end
else
                               *)
                               let
                                 (* val () = println $ "Try subst eq premise" *)
                                 (* fun collect_Imply_Forall p = *)
                                 (*     case p of *)
                                 (*         BinConn (Imply, p1, p2) => *)
                                 (*         let *)
                                 (*           val (hyps, conclu) = collect_Imply_Forall p2 *)
                                 (*         in *)
                                 (*           (map PropH (collect_And p1)(* [PropH p1] *) @ hyps, conclu) *)
                                 (*         end *)
                                 (*       | Quan (Forall, bs, name, p, r) => *)
                                 (*         let *)
                                 (*           val (hyps, p) = collect_Imply_Forall p *)
                                 (*         in *)
                                 (*           (VarH (name, (bs, r)) :: hyps, p) *)
                                 (*         end *)
                                 (*       | _ => ([], p) *)
                                 (* a faster version *)
                                 fun collect_Imply_Forall p =
                                     let
                                       fun loop (acc, p) =
                                           case p of
                                               BinConn (Imply, p1, p2) =>
                                               loop (map PropH (rev $ collect_And p1) @ acc, p2)
                                             | Quan (Forall, bs, Bind (name, p), r) =>
                                               loop (VarH (name, (bs, r)) :: acc, p)
                                             | _ => (acc, p)
                                       val (hyps, conclu) = loop ([], p)
                                       val hyps = rev hyps
                                     in
                                       (hyps, conclu)
                                     end
                                 fun combine_Imply_Forall hyps conclu =
                                     let
                                       fun iter (h, conclu) =
                                           case h of
                                               PropH p =>
                                               p --> conclu
                                             | VarH (name, (bs, r))  =>
                                               Quan (Forall, bs, Bind (name, conclu), r)
                                     in
                                       foldr iter conclu hyps
                                     end
                                 val (hyps, conclu) = collect_Imply_Forall p
                                 val hyps = rev hyps
                                 val binds_len = length $ hyps2ctx hyps
                                 (* test whether [p] is [VarI x = _] or [_ = VarI x] *)
                                 fun is_var_equals x p =
                                     let
                                       fun find_var (i1, i2) =
                                           if eq_i i1 (VarI (NONE, (int2var x, dummy))) then
                                             SOME (forget_i_i x 1 i2) handle ForgetError _ => NONE
                                           else NONE
                                     in
                                       case p of
                                           BinPred (EqP, i1, i2) => firstSuccess find_var [(i1, i2), (i2, i1)]
                                         | _ => NONE
                                     end
                                 fun foldr_hyps shift1 shift2 f init hyps =
                                     let
                                       fun iter (h, (x, acc)) =
                                           case h of
                                               VarH _ => (shift1 x, Option.map shift2 acc)
                                             | PropH p =>
                                               case acc of
                                                   SOME _ => (x, acc)
                                                 | NONE => (x, f x p)
                                     in
                                       snd $ foldr iter (init, NONE) hyps
                                     end
                               in
                                 case foldr_hyps (fn x => var2int (shiftx_v 0 1 (int2var x))) shift_i_i is_var_equals 0 hyps of
                                     SOME i =>
                                     (let
                                       val x = binds_len
                                       val ctxn = map fst $ hyps2ctx hyps
                                       (* val () = println $ sprintf "Substing for $ with $" [str_v (ctxn @ [fst name]) x, str_i ctxn i] *)
                                       (* val () = app println $ str_hyps_conclu (hyps @ [VarH (name, (bs, r_all))], conclu) @ [""]  *)
                                       val conclu = substx_i_p x i conclu
                                       fun subst_hyp n p =
                                           let
                                             val x = var2int $ forget_v 0 n (int2var x)
                                             val p =
                                                 case try_forget (forget_i_p x 1) p of
                                                     NONE =>
                                                     let
                                                       val i = forget_i_i 0 n i
                                                     in
                                                       substx_i_p x i p
                                                     end
                                                   | SOME p => p
                                           in
                                             p
                                           end
                                       fun foldl_hyps f hyps =
                                           let
                                             fun iter (h, (n, acc)) =
                                                 case h of
                                                     VarH _ => (n + 1, h :: acc)
                                                   | PropH p => (n, PropH (f n p) :: acc)
                                           in
                                             rev $ snd $ foldl iter (0, []) hyps
                                           end
                                       val hyps = foldl_hyps subst_hyp hyps
                                       (* val () = app println $ str_hyps_conclu (hyps, conclu) @ [""]  *)
                                       val ret = combine_Imply_Forall (rev hyps) conclu
                                     in
                                       mark ret
                                     end
                                      handle ForgetError _ => def ()
                                     )
                                   | NONE => def ()
                               end

                                 
                          (*
                      (case p of
                           BinConn (Imply, p1, p2) =>
                           let
                               fun forget i = try_forget (forget_i_i 0 1) i
                               fun f i1 i2 =
                                   if eq_i i1 (VarI (0, dummy)) then forget i2
                                   else if eq_i i2 (VarI (0, dummy)) then forget i1
                                   else NONE
                               val i = case p1 of
                                           BinPred (EqP, i1, i2) => f i1 i2
                                         | _ => NONE
                           in
                               case i of
                                   SOME i => (set (); subst_i_p i p2)
                                 | _ => Quan (q, bs, name, passp p)
                           end
                         | _ =>
                           Quan (q, bs, name, passp p)
                      )
                          *)
                          )
                        | Exists ins =>
                          (* for unconstrained Time evar, infer it to be 0 *)
                          let
                            val p = passp p
                          in
                            case (eq_bs bs (Base Time), try_forget (forget_i_p 0 1) p) of
                                (true, SOME p) =>
                                (set ();
                                 (case ins of SOME f => f (T0 dummy) | NONE => ());
                                 p)
                              | _ =>
                                let
                                  val ps = collect_And p
                                  val (irrelevant, relevant) = partitionOption (try_forget (forget_i_p 0 1)) ps
                                in
                                  case relevant of
                                      [] => def ()
                                    | _ => combine_And $ Quan (q, bs, Bind (name, combine_And relevant), r_all) :: irrelevant
                                end
                          end
                    end
	          | True _ => p
	          | False _ => p
              end
                
          fun until_unchanged f a = 
              let fun loop a =
	              let
                        val _ = unset ()
                        (* val () = println "before f()" *)
                        val a = f a
                                  (* val () = println "after f()" *)
                      in
		        if !changed then loop a
		        else a
	              end
              in
	        loop a
              end
        in
        val simp_i = until_unchanged passi
        fun simp_p p =
            let
              (* val () = println $ "Before simp_p: " ^ str_p [] p *)
              val p = until_unchanged passp p
                                      (* val () = println $ "After simp_p:  " ^ str_p [] p *)
                                      (* val () = println "" *)
            in
              p      
            end
        fun simp_p_with_plugin plugin p =
            let
              fun iter p =
                  let
                    val p = plugin set p
                    val p = passp p
                  in
                    p
                  end
              val p = until_unchanged iter p
            in
              p      
            end
              
        end

        fun simp_vc (ctx, ps, p, r) = (ctx, map simp_p ps, simp_p p, r)

        fun simp_ibind f (Bind (name, inner)) = Bind (name, f inner)
        fun simp_tbind f (Bind (name, inner)) = Bind (name, f inner)

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
              | MtVar x => MtVar x
              | MtApp (t1, t2) => MtApp (simp_mt t1, simp_mt t2)
              | MtAbs (bind, r) => MtAbs (simp_tbind simp_mt bind, r)
              | MtAppI (t, i) => MtAppI (simp_mt t, simp_i i)
              | MtAbsI (s, bind, r) => MtAbsI (simp_s s, simp_ibind simp_mt bind, r)
	      | UniI (s, bind, r) => UniI (simp_s s, simp_ibind simp_mt bind, r)
	      | BaseType a => BaseType a
              | UVar u => UVar u

        fun simp_t t =
	    case t of
	        Mono t => Mono (simp_mt t)
	      | Uni (Bind (name, t), r) => Uni (Bind (name, simp_t t), r)

        end

        end
                                                                
structure StringVar = struct
open Util
type var = string
fun str_v ctx x : string = x
fun eq_v (x : var, y) = x = y
                              
fun shiftx_v x n y = y
fun forget_v ForgetError x n y =  y
fun substx_v Var x v y = raise Impossible "Can't do StringVar.substx_v()"

fun int2var x = raise Impossible "StringVar.int2var()"
fun var2int x = raise Impossible "StringVar.var2int()"
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

fun shiftx_v x n y = 
    if y >= x then
      y + n
    else
      y

fun forget_v ForgetError x n y = 
    if y >= x + n then
      y - n
    else if y < x then
      y
    else
      raise ForgetError (y, "")

fun substx_v Var x v y =
    if y = x then
      v ()
    else if y > x then
      Var (y - 1)
    else
      Var y

fun int2var x = x
fun var2int x = x
                  
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

fun shiftx_i_UVarI UVarI _ _ _ a = UVarI a
fun shiftx_i_UVarS UVarS _ _ _ a = UVarS a 
fun shiftx_i_UVar _ UVar _ _ _ a = UVar a
fun shiftx_t_UVar _ UVar _ _ _ a = UVar a
                                        
fun forget_i_UVarI _ _ UVarI _ _ _ a = UVarI a
fun forget_i_UVarS _ _ UVarS _ _ _ a = UVarS a 
fun forget_i_UVar _ _ _ UVar _ _ _ a = UVar a
fun forget_t_UVar _ _ _ UVar _ _ _ a = UVar a
                                            
fun substx_i_UVarI _ UVarI _ _ _ a = UVarI a
fun substx_i_UVarS _ UVarS _ _ _ a = UVarS a 
fun substx_i_UVar _ _ UVar _ _ _ a = UVar a
fun substx_t_UVar _ _ UVar _ _ _ a = UVar a
                                          
end

structure NamefulExpr = ExprFun (structure Var = StringVar structure UVar = Underscore)
structure UnderscoredExpr = ExprFun (structure Var = IntVar structure UVar = Underscore)
