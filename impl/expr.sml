structure BasicSorts = struct
(* basic index sort *)
datatype base_sort =
	 Time
         | Nat
	 | Bool
	 | BSUnit

fun str_b (s : base_sort) : string = 
    case s of
        Time => "Time"
      | Nat => "Nat"
      | Bool => "Bool"
      | BSUnit => "Unit"
end

structure ExprUtil = struct

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

end

signature VAR = sig
    type var
    val str_v : string list -> var -> string
end

signature UVAR = sig
    type 't uvar_i
    type 't uvar_bs
    type 't uvar_s
    type 't uvar_mt
end

functor ExprFun (structure Var : VAR structure UVar : UVAR) = struct
        open Var
        open BasicSorts
        open Util
        open Operators
        open UVar
        open Region

        type id = var * region
        type name = string * region

        datatype idx =
	         VarI of var * region
	         | ConstIT of string * region
	         | ConstIN of int * region
                 | UnOpI of idx_un_op * idx * region
                 | BinOpI of idx_bin_op * idx * idx
	         | TrueI of region
	         | FalseI of region
	         | TTI of region
                 | UVarI of idx uvar_i * region

        fun T0 r = ConstIT ("0.0", r)
        fun T1 r = ConstIT ("1.0", r)

        datatype prop =
	         True of region
	         | False of region
                 | BinConn of bin_conn * prop * prop
                 | Not of prop * region
	         | BinPred of bin_pred * idx * idx

        datatype bsort = 
                 Base of base_sort
                 | UVarBS of bsort uvar_bs

        (* index sort *)
        datatype sort =
	         Basic of bsort * region
	         | Subset of (bsort * region) * (name * prop) ibind
                 | UVarS of sort uvar_s * region
					 
        val STime = Basic (Time, dummy)
        val SBool = Basic (Bool, dummy)
        val SUnit = Basic (BSUnit, dummy)

        (* monotypes *)
        datatype mtype = 
	         Arrow of mtype * idx * mtype
	         | Prod of mtype * mtype
	         | Unit of region
	         | UniI of sort * (name * mtype) ibind
	         | ExI of sort * (name * mtype) ibind
	         (* the first operant of App can only be a type variable. The degenerated case of no-arguments is also included *)
	         | AppV of id * mtype list * idx list * region
	         | Int of region
                 | UVar of mtype uvar_mt * region

        datatype ty = 
	         Mono of mtype
	         | Uni of name * ty

        fun VarT x = AppV (x, [], [], dummy)
        fun AppVar (x, is) = AppV (x, [], is, dummy)

        datatype kind = 
	         ArrowK of bool (* is datatype *) * int * sort list

        val Type = ArrowK (false, 0, [])

        type constr_core = (sort, string, mtype * idx list) ibinds
        type constr_decl = string * constr_core * region
        type constr = var * string list * constr_core

        fun constr_type shiftx_v ((family, tnames, ibinds) : constr) = 
            let 
                val (ns, (t, is)) = unfold_ibinds ibinds
                val ts = (map (fn x => VarT (x, dummy)) o rev o range o length) tnames
	        val t2 = AppV ((shiftx_v 0 (length tnames) family, dummy), ts, is, dummy)
	        val t = Arrow (t, T0 dummy, t2)
	        val t = foldr (fn ((name, s), t) => UniI (s, BindI ((name, dummy), t))) t ns
                val t = Mono t
	        val t = foldr (fn (name, t) => Uni ((name, dummy), t)) t tnames
            in
	        t
            end

        fun constr_from_type t =
            let
                val (tnames, t) = peel_Uni t
                val tnames = map fst tnames
                val (ns, t) = peel_UniI t
                val (t = case t of
                            Arrow (t, _, t2) => t
                          | _ => raise Impossible "constr_from_type (): not Arrow"
            in
                (tnames, fold_ibinds (ns, (t, is)))
            end

        type return = mtype option * idx option
                                       
        datatype ptrn =
	         ConstrP of id * string list * ptrn option * region
                 | VarP of name
                 | PairP of ptrn * ptrn
                 | TTP of region
                 | AliasP of name * ptrn * region
                 | AnnoP of ptrn * ty

        datatype expr =
	         Var of var * region
	         | App of expr * expr
	         | Abs of mtype * ptrn * expr 
	         (* unit type *)
	         | TT of region
	         (* product type *)
	         | Pair of expr * expr
	         | Fst of expr
	         | Snd of expr
	         (* universal *)
	         | AbsT of name * expr
	         | AppT of expr * mtype
	         (* universal index *)
	         | AbsI of sort * name * expr
	         | AppI of expr * idx
	         (* existential index *)
	         | Pack of mtype * idx * expr
	         | Unpack of expr * return * string * string * expr
                 (* region *)
	         | BinOp of bin_op * expr * expr
	         | Const of int * region
	         | AppConstr of id * mtype list * idx list * expr
	         | Case of expr * return * (ptrn * expr) list * region
	         | Never of mty
	         | Let of decl list * expr * region
	         | Fix of mtype * name * expr
	         | Ascription of expr * mtype
	         | AscriptionTime of expr * idx

             and decl =
                 Val of ptrn * expr
	         | Datatype of string * string list * sort list * constr_decl list * region

        infix 6 %+ 
        fun a %+ b = BinOpI (AddI, a, b)
        infix 6 %*
        fun a %* b = BinOpI (MultI, a, b)
        infix 4 %<=
        fun a %<= b = BinPred (LeP, a, b)
        infix 3 /\
        fun a /\ b = BinConn (And, a, b)
        infix 1 -->
        fun a --> b = BinConn (Imply, a, b)
        infix 1 <->
        fun a <-> b = BinConn (Iff, a, b)

        (* pretty-printers *)

        fun str_i ctx (i : idx) : string = 
            case i of
                VarI (x, _) => str_v ctx x
              | ConstIN (n, _) => str_int n
              | ConstIT (x, _) => x
              | UnOpI (opr, i, _) => sprintf "($ $)" [str_idx_un_op opr, str_i ctx i]
              | BinOpI (opr, i1, i2) => sprintf "($ $ $)" [str_i ctx i1, str_idx_bin_op opr, str_i ctx i2]
              | TTI _ => "()"
              | TrueI _ => "true"
              | FalseI _ => "false"

        fun str_p ctx p = 
            case p of
                True _ => "True"
              | False _ => "False"
              | Not (p, _) => sprintf "(~ $)" [str_p ctx p]
              | BinConn (opr, p1, p2) => sprintf "($ $ $)" [str_p ctx p1, str_bin_conn opr, str_p ctx p2]
              | BinPred (opr, i1, i2) => sprintf "($ $ $)" [str_i ctx i1, str_bin_pred opr, str_i ctx i2]

        fun str_s ctx (s : sort) : string = 
            case s of
                Basic (s, _) => str_b s
              | Subset ((s, _), (BindI ((name, _), p))) => sprintf "{ $ :: $ | $ }" [name, str_b s, str_p (name :: ctx) p]

        datatype 'a bind = 
                 KindingT of string
                 | SortingT of string * 'a

        fun collect_UniI t =
            case t of
                UniI (s, BindI ((name, _), t)) =>
                let val (binds, t) = collect_UniI t
                in
                    ((name, s) :: binds, t)
                end
              | _ => ([], t)

        fun collect_Uni t =
            case t of
                Uni ((name, _), t) =>
                let val (names, t) = collect_Uni t
                in
                    (name :: names, t)
                end
              | Mono t => ([], t)

        fun collect_Uni_UniI t =
            let
                val (tnames, t) = collect_Uni t
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

        fun str_mt (ctx as (sctx, kctx)) (t : mtype) : string =
            case t of
                Arrow (t1, d, t2) => sprintf "($ -- $ -> $)" [str_mt ctx t1, str_i sctx d, str_mt ctx t2]
              | Unit _ => "unit"
              | Prod (t1, t2) => sprintf "($ * $)" [str_mt ctx t1, str_mt ctx t2]
              | Sum (t1, t2) => sprintf "($ + $)" [str_mt ctx t1, str_mt ctx t2]
              | UniI _ =>
                let
                    val (binds, t) = collect_UniI t
                in
                    str_uni ctx (map SortingT binds, t)
                end
              | ExI (s, BindI ((name, _), t)) => sprintf "(exists {$ : $}, $)" [name, str_s sctx s, str_mt (name :: sctx, kctx) t]
              | AppRecur (name, ns, t, i, _) => 
                sprintf "((rec $ $, $) $)" 
	                [name, 
	                 join " " (map (fn (name, s) => sprintf "($ :: $)" [name, str_s sctx s]) ns),
	                 str_mt (rev (map #1 ns) @ sctx, name :: kctx) t,
	                 join " " (map (str_i sctx) i)]
              | AppV ((x, _), ts, is, _) => 
                if null ts andalso null is then
	            str_v kctx x

                else
	            sprintf "($$$)" [(join "" o map (suffix " ") o map (surround "{" "}") o map (str_i sctx) o rev) is, (join "" o map (suffix " ") o map (str_mt ctx) o rev) ts, str_v kctx x]
              | Int _ => "int"

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
                let val (inames', enames) = ptrn_names (default (TTP dummy) pn)
                in
                    (inames' @ rev inames, enames)
                end
              | VarP (name, _) =>
                ([], [name])
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

        fun str_pn cctx pn = 
            case pn of
                ConstrP ((x, _), inames, pn, _) => sprintf "$ $$" [str_v cctx x, join " " inames, str_opt (str_pn cctx) pn]
              | VarP (name, _) => name
              | PairP (pn1, pn2) => sprintf "($, $)" [str_pn cctx pn1, str_pn cctx pn2]
              | TTP _ => "()"
              | AliasP ((name, _), pn, _) => sprintf "$ as $" [name, str_pn cctx pn]

        fun str_return (skctx as (sctx, _)) return =
            case return of
                (NONE, NONE) => ""
              | (SOME t, NONE) => sprintf "return $ " [str_mt skctx t]
              | (NONE, SOME d) => sprintf "return |> $ " [str_i sctx d]
              | (SOME t, SOME d) => sprintf "return $ |> $ " [str_mt skctx t, str_i sctx d]
                                            
        fun str_e (ctx as (sctx, kctx, cctx, tctx)) (e : expr) : string =
            let fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx) 
                val skctx = (sctx, kctx) 
            in
                case e of
	            Var (x, _) => str_v tctx x
	          | Abs (t, pn, e) => 
                    let val t = str_mt skctx t
                        val (inames, enames) = ptrn_names pn
                        val pn = str_pn cctx pn
                        val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
	                val e = str_e ctx e
                    in
                        sprintf "(fn ($ : $) => $)" [pn, t, e]
                    end
	          | App (e1, e2) => sprintf "($ $)" [str_e ctx e1, str_e ctx e2]
	          | TT _ => "()"
	          | Pair (e1, e2) => sprintf "($, $)" [str_e ctx e1, str_e ctx e2]
	          | Fst e => sprintf "(fst $)" [str_e ctx e]
	          | Snd e => sprintf "(snd $)" [str_e ctx e]
	          | Inl (t, e) => sprintf "(inl [$] $)" [str_mt skctx t, str_e ctx e]
	          | Inr (t, e) => sprintf "(inr [$] $)" [str_mt skctx t, str_e ctx e]
	          | SumCase (e, name1, e1, name2, e2) => sprintf "(sumcase $ of inl $ => $ | inr $  => $)" [str_e ctx e, name1, str_e (add_t name1 ctx) e1, name2, str_e (add_t name2 ctx) e2]
	          | Fold (t, e) => sprintf "(fold [$] $)" [str_mt skctx t, str_e ctx e]
	          | Unfold e => sprintf "(unfold $)" [str_e ctx e]
	          | AbsT ((name, _), e) => sprintf "(fn $ => $)" [name, str_e (sctx, name :: kctx, cctx, tctx) e]
	          | AppT (e, t) => sprintf "($ [$])" [str_e ctx e, str_mt skctx t]
	          | AbsI (s, (name, _), e) => sprintf "(fn $ :: $ => $)" [name, str_s sctx s, str_e (name :: sctx, kctx, cctx, tctx) e]
	          | AppI (e, i) => sprintf "($ [$])" [str_e ctx e, str_i sctx i]
	          | Pack (t, i, e) => sprintf "(pack $ ($, $))" [str_mt skctx t, str_i sctx i, str_e ctx e]
	          | Unpack (e1, return, iname, ename, e2) => sprintf "unpack $ $as ($, $) in $ end" [str_e ctx e1, str_return skctx return, iname, ename, str_e (iname :: sctx, kctx, cctx, ename :: tctx) e2]
	          | Fix (t, (name, _), e) => sprintf "(fix ($ : $) => $)" [name, str_mt skctx t, str_e (add_t name ctx) e]
	          | Let (decls, e, _) => 
                    let val (decls, ctx) = str_decls ctx decls
                    in
                        sprintf "let$ in $ end" [join_prefix " " decls, str_e ctx e]
                    end
	          | Ascription (e, t) => sprintf "($ : $)" [str_e ctx e, str_t skctx t]
	          | AscriptionTime (e, d) => sprintf "($ |> $)" [str_e ctx e, str_i sctx d]
	          | BinOp (opr, e1, e2) => sprintf "($ $ $)" [str_e ctx e1, str_bin_op opr, str_e ctx e2]
	          | Const (n, _) => str_int n
	          | AppConstr ((x, _), ts, is, e) => sprintf "($$$ $)" [str_v cctx x, (join "" o map (prefix " ") o map (fn t => sprintf "[$]" [str_mt skctx t])) ts, (join "" o map (prefix " ") o map (fn i => sprintf "[$]" [str_i sctx i])) is, str_e ctx e]
	          | Case (e, return, rules, _) => sprintf "(case $ $of $)" [str_e ctx e, str_return skctx return, join " | " (map (str_rule ctx) rules)]
	          | Never t => sprintf "(never [$])" [str_t skctx t]
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
                Val (pn, e) =>
                let val e = str_e ctx e
                    val (inames, enames) = ptrn_names pn
                    val pn = str_pn cctx pn
	            val ctx = (inames @ sctx, kctx, cctx, enames @ tctx)
                in
                    (sprintf "val $ = $" [pn, e], ctx)
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

        and str_rule (ctx as (sctx, kctx, cctx, tctx)) (pn, e) =
            let val (inames, enames) = ptrn_names pn
	        val ctx' = (inames @ sctx, kctx, cctx, enames @ tctx)
            in
	        sprintf "$ => $" [str_pn cctx pn, str_e ctx' e]
            end

        (* region calculations *)

        fun get_region_i i =
            case i of
                VarI (_, r) => r
              | ConstIN (_, r) => r
              | ConstIT (_, r) => r
              | UnOpI (_, _, r) => r
              | BinOpI (_, i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
              | TrueI r => r
              | FalseI r => r
              | TTI r => r

        fun get_region_p p = 
            case p of
                True r => r
              | False r => r
              | Not (_, r) => r
              | BinConn (_, p1, p2) => combine_region (get_region_p p1) (get_region_p p2)
              | BinPred (_, i1, i2) => combine_region (get_region_i i1) (get_region_i i2)

        fun get_region_ibind f (BindI ((_, r), inner)) = combine_region r (f inner)

        fun get_region_s s = 
            case s of
                Basic (_, r) => r
              | Subset (_, bind) => get_region_ibind get_region_p bind

        fun get_region_mt t = 
            case t of
                Arrow (t1, d, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
              | Prod (t1, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
              | Sum (t1, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
              | Unit r => r
              | UniI (_, bind) => get_region_ibind get_region_mt bind
              | ExI (_, bind) => get_region_ibind get_region_mt bind
              | AppRecur (_, _, t, _, r) => r
              | AppV (_, _, _, r) => r
              | Int r => r

        fun get_region_t t = 
            case t of
                Mono t => get_region_mt t
              | Uni ((_, r), t) => combine_region r (get_region_t t)

        fun get_region_pn pn = 
            case pn of
                ConstrP (_, _, _, r) => r
              | VarP (_, r) => r
              | PairP (pn1, pn2) => combine_region (get_region_pn pn1) (get_region_pn pn2)
              | TTP r => r
              | AliasP (_, _, r) => r

        fun get_region_e e = 
            case e of
                Var (_, r) => r
              | Abs (_, pn, e) => combine_region (get_region_pn pn) (get_region_e e)
              | App (e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
              | TT r => r
              | Pair (e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
              | Fst e => get_region_e e
              | Snd e => get_region_e e
              | Inl (t, e) => combine_region (get_region_mt t) (get_region_e e)
              | Inr (t, e) => combine_region (get_region_mt t) (get_region_e e)
              | SumCase (e, _, _, _, e2) => combine_region (get_region_e e) (get_region_e e2)
              | AbsT ((_, r), e) => combine_region r (get_region_e e)
              | AppT (e, t) => combine_region (get_region_e e) (get_region_mt t)
              | AbsI (_, (_, r), e) => combine_region r (get_region_e e)
              | AppI (e, i) => combine_region (get_region_e e) (get_region_i i)
              | Pack (t, _, e) => combine_region (get_region_mt t) (get_region_e e)
              | Unpack (e1, _, _, _, e2) => combine_region (get_region_e e1) (get_region_e e2)
              | Fold (t, e) => combine_region (get_region_mt t) (get_region_e e)
              | Unfold e => get_region_e e
              | BinOp (_, e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
              | Const (_, r) => r
              | AppConstr ((_, r), _, _, e) => combine_region r (get_region_e e)
              | Case (_, _, _, r) => r
              | Never t => get_region_t t
              | Let (_, _, r) => r
              | Fix (_, (_, r), e) => combine_region r (get_region_e e)
              | Ascription (e, t) => combine_region (get_region_e e) (get_region_t t)
              | AscriptionTime (e, i) => combine_region (get_region_e e) (get_region_i i)
                                                        
        fun get_region_rule (pn, e) = combine_region (get_region_pn pn) (get_region_e e)

        fun get_region_dec dec =
            case dec of
                Val (pn, e) => combine_region (get_region_pn pn) (get_region_e e)
              | Datatype (_, _, _, _, r) => r

        end
                                                                    
structure StringVar = struct
type var = string
fun str_v ctx x : string = x
end

structure IntVar = struct
open Util
type var = int
fun str_v ctx x : string =
    (* sprintf "%$" [str_int x] *)
    case nth_error ctx x of
        SOME name => name
      | NONE => "unbound_" ^ str_int x
end

structure Underscore = struct
type 't uvar_i = unit
type 't uvar_bs = unit
type 't uvar_s = unit
type 't uvar_mt = unit
end

structure NamefulExpr = ExprFun (structure Var = StringVar structure UVar = Underscore)
structure UnderscoredExpr = ExprFun (structure Var = IntVar structure UVar = Underscore)
