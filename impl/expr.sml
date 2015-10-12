structure BasicSorts = struct
(* basic index sort *)
datatype bsort =
	 Time
         | Nat
	 | Bool
	 | BSUnit

fun str_b (s : bsort) : string = 
  case s of
      Time => "Time"
    | Nat => "Nat"
    | Bool => "Bool"
    | BSUnit => "Unit"
end

signature VAR = sig
    type var
    val str_v : string list -> var -> string
end

signature DEBUG = sig
    type t
    val dummy : t
end

(* types *)
functor TypeFun (structure Var : VAR structure Other : DEBUG) = struct
open Var
open BasicSorts
open Util
open Operators
         
type other = Other.t
val dummy = Other.dummy
type id = var * other
type name = string * other

datatype idx =
	 VarI of var * other
	 | ConstIT of string * other
	 | ConstIN of int * other
         | UnOpI of idx_un_op * idx * other
         | BinOpI of idx_bin_op * idx * idx
	 | TrueI of other
	 | FalseI of other
	 | TTI of other

fun T0 r = ConstIT ("0.0", r)
fun T1 r = ConstIT ("1.0", r)

datatype prop =
	 True of other
	 | False of other
         | BinConn of bin_conn * prop * prop
         | Not of prop * other
	 | BinPred of bin_pred * idx * idx

(* index sort *)
datatype sort =
	 Basic of bsort * other
	 | Subset of (bsort * other) * name * prop
						  
val STime = Basic (Time, dummy)
val SBool = Basic (Bool, dummy)
val SUnit = Basic (BSUnit, dummy)

datatype ty = 
	 Arrow of ty * idx * ty
	 | Prod of ty * ty
	 | Sum of ty * ty
	 | Unit of other
	 | Uni of name * ty
	 | UniI of sort * name * ty
	 | ExI of sort * name * ty
	 (* the kind of Recur is sort => Type, to allow for change of index *)
	 | AppRecur of string * (string * sort) list * ty * idx list * other
	 (* the first operant of App can only be a type variable. The degenerated case of no-arguments is also included *)
	 | AppV of id * ty list * idx list * other
	 | Int of other

fun VarT x = AppV (x, [], [], dummy)
fun AppVar (x, is) = AppV (x, [], is, dummy)

datatype kind = 
	 ArrowK of bool (* is datatype *) * int * sort list

val Type = ArrowK (false, 0, [])

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
    | Subset ((s, _), (name, _), p) => sprintf "{ $ :: $ | $ }" [name, str_b s, str_p (name :: ctx) p]

datatype 'a bind = 
         KindingT of string
         | SortingT of string * 'a

fun collect_Uni_UniI t =
  case t of
      Uni ((name, _), t) =>
      let val (names, t) = collect_Uni_UniI t
      in
          (KindingT name :: names, t)
      end
    | UniI (s, (name, _), t) =>
      let val (names, t) = collect_Uni_UniI t
      in
          (SortingT (name, s) :: names, t)
      end
    | _ => ([], t)

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

fun str_t (ctx as (sctx, kctx)) (c : ty) : string =
  let
      fun str_uni ctx t =
        let val (binds, t) = collect_Uni_UniI t 
            val (binds, ctx) = str_tbinds ctx binds
            fun f bind =
              case bind of
                  KindingT name => name
                | SortingT (name, s) => sprintf "{$ : $}" [name, s]
            val binds = map f binds
        in
            sprintf "(forall$, $)" [join_prefix " " binds, str_t ctx t]
        end
  in
      case c of
	  Arrow (c1, d, c2) => sprintf "($ -- $ -> $)" [str_t ctx c1, str_i sctx d, str_t ctx c2]
	| Unit _ => "unit"
	| Prod (t1, t2) => sprintf "($ * $)" [str_t ctx t1, str_t ctx t2]
	| Sum (t1, t2) => sprintf "($ + $)" [str_t ctx t1, str_t ctx t2]
	| Uni _ => str_uni ctx c
	| UniI _ => str_uni ctx c
	| ExI (s, (name, _), t) => sprintf "(exists {$ : $}, $)" [name, str_s sctx s, str_t (name :: sctx, kctx) t]
	| AppRecur (name, ns, t, i, _) => 
	  sprintf "((rec $ $, $) $)" 
		  [name, 
		   join " " (map (fn (name, s) => sprintf "($ :: $)" [name, str_s sctx s]) ns),
		   str_t (rev (map #1 ns) @ sctx, name :: kctx) t,
		   join " " (map (str_i sctx) i)]
	| AppV ((x, _), ts, is, _) => 
	  if null ts andalso null is then
	      str_v kctx x
	  else
	      sprintf "($$$)" [(join "" o map (suffix " ") o map (surround "{" "}") o map (str_i sctx) o rev) is, (join "" o map (suffix " ") o map (str_t ctx) o rev) ts, str_v kctx x]
	| Int _ => "int"
  end

fun str_k ctx (k : kind) : string = 
  case k of
      ArrowK (_, n, sorts) => sprintf "($$Type)" [if n = 0 then "" else join " * " (repeat n "Type") ^ " => ", if null sorts then "" else join " * " (map (str_s ctx) sorts) ^ " => "]

end

signature TYPE = sig
    type sort
    type idx
    type ty
    val str_i : string list -> idx -> string
    val str_s : string list -> sort -> string
    val str_t : string list * string list -> ty -> string
    val str_sortings : string list -> (string * sort) list -> ((string * string) list * string list)
end

(* expressions *)
functor ExprFun (structure Var : VAR structure Type : TYPE structure Other : DEBUG) = struct
open Var
open Type
open Util
open Operators

type other = Other.t
val dummy = Other.dummy
type id = var * other
type name = string * other

type constr_core = (string * sort) list * ty * idx list
type constr_decl = string * constr_core * other
type constr = var * string list * constr_core

type return = ty option * idx option
                              
datatype ptrn =
	 ConstrP of id * string list * ptrn option * other
         | VarP of name
         | PairP of ptrn * ptrn
         | TTP of other
         | AliasP of name * ptrn * other

datatype expr =
	 Var of var * other
	 | App of expr * expr
	 | Abs of ty * ptrn * expr 
	 (* unit type *)
	 | TT of other
	 (* product type *)
	 | Pair of expr * expr
	 | Fst of expr
	 | Snd of expr
	 (* sum type *)
	 | Inl of ty * expr
	 | Inr of ty * expr
	 | SumCase of expr * string * expr * string * expr
	 (* universal *)
	 | AbsT of name * expr
	 | AppT of expr * ty
	 (* universal index *)
	 | AbsI of sort * name * expr
	 | AppI of expr * idx
	 (* existential index *)
	 | Pack of ty * idx * expr
	 | Unpack of expr * return * string * string * expr
	 (* recursive type *)
	 | Fold of ty * expr
	 | Unfold of expr
	 | BinOp of bin_op * expr * expr
	 | Const of int * other
	 | AppConstr of id * ty list * idx list * expr
	 | Case of expr * return * (ptrn * expr) list * other
	 | Never of ty
	 | Let of decl list * expr * other
	 | Fix of ty * name * expr
	 | Ascription of expr * ty
	 | AscriptionTime of expr * idx

     and decl =
         Val of ptrn * expr
	 | Datatype of string * string list * sort list * constr_decl list * other

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
    | (SOME t, NONE) => sprintf "return $ " [str_t skctx t]
    | (NONE, SOME d) => sprintf "return |> $ " [str_i sctx d]
    | (SOME t, SOME d) => sprintf "return $ |> $ " [str_t skctx t, str_i sctx d]
                                  
fun str_e (ctx as (sctx, kctx, cctx, tctx)) (e : expr) : string =
  let fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx) 
      val skctx = (sctx, kctx) 
  in
      case e of
	  Var (x, _) => str_v tctx x
	| Abs (t, pn, e) => 
          let val t = str_t skctx t
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
	| Inl (t, e) => sprintf "(inl [$] $)" [str_t skctx t, str_e ctx e]
	| Inr (t, e) => sprintf "(inr [$] $)" [str_t skctx t, str_e ctx e]
	| SumCase (e, name1, e1, name2, e2) => sprintf "(sumcase $ of inl $ => $ | inr $  => $)" [str_e ctx e, name1, str_e (add_t name1 ctx) e1, name2, str_e (add_t name2 ctx) e2]
	| Fold (t, e) => sprintf "(fold [$] $)" [str_t skctx t, str_e ctx e]
	| Unfold e => sprintf "(unfold $)" [str_e ctx e]
	| AbsT ((name, _), e) => sprintf "(fn $ => $)" [name, str_e (sctx, name :: kctx, cctx, tctx) e]
	| AppT (e, t) => sprintf "($ [$])" [str_e ctx e, str_t skctx t]
	| AbsI (s, (name, _), e) => sprintf "(fn $ :: $ => $)" [name, str_s sctx s, str_e (name :: sctx, kctx, cctx, tctx) e]
	| AppI (e, i) => sprintf "($ [$])" [str_e ctx e, str_i sctx i]
	| Pack (t, i, e) => sprintf "(pack $ ($, $))" [str_t skctx t, str_i sctx i, str_e ctx e]
	| Unpack (e1, return, iname, ename, e2) => sprintf "unpack $ $as ($, $) in $ end" [str_e ctx e1, str_return skctx return, iname, ename, str_e (iname :: sctx, kctx, cctx, ename :: tctx) e2]
	| Fix (t, (name, _), e) => sprintf "(fix ($ : $) => $)" [name, str_t skctx t, str_e (add_t name ctx) e]
	| Let (decls, e, _) => 
          let val (decls, ctx) = str_decls ctx decls
          in
              sprintf "let$ in $ end" [join_prefix " " decls, str_e ctx e]
          end
	| Ascription (e, t) => sprintf "($ : $)" [str_e ctx e, str_t skctx t]
	| AscriptionTime (e, d) => sprintf "($ |> $)" [str_e ctx e, str_i sctx d]
	| BinOp (opr, e1, e2) => sprintf "($ $ $)" [str_e ctx e1, str_bin_op opr, str_e ctx e2]
	| Const (n, _) => str_int n
	| AppConstr ((x, _), ts, is, e) => sprintf "($$$ $)" [str_v cctx x, (join "" o map (prefix " ") o map (fn t => sprintf "[$]" [str_t skctx t])) ts, (join "" o map (prefix " ") o map (fn i => sprintf "[$]" [str_i sctx i])) is, str_e ctx e]
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
            fun str_constr_decl (cname, (name_sorts, t, idxs), _) =
              let val (name_sorts, sctx') = str_sortings sctx name_sorts
                  val name_sorts = map (fn (nm, s) => sprintf "$ : $" [nm, s]) name_sorts
              in
                  sprintf "$ of$ $ ->$$ $" [cname, (join_prefix " " o map (surround "{" "}")) name_sorts, str_t (sctx', rev tnames @ name :: kctx) t, (join_prefix " " o map (surround "{" "}" o str_i sctx') o rev) idxs, str_tnames, name]
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

structure R = struct
open Region
type t = region
val dummy = dummy_region
end

structure NamefulType = TypeFun (structure Var = StringVar structure Other = R)
structure NamefulExpr = ExprFun (structure Var = StringVar structure Type = NamefulType structure Other = R)
structure Type = TypeFun (structure Var = IntVar structure Other = R)
structure Expr = ExprFun (structure Var = IntVar structure Type = Type structure Other = R)

