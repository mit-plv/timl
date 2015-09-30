signature VAR = sig
    eqtype var
    val str_v : string list -> var -> string
end

structure BasicSorts = struct
(* basic index sort *)
datatype bsort =
	 Time
	 | Bool
	 | BSUnit

fun str_b (s : bsort) : string = 
    case s of
	Time => "Time"
      | Bool => "Bool"
      | BSUnit => "Unit"
end

(* types *)
functor MakeType (structure Var : VAR) = struct
	open Var
	open BasicSorts
	open Util

	datatype idx =
		 VarI of var
		 | T0
		 | T1
		 | Tadd of idx * idx
		 | Tmult of idx * idx
		 | Tmax of idx * idx
		 | Tmin of idx * idx
		 | TrueI
		 | FalseI
		 | TT
		 | Tconst of int

	datatype prop =
		 True
		 | False
		 | And of prop * prop
		 | Or of prop * prop
		 | Imply of prop * prop
		 | Iff of prop * prop
		 | TimeLe of idx * idx
		 | Eq of idx * idx

	(* index sort *)
	datatype sort =
		 Basic of bsort
		 | Subset of bsort * string * prop
						  
	val STime = Basic Time
	val SBool = Basic Bool
	val SUnit = Basic BSUnit

	datatype ty = 
		 VarT of var
		 | Arrow of ty * idx * ty
		 | Unit
		 | Prod of ty * ty
		 | Sum of ty * ty
		 | UniI of sort * string * ty
		 | ExI of sort * string * ty
		 | Uni of string * ty
		 (* the kind of Recur is sort => Type, to allow for change of index *)
		 | AppRecur of string * (string * sort) list * ty * idx list
		 (* the first operant of App can only be a recursive type*)
		 | AppVar of var * idx list
		 | Int
		 | AppDatatype of var * ty list * idx list

	type constr = var * string list * (string * sort) list * ty * idx list

	datatype kind = 
		 Type
		 (* will only be used by recursive types *)
		 | KArrow of sort list
		 (* will only be used by datatypes *)
		 | KArrowDatatype of int * sort list

	infix 7 $ val op$ = Tmax
	infix 6 %+ val op%+ = Tadd
	infix 6 %* val op%* = Tmult
	infix 4 %<= val op%<= = TimeLe
	infix 3 /\ val op/\ = And
	infix 1 --> val op--> = Imply
	infix 1 <-> val op<-> = Iff

	fun str_i ctx (i : idx) : string = 
	    case i of
		VarI x => str_v ctx x
	      | T0 => "0"
	      | T1 => "1"
	      | Tadd (d1, d2) => sprintf "($ + $)" [str_i ctx d1, str_i ctx d2]
	      | Tmult (d1, d2) => sprintf "($ * $)" [str_i ctx d1, str_i ctx d2]
	      | Tmax (d1, d2) => sprintf "(max $ $)" [str_i ctx d1, str_i ctx d2]
	      | Tmin (d1, d2) => sprintf "(min $ $)" [str_i ctx d1, str_i ctx d2]
	      | TT => "()"
	      | TrueI => "true"
	      | FalseI => "false"
	      | Tconst n => str_int n

	fun str_p ctx p = 
	    case p of
		True => "True"
	      | False => "False"
	      | And (p1, p2) => sprintf "($ /\\ $)" [str_p ctx p1, str_p ctx p2]
	      | Or (p1, p2) => sprintf "($ \\/ $)" [str_p ctx p1, str_p ctx p2]
	      | Imply (p1, p2) => sprintf "($ -> $)" [str_p ctx p1, str_p ctx p2]
	      | Iff (p1, p2) => sprintf "($ <-> $)" [str_p ctx p1, str_p ctx p2]
	      | TimeLe (d1, d2) => sprintf "($ <= $)" [str_i ctx d1, str_i ctx d2]
	      | Eq (i1, i2) => sprintf "($ = $)" [str_i ctx i1, str_i ctx i2]

	fun str_s ctx (s : sort) : string = 
	    case s of
		Basic s => str_b s
	      | Subset (s, name, p) => sprintf "{ $ :: $ | $ }" [name, str_b s, str_p (name :: ctx) p]

	fun str_t (ctx as (sctx, kctx)) (c : ty) : string =
	    case c of
		Arrow (c1, d, c2) => sprintf "($ -- $ -> $)" [str_t ctx c1, str_i sctx d, str_t ctx c2]
	      | VarT x => str_v kctx x
	      | Unit => "unit"
	      | Prod (t1, t2) => sprintf "($ * $)" [str_t ctx t1, str_t ctx t2]
	      | Sum (t1, t2) => sprintf "($ + $)" [str_t ctx t1, str_t ctx t2]
	      | Uni (name, t) => sprintf "(forall $, $)" [name, str_t (sctx, name :: kctx) t]
	      | UniI (s, name, t) => sprintf "(forall $ :: $, $)" [name, str_s sctx s, str_t (name :: sctx, kctx) t]
	      | ExI (s, name, t) => sprintf "(exists $ :: $, $)" [name, str_s sctx s, str_t (name :: sctx, kctx) t]
	      | AppRecur (name, ns, t, i) => 
		sprintf "((rec $ $, $) $)" 
			[name, 
			 join " " (map (fn (name, s) => sprintf "($ :: $)" [name, str_s sctx s]) ns),
			 str_t (rev (map #1 ns) @ sctx, name :: kctx) t,
			 join " " (map (str_i sctx) i)]
	      | AppVar (x, i) => sprintf "($$)" [str_v kctx x, (join "" o map (prefix " ") o map (str_i sctx)) i]
	      | Int => "int"
	      | AppDatatype (x, ts, is) => sprintf "($$$)" [str_v kctx x, (join "" o map (prefix " ") o map (str_t ctx)) ts, (join "" o map (prefix " ") o map (str_i sctx)) is]

	fun str_k ctx (k : kind) : string = 
	    case k of
		Type => "Type"
	      | KArrow s => sprintf "($ => Type)" [join " * " (map (str_s ctx) s)]
	      | KArrowDatatype (n, sorts) => sprintf "($ => $ => Type)" [join " * " (repeat n "Type"), join " * " (map (str_s ctx) sorts)]

	end

signature TYPE = sig
    type sort
    type idx
    type ty
    val str_i : string list -> idx -> string
    val str_s : string list -> sort -> string
    val str_t : string list * string list -> ty -> string
end

(* expressions *)
functor MakeExpr (structure Var : VAR structure Type : TYPE) = struct
	open Var
	open Type
	open Util

	datatype ptrn =
		 Constr of var * string list * string

	datatype expr =
		 Var of var
		 | App of expr * expr
		 | Abs of ty * string * expr (* string is the variable name only for debug purpose *)
		 (* convenience facilities *)
		 | Fix of ty * string * expr
		 | Let of expr * string * expr
		 | Ascription of expr * ty
		 | AscriptionTime of expr * idx
		 (* unit type *)
		 | TT
		 (* product type *)
		 | Pair of expr * expr
		 | Fst of expr
		 | Snd of expr
		 (* sum type *)
		 | Inl of ty * expr
		 | Inr of ty * expr
		 | SumCase of expr * string * expr * string * expr
		 (* universal *)
		 | AbsT of string * expr
		 | AppT of expr * ty
		 (* universal index *)
		 | AbsI of sort * string * expr
		 | AppI of expr * idx
		 (* existential index *)
		 | Pack of ty * idx * expr
		 | Unpack of expr * ty * idx * string * string * expr
		 (* recursive type *)
		 | Fold of ty * expr
		 | Unfold of expr
		 | Plus of expr * expr
		 | Const of int
		 | AppConstr of var * ty list * idx list * expr
		 | Case of expr * ty * idx * (ptrn * expr) list
		 | Never of ty

	fun str_pn ctx pn = 
	    case pn of
		Constr (x, inames, ename) => sprintf "$ $ $" [str_v ctx x, join " " inames, ename]

	fun ptrn_names pn =
	    case pn of
		Constr (_, inames, ename) => (rev inames, [ename])

	fun str_e (ctx as (sctx, kctx, cctx, tctx)) (e : expr) : string =
	    let fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx) 
		val skctx = (sctx, kctx) 
	    in
		case e of
		    Var x => str_v tctx x
		  | Abs (t, name, e) => sprintf "(fn ($ : $) => $)" [name, str_t skctx t, str_e (add_t name ctx) e]
		  | App (e1, e2) => sprintf "($ $)" [str_e ctx e1, str_e ctx e2]
		  | TT => "()"
		  | Pair (e1, e2) => sprintf "($, $)" [str_e ctx e1, str_e ctx e2]
		  | Fst e => sprintf "(fst $)" [str_e ctx e]
		  | Snd e => sprintf "(snd $)" [str_e ctx e]
		  | Inl (t, e) => sprintf "(inl [$] $)" [str_t skctx t, str_e ctx e]
		  | Inr (t, e) => sprintf "(inr [$] $)" [str_t skctx t, str_e ctx e]
		  | SumCase (e, name1, e1, name2, e2) => sprintf "(sumcase $ of inl $ => $ | inr $  => $)" [str_e ctx e, name1, str_e (add_t name1 ctx) e1, name2, str_e (add_t name2 ctx) e2]
		  | Fold (t, e) => sprintf "(fold [$] $)" [str_t skctx t, str_e ctx e]
		  | Unfold e => sprintf "(unfold $)" [str_e ctx e]
		  | AbsT (name, e) => sprintf "(fn $ => $)" [name, str_e (sctx, name :: kctx, cctx, tctx) e]
		  | AppT (e, t) => sprintf "($ [$])" [str_e ctx e, str_t skctx t]
		  | AbsI (s, name, e) => sprintf "(fn $ :: $ => $)" [name, str_s sctx s, str_e (name :: sctx, kctx, cctx, tctx) e]
		  | AppI (e, i) => sprintf "($ [$])" [str_e ctx e, str_i sctx i]
		  | Pack (t, i, e) => sprintf "(pack $ ($, $))" [str_t skctx t, str_i sctx i, str_e ctx e]
		  | Unpack (e1, t, d, iname, ename, e2) => sprintf "unpack $ return $ |> $ as ($, $) in $ end" [str_e ctx e1, str_t skctx t, str_i sctx d, iname, ename, str_e (iname :: sctx, kctx, cctx, ename :: tctx) e2]
		  | Fix (t, name, e) => sprintf "(fix ($ : $) => $)" [name, str_t skctx t, str_e (add_t name ctx) e]
		  | Let (e1, name, e2) => sprintf "let $ = $ in $ end" [name, str_e ctx e1, str_e ctx e2]
		  | Ascription (e, t) => sprintf "($ : $)" [str_e ctx e, str_t skctx t]
		  | AscriptionTime (e, d) => sprintf "($ |> $)" [str_e ctx e, str_i sctx d]
		  | Plus (e1, e2) => sprintf "($ + $)" [str_e ctx e1, str_e ctx e2]
		  | Const n => str_int n
		  | AppConstr (x, ts, is, e) => sprintf "($$$ $)" [str_v cctx x, (join "" o map (prefix " ") o map (fn t => sprintf "[$]" [str_t skctx t])) ts, (join "" o map (prefix " ") o map (fn i => sprintf "[$]" [str_i sctx i])) is, str_e ctx e]
		  | Case (e, t, d, rules) => sprintf "(case $ return $ |> $ of $)" [str_e ctx e, str_t skctx t, str_i sctx d, join " | " (map (str_rule ctx) rules)]
		  | Never t => sprintf "(never [$])" [str_t skctx t]
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

structure NamefulType = MakeType (structure Var = StringVar)
structure NamefulExpr = MakeExpr (structure Var = StringVar structure Type = NamefulType)
structure Type = MakeType (structure Var = IntVar)
structure Expr = MakeExpr (structure Var = IntVar structure Type = Type)

