fun interleave xs ys =
  case xs of
      x :: xs' => x :: interleave ys xs'
    | nil => ys

fun sprintf s ls =
  String.concat (interleave (String.fields (fn c => c = #"$") s) ls)

val join = String.concatWith
fun prefix a b = a ^ b
val str_int = Int.toString

fun nth_error ls n =
  if n < 0 orelse n >= length ls then
      NONE
  else
      SOME (List.nth (ls, n))

signature VAR = sig
    eqtype var
    val str_v : string list -> var -> string
end

fun mapFst f (a, b) = (f a, b)
fun mapSnd f (a, b) = (a, f b)

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

(* types *)
functor MakeType (structure Var : VAR) = struct
open Var

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
	 | Eq of bsort * idx * idx

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
    | Eq (s, i1, i2) => sprintf "($ = $)" [str_i ctx i1, str_i ctx i2]

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
	| Unpack (e1, t, d, iname, ename, e2) => sprintf "unpack $ return $ time $ as ($, $) in $ end" [str_e ctx e1, str_t skctx t, str_i sctx d, iname, ename, str_e (iname :: sctx, kctx, cctx, ename :: tctx) e2]
	| Fix (t, name, e) => sprintf "(fix ($ : $) => $)" [name, str_t skctx t, str_e (add_t name ctx) e]
	| Let (e1, name, e2) => sprintf "let $ = $ in $ end" [name, str_e ctx e1, str_e ctx e2]
	| Ascription (e, t) => sprintf "($ : $)" [str_e ctx e, str_t skctx t]
	| AscriptionTime (e, d) => sprintf "($ |> $)" [str_e ctx e, str_i sctx d]
	| Plus (e1, e2) => sprintf "($ + $)" [str_e ctx e1, str_e ctx e2]
	| Const n => str_int n
	| AppConstr (x, ts, is, e) => sprintf "($$$ $)" [str_v cctx x, (join "" o map (prefix " ") o map (fn t => sprintf "[$]" [str_t skctx t])) ts, (join "" o map (prefix " ") o map (fn i => sprintf "[$]" [str_i sctx i])) is, str_e ctx e]
	| Case (e, t, d, rules) => sprintf "(case $ return $ time $ of $)" [str_e ctx e, str_t skctx t, str_i sctx d, join " | " (map (str_rule ctx) rules)]
	| Never t => sprintf "(never [$])" [str_t skctx t]
  end

and str_rule (ctx as (sctx, kctx, cctx, tctx)) (pn, e) =
    let val (inames, enames) = ptrn_names pn
	val ctx' = (inames @ sctx, kctx, cctx, enames @ tctx)
    in
	sprintf "$ => $" [str_pn cctx pn, str_e ctx' e]
    end

end			       

datatype 'a result =
	 OK of 'a
	 | Failed of string

fun error_monad () =
  let
      exception Error of string
      fun runError m _ =
	OK (m ())
	handle
	Error msg => Failed msg
  in
      (Error, runError)
  end

fun id x = x
fun const a _ = a
fun range n = List.tabulate (n, id)
fun repeat n a = List.tabulate (n, const a)
fun add_idx ls = ListPair.zip (range (length ls), ls)

structure StringVar = struct
type var = string
fun str_v ctx x : string = x
end

structure IntVar = struct
type var = int
fun str_v ctx x : string =
  (* sprintf "%$" [str_int x] *)
  case nth_error ctx x of
      SOME name => name
    | NONE => "unbound_" ^ str_int x
end

structure NameResolve = struct
structure T = MakeType (structure Var = StringVar)
structure E = MakeExpr (structure Var = StringVar structure Type = T)
structure Type = MakeType (structure Var = IntVar)
structure Expr = MakeExpr (structure Var = IntVar structure Type = Type)
open Type
open Expr

local
    val (Error, runError) = error_monad ()
    fun on_var ctx x =
      case List.find (fn (_, y) => y = x) (add_idx ctx) of
	  SOME (i, _) => i
	| NONE => raise Error ("Unbound variable " ^ x)

    fun on_idx ctx i =
	case i of
	    T.VarI x => VarI (on_var ctx x)
	  | T.T0 => T0
	  | T.T1 => T1
	  | T.Tadd (i1, i2) => Tadd (on_idx ctx i1, on_idx ctx i2)
	  | T.Tmult (i1, i2) => Tmult (on_idx ctx i1, on_idx ctx i2)
	  | T.Tmax (i1, i2) => Tmax (on_idx ctx i1, on_idx ctx i2)
	  | T.Tmin (i1, i2) => Tmin (on_idx ctx i1, on_idx ctx i2)
	  | T.TrueI => TrueI
	  | T.FalseI => FalseI
	  | T.TT => Type.TT
	  | T.Tconst n => Tconst n

    fun on_prop ctx p =
	case p of
	    T.True => True
	  | T.False => False
	  | T.And (p1, p2) => And (on_prop ctx p1, on_prop ctx p2)
	  | T.Or (p1, p2) => Or (on_prop ctx p1, on_prop ctx p2)
	  | T.Imply (p1, p2) => Imply (on_prop ctx p1, on_prop ctx p2)
	  | T.Iff (p1, p2) => Iff (on_prop ctx p1, on_prop ctx p2)
	  | T.TimeLe (i1, i2) => TimeLe (on_idx ctx i1, on_idx ctx i2)
	  | T.Eq (s, i1, i2) => Eq (s, on_idx ctx i1, on_idx ctx i2)

    fun on_sort ctx s =
	case s of
	    T.Basic s => Basic s
	  | T.Subset (s, name, p) => Subset (s, name, on_prop (name :: ctx) p)

    fun on_type (ctx as (sctx, kctx)) t =
	case t of
	    T.VarT x => VarT (on_var kctx x)
	  | T.Arrow (t1, d, t2) => Arrow (on_type ctx t1, on_idx sctx d, on_type ctx t2)
	  | T.Prod (t1, t2) => Prod (on_type ctx t1, on_type ctx t2)
	  | T.Sum (t1, t2) => Sum (on_type ctx t1, on_type ctx t2)
	  | T.Unit => Unit
	  | T.Uni (name, t) => Uni (name, on_type (sctx, name :: kctx) t)
	  | T.UniI (s, name, t) => UniI (on_sort sctx s, name, on_type (name :: sctx, kctx) t)
	  | T.ExI (s, name, t) => ExI (on_sort sctx s, name, on_type (name :: sctx, kctx) t)
	  | T.AppRecur (name, named_sorts, t, is) => AppRecur (name, map (mapSnd (on_sort sctx)) named_sorts, on_type (rev (map #1 named_sorts) @ sctx, name :: kctx) t, map (on_idx sctx) is)
	  | T.AppVar (x, is) => AppVar (on_var kctx x, map (on_idx sctx) is)
	  | T.Int => Int
	  | T.AppDatatype (x, ts, is) => AppDatatype (on_var kctx x, map (on_type ctx) ts, map (on_idx sctx) is)

    fun on_ptrn cctx pn =
	case pn of
	    E.Constr (x, inames, ename) => Constr (on_var cctx x, inames, ename)

    fun on_expr (ctx as (sctx, kctx, cctx, tctx)) e =
	let fun add_t name (sctx, kctx, cctx, tctx) = (sctx, kctx, cctx, name :: tctx)
	    val skctx = (sctx, kctx)
	in
	    case e of
		E.Var x => Var (on_var tctx x)
	      | E.Abs (t, name, e) => Abs (on_type skctx t, name, on_expr (add_t name ctx) e)
	      | E.App (e1, e2) => App (on_expr ctx e1, on_expr ctx e2)
	      | E.TT => TT
	      | E.Pair (e1, e2) => Pair (on_expr ctx e1, on_expr ctx e2)
	      | E.Fst e => Fst (on_expr ctx e)
	      | E.Snd e => Snd (on_expr ctx e)
	      | E.Inr (t, e) => Inr (on_type skctx t, on_expr ctx e)
	      | E.Inl (t, e) => Inl (on_type skctx t, on_expr ctx e)
	      | E.SumCase (e, name1, e1, name2, e2) => SumCase (on_expr ctx e, name1, on_expr (add_t name1 ctx) e1, name2, on_expr (add_t name2 ctx) e2)
	      | E.Fold (t, e) => Fold (on_type skctx t, on_expr ctx e)
	      | E.Unfold e => Unfold (on_expr ctx e)
	      | E.AbsT (name, e) => AbsT (name, on_expr (sctx, name :: kctx, cctx, tctx) e)
	      | E.AppT (e, t) => AppT (on_expr ctx e, on_type skctx t)
	      | E.AbsI (s, name, e) => AbsI (on_sort sctx s, name, on_expr (name :: sctx, kctx, cctx, tctx) e)
	      | E.AppI (e, i) => AppI (on_expr ctx e, on_idx sctx i)
	      | E.Pack (t, i, e) => Pack (on_type skctx t, on_idx sctx i, on_expr ctx e)
	      | E.Unpack (e1, t, d, iname, ename, e2) => Unpack (on_expr ctx e1, on_type skctx t, on_idx sctx d, iname, ename, on_expr (iname :: sctx, kctx, cctx, ename :: tctx) e2)
	      | E.Fix (t, name, e) => Fix (on_type skctx t, name, on_expr (add_t name ctx) e)
	      | E.Let (e1, name, e2) => Let (on_expr ctx e1, name, on_expr (add_t name ctx) e2)
	      | E.Ascription (e, t) => Ascription (on_expr ctx e, on_type skctx t)
	      | E.AscriptionTime (e, d) => AscriptionTime (on_expr ctx e, on_idx sctx d)
	      | E.Const n => Const n
	      | E.Plus (e1, e2) => Plus (on_expr ctx e1, on_expr ctx e2)
	      | E.AppConstr (x, ts, is, e) => AppConstr (on_var cctx x, map (on_type skctx) ts, map (on_idx sctx) is, on_expr ctx e)
	      | E.Case (e, t, d, rules) => Case (on_expr ctx e, on_type skctx t, on_idx sctx d, map (fn (pn, e) => (on_ptrn cctx pn, let val (inames, enames) = E.ptrn_names pn in on_expr (inames @ sctx, kctx, cctx, enames @ tctx ) e end)) rules)
	      | E.Never t => Never (on_type skctx t)
	end
in
fun resolve_type ctx e = runError (fn () => on_type ctx e) ()
fun resolve_expr ctx e = runError (fn () => on_expr ctx e) ()
end
end
			    
structure TypeCheck = struct

structure Type = MakeType (structure Var = IntVar)
structure Expr = MakeExpr (structure Var = IntVar structure Type = Type)
open Type
open Expr

infix 7 $
infix 6 %+
infix 6 %*
infix 4 %<=
infix 3 /\
infix 1 -->
infix 1 <->

fun is_value (e : expr) : bool =
  case e of
      Var _ => true
    | App _ => false
    | Abs _ => true
    | TT => true
    | Pair (e1, e2) => is_value e1 andalso is_value e2
    | Fst _ => false
    | Snd _ => false
    | Inl (_, e) => is_value e
    | Inr (_, e) => is_value e
    | SumCase _ => false
    | Fold (_, e) => is_value e
    | Unfold _ => false
    | AbsT _ => true
    | AppT _ => false
    | AbsI _ => true
    | AppI _ => false
    | Pack (_, _, e) => is_value e
    | Unpack _ => false
    | Fix _ => false
    | Let _ => false
    | Ascription _ => false
    | AscriptionTime _ => false
    | Plus _ => false
    | Const _ => true
    | AppConstr (_, _, _, e) => is_value e
    | Case _ => false
    | Never _ => false

fun shiftx_v x n y = 
  if y >= x then
      y + n
  else
      y

local
    fun f x n b =
      case b of
	  VarI y => VarI (shiftx_v x n y)
	| T0 => T0
	| T1 => T1
	| Tadd (d1, d2) => Tadd (f x n d1, f x n d2)
	| Tmult (d1, d2) => Tmult (f x n d1, f x n d2)
	| Tmax (d1, d2) => Tmax (f x n d1, f x n d2)
	| Tmin (d1, d2) => Tmin (f x n d1, f x n d2)
	| Type.TT => Type.TT
	| TrueI => TrueI
	| FalseI => FalseI
	| Tconst n => Tconst n
in
fun shiftx_i_i x n b = f x n b
fun shift_i_i b = shiftx_i_i 0 1 b
end

local
    fun f x n b =
      case b of
	  True => True
	| False => False
	| And (p1, p2) => And (f x n p1, f x n p2)
	| Or (p1, p2) => Or (f x n p1, f x n p2)
	| Imply (p1, p2) => Imply (f x n p1, f x n p2)
	| Iff (p1, p2) => Iff (f x n p1, f x n p2)
	| TimeLe (d1, d2) => TimeLe (shiftx_i_i x n d1, shiftx_i_i x n d2)
	| Eq (s, i1, i2) => Eq (s, shiftx_i_i x n i1, shiftx_i_i x n i2)
in
fun shiftx_i_p x n b = f x n b
fun shift_i_p b = shiftx_i_p 0 1 b
end

local
    fun f x n b =
      case b of
	  Basic s => Basic s
	| Subset (s, name, p) => Subset (s, name, shiftx_i_p (x + 1) n p)
in
fun shiftx_i_s x n b = f x n b
fun shift_i_s b = shiftx_i_s 0 1 b
end

local
    fun f x n b =
      case b of
	  VarT y => VarT y
	| Arrow (t1, d, t2) => Arrow (f x n t1, shiftx_i_i x n d, f x n t2)
	| Unit => Unit
	| Prod (t1, t2) => Prod (f x n t1, f x n t2)
	| Sum (t1, t2) => Sum (f x n t1, f x n t2)
	| Uni (name, t) => Uni (name, f x n t)
	| UniI (s, name, t) => UniI (shiftx_i_s x n s, name, f (x + 1) n t)
	| ExI (s, name, t) => ExI (shiftx_i_s x n s, name, f (x + 1) n t)
	| AppRecur (name, ns, t, i) => AppRecur (name, map (mapSnd (shiftx_i_s x n)) ns, f (x + length ns) n t, map (shiftx_i_i x n) i)
	| AppVar (y, i) =>  AppVar (y, map (shiftx_i_i x n) i)
	| Int => Int
	| AppDatatype (family, ts, is) => AppDatatype (family, map (f x n) ts, map (shiftx_i_i x n) is)
in
fun shiftx_i_t x n b = f x n b
fun shift_i_t b = shiftx_i_t 0 1 b
end

local
    fun f x n b =
      case b of
	  VarT y => VarT (shiftx_v x n y)
	| Arrow (t1, d, t2) => Arrow (f x n t1, d, f x n t2)
	| Unit => Unit
	| Prod (t1, t2) => Prod (f x n t1, f x n t2)
	| Sum (t1, t2) => Sum (f x n t1, f x n t2)
	| Uni (name, t) => Uni (name, f (x + 1) n t)
	| UniI (s, name, t) => UniI (s, name, f x n t)
	| ExI (s, name, t) => ExI (s, name, f x n t)
	| AppRecur (name, ns, t, i) => AppRecur (name, ns, f (x + 1) n t, i)
	| AppVar (y, i) => AppVar (shiftx_v x n y, i)
	| Int => Int
	| AppDatatype (family, ts, is) => AppDatatype (shiftx_v x n family, map (f x n) ts, is)

in
fun shiftx_t_t x n b = f x n b
fun shift_t_t b = shiftx_t_t 0 1 b
end

fun shift_pn_i pn i =
  let val (inames, _) = ptrn_names pn
  in
      shiftx_i_i 0 (length inames) i
  end

fun shift_pn_t pn t =
  let val (inames, _) = ptrn_names pn
  in
      shiftx_i_t 0 (length inames) t
  end

local
    fun f x n b =
      case b of
	  Var y => Var (shiftx_v x n y)
	| Abs (t, name, e) => Abs (t, name, f (x + 1) n e)
	| App (e1, e2) => App (f x n e1, f x n e2)
	| TT => TT
	| Pair (e1, e2) => Pair (f x n e1, f x n e2)
	| Fst e => Fst (f x n e)
	| Snd e => Snd (f x n e)
	| Inl (t, e) => Inl (t, f x n e)
	| Inr (t, e) => Inr (t, f x n e)
	| SumCase (e, name1, e1, name2, e2) => 
	  SumCase (f x n e, name1, f (x + 1) n e1, name2, f (x + 1) n e2)
	| Fold (t, e) => Fold (t, f x n e)
	| Unfold e => Unfold (f x n e)
	| AbsT (name, e) => AbsT (name, f x n e)
	| AppT (e, t) => AppT (f x n e, t)
	| AbsI (s, name, e) => AbsI (s, name, f x n e)
	| AppI (e, i) => AppI (f x n e, i)
	| Pack (t, i, e) => Pack (t, i, f x n e)
	| Unpack (e1, t, d, iname, ename, e2) => 
	  Unpack (f x n e1, t, d, iname, ename, f (x + 1) n e2)
	| Fix (t, name, e) => 
	  Fix (t, name, f (x + 1) n e)
	| Let (e1, name, e2) => Let (f x n e1, name, f (x + 1) n e2)
	| Ascription (e, t) => Ascription (f x n e, t)
	| AscriptionTime (e, d) => AscriptionTime (f x n e, d)
	| Const n => Const n
	| Plus (e1, e2) => Plus (f x n e1, f x n e2)
	| AppConstr (cx, ts, is, e) => AppConstr (cx, ts, is, f x n e)
	| Case (e, t, d, rules) => Case (f x n e, t, d, map (f_rule x n) rules)
	| Never t => Never t

    and f_rule x n (pn, e) =
	let val (_, enames) = ptrn_names pn 
	in
	    (pn, f (x + length enames) n e)
	end
in
fun shiftx_e_e x n b = f x n b
fun shift_e_e b = shiftx_e_e 0 1 b
end

exception Subst of string

local
    fun f x v b =
      case b of
	  VarI y =>
	  if y = x then
	      v
	  else if y > x then
	      VarI (y - 1)
	  else
	      VarI y
	| Tadd (d1, d2) => Tadd (f x v d1, f x v d2)
	| Tmult (d1, d2) => Tmult (f x v d1, f x v d2)
	| Tmax (d1, d2) => Tmax (f x v d1, f x v d2)
	| Tmin (d1, d2) => Tmin (f x v d1, f x v d2)
	| T0 => T0
	| T1 => T1
	| TrueI => TrueI
	| FalseI => FalseI
	| Type.TT => Type.TT
	| Tconst n => Tconst n
in
fun substx_i_i x (v : idx) (b : idx) : idx = f x v b
fun subst_i_i v b = substx_i_i 0 v b
end

local
    fun f x v b =
      case b of
	  True => True
	| False => False
	| And (p1, p2) => And (f x v p1, f x v p2)
	| Or (p1, p2) => Or (f x v p1, f x v p2)
	| Imply (p1, p2) => Imply (f x v p1, f x v p2)
	| Iff (p1, p2) => Iff (f x v p1, f x v p2)
	| TimeLe (d1, d2) => TimeLe (substx_i_i x v d1, substx_i_i x v d2)
	| Eq (s, i1, i2) => Eq (s, substx_i_i x v i1, substx_i_i x v i2)
in
fun substx_i_p x (v : idx) b = f x v b
fun subst_i_p (v : idx) (b : prop) : prop = substx_i_p 0 v b
end

local
    fun f x v b =
      case b of
	  Basic s => Basic s
	| Subset (s, name, p) => Subset (s, name, substx_i_p (x + 1) (shift_i_i v) p)
in
fun substx_i_s x (v : idx) (b : sort) : sort = f x v b
fun subst_i_s (v : idx) (b : sort) : sort = substx_i_s 0 v b
end

local
    fun f x v b =
      case b of
	  VarT y => VarT y
	| Arrow (t1, d, t2) => Arrow (f x v t1, substx_i_i x v d, f x v t2)
	| Unit => Unit
	| Prod (t1, t2) => Prod (f x v t1, f x v t2)
	| Sum (t1, t2) => Sum (f x v t1, f x v t2)
	| Uni (name, t) => Uni (name, f x v t)
	| UniI (s, name, t) => UniI (substx_i_s x v s, name, f (x + 1) (shift_i_i v) t)
	| ExI (s, name, t) => ExI (substx_i_s x v s, name, f (x + 1) (shift_i_i v) t)
	| AppRecur (name, ns, t, i) =>
	  let val n = length ns in
	      AppRecur (name, map (mapSnd (substx_i_s x v)) ns, f (x + n) (shiftx_i_i 0 n v) t, map (substx_i_i x v) i)
	  end
	| AppVar (y, i) => AppVar (y, map (substx_i_i x v) i)
	| Int => Int
	| AppDatatype (family, ts, is) => AppDatatype (family, map (f x v) ts, map (substx_i_i x v) is)
in
fun substx_i_t x (v : idx) (b : ty) : ty = f x v b
fun subst_i_t (v : idx) (b : ty) : ty = substx_i_t 0 v b
end

local
    fun f x (v : ty) (b : ty) : ty =
      case b of
	  VarT y =>
	  if y = x then
	      v
	  else if y > x then
	      VarT (y - 1)
	  else
	      VarT y
	| Arrow (t1, d, t2) => Arrow (f x v t1, d, f x v t2)
	| Unit => Unit
	| Prod (t1, t2) => Prod (f x v t1, f x v t2)
	| Sum (t1, t2) => Sum (f x v t1, f x v t2)
	| Uni (name, t) => Uni (name, f (x + 1) (shift_t_t v) t)
	| UniI (s, name, t) => UniI (s, name, f x (shift_i_t v) t)
	| ExI (s, name, t) => ExI (s, name, f x (shift_i_t v) t)
	| AppRecur (name, ns, t, i) => AppRecur (name, ns, f (x + 1) (shiftx_i_t 0 (length ns) (shift_t_t v)) t, i)
	| AppVar (y, i) => 
	  if y = x then
	      raise Subst "self-reference variable should only be substitute for via unrolling"
	  else if y > x then
	      AppVar (y - 1, i)
	  else
	      AppVar (y, i)
	| Int => Int
	| AppDatatype (y, ts, is) => 
	  let val y' = 
		  if y = x then
		      raise Subst "datatype can't be substituted for"
		  else if y > x then
		      y - 1
		  else
		      y 
	  in
	      AppDatatype (y', map (f x v) ts, is)
	  end
in
fun substx_t_t x (v : ty) (b : ty) : ty = f x v b
fun subst_t_t (v : ty) (b : ty) : ty = substx_t_t 0 v b
end

fun subst_is_t is t = 
  #1 (foldl (fn (i, (t, x)) => (substx_i_t x (shiftx_i_i 0 x i) t, x - 1)) (t, length is - 1) is)

fun subst_ts_t vs b = 
  #1 (foldl (fn (v, (b, x)) => (substx_t_t x (shiftx_t_t 0 x v) b, x - 1)) (b, length vs - 1) vs)

local
    datatype recur = Recur of string * (string * sort) list * ty
    fun shift_i_r n (Recur (name, ns, t)) = Recur (name, map (mapSnd (shiftx_i_s 0 n)) ns, shiftx_i_t (length ns) n t)
    fun shift_t_r (Recur (name, ns, t)) = Recur (name, ns, shiftx_t_t 1 1 t)
    fun f x v (b : ty) : ty =
      case b of
	  VarT y =>
	  if y = x then
	      raise Subst "unroll should only do subtitution on self-reference variable"
	  else if y > x then
	      VarT (y - 1)
	  else
	      VarT y
	| Arrow (t1, d, t2) => Arrow (f x v t1, d, f x v t2)
	| Unit => Unit
	| Prod (t1, t2) => Prod (f x v t1, f x v t2)
	| Sum (t1, t2) => Sum (f x v t1, f x v t2)
	| Uni (name, t) => Uni (name, f (x + 1) (shift_t_r v) t)
	| UniI (s, name, t) => UniI (s, name, f x (shift_i_r 1 v) t)
	| ExI (s, name, t) => ExI (s, name, f x (shift_i_r 1 v) t)
	| AppRecur (name, ns, t, i) => AppRecur (name, ns, f (x + 1) (shift_i_r (length ns) (shift_t_r v)) t, i)
	| AppVar (y, i) => 
	  if y = x then
	      let val Recur (name, ns, t) = v in
		  AppRecur (name, ns, t, i)
	      end
	  else if y > x then
	      AppVar (y - 1, i)
	  else
	      AppVar (y, i)
	| Int => Int
	| AppDatatype (y, ts, is) => 
	  let val y' = 
		  if y = x then
		      raise Subst "unroll should only do subtitution on self-reference variable"
		  else if y > x then
		      y - 1
		  else
		      y 
	  in
	      AppDatatype (y', map (f x v) ts, is)
	  end

in
fun unroll (name, ns, t, i) =
  subst_is_t i (f 0 (shift_i_r (length ns) (Recur (name, ns, t))) t)
end

fun shiftx_i_c x n (family, tnames, named_sorts, t, is) =
  let val m = length named_sorts 
  in
      (family, tnames, 
       #1 (foldr (fn ((name, s), (acc, m)) => ((name, shiftx_i_s (x + m) n s) :: acc, m - 1)) ([], m - 1) named_sorts), 
       shiftx_i_t (x + m) n t, 
       map (shiftx_i_i (x + m) n) is)
  end
fun shift_i_c b = shiftx_i_c 0 1 b

fun shiftx_t_c x n (family, tnames, named_sorts, t, is) =
  (shiftx_v x n family, tnames, named_sorts, shiftx_t_t (x + length tnames) n t, is)
fun shift_t_c b = shiftx_t_c 0 1 b

datatype kind = 
	 Type
	 (* will only be used by recursive types *)
	 | KArrow of sort list
	 (* will only be used by datatypes *)
	 | KArrowDatatype of int * sort list

local
    fun f x n b =
      case b of
	  Type => Type
	| KArrow s => KArrow (map (shiftx_i_s x n) s)
	| KArrowDatatype (n, sorts) => KArrowDatatype (n, map (shiftx_i_s x n) sorts)
in
fun shiftx_i_k x n b = f x n b
fun shift_i_k b = shiftx_i_k 0 1 b
end

fun str_k ctx (k : kind) : string = 
  case k of
      Type => "Type"
    | KArrow s => sprintf "($ => Type)" [join " * " (map (str_s ctx) s)]
    | KArrowDatatype (n, sorts) => sprintf "($ => $ => Type)" [join " * " (repeat n "Type"), join " * " (map (str_s ctx) sorts)]

(* sorting context *)
type scontext = (string * sort) list * prop list
(* kinding context *)
type kcontext = (string * kind) list 
(* constructor context *)
type constr = var * string list * (string * sort) list * ty * idx list
type ccontext = (string * constr) list
(* typing context *)
type tcontext = (string * ty) list
type context = scontext * kcontext * ccontext * tcontext

fun names (ctx : ('a * 'b) list) = map #1 ctx

fun shiftx_i_ps n ps = 
  map (shiftx_i_p 0 n) ps
fun shiftx_i_ks n ctx = 
  map (mapSnd (shiftx_i_k 0 n)) ctx
fun shiftx_i_cs n ctx = 
  map (mapSnd (shiftx_i_c 0 n)) ctx
fun shiftx_t_cs n ctx = 
  map (mapSnd (shiftx_t_c 0 n)) ctx
fun shiftx_i_ts n ctx = 
  map (mapSnd (shiftx_i_t 0 n)) ctx
fun shiftx_t_ts n ctx = 
  map (mapSnd (shiftx_t_t 0 n)) ctx

fun add_sorting pair (pairs, ps) = (pair :: pairs, shiftx_i_ps 1 ps)
fun add_sorting_sk pair (sctx, kctx) = 
  (add_sorting pair sctx, 
   shiftx_i_ks 1 kctx)
fun add_sorting_skc pair (sctx, kctx, cctx) = 
  (add_sorting pair sctx, 
   shiftx_i_ks 1 kctx,
   shiftx_i_cs 1 cctx)
fun add_sorting_skct pair (sctx, kctx, cctx, tctx) = 
  (add_sorting pair sctx, 
   shiftx_i_ks 1 kctx, 
   shiftx_i_cs 1 cctx, 
   shiftx_i_ts 1 tctx)
(* Within 'pairs', sort depends on previous sort *)
fun add_dep_sortings_skct (pairs', ps') ((pairs, ps), kctx, cctx, tctx) = 
  let val n = length pairs' 
  in
      ((pairs' @ pairs, ps' @ shiftx_i_ps n ps), 
       shiftx_i_ks n kctx, 
       shiftx_i_cs n cctx, 
       shiftx_i_ts n tctx)
  end
(* Within 'pairs', sort doesn't depend on previous sort. All of them point to 'sctx'. So the front elements of 'pairs' must be shifted to skip 'pairs' and point to 'sctx' *)
fun add_nondep_sortings pairs sctx = 
  #1 (foldr (fn ((name, s), (ctx, n)) => (add_sorting (name, (shiftx_i_s 0 n s)) ctx, n + 1)) (sctx, 0) pairs)
fun add_nondep_sortings_sk pairs (sctx, kctx) = 
  let val n = length pairs
  in
      (add_nondep_sortings pairs sctx,
       shiftx_i_ks n kctx)
  end
fun add_nondep_sortings_skc pairs (sctx, kctx, cctx) = 
  let val n = length pairs
  in
      (add_nondep_sortings pairs sctx,
       shiftx_i_ks n kctx,
       shiftx_i_ks n cctx)
  end

fun sctx_length (pairs, _) = length pairs
fun sctx_names ((pairs, _) : scontext) = map #1 pairs

fun lookup_sort (n : int) (pairs, _) : sort option = 
  case nth_error pairs n of
      NONE => NONE
    | SOME (_, s) => 
      SOME (shiftx_i_s 0 (n + 1) s)

fun add_kinding pair (kctx : kcontext) = pair :: kctx
fun add_kinding_kc pair (kctx, cctx) = 
  (add_kinding pair kctx, 
   shiftx_t_cs 1 cctx)
fun add_kinding_kct pair (kctx, cctx, tctx) = 
  (add_kinding pair kctx,
   shiftx_t_cs 1 cctx,
   shiftx_t_ts 1 tctx)
fun add_kinding_skct pair (sctx, kctx, cctx, tctx) = 
  (sctx,
   add_kinding pair kctx,
   shiftx_t_cs 1 cctx,
   shiftx_t_ts 1 tctx)
fun add_kinding_sk pair (sctx, kctx) = 
  (sctx, 
   add_kinding pair kctx)

fun lookup_kind (n : int) kctx : kind option = 
  case nth_error kctx n of
      NONE => NONE
    | SOME (_, k) => SOME k

fun add_typing pair tctx = pair :: tctx
fun add_typing_skct pair (sctx, kctx, cctx, tctx) = 
  (sctx, 
   kctx, 
   cctx,
   add_typing pair tctx)

fun lookup (n : int) (ctx : tcontext) : ty option = 
  case nth_error ctx n of
      NONE => NONE
    | SOME (_, t) => SOME t

fun get_base s =
  case s of
      Basic s => s
    | Subset (s, _, _) => s

type bscontext = (string * bsort) list

fun collect (pairs, ps) : bscontext * prop list = 
  let fun get_p s n ps =
	case s of
	    Basic _ => ps
	  | Subset (_, _, p) => shiftx_i_p 0 n p :: ps
      val bctx = map (mapSnd get_base) pairs
      val (ps', _) = foldl (fn ((name, s), (ps, n)) => (get_p s n ps, n + 1)) ([], 0) pairs
  in
      (bctx, ps @ ps')
  end

type vc = bscontext * prop list * prop

fun mem eq x ls = List.exists (fn y => eq (y, x)) ls
fun subset eq a b =
  List.all (fn x => mem eq x b) a
fun diff eq a b = List.filter (fn x => not (mem eq x b)) a

local
    fun find_unique name ls =
      if not (mem op= name ls) then
	  name
      else
	  let fun loop n =
		let val name' = name ^ str_int n in
		    if not (mem op= name' ls) then name' else loop (n + 1)
		end in
	      loop 0
	  end
in
fun unique names = foldr (fn (name, acc) => find_unique name acc :: acc) [] names
end

fun str_vc (ctx : bscontext, ps, p) =
  let val ctx = ListPair.zip (mapFst unique (ListPair.unzip ctx))
      val ctxn = map #1 ctx in
      sprintf "$$===============\n$\n" 
	      [join "" (map (fn (name, s) => sprintf "$ : $\n" [name, str_b s]) (rev ctx)), 
	       join "" (map (fn p => str_p ctxn p ^ "\n") ps), 
	       str_p ctxn p]
  end 

(* exception Unimpl *)
exception Impossible of string

(* use exception and cell to mimic the Error and Writer monads *)
local								    

    val (Error, runError) = error_monad ()

    val acc = ref ([] : vc list)

    fun tell vc =
      (
	(* print (sprintf "Output VC:\n$" [str_vc vc]); *)
	acc := vc :: !acc)

    fun runWriter m _ =
      (acc := []; let val r = m () in (r, !acc) end)

    fun check_length_n (n, ls) =
      if length ls = n then
	  ()
      else
	  raise Error "List length mismatch"

    fun check_length (a, b) =
      if length a = length b then
	  ()
      else
	  raise Error "List length mismatch"

    fun is_le (ctx : scontext, d : idx, d' : idx) =
      let val (bctx, ps) = collect ctx in
	  tell (bctx, ps, d %<= d')
      end
	  
    fun is_eq (ctx : scontext, i : idx, i' : idx, s : sort) = 
      let val (bctx, ps) = collect ctx in
	  tell (bctx, ps, Eq (get_base s, i, i'))
      end

    fun is_eqs (ctx, i, i', s) =
      (check_length (i, i');
       check_length (i, s);
       app (fn ((i, i'), s) => is_eq (ctx, i, i', s)) (ListPair.zip ((ListPair.zip (i, i')), s)))
	  
    fun is_true (ctx : scontext, p : prop) = 
      let val (bctx, ps) = collect ctx in
	  tell (bctx, ps, p)
      end

    fun is_iff (ctx : scontext, p1 : prop, p2 : prop) = 
      let val (bctx, ps) = collect ctx in
	  tell (bctx, ps, p1 <-> p2)
      end

    fun is_eqvbsort_b s s' =
      case (s, s') of
	  (Time, Time) => true
	| (Bool, Bool) => true
	| (BSUnit, BSUnit) => true
	| _ => false

    fun is_eqvbsort (s, s') =
      if is_eqvbsort_b s s' then
	  ()
      else
	  raise Error ("Basic sort mismatch: " ^ str_b s ^ " and " ^ str_b s')
		
    fun is_eqvsort (ctx, s, s') =
      case (s, s') of
	  (Basic s1, Basic s1') =>
	  is_eqvbsort (s1, s1')
	| (Subset (s1, name, p), Subset (s1', _, p')) =>
	  (is_eqvbsort (s1, s1');
	   is_iff (add_sorting (name, Basic s1) ctx, p, p'))
	| (Subset (s1, name, p), Basic s1') =>
	  (is_eqvbsort (s1, s1');
	   is_true (add_sorting (name, Basic s1) ctx, p))
	| (Basic s1, Subset (s1', name, p)) =>
	  (is_eqvbsort (s1, s1');
	   is_true (add_sorting (name, Basic s1) ctx, p))

    fun is_eqvsorts (ctx, s, s') =
      (check_length (s, s');
       ListPair.app (fn (s, s') => is_eqvsort (ctx, s, s')) (s, s'))
	  
    fun sort_mismatch ctx i expect have =  "Sort mismatch for " ^ str_i ctx i ^ ": expect " ^ expect ^ " have " ^ str_s ctx have

    fun is_wfsort (ctx : scontext, s : sort) =
      case s of
	  Basic _ => ()
	| Subset (s, name, p) =>
	  is_wfprop (add_sorting (name, Basic s) ctx, p)

    and is_wfprop (ctx : scontext, p : prop) =
	case p of
	    True => ()
	  | False => ()
	  | And (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | Or (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | Imply (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | Iff (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | TimeLe (d1, d2) =>
	    (check_sort (ctx, d1, STime);
	     check_sort (ctx, d2, STime))
	  | Eq (s, i1, i2) =>
	    (check_sort (ctx, i1, Basic s);
	     check_sort (ctx, i2, Basic s))

    and check_sort (ctx, i, s) : unit =
	let val s' = get_bsort (ctx, i) in
	    case s of
		Subset (s1, _, p) =>
		(is_eqvbsort (s', s1);
		 is_true (ctx, subst_i_p i p))
	      | Basic s1 => 
		is_eqvbsort (s', s1)
	end

    and check_bsort (ctx, i, s) : unit =
	is_eqvbsort (get_bsort (ctx, i), s)

    and get_bsort (ctx, i) =
	case i of
	    VarI x =>
	    (case lookup_sort x ctx of
      		 SOME s => get_base s
      	       | NONE => raise Error ("Unbound index variable " ^ str_v (sctx_names ctx) x))
      	  | T0 => Time
	  | T1 => Time
	  | Tadd (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | Tmult (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | Tmax (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | Tmin (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | TrueI => Bool
	  | FalseI => Bool
	  | Type.TT => BSUnit
	  | Tconst n => 
	    if n >= 0 then
		Time
	    else
		raise Error ("Time constant must be non-negative")

    fun is_wfsorts (ctx, s) = List.app (fn s => is_wfsort (ctx, s)) s
    fun check_sorts (ctx, i, s) =
      (check_length (i, s);
       ListPair.app (fn (i, s) => check_sort (ctx, i, s)) (i, s))

    (* k => Type *)
    fun recur_kind k = KArrow k

    fun kind_mismatch (ctx as (sctx, kctx)) c expect have =  "Kind mismatch for " ^ str_t ctx c ^ ": expect " ^ expect ^ " have " ^ str_k sctx have

    fun fetch_kind (kctx, a) =
      case lookup_kind a kctx of
      	  SOME k => k
      	| NONE => raise Error ("Unbound type variable " ^ str_v (names kctx) a)

    fun is_wftype (ctx as (sctx : scontext, kctx : kcontext), c : ty) : unit = 
      let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
					   (* val () = print (sprintf "Type wellformedness checking: $\n" [str_t ctxn c]) *)
      in
	  case c of
	      VarT a =>
	      (case fetch_kind (kctx, a) of
		   Type => ()
		 | k => raise Error (kind_mismatch ctxn c "Type" k))
	    | Arrow (c1, d, c2) => 
	      (is_wftype (ctx, c1);
	       check_sort (sctx, d, STime);
	       is_wftype (ctx, c2))
	    | Unit => ()
	    | Prod (c1, c2) => 
	      (is_wftype (ctx, c1);
	       is_wftype (ctx, c2))
	    | Sum (c1, c2) => 
	      (is_wftype (ctx, c1);
	       is_wftype (ctx, c2))
	    | Uni (name, c) => 
	      is_wftype (add_kinding_sk (name, Type) ctx, c)
	    | UniI (s, name, c) => 
	      (is_wfsort (sctx, s);
	       is_wftype (add_sorting_sk (name, s) ctx, c))
	    | ExI (s, name, c) => 
	      (is_wfsort (sctx, s);
	       is_wftype (add_sorting_sk (name, s) ctx, c))
	    | AppRecur (nameself, ns, t, i) =>
	      let val s = List.map #2 ns in
		  is_wfsorts (sctx, s);
		  is_wftype (add_nondep_sortings_sk (rev ns) (add_kinding_sk (nameself, recur_kind s) ctx), t);
		  check_sorts (sctx, i, s)
	      end
	    | AppVar (a, i) => 
	      (case fetch_kind (kctx, a) of
		   KArrow s => check_sorts (sctx, i, s)
		 | k => raise Error (kind_mismatch ctxn c "(s* => Type)" k))
	    | Int => ()
	    | AppDatatype (family, ts, is) => 
	      (case fetch_kind (kctx, family) of
		   KArrowDatatype (n, sorts) => 
		   (check_length_n (n, ts);
		    check_sorts (sctx, is, sorts))
		 | k => raise Error (kind_mismatch ctxn c "Type* => s* => Type" k))
      end

    fun not_subtype ctx c c' = str_t ctx c ^ " is not subtype of " ^ str_t ctx c'

    (* is_subtype assumes that the types are already checked against the given kind, so it doesn't need to worry about their well-formedness *)
    fun is_subtype (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) =
      let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
					   (* val () = print (sprintf "Subtyping checking: \n$\n<:\n$\n" [str_t ctxn c, str_t ctxn c'])  *)
      in
	  case (c, c') of
	      (Arrow (c1, d, c2), Arrow (c1', d', c2')) =>
	      (is_subtype (ctx, c1', c1);
	       is_le (sctx, d, d');
	       is_subtype (ctx, c2, c2'))
	    | (VarT a, VarT a') => 
	      if a = a' then
		  ()
	      else
		  raise Error (not_subtype ctxn c c')
	    | (Unit, Unit) => ()
	    | (Prod (c1, c2), Prod (c1', c2')) =>
	      (is_subtype (ctx, c1, c1');
	       is_subtype (ctx, c2, c2'))
	    | (Sum (c1, c2), Sum (c1', c2')) => 
	      (is_subtype (ctx, c1, c1');
	       is_subtype (ctx, c2, c2'))
	    | (Uni (name, c), Uni (_, c')) => 
	      is_subtype (add_kinding_sk (name, Type) ctx, c, c')
	    | (UniI (s, name, c), UniI (s', _, c')) => 
	      (is_eqvsort (sctx, s, s');
	       is_subtype (add_sorting_sk (name, s) ctx, c, c'))
	    | (ExI (s, name, c), ExI (s', _, c')) => 
	      (is_eqvsort (sctx, s, s');
	       is_subtype (add_sorting_sk (name, s) ctx, c, c'))
	    (* currently don't support subtyping for recursive types, so they must be equivalent *)
	    | (AppRecur (nameself, ns, t, i), AppRecur (_, ns', t', i')) => 
	      let val s = List.map #2 ns
		  val s' = List.map #2 ns'
		  val () = is_eqvsorts (sctx, s, s')
		  val () = is_eqs (sctx, i, i', s)
		  val ctx' = add_nondep_sortings_sk (rev ns) (add_kinding_sk (nameself, recur_kind s) ctx) in
		  is_eqvtype (ctx', t, t')
	      end
	    | (AppVar (a, i), AppVar (a', i')) => 
	      if a = a' then
		  case fetch_kind (kctx, a) of
		      KArrow s => is_eqs (sctx, i, i', s)
		    | _ => raise Impossible "is_subtype: x in (x is) should have an arrow kind"
	      else
		  raise Error (not_subtype ctxn c c')
	    | (Int, Int) => ()
	    | (AppDatatype (a, ts, is), AppDatatype (a', ts', is')) => 
	      if a = a' then
		  case fetch_kind (kctx, a) of
		      KArrowDatatype (_, sorts) =>
		      (app (fn (t, t') => is_eqvtype (ctx, t, t')) (ListPair.zip (ts, ts'));
		       is_eqs (sctx, is, is', sorts))
		    | k => raise Impossible "is_subtype: x in (x ts is) should have an datatype-arrow kind"
	      else
		  raise Error (not_subtype ctxn c c')
	    | _ => raise Error (not_subtype ctxn c c')
      end

    and is_eqvtype (kctx, c, c') =
	(is_subtype (kctx, c, c');
	 is_subtype (kctx, c', c))

    fun no_join ctx c c' = "Cannot find a join (minimal supertype) of " ^ str_t ctx c ^ " and " ^ str_t ctx c'
    fun no_meet ctx c c' = "Cannot find a meet (maximal subtype) of " ^ str_t ctx c ^ " and " ^ str_t ctx c'

    (* c and c' are already checked for wellformedness *)
    fun join_type (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) : ty = 
      let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
      in
	  case (c, c') of
	      (Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
	      let val c1'' = meet (ctx, c1, c1') 
		  val d'' = d $ d' 
		  val c2'' = join_type (ctx, c2, c2') in
		  Arrow (c1'', d'', c2'')
	      end
	    | (VarT a, VarT a') => 
	      if a = a' then
		  c
	      else
		  raise Error (no_join ctxn c c')
	    | (Unit, Unit) => Unit
	    | (Prod (c1, c2), Prod (c1', c2')) => 
	      let val c1'' = join_type (ctx, c1, c1') 
		  val c2'' = join_type (ctx, c2, c2') in
		  Prod (c1'', c2'')
	      end
	    | (Sum (c1, c2), Sum (c1', c2')) => 
	      let val c1'' = join_type (ctx, c1, c1') 
		  val c2'' = join_type (ctx, c2, c2') in
		  Sum (c1'', c2'')
	      end
	    | (Uni (name, t), Uni (_, t')) => 
	      let val t'' = join_type (add_kinding_sk (name, Type) ctx, t, t') in
		  Uni (name, t'')
	      end
	    | (UniI (s, name, t), UniI (s', _, t')) => 
	      let val () = is_eqvsort (sctx, s, s')
		  val t'' = join_type (add_sorting_sk (name, s) ctx, t, t') in
		  UniI (s, name, t'')
	      end
	    | (ExI (s, name, t), ExI (s', _, t')) => 
	      let val () = is_eqvsort (#1 ctx, s, s')
		  val t'' = join_type (add_sorting_sk (name, s) ctx, t, t') in
		  ExI (s, name, t'')
	      end
	    (* currently don't support join for recursive types, so they must be equivalent *)
	    | (AppRecur _, AppRecur _) => 
	      (is_eqvtype (ctx, c, c');
	       c)
	    | (AppVar _, AppVar _) => 
	      (is_eqvtype (ctx, c, c');
	       c)
	    | (Int, Int) => Int
	    | _ => raise Error (no_join ctxn c c')
      end

    and meet (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) : ty = 
	let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	in
	    case (c, c') of
		(Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
		let val c1'' = join_type (ctx, c1, c1') 
		    val d'' = Tmin (d, d')
		    val c2'' = meet (ctx, c2, c2') in
		    Arrow (c1'', d'', c2'')
		end
	      | (VarT a, VarT a') => 
		if a = a' then
		    c
		else
		    raise Error (no_meet ctxn c c')
	      | (Unit, Unit) => Unit
	      | (Prod (c1, c2), Prod (c1', c2')) => 
		let val c1'' = meet (ctx, c1, c1') 
		    val c2'' = meet (ctx, c2, c2') in
		    Prod (c1'', c2'')
		end
	      | (Sum (c1, c2), Sum (c1', c2')) => 
		let val c1'' = meet (ctx, c1, c1') 
		    val c2'' = meet (ctx, c2, c2') in
		    Sum (c1'', c2'')
		end
	      | (Uni (name, t), Uni (_, t')) => 
		let val t'' = meet (add_kinding_sk (name, Type) ctx, t, t') in
		    Uni (name, t'')
		end
	      | (UniI (s, name, t), UniI (s', _, t')) => 
		let val () = is_eqvsort (sctx, s, s')
		    val t'' = meet (add_sorting_sk (name, s) ctx, t, t') in
		    UniI (s, name, t'')
		end
	      | (ExI (s, name, t), ExI (s', _, t')) => 
		let val () = is_eqvsort (#1 ctx, s, s')
		    val t'' = meet (add_sorting_sk (name, s) ctx, t, t') in
		    ExI (s, name, t'')
		end
	      (* currently don't support meet for recursive types, so they must be equivalent *)
	      | (AppRecur _, AppRecur _) => 
		(is_eqvtype (ctx, c, c');
		 c)
	      | (AppVar _, AppVar _) => 
		(is_eqvtype (ctx, c, c');
		 c)
	      | (Int, Int) => Int
	      | _ => raise Error (no_meet ctxn c c')
	end

    val Cover_False = []
    fun Cover_Or (a, b) = a @ b
    fun Cover_Constr e = [e]

    fun get_family ((x, _, _, _, _) : constr) = x

    fun get_family_members cctx x =
      List.mapPartial (fn (n, (_, c)) => if get_family c = x then SOME n else NONE) (add_idx cctx)

    (* covers should already have type t *)
    fun check_redundancy ((_, _, cctx), t, prev, this) =
      if not (subset op= this prev) then ()
      else raise Error (sprintf "Redundant pattern $ after [$]" [join ", " (map (str_v (names cctx)) this), join ", " (map (str_v (names cctx)) prev)])

    fun check_exhaustive ((_, _, cctx), t, cover) =
      case t of
	  AppDatatype (family, _, _) =>
	  let val all = get_family_members cctx family
	      val missed = diff op= all cover
	  in
	      if missed = [] then ()
	      else raise Error (sprintf "Not exhaustive, missing these constructors: $" [join ", " (map (str_v (names cctx)) missed)])
	  end
	| _ => raise Impossible "shouldn't check exhaustiveness under this type"

    fun fetch_constr (ctx, x) =
      case nth_error ctx x of
	  SOME (name, c) => (name, c)
	| NONE => raise Error (sprintf "Unbound constructor $" [str_v (names ctx) x])

    fun fetch_constr_type (ctx, cx) =
      let val (cname, (family, tnames, ns, t, is)) = fetch_constr (ctx, cx)
	  val ts = (map VarT o rev o range o length) tnames
	  val t = Arrow (t, T0, AppDatatype (shiftx_v 0 (length tnames) family, ts, is))
	  val t = foldr (fn ((name, s), t) => UniI (s, name, t)) t ns
	  val t = foldr Uni t tnames
      in
	  (cname, t)
      end

    (* t is already checked for wellformedness *)
    fun match_ptrn (ctx as (sctx, kctx, cctx), pn, t) =
      let val skctxn as (sctxn, _) = (sctx_names sctx, names kctx)
      in
	  case (pn, t) of
	      (Constr (cx, inames, ename), AppDatatype (x, ts, is)) =>
	      let val (_, c as (x', tnames, ns, t1, is')) = fetch_constr (cctx, cx)
	      in
		  if x' = x then
		      let val () = check_length (tnames, ts)
			  val t1 = subst_ts_t ts t1
			  val bs = map (fn i => get_bsort (sctx, i)) is
			  val is = map (shiftx_i_i 0 (length ns)) is
			  val () = check_length (is', is)
			  val ps = map (fn (s, (i', i)) => Eq (s, i', i)) (ListPair.zip (bs, ListPair.zip (is', is)))
			  val () = check_length (inames, ns)
		      in
			  ((rev (ListPair.zip (inames, #2 (ListPair.unzip ns))), ps), (ename, t1), Cover_Constr cx)
		      end
		  else
		      raise Error (sprintf "Type of constructor $ doesn't match datatype:\n  expect: $\n  got: $\n" [str_v (names cctx) cx, str_t skctxn (VarT x), str_t skctxn (VarT x')])
	      end
	    | _ => raise Error (sprintf "Pattern $ doesn't match type $" [str_pn (names cctx) pn, str_t skctxn t])
      end

    fun mismatch (ctx as (sctx, kctx, _, _)) e expect have =  
      sprintf "Type mismatch for $:\n  expect: $\n  got: $\n" [str_e ctx e, expect, str_t (sctx, kctx) have]
    fun mismatch_anno ctx expect have =  "Type annotation mismatch: expect " ^ expect ^ " have " ^ str_t ctx have

    fun check_fix_body e =
      case e of
    	  AbsI (_, _, e') => check_fix_body e'
    	| Abs _ => ()
    	| _ => raise Error "The body of fixpoint must have the form (fn [(_ :: _) ... (_ :: _)] (_ : _) => _)"

    fun get_type (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext, tctx : tcontext), e : expr) : ty * idx =
      let val skctx = (sctx, kctx) 
	  val ctxn as (sctxn, kctxn, cctxn, tctxn) = (sctx_names sctx, names kctx, names cctx, names tctx) 
	  val skctxn = (sctxn, kctxn)
	  (* val () = print (sprintf "Typing $\n" [str_e ctxn e]) *)
	  val (t, d) =
	      case e of
		  Var x =>
		  (case lookup x tctx of
      		       SOME t => (t, T0)
      		     | NONE => raise Error ("Unbound variable " ^ str_v tctxn x))
		| App (e1, e2) =>
		  let val (t1, d1) = get_type (ctx, e1) in
    		      case t1 of
    			  Arrow (t2, d, t) =>
    			  let val (t2', d2) = get_type (ctx, e2) 
			      val () = is_subtype (skctx, t2', t2) in
    			      (t, d1 %+ d2 %+ T1 %+ d) 
			  end
    			| t1' =>  raise Error (mismatch ctxn e1 "(_ -- _ -> _)" t1')
		  end
		| Abs (t, varname, e) => 
		  let val () = is_wftype (skctx, t)
		      val (t1, d) = get_type (add_typing_skct (varname, t) ctx, e) in
		      (Arrow (t, d, t1), T0)
		  end
		| TT => (Unit, T0)
		| Pair (e1, e2) => 
		  let val (t1, d1) = get_type (ctx, e1) 
		      val (t2, d2) = get_type (ctx, e2) in
		      (Prod (t1, t2), d1 %+ d2)
		  end
		| Fst e => 
		  let val (t, d) = get_type (ctx, e) in 
		      case t of
			  Prod (t1, t2) => (t1, d)
			| t' => raise Error (mismatch ctxn e "(_ * _)" t')
		  end
		| Snd e => 
		  let val (t, d) = get_type (ctx, e) in 
		      case t of
			  Prod (t1, t2) => (t2, d)
			| t' => raise Error (mismatch ctxn e "(_ * _)" t')
		  end
		| Inl (t2, e) => 
		  let val (t1, d) = get_type (ctx, e)
		      val () = is_wftype (skctx, t2) in
		      (Sum (t1, t2), d)
		  end
		| Inr (t1, e) => 
		  let val (t2, d) = get_type (ctx, e)
		      val () = is_wftype (skctx, t1) in
		      (Sum (t1, t2), d)
		  end
		| SumCase (e, name1, e1, name2, e2) => 
		  let val (t, d) = get_type (ctx, e) in
		      case t of
			  Sum (t1, t2) => 
			  let val (tr1, d1) = get_type (add_typing_skct (name1, t1) ctx, e1)
			      val (tr2, d2) = get_type (add_typing_skct (name2, t2) ctx, e2)
			      val tr = join_type (skctx, tr1, tr2) in
			      (tr, d %+ d1 $ d2)
			  end
			| t' => raise Error (mismatch ctxn e "(_ + _)" t')
		  end
		| AbsT (name, e) => 
		  if is_value e then
		      let val (t, _) = get_type (add_kinding_skct (name, Type) ctx, e) in
			  (Uni (name, t), T0)
		      end 
		  else
		      raise Error ("The body of a universal abstraction must be a value")
		| AppT (e, c) =>
		  let val (t, d) = get_type (ctx, e) in
		      case t of
			  Uni (_, t1) => 
			  let val () = is_wftype (skctx, c) in
			      (subst_t_t c t1, d)
			  end
			| t' => raise Error (mismatch ctxn e "(forall _ : _, _)" t')
		  end
		| AbsI (s, name, e) => 
		  if is_value e then
		      let val () = is_wfsort (sctx, s)
			  val (t, _) = get_type ((add_sorting_skct (name, s) ctx), e) in
			  (UniI (s, name, t), T0)
		      end 
		  else
		      raise Error ("The body of a universal abstraction must be a value")
		| AppI (e, i) =>
		  let val (t, d) = get_type (ctx, e) in
		      case t of
			  UniI (s, _, t1) => 
			  let val () = check_sort (sctx, i, s) in
			      (subst_i_t i t1, d)
			  end
			| t' => raise Error (mismatch ctxn e "(forallI _ : _, _)" t')
		  end
		| Fold (t, e) => 
		  (case t of
		       AppRecur t1 =>
		       let val () = is_wftype (skctx, t)
			   val (t', d) = get_type (ctx, e)
			   val () = is_subtype (skctx, t', unroll t1) in
			   (t, d)
		       end
		     | t' => raise Error (mismatch_anno skctxn "((recur (_ :: _) (_ : _), _) _)" t'))
		| Unfold e =>
		  let val (t, d) = get_type (ctx, e) in
		      case t of
	      		  AppRecur t1 =>
			  (unroll t1, d)
			| t' => raise Error (mismatch ctxn e "((recur (_ :: _) (_ : _), _) _)" t')
		  end
		| Pack (t, i, e) =>
		  (case t of
		       ExI (s, _, t1) =>
		       let val () = is_wftype (skctx, t)
			   val () = check_sort (sctx, i, s)
			   val (t2, d) = get_type (ctx, e)
			   val () = is_subtype (skctx, t2, (subst_i_t i t1)) in
			   (t, d)
		       end
		     | t' => raise Error (mismatch_anno skctxn "(ex _ : _, _)" t'))
		| Unpack (e1, t, d, idx_var, expr_var, e2) => 
		  let val () = is_wftype (skctx, t)
		      val () = check_sort (sctx, d, STime)
		      val (t1, d1) = get_type (ctx, e1) in
		      case t1 of
			  ExI (s, _, t1') => 
			  let val ctx' = add_typing_skct (expr_var, t1') (add_sorting_skct (idx_var, s) ctx)
			      val () = check_type (ctx', e2, shift_i_t t, shift_i_i d)
			  in
			      (t, d1 %+ d)
			  end
			| t1' => raise Error (mismatch ctxn e1 "(ex _ : _, _)" t1')
		  end
		| Let (e1, name, e2) => 
		  let val (t1, d1) = get_type (ctx, e1)
		      val (t2, d2) = get_type (add_typing_skct (name, t1) ctx, e2) in
		      (t2, d1 %+ d2)
		  end
		| Fix (t, name, e) => 
		  let val () = check_fix_body e
		      val () = is_wftype (skctx, t)
		      val (t1, _) = get_type (add_typing_skct (name, t) ctx, e)
		      val () = is_subtype (skctx, t1, t) in
		      (t, T0)
		  end
		| Ascription (e, t) => 
		  let val () = is_wftype (skctx, t)
		      val (t1, d) = get_type (ctx, e)
		      val () = is_subtype (skctx, t1, t) in
		      (t, d)
		  end
		| AscriptionTime (e, d) => 
		  let val () = check_sort (sctx, d, STime)
		      val (t, d1) = get_type (ctx, e)
		      val () = is_le (sctx, d1, d) in
		      (t, d)
		  end
		| Plus (e1, e2) =>
		  let val (t1, d1) = get_type (ctx, e1)
		      val (t2, d2) = get_type (ctx, e2) in
		      is_subtype (skctx, t1, Int);
		      is_subtype (skctx, t2, Int);
		      (Int, d1 %+ d2 %+ T1)
		  end
		| Const _ => 
		  (Int, T0)
		| AppConstr (cx, ts, is, e) => 
		  let val (cname, tc) = fetch_constr_type (cctx, cx)
		      val () = is_wftype (skctx, tc)
		      val (_, d) = get_type (ctx, e)
		      (* delegate to checking e' *)
		      val f = Var 0
		      val f = foldl (fn (t, e) => AppT (e, t)) f ts
		      val f = foldl (fn (i, e) => AppI (e, i)) f is
		      val e' = App (f, shift_e_e e)
		      val (t, _) = get_type (add_typing_skct (cname, tc) ctx, e') 
		  in
		      (* constructor application doesn't incur count *)
		      (t, d)
		  end
		| Case (e, t, d, rules) => 
		  let val () = is_wftype (skctx, t)
		      val () = check_sort (sctx, d, STime)
		      val (t1, d1) = get_type (ctx, e)
		  in
		      check_rules (ctx, rules, (t1, d, t));
		      (t, d1 %+ d)
		  end
		| Never t => 
		  (is_wftype (skctx, t);
		   is_true (sctx, False);
		   (t, T0))
		      (* val () = print (sprintf "  type: $ [for $]\n  time: $\n" [str_t skctxn t, str_e ctxn e, str_i sctxn d]) *)
      in
	  (t, d)
      end

    and check_type (ctx as (sctx, kctx, cctx, tctx), e, t, d) =
	let 
	    val ctxn as (sctxn, kctxn, cctxn, tctxn) = (sctx_names sctx, names kctx, names cctx, names tctx) 
	    (* val () = print (sprintf "Type checking $ against $ and $\n" [str_e ctxn e, str_t (sctxn, kctxn) t, str_i sctxn d]) *)
	    val (t', d') = get_type (ctx, e)
	in
	    is_subtype ((sctx, kctx), t', t);
	    is_le (sctx, d', d)
	end

    and check_rules (ctx as (sctx, kctx, cctx, tctx), rules, t as (t1, _, _)) =
	let val skcctx = (sctx, kctx, cctx) 
	    fun f (rule, acc) =
	      let val cover = check_rule (ctx, rule, t)
		  val () = check_redundancy (skcctx, t1, acc, cover)
	      in
		  Cover_Or (cover, acc)
	      end 
	    val cover = foldl f Cover_False rules
	in
	    check_exhaustive (skcctx, t1, cover)
	end

    and check_rule (ctx as (sctx, kctx, cctx, tctx), (pn, e), t as (t1, d, t2)) =
	let val skcctx = (sctx, kctx, cctx) 
	    val (sctx', nt, cover) = match_ptrn (skcctx, pn, t1)
	    val ctx' = add_typing_skct nt (add_dep_sortings_skct sctx' ctx)
	in
	    check_type (ctx', e, shift_pn_t pn t2, shift_pn_i pn d);
	    cover
	end

in								     

fun vcgen ctx e : ((ty * idx) * vc list) result =
  runError (runWriter (fn () => get_type (ctx, e))) ()
	   
end

local
    fun solver (ctx, ps, p) =
      isSome (List.find (fn x => x = p) ps) orelse
      case p of
	  Imply (p1, p2) => solver (ctx, p1 :: ps, p2)
	| Iff (p1, p2) => solver (ctx, p1 :: ps, p2) andalso solver (ctx, p2 :: ps, p1)
	| And (p1, p2) => solver (ctx, ps, p1) andalso solver (ctx, ps, p1)
	| Or (p1, p2) => solver (ctx, ps, p1) orelse solver (ctx, ps, p1)
	| True => true
	| Eq (_, i1, i2) => i1 = i2
	| TimeLe (i1, i2) => i1 = i2
	| _ => false

in
fun trivial_solver vcs = List.filter (fn vc => solver vc = false) vcs
end

local
    fun passi i =
      case i of
	  Tmax (i1, i2) =>
	  if i1 = i2 then
	      (true, i1)
	  else
	      let val (b1, i1) = passi i1
		  val (b2, i2) = passi i2 in
		  (b1 orelse b2, Tmax (i1, i2))
	      end
	| Tmin (i1, i2) =>
	  if i1 = i2 then
	      (true, i1)
	  else
	      let val (b1, i1) = passi i1
		  val (b2, i2) = passi i2 in
		  (b1 orelse b2, Tmin (i1, i2))
	      end
	| Tadd (i1, i2) => 
	  if i1 = T0 then (true, i2)
	  else if i2 = T0 then (true, i1)
	  else
	      let val (b1, i1) = passi i1
		  val (b2, i2) = passi i2 in
		  (b1 orelse b2, Tadd (i1, i2))
	      end
	| Tmult (i1, i2) => 
	  if i1 = T0 then (true, T0)
	  else if i2 = T0 then (true, T0)
	  else if i1 = T1 then (true, i2)
	  else if i2 = T1 then (true, i1)
	  else
	      let val (b1, i1) = passi i1
		  val (b2, i2) = passi i2 in
		  (b1 orelse b2, Tmult (i1, i2))
	      end
	| _ => (false, i)
		   
    fun passp p = 
      case p of
	  And (p1, p2) => 
	  let val (b1, p1) = passp p1
	      val (b2, p2) = passp p2 in
	      (b1 orelse b2, And (p1, p2))
	  end
	| Or (p1, p2) => 
	  let val (b1, p1) = passp p1
	      val (b2, p2) = passp p2 in
	      (b1 orelse b2, Or (p1, p2))
	  end
	| Imply (p1, p2) => 
	  let val (b1, p1) = passp p1
	      val (b2, p2) = passp p2 in
	      (b1 orelse b2, Imply (p1, p2))
	  end
	| Iff (p1, p2) => 
	  let val (b1, p1) = passp p1
	      val (b2, p2) = passp p2 in
	      (b1 orelse b2, Iff (p1, p2))
	  end
	| Eq (s, i1, i2) => 
	  let val (b1, i1) = passi i1
	      val (b2, i2) = passi i2 in
	      (b1 orelse b2, Eq (s, i1, i2))
	  end
	| TimeLe (i1, i2) => 
	  let val (b1, i1) = passi i1
	      val (b2, i2) = passi i2 in
	      (b1 orelse b2, TimeLe (i1, i2))
	  end
	| _ => (false, p)
    fun until_unchanged f a = 
      let fun loop a =
	    let val (changed, a') = f a in
		if changed then loop a'
		else a
	    end in
	  loop a
      end
in
val simp_p = until_unchanged passp
val simp_i = until_unchanged passi
fun simplify (ctx, ps, p) = (ctx, map simp_p ps, simp_p p)
end

fun simp_s s =
  case s of
      Basic b => Basic b
    | Subset (b, name, p) => Subset (b, name, simp_p p)

local
    fun f t =
      case t of
	  VarT _ => t
	| Arrow (t1, d, t2) => Arrow (f t1, simp_i d, f t2)
	| Prod (t1, t2) => Prod (f t1, f t2)
	| Sum (t1, t2) => Sum (f t1, f t2)
	| Unit => Unit
	| AppRecur (name, ns, t, is) => AppRecur (name, map (mapSnd simp_s) ns, f t, map simp_i is)
	| AppVar (x, is) => AppVar (x, map simp_i is)
	| Uni (name, t) => Uni (name, f t)
	| UniI (s, name, t) => UniI (simp_s s, name, f t)
	| ExI (s, name, t) => ExI (simp_s s, name, f t)
	| Int => Int
	| AppDatatype (x, ts, is) => AppDatatype (x, map f ts, map simp_i is)

in
val simp_t = f
end

fun check (ctx as (sctx, kctx, cctx, tctx)) e =
  let 
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = (sctx_names sctx, names kctx, names cctx, names tctx)
  in
      case vcgen ctx e of
	  OK ((t, d), vcs) =>
	  let
	      (* val () = print "Simplifying and applying trivial solver ...\n" *)
	      val vcs = trivial_solver vcs
	      val vcs = map simplify vcs
	      val vcs = trivial_solver vcs
	      val t = simp_t t
	      val d = simp_i d
	  in
	      sprintf
		  "OK: \nExpr: $\nType: $\nTime: $\nVCs: [count=$]\n$\n"
		  [str_e ctxn e,
		   str_t (sctxn, kctxn) t,
		   str_i sctxn d,
		   str_int (length vcs),
		   join "\n" (map str_vc vcs)]
	  end
	| Failed msg => sprintf "Failed: $\nExpr: $\n" [msg, str_e ctxn e]
  end

end
			  
fun curry f a b = f (a, b)
fun uncurry f (a, b) = f a b

structure RecurExamples = struct
open TypeCheck

infix  3 <\     fun x <\ f = fn y => f (x, y)     (* Left section      *)
infix  3 \>     fun f \> y = f y                  (* Left application  *)
infixr 3 />     fun f /> y = fn x => f (x, y)     (* Right section     *)
infixr 3 </     fun x </ f = f x                  (* Right application *)

infix  2 o  
infix  0 :=

infix  1 >|     val op>| = op</      (* Left pipe *)
infixr 1 |<     val op|< = op\>      (* Right pipe *)

infix 7 $
infix 6 %+
infix 6 %*
infix 4 %<=
infix 3 /\
infix 1 -->
infix 1 <->

fun ilist_left l = ExI ((Subset (BSUnit, "_", Eq (Time, T0, shift_i_i l))), "_", Unit)
fun ilist_right ilist t l = ExI ((Subset (Time, "l'", Eq (Time, VarI 0 %+ T1, shift_i_i l))), "l'", Prod (shift_i_t t, ilist [VarI 0]))
fun ilist_core t i = ("ilist", [("l", STime)],
		      Sum (ilist_left (VarI 0),
			   ilist_right (curry AppVar 0) (shift_t_t t) (VarI 0)), i)
fun ilist t i = AppRecur (ilist_core t i)
fun nil_ t = Fold (ilist t [T0], Inl (ilist_right (ilist t) t T0, Pack (ilist_left T0, Type.TT, TT)))
fun cons_ t (n : idx) x xs = Fold (ilist t [n %+ T1], Inr (ilist_left (n %+ T1), Pack (ilist_right (ilist t) t (n %+ T1), n, Pair (x, xs))))
(* val output = check [("n", STime)] [("a", Type)] [] (cons_ (VarT 0) (VarI 0)) *)
fun match_list e t d e1 iname ename e2 = SumCase (Unfold e, "_", Unpack (Var 0, t, d, "_", "_", shiftx_e_e 0 2 e1), "_", Unpack (Var 0, t, d, iname, ename, shiftx_e_e 1 1 e2))
fun map_ a b = AbsI (STime, "m", Abs (Arrow (shift_i_t a, VarI 0, shift_i_t b), "f", Fix (UniI (STime, "n", Arrow (ilist (shiftx_i_t 0 2 a) [VarI 0], (VarI 1 %+ Tconst 2) %* VarI 0, ilist (shiftx_i_t 0 2 b) [VarI 0])), "map", AbsI (STime, "n", Abs (ilist (shiftx_i_t 0 2 a) [VarI 0], "ls", match_list (Var 0) (ilist (shiftx_i_t 0 2 b) [VarI 0]) ((VarI 1 %+ Tconst 2) %* VarI 0) (nil_ (shiftx_i_t 0 2 b)) "n'" "x_xs" (cons_ (shiftx_i_t 0 2 b) (VarI 0) (App (Var 3, Fst (Var 0))) (App (AppI (Var 2, VarI 0), Snd (Var 0)))))))))
fun main () = check (([], []), [("b", Type), ("a", Type)], [], []) (map_ (VarT 1) (VarT 0))
		    (* val output = str_t (["l"], ["ilist"]) (ExI ((Subset (BSUnit, "nouse2", Eq (Time, VarI 1, T0))), "nouse1", Unit)) *)
		    (* val output = str_t (["l"], ["a", "ilist"]) (Sum (ExI ((Subset (BSUnit, "nouse2", Eq (Time, VarI 1, T0))), "nouse1", Unit), *)
		    (* 						 ExI ((Subset (Time, "l'", Eq (Time, VarI 1, VarI 0 %+ T1))), "l'", Prod (shift_t_t (VarT 0), AppVar (0, [VarI 0]))))) *)
		    (* val ilist1 = ilist (VarT 0) [VarI 0] *)
		    (* val output = str_t (["n"], ["a"]) ilist1 *)

		    (* val plus = Abs (Int, "a", Abs (Int, "b", Plus (Var 1, Var 0))) *)
		    (* val output = str_e (([], []), []) plus *)
		    (* val plus1 = Abs (Int, "a", Abs (Int, "b", Plus (Plus (Var 1, Var 0), Var 2))) *)
		    (* val output = str_e (([], []), ["c"]) plus1 *)
		    (* val ttt = Uni ("a", Uni ("b", Prod (Prod (VarT 1, VarT 0), VarT 2))) *)
		    (* val output = str_t ([], ["c"]) ttt *)
		    (* val output = str_t ([], []) (subst_t_t Int ttt) *)

		    (* val bool = Sum (Unit, Unit) *)
		    (* fun cmp_t t n = Arrow (t, T0, Arrow (t, n, bool)) *)
		    (* val msort = AbsT ("a", AbsI (STime, "m", Abs (cmp_t (VarT 0) (VarI 0), "cmp", AbsI (STime, "n", Fix (ilist (VarT 0) [VarI 0], VarI 1 %+ VarI 0, ilist (VarT 0) [VarI 0], "msort", "xs", nil_ (VarT 0)))))) *)
		    (* val empty = (([], []), []) *)
		    (* val output = str_e empty msort *)
		    (* val output = check [] [] [] msort *)

		    (* val plus_5_7 = App (App (plus, Const 5), Const 7) *)
		    (* (* val output = check [] [] [] plus_5_7 *) *)

		    (* val ilist1_core = ilist_core (VarT 0) [VarI 0 %+ T1] *)
		    (* val output = str_t (["n"], ["a"]) (unroll ilist1_core) *)

end

structure DatatypeExamples = struct
open TypeCheck

infix 7 $
infix 6 %+
infix 6 %*
infix 4 %<=
infix 3 /\
infix 1 -->
infix 1 <->

val ilist = KArrowDatatype (1, [STime])
fun NilI family = (family, ["a"], [], Unit, [T0])
fun ConsI family = (family, ["a"], [("n", STime)], Prod (VarT 0, AppDatatype (shiftx_v 0 1 family, [VarT 0], [VarI 0])), [VarI 0 %+ T1])
val ctx : context = (([], []), [("ilist", ilist)], [("ConsI", ConsI 0), ("NilI", NilI 0)], []) 
val NilI_int = AppConstr (1, [Int], [], TT)
val ConsI_int = AppConstr (0, [Int], [T0], Pair (Const 77, NilI_int))
fun main () = check ctx NilI_int
fun main () = check ctx ConsI_int

val map_ = 
    AbsT ("'a",
	  AbsT ("'b",
		AbsI (STime, "m", 
		      Abs (Arrow (VarT 1, VarI 0, VarT 0), "f", 
			   Fix (UniI (STime, "n", Arrow (AppDatatype (2, [VarT 1], [VarI 0]), (VarI 1 %+ Tconst 2) %* VarI 0, AppDatatype (2, [VarT 0], [VarI 0]))), "map", 
				AbsI (STime, "n", 
				      Abs (AppDatatype (2, [VarT 1], [VarI 0]), "ls", 
					   Case (Var 0, AppDatatype (2, [VarT 0], [VarI 0]), (VarI 1 %+ Tconst 2) %* VarI 0, 
						 [(Constr (1, [], "_"), AppConstr (1, [VarT 0], [], TT)),
						  (Constr (0, ["n'"], "x_xs"), AppConstr (0, [VarT 0], [VarI 0], Pair (App (Var 3, Fst (Var 0)), App (AppI (Var 2, VarI 0), Snd (Var 0)))))]))))))))

val wrong = AppConstr (1, [Int], [T0], Pair (Const 77, NilI_int))

fun main () =
  check ctx wrong ^ "\n" ^
  check ctx map_

end

structure NamedDatatypeExamples = struct

structure T = MakeType (structure Var = StringVar)
structure E = MakeExpr (structure Var = StringVar structure Type = T)
open T
open E

infix 7 $
infix 6 %+
infix 6 %*
infix 4 %<=
infix 3 /\
infix 1 -->
infix 1 <->

fun NilI family = (family, ["a"], [], Unit, [T0])
fun ConsI family = (family, ["a"], [("n", STime)], Prod (VarT "a", AppDatatype (family, [VarT "a"], [VarI "n"])), [VarI "n" %+ T1])
val NilI_int = AppConstr ("NilI", [Int], [], TT)
val ConsI_int = AppConstr ("ConsI", [Int], [T0], Pair (Const 77, NilI_int))

val map_ = 
    AbsT ("'a",
	  AbsT ("'b",
		AbsI (STime, "m", 
		      Abs (Arrow (VarT "a", VarI "m", VarT "b"), "f", 
			   Fix (UniI (STime, "n", Arrow (AppDatatype ("ilist", [VarT "a"], [VarI "n"]), (VarI "m" %+ Tconst 2) %* VarI "n", AppDatatype ("ilist", [VarT "b"], [VarI "n"]))), "map", 
				AbsI (STime, "n", 
				      Abs (AppDatatype ("ilist", [VarT "a"], [VarI "n"]), "ls", 
					   Case (Var "ls", AppDatatype ("ilist", [VarT "b"], [VarI "n"]), (VarI "m" %+ Tconst 2) %* VarI "n", 
						 [(Constr ("NilI", [], "_"), AppConstr ("NilI", [VarT "b"], [], TT)),
						  (Constr ("ConsI", ["n'"], "x_xs"), AppConstr ("ConsI", [VarT "b"], [VarI "n'"], Pair (App (Var "f", Fst (Var "x_xs")), App (AppI (Var "map", VarI "n'"), Snd (Var "x_xs")))))]))))))))

val wrong = AppConstr ("NilI", [Int], [T0], Pair (Const 77, NilI_int))

structure Type = MakeType (structure Var = IntVar)
structure Expr = MakeExpr (structure Var = IntVar structure Type = Type)
open Type
open Expr

open NameResolve
open TypeCheck

exception Resolve of string

(* fun main () = check ctx NilI_int *)
(* fun main () = check ctx ConsI_int *)
fun main () =
    let
	val ctxn = ([], ["ilist"], ["ConsI", "NilI"], [])
	val map_ = case resolve_expr ctxn map_ of OK v => v 
						| Failed msg => raise Resolve msg
	val ilist = KArrowDatatype (1, [STime])
	val ctx : context = (([], []), [("ilist", ilist)], [("ConsI", ConsI "ilist"), ("NilI", NilI "ilist")], [])
    in
	check ctx wrong ^ "\n" ^
	check ctx map_
    end

end

fun main () = 
  let
      val output = ""
      (* val output = RecurExamples.main () *)
      val output = DatatypeExamples.main ()
  in			 
      print (output ^ "\n")
  end

val _ = main ()
