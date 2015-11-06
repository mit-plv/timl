structure SMT2Printer = struct
open Util
open VC

infixr 0 $

val prelude = [
    (* "(set-option :produce-proofs true)", *)
    "(declare-fun log2 (Real) Real)",
    (* "(assert (forall ((x Real) (y Real))", *)
    (* "  (! (=> (and (< 0 x) (< 0 y)) (= (log2 ( * x y)) (+ (log2 x) (log2 y))))", *)
    (* "    :pattern ((log2 ( * x y))))))", *)
    (* "(assert (forall ((x Real) (y Real))", *)
    (* "  (! (=> (and (< 0 x) (< 0 y)) (= (log2 (/ x y)) (- (log2 x) (log2 y))))", *)
    (* "    :pattern ((log2 (/ x y))))))", *)
    (* "(assert (= (log2 1) 0))", *)
    (* "(assert (= (log2 2) 1))", *)
    (* "(assert (forall ((x Real) (y Real)) (=> (and (< 0 x) (< 0 y)) (=> (< x y) (< (log2 x) (log2 y))))))", *)
    "(declare-datatypes () ((Unit TT)))",
    ""
]

val push = [
    "(push)"
]

val pop = [
    "(pop)"
]

val check = [
    "(check-sat)",
    (* "(get-proof)", *)
    (* "(get-value (n))", *)
    "(get-model)"
]

datatype escaped = Escaped of string
fun escape s = Escaped s
fun print_escaped (Escaped s) = String.map (fn c => if c = #"'" then #"!" else c) s

fun declare_const x sort = [
    sprintf "(declare-const $ $)" [print_escaped x, sort]
]

fun assert s = [
    sprintf "(assert $)" [s]
]

fun print_i ctx i =
  case i of
      VarI (n, _) =>
      ((print_escaped o fst o List.nth) (ctx, n) handle Subscript => "unbound_" ^ str_int n)
    | ConstIN (n, _) => str_int n
    | ConstIT (x, _) => x
    | UnOpI (ToReal, i, _) => sprintf "(to_real $)" [print_i ctx i]
    | UnOpI (Log2, i, _) => sprintf "(log2 $)" [print_i ctx i]
    | BinOpI (AddI, i1, i2) => sprintf "(+ $ $)" [print_i ctx i1, print_i ctx i2]
    | BinOpI (MinusI, i1, i2) =>
      let fun proper_sub a b =
            sprintf "(ite (>= $ $) (- $ $) 0)" [a, b, a, b]
      in
          proper_sub (print_i ctx i1) (print_i ctx i2)
      end
    | BinOpI (MultI, i1, i2) => sprintf "($ $ $)" ["*", print_i ctx i1, print_i ctx i2]
    | BinOpI (MaxI, i1, i2) =>
      let fun max a b =
            sprintf "(ite (>= $ $) $ $)" [a, b, a, b]
      in
          max (print_i ctx i1) (print_i ctx i2)
      end
    | BinOpI (MinI, i1, i2) =>
      let fun min a b =
            sprintf "(ite (<= $ $) $ $)" [a, b, a, b]
      in
          min (print_i ctx i1) (print_i ctx i2)
      end
    | TrueI _ => "true"
    | FalseI _ => "false"
    | TTI _ => "TT"
    | UVarI _ => "?"

fun print_p ctx p =
  let
      fun str_conn opr =
        case opr of
            And => "and"
          | Or => "or"
          | Imply => "=>"
          | Iff => "="
      fun str_pred opr =
        case opr of
            EqP => "="
          | LeP => "<="
          | GtP => ">"
      fun f p =
        case p of
            True _ => "true"
          | False _ => "false"
          | Not (p, _) => sprintf "(not $)" [f p]
          | BinConn (opr, p1, p2) => sprintf "($ $ $)" [str_conn opr, f p1, f p2]
          | BinPred (opr, i1, i2) => sprintf "($ $ $)" [str_pred opr, print_i ctx i1, print_i ctx i2]
  in
      f p
  end

fun assert_p ctx p =
  assert (print_p ctx p)

fun print_bind (name, bsort) =
  case bsort of
      Base BSUnit =>
      declare_const name "Unit"
    | Base Bool =>
      declare_const name "Bool"
    | Base Time =>
      declare_const name "Real" @
      assert (sprintf "(<= 0 $)" [print_escaped name])
    | Base Nat =>
      declare_const name "Int" @
      assert (sprintf "(<= 0 $)" [print_escaped name])
    | UVarBS _ => ["?"]

fun print_vc ((ctx, ps, goal, _) : vc) =
  let
      val ctx = map (mapFst escape) ctx
      val lines = push
      val lines = lines @ concatMap print_bind ctx
      val lines = lines @ concatMap (assert_p ctx) ps
      val lines = lines @ assert_p ctx (Not (goal, dummy))
      val lines = lines @ check
      val lines = lines @ pop
      val lines = lines @ [""]
  in
      lines
  end

fun to_smt2 vcs = 
  let
      val lines =
	  concatMap print_vc vcs
      val lines = prelude @ lines
      val s = join_lines lines
  in
      s
  end

end
