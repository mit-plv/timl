structure SMT2Printer = struct
open Util
open VC
open Type

infixr 0 $

val prelude = [
    "(define-fun max ((x Int) (y Int)) Int",
    "  (ite (< x y) y x))",
    "(define-fun mymin ((x Int) (y Int)) Int",
    "  (ite (> x y) y x))",
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
    "(check-sat)"
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
      | T0 _ => "0"
      | T1 _ => "1"
      | Tconst (n, _) => str_int n
      | TrueI _ => "true"
      | FalseI _ => "false"
      | TTI _ => "TT"
      | Tadd (i1, i2) => sprintf "(+ $ $)" [print_i ctx i1, print_i ctx i2]
      | Tmult (i1, i2) => sprintf "($ $ $)" ["*", print_i ctx i1, print_i ctx i2]
      | Tmax (i1, i2) => sprintf "(max $ $)" [print_i ctx i1, print_i ctx i2]
      | Tmin (i1, i2) => sprintf "(mymin $ $)" [print_i ctx i1, print_i ctx i2]

fun print_p ctx p =
    let 
        fun f p =
            case p of
                True _ => "true"
              | False _ => "false"
              | Not (p, _) => sprintf "(not $)" [f p]
              | And (p1, p2) => sprintf "(and $ $)" [f p1, f p2]
              | Or (p1, p2) => sprintf "(or $ $)" [f p1, f p2]
              | Imply (p1, p2) => sprintf "(=> $ $)" [f p1, f p2]
              | Iff (p1, p2) => sprintf "(= $ $)" [f p1, f p2]
              | Eq (i1, i2) => sprintf "(= $ $)" [print_i ctx i1, print_i ctx i2]
              | TimeLe (i1, i2) => sprintf "(<= $ $)" [print_i ctx i1, print_i ctx i2]
    in
        f p
    end

fun assert_p ctx p =
    assert (print_p ctx p)

fun print_bind (name, bsort) =
    case bsort of
        BSUnit => declare_const name "Unit"
      | Bool => declare_const name "Bool"
      | Time => declare_const name "Int" @
                assert (sprintf "(<= 0 $)" [print_escaped name])

fun print_vc ((ctx, ps, goal, _) : vc) =
    let
        val ctx = uniquefy ctx
        val ctx = map (mapFst escape) ctx
        val lines = push
        val lines = lines @ concatMap print_bind ctx
        val lines = lines @ concatMap (assert_p ctx) ps
        val lines = lines @ assert_p ctx (Not (goal, dummy))
        val lines = lines @ check
        val lines = lines @ pop
    in
        lines
    end

fun to_smt vcs = 
    let
        val lines =
	    concatMap print_vc vcs
        val lines = prelude @ lines
        val s = join_lines lines
    in
        s
    end

end
