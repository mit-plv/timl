structure SMT2Printer = struct
open Util
open VC
open NoUVarExpr

infixr 0 $

infix 1 -->

fun escape s = String.map (fn c => if c = #"'" then #"!" else c) s
fun evar_name n = "!!" ^ str_int n

fun print_i ctx i =
  case i of
      VarI (n, _) =>
      (List.nth (ctx, n) handle Subscript => "unbound_" ^ str_int n)
    | ConstIN (n, _) => str_int n
    | ConstIT (x, _) => x
    | DivI (i1, (n2, _)) => sprintf "(/ $ $)" [print_i ctx i1, str_int n2]
    | ExpI (i1, (n2, _)) => sprintf "(^ $ $)" [print_i ctx i1, n2]
    | UnOpI (opr, i, _) => 
      (case opr of
           ToReal => sprintf "(to_real $)" [print_i ctx i]
         | Log2 => sprintf "(log2 $)" [print_i ctx i]
         | Ceil => sprintf "(ceil $)" [print_i ctx i]
         | Floor => sprintf "(floor $)" [print_i ctx i]
      )
    | BinOpI (opr, i1, i2) => 
      (case opr of
           AddI => sprintf "(+ $ $)" [print_i ctx i1, print_i ctx i2]
         | MultI => 
           sprintf "($ $ $)" ["*", print_i ctx i1, print_i ctx i2]
         | MaxI =>
           let fun max a b =
                   sprintf "(ite (>= $ $) $ $)" [a, b, a, b]
           in
               max (print_i ctx i1) (print_i ctx i2)
           end
         | MinI =>
           let fun min a b =
                   sprintf "(ite (<= $ $) $ $)" [a, b, a, b]
           in
               min (print_i ctx i1) (print_i ctx i2)
           end
         | App1 =>
           sprintf "(app1 $ $)" [print_i ctx i1, print_i ctx i2]
      )
    | TrueI _ => "true"
    | FalseI _ => "false"
    | TTI _ => "TT"
    | Abs1 ((name, _), i, _) => "fn"
    | UVarI (u, _) => exfalso u

fun negate s = sprintf "(not $)" [s]

fun print_base_sort b =
  case b of
      BSUnit => "Unit"
    | Bool => "Bool"
    | Time => "Real"
    | Nat => "Int"
    | Fun1 => "Fun1"

fun print_bsort bsort =
  case bsort of
      Base b => print_base_sort b
    | UVarBS u => exfalso u

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
          | BigO => ""
      fun f p =
        case p of
            True _ => "true"
          | False _ => "false"
          | Not (p, _) => negate (f p)
          | BinConn (opr, p1, p2) => sprintf "($ $ $)" [str_conn opr, f p1, f p2]
          | BinPred (BigO, i1, i2) => sprintf "(bigO $ $)" [print_i ctx i1, print_i ctx i2]
          | BinPred (opr, i1, i2) => sprintf "($ $ $)" [str_pred opr, print_i ctx i1, print_i ctx i2]
          | Quan (q, bs, (name, _), p) => sprintf "($ (($ $)) $)" [str_quan q, name, print_bsort bs, print_p (name :: ctx) p]
  in
      f p
  end

fun declare_const x sort = 
    sprintf "(declare-const $ $)" [x, sort]

fun assert s = 
    sprintf "(assert $)" [s]

fun assert_p ctx p =
  assert (print_p ctx p)

fun print_hyp ctx h =
    case h of
        VarH (name, bsort) =>
        (declare_const name (print_base_sort bsort), name :: ctx)
      | PropH p =>
        (assert (print_p ctx p), ctx)

val prelude = [
    (* "(set-option :produce-proofs true)", *)
    "(declare-datatypes () ((Unit TT)))",
    "(declare-datatypes () ((Fun1 fn)))",
    "(declare-fun log2 (Real) Real)",
    "(declare-fun bigO (Fun1 Fun1) Bool)",
    "(declare-fun app1 (Fun1 Int) Real)",
    "(define-fun floor ((x Real)) Int",
    "(to_int x))",
    "(define-fun ceil ((x Real)) Int",
    "(to_int (+ x 0.5)))",
    (* "(assert (forall ((x Real) (y Real))", *)
    (* "  (! (=> (and (< 0 x) (< 0 y)) (= (log2 ( * x y)) (+ (log2 x) (log2 y))))", *)
    (* "    :pattern ((log2 ( * x y))))))", *)
    (* "(assert (forall ((x Real) (y Real))", *)
    (* "  (! (=> (and (< 0 x) (< 0 y)) (= (log2 (/ x y)) (- (log2 x) (log2 y))))", *)
    (* "    :pattern ((log2 (/ x y))))))", *)
    (* "(assert (= (log2 1) 0))", *)
    (* "(assert (= (log2 2) 1))", *)
    (* "(assert (forall ((x Real) (y Real)) (=> (and (< 0 x) (< 0 y)) (=> (< x y) (< (log2 x) (log2 y))))))", *)
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

(* convert to Z3's types and naming conventions *)
fun conv_base_sort b =
      case b of
          BSUnit => (BSUnit, NONE)
        | Bool => (Bool, NONE)
        | Time => (Time, SOME (BinPred (LeP, ConstIT ("0.0", dummy), VarI (0, dummy))))
        | Nat => (Nat, SOME (BinPred (LeP, ConstIN (0, dummy), VarI (0, dummy))))
        | Fun1 => (Fun1, NONE)

fun conv_bsort bsort =
  case bsort of
      UVarBS u => exfalso u
    | Base b => let val (b, p) = conv_base_sort b in (Base b, p) end

fun conv_p p =
    case p of
        Quan (q, bs, (name, r), p) => 
        let 
            val (bs, p1) = conv_bsort bs
            val p = conv_p p
            val p = case p1 of
                        NONE => p
                      | SOME p1 => (p1 --> p)
        in
            Quan (q, bs, (escape name, r), p)
        end
      | Not (p, r) => Not (conv_p p, r)
      | BinConn (opr, p1, p2) => BinConn (opr, conv_p p1, conv_p p2)
      | BinPred _ => p
      | True _ => p
      | False _ => p

fun conv_hyp h =
    case h of
        PropH _ => [h]
      | VarH (name, bs) =>
        let
            val (bs, p) = conv_base_sort bs
            val hs = [VarH (escape name, bs)]
            val hs = hs @ (case p of SOME p => [PropH p] | _ => [])
        in
            hs
        end

fun print_vc ((hyps, goal) : vc) =
  let
      val hyps = rev hyps
      val hyps = concatMap conv_hyp hyps
      val goal = conv_p goal
      val lines = push
      val (hyps, ctx) = foldl (fn (h, (hs, ctx)) => let val (h, ctx) = print_hyp ctx h in (h :: hs, ctx) end) ([], []) hyps
      val hyps = rev hyps
      val lines = lines @ hyps
      val lines = lines @ [assert (negate (print_p ctx goal))]
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
