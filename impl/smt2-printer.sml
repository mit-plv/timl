structure SMT2Printer = struct
open Util
open VC
open NoUVarExpr

infixr 0 $

fun escape s = String.map (fn c => if c = #"'" then #"!" else c) s
fun evar_name n = "!!" ^ str_int n

fun print_i ctx i =
  case i of
      VarI (n, _) =>
      (List.nth (ctx, n) handle Subscript => "unbound_" ^ str_int n)
    | ConstIN (n, _) => str_int n
    | ConstIT (x, _) => x
    | UnOpI (opr, i, _) => 
      (case opr of
           ToReal => sprintf "(to_real $)" [print_i ctx i]
         | Log2 => sprintf "(log2 $)" [print_i ctx i]
      )
    | BinOpI (opr, i1, i2) => 
      (case opr of
           AddI => sprintf "(+ $ $)" [print_i ctx i1, print_i ctx i2]
         | MinusI =>
           let fun proper_sub a b =
                   sprintf "(ite (>= $ $) (- $ $) 0)" [a, b, a, b]
           in
               proper_sub (print_i ctx i1) (print_i ctx i2)
           end
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
         | BigO =>
           sprintf "($ $ $)" ["bigO", print_i ctx i1, print_i ctx i2]
      )
    | TrueI _ => "true"
    | FalseI _ => "false"
    | TTI _ => "TT"
    | UVarI (u, _) => evar_name u

fun negate s = sprintf "(not $)" [s]

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
          | Not (p, _) => negate (f p)
          | BinConn (opr, p1, p2) => sprintf "($ $ $)" [str_conn opr, f p1, f p2]
          | BinPred (opr, i1, i2) => sprintf "($ $ $)" [str_pred opr, print_i ctx i1, print_i ctx i2]
  in
      f p
  end

fun print_base_sort b =
  case b of
      BSUnit => "Unit"
    | Bool => "Bool"
    | Time => "Real"
    | Nat => "Int"
    | Profile => "Profile"

fun print_bsort bsort =
  case bsort of
      Base b => print_base_sort b
    | UVarBS u => exfalso u

fun print_f ctx f =
    case f of
        PropF (p, _) => print_p ctx p
      | ImplyF (p, fs) => sprintf "(=> $ $)" [print_p ctx p, print_fs ctx fs]
      | ForallF (name, bs, fs) => sprintf "(forall (($ $)) $)" [name, print_base_sort bs, print_fs (name :: ctx) fs]
      | ExistsF (name, bs, fs) => sprintf "(exists (($ $)) $)" [evar_name name, print_base_sort bs, print_fs ctx fs]

and print_fs ctx fs =
    case map (print_f ctx) fs of
        [] => "true"
      | f :: fs => foldl (fn (f, acc) => sprintf "(and $ $)" [acc, f]) f fs

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
    "(declare-datatypes () ((Profile Profile1)))",
    "(declare-fun log2 (Real) Real)",
    "(declare-fun bigO (Profile Real) Real)",
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

fun conv_base_sort b =
      case b of
          BSUnit => (BSUnit, NONE)
        | Bool => (Bool, NONE)
        | Time => (Time, SOME (BinPred (LeP, ConstIT ("0.0", dummy), VarI (0, dummy))))
        | Nat => (Nat, SOME (BinPred (LeP, ConstIN (0, dummy), VarI (0, dummy))))
        | Profile => (Profile, NONE)

fun conv_bs bsort =
  case bsort of
      UVarBS u => exfalso u
    | Base b => conv_base_sort b

fun conv_f f =
    let
        fun conv_quan (bs, fs) =
            let
                val (bs, p) = conv_base_sort bs
                val fs = map conv_f fs
                val fs = case p of
                             NONE => fs
                           | SOME p => [ImplyF (p, fs)] 
            in 
                (bs, fs)
            end
    in
        case f of
            PropF _ => f
          | ImplyF (p, fs) => ImplyF (p, map conv_f fs)
          | ForallF (name, bs, fs) => 
            let 
                val (bs, fs) = conv_quan (bs, fs)
            in
                ForallF (escape name, bs, fs)
            end
          | ExistsF (name, bs, fs) => 
            let 
                val (bs, fs) = conv_quan (bs, fs)
            in
                ExistsF (name, bs, fs)
            end
    end

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
      val goal = conv_f goal
      val lines = push
      val (hyps, ctx) = foldl (fn (h, (hs, ctx)) => let val (h, ctx) = print_hyp ctx h in (h :: hs, ctx) end) ([], []) hyps
      val hyps = rev hyps
      val lines = lines @ hyps
      val lines = lines @ [assert (negate (print_f ctx goal))]
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
