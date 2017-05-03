structure SMT2Printer = struct
open Util
open Expr
open UVar
open Normalize
open VC

infixr 0 $

infixr 1 -->

exception SMTError of string

fun escape s = if s = "_" then "__!escaped_from_underscore_for_smt" else String.map (fn c => if c = #"'" then #"!" else c) s
fun evar_name n = "!!" ^ str_int n

fun print_idx_bin_op opr =
    case opr of
        AddI => "+"
      | BoundedMinusI => "-"
      | MultI => "*"
      | EqI => "="
      | AndI => "and"
      | ExpNI => "exp_i_i"
      | LtI => "<"
      | GeI => ">="
      | MaxI => raise Impossible "print_idx_bin_op ()"
      | MinI => raise Impossible "print_idx_bin_op ()"
      | TimeApp => raise Impossible "print_idx_bin_op ()"
        
fun print_i ctx i =
  case i of
      VarI (_, (n, _)) =>
      (List.nth (ctx, n) handle Subscript => raise SMTError $ "Unbound variable " ^ str_int n)
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
         | B2n => sprintf "(b2i $)" [print_i ctx i]
         | Neg => sprintf "(not $)" [print_i ctx i]
      )
    | BinOpI (opr, i1, i2) => 
      (case opr of
           MaxI =>
           let
               fun max a b =
                   sprintf "(ite (>= $ $) $ $)" [a, b, a, b]
           in
               max (print_i ctx i1) (print_i ctx i2)
           end
         | MinI =>
           let
               fun min a b =
                   sprintf "(ite (<= $ $) $ $)" [a, b, a, b]
           in
               min (print_i ctx i1) (print_i ctx i2)
           end
         | BoundedMinusI =>
           let
             fun bounded_minus a b =
                 sprintf "(ite (< $ $) 0 (- $ $))" [a, b, a, b]
           in
             bounded_minus (print_i ctx i1) (print_i ctx i2)
           end
         | IApp =>
           let
               val is = collect_IApp i1 @ [i2]
           in
               (* sprintf "(app_$$)" [str_int (length is - 1), join_prefix " " $ map (print_i ctx) is] *)
               sprintf "($)" [join " " $ map (print_i ctx) is]
           end
         (* | ExpNI => sprintf "($ $)" [print_idx_bin_op opr, print_i ctx i2] *)
         | _ => 
           sprintf "($ $ $)" [print_idx_bin_op opr, print_i ctx i1, print_i ctx i2]
      )
    | Ite (i1, i2, i3, _) => sprintf "(ite $ $ $)" [print_i ctx i1, print_i ctx i2, print_i ctx i3]
    | TrueI _ => "true"
    | FalseI _ => "false"
    | TTI _ => "TT"
    | IAbs _ => raise SMTError "can't handle abstraction"
    | AdmitI _ => "TT"
    | UVarI (x, _) =>
      case !x of
          Refined i => print_i ctx i
        | Fresh _ => raise SMTError "index contains uvar"

fun negate s = sprintf "(not $)" [s]

fun print_base_sort b =
  case b of
      UnitSort => "Unit"
    | BoolSort => "Bool"
    | Nat => "Int"
    | Time => "Real"

fun print_bsort bsort =
  case bsort of
      Base b => print_base_sort b
    | BSArrow _ => raise SMTError "can't handle higher-order sorts"
    | UVarBS x =>
      case !x of
          Refined b => print_bsort b
        | Fresh _ => raise SMTError "bsort contains uvar"

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
          | LtP => "<"
          | GeP => ">="
          | GtP => ">"
          | BigO => raise SMTError "can't handle big-O"
      fun f p =
        case p of
            True _ => "true"
          | False _ => "false"
          | Not (p, _) => negate (f p)
          | BinConn (opr, p1, p2) => sprintf "($ $ $)" [str_conn opr, f p1, f p2]
          (* | BinPred (BigO, i1, i2) => sprintf "(bigO $ $)" [print_i ctx i1, print_i ctx i2] *)
          (* | BinPred (BigO, i1, i2) => "true" *)
          | BinPred (opr, i1, i2) => sprintf "($ $ $)" [str_pred opr, print_i ctx i1, print_i ctx i2]
          | Quan (Exists _, bs, Bind ((name, _), p), _) => raise SMTError "Don't trust SMT solver to solve existentials"
          | Quan (q, bs, Bind ((name, _), p), _) => sprintf "($ (($ $)) $)" [str_quan q, name, print_bsort bs, print_p (name :: ctx) p]
  in
      f p
  end

fun declare_const x sort = 
    (* sprintf "(declare-const $ $)" [x, sort] *)
    sprintf "(declare-fun $ () $)" [x, sort]

fun assert s = 
    sprintf "(assert $)" [s] 

fun assert_p ctx p =
  assert (print_p ctx p)

fun print_hyp ctx h =
    case h of
        VarH (name, bs) =>
        (case update_bs bs of
             Base b =>
             (declare_const name (print_base_sort b), name :: ctx)
           | BSArrow _ =>
             let
               val (args, ret) = collect_BSArrow bs
             in
               (sprintf "(declare-fun $ ($) $)" [name, join " " $ map print_bsort args, print_bsort ret], name :: ctx)
             end
           | UVarBS x => raise SMTError "hypothesis contains uvar"
        )
      | PropH p =>
        let
          val p = print_p ctx p
                  handle SMTError _ => "" (* always sound to discard hypothesis *)
        in
          (assert p, ctx)
        end

fun prelude get_ce = [
    (* "(set-logic ALL_SUPPORTED)", *)
    if get_ce then "(set-option :produce-models true)" else "",
    (* "(set-option :produce-proofs true)", *)

    (* "(declare-datatypes () ((Unit TT)))", *)

    "(declare-fun exp_i_i (Int Int) Int)",
    (* "(declare-fun exp_i_i (Int) Int)", *)
    
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
    
    "(define-fun floor ((x Real)) Int",
    "(to_int x))",
    "(define-fun ceil ((x Real)) Int",
    "(to_int (+ x 0.5)))",
    "(define-fun b2i ((b Bool)) Int",
    "(ite b 1 0))",

    
    (* "(declare-datatypes () ((Fun_1 fn1)))", *)
    (* "(declare-datatypes () ((Fun_2 fn2)))", *)
    (* "(declare-fun app_1 (Fun_1 Int) Real)", *)
    (* "(declare-fun app_2 (Fun_2 Int Int) Real)", *)
    (* "(declare-fun bigO (Fun_2 Fun_2) Bool)", *)
    
    ""
]

val push = [
    "(push 1)"
]

val pop = [
    "(pop 1)"
]

fun check get_ce = [
    "(check-sat)",
    if get_ce then "(get-model)" else ""
    (* "(get-proof)" *)
    (* "(get-value (n))", *)
]

(* convert to Z3's types and naming conventions *)
fun conv_base_sort b =
      case b of
          UnitSort => (UnitSort, NONE)
        | BoolSort => (BoolSort, NONE)
        | Nat => (Nat, SOME (BinPred (LeP, ConstIN (0, dummy), VarI (NONE, (0, dummy)))))
        | Time => (Time, SOME (BinPred (LeP, ConstIT ("0.0", dummy), VarI (NONE, (0, dummy)))))

fun conv_bsort bsort =
  case bsort of
      Base b =>
      let
        val (b, p) = conv_base_sort b
      in
        (Base b, p)
      end
    | BSArrow _ => (bsort, NONE)
    | UVarBS x =>
      case !x of
          Refined b => conv_bsort b
        | Fresh _ => raise SMTError "bsort contains uvar"

fun conv_p p =
    case p of
        Quan (q, bs, Bind ((name, r), p), r_all) => 
        let 
            val (bs, p1) = conv_bsort bs
            val p = conv_p p
            val p = case p1 of
                        NONE => p
                      | SOME p1 => (p1 --> p)
        in
            Quan (q, bs, Bind ((escape name, r), p), r_all)
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
            val (bs, p) = conv_bsort bs
            val hs = [VarH (escape name, bs)]
            val hs = hs @ (case p of SOME p => [PropH p] | _ => [])
        in
            hs
        end

fun print_vc get_ce ((hyps, goal) : vc) =
  let
      val hyps = rev hyps
      val hyps = concatMap conv_hyp hyps
      val goal = conv_p goal
      val lines = push
      val (hyps, ctx) = foldl (fn (h, (hs, ctx)) => let val (h, ctx) = print_hyp ctx h in (h :: hs, ctx) end) ([], []) hyps
      val hyps = rev hyps
      val lines = lines @ hyps
      val lines = lines @ [assert (negate (print_p ctx goal))]
      val lines = lines @ check get_ce
      val lines = lines @ pop
      val lines = lines @ [""]
  in
      lines
  end

fun to_smt2 get_ce vcs = 
  let
      val lines =
	  concatMap (print_vc get_ce) vcs
      val lines = prelude get_ce @ lines
      val s = join_lines lines
  in
      s
  end

end

(* open CheckNoUVar *)
(* val vcs = map no_uvar_vc vcs *)
(*           handle NoUVarError _ => raise SMTError "VC contains uvar" *)
                          
