structure Operators = struct
open Util

datatype idx_const =
         ICBool of bool
	 | ICTT
         | ICAdmit
         | ICNat of int
         | ICTime of string


datatype idx_un_op =
         ToReal
         | Log2
         | Ceil
         | Floor
         | B2n
         | Neg
         | IUDiv of int
         | IUExp of string
               
datatype idx_bin_op =
	 AddI
	 | MultI
	 | MaxI
	 | MinI
         | IApp 
         | EqI
         | AndI
         | ExpNI
         | LtI
         | GeI
         | BoundedMinusI

(* binary logical connectives *)
datatype bin_conn =
	 And
	 | Or
	 | Imply
	 | Iff

(* binary predicates on indices *)
datatype bin_pred =
         EqP
         | LeP
         | LtP
         | GeP
         | GtP
         | BigO
               
(* existential quantifier might carry other information such as a unification variable to update when this existential quantifier gets instantiated *)
datatype 'a quan =
         Forall
         | Exists of 'a

datatype expr_const =
         ECTT
         | ECNat of int
         | ECInt of int

datatype expr_un_op =
         EUFst
         | EUSnd

datatype bin_op =
         EBApp
         | EBPair
         | Add
         | New
         | Read

datatype tri_op =
         Write

datatype expr_EI =
         EEIAppI
         | EEIAscriptionTime

datatype expr_T =
         ETNever
         | ETBuiltin
             
fun str_idx_const c =
  case c of
      ICBool b => str_bool b
    | ICTT => "()"
    | ICAdmit => "admit"
    | ICNat n => str_int n
    | ICTime s => s

fun str_idx_un_op opr =
  case opr of
      ToReal => "$"
    | Log2 => "log2"
    | Ceil => "ceil"
    | Floor => "floor"
    | B2n => "b2n"
    | Neg => "not"
    | IUDiv d => sprintf "(/ $)" [str_int d]
    | IUExp s => sprintf "(^ $)" [s]

fun str_idx_bin_op opr =
  case opr of
      AddI => "+"
    | MultI => "*"
    | MaxI => "max"
    | MinI => "min"
    | IApp => ""
    | EqI => "=="
    | AndI => "&&"
    | ExpNI => "^"
    | LtI => "<"
    | GeI => ">="
    | BoundedMinusI => "-"

fun str_bin_conn opr =
  case opr of
      And => "/\\"
    | Or => "\\/"
    | Imply => "->"
    | Iff => "<->"

fun str_bin_pred opr =
  case opr of
      EqP => "="
    | LeP => "<="
    | LtP => "<"
    | GeP => ">="
    | GtP => ">"
    | BigO => "<=="

fun str_quan q =
    case q of
        Forall => "forall"
      | Exists _ => "exists"

fun str_bin_op opr =
  case opr of
      EBApp => "$"
    | EBPair => "pair"
    | Add => "+"
    | New => "new"
    | Read => "read"

end
