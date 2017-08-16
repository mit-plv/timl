structure Operators = struct

open Util

datatype idx_const =
         ICBool of bool
	 | ICTT
         | ICAdmit
         | ICNat of int
         | ICTime of TimeType.time


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

type nat = int

datatype expr_const =
         ECTT
         | ECNat of nat
         | ECInt of int

datatype expr_un_op =
         EUFst
         | EUSnd

datatype bin_op =
         EBApp
         | EBPair
         | EBAdd
         | EBNew
         | EBRead

datatype tri_op =
         Write

datatype expr_EI =
         EEIAppI
         | EEIAscTime

datatype expr_ET =
         EETAppT
         | EETAsc

datatype expr_T =
         ETNever
         | ETBuiltin
             
fun str_idx_const c =
  case c of
      ICBool b => str_bool b
    | ICTT => "()"
    | ICAdmit => "admit"
    | ICNat n => str_int n
    | ICTime x => TimeType.str_time x

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
    | MultI => " *"
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

fun strip_quan q =
  case q of
      Forall => Forall
    | Exists _ => Exists ()
                         
fun str_quan q =
    case q of
        Forall => "forall"
      | Exists _ => "exists"

fun str_bin_op opr =
  case opr of
      EBApp => "$"
    | EBPair => "pair"
    | EBAdd => "+"
    | EBNew => "new"
    | EBRead => "read"

fun str_expr_EI opr =
  case opr of
      EEIAppI => "EEIAppI"
    | EEIAscTime => "EEIAscTime"

fun str_expr_ET opr =
  case opr of
      EETAppT => "EETAppT"
    | EETAsc => "EETAsc"

fun str_expr_T opr =
  case opr of
      ETNever => "ETNever"
    | ETBuiltin => "ETBuiltin"
                  
fun str_expr_const c =
  case c of
      ECTT => "()"
    | ECInt n => str_int n
    | ECNat n => sprintf "#$" [str_int n]
                                
fun str_expr_un_op opr = 
  case opr of
      EUFst => "fst"
    | EUSnd => "snd"

fun str_expr_bin_op opr =
  case opr of
      EBApp => "app"
    | EBPair => "pair"
    | EBNew => "new"
    | EBRead => "read"
    | EBAdd => "add"

end
