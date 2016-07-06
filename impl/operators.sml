structure Operators = struct

datatype idx_un_op =
         ToReal
         | Log2
         | Ceil
         | Floor
         | B2n
         | Neg
               
datatype idx_bin_op =
	 AddI
	 | MultI
         (* | DivI *)
	 | MaxI
	 | MinI
         | TimeApp (* TF: Time Function *)
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
               
datatype bin_op =
         Add
         | New
         | Read

datatype tri_op =
         Write

(* existential quantifier might carry other information such as a unification variable to update when this existential quantifier gets instantiated *)
datatype 'a quan =
         Forall
         | Exists of 'a

fun str_idx_un_op opr =
  case opr of
      ToReal => "$"
    | Log2 => "log2"
    | Ceil => "ceil"
    | Floor => "floor"
    | B2n => "b2n"
    | Neg => "not"

fun str_idx_bin_op opr =
  case opr of
      AddI => "+"
    | MultI => "*"
    | MaxI => "max"
    | MinI => "min"
    | TimeApp => ""
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

fun str_bin_op opr =
  case opr of
      Add => "+"
    | New => "new"
    | Read => "read"

fun str_quan q =
    case q of
        Forall => "forall"
      | Exists _ => "exists"

end
