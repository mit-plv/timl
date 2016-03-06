structure Operators = struct

datatype idx_un_op =
         ToReal
         | Log2
         | Ceil
         | Floor
               
datatype idx_bin_op =
	 AddI
	 | MultI
	 | MaxI
	 | MinI
         | App1

(* binary logical connectives *)
datatype bin_conn =
	 And
	 | Or
	 | Imply
	 | Iff

(* binary predicates on indices *)
datatype bin_pred =
         LeP
         | EqP
         | GtP
         | BigO
               
datatype bin_op =
         Add

datatype quan =
         Forall
         | Exists

fun str_idx_un_op opr =
  case opr of
      ToReal => "$"
    | Log2 => "log2"
    | Ceil => "ceil"
    | Floor => "floor"

fun str_idx_bin_op opr =
  case opr of
      AddI => "+"
    | MultI => "*"
    | MaxI => "max"
    | MinI => "min"
    | App1 => ""

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
    | GtP => ">"
    | BigO => "O"

fun str_bin_op opr =
  case opr of
      Add => "+"

fun str_quan q =
    case q of
        Forall => "forall"
      | Exists => "exists"

end
