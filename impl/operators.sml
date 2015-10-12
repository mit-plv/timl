structure Operators = struct

datatype idx_bin_op =
	 AddI
	 | MinusI
	 | MultI
	 | MaxI
	 | MinI

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
               
datatype bin_op =
         Add

fun str_idx_bin_op opr =
  case opr of
      AddI => "+"
    | MinusI => "-"
    | MultI => "*"
    | MaxI => "max"
    | MinI => "min"

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

fun str_bin_op opr =
  case opr of
      Add => "+"

end
