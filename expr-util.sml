functor ExprUtilFn (Expr : EXPR) = struct

open Expr

fun collect_Pair e =
  case e of
      EBinOp (EBPair, e1, e2) =>
      collect_Pair e1 @ [e2]
    | _ => [e]
             
end
