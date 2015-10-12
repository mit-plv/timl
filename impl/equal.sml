structure IdxEqual = struct
open Type
         
fun eq_i i i' =
  case (i, i') of
      (VarI (x, _), VarI (x', _)) => x = x'
    | (ConstIN (n, _), ConstIN (n', _)) => n = n'
    | (ConstIT (x, _), ConstIT (x', _)) => x = x'
    | (ToReal (i, _), ToReal (i', _)) => eq_i i i'
    | (BinOpI (opr, i1, i2), BinOpI (opr', i1', i2')) => opr = opr' andalso eq_i i1 i1' andalso eq_i i2 i2'
    | (TrueI _, TrueI _) => true
    | (FalseI _, FalseI _) => true
    | (TTI _, TTI _) => true
    | _ => false

fun eq_p p p' =
  case (p, p') of
      (True _ , True _) => true
    | (False _, False _) => true
    | (BinConn (opr, p1, p2), BinConn (opr', p1', p2')) => opr = opr' andalso eq_p p1 p1' andalso eq_p p2 p2'
    | (BinPred (opr, i1, i2), BinPred (opr', i1', i2')) => opr = opr' andalso eq_i i1 i1' andalso eq_i i2 i2'
    | _ => false

end
