structure LongIdUtil = struct

(* if it has module reference, don't shift/forget *)
fun on_v_long_id on_v x n (m, (y, r)) =
  let
    val y =
        case m of
            NONE => on_v x n y
          | SOME _ => y
  in
    (m, (y, r))
  end

end
