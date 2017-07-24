functor TypeUtilFn (structure Type : TYPE (* where type name = string * Region.region *)
                   (* val dummy : Idx.region *)
                   ) = struct

open Type
open Bind
       
fun collect_UniI t =
  case t of
      UniI (s, Bind (name, t), _) =>
      let val (binds, t) = collect_UniI t
      in
        ((name, s) :: binds, t)
      end
    | _ => ([], t)

fun collect_Uni t =
  case t of
      Uni (Bind (name, t), _) =>
      let val (names, t) = collect_Uni t
      in
        (name :: names, t)
      end
    | Mono t => ([], t)

end

