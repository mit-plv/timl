(* common interface for enumerating elements in a container *)
structure Enum = struct

type ('a, 'b) enum = ('a * 'b -> 'b) -> 'b -> 'b

end

