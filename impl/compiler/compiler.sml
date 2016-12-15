structure Compiler =
struct
open Util
open OS.Process

fun main (prog_name, args : string list) : int =
  let
      val _ =
          case args of
              [] => (println "no input"; exit failure)
            | _ => Parser.parse_file (hd args)
  in
      0
  end

end
