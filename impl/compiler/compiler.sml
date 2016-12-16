structure Compiler =
struct
open Util
open OS.Process
open Parser
infixr 0 $

fun main (prog_name, args : string list) : int =
  let
      val ty1 =
          case args of
              [] => (println "no input"; exit failure)
            | _ => (parse_file (hd args)) (([], []), ([], []))
      val ty2 = cps_deriv ty1
      val () = println $ PlainPrinter.str_expr (#2 (extract_judge_typing ty2))
  in
      0
  end

end
