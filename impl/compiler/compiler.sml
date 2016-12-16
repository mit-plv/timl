structure Compiler =
struct
open Util
open OS.Process
open Parser
infixr 0 $

fun main (prog_name, args : string list) : int =
  let
      val ast =
          case args of
              [] => (println "no input"; exit failure)
            | _ => (parse_file (hd args))
      val () = println "---- parsed."
      val ty1 = ast (([], []), ([], []))
      val () = println "---- generated."
      val ty2 = cps_deriv ty1
      val () = println "---- cpsed."
      val () = println $ PlainPrinter.str_expr (#2 (extract_judge_typing ty2))
      val ty3 = wrap_abs_deriv ty2
      val () = println "---- wrapped."
      val () = println $ PlainPrinter.str_expr (#2 (extract_judge_typing ty3))
  in
      0
  end

end
