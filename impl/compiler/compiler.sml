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
      val ty4 = clo_conv_deriv ty3
      val () = println "---- flattened."
      val () = println $ PlainPrinter.str_expr (#2 (extract_judge_typing ty4))
      val ty5 = hoist_deriv ty4
      val () = check_program ty5
      val () = println "---- hoisted."
      val () = println $ str_program (#1 (extract_judge_ptyping ty5))
      val ty6 = code_gen_deriv ty5
      val () = println "---- coded."
      val () = println $ str_tal_program (#1 (extract_judge_tal_program_typing ty6))
  in
      0
  end

end
