structure SMTSolver = struct
(* open Unix *)

open TextIO
open SMT2Printer
open OS.Process
open SExp

infixr 0 $

(* fun dowhile cond body st = *)
(*     if cond st then *)
(*         dowhile cond body (body st) *)
(*     else *)
(*         st *)

fun group n ls =
    if length ls <= n then
        [ls]
    else
        List.take (ls, n) :: group n (List.drop (ls, n))
                                
exception SMTError of string

fun get_model model =
  let
      val err = SMTError "Wrong model format"
      fun on_def def =
        case def of
            List [Atom header, Atom name, List [], _, Atom value] =>
            if header = "define-fun" then
                (name, value)
            else
                raise err
          | _ => raise err
  in
      case model of
          List (Atom header :: defs) =>
          if header = "model" then
              map on_def defs
          else
              raise err
        | _ => raise err
  end
                          
fun smt_solver filename vcs = 
    let
        val smt2 = to_smt2 vcs
        val smt2_filename = filename ^ ".smt2"
        val resp_filename = filename ^ ".lisp"
        val () = write_file (smt2_filename, smt2)
        val _ = system (sprintf "z3 $ > $" [smt2_filename, resp_filename])
        (* val resp = read_file resp_filename *)
        (* val () = println resp *)
        val resps = SExpParserString.parse_file resp_filename
        (* val () = println $ str_int $ length resps *)
        val () = if length resps = 2 * length vcs then ()
                 else raise SMTError "Wrong number of responses"
        val resps = group 2 resps
        fun on_resp (vc, resp) =
            let val error_msg = "Wrong response format: first answer should be (sat), (unsat) or (unknown)"
            in
                case resp of
                    [is_sat, model] =>
                    (case is_sat of
                         Atom is_sat =>
                         if is_sat = "unsat" then
                             NONE
                         else if is_sat = "sat" then
                             SOME (vc, SOME (get_model model))
                         else if is_sat = "unknown" then
                             SOME (vc, NONE)
                         else
                             raise SMTError error_msg
                       | _ => raise SMTError error_msg
                    )
                  | _ => raise Impossible "number of responses should have been checked "
            end
        val vcs = List.mapPartial on_resp (zip (vcs, resps))
                      
        (* val proc = execute ("z3", ["-in"]) *)
        (* val (ins, outs) = (textInstreamOf proc, textOutstreamOf proc) *)
        (* val () = output (outs, smt2) *)
        (* val () = println $ str_bool $ endOfStream ins *)
        (* val s = input ins *)
        (* (* val s = inputN (ins, 30) *) *)
        (* val () = println $ str_int $ size s *)
        (* val () = println s *)
        (* val () = case inputLine ins of SOME str => println str | _ => ()  *)
        (* val resp = rev $ dowhile (fn _ => not (endOfStream ins)) (fn acc => case inputLine ins of SOME line => line :: acc | _ => acc) [] *)
        (* val () = println "hello?" *)
        (* val () = List.app println resp *)
        (* val _ = reap proc *)
    in
        vcs
    end
        
end
