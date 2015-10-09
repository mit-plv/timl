structure SMTSolver = struct
open Unix
open TextIO
open SMT2Printer

infixr 0 $

fun dowhile cond body st =
    if cond st then
        dowhile cond body (body st)
    else
        st

fun smt_solver filename vcs = 
    let
        val smt2 = to_smt vcs
        val proc = execute ("z3", ["-in"])
        val (ins, outs) = (textInstreamOf proc, textOutstreamOf proc)
        val () = output (outs, smt2)
        val resp = rev $ dowhile (fn _ => not (endOfStream ins)) (fn acc => case inputLine ins of SOME line => line :: acc | _ => acc) []
        val () = List.app println resp
        val _ = reap proc
    in
        vcs
    end
end
