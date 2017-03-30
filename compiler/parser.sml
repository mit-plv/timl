structure MicroTiMLLrVals = MicroTiMLLrValsFun(structure Token = LrParser.Token)

structure MicroTiMLLex = MicroTiMLLexFun(structure Tokens = MicroTiMLLrVals.Tokens)

structure MicroTiMLParser = JoinWithArg(
    structure ParserData = MicroTiMLLrVals.ParserData
    structure Lex = MicroTiMLLex
    structure LrParser = LrParser)

structure Parser =
struct
open Util
open MicroTiMLInst

val lookahead = 15

type input_stream = int -> string

exception Error

fun parse (input : input_stream, on_lex_error : reporter, on_parse_error : reporter) =
  #1 (MicroTiMLParser.parse
          (lookahead,
           MicroTiMLParser.makeLexer input on_lex_error,
           on_parse_error,
           on_lex_error))
  handle MicroTiMLParser.ParseError => raise Error

fun parse_file filename =
  let
      val inStream = TextIO.openIn filename
      fun input n =
        if TextIO.endOfStream inStream then ""
        else TextIO.inputN (inStream, n)
      fun on_error (msg, left, right) = print (str_error "error" filename (left, right) [msg])
      val () = MicroTiMLLex.UserDeclarations.reset_line ()
      val s = parse (input, on_error, on_error)
      val _ = TextIO.closeIn inStream
  in
      s
  end
end
