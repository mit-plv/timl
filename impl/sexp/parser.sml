structure SExpLrVals = SExpLrValsFun(structure Token = LrParser.Token)

structure SExpLex = SExpLexFun (structure Tokens = SExpLrVals.Tokens)

structure SExpParser = JoinWithArg (
    structure ParserData = SExpLrVals.ParserData
    structure Lex = SExpLex
    structure LrParser = LrParser)

structure SExpParserString = struct
open SExp
	 
val lookahead = 15
		    
type input_stream = int -> string
			       
exception Error
	      
fun parse (input : input_stream, on_lex_error : reporter, on_parse_error : reporter) =
  #1 (SExpParser.parse 
	  (lookahead,
	   SExpParser.makeLexer input on_lex_error,
	   on_parse_error,
	   on_lex_error))
  handle SExpParser.ParseError => raise Error
					
open Util
	 
fun parse_opt (input : input_stream, on_lex_error : reporter, on_parse_error : reporter) =
    OK (parse (input, on_parse_error, on_lex_error)) handle Error => Failed "Parse error"
									    
open Region

fun parse_file filename =
  let
      val inStream =  TextIO.openIn filename
      fun input n =
	if TextIO.endOfStream inStream
	then ""
	else TextIO.inputN (inStream,n);

      fun on_error (msg, left, right) = print (str_error "Error" filename (left, right) [msg])
      val ret = parse (input, on_error, on_error)
      val _ = TextIO.closeIn inStream
  in
      ret
  end

end
