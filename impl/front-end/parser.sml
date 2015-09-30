structure TiMLLrVals = TiMLLrValsFun(structure Token = LrParser.Token)

structure TiMLLex = TiMLLexFun (structure Tokens = TiMLLrVals.Tokens)

structure TiMLParser = JoinWithArg (
    structure ParserData = TiMLLrVals.ParserData
    structure Lex = TiMLLex
    structure LrParser = LrParser)

structure Parser = struct
open Ast
	 
val lookahead = 15
		    
type input_stream = int -> string
			       
exception Error
	      
fun parse (input : input_stream, on_lex_error : reporter, on_parse_error : reporter) : exp =
  #1 (TiMLParser.parse 
	  (lookahead,
	   TiMLParser.makeLexer input on_lex_error,
	   on_parse_error,
	   on_lex_error))
  handle TiMLParser.ParseError => raise Error
					
open Util
	 
fun parse_opt (input : input_stream, on_lex_error : reporter, on_parse_error : reporter) : exp result =
    OK (parse (input, on_parse_error, on_lex_error)) handle Error => Failed "Parse error"
									    
end
