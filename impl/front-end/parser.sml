structure TiMLLrVals = TiMLLrValsFun(structure Token = LrParser.Token)

structure TiMLLex = TiMLLexFun (structure Tokens = TiMLLrVals.Tokens)

structure TiMLParser = JoinWithArg (
    structure ParserData = TiMLLrVals.ParserData
    structure Lex = TiMLLex
    structure LrParser = LrParser)

structure Parser = struct
open Util
val lookahead = 15
fun parse input on_lex_error on_parse_error = OK (TiMLParser.parse 
		    (lookahead,
		     TiMLParser.makeLexer input on_lex_error,
		     on_parse_error,
		     on_lex_error))
	    handle TiMLParser.ParseError => Failed "Parse error"
end
