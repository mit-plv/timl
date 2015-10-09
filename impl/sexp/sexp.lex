open SExp
open Util

structure T = Tokens

type pos = pos
type svalue = T.svalue
type ('a, 'b) token = ('a, 'b) T.token
type lexresult = (svalue, pos) token
type lexarg = reporter
type arg = lexarg

val line = ref 1
val linestart = ref 1
  
(* debug toggle *)
val print = fn s => ()

fun make_pos abs : pos = 
    {abs = abs, line = !line, col = abs - !linestart - 1}
fun make_region (abs, size) : region = 
    (make_pos abs, 
     make_pos (abs + size))
fun update_line yypos = (inc line; linestart := yypos)

fun flat (a, (b, c)) = (a, b, c)

fun eof reporter =
  let
      val r = make_region (!linestart, 0)
  in
      print "matched eof\n";
      T.EOF r
  end
      
%%
      
%header (functor SExpLexFun (structure Tokens : SExp_TOKENS));

%arg (reporter : SExp.reporter);
%s COMMENT STRING_S;

ws = [\ \t];
eol = (\013\010|\010|\013);

%%

{eol} => (print "matched eol\n"; YYBEGIN INITIAL; update_line yypos; continue());

<INITIAL>{ws}+ => (continue ());
<INITIAL>"(" => (print "matched (\n"; T.LPAREN (make_region (yypos, size yytext)));
<INITIAL>")" => (print "matched )\n"; T.RPAREN (make_region (yypos, size yytext)));
<INITIAL>[^\ \t\n"()]+ => ((T.ATOM o flat) (yytext, make_region (yypos, size yytext)));
<INITIAL>"\"" => (YYBEGIN STRING_S; continue());
<INITIAL>";" => (YYBEGIN COMMENT; continue());
<INITIAL>. => ((reporter o flat) (sprintf "Bad character: $" [yytext], make_region (yypos, size yytext)); (T.BOGUS o flat) (yytext, make_region (yypos, size yytext)));

<STRING_S> (\\\"|[^\n"])* => ((T.STRING o flat) (yytext, make_region (yypos, size yytext)));
<STRING_S> "\"" => (YYBEGIN INITIAL; continue());
 
<COMMENT>. => (continue());
