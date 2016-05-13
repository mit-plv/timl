open Ast
open Util

structure T = Tokens

type pos = pos
type svalue = T.svalue
type ('a, 'b) token = ('a, 'b) T.token
type lexresult = (svalue, pos) token
type lexarg = reporter
type arg = lexarg

val LINE = 1
val LINE_START = 1
val COMMENT_LEVEL = 0
val line = ref LINE
val linestart = ref LINE_START
val comment_level = ref COMMENT_LEVEL
  
(* debug toggle *)
val print = fn s => ()

fun make_pos abs : pos = 
    {abs = abs, line = !line, col = abs - !linestart - 1}
fun make_region (abs, size) : region = 
    (make_pos abs, 
     make_pos (abs + size))
fun update_line yypos = (inc line; linestart := yypos)
fun reset_line () =
    (line := LINE;
     linestart := LINE_START;
     comment_level := COMMENT_LEVEL
    )

fun flat (a, (b, c)) = (a, b, c)

fun eof reporter =
  let
      val r = make_region (!linestart, 0)
  in
      print "matched eof\n";
      if !comment_level > 0 then (reporter o flat) ("Unclosed comment", r) else ();
      T.EOF r
  end
      
(* fun error (f, msg, left, right) = f (msg, left, right) *)

val keywords = [
    ("fn", T.FN),
    ("fun", T.FUN),
    ("case", T.CASE),
    ("unpack", T.UNPACK),
    ("of", T.OF),
    ("let", T.LET),
    ("in", T.IN),
    ("end", T.END),
    ("return", T.RETURN),
    ("val", T.VAL),
    ("datatype", T.DATATYPE),
    ("forall", T.FORALL),
    ("exists", T.EXISTS),
    ("max", T.MAX),
    ("min", T.MIN),
    ("O", T.BIG_O_INFIX),
    ("idx", T.IDX),
    ("type", T.TYPE),
    ("abstype", T.ABSTYPE),
    ("absidx", T.ABSIDX),
    ("with", T.WITH),
    ("using", T.RTRI),
    ("as", T.AS)
]
 
fun find (m, k : string) = Option.map #2 (List.find (fn (k', _) => k' = k) m)

fun is_keyword s = find (keywords, s)

				 %%

				 %header (functor TiMLLexFun (structure Tokens : TiML_TOKENS));

%arg (reporter : Ast.reporter);
				 %s COMMENT;

alpha = [A-Za-z];
digit = [0-9];
ws = [\ \t];
eol = (\013\010|\010|\013);
id_init = ({alpha}|[_']);

%%

{eol} => (print "matched eol\n"; update_line yypos; continue());

<INITIAL>{ws}+ => (continue ());

<INITIAL>"(" => (print "matched (\n"; T.LPAREN (make_region (yypos, size yytext)));
<INITIAL>")" => (print "matched )\n"; T.RPAREN (make_region (yypos, size yytext)));
<INITIAL>"=>" => (T.DARROW (make_region (yypos, size yytext)));
<INITIAL>"[" => (T.LSQ (make_region (yypos, size yytext)));
<INITIAL>"]" => (T.RSQ (make_region (yypos, size yytext)));
<INITIAL>"{" => (T.LCUR (make_region (yypos, size yytext)));
<INITIAL>"}" => (T.RCUR (make_region (yypos, size yytext)));
<INITIAL>":" => (T.COLON (make_region (yypos, size yytext)));
<INITIAL>"|>" => (T.RTRI (make_region (yypos, size yytext)));
<INITIAL>"," => (T.COMMA (make_region (yypos, size yytext)));
<INITIAL>"->" => (T.ARROW (make_region (yypos, size yytext)));
<INITIAL>"-->" => (T.LARROW (make_region (yypos, size yytext)));
<INITIAL>"--" => (T.DDASH (make_region (yypos, size yytext)));
<INITIAL>"|" => (T.BAR (make_region (yypos, size yytext)));
<INITIAL>"~" => (T.NOT (make_region (yypos, size yytext)));
<INITIAL>"/\\" => (T.AND (make_region (yypos, size yytext)));
<INITIAL>"\\/" => (T.OR (make_region (yypos, size yytext)));
<INITIAL>"<->" => (T.IFF (make_region (yypos, size yytext)));
<INITIAL>"=" => (T.EQ (make_region (yypos, size yytext)));
<INITIAL>"==" => (T.DOUBLE_EQ (make_region (yypos, size yytext)));
<INITIAL>"&&" => (T.DOUBLE_POND (make_region (yypos, size yytext)));
<INITIAL>"<=" => (T.LE (make_region (yypos, size yytext)));
<INITIAL>"<" => (T.LT (make_region (yypos, size yytext)));
<INITIAL>">=" => (T.GE (make_region (yypos, size yytext)));
<INITIAL>">" => (T.GT (make_region (yypos, size yytext)));
<INITIAL>"+" => (T.PLUS (make_region (yypos, size yytext)));
<INITIAL>"-" => (T.MINUS (make_region (yypos, size yytext)));
<INITIAL>"*" => (T.MULT (make_region (yypos, size yytext)));
<INITIAL>"/" => (T.DIV (make_region (yypos, size yytext)));
<INITIAL>"$" => (T.DOLLAR (make_region (yypos, size yytext)));
<INITIAL>"@" => (T.AT (make_region (yypos, size yytext)));
<INITIAL>"<==" => (T.BIG_O_INFIX (make_region (yypos, size yytext)));

<INITIAL>{digit}+\.{digit}+ => ((T.NNREAL o flat)
                 (yytext, make_region (yypos, size yytext)));
 
<INITIAL>{digit}+ => ((T.INT o flat)
                 (foldl (fn (a,r) => ord(a)-ord(#"0")+10*r) 0 (explode yytext),
                    make_region (yypos, size yytext)));
 
<INITIAL>{id_init}({id_init}|{digit})* => ((getOpt (is_keyword yytext, fn r => (T.ID o flat) (yytext, r)))
				  (make_region (yypos, size yytext)));
<INITIAL>. => ((reporter o flat) (sprintf "Bad character: $" [yytext], make_region (yypos, size yytext)); (T.BOGUS o flat) (yytext, make_region (yypos, size yytext)));

<INITIAL>"(*" => (inc comment_level; YYBEGIN COMMENT; continue());
<COMMENT>"(*" => (inc comment_level; continue());
<COMMENT>"*)" => (dec comment_level; if !comment_level = 0 then YYBEGIN INITIAL else (); continue());
<COMMENT>. => (continue());
