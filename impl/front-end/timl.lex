open Ast
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

fun inc r = r := !r + 1
fun make_pos abs : pos = 
    {abs = abs, line = !line, col = abs - !linestart}
fun make_region (abs, size) : region = 
    (make_pos abs, 
     make_pos (abs + size))
fun update_line yypos = (inc line; linestart := yypos)

fun eof _ = (print "matched eof\n"; T.EOF (make_region (!linestart, 0)))
(* fun error (f, msg, left, right) = f (msg, left, right) *)

fun flat (a, (b, c)) = (a, b, c)

val keywords = [
    ("fn", T.FN),
    ("fix", T.FIX),
    ("case", T.CASE),
    ("of", T.OF),
    ("let", T.LET),
    ("in", T.IN),
    ("end", T.END),
    ("return", T.RETURN),
    ("mu", T.MU),
    ("val", T.VAL),
    ("forall", T.FORALL),
    ("exists", T.EXISTS),
    ("max", T.MAX),
    ("min", T.MIN)
]

fun find (m, k : string) = Option.map #2 (List.find (fn (k', _) => k' = k) m)

fun is_keyword s = find (keywords, s)

				 %%

				 %header (functor TiMLLexFun (structure Tokens : TiML_TOKENS));

%arg (reporter : reporter);
				 %s COMMENT;

alpha = [A-Za-z];
digit = [0-9];
ws = [\ \t];
eol = (\013\010|\010|\013);
(* eol = ("\013\010"|"\010"|"\013"); *)
(* eol = \n; *)
id_init = ({alpha}|[_']);

%%

(* \013\010|\010|\013 => (print "matched eol\n"; update_line yypos; continue()); *)
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
<INITIAL>"--" => (T.DDASH (make_region (yypos, size yytext)));
<INITIAL>"|" => (T.BAR (make_region (yypos, size yytext)));
<INITIAL>"/\\" => (T.AND (make_region (yypos, size yytext)));
<INITIAL>"\\/" => (T.OR (make_region (yypos, size yytext)));
<INITIAL>"<->" => (T.IFF (make_region (yypos, size yytext)));
<INITIAL>"=" => (T.EQ (make_region (yypos, size yytext)));
<INITIAL>"<=" => (T.LE (make_region (yypos, size yytext)));
<INITIAL>"+" => (T.PLUS (make_region (yypos, size yytext)));
<INITIAL>"*" => (T.MULT (make_region (yypos, size yytext)));

<INITIAL>{digit}+ => ((T.INT o flat)
                 (foldl (fn (a,r) => ord(a)-ord(#"0")+10*r) 0 (explode yytext),
                    make_region (yypos, size yytext)));
 
<INITIAL>{id_init}({id_init}|{digit})* => ((getOpt (is_keyword yytext, fn r => (T.ID o flat) (yytext, r)))
				  (make_region (yypos, size yytext)));
<INITIAL>. => ((reporter o flat) (sprintf "Bad character: $" [yytext], make_region (yypos, size yytext)); (T.BOGUS o flat) (yytext, make_region (yypos, size yytext)));

<INITIAL>"(*" => (YYBEGIN COMMENT; continue());
<COMMENT>"*)" => (YYBEGIN INITIAL; continue());
<COMMENT>. => (continue());
