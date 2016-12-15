open List

structure T = Tokens

type pos = unit
type svalue = T.svalue
type ('a, 'b) token = ('a, 'b) T.token
type lexresult = (svalue, pos) token

fun eof _ = T.EOF ((), ())

%%

%header (functor MicroTiMLLexFun (structure Tokens : MicroTiML_TOKENS));

id = ([a-zA-Z]|[0-9]|_);
digit = [0-9];
ws = [\ \t];
eol = (\013\010|\010|\013);

%%

{eol} => (continue ());
{ws}+ => (continue ());

"(" => (T.LPAREN ((), ()));
")" => (T.RPAREN ((), ()));
":" => (T.COLON ((), ()));
"|>" => (T.RTRI ((), ()));
"[" => (T.LSQUARE ((), ()));
"]" => (T.RSQUARE ((), ()));
"{" => (T.LCURLY ((), ()));
"}" => (T.RCURLY ((), ()));
"+" => (T.PLUS ((), ()));
"-" => (T.MINUS ((), ()));
"*" => (T.MULT ((), ()));
"/" => (T.DIV ((), ()));

"tt" => (T.TT ((), ()));
"fn" => (T.FN ((), ()));
"pair" => (T.PAIR ((), ()));
"fst" => (T.FST ((), ()));
"snd" => (T.SND ((), ()));
"inl" => (T.INL ((), ()));
"inr" => (T.INR ((), ()));
"fold" => (T.FOLD ((), ()));
"unfold" => (T.UNFOLD ((), ()));
"pack" => (T.PACK ((), ()));
"unpack" => (T.UNPACK ((), ()));
"rec" => (T.REC ((), ()));
"let" => (T.LET ((), ()));
"new" => (T.NEW ((), ()));
"read" => (T.READ ((), ()));
"write" => (T.WRITE ((), ()));

{digit}+\.{digit}+ => (T.REALV (yytext, (), ()));
{digit}+ => (T.INTV (foldl (fn (a, r) => ord(a) - ord(#"0") + 10 * r) 0 (explode yytext), (), ()));
"#"{digit}+ => (T.NATV (foldl (fn (a, r) => ord(a) - ord(#"0") + 10 * r) 0 (drop (explode yytext, 1)), (), ()));
([a-z]|_){id}* => (T.LCID (yytext, (), ()));
[A-Z]{id}* => (T.UCID (yytext, (), ()));
