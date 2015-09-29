structure T = Tokens

type pos = pos
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token
type lexarg = reporter
type arg = lexarg

val lin = ref 1
val linstart = ref 0

fun eof _ = Tokens.EOF (makeregion (yypos, 0))
fun error (f, msg, pos, pos) = f (msg, pos, pos)

fun makeregion (abs, size) = ({abs = abs, lin = !lin, col = abs - !linstart}, {abs = abs + size, lin = 0, col = 0})

				 %%

				 %header (functor TiMLLexFun (structure Tokens : TiML_TOKENS));

alpha = [A-Za-z];
digit = [0-9];
ws = [\ \t];
eol = ("\013\010"|"\010"|"\013");

%%

    eol => (update_lin yypos);

{ws}+ => (continue ());

{digit}+ => (Tokens.INT
                 (revfold (fn (a,r) => ord(a)-ord("0")+10*r) (explode yytext) 0,
                  makeregion (yypos, 0)));

"+" => (Tokens.Plus (makeregion (yypos, 0)));
