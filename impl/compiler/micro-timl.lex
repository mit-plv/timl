open List
open MicroTiMLInst

structure T = Tokens

type pos = unit
type svalue = T.svalue
type ('a, 'b) token = ('a, 'b) T.token
type lexresult = (svalue, pos) token
type lexarg = reporter
type arg = lexarg

fun eof _ = T.EOF ((), ())

%%

%header (functor MicroTiMLLexFun (structure Tokens : MicroTiML_TOKENS));

%arg (reporter : MicroTiMLInst.reporter);

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
"+n" => (T.NPLUS ((), ()));
"+r" => (T.RPLUS ((), ()));
"+t" => (T.TPLUS ((), ()));
"-n" => (T.NMINUS ((), ()));
"-r" => (T.RMINUS ((), ()));
"*n" => (T.NMULT ((), ()));
"*r" => (T.RMULT ((), ()));
"*t" => (T.TMULT ((), ()));
"*" => (T.MULT ((), ()));
"/" => (T.DIV ((), ()));
"->" => (T.ARROW ((), ()));
"=>" => (T.DARROW ((), ()));
"|" => (T.VBAR ((), ()));
"~" => (T.TILDE ((), ()));
"/\\" => (T.CONJ ((), ()));
"\\/" => (T.DISJ ((), ()));
"<->" => (T.IFF ((), ()));
"=n" => (T.NEQ ((), ()));
"<=n" => (T.NLE ((), ()));
">=n" => (T.NGE ((), ()));
"<n" => (T.NLT ((), ()));
">n" => (T.NGT ((), ()));
"=r" => (T.REQ ((), ()));
"<=r" => (T.RLE ((), ()));
">=r" => (T.RGE ((), ()));
"<r" => (T.RLT ((), ()));
">r" => (T.RGT ((), ()));

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
"true" => (T.TRUE ((), ()));
"false" => (T.FALSE ((), ()));
"Unit" => (T.TUNIT ((), ()));
"Int" => (T.TINT ((), ()));
"ite" => (T.ITE ((), ()));
"TimeAbs" => (T.TIMEABS ((), ()));
"TimeApp" => (T.TIMEAPP ((), ()));
"BigO" => (T.BIGO ((), ()));
"min" => (T.MIN ((), ()));
"max" => (T.MAX ((), ()));
"ceil" => (T.CEIL ((), ()));
"floor" => (T.FLOOR ((), ()));
"log" => (T.LOG ((), ()));
"n2t" => (T.N2T ((), ()));
"b2n" => (T.B2N ((), ()));
"forall" => (T.FORALL ((), ()));
"exists" => (T.EXISTS ((), ()));
"Nat" => (T.TNAT ((), ()));
"Arr" => (T.TARR ((), ()));
"nat" => (T.SNAT ((), ()));
"bool" => (T.SBOOL ((), ()));
"unit" => (T.SUNIT ((), ()));
"tfun" => (T.STFUN ((), ()));

{digit}+\.{digit}+ => (T.REALV (yytext, (), ()));
{digit}+ => (T.INTV (foldl (fn (a, r) => ord(a) - ord(#"0") + 10 * r) 0 (explode yytext), (), ()));
"#"{digit}+ => (T.NATV (foldl (fn (a, r) => ord(a) - ord(#"0") + 10 * r) 0 (drop (explode yytext, 1)), (), ()));
([a-z]|_){id}* => (T.LCID (yytext, (), ()));
[A-Z]{id}* => (T.UCID (yytext, (), ()));
