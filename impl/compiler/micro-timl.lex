open List
open MicroTiMLInst

structure T = Tokens

type pos = pos
type svalue = T.svalue
type ('a, 'b) token = ('a, 'b) T.token
type lexresult = (svalue, pos) token
type lexarg = reporter
type arg = lexarg

val LINE = 1
val LINE_START = 1
val line = ref LINE
val linestart = ref LINE_START

fun make_pos abs : pos =
  {abs = abs, line = !line, col = abs - !linestart - 1}

fun make_region (abs, size) : region =
  (make_pos abs, make_pos (abs + size))

fun update_line yypos = (inc line; linestart := yypos)

fun reset_line () =
  (line := LINE;
   linestart := LINE_START)

fun flat (a, (b, c)) = (a, b, c)

fun eof reporter =
  let
    val r = make_region (!linestart, 0)
  in
    T.EOF r
  end

%%

%header (functor MicroTiMLLexFun (structure Tokens : MicroTiML_TOKENS));

%arg (reporter : MicroTiMLInst.reporter);

id = ([a-zA-Z]|[0-9]|_);
digit = [0-9];
ws = [\ \t];
eol = (\013\010|\010|\013);

%%

{eol} => (update_line yypos; continue ());
{ws}+ => (continue ());

"(" => (T.LPAREN (make_region (yypos, size yytext)));
")" => (T.RPAREN (make_region (yypos, size yytext)));
":" => (T.COLON (make_region (yypos, size yytext)));
"|>" => (T.RTRI (make_region (yypos, size yytext)));
"[" => (T.LSQUARE (make_region (yypos, size yytext)));
"]" => (T.RSQUARE (make_region (yypos, size yytext)));
"{" => (T.LCURLY (make_region (yypos, size yytext)));
"}" => (T.RCURLY (make_region (yypos, size yytext)));
"+" => (T.PLUS (make_region (yypos, size yytext)));
"+n" => (T.NPLUS (make_region (yypos, size yytext)));
"+r" => (T.RPLUS (make_region (yypos, size yytext)));
"+t" => (T.TPLUS (make_region (yypos, size yytext)));
"-n" => (T.NMINUS (make_region (yypos, size yytext)));
"-r" => (T.RMINUS (make_region (yypos, size yytext)));
"*n" => (T.NMULT (make_region (yypos, size yytext)));
"*r" => (T.RMULT (make_region (yypos, size yytext)));
"*t" => (T.TMULT (make_region (yypos, size yytext)));
"*" => (T.MULT (make_region (yypos, size yytext)));
"/" => (T.DIV (make_region (yypos, size yytext)));
"->" => (T.ARROW (make_region (yypos, size yytext)));
"=>" => (T.DARROW (make_region (yypos, size yytext)));
"|" => (T.VBAR (make_region (yypos, size yytext)));
"~" => (T.TILDE (make_region (yypos, size yytext)));
"/\\" => (T.CONJ (make_region (yypos, size yytext)));
"\\/" => (T.DISJ (make_region (yypos, size yytext)));
"<->" => (T.IFF (make_region (yypos, size yytext)));
"=n" => (T.NEQ (make_region (yypos, size yytext)));
"<=n" => (T.NLE (make_region (yypos, size yytext)));
">=n" => (T.NGE (make_region (yypos, size yytext)));
"<n" => (T.NLT (make_region (yypos, size yytext)));
">n" => (T.NGT (make_region (yypos, size yytext)));
"=r" => (T.REQ (make_region (yypos, size yytext)));
"<=r" => (T.RLE (make_region (yypos, size yytext)));
">=r" => (T.RGE (make_region (yypos, size yytext)));
"<r" => (T.RLT (make_region (yypos, size yytext)));
">r" => (T.RGT (make_region (yypos, size yytext)));

"tt" => (T.TT (make_region (yypos, size yytext)));
"fn" => (T.FN (make_region (yypos, size yytext)));
"pair" => (T.PAIR (make_region (yypos, size yytext)));
"fst" => (T.FST (make_region (yypos, size yytext)));
"snd" => (T.SND (make_region (yypos, size yytext)));
"inl" => (T.INL (make_region (yypos, size yytext)));
"inr" => (T.INR (make_region (yypos, size yytext)));
"fold" => (T.FOLD (make_region (yypos, size yytext)));
"unfold" => (T.UNFOLD (make_region (yypos, size yytext)));
"pack" => (T.PACK (make_region (yypos, size yytext)));
"unpack" => (T.UNPACK (make_region (yypos, size yytext)));
"rec" => (T.REC (make_region (yypos, size yytext)));
"let" => (T.LET (make_region (yypos, size yytext)));
"new" => (T.NEW (make_region (yypos, size yytext)));
"read" => (T.READ (make_region (yypos, size yytext)));
"write" => (T.WRITE (make_region (yypos, size yytext)));
"true" => (T.TRUE (make_region (yypos, size yytext)));
"false" => (T.FALSE (make_region (yypos, size yytext)));
"Unit" => (T.TUNIT (make_region (yypos, size yytext)));
"Int" => (T.TINT (make_region (yypos, size yytext)));
"ite" => (T.ITE (make_region (yypos, size yytext)));
"TimeAbs" => (T.TIMEABS (make_region (yypos, size yytext)));
"TimeApp" => (T.TIMEAPP (make_region (yypos, size yytext)));
"BigO" => (T.BIGO (make_region (yypos, size yytext)));
"min" => (T.MIN (make_region (yypos, size yytext)));
"max" => (T.MAX (make_region (yypos, size yytext)));
"ceil" => (T.CEIL (make_region (yypos, size yytext)));
"floor" => (T.FLOOR (make_region (yypos, size yytext)));
"log" => (T.LOG (make_region (yypos, size yytext)));
"n2t" => (T.N2T (make_region (yypos, size yytext)));
"b2n" => (T.B2N (make_region (yypos, size yytext)));
"forall" => (T.FORALL (make_region (yypos, size yytext)));
"exists" => (T.EXISTS (make_region (yypos, size yytext)));
"Nat" => (T.TNAT (make_region (yypos, size yytext)));
"Arr" => (T.TARR (make_region (yypos, size yytext)));
"nat" => (T.SNAT (make_region (yypos, size yytext)));
"bool" => (T.SBOOL (make_region (yypos, size yytext)));
"unit" => (T.SUNIT (make_region (yypos, size yytext)));
"tfun" => (T.STFUN (make_region (yypos, size yytext)));

{digit}+\.{digit}+ => ((T.REALV o flat) (yytext, make_region (yypos, size yytext)));
{digit}+ => ((T.INTV o flat) (foldl (fn (a, r) => ord(a) - ord(#"0") + 10 * r) 0 (explode yytext), make_region (yypos, size yytext)));
"#"{digit}+ => ((T.NATV o flat) (foldl (fn (a, r) => ord(a) - ord(#"0") + 10 * r) 0 (drop (explode yytext, 1)), make_region (yypos, size yytext)));
([a-z]|_){id}* => ((T.LCID o flat) (yytext, make_region (yypos, size yytext)));
[A-Z]{id}* => ((T.UCID o flat) (yytext, make_region (yypos, size yytext)));

. => ((reporter o flat) (sprintf "bad character: $" [yytext], make_region (yypos, size yytext)); (T.BOGUS o flat) (yytext, make_region (yypos, size yytext)));
