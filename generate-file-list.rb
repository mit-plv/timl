#!/usr/bin/env ruby

require 'stringio'

def usage
 puts "usage: THIS_SCRIPT [smlnj|mlton|Makefile]"  
end

def wrong_arguments
  puts "wrong arguments"
  usage
  exit 1
end

if ARGV.size != 1 then
  wrong_arguments
end

target = ARGV[0]

if target == "smlnj" then
  target = :smlnj
elsif target == "mlton" then
  target = :mlton
elsif target == "Makefile" then
  target = :Makefile
else
  wrong_arguments
end

captured_stdio = StringIO.new('', 'w')
old_stdout = $stdout
$stdout = captured_stdio

if target == :smlnj then
  
print %{
Group is
      
cont-smlnj.sml
}

elsif target == :mlton then

print %{  
$(SML_LIB)/basis/basis.mlb
$(SML_LIB)/basis/build/sources.mlb
$(SML_LIB)/mlyacc-lib/mlyacc-lib.mlb
$(SML_LIB)/smlnj-lib/Util/smlnj-lib.mlb
$(SML_LIB)/smlnj-lib/PP/pp-lib.mlb
}

end

if target == :mlton || target == :Makefile then
  
print %{
cont-mlton.sml
}

end

print %{
enumerator.sml
util.sml
string-key.sml
list-pair-map.sml
set-util.sml
map-util.sml
unique-map.sml
region.sml
time.sml
operators.sml
}

if target == :smlnj || target == :Makefile then

print %{  
sexp/sexp.sml
sexp/sexp.grm
sexp/sexp.lex
sexp/parser.sml
parser/ast.sml
parser/timl.grm
parser/timl.lex
parser/parser.sml
}

elsif target == :mlton then

print %{  
sexp/sexp.sml
sexp/sexp.grm.sig
sexp/sexp.grm.sml
sexp/sexp.lex.sml
sexp/parser.sml
parser/ast.sml
parser/timl.grm.sig
parser/timl.grm.sml
parser/timl.lex.sml
parser/parser.sml
}

end

print %{
module-context.sml
to-string-util.sml
long-id.sml
uvar.sig
base-sorts.sml
bind.sml
visitor-util.sml                                 
unbound.sml
idx.sig
idx-visitor.sml
idx.sml
shift-util.sml
idx-trans.sml
type.sig
type-visitor.sml
type.sml
type-trans.sml
pattern.sml
pattern-visitor.sml                                 
hyp.sml
expr.sig
expr-visitor.sml                                 
expr-fn.sml
get-region.sml
base-types.sml
idx-util.sml
type-util.sml
expr-util.sml
idx-type-expr.sig
idx-type-expr-fn.sml
expr-trans.sml
simp.sml
simp-type.sml
vc.sml
equal.sml
subst.sml
long-id-subst.sml
export.sml
to-string-raw.sml
to-string-nameful.sml
to-string.sml
uvar.sml
expr.sml
underscore-exprs.sml
elaborate.sml
name-resolve.sml
package.sml
typecheck-util.sml
normalize.sml
simp-expr.sml
collect-var.sml
collect-uvar.sml
parallel-subst.sml
fresh-uvar.sml
uvar-forget.sml
unify.sml
redundant-exhaust.sml
collect-mod.sml
subst-uvar.sml
update-expr.sml
typecheck-main.sml
trivial-solver.sml
post-typecheck.sml
typecheck.sml
smt2-printer.sml
smt-solver.sml
long-id-map.sml
bigO-solver.sml
simp-ctx.sml
main.sml
pp-util.sml
micro-timl/micro-timl.sml
nouvar-expr.sml
visitor.sml                                 
micro-timl/micro-timl-visitor.sml
micro-timl/micro-timl-pp.sml
micro-timl/micro-timl-ex.sml
micro-timl/micro-timl-ex-pp.sml
pattern-ex.sml
micro-timl/micro-timl-ex-util.sml
micro-timl/post-process.sml
micro-timl/timl-to-micro-timl.sml
}

if target == :smlnj then

print %{  
$/basis.cm
$/smlnj-lib.cm
$/ml-yacc-lib.cm
$/pp-lib.cm
}

elsif target == :mlton || target == :Makefile then

print %{  
mlton-main.sml
}

end

$stdout = old_stdout
output = captured_stdio.string

output.gsub!(/#.*/, '')

print output
