.PHONY: Main.main

default: smlnj

all: smlnj mlton

mlton: main

FILES = \
cont-mlton.sml \
\
enumerator.sml \
util.sml \
string-key.sml \
list-pair-map.sml \
set-util.sml \
map-util.sml \
unique-map.sml \
region.sml \
operators.sml \
\
sexp/sexp.sml \
sexp/sexp.grm \
sexp/sexp.lex \
sexp/parser.sml \
parser/ast.sml \
parser/timl.grm \
parser/timl.lex \
parser/parser.sml \
\
bind.sml \
visitor-util.sml \
unbound.sml \
module-context.sml \
long-id.sml \
var-uvar.sig \
shift-util.sml \
idx.sig \
idx-visitor.sml \
idx.sml \
idx-trans.sml \
type.sig \
type-visitor.sml \
type.sml \
type-trans.sml \
datatype.sml \
pattern.sml \
expr.sig \
pattern-visitor.sml \
expr-visitor.sml \
expr-trans.sml \
expr-fn.sml \
underscore-exprs.sml \
expr.sml \
elaborate.sml \
name-resolve.sml \
package.sml \
typecheck-util.sml \
normalize.sml \
simp-expr.sml \
collect-var.sml \
collect-uvar.sml \
parallel-subst.sml \
fresh-uvar.sml \
uvar-forget.sml \
unify.sml \
redundant-exhaust.sml \
typecheck-main.sml \
trivial-solver.sml \
post-typecheck.sml \
typecheck.sml \
smt2-printer.sml \
smt-solver.sml \
long-id-map.sml \
bigO-solver.sml \
main.sml \
pp-util.sml \
micro-timl/micro-timl.sml \
nouvar-expr.sml \
visitor.sml \
micro-timl/micro-timl-visitor.sml \
micro-timl/micro-timl-pp.sml \
micro-timl/micro-timl-ex.sml \
micro-timl/micro-timl-ex-pp.sml \
pattern-ex.sml \
micro-timl/timl-to-micro-timl.sml \
\
mlton-main.sml \

main: main.mlb $(FILES)
	mlyacc parser/timl.grm
	mllex parser/timl.lex
	mlyacc sexp/sexp.grm
	mllex sexp/sexp.lex
	mlton $(MLTON_FLAGS) main.mlb

profile:
	mlprof -show-line true -raw true main mlmon.out

smlnj: main.cm
	./format.rb ml-build -Ccontrol.poly-eq-warn=false -Ccompiler-mc.error-non-exhaustive-match=true -Ccompiler-mc.error-non-exhaustive-bind=true main.cm Main.main main-image

clean:
	rm -f main
	rm -f main-image*
