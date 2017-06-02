.PHONY: Main.main

default: smlnj

all: smlnj mlton

mlton: main

FILES = \
cont-mlton.sml \
enumerator.sml \
util.sml \
string-key.sml \
list-pair-map.sml \
set-util.sml \
map-util.sml \
unique-map.sml \
region.sml \
sexp/sexp.sml \
sexp/sexp.grm \
sexp/sexp.lex \
sexp/parser.sml \
operators.sml \
parser/ast.sml \
parser/timl.grm \
parser/timl.lex \
parser/parser.sml \
bind.sml \
module-context.sml \
var-uvar.sml \
expr.sml \
uvar-expr.sml \
elaborate.sml \
name-resolve.sml \
trivial-solver.sml \
package.sml \
typecheck-util.sml \
normalize.sml \
collect-var.sml \
collect-uvar.sml \
parallel-subst.sml \
unify.sml \
fresh-uvar.sml \
redundant-exhaust.sml \
uvar-forget.sml \
do-typecheck.sml \
post-typecheck.sml \
typecheck.sml \
smt2-printer.sml \
smt-solver.sml \
long-id-map.sml \
bigO-solver.sml \
main.sml \
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
	./format.rb ml-build -Ccontrol.poly-eq-warn=false -Ccompiler-mc.error-non-exhaustive-match=true -Ccompiler-mc.error-non-exhaustive-bind=true -Celab.value-restriction-top-warn=false main.cm Main.main main-image

clean:
	rm main
	rm main-image*
