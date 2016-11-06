.PHONY: Main.main

default: smlnj

all: smlnj mlton

mlton: main

FILES = \
cont-mlton.sml \
util.sml \
region.sml \
operators.sml \
front-end/ast.sml \
front-end/timl.grm \
front-end/timl.lex \
front-end/parser.sml \
bind.sml \
var-uvar.sml \
expr.sml \
uvar-expr.sml \
elaborate.sml \
name-resolve.sml \
trivial-solver.sml \
nouvar-expr.sml \
vc.sml \
bigO-solver.sml \
typecheck.sml \
post-typecheck.sml \
sexp/sexp.sml \
sexp/sexp.grm \
sexp/sexp.lex \
sexp/parser.sml \
smt2-printer.sml \
smt-solver.sml \
main.sml \
mlton-main.sml \

main: main.mlb $(FILES)
	mlyacc front-end/timl.grm
	mllex front-end/timl.lex
	mlyacc sexp/sexp.grm
	mllex sexp/sexp.lex
	mlton $(MLTON_FLAGS) time main.mlb

profile:
	mlprof -show-line true -raw true main mlmon.out

smlnj: main.cm
	./format.rb ml-build -Ccompiler-mc.error-non-exhaustive-match=true -Ccompiler-mc.error-non-exhaustive-bind=true main.cm Main.main main-image

clean:
	rm main
	rm main-image*
