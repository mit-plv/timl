.PHONY: Main.main

default: smlnj

all: smlnj mlton

mlton: main

FILES = \
cont-mlton.sml \
util.sml \
debug.sml \
region.sml \
operators.sml \
front-end/ast.sml \
front-end/timl.grm \
front-end/timl.lex \
front-end/parser.sml \
expr.sml \
uvar-expr.sml \
elaborate.sml \
underscored-subst.sml \
name-resolve.sml \
subst.sml \
trivial-solver.sml \
nouvar-expr.sml \
vc.sml \
bigO-solver.sml \
typecheck.sml \
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
	mlton -profile time main.mlb

profile:
	mlprof main mlmon.out

smlnj: main.cm
	./format.rb ml-build -Ccompiler-mc.error-non-exhaustive-match=true -Ccompiler-mc.error-non-exhaustive-bind=true main.cm Main.main main-image

clean:
	rm main
	rm main-image*
