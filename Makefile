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
module-context.sml \
to-string-util.sml \
long-id.sml \
var-uvar.sig \
base-sorts.sml \
bind.sml \
visitor-util.sml \
unbound.sml \
idx.sig \
idx-visitor.sml \
idx.sml \
shift-util.sml \
idx-trans.sml \
idx-util.sml \
type.sig \
type-visitor.sml \
type.sml \
type-trans.sml \
pattern.sml \
pattern-visitor.sml \
get-region.sml \
hyp.sml \
expr.sig \
expr-fn.sml \
expr-visitor.sml \
expr-trans.sml \
int-var.sml \
simp.sml \
vc.sml \
subst.sml \
long-id-subst.sml \
expr.sml \
underscore-exprs.sml \
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
collect-mod.sml \
simp-type.sml \
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

main.mlb: generate-file-list.rb
	ruby generate-file-list.rb mlton > main.mlb

profile:
	mlprof -show-line true -raw true main mlmon.out

smlnj: main.cm
	./format.rb ml-build -Ccontrol.poly-eq-warn=false -Ccompiler-mc.error-non-exhaustive-match=true -Ccompiler-mc.error-non-exhaustive-bind=true main.cm Main.main main-image

main.cm: generate-file-list.rb
	ruby generate-file-list.rb smlnj > main.cm

clean:
	rm -f main
	rm -f main-image*
	rm main.cm
	rm main.mlb
