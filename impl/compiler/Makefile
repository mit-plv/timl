.PHONY: default all smlnj mlton clean

FILES = \
util.sml \
micro-timl-def.sig \
micro-timl-util.sig \
ast-transformers.sig \
deriv-transformers.sig \
cps-pass.sig \
wrap-abs-pass.sig \
clo-conv-pass.sig \
deriv-checker.sig \
micro-timl-hoisted-def.sig \
hoisted-deriv-checker.sig \
typed-assembly-def.sig \
micro-timl-test.sig \
micro-timl-def.sml \
micro-timl-util.sml \
ast-transformers.sml \
deriv-transformers.sml \
cps-pass.sml \
wrap-abs-pass.sml \
clo-conv-pass.sml \
deriv-checker.sml \
micro-timl-hoisted-def.sml \
hoisted-deriv-checker.sml \
typed-assembly-def.sml \
micro-timl-test.sml \
micro-timl-inst.sml \
micro-timl.grm \
micro-timl.lex \
parser.sml \
compiler.sml \
mlton-compiler.sml

default: smlnj

all: smlnj mlton

smlnj: compiler.cm
	ml-build -Ccompiler-mc.error-non-exhaustive-match=true -Ccompiler-mc.error-non-exhaustive-bind=true -Ccontrol.poly-eq-warn=false compiler.cm Compiler.main compiler-image

mlton: compiler

compiler: compiler.mlb $(FILES)
	mlyacc micro-timl.grm
	mllex micro-timl.lex
	mlton $(MLTON_FLAGS) compiler.mlb

clean:
	rm -rf .cm compiler-image* compiler
