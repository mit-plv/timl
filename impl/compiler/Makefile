.PHONY: Compiler.main

default: smlnj

all: smlnj

smlnj: compiler.cm
	ml-build -Ccompiler-mc.error-non-exhaustive-match=true -Ccompiler-mc.error-non-exhaustive-bind=true -Ccontrol.poly-eq-warn=false compiler.cm Compiler.main compiler-image

clean:
	rm -rf .cm compiler-image*
