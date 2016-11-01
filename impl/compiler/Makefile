.PHONY: Compiler.main

default: smlnj

all: smlnj

smlnj: compiler.cm
	ml-build -Ccompiler-mc.error-non-exhaustive-match=true -Ccompiler-mc.error-non-exhaustive-bind=true compiler.cm Compiler.main compiler-image

clean:
	rm compiler-image*
