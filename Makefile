.PHONY: Main.main

default: smlnj

all: smlnj mlton

mlton: main

FILES = $(shell ruby generate-file-list.rb Makefile)

main: main.mlb $(FILES)
	mlyacc parser/timl.grm
	mllex parser/timl.lex
	mlyacc sexp/sexp.grm
	mllex sexp/sexp.lex
	mlton $(MLTON_FLAGS) -default-ann 'nonexhaustiveMatch error' -default-ann 'redundantMatch error' main.mlb

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
	rm -f main.cm
	rm -f main.mlb

print-%  : ; @echo $* = $($*)
