default: smlnj

all: smlnj mlton

mlton : main

main: main.mlb front-end/timl.grm.sml front-end/timl.lex.sml

	mlton main.mlb
front-end/timl.grm.sig front-end/timl.grm.sml: front-end/timl.grm
	mlyacc front-end/timl.grm

front-end/timl.lex.sml: front-end/timl.lex
	mllex front-end/timl.lex

smlnj: main.cm
	ml-build main.cm Main.main main-image

clean:
	rm main
	rm main-image*
