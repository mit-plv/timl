default: smlnj

all: smlnj mlton

mlton: main.mlb
	mlton main.mlb

smlnj: main.cm
	ml-build main.cm Main.main main-image

clean:
	rm main
	rm main-image*
