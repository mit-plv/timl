make mlton MLTON_FLAGS="-profile time" && ./main -l examples/stdlib.pkg $(for i in {1..1}; do echo -n "examples/test-suite.pkg "; done) && make profile
