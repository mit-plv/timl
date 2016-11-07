make mlton MLTON_FLAGS="-profile time" && ./main examples/stdlib.pkg $(for i in {1..5}; do echo -n "examples/test-suite.pkg "; done) && make profile
