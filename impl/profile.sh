make mlton && ./main examples/stdlib.pkg $(for i in {1..5}; do echo -n "examples/test-suite.pkg "; done) && make profile
