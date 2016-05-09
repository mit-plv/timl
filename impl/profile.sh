make mlton && ./main examples/bool.timl $(for i in {1..50}; do echo -n "examples/rbt.timl "; done) && make profile
