# TiML: A Functional Programming Language with Time Complexity (Parser and Typechecker)

-------------------------------------------------------------------------------

## Setup instructions

1. Install the Z3 SMT solver. Make sure command `z3` is in current PATH.
   Z3-4.4.1 is required. Z3-4.4.2 has a known issue.
   Install Ruby. Make sure command `ruby` is in current PATH.

2. Install SML/NJ. Make sure command `sml` and `ml-build` is in current PATH.
   On Ubuntu, use this command to install all necessary components of SML/NJ:
       
   ``
   apt-get install smlnj libsmlnj-smlnj ml-yacc ml-ulex
   ``

3. Use `make` to build TiML, or use `./test.sh` to build and test on files in `examples` sub-directory.

4. (Optional). Install MLton (a whole-program optimizing SML compiler). Make sure command `mlton`, `mlyacc` and `mllex` is in current PATH. Use `make mlton` to build TiML with MLton, or use `./test-mlton.sh` to build and test on files in `examples` sub-directory.

5. (Optional, requires step 4). Run `ruby benchmark.rb` in directory `examples`, which will generate file `result.csv` that reproduces results in the table in Section 6 of the paper.

6. (Optional). Follow `emacs/README.rst` to install TiML mode on Emacs.

-------------------------------------------------------------------------------

## Play with TiML

`examples/test-suite.pkg` lists all the benchmark examples. You can use this command to run all the examples:

  ``
  ./main.sh examples/stdlib.pkg examples/test-suite.pkg
  ``

or this command to run a single example:

  ``
  ./main.sh examples/stdlib.pkg examples/FILENAME.timl
  ``

Note that `examples/stdlib.pkg` (the standard library) is usually required.
