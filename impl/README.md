TiML: A Functional Programming Language with Time Complexity (Parser and Typechecker)

===============================================

Setup instructions:

  1. Install the Z3 SMT solver. Make sure command 'z3' is in current PATH.
     Install Ruby. Make sure command 'ruby' is in current PATH.

  2. Install SML/NJ. Make sure command 'sml' and 'ml-build' is in current PATH.
     On Ubuntu, use this command to install all necessary components of SML/NJ:
       apt-get install smlnj libsmlnj-smlnj ml-yacc ml-ulex

  3. Use 'make' to build TiML, or use './test.sh' to build and test on files in 'examples' sub-directory.

  4 (Option). Install MLton (a whole-program optimizing SML compiler). Make sure command 'mlton', 'mlyacc' and 'mllex' is in current PATH. Use 'make mlton' to build TiML with MLton, or use './test-mlton.sh' to build and test on files in 'examples' sub-directory.

See *.timl files in 'examples' sub-directory for example TiML code.
