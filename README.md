TiML: A Functional Programming Language with Time Complexity (Parser, Typechecker and Coq Formalization)
===========================================

Setup Instructions
-----------------------

1. Install SML/NJ. Make sure command `sml` and `ml-build` is in current PATH.
   On Ubuntu, use this command to install all necessary components of SML/NJ:
       
   ```
   sudo apt-get install smlnj libsmlnj-smlnj ml-yacc ml-ulex
   ```

2. Install the Z3 SMT solver version 4.4.1. Make sure command `z3` is in current PATH. Z3-4.4.1 is required. Z3-4.4.2 has a known issue.

3. Install Ruby. Make sure command `ruby` is in current PATH.

4. Use `make` to build TiML, or use `./test.sh` to build and test on files in [examples](examples) sub-directory.

5. (Optional). Install MLton (a whole-program optimizing SML compiler). Make sure command `mlton`, `mlyacc` and `mllex` is in current PATH. Use `make mlton` to build TiML with MLton, or use `./test-mlton.sh` to build and test on files in [examples](examples) sub-directory.

6. (Optional, requires step 5). Run `ruby benchmark.rb` in directory [examples](examples), which will generate file `result.csv` that reproduces results in Table 1 of the paper.

7. (Optional). Follow [emacs/README.rst](emacs/README.rst) to install TiML mode on Emacs.

Play with TiML
----------------------------------

[examples/test-suite.pkg](examples/test-suite.pkg) lists all the benchmark examples. You can use this command to run all the examples:

  ```
  ./main.sh examples/stdlib.pkg examples/test-suite.pkg
  ```

or this command to run a single example:

  ```
  ./main.sh examples/stdlib.pkg examples/FILENAME.timl
  ```

Note that [examples/stdlib.pkg](examples/stdlib.pkg) (the standard library) is usually needed.

Readers are advised to read the example files following the order in Table 1 of the companion paper (and in file [examples/test-suite.pkg](examples/test-suite.pkg)), as new syntax are explained in that order.

To reproduce the results in Table 1 of the companion paper, you can run

  ```
  cd examples
  ruby benchmark.rb
  ```

The results will be printed out and written to file "result.csv". Note that this experiment requires MLton, and the processing time will depend on your hardware.

Coq Proof
----------------------------------

The Coq formalization of TiML and its soundness is in [proof/Soundness.v](proof/Soundness.v). The proof requires Coq 8.5pl3. To check the proof, first compile the utility library:

  ```
  make
  ```

You can also compile the utility library and the soundness proof altogether:

  ```
  make soundness
  ```
