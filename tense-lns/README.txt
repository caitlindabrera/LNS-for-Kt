Instructions for compiling files up to and including cut.v which contains cut-elimination
=========================================================================================

1. Run "make general" which compiles all files found in ../general directory.

2. Run "make cut.vo" which compiles all files in tense-lns up to and including cut.v.




Instructions for producing and using the extracted Haskell cut-elimination procedure
====================================================================================

To run a pre-loaded extracted example:
--------------------------------------

1. Run "cut_ex" in shell which compiles all required .v files, including cut_extraction_example.v that extracts the cut-elimination function and an example to run it on.

2. Load Main_example.hs.

3. Run "cut_example4" or its definition "coq_LNSKt_cut_elimination concl4_0 example4" to produce a cut-free version of example4.



To run your own extracted example:
----------------------------------

0. In cut_extraction_example_pre.v, write up your own example following the same kind of framework as the other example/s. In cut_extraction_example.v, change the Extraction object from "cut_example4" to the name of your own example.

1. Run "cut_ex" in shell which compiles all required .v files, including cut_extraction_example.v that extracts the cut-elimination function and your example.

2. Load Main_example.hs.

3. Run your example as you would the pre-loaded example.



To extract the cut-elimination function without an example:
-----------------------------------------------------------

1. Run "cut_thm" in shell which compiles all required .v files, including cut_extraction_theorem.v that extracts the cut-elimination function.

2. Load Main_thm.hs.

3. You can run your own handwritten examples using the call "coq_LNSKt_cut_elimination".



NOTES
-----

If you'd like to use in any of the above methods the following import commands

  Require Import ExtrHaskellBasic.
  Require Import ExtrHaskellNatInt.

then uncomment them in cut_extraction_theorem.v or cut_extraction_example.v, then follow the above methods with the exception of using the "_extrlib" versions of the Main files for step 2.



The ../general directory contains .v files not needed for cut-elimination.
