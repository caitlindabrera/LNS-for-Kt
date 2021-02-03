(*
Add LoadPath "../../../../general".
Add LoadPath "../../..".
 *)
Add LoadPath "../../..".

Require Import ind_lex.
Require Import extraction_files.cygwin.Compiling_examples.mwe_attempt1.
Require Import Extraction.

Extraction Language Haskell.
(*
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
*)
Time Separate Extraction lem_ex1.
