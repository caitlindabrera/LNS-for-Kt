Add LoadPath "../general".

Require Import cut.
Require Import cut_extraction_example_pre.

Require Import Extraction.
Extraction Language Haskell.

(*
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
*)

Unset Extraction Optimize.

Time Separate Extraction cut_example3.