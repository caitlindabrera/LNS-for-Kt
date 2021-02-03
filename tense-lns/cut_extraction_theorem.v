Add LoadPath "../general".

Require Import cut.

Require Import Extraction.
Extraction Language Haskell.

(*
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
*)

Unset Extraction Optimize.

Time Separate Extraction LNSKt_cut_elimination.