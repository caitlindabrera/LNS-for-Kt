Add LoadPath "../../general".
Add LoadPath "..".
Require Import cut.
Require Import Extraction.

Extraction Language Haskell.

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.

Time Separate Extraction LNSKt_cut_elimination.