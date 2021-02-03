Add LoadPath "../general".

Require Import Lemma_Sixteen_setup.
Require Import Lemma_Sixteen_SR_bb_fwd.
Require Import Lemma_Sixteen_SR_bb_bac.


Set Implicit Arguments.

(* ------------------- *)
(* Lemma_Sixteen_SR_bb *)
(* ------------------- *)

Lemma Lemma_Sixteen_SR_bb : forall n m,
  (forall y : nat * nat, lt_lex_nat y (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y) ->
  SR_bb (S n, m).
Proof.
  intros n m IH.
  apply SR_bb_fwd_bac_rev.
  apply Lemma_Sixteen_SR_bb_fwd. assumption.
  apply Lemma_Sixteen_SR_bb_bac. assumption.
Defined.