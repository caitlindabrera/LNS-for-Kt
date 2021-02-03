Add LoadPath "../general".

Require Import Lia.

Require Import Lemma_Sixteen_setup.
Require Import Lemma_Sixteen_SR_wb_fwd.
Require Import Lemma_Sixteen_SR_wb_bac.

Set Implicit Arguments.

Lemma Lemma_Sixteen_SR_wb : forall n m,
  (forall y : nat * nat, lt_lex_nat y (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y) ->
  SR_wb (S n, m).
Proof.
  intros n m IH.
  apply SR_wb_fwd_bac_rev.
  apply Lemma_Sixteen_SR_wb_fwd. assumption.
  apply Lemma_Sixteen_SR_wb_bac. assumption.
Defined.