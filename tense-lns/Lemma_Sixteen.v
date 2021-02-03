Add LoadPath "../general".

Require Import Lemma_Sixteen_setup.
Require Import Lemma_Sixteen_SR_wb.
Require Import Lemma_Sixteen_SR_bb.
Require Import Lemma_Sixteen_SR_p.
Require Import Lemma_Sixteen_SL.


Set Implicit Arguments.


(* ----------------------- *)
(* Lemma_Sixteen_base_case *)
(* ----------------------- *)

Lemma SR_wb_base : forall m, SR_wb (0,m).
Proof.
  intros m. unfold SR_wb. unfold SR_wb_pre.
  intros until 0. intros Hprinc Hdp Hstr Hm Hex Hsize.
  apply Le.le_n_0_eq in Hsize.
  simpl in Hsize. discriminate.
Qed.

Lemma SR_bb_base : forall m, SR_bb (0, m).
Proof.
  intros m. unfold SR_bb. unfold SR_bb_pre.
  intros until 0. intros Hprinc Hdp Hstr Hm Hex Hsize.
  apply Le.le_n_0_eq in Hsize.
  simpl in Hsize. discriminate.
Qed.

Lemma SR_p_base : forall m, SR_p (0, m).
Proof.
  intros m. unfold SR_p. unfold SR_p_pre.
  intros until 0. intros Hprinc Hdp Hsize Hnb Hstr Hm.
  apply Le.le_n_0_eq in Hsize.
  symmetry in Hsize. apply fsize_not_0 in Hsize.
  contradiction.
Qed.

Lemma SL_base : forall m, SL (0, m).
Proof.
  intros m. unfold SL. unfold SL_pre.
  intros until 0. intros Hdp Hsize Hm.
  apply Le.le_n_0_eq in Hsize.
  symmetry in Hsize. apply fsize_not_0 in Hsize.
  contradiction.
Qed.

Lemma Lemma_Sixteen_base_case : forall m,
    SR_wb (0, m) * SR_bb (0, m) * SR_p (0, m) * SL (0, m).
Proof.
  intros m. split.
  split. split.
  apply SR_wb_base.
  apply SR_bb_base.
  apply SR_p_base.
  apply SL_base.
Defined.

(* ------------- *)
(* Lemma_Sixteen *)
(* ------------- *)

Lemma Lemma_Sixteen : forall (nm : nat * nat),
    SR_wb nm *
    SR_bb nm *
    SR_p  nm *
    SL    nm.
Proof.
  intros nm.
  induction nm using wf_lt_lex_nat_inductionT.
  destruct nm as [n m].
  destruct n.
  apply Lemma_Sixteen_base_case.
  assert (SR_wb (S n, m)) as HSRwb.
  apply Lemma_Sixteen_SR_wb. assumption.
  assert (SR_bb (S n, m)) as HSRbb.
  apply Lemma_Sixteen_SR_bb. assumption.
  assert (SR_p (S n, m)) as HSRp.
  apply Lemma_Sixteen_SR_p; assumption.
  assert (SL (S n, m)) as HSL.
  apply Lemma_Sixteen_SL; assumption.
  repeat split; assumption.
Defined.