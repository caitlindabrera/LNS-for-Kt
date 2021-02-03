Require Import inclT.
Require Import List_lemmasT.
Require Import gen genT gen_tacs.
Require Import existsT.

Require Import List.
Import ListNotations.

Set Implicit Arguments.

(* Contains definitions and lemmas for ... *)

Inductive weakened {T} : list T -> list T -> Type :=
  | weakened_I : forall (X Y A B C : list T), X = (A ++ C) -> 
    Y = (A ++ B ++ C) -> weakened X Y.

Lemma weakened_I': forall T (A B C D : list T),
   weakened (A ++ C) (A ++ B ++ C).
Proof.  intros.  eapply weakened_I ; reflexivity. Qed.

Inductive weakened_spec {T} : list T -> list T -> list T -> Type :=
| weakened_spec_I : forall (X Y A B C : list T),
    X = (A ++ C) -> 
    Y = (A ++ B ++ C) -> weakened_spec B X Y.

Lemma weakened_spec_weakened : forall {T : Type} (L l1 l2 : list T),
    weakened_spec L l1 l2 -> weakened l1 l2.
Proof.
  intros until 0; intros H.
  inversion H. subst. econstructor; reflexivity.
Qed.

Inductive weakened_multi {T : Type} : list T -> list T -> Type :=
| weak_multi_refl X : @weakened_multi T X X
(*| cont_multi_base X Y   : @contracted_gen T X Y -> contracted_multi X Y *)
| weak_multi_step X Y Z : @weakened T X Y -> weakened_multi Y Z -> weakened_multi X Z.

Inductive weakened_multi_enum {T : Type} : list T -> list T -> nat -> Type :=
| weak_multi_enum_refl X : @weakened_multi_enum T X X 0
(*| cont_multi_base X Y   : @contracted_gen T X Y -> contracted_multi X Y *)
| weak_multi_enum_step X Y Z n : @weakened T X Y -> weakened_multi_enum Y Z n -> weakened_multi_enum X Z (S n).

Lemma weak_multi_weak_multi_enum : forall {T : Type} (X Y : list T),
    weakened_multi X Y -> existsT2 n, weakened_multi_enum X Y n.
Proof.
  intros T X Y Hc.
  induction Hc. exists 0. eapply weak_multi_enum_refl.
  destruct IHHc as [n IH].
  exists (S n). eapply weak_multi_enum_step.
  eapply w. apply IH.
Qed.

Lemma weak_multi_weak_multi_enum_rev : forall {T : Type} (X Y : list T) n,
    weakened_multi_enum X Y n -> weakened_multi X Y.
Proof.
  intros T X Y n Hc.
  induction Hc. eapply weak_multi_refl.
  eapply weak_multi_step. eapply w.
  assumption.
Qed.

Inductive weakened_seqL {T1 T2 : Type} : ((list T1) * (list T1) * T2) -> ((list T1) * (list T1) * T2) -> Type :=
| weak_seqL X Y Δ d : weakened_multi X Y -> weakened_seqL (X,Δ,d) (Y,Δ,d).

Inductive weakened_seqR {T1 T2 : Type} : ((list T1) * (list T1) * T2) -> ((list T1) * (list T1) * T2) -> Type :=
| weak_seqR X Y Γ d : weakened_multi X Y -> weakened_seqR (Γ,X,d) (Γ,Y,d).

Inductive weakened_seq {T1 T2 : Type} : ((list T1) * (list T1) * T2) -> ((list T1) * (list T1) * T2) -> Type :=
| weak_seq_baseL s1 s2 : weakened_seqL s1 s2 -> weakened_seq s1 s2
| weak_seq_baseR s1 s2  : weakened_seqR s1 s2 -> weakened_seq s1 s2
| weak_seq_baseLR s1 s2 s3 : weakened_seqL s1 s2 -> weakened_seqR s2 s3 -> weakened_seq s1 s3.

Inductive weakened_nseq {T1 T2 : Type} : list ((list T1) * (list T1) * T2) -> list ((list T1) * (list T1) * T2) -> Type :=
| weak_nseq_nil  : weakened_nseq [] []
| weak_nseq_cons s1 s2 ns1 ns2 : weakened_seq s1 s2 -> weakened_nseq ns1 ns2 ->
                                 weakened_nseq (s1::ns1) (s2::ns2).

Lemma weakened_cons : forall {T : Type} Y Z (a : T),
    weakened Y Z ->
    weakened (a :: Y) (a :: Z).
Proof.
  intros until 0; intros Hc; inversion Hc; subst.
  rewrite ?app_comm_cons.
  econstructor. reflexivity.
  reflexivity.
Qed.

Lemma weakened_multi_cons : forall {T : Type} Y Z (a : T),
    weakened_multi Y Z ->
    weakened_multi (a :: Y) (a :: Z).
Proof.
  intros until 0; intros Hc.
  induction Hc. subst. eapply weak_multi_refl.
  subst.
  eapply weak_multi_step. eapply weakened_cons.
  eapply w.
  assumption.
Qed.

Lemma weakened_multi_cons_tl : forall {T : Type} Y Z (a : T),
    weakened_multi Y Z ->
    weakened_multi (Y ++ [a]) (Z ++ [a]).
Proof.
  intros until 0; intros Hc.
  induction Hc. eapply weak_multi_refl.
  inversion w. subst. 
  eapply weak_multi_step.
  list_assoc_r'. simpl. eapply weakened_I.
  reflexivity. reflexivity.
  do 2 rewrite <- app_assoc in IHHc. eassumption.
Qed.

Lemma weakened_multi_L : forall {T : Type} (X Y Z : list T),
    weakened_multi Y Z ->
    weakened_multi (X ++ Y) (X ++ Z).
Proof.
  induction X; intros Y Z Hc. assumption.
  simpl. eapply weakened_multi_cons.
  apply IHX. apply Hc.
Qed.

Lemma weakened_multi_R : forall {T : Type} (X Y Z : list T),
    weakened_multi Y Z ->
    weakened_multi (Y ++ X) (Z ++ X).
Proof.
  induction X; intros Y Z Hc. do 2 rewrite app_nil_r. assumption.
  rewrite cons_singleton. do 2 rewrite app_assoc.
  eapply IHX. eapply weakened_multi_cons_tl. assumption.
Qed.

Lemma weakened_multi_same : forall { T : Type} (X Y : list T),
    X = Y -> weakened_multi X Y.
Proof.  intros. subst. econstructor. Qed.

Lemma weakened_seq_refl : forall {T1 T2 : Type} s,
    @weakened_seq T1 T2 s s.
Proof.
  intros T1 T2 [[Γ Δ] d].
  econstructor. econstructor.
  econstructor.
Qed.

Lemma weakened_nseq_refl : forall {T1 T2 : Type} ns,
    @weakened_nseq T1 T2 ns ns.
Proof.
  induction ns. constructor.
  constructor. apply weakened_seq_refl.
  assumption.
Qed.

Lemma weak_appL : forall {T : Type} (X Y : list T),
    weakened X (X ++ Y).
Proof.
  intros.  rewrite <- (app_nil_r Y).
  rewrite <- (app_nil_r X).
  econstructor. reflexivity.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma weak_appR : forall {T : Type} (X Y : list T),
    weakened Y (X ++ Y).
Proof.
  intros.  rewrite <- (app_nil_l X).
  rewrite <- (app_nil_l Y).
  econstructor. reflexivity.
  simpl. reflexivity.
Qed.

Lemma weakened_nseq_app : forall {T1 T2 : Type} l1 l2 l3 l4,
  @weakened_nseq T1 T2 l1 l3 ->
  weakened_nseq l2 l4 ->
  weakened_nseq (l1 ++ l2) (l3 ++ l4).
Proof.
  induction l1; intros l2 l3 l4 H1 H2.
  simpl in *. inversion H1. assumption.
  inversion H1. subst. simpl.
  econstructor. assumption.
  apply IHl1; assumption.
Qed.

Lemma weakened_consL : forall {T : Type} (A : list T) b,
    weakened A (b :: A).
Proof.
  intros.
  list_assoc_r_single.
  econstructor. erewrite app_nil_l. reflexivity.
  rewrite app_nil_l. reflexivity.
Qed.

Lemma weakened_multi_consL : forall {T : Type} (A : list T) b,
    weakened_multi A (b :: A).
Proof.
  intros. econstructor.
  2 : econstructor. eapply weakened_consL.
Qed.
  
Lemma weakened_multi_appL : forall {T : Type} (A B : list T),
    weakened_multi A (B ++ A).
Proof.
  induction B. econstructor.
  simpl. econstructor.
  eapply weakened_consL.
  eapply weakened_multi_cons.
  assumption.
Qed.

Lemma weak_same: forall T X, weakened X (X : list T).
Proof.
  intros. apply (weakened_I [] [] X); reflexivity.
Qed.

Lemma weak_L: forall T X Y Z,
  weakened X (Y : list T) -> weakened (Z ++ X) (Z ++ Y).
Proof.  intros. destruct X0. subst. 
  rewrite !(app_assoc Z). apply weakened_I'. auto. Qed.

Lemma weak_R: forall T X Y Z,
  weakened X (Y : list T) -> weakened (X ++ Z) (Y ++ Z).
Proof.
  intros. destruct X0. subst. rewrite <- !app_assoc.
  apply weakened_I'. auto.
Qed.

Lemma weak_cons: forall T (x : T) Y Z,
  weakened Y Z -> weakened (x :: Y) (x :: Z).
Proof.  intros. destruct X. subst. list_assoc_l. rewrite <- !app_assoc.
  apply weakened_I'. auto. Qed.

Lemma weak_simpleRX : forall T (A B : list T),
    weakened A (A ++ B).
Proof.
  intros. apply (weakened_I A B []);
            list_app_nil; reflexivity.
Qed.

Lemma weak_simpleLX : forall T (A B : list T),
    weakened A (B ++ A).
Proof.
  intros. apply (weakened_I [] B A);
            list_app_nil; reflexivity.
Qed.

Ltac weak_tacX :=
 list_assoc_r ; try (apply weak_same) ; 
    repeat (apply weak_L || apply weak_cons) ;  
    list_assoc_l ; repeat (apply weak_R); try apply weak_simpleRX;
    try apply weak_simpleLX.

Lemma weakened_multi_appR : forall {T : Type} (A B : list T),
    weakened_multi A (A ++ B).
Proof.
  intros. revert A. induction B; intros A.
  rewrite app_nil_r. econstructor.
  econstructor;
  [| list_assoc_r_single; list_assoc_l;
  eapply IHB].
  weak_tacX.
Qed.

Lemma weakened_seq_appL : forall {T1 T2 : Type} (A B l1 l2 : list T1) (d : T2),
    weakened_seq (A, B, d) (l1 ++ A, l2 ++ B, d).
Proof.
  intros.
  eapply weak_seq_baseLR;
    econstructor.
  eapply weakened_multi_appL.
  eapply weakened_multi_appL.
Qed.

Lemma weakened_nseq_app_sameL:
  forall {T1 T2 : Type} (l1 l2 l3 : list (list T1 * list T1 * T2)),
    weakened_nseq l2 l3 -> weakened_nseq (l1 ++ l2) (l1 ++ l3).
Proof.
  intros.
  eapply weakened_nseq_app.
  eapply weakened_nseq_refl.
  assumption.
Qed.

Lemma weakened_nseq_app_sameR:
  forall {T1 T2 : Type} (l1 l2 l3 : list (list T1 * list T1 * T2)),
    weakened_nseq l2 l3 -> weakened_nseq (l2 ++ l1) (l3 ++ l1).
Proof.
  intros.
  eapply weakened_nseq_app.
  assumption.
  eapply weakened_nseq_refl.
Qed.

Lemma weakened_multi_enum_trans : forall {T : Type} n m X Y Z,
         weakened_multi_enum X Y n ->
         weakened_multi_enum Y Z m ->
         @weakened_multi_enum T X Z (n + m)%nat.
Proof.
  induction n; intros m X Y Z H1 H2.  
  simpl in *. inversion H1. subst. assumption.
  inversion H1. subst. simpl.
  econstructor. eassumption.
  eapply IHn; eassumption.
Qed. 
  
Lemma weakened_multi_trans : forall {T : Type} X Y Z,
         weakened_multi X Y ->
         weakened_multi Y Z ->
         @weakened_multi T X Z.
Proof.
  intros T X Y Z H1 H2.
  eapply weak_multi_weak_multi_enum in H1.
  eapply weak_multi_weak_multi_enum in H2.
  sD.
  eapply weak_multi_weak_multi_enum_rev.
  eapply weakened_multi_enum_trans; eassumption.
Qed.

Lemma weakened_seqL_trans : forall {T1 T2 : Type} l1 l2 l3,
    weakened_seqL l1 l2 ->
    weakened_seqL l2 l3 ->
    @weakened_seqL T1 T2 l1 l3.
Proof.
  intros T1 T2 l1 l2 l3 H1 H2.
  inversion H1. inversion H2.
  subst. inversion_pair.
  econstructor.
  eapply weakened_multi_trans;
    eassumption.
Qed.

Lemma weakened_seqR_trans : forall {T1 T2 : Type} l1 l2 l3,
    weakened_seqR l1 l2 ->
    weakened_seqR l2 l3 ->
    @weakened_seqR T1 T2 l1 l3.
Proof.
  intros T1 T2 l1 l2 l3 H1 H2.
  inversion H1. inversion H2.
  subst. inversion_pair.
  econstructor.
  eapply weakened_multi_trans;
    eassumption.
Qed.

Lemma weakened_multi_appLR : forall {T : Type} l1 l2 l3,
    @weakened_multi T l1 (l2 ++ l1 ++ l3).
Proof.
  intros.
  eapply (@weak_multi_step _ _ (l2 ++ l1)).
  weak_tacX.
  eapply weak_multi_step; [ | eapply weak_multi_refl].
  weak_tacX.
Qed.

Lemma weakened_multi_enum_L:
  forall (T : Type) n (X Y Z : list T),
    weakened_multi_enum Y Z n -> weakened_multi_enum (X ++ Y) (X ++ Z) n.
Proof.
  induction n; intros X Y Z H.
  inversion H. subst. econstructor.
  inversion H. subst. eapply IHn in X2.
  econstructor; [ | eapply X2].
  weak_tacX. assumption.
Qed.

Lemma weakened_multi_enum_R:
  forall (T : Type) n (X Y Z : list T),
    weakened_multi_enum Y Z n -> weakened_multi_enum (Y ++ X) (Z ++ X) n.
Proof.
  induction n; intros X Y Z H.
  inversion H. subst. econstructor.
  inversion H. subst. eapply IHn in X2.
  econstructor; [ | eapply X2].
  weak_tacX. assumption.
Qed.

Lemma weakened_multi_enum_app : forall {T : Type} n m l1 l2 l3 l4,
    weakened_multi_enum l1 l2 n ->
    weakened_multi_enum l3 l4 m ->
    @weakened_multi_enum T (l1 ++ l3) (l2 ++ l4) (n + m).
Proof.
  induction n; intros m l1 l2 l3 l4 H1 H2.
  inversion H1. subst. simpl.
  eapply weakened_multi_enum_L. eassumption.
  
  inversion H1. subst.
  simpl. econstructor;
           [ | eapply IHn; eassumption] .
  weak_tacX. assumption.
Qed.

Lemma weakened_multi_app : forall {T : Type} l1 l2 l3 l4,
    weakened_multi l1 l2 ->
    weakened_multi l3 l4 ->
    @weakened_multi T (l1 ++ l3) (l2 ++ l4).
Proof.
  intros until 0; intros H1 H2.
  
  eapply weak_multi_weak_multi_enum in H1.
  eapply weak_multi_weak_multi_enum in H2.
  sD.
  eapply weak_multi_weak_multi_enum_rev.
  eapply weakened_multi_enum_app; eassumption.
Qed.


Lemma weakened_multi_app_lem  : forall {T : Type} l1 l2 l3 l4,
    weakened_multi l2 l4 ->
    @weakened_multi T (l1 ++ l2) (l3 ++ l1 ++ l4).
Proof.
  intros until 0; intros H.
  rewrite (app_assoc l3).
  eapply weakened_multi_app.
  econstructor; [ | econstructor].
  weak_tacX.
  eassumption.
Qed.


Ltac weakened_nseq_solve_nseq :=
  repeat match goal with
         | [ |- weakened_nseq [] [] ] => eapply weak_nseq_nil
         | [ |- weakened_nseq (?l1 ++ ?l2) (?l1 ++ ?l3) ] => eapply weakened_nseq_app_sameL
         | [ |- weakened_nseq (?l2 ++ ?l1) (?l3 ++ ?l1) ] => eapply weakened_nseq_app_sameR
         | [ |- weakened_nseq (?a1 :: ?l1) (?a2 :: ?l2) ] => eapply weak_nseq_cons
         end.

Ltac weakened_seq_solve :=
  repeat match goal with
         | [ |- weakened_seq (?L1, ?L2, ?d) (?L1, ?L3, ?d) ] => eapply weak_seq_baseR; econstructor
         | [ |- weakened_seq (?L1, ?L2, ?d) (?L3, ?L2, ?d) ] => eapply weak_seq_baseL; econstructor
         | [ |- weakened_seq _ _ ] => eapply weak_seq_baseLR; econstructor
         end.


Ltac weakened_multi_gen Γ Σ :=
  match Γ with
  | ?Γ1 ++ ?Γ2 => assoc_mid_loc Γ1; eapply weakened_multi_app_lem
  end.

Ltac weakened_multi_solve_pre :=
  repeat match goal with
         | [ |- weakened_multi ?Γ ?Γ ] => eapply weak_multi_refl
         | [ |- weakened_multi (?Γ ++ ?Σ) (?Γ ++ ?Π) ] => eapply weakened_multi_L
         | [ |- weakened_multi (?Γ ++ ?Σ) (?Π ++ ?Σ) ] => eapply weakened_multi_L
         | [ |- weakened_multi ?Γ (?Σ ++ ?Γ) ] => eapply weak_multi_step; [ | eapply weak_multi_refl]
         | [ |- weakened_multi ?Γ (?Γ ++ ?Σ) ] => eapply weak_multi_step; [ | eapply weak_multi_refl]
         | [ |- weakened_multi ?Γ ?Σ ] =>
           match Σ with
           | context [ Γ ] => assoc_mid_loc Γ; eapply weakened_multi_appLR
           | _ => weakened_multi_gen Γ Σ
           end
         | [ |- weakened _ _ ] => weak_tacX
         end.

Ltac weakened_multi_solve :=
  repeat (progress (list_assoc_r_single; weakened_multi_solve_pre) ||
          (progress (list_assoc_l; weakened_multi_solve_pre))).

  Ltac weakened_nseq_solve :=
  weakened_nseq_solve_nseq; 
  weakened_seq_solve; 
  weakened_multi_solve.
