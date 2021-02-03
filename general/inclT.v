Require Import genT.

Set Implicit Arguments.

Definition inclT {A : Type} (l m:list A) := forall a:A, InT a l -> InT a m.

Lemma inclT_consL_InT : forall {T : Type} (l1 l2 : list T) a,
    inclT (a :: l1) l2 -> (InT a l2).
Proof.
  intros until 0; intros Hincl.
  apply Hincl. econstructor. reflexivity.
Qed.

Lemma inclT_consL_inclT : forall {T : Type} (l1 l2 : list T) a,
    inclT (a :: l1) l2 -> inclT l1 l2.
Proof.
  intros until 0; intros Hincl.
  intros b Hin. apply Hincl.
  econstructor 2. assumption.
Qed.

Lemma inclT_appL : forall {T : Type} (L1 L2 L3 : list T),
    inclT L1 L3 ->
    inclT L2 L3 ->
    inclT (L1 ++ L2) L3.
Proof.
  intros T L1 L2 L3 Hincl1 Hincl2 a Hin.
  apply InT_appE in Hin.
  destruct Hin as [Hin | Hin];
    [apply Hincl1 | apply Hincl2]; assumption.             
Qed.


Lemma inclT_refl : forall {T : Type} (L : list T),
    inclT L L.
Proof. intros T L a Ha; assumption. Qed.

Lemma inclT_appL_refl : forall {T : Type} (L1 L2 : list T),
    inclT L1 (L1 ++ L2).
Proof.
  intros T L1 L2 a Ha.
  apply InT_appL. assumption.
Qed.

Lemma inclT_appRL : forall {T : Type} (L1 L2 L3 : list T),
    inclT L1 L3 ->
    inclT L1 (L2 ++ L3).
Proof.
  intros T L1 L2 L3 Hincl a Ha.
  apply InT_appR. apply Hincl. assumption.
Qed.

Ltac solve_inclT :=
  repeat
    match goal with
    | [ |- inclT (?L1 ++ ?L2) ?L3 ] => apply inclT_appL
    | [ |- inclT ?L1 ?L1 ] => apply inclT_refl
    | [ |- inclT ?L1 (?L1 ++ ?L2) ] => apply inclT_appL_refl
    | [ |- inclT ?L1 (?L2 ++ ?L3) ] => apply inclT_appRL
    end.
