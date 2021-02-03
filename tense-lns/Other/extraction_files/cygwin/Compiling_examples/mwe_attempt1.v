Add LoadPath "../../..".

(* Require Import ind_lex_min. *)
Require Import Lia.

Inductive eqT {A : Type} (x : A) : A -> Type :=  eq_reflT : eqT x x.

Print lt.
Print le.

Inductive leT (n : nat) : nat -> Type :=
  le_nT : leT n n | le_ST : forall m : nat, leT n m -> leT n (S m).
                                                          
Definition ltT := fun n m : nat => leT (S n) m.

Inductive lt_lex_natT : (nat * nat) -> (nat * nat) -> Type :=
| le_lex_nat_fstT p q a b n m : eqT p (a,b) -> eqT q (n,m) -> ltT a n -> lt_lex_natT p q
| le_lex_nat_sndT p q a b n m : eqT p (a,b) -> eqT q (n,m) -> eqT a n -> ltT b m -> lt_lex_natT p q.


Inductive lt_lex_nat : (nat * nat) -> (nat * nat) -> Prop :=
| le_lex_nat_fst p q a b n m : p = (a,b) -> q = (n,m) -> a < n -> lt_lex_nat p q
| le_lex_nat_snd p q a b n m : p = (a,b) -> q = (n,m) -> a = n -> b < m -> lt_lex_nat p q.

(* found elsewhere *)
Ltac clear_useless_refl :=
  repeat match goal with
         | [H : ?a = ?a |- _] => clear H
         end.

(* found elsewhere *)
Ltac inversion_pair_refl :=
  repeat (clear_useless_refl; match goal with
  | [ H : (?a,?b)=(?c,?d) |- _ ] => inversion H; subst
  end; clear_useless_refl).


Theorem wf_le_lex_nat : well_founded lt_lex_nat.
Proof.
  unfold well_founded.
  intros a. destruct a as [a b].
  revert b.
  induction a; intros b.
  + induction b. constructor. intros [n m] H.
    inversion H. inversion_pair_refl.
    contradiction (PeanoNat.Nat.nlt_0_r _ H2).
    inversion_pair_refl.
    contradiction (PeanoNat.Nat.nlt_0_r _ H3).
    constructor. intros [n m] H. inversion H. subst.
    inversion H1. subst.
    contradiction (PeanoNat.Nat.nlt_0_r _ H2).
    inversion_pair_refl.
    destruct (PeanoNat.Nat.eq_dec b0 b). subst.
    assumption.
    apply IHb.
    econstructor 2; try reflexivity.
    lia.

  + induction b. econstructor.
    intros [n m] H. inversion H. inversion_pair_refl.
    destruct (PeanoNat.Nat.eq_dec a0 a). subst.
    apply IHa.
    eapply IHa. econstructor; try reflexivity. lia.
    inversion_pair_refl. lia.

    inversion IHb as [H].
    constructor. intros [n m] H2.
    inversion H2. inversion_pair_refl.
    destruct (PeanoNat.Nat.eq_dec a0 a). subst. apply IHa.
    eapply IHa. econstructor; try reflexivity. lia.
    inversion_pair_refl. 
    specialize (IHa b0).

    destruct (PeanoNat.Nat.eq_dec b0 b).
    subst. assumption.
    apply H. econstructor 2; try reflexivity. lia.
    Unshelve. all : exact 0.
Qed. 

Definition wf_le_lex_nat_induction := well_founded_induction_type wf_le_lex_nat.

Infix "<<" := lt_lex_nat (at level 70, no associativity).

Lemma lt_lex_nat_lem1 : forall n m1 m2,
    (n,m1) << (S n, m2).
Proof. intros. econstructor; firstorder. Qed.


Lemma lem : forall nm : nat * nat,
    sum ((0, 0) << nm) (eqT (fst nm) 0).
Proof.
  induction nm using wf_le_lex_nat_induction;
    destruct nm as [n m].
  Show Proof.
  destruct n. right. reflexivity.
  left. econstructor; try reflexivity.
  lia.
Defined.

Definition ex1 := (0,0).
Definition ex2 := (2,0).
Definition ex3 := (2,5).

Definition lem_ex1 := lem ex1.
Check lem_ex1.
Locate "+".
Print sum.
Check (forall nm : nat * nat,
          ((0, 0) << nm) + (fst nm = 0)).

Lemma lem2 : forall nm : nat * nat,
    sum  (eqT (fst nm) 0) ((0, 0) << nm).
Proof.
  intros nm.
  pose (lem nm) as H.
  destruct H as [H | H].
  right. apply H.
  left. apply H.
Defined.


Lemma lem3 : forall A : Prop, sum (A) Type.
Proof.
  right. exact nat.
Defined.
Print lem3.
Check (forall A : Prop, sum (A) Type).
Definition lem4 : forall A : Prop, lem3 A.
Lemma lem4 : forall n : nat, sum Type (n = n)
  
  
Require Import Extraction.

Extraction Language Haskell.
(*
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
*)
Time Separate Extraction lem2.