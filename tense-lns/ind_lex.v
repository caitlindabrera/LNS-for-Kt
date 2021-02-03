Add LoadPath "../general".

Require Import Lia.

(* TACTICS *)

Ltac clear_useless_refl :=
  repeat match goal with
         | [H : ?a = ?a |- _] => clear H
         end.

Ltac inversion_pair_refl :=
  repeat (clear_useless_refl; match goal with
  | [ H : (?a,?b)=(?c,?d) |- _ ] => inversion H; subst
  end; clear_useless_refl).


(* Lexicographic ordering on pairs of natural numbers *)
Inductive lt_lex_nat : (nat * nat) -> (nat * nat) -> Prop :=
| le_lex_nat_fst p q a b n m : p = (a,b) -> q = (n,m) -> a < n -> lt_lex_nat p q
| le_lex_nat_snd p q a b n m : p = (a,b) -> q = (n,m) -> a = n -> b < m -> lt_lex_nat p q.

Infix "<<" := lt_lex_nat (at level 70, no associativity).

Theorem wf_lt_lex_nat : well_founded lt_lex_nat.
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

Definition wf_lt_lex_nat_inductionT := well_founded_induction_type wf_lt_lex_nat.

Definition wf_lt_inductionT := well_founded_induction_type Wf_nat.lt_wf.