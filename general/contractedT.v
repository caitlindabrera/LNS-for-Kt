Require Import inclT.
Require Import List_lemmasT.
Require Import genT gen_tacs.
Require Import existsT.

Require Import List.
Import ListNotations.

Set Implicit Arguments.

(* Contains definitions and lemmas for ... *)

Inductive contracted {T} : list T -> list T -> Type :=
  | contracted_I : forall a (X Y A B : list T), X = (A ++ [a;a] ++ B) -> 
    Y = (A ++ [a] ++ B) -> contracted X Y.

Lemma contracted_I': forall T a (A B : list T),
   contracted (A ++ [a;a] ++ B) (A ++ [a] ++ B).
Proof.  intros.  eapply contracted_I ; reflexivity. Qed.

Inductive contracted_gen {T} : list T -> list T -> Type :=
| contracted_genL_I : forall a (X Y A B C : list T),
    X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ [a] ++ B ++ C) -> contracted_gen X Y
| contracted_genR_I : forall a (X Y A B C : list T),
    X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ B ++ [a] ++ C) -> contracted_gen X Y.

Inductive contracted_gen_spec {T} (a : T) : list T -> list T -> Type :=
| contracted_genL_spec_I : forall (X Y A B C : list T),
    X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ [a] ++ B ++ C) -> contracted_gen_spec a X Y
| contracted_genR_spec_I : forall (X Y A B C : list T),
    X = (A ++ [a] ++ B ++ [a] ++ C) -> 
    Y = (A ++ B ++ [a] ++ C) -> contracted_gen_spec a X Y.

Lemma contracted_genL_I': forall T a (A B C : list T),
   contracted_gen (A ++ [a] ++ B ++ [a] ++ C) (A ++ [a] ++ B ++ C).
Proof.  intros.  eapply contracted_genL_I ; reflexivity. Qed.

Lemma contracted_genR_I': forall T a (A B C : list T),
   contracted_gen (A ++ [a] ++ B ++ [a] ++ C) (A ++ B ++ [a] ++ C).
Proof.  intros.  eapply contracted_genR_I ; reflexivity. Qed.

Lemma contracted_genR_spec_I': forall T a (A B C : list T),
   contracted_gen_spec a (A ++ [a] ++ B ++ [a] ++ C) (A ++ B ++ [a] ++ C).
Proof.  intros.  eapply contracted_genR_spec_I ; reflexivity. Qed.

Lemma contracted_genL_spec_I': forall T a (A B C : list T),
   contracted_gen_spec a (A ++ [a] ++ B ++ [a] ++ C) (A ++ [a] ++ B ++ C).
Proof.  intros.  eapply contracted_genL_spec_I ; reflexivity. Qed.

Lemma contracted_gen_spec_contracted_gen : forall {T} (a : T) l1 l2,
    contracted_gen_spec a l1 l2 -> contracted_gen l1 l2.
Proof.
  intros until 0; intros H. inversion H;
  [eapply contracted_genL_I |
   eapply contracted_genR_I].
  1,3 : apply H0.
  all : apply H1.
Qed.

(* ------------------- *)
(* CONTRACTION TACTICS *)
(* ------------------- *)

Lemma cont_L: forall T X Y Z,
  contracted X (Y : list T) -> contracted (Z ++ X) (Z ++ Y).
Proof.
  intros until 0; intros H. destruct H. subst. 
  rewrite !(app_assoc Z). apply contracted_I'.
Qed.

Lemma cont_R: forall T X Y Z,
  contracted X (Y : list T) -> contracted (X ++ Z) (Y ++ Z).
Proof.
  intros until 0; intros H. destruct H. subst.
  rewrite <- !app_assoc. apply contracted_I'. 
Qed.

Lemma cont_gen_L: forall T X Y Z,
  contracted_gen X (Y : list T) -> contracted_gen (Z ++ X) (Z ++ Y).
Proof.
  intros until 0; intros H. destruct H; subst; rewrite !(app_assoc Z).
  apply contracted_genL_I'.
  apply contracted_genR_I'.
Qed.

Lemma cont_gen_R: forall T X Y Z,
  contracted_gen X (Y : list T) -> contracted_gen (X ++ Z) (Y ++ Z).
Proof.
  intros until 0; intros H. destruct H; subst; rewrite <- !app_assoc.
  apply contracted_genL_I'. 
  apply contracted_genR_I'. 
Qed.

Lemma cont_gen_spec_basic : forall T (a : T),
    contracted_gen_spec a ([a]++[a]) [a].
Proof.
  intros. change ([a] ++ [a]) with ([] ++ [a] ++ [] ++ [a] ++ []).
  change ([a]) with ([] ++ [a] ++ [] ++ []) at 3.
  apply contracted_genL_spec_I'.
Qed.
  
Lemma cont_gen_spec_L: forall T a X Y Z,
  contracted_gen_spec a X (Y : list T) -> contracted_gen_spec a (Z ++ X) (Z ++ Y).
Proof.
  intros until 0; intros H. destruct H; subst; rewrite !(app_assoc Z).
  apply contracted_genL_spec_I'.
  apply contracted_genR_spec_I'.
Qed.

Lemma cont_gen_spec_R: forall T a X Y Z,
  contracted_gen_spec a X (Y : list T) -> contracted_gen_spec a (X ++ Z) (Y ++ Z).
Proof.
  intros until 0; intros H. destruct H; subst; rewrite <- !app_assoc.
  apply contracted_genL_spec_I'. 
  apply contracted_genR_spec_I'. 
Qed.

Lemma cont_gen_spec_rem_sml_L : forall T (a : T) Z,
    contracted_gen_spec a ([a] ++ Z ++ [a]) ([a] ++ Z).
Proof.
  intros.
  change ([a] ++ Z ++ [a]) with ([] ++ [a] ++ Z ++ [a] ++ []).
  replace ([a] ++ Z) with ([] ++ [a] ++ Z ++ []).
  apply contracted_genL_spec_I'. rewrite app_nil_r. reflexivity.
Qed.

Lemma cont_gen_spec_rem_sml_R : forall T (a : T) Z,
    contracted_gen_spec a ([a] ++ Z ++ [a]) (Z ++ [a]).
Proof.
  intros.
  change ([a] ++ Z ++ [a]) with ([] ++ [a] ++ Z ++ [a] ++ []).
  change (Z ++ [a]) with ([] ++ Z ++ [a] ++ []).
  apply contracted_genR_spec_I'.
Qed.

Lemma cont_cons: forall T (x : T) Y Z,
  contracted Y Z -> contracted (x :: Y) (x :: Z).
Proof.
  intros until 0; intros H. inversion H.
  subst. list_assoc_l.
  rewrite <- !app_assoc. apply contracted_I'.
Qed.

Lemma contracted_gen_in1: forall {T} (a : T) A Γ1 C H5,
    InT a C ->
 contracted_gen (A ++ [a] ++ Γ1 ++ C ++ H5) (A ++ Γ1 ++ C ++ H5).
Proof.
  intros until 0; intros H. apply InT_split in H.
  destruct H as [l1 [l2 H]].
  subst.  list_assoc_r'.
  simpl.
  do 2 change (a :: (?x ++ ?y)) with ([a] ++ (x ++ y)).
  eapply contracted_genR_I.
  do 2 apply applI.
  rewrite app_assoc.  reflexivity.
  list_assoc_r'. reflexivity.
Qed.

Lemma contracted_gen_in2: forall {T} (a : T) A Γ1 C,
    InT a Γ1 ->
 contracted_gen (A ++ [a] ++ Γ1 ++ C) (A ++ Γ1 ++ C).
Proof.
  intros until 0; intros H. apply InT_split in H.
  destruct H as [l1 [l2 H]].
  subst.   list_assoc_r'.
  simpl.
  change (a :: ?x) with ([a] ++ x).
  eapply contracted_genR_I.
  do 3 apply applI.
  2 : do 3 apply applI.
  all : reflexivity.
Qed.

Lemma contracted_gen_in3: forall {T} (a : T) A Γ1 C,
    InT a Γ1 ->
contracted_gen (A ++ Γ1 ++ [a] ++ C) (A ++ Γ1 ++ C).
Proof.
  intros until 0; intros H. apply InT_split in H.
  destruct H as [l1 [l2 H]].
  subst.   list_assoc_r'.
  simpl.
  change (a :: ?x) with ([a] ++ x).
  eapply contracted_genL_I.
  rewrite app_assoc.
  do 3 apply applI. reflexivity.
  apps_eq_tac.
Qed.

Lemma contracted_gen_in4: forall {T} (a : T) A Γ1 H5 C,
    InT a Γ1 ->
    contracted_gen (A ++ Γ1 ++ H5 ++ [a] ++ C) (A ++ Γ1 ++ H5 ++ C).
Proof.
  intros until 0; intros H. apply InT_split in H.
  destruct H as [l1 [l2 H]].
  subst.
  change (a :: ?x) with ([a] ++ x).
  assoc_mid [a].
  eapply contracted_genL_I.
  do 2 apply applI.
  assoc_mid [a]. reflexivity.
  apps_eq_tac.
Qed.

Ltac cont_rem_head :=
  list_assoc_r'; rewrite ?app_comm_cons;
  repeat match goal with
  | [ |- contracted_gen_spec ?a ?l1 ?l2 ] =>
    (tryif check_app_head l1 [a] then idtac else apply cont_gen_spec_L)
  end.

Ltac cont_rem_tail :=
  list_assoc_l'; rewrite ?app_comm_cons;
  repeat match goal with
  | [ |- contracted_gen_spec ?a ?l1 ?l2 ] =>
    (tryif check_app_tail l1 [a] then idtac else apply cont_gen_spec_R)
         end.

Ltac cont_rem_mid_simp :=
  apply cont_gen_spec_basic || apply cont_gen_spec_rem_sml_L
|| apply cont_gen_spec_rem_sml_R.

Ltac cont_gen_spec_app_brac_mid_L :=
  match goal with
  | [ |- contracted_gen_spec _ ?l1 ?l2 ] => app_bracket_middle_arg l1
  end.

Ltac cont_gen_spec_app_brac_mid_R :=
  match goal with
  | [ |- contracted_gen_spec _ ?l1 ?l2 ] => app_bracket_middle_arg l2
  end.

Ltac cont_gen_spec_app_brac_mid :=
  cont_gen_spec_app_brac_mid_L; cont_gen_spec_app_brac_mid_R.

(* Use this one *)
Ltac cont_solve :=
  cont_rem_head; cont_rem_tail;
  list_assoc_r_single; repeat cont_gen_spec_app_brac_mid;
  cont_rem_mid_simp.

Ltac cont_solve' :=
  cont_rem_head; cont_rem_tail;
  list_assoc_r_single; cont_gen_spec_app_brac_mid;
  cont_rem_mid_simp.

Inductive contracted_multi {T : Type} : list T -> list T -> Type :=
| cont_multi_refl X : @contracted_multi T X X
(*| cont_multi_base X Y   : @contracted_gen T X Y -> contracted_multi X Y *)
| cont_multi_step X Y Z : @contracted_gen T X Y -> contracted_multi Y Z -> contracted_multi X Z.

Inductive contracted_multi_enum {T : Type} : list T -> list T -> nat -> Type :=
| cont_multi_enum_refl X : @contracted_multi_enum T X X 0
(*| cont_multi_base X Y   : @contracted_gen T X Y -> contracted_multi X Y *)
| cont_multi_enum_step X Y Z n : @contracted_gen T X Y -> contracted_multi_enum Y Z n -> contracted_multi_enum X Z (S n).

Lemma cont_multi_cont_multi_enum : forall {T : Type} (X Y : list T),
    contracted_multi X Y -> existsT2 n, contracted_multi_enum X Y n.
Proof.
  intros T X Y Hc.
  induction Hc. exists 0. eapply cont_multi_enum_refl.
  destruct IHHc as [n IH].
  exists (S n). eapply cont_multi_enum_step.
  eapply c. apply IH.
Qed.

Lemma cont_multi_enum_cont_multi : forall {T : Type} (X Y : list T) n,
    contracted_multi_enum X Y n -> contracted_multi X Y.
Proof.
  intros T X Y n Hc.
  induction Hc. eapply cont_multi_refl.
  eapply cont_multi_step. eapply c.
  assumption.
Qed.

Inductive contracted_seqL {T1 T2 : Type} : ((list T1) * (list T1) * T2) -> ((list T1) * (list T1) * T2) -> Type :=
| cont_seqL X Y Δ d : contracted_multi X Y -> contracted_seqL (X,Δ,d) (Y,Δ,d).

Inductive contracted_seqR {T1 T2 : Type} : ((list T1) * (list T1) * T2) -> ((list T1) * (list T1) * T2) -> Type :=
| cont_seqR X Y Γ d : contracted_multi X Y -> contracted_seqR (Γ,X,d) (Γ,Y,d).

Inductive contracted_seq {T1 T2 : Type} : ((list T1) * (list T1) * T2) -> ((list T1) * (list T1) * T2) -> Type :=
| cont_seq_baseL s1 s2 : contracted_seqL s1 s2 -> contracted_seq s1 s2
| cont_seq_baseR s1 s2  : contracted_seqR s1 s2 -> contracted_seq s1 s2
| cont_seq_stepL s1 s2 s3 : contracted_seqL s1 s2 -> contracted_seq s2 s3 -> contracted_seq s1 s3
| cont_seq_stepR s1 s2 s3 : contracted_seqR s1 s2 -> contracted_seq s2 s3 -> contracted_seq s1 s3.

Inductive contracted_nseq {T1 T2 : Type} : list ((list T1) * (list T1) * T2) -> list ((list T1) * (list T1) * T2) -> Type :=
| cont_nseq_nil  : contracted_nseq [] []
| cont_nseq_cons s1 s2 ns1 ns2 : contracted_seq s1 s2 -> contracted_nseq ns1 ns2 ->
                                 contracted_nseq (s1::ns1) (s2::ns2).

Lemma contracted_gen_cons : forall {T : Type} Y Z (a : T),
    contracted_gen Y Z ->
    contracted_gen (a :: Y) (a :: Z).
Proof.
  intros until 0; intros Hc; inversion Hc; subst.
  rewrite ?app_comm_cons.
  eapply contracted_genL_I.
  reflexivity. reflexivity.
  rewrite ?app_comm_cons.
  eapply contracted_genR_I.
  reflexivity. reflexivity.
Qed.

Lemma contracted_multi_cons : forall {T : Type} Y Z (a : T),
    contracted_multi Y Z ->
    contracted_multi (a :: Y) (a :: Z).
Proof.
  intros until 0; intros Hc.
  induction Hc. subst. eapply cont_multi_refl.
  subst.
  eapply cont_multi_step. eapply contracted_gen_cons.
  eapply c.
  assumption.
Qed.

Lemma contracted_multi_cons_tl : forall {T : Type} Y Z (a : T),
    contracted_multi Y Z ->
    contracted_multi (Y ++ [a]) (Z ++ [a]).
Proof.
  intros until 0; intros Hc.
  induction Hc. eapply cont_multi_refl.
  inversion c. subst. 
  eapply cont_multi_step.
  list_assoc_r'. simpl. eapply contracted_genL_I.
  reflexivity. reflexivity.
  do 3 rewrite <- app_assoc in IHHc. assumption.

  subst. eapply cont_multi_step.
  list_assoc_r'. simpl. eapply contracted_genR_I.
  reflexivity. reflexivity.
  do 3 rewrite <- app_assoc in IHHc. assumption.
Qed.

Lemma contracted_multi_L : forall {T : Type} (X Y Z : list T),
    contracted_multi Y Z ->
    contracted_multi (X ++ Y) (X ++ Z).
Proof.
  induction X; intros Y Z Hc. assumption.
  simpl. eapply contracted_multi_cons.
  apply IHX. apply Hc.
Qed.

Lemma contracted_multi_R : forall {T : Type} (X Y Z : list T),
    contracted_multi Y Z ->
    contracted_multi (Y ++ X) (Z ++ X).
Proof.
  induction X; intros Y Z Hc. do 2 rewrite app_nil_r. assumption.
  rewrite cons_singleton. do 2 rewrite app_assoc.
  eapply IHX. eapply contracted_multi_cons_tl. assumption.
Qed.

Lemma contracted_multi_multi : forall {T : Type} Γ X Y Z,
    @contracted_multi T (X ++ Γ ++ Y ++ Γ ++ Z) (X ++ Γ ++ Y ++ Z).
Proof.
  induction X; intros.
  simpl.
  list_assoc_l'. eapply contracted_multi_R.
  list_assoc_r'.
  revert Y Z.
  induction Γ; intros Y Z.
  simpl. rewrite app_nil_r. apply cont_multi_refl.
  simpl. eapply cont_multi_step.
  2 :{ eapply contracted_multi_cons. eapply IHΓ. auto. }
  eapply (@contracted_gen_spec_contracted_gen _ a).
  rewrite (cons_singleton Γ a).
  do 2 rewrite (cons_singleton (Γ ++ _) a).
  cont_solve.

  simpl. eapply contracted_multi_cons. apply IHX.
Qed.

Lemma contracted_multi_double : forall {T : Type} Γ,
    @contracted_multi T (Γ ++ Γ) Γ.
Proof.
  intros T Γ.
  assert (    @contracted_multi T ([] ++ Γ ++ [] ++ Γ ++ []) ([] ++ Γ ++ [] ++ [])) as Hass.
  eapply contracted_multi_multi. 
  repeat rewrite app_nil_r in Hass.  assumption. 
Qed.

Lemma contracted_seq_double : forall {T1 T2 : Type} Γ Δ d,
    @contracted_seq T1 T2 (Γ ++ Γ, Δ ++ Δ, d) (Γ, Δ, d).
Proof.
  intros. econstructor 3.
  econstructor. eapply contracted_multi_double.
  econstructor 2. econstructor.
  eapply contracted_multi_double.
Qed.
  
Lemma contracted_seq_refl : forall {T1 T2 : Type} s,
    @contracted_seq T1 T2 s s.
Proof.
  intros T1 T2 [[Γ Δ] d].
  econstructor. econstructor.
  eapply cont_multi_refl.
Qed.

Lemma contracted_multi_seq : forall {T1 T2 : Type} G1 G2 H1 H2 d,
    contracted_multi G1 G2 ->
    contracted_multi H1 H2 ->
    @contracted_seq T1 T2 (G1, H1, d) (G2, H2, d).
  Proof.
    intros.
    eapply cont_seq_stepL.
    econstructor. eassumption.
    eapply cont_seq_baseR.
    econstructor. eassumption.
  Qed.


Lemma contracted_nseq_refl : forall {T1 T2 : Type} ns,
    @contracted_nseq T1 T2 ns ns.
Proof.
  induction ns. constructor.
  constructor. apply contracted_seq_refl.
  assumption.
Qed.


Lemma contracted_nseq_app : forall {T1 T2 : Type} l1 l2 l3 l4,
  @contracted_nseq T1 T2 l1 l3 ->
  contracted_nseq l2 l4 ->
  contracted_nseq (l1 ++ l2) (l3 ++ l4).
Proof.
  induction l1; intros l2 l3 l4 H1 H2.
  inversion H1. assumption.
  inversion H1. subst. simpl.
  econstructor. assumption.
  apply IHl1; assumption.
Qed.

Lemma contracted_seqL_consL : forall {T1 T2 : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seqL T1 T2 (l1, l2, d1) (l3, l4, d2) ->
    contracted_seqL (a :: l1, l2, d1) (a :: l3, l4, d2).
Proof.
  intros until 0; intros H.
  inversion H. subst.
  econstructor.
  eapply contracted_multi_cons.
  assumption.
Qed.

Lemma contracted_seqR_consL : forall {T1 T2 : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seqR T1 T2 (l1, l2, d1) (l3, l4, d2) ->
    contracted_seqR (a :: l1, l2, d1) (a :: l3, l4, d2).
Proof.
  intros until 0; intros H.
  inversion H. subst.
  econstructor.
  assumption.
Qed.

Lemma contracted_seqL_consR : forall {T1 T2 : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seqL T1 T2 (l1, l2, d1) (l3, l4, d2) ->
    contracted_seqL (l1, a :: l2, d1) (l3, a :: l4, d2).
Proof.
  intros until 0; intros H.
  inversion H. subst.
  econstructor.
  assumption.
Qed.

Lemma contracted_seqR_consR : forall {T1 T2 : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seqR T1 T2 (l1, l2, d1) (l3, l4, d2) ->
    contracted_seqR (l1, a :: l2, d1) (l3, a :: l4, d2).
Proof.
  intros until 0; intros H.
  inversion H. subst.
  econstructor.
  eapply contracted_multi_cons.
  assumption.
Qed.

Lemma contracted_seqL_dir : forall {T1 T2 : Type} (l1 l2 l3 l4 : list T1) (d1 d2 : T2),
    contracted_seqL (l1, l2, d1) (l3, l4, d2) -> d1 = d2.
Proof.
  intros until 0; intros Hc.
  inversion Hc. subst. reflexivity.
Qed.

Lemma contracted_seqR_dir : forall {T1 T2 : Type} (l1 l2 l3 l4 : list T1) (d1 d2 : T2),
    contracted_seqR (l1, l2, d1) (l3, l4, d2) -> d1 = d2.
Proof.
  intros until 0; intros Hc.
  inversion Hc. subst. reflexivity.
Qed.
  
Lemma contracted_seq_consL : forall {T1 T2 : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seq T1 T2 (l1, l2, d1) (l3, l4, d2) ->
    contracted_seq (a :: l1, l2, d1) (a :: l3, l4, d2).
Proof.
  intros until 0; intros H.
  remember (l1,l2,d1) as s1.
  remember (l3,l4,d2) as s2.
  revert l1 l2 l3 l4 Heqs1 Heqs2. 
  induction H as [ [[? ?] ?] [[? ?] ?] X | ? ? X | ? ? ? X X2| ? ? ? X X2];
    intros ll1 ll2 ll3 ll4 Heqs1 Heqs2;
    inversion Heqs1; inversion Heqs2; subst.

  eapply contracted_seqL_consL in X.
  econstructor. eassumption.

  eapply contracted_seqR_consL in X.
  econstructor 2. eassumption.

  destruct s2 as [[? ?] ?].
  econstructor 3.
  eapply contracted_seqL_consL.
  eassumption.
  eapply contracted_seqL_dir in X.  subst.
  eapply IHX2; reflexivity.

  destruct s2 as [[? ?] ?].
  econstructor 4.
  eapply contracted_seqR_consL.
  eassumption.
  eapply contracted_seqR_dir in X.  subst.
  eapply IHX2; reflexivity.
Qed.

Lemma contracted_seq_consR : forall {T1 T2 : Type} l1 l2 l3 l4 a d1 d2,
    @contracted_seq T1 T2 (l1, l2, d1) (l3, l4, d2) ->
    contracted_seq (l1, a :: l2, d1) (l3, a :: l4, d2).
Proof.
  intros until 0; intros H.
  remember (l1,l2,d1) as s1.
  remember (l3,l4,d2) as s2.
  revert l1 l2 l3 l4 Heqs1 Heqs2. 
  induction H as [ [[? ?] ?] [[? ?] ?] X | ? ? X | ? ? ? X X2| ? ? ? X X2];
    intros ll1 ll2 ll3 ll4 Heqs1 Heqs2;
    inversion Heqs1; inversion Heqs2; subst.

  eapply contracted_seqL_consR in X.
  econstructor. eassumption.

  eapply contracted_seqR_consR in X.
  econstructor 2. eassumption.

  destruct s2 as [[? ?] ?].
  econstructor 3.
  eapply contracted_seqL_consR.
  eassumption.
  eapply contracted_seqL_dir in X.  subst.
  eapply IHX2; reflexivity.

  destruct s2 as [[? ?] ?].
  econstructor 4.
  eapply contracted_seqR_consR.
  eassumption.
  eapply contracted_seqR_dir in X.  subst.
  eapply IHX2; reflexivity.
Qed.

Lemma contracted_seq_app_sameL : forall {T1 T2 : Type} l1 l2 d,
    @contracted_seq T1 T2 (l1 ++ l1, l2, d) (l1, l2, d).
Proof.
  intros.
  econstructor.
  econstructor.
  eapply contracted_multi_double.
Qed.

Lemma contracted_seq_app_sameR : forall {T1 T2 : Type} l1 l2 d,
    @contracted_seq T1 T2 (l1, l2 ++ l2, d) (l1, l2, d).
Proof.
  intros.
  econstructor 2.
  econstructor.
  eapply contracted_multi_double.
Qed.
  
Lemma contracted_nseq_singleL : forall {T1 T2 : Type} l1 l2 d,
    @contracted_nseq T1 T2 [(l1 ++ l1, l2, d)] [(l1, l2, d)].
Proof.
  intros. econstructor.
  eapply contracted_seq_app_sameL.
  econstructor.
Qed.

Lemma contracted_nseq_singleR : forall {T1 T2 : Type} l1 l2 d,
    @contracted_nseq T1 T2 [(l1, l2 ++ l2, d)] [(l1, l2, d)].
Proof.
  intros. econstructor.
  eapply contracted_seq_app_sameR.
  econstructor.
Qed.

Lemma contracted_nseq_single : forall {T1 T2 : Type} l1 l2 d,
    @contracted_nseq T1 T2 [(l1 ++ l1, l2 ++ l2, d)] [(l1, l2, d)].
Proof.
  intros. econstructor.
  apply contracted_seq_double.
  econstructor.
Qed.
Lemma contracted_multi_from_nil : forall {T : Type} Γ,
    @contracted_multi T [] Γ -> Γ = [].
Proof.
  induction Γ as [ | a l H1]; intros H. reflexivity.
  inversion H as [| H0 H2 H3 H4 H5]; subst. inversion H4; subst;
  repeat match goal with
  | [ H : [] = ?l |- _ ] => try contradiction (app_cons_not_nil _ _ _ H)
  | [ H : ?l = [] |- _ ] => try contradiction (app_cons_not_nil _ _ _ H)
  end.
Qed.

Lemma contracted_multi_trans : forall {T} X Y Z,
    contracted_multi X Y ->
    contracted_multi Y Z ->
    @contracted_multi T X Z.
Proof.
  intros.
  induction X0. eassumption.
  econstructor. eassumption. eapply IHX0.
  eassumption.
Qed.

Lemma contracted_multi_to_nil : forall {T : Type} l,
    @contracted_multi T l [] -> l = [].
Proof.
  intros V l H.
  remember [] as l2.
  induction H. reflexivity.
  subst. specialize (IHcontracted_multi eq_refl).
  subst.
  inversion c.
  repeat match goal with
         | [ H : [] = ?l |- _ ] => try contradiction (app_cons_not_nil _ _ _ H)
         | [ H : ?l = [] |- _ ] => try contradiction (app_cons_not_nil _ _ _ H)
         end.
  destruct A; destruct B; discriminate.
Qed.

Lemma contracted_gen_InT_fwd : forall {T : Type} Γ Σ,
    @contracted_gen T Γ Σ ->
    (forall a, InT a Σ -> InT a Γ).
Proof.
  intros V Γ Σ Hc.
  inversion Hc; intros b Hin; subst.
  apply InT_appE in Hin;
  destruct Hin as [Hin | Hin].
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  assumption.

    apply InT_appE in Hin;
  destruct Hin as [Hin | Hin].
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  assumption.
Qed.

Lemma contracted_gen_InT_rev : forall {T : Type} Γ Σ,
    @contracted_gen T Γ Σ ->
    (forall a, InT a Γ -> InT a Σ).
Proof.
  intros V Γ Σ Hc.
  inversion Hc; intros b Hin; subst.
  apply InT_appE in Hin;
  destruct Hin as [Hin | Hin].
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  assumption.

  apply InT_appE in Hin;
  destruct Hin as [Hin | Hin].
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appE in Hin;
    destruct Hin as [Hin | Hin].
  apply InT_appR.
  apply InT_appR.
  apply InT_appL. assumption.

  apply InT_appR.
  apply InT_appR.
  apply InT_appR.
  assumption.
Qed.
  
Lemma contracted_multi_InT_fwd : forall {T : Type} Γ Σ,
  @contracted_multi T Γ Σ ->
  (forall a, InT a Σ -> InT a Γ).
Proof.
  intros V Γ Σ Hc.
  induction Hc; intros b Hin.
  subst. assumption.
  eapply contracted_gen_InT_fwd.
  eassumption.
  apply IHHc. assumption.
Qed.

Lemma contracted_multi_InT_rev : forall {T : Type} Γ Σ,
  @contracted_multi T Γ Σ ->
  (forall a, InT a Γ -> InT a Σ).
Proof.
  intros V Γ Σ Hc.
  induction Hc; intros b Hin.
  subst. assumption.
  apply IHHc.
  eapply contracted_gen_InT_rev.
  eassumption.
  assumption.
Qed.

Lemma contracted_multi_insertL_pre : forall {T : Type} l1 l3 a,
    (InT a l1) ->
    contracted_multi l1 l3 ->
    @contracted_multi T ([a] ++ l1) l3.
Proof.
  intros V l1 l3 a Hin Hc.
  induction Hc.

  econstructor; [ | econstructor].
  eapply InT_split in Hin.
  destruct Hin as [l1 [l2 Hin]].
  subst.
  list_assoc_r_single.
  rewrite <- (app_nil_l (_ ++ (l1 ++ _))).
  econstructor; reflexivity.
  
  eapply contracted_multi_trans; [| eapply IHHc].
  eapply contracted_multi_cons. 
  econstructor. eassumption. econstructor.
  eapply contracted_gen_InT_rev. eassumption.
  assumption.
Qed.

Lemma contracted_multi_insertL : forall {T : Type} l1 l2 l3 a,
    (InT a l1 + InT a l2) ->
    contracted_multi (l1 ++ l2) l3 ->
    @contracted_multi T (l1 ++ [a] ++ l2) l3.
Proof.
  intros until 0; intros Hin Hc.
  econstructor; [ | eapply Hc].
  destruct Hin as [Hin | Hin].

  list_assoc_l.
  eapply cont_gen_R.
  eapply InT_split in Hin.
  destruct Hin as [l1' [l2' Hin']].
  subst. list_assoc_r_single.
  rewrite <- (app_nil_r [a]).
  econstructor. reflexivity.
  repeat rewrite app_nil_r. reflexivity.
  
  eapply cont_gen_L.
  eapply InT_split in Hin.
  destruct Hin as [l1' [l2' Hin']].
  subst. list_assoc_r_single.
  rewrite <- (app_nil_l [a]).
  repeat rewrite <- app_assoc.
  econstructor; reflexivity.
Qed.

Lemma contracted_multi_appL_InT : forall {T : Type} Γ Σ,
    (forall a, InT a Σ -> InT a Γ) ->
    @contracted_multi T (Γ ++ Σ) Γ.
Proof.
  intros V Γ Σ; revert Γ.
  induction Σ; intros Γ H.
  rewrite app_nil_r. econstructor.

  assert (InT a Γ) as H2.
  eapply H. econstructor. reflexivity.
  eapply contracted_multi_insertL.
  left. assumption.
  apply IHΣ.
  intros b Hb. apply H. econstructor 2. assumption.
Qed.

Lemma contracted_multi_appR_InT : forall {T : Type} Γ Σ,
    (forall a, InT a Σ -> InT a Γ) ->
    @contracted_multi T (Σ ++ Γ) Γ.
Proof.
  intros V Γ Σ; revert Γ.
  induction Σ; intros Γ H.
  simpl. econstructor.

  assert (InT a Γ) as H2.
  eapply H. econstructor. reflexivity.
  simpl. eapply contracted_multi_insertL_pre.
  eapply InT_appR. assumption.

  apply IHΣ.
  intros b Hb. apply H. econstructor 2. assumption.
Qed.

Lemma contracted_multi_appL : forall {T : Type} Γ Σ,
    contracted_multi Γ Σ ->
    @contracted_multi T (Γ ++ Σ) Γ.
Proof.
  intros. apply contracted_multi_appL_InT.
  apply contracted_multi_InT_fwd.
  assumption.
Qed.

Lemma contracted_multi_appL_rev : forall {T : Type} Γ Σ,
    contracted_multi Σ Γ ->
    @contracted_multi T (Γ ++ Σ) Γ.
Proof.
  intros. apply contracted_multi_appL_InT.  
  apply contracted_multi_InT_rev.
  assumption.
Qed.

Lemma contracted_multi_appR : forall {T : Type} Γ Σ,
    contracted_multi Γ Σ ->
    @contracted_multi T (Σ ++ Γ) Γ.
Proof.
  intros. apply contracted_multi_appR_InT.
  apply contracted_multi_InT_fwd.
  assumption.
Qed.

Lemma contracted_multi_appR_rev : forall {T : Type} Γ Σ,
    contracted_multi Σ Γ ->
    @contracted_multi T (Σ ++ Γ) Γ.
Proof.
  intros. apply contracted_multi_appR_InT.
  apply contracted_multi_InT_rev.
  assumption.
Qed.

Lemma contracted_seq_dir_same : forall {T1 T2 : Type} p1 p2 d1 d2,
    @contracted_seq T1 T2 (p1,d1) (p2,d2) -> d1 = d2.
Proof.
  intros *. intros H.
  remember (p1, d1) as s1.
  remember (p2, d2) as s2.
  revert Heqs1 Heqs2.
  revert  p1 p2 d1 d2.
  induction H; intros; subst.

  inversion c; subst. reflexivity.
  inversion c; subst. reflexivity.
  inversion c; subst. eapply IHcontracted_seq. reflexivity. reflexivity.
  inversion c. subst. eapply IHcontracted_seq. reflexivity. reflexivity.
Qed.

Lemma contracted_seq_multiR : forall {T1 T2 : Type} Γ Δ Σ Π d1 d2,
    @contracted_seq T1 T2 (Γ, Δ, d1) (Σ, Π, d2) ->
    contracted_multi Δ Π.
Proof.
  intros *. intros H.
  remember (Γ, Δ, d1) as s1.
  remember (Σ, Π, d2) as s2.
  revert Heqs1 Heqs2.
  revert  Γ Δ Σ Π d1 d2.
  induction H; intros; subst.
  inversion c. subst. econstructor. 
  inversion c. subst. eassumption.

  inversion c. subst.
  eapply IHcontracted_seq; reflexivity.

  inversion c. subst.
  pose proof (IHcontracted_seq _ _ _ _ _ _ eq_refl eq_refl).
  eapply contracted_multi_trans; eassumption.
Qed.

Lemma contracted_seq_multiL : forall {T1 T2 : Type} Γ Δ Σ Π d1 d2,
    @contracted_seq T1 T2 (Γ, Δ, d1) (Σ, Π, d2) ->
    contracted_multi Γ Σ.
Proof.
  intros *. intros H.
  remember (Γ, Δ, d1) as s1.
  remember (Σ, Π, d2) as s2.
  revert Heqs1 Heqs2.
  revert  Γ Δ Σ Π d1 d2.
  induction H; intros; subst.
  inversion c. subst. eassumption.
  inversion c. subst. econstructor.

  inversion c. subst.
  pose proof (IHcontracted_seq _ _ _ _ _ _ eq_refl eq_refl).
  eapply contracted_multi_trans; eassumption.

  inversion c. subst.
  eapply IHcontracted_seq; reflexivity.
Qed.

Lemma contracted_seq_seqL : forall {T1 T2 : Type} Γ Δ Σ d1 d2,
    @contracted_seq T1 T2 (Γ, Δ, d1) (Σ, Δ, d2) ->
    contracted_seqL (Γ, Δ, d1) (Σ, Δ, d2).
Proof.
  intros *. intros H.
  pose proof (contracted_seq_dir_same H). subst.
  econstructor.
  eapply contracted_seq_multiL in H.
  eassumption.
Qed.
  
Lemma contracted_seq_seqR : forall {T1 T2 : Type} Γ Δ Π d1 d2,
    @contracted_seq T1 T2 (Γ, Δ, d1) (Γ, Π, d2) ->
    contracted_seqR (Γ, Δ, d1) (Γ, Π, d2).
Proof.
  intros *. intros H.
  pose proof (contracted_seq_dir_same H). subst.
  econstructor.
  eapply contracted_seq_multiR in H.
  eassumption.
Qed.

Lemma contracted_seq_merge_app2L : forall {T1 T2 : Type} Γ Δ Σ Π d,
  contracted_seq (Γ, Δ, d) (Σ, Π, d) ->
  @contracted_seq T1 T2 (Γ ++ Σ, Δ ++ Π, d) (Γ, Δ, d).
Proof.
  intros until 0; intros H.
  eapply cont_seq_stepR.
  econstructor.
  eapply contracted_multi_appL.
  eapply contracted_seq_multiR. eassumption.
  eapply cont_seq_baseL.
  econstructor.
  eapply contracted_multi_appL.
  eapply contracted_seq_multiL. eassumption.
Qed.

Lemma contracted_seq_merge_app2R : forall {T1 T2 : Type} Γ Δ Σ Π d,
  contracted_seq (Γ, Δ, d) (Σ, Π, d) ->
  @contracted_seq T1 T2 (Σ ++ Γ, Π ++ Δ, d) (Γ, Δ, d).
Proof.
  intros until 0; intros H.
  eapply cont_seq_stepR.
  econstructor.
  eapply contracted_multi_appR.
  eapply contracted_seq_multiR. eassumption.
  eapply cont_seq_baseL.
  econstructor.
  eapply contracted_multi_appR.
  eapply contracted_seq_multiL. eassumption.
Qed.

Lemma contracted_seq_merge_app2L_rev : forall {T1 T2 : Type} Γ Δ Σ Π d,
  contracted_seq (Σ, Π, d) (Γ, Δ, d)  ->
  @contracted_seq T1 T2 (Γ ++ Σ, Δ ++ Π, d) (Γ, Δ, d).
Proof.
  intros until 0; intros H.
  eapply cont_seq_stepR.
  econstructor.
  eapply contracted_multi_appL_rev.
  eapply contracted_seq_multiR. eassumption.
  eapply cont_seq_baseL.
  econstructor.
  eapply contracted_multi_appL_rev.
  eapply contracted_seq_multiL. eassumption.
Qed.

Lemma contracted_seq_merge_app2R_rev : forall {T1 T2: Type} Γ Δ Σ Π d,
  contracted_seq (Σ, Π, d) (Γ, Δ, d)  ->
  @contracted_seq T1 T2 (Σ ++ Γ, Π ++ Δ, d) (Γ, Δ, d).
Proof.
  intros until 0; intros H.
  eapply cont_seq_stepR.
  econstructor.
  eapply contracted_multi_appR_rev.
  eapply contracted_seq_multiR. eassumption.
  eapply cont_seq_baseL.
  econstructor.
  eapply contracted_multi_appR_rev.
  eapply contracted_seq_multiL. eassumption.
Qed.

Lemma contracted_multi_appL_inclT : forall {T : Type} (L1 L2 : list T),
    inclT L2 L1 ->
    contracted_multi (L2 ++ L1) L1.
Proof.
  induction L2; intros Hincl.
  econstructor.
  simpl.
  pose proof (inclT_consL_InT Hincl) as Hin.
  pose proof (inclT_consL_inclT Hincl) as Hincl2.
  list_assoc_r_single.
  apply contracted_multi_insertL_pre.
  apply InT_appR. assumption.
  eapply IHL2. assumption.
Qed.

Lemma contracted_multi_appR_inclT : forall {T : Type} (L1 L2 : list T),
    inclT L2 L1 ->
    contracted_multi (L1 ++ L2) L1.
Proof.
  induction L2; intros Hincl.
  rewrite app_nil_r. econstructor.
  pose proof (inclT_consL_InT Hincl) as Hin.
  pose proof (inclT_consL_inclT Hincl) as Hincl2.
  list_assoc_r_single.
  eapply contracted_multi_insertL. left. assumption.
  eapply IHL2. assumption.
Qed.

Lemma contracted_gen_insert_InT : forall {T : Type} (l1 l2 : list T) a,
    (InT a l1 + InT a l2) ->
    contracted_gen (l1 ++ [a] ++ l2) (l1 ++ l2).
Proof.
  intros T l1 l2 a Hin.
  destruct Hin as [Hin | Hin];
    apply InT_split in Hin; destruct Hin as [L1 [L2 HH]];
      subst;
      list_assoc_r_single;
      econstructor; reflexivity.
Qed.

Lemma contracted_multi_insert_inclT : forall {T : Type} (L1 L2 L3 L4 : list T),
    (inclT L2 L1 + inclT L2 L3) ->
    contracted_multi (L1 ++ L3) L4 ->
    contracted_multi (L1 ++ L2 ++ L3) L4.
Proof.
  induction L2; intros until 0; intros Hincl Hcont.
  simpl in *. assumption.
  list_assoc_r_single.
  econstructor; [ | eapply IHL2]; try eassumption.
  destruct Hincl as [Hincl | Hincl]; apply inclT_consL_InT in Hincl.
  apply contracted_gen_insert_InT. firstorder.
  apply contracted_gen_insert_InT. right. apply InT_appR. assumption.
  destruct Hincl as [Hincl | Hincl]; apply inclT_consL_inclT in Hincl;
    firstorder.
Qed.

Ltac solve_contracted_multi :=
  repeat match goal with
         | [ |- contracted_multi ?L1 ?L2 ] =>
           match L1 with
           | L2 => apply cont_multi_refl
           | L2 ++ ?L3 => apply contracted_multi_appR_inclT
           | ?l3 ++ L2 => apply contracted_multi_appL_inclT (* I think should work but haven't tested *)
           | ?l1 ++ (?l2 ++ ?l3) =>
             match L2 with
             | l1 ++ (l2 ++ ?m2) => rewrite (app_assoc l1 l2 l3);
                                    rewrite (app_assoc l1 l2 m2)
             | l1 ++ l2 => rewrite (app_assoc l1 l2 l3)
             | l1 ++ (?m1 ++ ?m2) => apply contracted_multi_insert_inclT
             end
           | _ => idtac 333
           end
         | [ |- _ ] => list_assoc_r_single; solve_inclT
         end.
