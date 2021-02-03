Add LoadPath "../general".

Require Import require_general.
Require Import ssreflect.

Set Implicit Arguments.

(* Definition of tense formulae, parameterised over propositional variable set.*)
Inductive PropF (V : Set) : Type :=
 | Var : V -> PropF V
 | Bot : PropF V
 | Imp : PropF V -> PropF V -> PropF V
 | WBox : PropF V -> PropF V
 | BBox : PropF V -> PropF V.

(* Indicates the direction connecting sequents look. *)
Inductive dir : Type :=
| fwd : dir
| bac : dir.

Definition seq {V : Set} := rel (list (PropF V)).
Definition LNS {V : Set} := list ((@seq V) * dir).


(* ------- *)
(* TACTICS *)
(* ------- *)

Ltac inversion_Kt_fml :=
  match goal with
  | [ H : WBox ?A = WBox ?B |- _ ] => inversion H; try clear H
  | [ H : BBox ?A = BBox ?B |- _ ] => inversion H; try clear H
  | [ H : Imp ?A ?B = Imp ?C ?D |- _ ] => inversion H; try clear H
  | [ H : Var ?A = Var ?B |- _ ] => inversion H; try clear H
  end.

Ltac inv_contr_PropF :=
  repeat clear_useless;
  match goal with
  | [ H : Var _ = _ |- _ ] => inversion H; subst
  | [ H : Bot _ = _ |- _ ] => inversion H; subst
  | [ H : ?A = _ , A : PropF ?V |- _ ] => inversion H; subst
  end.


(* --------------------------------- *)
(* DEFINITIONS FOR LNS LEVEL CONTEXT *)
(* --------------------------------- *)

Definition nsext (W : Type) G H (d : dir) (s : W) := G ++ (s, d) :: H.

Lemma nsext_def: forall (W : Type) G H d s, 
  @nsext W G H (d : dir) (s : W) = G ++ (s, d) :: H.
Proof.  unfold nsext. reflexivity.  Qed.

(* as above but where context allowed on left only (names ns -> nslc) *)
Definition nslcext (W : Type) G (d : dir) (s : W) := G ++ [(s, d)].

Lemma nslcext_def: forall (W : Type) G d s, 
  @nslcext W G (d : dir) (s : W) = G ++ [(s, d)].
Proof.  unfold nslcext. reflexivity.  Qed.

Inductive nslcrule (W : Type) (sr : rlsT W) : 
    rlsT (list (W * dir)) :=
  | NSlcctxt : forall ps c G d, sr ps c -> 
    nslcrule sr (map (nslcext G d) ps) (nslcext G d c).

Lemma NSlcctxt_nil: forall (W : Type) sr G d c, (sr [] c : Type) ->
  @nslcrule W sr [] (nslcext G d c).
Proof.
  intros until 0; intros H.
  eapply NSlcctxt in H.  simpl in H. exact H.  Qed.

Lemma NSlcctxt': forall W (sr : rlsT W) ps c G d, sr ps c ->
    nslcrule sr (map (nslcext G d) ps) (G ++ [(c, d)]).
Proof. intros. rewrite <- nslcext_def. apply NSlcctxt. assumption. Qed.

(* context of a nested sequent *)
Definition nslext W (G H ls : list W) := G ++ ls ++ H.

Lemma nslext_def: forall W G H ls, @nslext W G H ls = G ++ ls ++ H.
Proof.  unfold nslext. reflexivity.  Qed.

Lemma nslext2_def: forall W G H s1 s2,
  @nslext W G H [s1 ; s2] = G ++ s1 :: s2 :: H.
Proof.  unfold nslext. simpl. reflexivity.  Qed.

Lemma nslext2_def': forall W G H s1 s2,
  @nslext W G H [s1 ; s2] = (G ++ [s1]) ++ s2 :: H.
Proof.  unfold nslext. simpl. intros.  apply list_rearr22.  Qed.

Inductive nslrule W (sr : rlsT (list W)) : rlsT (list W) :=
  | NSlctxt : forall ps c G H, sr ps c ->
    nslrule sr (map (nslext G H) ps) (nslext G H c).

Lemma NSlctxt': forall W (sr : rlsT (list W)) ps c G H, sr ps c ->
    nslrule sr (map (nslext G H) ps) (G ++ c ++ H).
Proof. intros. rewrite <- nslext_def. apply NSlctxt. assumption. Qed.

Lemma NSlctxt2: forall W (sr : rlsT (list W)) ps x y G H, sr ps [x ; y] ->
    nslrule sr (map (nslext G H) ps) (G ++ x :: y :: H).
Proof. intros. rewrite list_rearr20. apply NSlctxt'. assumption. Qed.  

(* left context of a nested sequent *)
Definition nslclext W (G ls : list W) := G ++ ls.

Lemma nslclext_def: forall W G ls, @nslclext W G ls = G ++ ls.
Proof.  unfold nslclext. reflexivity.  Qed.

Lemma nslclext2_def: forall W G s1 s2,
  @nslclext W G [s1 ; s2] = G ++ [s1; s2].
Proof.  unfold nslclext. simpl. reflexivity.  Qed.

Lemma nslclext2_def': forall W G s1 s2,
  @nslclext W G [s1 ; s2] = (G ++ [s1]) ++ [s2].
Proof.  unfold nslclext. simpl. intros.  apply list_rearr22.  Qed.

Inductive nslclrule W (sr : rlsT (list W)) : rlsT (list W) :=
  | NSlclctxt : forall ps c G, sr ps c ->
    nslclrule sr (map (nslclext G) ps) (nslclext G c).

Lemma NSlclctxt': forall W (sr : rlsT (list W)) ps c G, sr ps c ->
    nslclrule sr (map (nslclext G) ps) (G ++ c).
Proof. intros. rewrite <- nslclext_def. apply NSlclctxt. assumption. Qed.

Lemma nslcrule_gen (W : Type) (sr : rlsT W) : forall (ps : list W) (c : W) (G : list (W * dir)) (d : dir) PS C,
    PS = (map (nslcext G d) ps) -> C = (nslcext G d c) ->
    sr ps c -> nslcrule sr PS C.
Proof.
  intros. subst. econstructor. eassumption.
Qed.

Lemma nslclrule_gen
     : forall (W : Type) sr ps c (G : list (W * dir))
         (PS : list (list (W * dir))) C,
      PS = map (nslclext G) ps -> C = nslclext G c -> sr ps c -> nslclrule sr PS C.
Proof.
  intros *; intros Hps Hc Hsr. subst.
  econstructor. assumption.
Qed.

Inductive nsrule (W : Type) (sr : rlsT W) : 
    rlsT (list (W * dir)) :=
  | NSctxt : forall ps c G H d, sr ps c -> 
    nsrule sr (map (nsext G H d) ps) (nsext G H d c).

Lemma NSctxt_nil: forall (W : Type) sr G H d c, (sr [] c : Type) ->
  @nsrule W sr [] (nsext G H d c).
Proof.
  intros until 0; intros H0.
  eapply NSctxt in H0.  simpl in H0. exact H0.
Qed.

Lemma NSctxt': forall W (sr : rlsT W) ps c G H d, sr ps c ->
    nsrule sr (map (nsext G H d) ps) (G ++ (c, d) :: H).
Proof. intros. rewrite <- nsext_def. apply NSctxt. assumption. Qed.


