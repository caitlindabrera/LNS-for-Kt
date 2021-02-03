Add LoadPath "../../general".
Add LoadPath "..".
(* Require Import cut. *)
Require Import Extraction.

Extraction Language Haskell.

Require Import genT gen gen_seq gen_tacs.
Require Import lntT.
(*
Require Import ddT.
Require Import List_lemmasT.
Require Import gen_tacs lntT lntkt_exchT.
*)

Set Implicit Arguments.
Export ListNotations.

Inductive derrec X (rules : list X -> X -> Type) (prems : X -> Type) :
  X -> Type := 
  | dpI : forall concl,
    prems concl -> derrec rules prems concl
  | derI : forall ps concl,
    rules ps concl -> dersrec rules prems ps -> derrec rules prems concl 
with dersrec X (rules : list X -> X -> Type) (prems : X -> Type) :
  list X -> Type :=
  | dlNil : dersrec rules prems []
  | dlCons : forall seq seqs, 
    derrec rules prems seq -> dersrec rules prems seqs ->
    dersrec rules prems (seq :: seqs)
    .

Scheme derrec_rect_mut := Induction for derrec Sort Type
with dersrec_rect_mut := Induction for dersrec Sort Type.
Scheme derrec_rec_mut := Induction for derrec Sort Set
with dersrec_rec_mut := Induction for dersrec Sort Set.
Scheme derrec_ind_mut := Induction for derrec Sort Prop
with dersrec_ind_mut := Induction for dersrec Sort Prop.

Lemma derrec_same: forall X rules prems (c c' : X),
  derrec rules prems c -> c = c' -> derrec rules prems c'.
Proof. intros. subst. assumption. Qed.

Inductive b2rrules (V : Set) : rlsT (list (rel (list (PropF V)) * dir)) :=
  | WBox2Rs : forall A H1 K1l K1r, b2rrules 
      [[(pair H1 (K1l ++ WBox A :: K1r), fwd) ; (pair [] [A], fwd) ]]
      [(pair H1 (K1l ++ WBox A :: K1r), fwd)]
  | BBox2Rs : forall A H1 K1l K1r, b2rrules 
      [[(pair H1 (K1l ++ BBox A :: K1r), bac) ; (pair [] [A], bac) ]]
      [(pair H1 (K1l ++ BBox A :: K1r), bac)].

Inductive b1rrules (V : Set) : rlsT (list (rel (list (PropF V)) * dir)) :=
  | WBox1Rs : forall A d H1 H2 K1l K1r K2l K2r, b1rrules 
    [[(pair H1 (K1l ++ A :: K1r), d) ; (pair H2 (K2l ++ WBox A :: K2r), bac) ] ;
       [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ WBox A :: K2r), bac) ;
         (pair [] [A], fwd)] ]
      [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ WBox A :: K2r), bac)]
  | BBox1Rs : forall A d H1 H2 K1l K1r K2l K2r, b1rrules 
    [[(pair H1 (K1l ++ A :: K1r), d) ; (pair H2 (K2l ++ BBox A :: K2r), fwd) ] ;
       [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ BBox A :: K2r), fwd) ;
         (pair [] [A], bac)] ]
      [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ BBox A :: K2r), fwd)].

Inductive b1lrules (V : Set) : rlsT (list (rel (list (PropF V)) * dir)) :=
  | WBox1Ls : forall A d H1l H1r H2l H2r K1 K2, b1lrules 
      [[(pair (H1l ++ WBox A :: H1r) K1, d);
        (pair (H2l ++ A :: H2r) K2, fwd)]]
      [(pair (H1l ++ WBox A :: H1r) K1, d); 
        (pair (H2l ++ H2r) K2, fwd)]
  | BBox1Ls : forall A d H1l H1r H2l H2r K1 K2, b1lrules 
      [[(pair (H1l ++ BBox A :: H1r) K1, d);
        (pair (H2l ++ A :: H2r) K2, bac)]]
      [(pair (H1l ++ BBox A :: H1r) K1, d); 
         (pair (H2l ++ H2r) K2, bac)].

Inductive b2lrules (V : Set) : rlsT (list (rel (list (PropF V)) * dir)) :=
  | WBox2Ls : forall A d H1l H1r H2l H2r K1 K2, b2lrules 
      [[(pair (H1l ++ A :: H1r) K1, d) ]]
      [(pair (H1l ++ H1r) K1, d); 
        (pair (H2l ++ WBox A :: H2r) K2, bac)]
  | BBox2Ls : forall A d H1l H1r H2l H2r K1 K2, b2lrules 
      [[(pair (H1l ++ A :: H1r) K1, d) ]]
      [(pair (H1l ++ H1r) K1, d); 
         (pair (H2l ++ BBox A :: H2r) K2, fwd)].

Inductive EW_rule (V : Set) : rlsT (list (rel (list (PropF V)) * dir)) :=
| EW : forall H K d, EW_rule [[]] [(pair H K, d)].

Inductive LNSKt_rules (V : Set) : rlsT (list (rel (list (PropF V)) * dir)) :=
  | b2r : forall ps c, nslclrule (@b2rrules V) ps c -> LNSKt_rules ps c
  | b1r : forall ps c, nslclrule (@b1rrules V) ps c -> LNSKt_rules ps c
  | b2l : forall ps c, nslclrule (@b2lrules V) ps c -> LNSKt_rules ps c
  | b1l : forall ps c, nslclrule (@b1lrules V) ps c -> LNSKt_rules ps c
  | nEW : forall ps c, nslclrule (@EW_rule V) ps c -> LNSKt_rules ps c
  | prop : forall ps c, 
    nslcrule (seqrule (@princrule_pfc V)) ps c -> LNSKt_rules ps c.

Definition noprem {X : Type} := (fun (_ : X) => False).


Lemma nslcrule_gen (W : Type) (sr : rlsT W) : forall (ps : list W) (c : W) (G : list (W * dir)) (d : dir) PS C,
    PS = (map (nslcext G d) ps) -> C = (nslcext G d c) ->
    sr ps c -> nslcrule sr PS C.
Proof.
  intros. subst. econstructor. eassumption.
Qed.

Lemma map_nil : forall {A B : Type} (f : A -> B), map f [] = [].
Proof. reflexivity. Qed.

Lemma seqext_all_nil : forall {W : Type} c, @seqext W [] [] [] [] c = c.
Proof.
  unfold seqext. intros W [c1 c2].
  repeat rewrite app_nil_r.
  repeat rewrite app_nil_l.
  reflexivity.
Qed.

Lemma pf :  (@LNSKt_rules nat [] [([Var 0], [Var 0], fwd)]).
Proof.
  eapply prop.
  eapply nslcrule_gen; try reflexivity.
  erewrite map_nil. reflexivity.
  unfold nslcext.
  erewrite (app_nil_l). reflexivity.
  rewrite <- seqext_all_nil.
  eapply Sctxt_nil.
  eapply Id_pfc.
Qed.

Definition example1 := (@derI (list (rel (list (PropF nat)) * dir)) (@LNSKt_rules nat) noprem [] [([Var 0], [Var 0], fwd)] pf (@dlNil _ (@LNSKt_rules nat) noprem)).

Lemma pf2 : 
[([Var 0], [Var 0], fwd)] = [([] ++ [Var 0], [Var 0], fwd)].
Proof. reflexivity. Qed.

Check (derrec_same example1 pf2).
Definition swap_example2 := derrec_same example1 pf2.

Time Separate Extraction swap_example2.