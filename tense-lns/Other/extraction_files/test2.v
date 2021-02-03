Add LoadPath "../../general".
Add LoadPath "..".
Require Import cut.
Require Import Extraction.

Extraction Language Haskell.

Require Import genT gen gen_seq.
Require Import ddT.
Require Import List_lemmasT.
Require Import gen_tacs lntT lntkt_exchT.


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

Lemma pf_wc :  (@LNSKt_cut_rules nat [] [([Var 0], [Var 0], fwd)]).
Proof.
  eapply LNSKt_rules_woc.
  eapply prop.
  eapply nslcrule_gen; try reflexivity.
  erewrite map_nil. reflexivity.
  unfold nslcext.
  erewrite (app_nil_l). reflexivity.
  rewrite <- seqext_all_nil.
  eapply Sctxt_nil.
  eapply Id_pfc.
Qed.


Definition seq := [([Var 0], [Var 0], fwd)].
(* Example derivation of LNS "p => p". *)
Definition example1 := (@derI (list (rel (list (PropF nat)) * dir)) (@LNSKt_rules nat) noprem [] [([Var 0], [Var 0], fwd)] pf (@dlNil _ (@LNSKt_rules nat) noprem)).

Definition example2 := (@derI (list (rel (list (PropF nat)) * dir)) (@LNSKt_cut_rules nat) noprem [] seq pf_wc (@dlNil _ (@LNSKt_cut_rules nat) noprem)).

Check (LNSKt_cut_elimination).
Check (LNSKt_cut_elimination example2).

Definition cut_example2 := LNSKt_cut_elimination example2.




Time Separate Extraction cut_example2.