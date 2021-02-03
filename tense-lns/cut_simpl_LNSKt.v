Add LoadPath "../general".

Require Import ddT.
Require Import lntkt_exchT.
Require Import cut.

Definition pf_LNSKt {V : Set} ns := derrec (@LNSKt_rules V) (fun _ => False) ns.
Definition pf_LNSKt_cut {V : Set} ns := derrec (@LNSKt_cut_rules V) (fun _ => False) ns.

Theorem LNSKt_cut_elimination_simpl :
  forall {V : Set} ns, @pf_LNSKt_cut V ns -> pf_LNSKt ns.
Proof.
  unfold pf_LNSKt_cut. unfold pf_LNSKt.
  intros until 0. apply LNSKt_cut_elimination.
Defined.
