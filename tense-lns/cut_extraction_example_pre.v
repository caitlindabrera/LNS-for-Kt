Add LoadPath "../general".

Require Import LNSKt_calculus.
Require Import cut_setup.
Require Import cut.

Set Implicit Arguments.


Definition noprem {X : Type} := (fun (_ : X) => False).

Definition Ds_nil := (@dlNil _ (@LNSKt_cut_rules nat) noprem).

Definition p := Var 0.
Definition q := Var 1.
Definition r := Var 2.



(* -------- *)
(* EXAMPLES *)
(* -------- *)

(*

For each example there are four stages:

1. Conclusion building:
-----------------------
Each LNS in the derivation is defined, with the name conclX_Y, where
X is the example number and Y is the label of the node of the derivation
tree, where the root is labelled 0 and each node's immediate children add 
on a digit, the leftmost child a 0 and the rightmost child a 1.

E.g. 

 000 010 011
  |   | /  
  00  01
   \ /
    0

2. Proof (of validity of each rule) building:
---------------------------------------------
Each rule application requires a proof of its validity, called pfX_Y,
where X is the example number and Y is the label of the conclusion of
the rule application.

3. Derivation building:
-----------------------
Instead of going straight into building the proofterm of the whole
derivation, incrementally build the subderivation until the final 
one. These are called derX_Y, where X is the example number and Y is 
the label of the conclusion of the derivation. We call the full 
derivation exampleX where X is the example number.

4. Cut-free derivation building:
--------------------------------
Define the cut-free derivation output of the cut-elimination 
alogorithm.

--

Examples 1 and 2 give small derivations that are already cut-free in order to provide a simple introduction to the approach we take to encode concrete derivations.
Example 3 is a non-trivial derivation with cut.

*)


(* --------- *)
(* EXAMPLE 1 *)
(* --------- *)

(*
Trivial example where the derivation is just one rule application, the (id) rule.


------------- (id)
    P => P
 *)

(* CONCLUSION BUILDING *)

Definition concl1 : LNS := [([p], [p], fwd)].

(* PROOF (OF VALIDITY OF EACH RULE) BUILDING *)

Lemma pf1 :  @LNSKt_cut_rules nat [] concl1.
Proof.
  eapply LNSKt_rules_woc.
  eapply prop.
  eapply nslcrule_gen; try reflexivity.
  erewrite map_nil. reflexivity.
  unfold nslcext.
  erewrite (app_nil_l). reflexivity.
  rewrite <- seqext_all_nil.
  eapply (Sctxt _ [] _ [] [] [] [] (Id _)).
Qed.

(* DERIVATION BUILDING *)

Definition der1 := (@derI _ (@LNSKt_cut_rules nat) noprem [] concl1 pf1 Ds_nil).

Definition example1 := der1.

(* CUT-FREE DERIVATION BULIDING *)

Definition cut_example1 := LNSKt_cut_elimination example1.



(* --------- *)
(* EXAMPLE 2 *)
(* --------- *)

(*
Trivial example with two rule applications.

--------------------- (id)
00   p => p -> p, p
--------------------- (ImpR)
0      => p -> p

*)

(* CONCLUSION BUILDING *)

Definition concl2_00 := [([p],  [Imp p p] ++ [p] , fwd)].
Definition concl2_0 : LNS := [ ([], [Imp p p], fwd) ]. 


(* PROOF (OF VALIDITY OF EACH RULE) BUILDING *)

Lemma pf2_00 : LNSKt_cut_rules [] concl2_00.
Proof.
  unfold concl2_00.
  eapply LNSKt_rules_woc.
  eapply prop.
  eapply nslcrule_gen; try reflexivity.
  2:{ unfold nslcext. erewrite app_nil_l. reflexivity.  }
  2:{ eapply (Sctxt _ [] _ [] [] _ [] (Id _)). }
  reflexivity.
Defined.

Lemma pf2_0 :  (@LNSKt_cut_rules nat [concl2_00] concl2_0).
Proof.
  unfold concl2_0.
  eapply LNSKt_rules_woc.
  eapply prop.
  eapply nslcrule_gen; try reflexivity.
  2:{ unfold nslcext. erewrite app_nil_l. reflexivity.  }
  2:{ apply seqrule_id.
      apply ImpR. }
  reflexivity.
Defined.


(* DERIVATION BUILDING *)

Definition der2_00 := (derI concl2_00 pf2_00 Ds_nil).
Definition der2_0 := (derI concl2_0 pf2_0 (dlCons der2_00 Ds_nil)).

Definition example2 := der2_0.

(* CUT-FREE DERIVATION BULIDING *)

Definition cut_example2 := LNSKt_cut_elimination example2.



(* --------- *)
(* EXAMPLE 3 *)
(* --------- *)

(*
Non-trivial example with cut.


--------------------------- (id)           ---------------------------- (id)
000   WBox p =>  // p => p               010     =>  // p,q => p, q->p
--------------------------- WBox1L         ---------------------------- ImpR
00    WBox p =>  //   => p               01      =>  //  p  => q->p
------------------------------------------------------------------------ cut
0                    WBox p =>   //  => q -> p

*)

(* CONCLUSION BUILDING *)

Definition concl3_0 := [ ([WBox (Var 0)], [], fwd) ; ([], [Imp (Var 1) (Var 0)], fwd) ].
Definition concl3_00 := [ ([WBox (Var 0)], [], fwd) ; ([], [Var 0], fwd) ].
Definition concl3_000 := [ ([WBox (Var 0)], [], fwd) ; ([Var 0], [Var 0], fwd) ].
Definition concl3_01 := [ ([], [], fwd) ; ([Var 0], [Imp (Var 1) (Var 0)], fwd) ].
Definition concl3_010 := [ ([], [], fwd) ; ([Var 0; Var 1], [Imp (Var 1) (Var 0); (Var 0)], fwd) ].


(* PROOF (OF VALIDITY OF EACH RULE) BUILDING *)

Lemma pf3_000 : LNSKt_cut_rules [] concl3_000.
Proof.
  unfold concl3_000.
  eapply LNSKt_rules_woc.
  rewrite cons_singleton.
  eapply prop.
  eapply nslcrule_gen. erewrite map_nil. reflexivity.
  unfold nslcext. reflexivity.
  apply seqrule_id.
  apply Id. 
Defined.

Lemma pf3_010 : LNSKt_cut_rules [] concl3_010.
Proof.
  unfold concl3_010.
  eapply LNSKt_rules_woc.
  rewrite cons_singleton.
  eapply prop.
  eapply nslcrule_gen. erewrite map_nil. reflexivity.
  unfold nslcext. reflexivity.
  eapply seqrule_same.
  eapply Sctxt_nil.
  apply Id.
  unfold seqext.
  rewrite (cons_singleton [Var 1]).
  eapply pair_eqI.
  erewrite app_nil_l. reflexivity.
  erewrite app_nil_r. rewrite (cons_singleton _ (Imp _ _)). reflexivity.
Defined.

Lemma pf3_00 : LNSKt_cut_rules [concl3_000] concl3_00.
Proof.
  unfold concl3_00.
  eapply LNSKt_rules_woc.
  eapply b1l.
  eapply nslclrule_gen.
  2:{  
    rewrite <- (app_nil_l [_;_]).  reflexivity. }
  2:{ change [([WBox (Var 0)], [], fwd); ([], [Var 0], fwd)] with
          [([] ++ [WBox (Var 0)] ++ [], [] ++ [] ++ [], fwd); ([] ++ [] ++ [], [] ++ [Var 0] ++ [], fwd)].
      econstructor. }
  unfold concl3_000. simpl. reflexivity.
Defined.

Lemma pf3_01 : LNSKt_cut_rules [concl3_010] concl3_01.
Proof.
  unfold concl3_010. unfold concl3_01.
  eapply LNSKt_rules_woc.
  eapply prop.
  eapply nslcrule_gen.
  3:{ eapply seqrule_same.
      econstructor.
      eapply ImpR.
      unfold seqext. simpl.
      reflexivity. }
  unfold nslcext. simpl.
  rewrite (cons_singleton _ (([],[]),_)).
  change [([Var 0; Var 1], [Imp (Var 1) (Var 0); Var 0], fwd)] with
      [([Var 0] ++ [Var 1] ++ [], [] ++ [Imp (Var 1) (Var 0)] ++ [Var 0] ++ [], fwd)].
  reflexivity.
  unfold nslcext. simpl. reflexivity.
Defined.

Lemma pf3_0 : LNSKt_cut_rules [concl3_00; concl3_01] concl3_0.
Proof.
  unfold concl3_00. unfold concl3_01.
  unfold concl3_0.
  change [([WBox (Var 0)], [], fwd); ([], [Var 0], fwd)] with
      ([([WBox (Var 0)], [], fwd)] ++ [([], [] ++ [Var 0] ++ [], fwd)]).
  change
    [([], [], fwd); ([Var 0], [Imp (Var 1) (Var 0)], fwd)]
    with
    ([([], [], fwd)] ++ [([] ++ [Var 0] ++ [], [Imp (Var 1) (Var 0)], fwd)]).  
  eapply LNSKt_rules_wc.
  econstructor.
  reflexivity. reflexivity. reflexivity. reflexivity.
  rewrite cons_singleton. reflexivity.
  reflexivity.
  eapply merge.merge_step; try reflexivity. econstructor; reflexivity.
  eapply structural_equivalence.se_step2; try reflexivity. econstructor; reflexivity.
Defined.


(* DERIVATION BUILDING *)

Definition der3_000 := (derI concl3_000 pf3_000 Ds_nil).

Definition der3_010 := (derI concl3_010 pf3_010 Ds_nil).

Definition der3_00 := (derI concl3_00 pf3_00 (dlCons der3_000 Ds_nil)).

Definition der3_01 := (derI concl3_01 pf3_01 (dlCons der3_010 Ds_nil)).

Definition der3_0 := (derI concl3_0 pf3_0 (dlCons der3_00 (dlCons der3_01 Ds_nil))).

Definition example3 := der3_0.


(* CUT-FREE DERIVATION BULIDING *)

Definition cut_example3 := LNSKt_cut_elimination example3.