Add LoadPath "../general".

Require Import cut_setup.
Require Import Lemma_Sixteen_setup.
Require Import Lemma_Sixteen.

Set Implicit Arguments.


Theorem LNSKt_cut_admissibility : forall (V : Set) ns1 ns2
  (D1 : pf_LNSKt ns1)
  (D2 : pf_LNSKt ns2),
    can_gen_cut (@LNSKt_rules V) ns1 ns2.
Proof.
  unfold can_gen_cut.
  intros.
  destruct (Lemma_Sixteen (fsize(A), ((dp D1) + (dp D2))%nat))
           as [[[LS1 LS2] LS3] LS4].
  unfold SL in LS4. unfold SL_pre in LS4.
  subst.
  rewrite <- app_nil_r. rewrite <- app_assoc.
  eapply LS4. 
  apply PeanoNat.Nat.le_refl.
  apply PeanoNat.Nat.le_refl.
  eassumption. eassumption.
Defined.

(* Follows from LNSKt_cut_admissibility. *)
Theorem LNSKt_cut_admissibility_simpl : forall (V : Set) ns1 ns2
  (D1 : pf_LNSKt ns1)
  (D2 : pf_LNSKt ns2),
    can_gen_cut_simpl (@LNSKt_rules V) ns1 ns2.
Proof.
  intros. unfold can_gen_cut_simpl.
  intros. subst.
  destruct (@merge_ex V _ _ (struct_equiv_weak_refl G)) as [G3 HG3].   
  eapply derrec_mergeL.
  eassumption.
  eapply LNSKt_cut_admissibility in D2. 2 : exact D1.
  unfold can_gen_cut in D2.
  rewrite <- (app_nil_r Γ2).
  rewrite <- (app_nil_r Δ1).
  rewrite <- app_assoc.
  eapply D2; try reflexivity.
  assumption.
  apply struct_equiv_str_refl.
Qed.


(* --------------- *)
(* CUT ELIMINATION *)
(* --------------- *)

Inductive Cut_rule {V : Set} : rlsT (@LNS V) :=
| Cut : forall G1 G2 G3 s1 s2 s3 ns1 ns2 ns3 (d : dir) Γ Δ1 Δ2 Σ1 Σ2 Π A,
    ns1 = G1 ++ [(s1, d)] -> s1 = pair Γ (Δ1++[A]++Δ2) ->
    ns2 = G2 ++ [(s2, d)] -> s2 = pair (Σ1++[A]++Σ2) Π ->
    ns3 = G3 ++ [(s3, d)] -> s3 = pair (Γ++Σ1++Σ2) (Δ1++Δ2++Π) ->
    merge G1 G2 G3 ->
    struct_equiv_str G1 G2 ->
    Cut_rule [ns1 ; ns2] ns3.

(* LNSKt with cut: rules "WithOut Cut" (_woc) and "With Cut" (_wc). *)
Inductive LNSKt_cut_rules {V : Set} : rlsT (@LNS V) :=
| LNSKt_rules_woc : forall ps c, LNSKt_rules ps c -> LNSKt_cut_rules ps c
| LNSKt_rules_wc  : forall ps c, (@Cut_rule V) ps c -> LNSKt_cut_rules ps c. 
(* | LNSKt_rules_wc  : forall ps c, nslclrule (@Cut_rule V) ps c -> LNSKt_cut_rules ps c.*)

Definition pf_LNSKt_cut {V : Set} ns := derrec (@LNSKt_cut_rules V) (fun _ => False) ns.

Definition lt_wf_indT := well_founded_induction_type Wf_nat.lt_wf.

Theorem LNSKt_cut_elimination :
  forall {V : Set} (ns : @LNS V), pf_LNSKt_cut ns -> pf_LNSKt ns.
Proof.
  intros V ns H.
  remember (derrec_height H) as n.
  revert Heqn. revert H. revert ns.
  induction n using wf_lt_inductionT.
  destruct n.
  +{ intros ns H Heqn. destruct H. contradiction.
     simpl in Heqn. discriminate.
   }
  +{ intros ns H Heqn. remember H as H'.
     destruct H. contradiction.
     simpl in *. rewrite HeqH' in Heqn. inversion Heqn as [Heqn2].
     rewrite <- HeqH' in Heqn.
     inversion l.
     ++{ subst c ps0. eapply derI. apply X0.
         apply dersrecI_forall.
         intros p Hin.
         (*         pose proof (dersrecD_forall d Hin) as d3. *)
         pose proof (@dersrecD_forall_in_dersrec _ _ _ _ d _ Hin) as [d2 Hin2].
         eapply (X (derrec_height d2)). 2 : reflexivity.
         rewrite Heqn2.
         apply Lt.le_lt_n_Sm.
         eapply le_dersrec_height. exact Hin2.
         apply le_n.
       }
     ++{ subst c ps0.
         inversion X0.
         subst ps concl. clear X0.
         pose proof (@dersrec_double_verb _ _ _ _ _ d) as [d1 [d2 [Hin1 Hin2]]].
         subst s3.
         eapply LNSKt_cut_admissibility;
           [ | | reflexivity | reflexivity | reflexivity | reflexivity | exact X1 | exact H5 | ..].
         +++{ subst. eapply X. 2 : reflexivity. Unshelve.
              3:{ exact d1. }
              apply Lt.le_lt_n_Sm. 
              eapply dersrec_derrec_height_le. 
              assumption.
            }
         +++{ subst. eapply X. 2 : reflexivity. Unshelve. 2:{ exact d2. }
              apply Lt.le_lt_n_Sm. 
              eapply dersrec_derrec_height_le.
              assumption.
            }
       }
   }
Defined.

Print Assumptions LNSKt_cut_elimination. 


