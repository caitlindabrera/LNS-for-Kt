Add LoadPath "../general".

Require Import require_general.
Require Import LNS.
Require Import weakenedT contractedT.
Require Import structural_defs.
Require Import ssreflect.

Set Implicit Arguments.


Ltac nsgen_sw_cont_gen rs sppc c c' acm inps0 swap :=
derIrs rs ; [>
  (assoc_mid c ; apply NSlctxt') ||
  (assoc_single_mid' c ; apply NSctxt') ||
  (list_assoc_l' ; apply NSlclctxt') ||
  (list_assoc_l' ; apply NSlcctxt') ;
  exact sppc |
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; subst q ;

rewrite -> Forall_forall in acm ;
rename_last inps0 ;  eapply in_map in inps0 ;
eapply acm in inps0 ;
rewrite -> ?can_gen_contL_gen_def' in inps0 ;
rewrite -> ?can_gen_contR_gen_def' in inps0 ; 
unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
assoc_single_mid' c' ;
eapply inps0 ; [> exact swap |
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  list_eq_assoc | reflexivity ]].


(* -------------------------------------------------- *)
(* HYPOTHESES USED IN LEFT CONTRACTION FOR PRINCRULES *)
(* -------------------------------------------------- *)

Definition premises_fullLT {V} (ps : list (rel (list (PropF V)))) :=
  (non_empty ps -> ForallT (fun p => fst p <> []) ps).

Definition premises_fullL_sT {V} (s : (rel (list (PropF V)))) :=
non_empty (fst s).

Definition premises_fullL_nsT {V} (ps : list (@LNS V)) :=
  ForallT (fun ns => ForallT (fun s => premises_fullL_sT (fst s)) ns) ps.

Definition rules_L_carryT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps a x Δ, rules ps (a::x, Δ) ->
                   ForallT (fun ps' => a = hd a (fst ps')) ps.

Definition rules_R_carryT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps a x Γ, rules ps (Γ, a::x) ->
                   ForallT (fun ps' => a = hd a (snd ps')) ps.

Definition rules_L_neT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps c,
    rules ps c -> (non_empty ps -> ForallT (fun p => fst p <> []) ps).

Definition rules_R_neT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps c,
    rules ps c -> non_empty ps -> non_empty (snd c) ->ForallT (fun p => snd p <> []) ps.


Definition rules_L_ocT {W : Set} (rules : rlsT (rel (list W))) :=
forall (ps : list (rel (list W))) a (x Δ : list W),
rules ps (a :: x, Δ) -> x = [].

Lemma loe_imp_loc : forall {V} (princrules : rlsT (rel (list (PropF V)))),
  rules_L_oeT princrules -> rules_L_ocT princrules.
Proof.
  intros V princrules Hoe.
  unfold rules_L_oeT in Hoe.
  intros ps a x l Hrules.
  change (a :: x) with ([a] ++ x) in Hrules.
  apply Hoe in Hrules. destruct Hrules.
  discriminate. assumption.
Qed.

Lemma in_nslcext_seqext : forall  V Φ1 Φ2 Ψ1 Ψ2 l l1 ps G d0,
   InT (l, l1) ps ->
  InT (nslcext G d0 (seqext Φ1 Φ2 Ψ1 Ψ2 (l, l1)))
         (map (nslcext G d0) (map (@seqext V Φ1 Φ2 Ψ1 Ψ2) ps)).
Proof. intros. do 2 apply InT_map. auto. Qed.

Lemma in_nslc_seq : forall {V} ns ps G d0 (Γ1 Γ2 Ψ1 Ψ2 : list (PropF V)),
  iffT (InT ns (map (nslcext G d0)
             (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)))
  (existsT2 p, (ns = (nslcext G d0 (seqext Γ1 Γ2 Ψ1 Ψ2 p))) *
            InT p ps).
Proof.
  induction ps; intros.
  +  simpl. split; intros H. inversion H. 
     destruct H as [[p H] [H2 H3]]. inversion H3. 
  + simpl. split; intros H.
    ++ inversion H as [H1 | H2 H3]; subst.
        exists a.  firstorder. econstructor. auto.
        apply IHps in H0. destruct H0 as [p [H0 H1]].
        exists p. split. auto. constructor 2. auto.
    ++ inversion H as [p [H1 H2]].
       inversion H2 as [ | ? ? H3]; subst.  constructor. reflexivity.
       constructor 2. eapply IHps. eexists. split. reflexivity. assumption.
Qed.

Lemma in_rules_L_carry: forall {V} (princrules : rlsT (rel (list (PropF V))))  ps a l l0 Γ1 Γ2,
    rules_L_carryT princrules ->
    rules_L_neT princrules ->
    princrules ps (a::l, l0) ->
    InT (Γ1, Γ2) ps ->
    InT a Γ1.
Proof.
  intros until 0; intros H1 H2 H3 H4.
  unfold rules_L_carryT in H1.
  unfold rules_L_neT in H2.
  pose proof H3 as H3'. pose proof H3 as H3''.
  eapply H1 in H3. eapply H2 in H3'.
  clear H1 H2. 
  eapply ForallT_forall in H3. 2: exact H4.
  eapply ForallT_forall in H3'. 2 : exact H4.
  simpl in H3. destruct Γ1. contradiction.
  simpl in H3. subst. constructor. reflexivity.
  destruct ps. inversion H4. constructor.
Qed.

Lemma in_rules_R_carry: forall {V} (princrules : rlsT (rel (list (PropF V))))  ps a l l0 Γ1 Γ2,
    rules_R_carryT princrules ->
    rules_R_neT princrules -> 
    princrules ps (l0, a::l) ->
    InT (Γ1, Γ2) ps ->
    InT a Γ2.
Proof.
  intros until 0; intros H1 H2 H3 H4.
  unfold rules_R_carryT in H1.
  unfold rules_R_neT in H2.
  pose proof H3 as H3'. pose proof H3 as H3''.
  eapply H1 in H3. eapply H2 in H3'.
  clear H1 H2. 
  eapply ForallT_forall in H3. 2: exact H4.
  eapply ForallT_forall in H3'. 2 : exact H4.
  simpl in H3. destruct Γ2. contradiction.
  simpl in H3. subst. constructor. reflexivity.
  destruct ps. inversion H4. constructor.
  simpl. auto.
Qed.

Lemma rules_L_oe_cons_nil_blind : forall {V} princrules ps a l1 l2,
    @rules_L_oeT V princrules -> 
    princrules ps (a :: l1, l2) ->
    l1 = nil.
Proof.
  intros until 0; intros H1 H2.
  unfold rules_L_oeT in H1.
  change (a :: l1) with ([a] ++ l1) in H2.
  eapply H1 in H2. destruct H2.
  discriminate. assumption.
Qed.

Lemma rules_R_oe_cons_nil_blind : forall {V} princrules ps a l1 l2,
    @rules_R_oeT V princrules -> 
    princrules ps (l1, a :: l2) ->
    l2 = nil.
Proof.
  intros until 0; intros H1 H2.
  unfold rules_R_oe in H1.
  change (a :: l2) with ([a] ++ l2) in H2.
  eapply H1 in H2. destruct H2.
  discriminate. assumption.
Qed.






(* ------------------------------- *)
(* LEFT CONTRACTION FOR PRINCRULES *)
(* ------------------------------- *)

Ltac solve_prop_cont_pr1 :=
  intros until 0; intros Hcarry Hne Hrsub pr HF;
  edestruct Forall_forall as [fwd rev];
  pose proof (fwd HF) as Hcont; clear fwd rev;
  apply dersrec_forall; intros c Hin;
  apply in_nslc_seq in Hin;
  destruct Hin as [[Γ1 Γ2] [Heq Hin]];
  subst; specialize Hin as Hin';
  eapply in_nslcext_seqext in Hin;
  eapply Hcont in Hin;
  (eapply can_gen_contL_gen_def' in Hin ||
   eapply can_gen_contR_gen_def' in Hin);                                    
  [exact Hin | | reflexivity | reflexivity].

Ltac solve_prop_cont_pr1T :=
  intros until 0; intros Hcarry Hne Hrsub pr HF;
  edestruct ForallT_forall as [fwd rev];
  pose proof (fwd HF) as Hcont; clear fwd rev;
  apply dersrec_forall; intros c Hin;
  apply in_nslc_seq in Hin;
  destruct Hin as [[Γ1 Γ2] [Heq Hin]];
  subst; specialize Hin as Hin';
  eapply in_nslcext_seqext in Hin;
  eapply Hcont in Hin;
  (eapply can_gen_contL_gen_def' in Hin ||
   eapply can_gen_contR_gen_def' in Hin);                                    
  [exact Hin | | reflexivity | reflexivity].

Ltac solve_prop_cont :=
  intros until 0; intros HF;
  edestruct Forall_forall as [fwd rev];
  pose proof (fwd HF) as Hcont; clear fwd rev;
  apply dersrec_forall; intros c Hin;
  apply in_nslc_seq in Hin;
  destruct Hin as [[Γ1 Γ2] [Heq Hin]];
  subst; specialize Hin as Hin';
  eapply in_nslcext_seqext in Hin;
  eapply Hcont in Hin;
  (eapply can_gen_contL_gen_def' in Hin ||
   eapply can_gen_contR_gen_def' in Hin);                                    
  [exact Hin | | reflexivity | reflexivity].

Ltac solve_prop_contT :=
  intros until 0; intros HF;
  edestruct ForallT_forall as [fwd rev];
  pose proof (fwd HF) as Hcont; clear fwd rev;
  apply dersrec_forall; intros c Hin;
  apply in_nslc_seq in Hin;
  destruct Hin as [[Γ1 Γ2] [Heq Hin]];
  subst; specialize Hin as Hin';
  eapply in_nslcext_seqext in Hin;
  eapply Hcont in Hin;
  (eapply can_gen_contL_gen_def' in Hin ||
   eapply can_gen_contR_gen_def' in Hin);                                    
  [exact Hin | | reflexivity | reflexivity].

Ltac solve_prop_contL_pr2 thm Hin' Hcarry Hne pr:=
  (eapply in_rules_L_carry in Hin'); [| exact Hcarry | exact Hne | exact pr];
  list_assoc_r_single;  apply thm; exact Hin'.

Ltac solve_prop_contR_pr2 thm Hin' Hcarry Hne pr:=
  (eapply in_rules_R_carry in Hin'); [| exact Hcarry | exact Hne | exact pr];
  list_assoc_r_single;  apply thm; exact Hin'.

Lemma prop_contL_step_pr_L: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (@LNS V)) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_L_carryT princrules ->
  rules_L_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
ForallT (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext (H5 ++ [a] ++ C) A Ψ1 Ψ2) ps)) ->
(pfs rules (map (nslcext G d0) (map (seqext (H5 ++ C) (A) Ψ1 Ψ2) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contL_pr2 (@contracted_gen_in1 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contL_step_pr_R: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (@LNS V)) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_L_carryT princrules ->
  rules_L_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
ForallT (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext A (H5 ++ [a] ++ C) Ψ1 Ψ2) ps)) ->
(pfs rules (map (nslcext G d0) (map (seqext (A) (H5 ++ C) Ψ1 Ψ2) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contL_pr2 (@contracted_gen_in4 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contL_step_pr_L_end: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (@LNS V)) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_L_carryT princrules ->
  rules_L_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
 ForallT (can_gen_contL_gen rules)
          (map (nslcext G d0) (map (seqext (A ++ [a]) C Ψ1 Ψ2) ps)) ->
pfs rules 
        (map (nslcext G d0) (map (seqext (A) C Ψ1 Ψ2) ps)).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contL_pr2 (@contracted_gen_in2 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contL_step_pr_R_start: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (@LNS V)) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_L_carryT princrules ->
  rules_L_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps ([a], l0) ->
ForallT (can_gen_contL_gen rules)
       (map (nslcext G d0) (map (seqext A ([a] ++ C) Ψ1 Ψ2) ps)) ->
(pfs rules (map (nslcext G d0) (map (seqext A C Ψ1 Ψ2) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contL_pr2 (@contracted_gen_in3 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step1: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (@LNS V)) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_R_carryT princrules ->
  rules_R_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
ForallT (can_gen_contR_gen rules)
       (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (H5 ++ [a] ++ C) A) ps)) ->
(pfs rules (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (H5 ++ C) A) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contR_pr2 (@contracted_gen_in1 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step1_OPP: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (@LNS V)) ps a l0 G d0 A H5 C Ψ1 Ψ2,
  rules_R_carryT princrules ->
  rules_R_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
ForallT (can_gen_contR_gen rules)
       (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A (H5 ++ [a] ++ C)) ps)) ->
(pfs rules (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A (H5 ++ C)) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contR_pr2 (@contracted_gen_in4 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step4: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (@LNS V)) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_R_carryT princrules ->
  rules_R_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
 ForallT (can_gen_contR_gen rules)
          (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A ++ [a]) C) ps)) ->
pfs rules 
        (map (nslcext G d0) (map (seqext Ψ1 Ψ2 (A) C) ps)).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contR_pr2 (@contracted_gen_in1 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Lemma prop_contR_step2: forall {V} (princrules : rlsT (rel (list (PropF V)))) (rules : rlsT (@LNS V)) ps a l0 G d0 A C Ψ1 Ψ2,
  rules_R_carryT princrules ->
  rules_R_neT princrules ->
  rsub (nslcrule (seqrule princrules)) rules ->
  princrules ps (l0, [a]) ->
ForallT (can_gen_contR_gen rules)
       (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A ([a] ++ C)) ps)) ->
(pfs rules (map (nslcext G d0) (map (seqext Ψ1 Ψ2 A C) ps))).
Proof.
  solve_prop_cont_pr1T.
  solve_prop_contR_pr2 (@contracted_gen_in3 (PropF V)) Hin' Hcarry Hne pr.
Qed.

Ltac contL_make_gen_L_hyp :=
  unf_pfs_all; match goal with
  | [ Hcont :  Forall (can_gen_contL_gen ?rules)
                      (map ?nsl (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?l1' ?l2' ?Ψ1 ?Ψ2) ?ps)) ] =>
    match l2 with
    | [?a] ++ ?B => add_empty_hyp_L l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | [?a] ++ ?B => add_empty_hyp_L l1 Hcont
    | _ => idtac 
    end
  end.

Ltac contL_make_gen_L_hypT :=
  unf_pfs_all; match goal with
  | [ Hcont :  ForallT (can_gen_contL_gen ?rules)
                      (map ?nsl (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?l1' ?l2' ?Ψ1 ?Ψ2) ?ps)) ] =>
    match l2 with
    | [?a] ++ ?B => add_empty_hyp_L l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | [?a] ++ ?B => add_empty_hyp_L l1 Hcont
    | _ => idtac 
    end
  end.

Ltac contR_make_gen_L_hyp :=
  unf_pfs_all; match goal with
  | [ Hcont :  Forall (can_gen_contR_gen ?rules)
                      (map ?nsl (map (seqext ?Ψ1 ?Ψ2 ?l1 ?l2 ) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?Ψ1 ?Ψ2 ?l1' ?l2') ?ps)) ] =>
    match l2 with
    | [?a] ++ ?B => add_empty_hyp_L l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | [?a] ++ ?B => add_empty_hyp_L l1 Hcont
    | _ => idtac 
    end
  end.

Ltac contR_make_gen_L_hypT :=
  unf_pfs_all; match goal with
  | [ Hcont :  ForallT (can_gen_contR_gen ?rules)
                      (map ?nsl (map (seqext ?Ψ1 ?Ψ2 ?l1 ?l2 ) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?Ψ1 ?Ψ2 ?l1' ?l2') ?ps)) ] =>
    match l2 with
    | [?a] ++ ?B => add_empty_hyp_L l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | [?a] ++ ?B => add_empty_hyp_L l1 Hcont
    | _ => idtac 
    end
  end.

Ltac contL_make_gen_R_hyp :=
  unf_pfs_all; match goal with
  | [ Hcont :  Forall (can_gen_contL_gen ?rules)
                      (map ?nsl (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?l1' ?l2' ?Ψ1 ?Ψ2) ?ps)) ] =>
    match l2 with
    | ?B ++ [?a] => add_empty_hyp_R l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | ?B ++ [?a] => add_empty_hyp_R l1 Hcont
    | _ => idtac 
    end
  end.

Ltac contR_make_gen_R_hyp :=
 unf_pfs_all;  match goal with
  | [ Hcont :  Forall (can_gen_contR_gen ?rules)
                      (map ?nsl (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules (fun _ : list (rel (list (PropF ?V)) * dir) => False)
              (map ?nsl (map (seqext ?l1' ?l2' ?Ψ1 ?Ψ2) ?ps)) ] =>
    match l2 with
    | ?B ++ [?a] => add_empty_hyp_R l2 Hcont
    | _ => idtac 
    end;
    match l1 with
    | ?B ++ [?a] => add_empty_hyp_R l1 Hcont
    | _ => idtac 
    end
  end.

Lemma can_gen_swapL_derrec_spec : forall {V} n rules G d0 Γ Ψ Γ',
  (forall ns : (@LNS V),
         pf rules ns ->
         can_gen_swapL rules ns) ->
  swapped_spec n Γ Γ' ->
  pf rules
         (nslcext G d0 (Γ, Ψ)) ->
  pf rules
         (nslcext G d0 (Γ', Ψ)).
Proof.
  induction n; intros until 0; intros Hcan Hswap Hder.
  inversion Hswap. subst.
  eapply can_gen_swapL_imp. apply Hcan. apply Hder.
  apply H. reflexivity. reflexivity.
  inversion Hswap. subst. eapply IHn in H0.
  eapply can_gen_swapL_imp. apply Hcan. apply H0.
  apply H1. reflexivity.
  reflexivity. assumption. assumption.
Qed.

Lemma can_gen_swapR_derrec_spec : forall {V} n rules G d0 Γ Ψ Ψ',
  (forall ns : (@LNS V),
         pf rules ns ->
         can_gen_swapR rules ns) ->
  swapped_spec n Ψ Ψ' ->
  pf rules
         (nslcext G d0 (Γ, Ψ)) ->
  pf rules
         (nslcext G d0 (Γ, Ψ')).
Proof.
  induction n; intros until 0; intros Hcan Hswap Hder.
  inversion Hswap. subst.
  eapply can_gen_swapR_imp. apply Hcan. apply Hder.
  apply H. reflexivity. reflexivity.
  inversion Hswap. subst. eapply IHn in H0.
  eapply can_gen_swapR_imp. apply Hcan. apply H0.
  apply H1. reflexivity.
  reflexivity. assumption. assumption.
Qed.

Lemma can_gen_swapL_derrec_nslcext : forall {V} rules G d0 s1 s2 Γ Ψ Γ',
  (forall ns : (@LNS V),
         pf rules ns ->
         can_gen_swapL rules ns) ->
  swapped Γ Γ' ->
  s1 = (Γ, Ψ) ->
  s2 = (Γ', Ψ) ->
  pf rules
         (nslcext G d0 s1) ->
  pf rules
         (nslcext G d0 s2).
Proof.
  intros until 0. intros Hexch Hswap Hs1 Hs2 Hd.
  subst. eapply can_gen_swapL_derrec_spec; auto.
  eapply swapped_spec_I. exact Hswap.
  exact Hd.
Qed.

Lemma can_gen_swapR_derrec_nslcext : forall {V} rules G d0 s1 s2 Γ Ψ Ψ',
  (forall ns : (@LNS V),
         pf rules ns ->
         can_gen_swapR rules ns) ->
  swapped Ψ Ψ' ->
  s1 = (Γ, Ψ) ->
  s2 = (Γ, Ψ') ->
  pf rules
         (nslcext G d0 s1) ->
  pf rules
         (nslcext G d0 s2).
Proof.
  intros until 0. intros Hexch Hswap Hs1 Hs2 Hd.
  subst. eapply can_gen_swapR_derrec_spec; auto.
  eapply swapped_spec_I. exact Hswap.
  exact Hd.
Qed.

Lemma can_gen_swapL_derrec_nslcext_gen : forall {V} rules G d0 s1 s2 Γ Ψ Γ',
  (forall ns : (@LNS V),
         pf rules ns ->
         can_gen_swapL rules ns) ->
  swapped_gen Γ Γ' ->
  s1 = (Γ, Ψ) ->
  s2 = (Γ', Ψ) ->
  pf rules
         (nslcext G d0 s1) ->
  pf rules
         (nslcext G d0 s2).
Proof.
  intros until 0. intros Hexch Hswap Hs1 Hs2 Hd.
  inversion Hswap as [[n Hsw]].
  subst. eapply can_gen_swapL_derrec_spec; auto.
  exact Hsw.  exact Hd.
Qed.

Lemma can_gen_swapL_derrec_nslcext_spec : forall {V} n rules G d0 s1 s2 Γ Ψ Γ',
  (forall ns : (@LNS V),
         pf rules ns ->
         can_gen_swapL rules ns) ->
  swapped_spec n Γ Γ' ->
  s1 = (Γ, Ψ) ->
  s2 = (Γ', Ψ) ->
  pf rules
         (nslcext G d0 s1) ->
  pf rules
         (nslcext G d0 s2).
Proof.
  induction n; intros until 0; intros Hexch Hswap Hs1 Hs2 Hd.
  subst; eapply can_gen_swapL_derrec_nslcext in Hd.
  exact Hd. exact Hexch. inversion Hswap. exact H.
  reflexivity. reflexivity.

  inversion Hswap. subst. eapply IHn in H0.
  eapply can_gen_swapL_derrec_nslcext in H0.
  exact H0. exact Hexch. exact H1.
  reflexivity. reflexivity.
  exact Hexch. reflexivity. reflexivity.
  exact Hd.
Qed.

Lemma can_gen_swapR_derrec_nslcext_spec : forall {V} n rules G d0 s1 s2 Ψ Ψ' Γ,
  (forall ns : (@LNS V),
         pf rules ns ->
         can_gen_swapR rules ns) ->
  swapped_spec n Ψ Ψ' ->
  s1 = (Γ, Ψ) ->
  s2 = (Γ, Ψ') ->
  pf rules
         (nslcext G d0 s1) ->
  pf rules
         (nslcext G d0 s2).
Proof.
  induction n; intros until 0; intros Hexch Hswap Hs1 Hs2 Hd.
  subst; eapply can_gen_swapR_derrec_nslcext in Hd.
  exact Hd. exact Hexch. inversion Hswap. exact H.
  reflexivity. reflexivity.

  inversion Hswap. subst. eapply IHn in H0.
  eapply can_gen_swapR_derrec_nslcext in H0.
  exact H0. exact Hexch. exact H1.
  reflexivity. reflexivity.
  exact Hexch. reflexivity. reflexivity.
  exact Hd.
Qed.

Lemma can_gen_swapR_derrec_nslcext_gen : forall {V} rules G d0 s1 s2 Ψ Ψ' Γ,
  (forall ns : (@LNS V),
         pf rules ns ->
         can_gen_swapR rules ns) ->
  swapped_gen Ψ Ψ' ->
  s1 = (Γ, Ψ) ->
  s2 = (Γ, Ψ') ->
  pf rules
         (nslcext G d0 s1) ->
  pf rules
         (nslcext G d0 s2).
Proof.
  intros until 0; intros Hexch Hswap Hs1 Hs2 Hd.
  inversion Hswap as [H]. destruct H as [n H].
  eapply can_gen_swapR_derrec_nslcext_spec in Hd.
  exact Hd. exact Hexch. exact H. exact Hs1. exact Hs2.
Qed.

Lemma can_gen_swapL_derrec : forall {V} l rules G d0 Γ1 Γ2 Ψ Γ1' Γ2',
  (forall ns : (@LNS V),
         pf rules ns ->
         can_gen_swapL rules ns) ->
  swapped (Γ1 ++ Γ2) (Γ1' ++ Γ2') ->
  pf rules
         (nslcext G d0 (Γ1 ++ l ++ Γ2, Ψ)) ->
  pf rules
         (nslcext G d0 (Γ1' ++ l ++ Γ2', Ψ)).
Proof.
  intros until 0. intros Hcan Hswap Hder.
  eapply swapped_spec_I in Hswap.
  eapply swapped__n_mid in Hswap.
  destruct Hswap as [n HH]. 
  eapply can_gen_swapL_derrec_spec.
  apply Hcan. 2 : apply Hder.
  exact HH. 
Qed.

Lemma can_gen_swapR_derrec : forall {V} l rules G d0 Ψ1 Ψ2 Γ Ψ1' Ψ2',
  (forall ns : (@LNS V),
         pf rules ns ->
         can_gen_swapR rules ns) ->
  swapped (Ψ1 ++ Ψ2) (Ψ1' ++ Ψ2') ->
  pf rules
         (nslcext G d0 (Γ, Ψ1 ++ l ++ Ψ2)) ->
  pf rules
         (nslcext G d0 (Γ, Ψ1' ++ l ++ Ψ2')).
Proof.
  intros until 0. intros Hcan Hswap Hder.
  eapply swapped_spec_I in Hswap.
  eapply swapped__n_mid in Hswap.
  destruct Hswap as [n HH]. 
  eapply can_gen_swapR_derrec_spec.
  apply Hcan. 2 : apply Hder.
  exact HH. 
Qed.

Lemma can_gen_swapL_dersrec : forall {V} rules G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2' ps,
(forall ns : (@LNS V),
        pf rules ns ->
        can_gen_swapL rules ns) ->
    swapped (Γ1 ++ Γ2) (Γ1' ++ Γ2') ->
    pfs rules
            (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
    pfs rules
            (map (nslcext G d0) (map (seqext Γ1' Γ2' Ψ1 Ψ2) ps)).
Proof.
  unf_pf. unf_pfs.
  induction ps; intros Hcan Hswap Hder.
  simpl in *. exact Hder.
  destruct a. simpl in *.
  inversion Hder. subst.
  apply dlCons; auto. 
  unfold nslcext.
  eapply can_gen_swapL_derrec in X.
  exact X. exact Hcan. exact Hswap.
Qed.

Lemma can_gen_swapR_dersrec : forall {V} rules G d0 Γ1 Γ2 Ψ1 Ψ2 Ψ1' Ψ2' ps,
(forall ns : (@LNS V),
        pf rules ns ->
        can_gen_swapR rules ns) ->
    swapped (Ψ1 ++ Ψ2) (Ψ1' ++ Ψ2') ->
    pfs rules
            (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
    pfs rules
            (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1' Ψ2') ps)).
Proof.
  unf_pf. unf_pfs.
  induction ps; intros Hcan Hswap Hder.
  simpl in *. exact Hder.
  destruct a. simpl in *.
  inversion Hder. subst.
  apply dlCons; auto. 
  unfold nslcext.
  eapply can_gen_swapR_derrec in X.
  exact X. exact Hcan. exact Hswap.
Qed.

Ltac look_for_swapL Hexch :=
  unf_pfs_all; match goal with
  | [ Hcont :  dersrec ?rules ?f  (map ?nscl (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules ?f (map ?nscl (map (seqext ?Γ1' ?Γ2' ?Ψ1 ?Ψ2) ?ps)) ]
    =>
    match Γ1' with
    | Γ1 => exact Hcont
    | _  => eapply (can_gen_swapL_dersrec _ _ _ Γ1); [exact Hexch|  swap_tac | list_assoc_r_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
    end;
    try 
      match Γ2' with
      | Γ2 => exact Hcont
      | _  => eapply (can_gen_swapL_dersrec _ _ _ Γ1); [exact Hexch | swap_tac | list_assoc_r_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
      end
  end.


Ltac look_for_swapR Hexch :=
  unf_pfs_all; match goal with
  | [ Hcont :  dersrec ?rules ?f  (map ?nscl (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |-
      dersrec ?rules ?f (map ?nscl (map (seqext ?Γ1 ?Γ2 ?Ψ1' ?Ψ2') ?ps)) ]
    =>
    match Ψ1' with
    | Ψ1 => exact Hcont
    | _  => eapply (can_gen_swapR_dersrec _ _ _ _ _ Ψ1); [exact Hexch|  swap_tac | list_assoc_r_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
    end;
    try 
      match Ψ2' with
      | Ψ2 => exact Hcont
      | _  => eapply (can_gen_swapR_dersrec _ _ _ _ _ Ψ1); [exact Hexch | swap_tac | list_assoc_r_arg_conc Hcont; tac_cons_singleton; rem_nil; apply Hcont]
      end
  end.

Ltac breakdownT :=
  repeat (
      repeat (match goal with
              | [ H : ?A ++ ?B = ?x ++ ?y |- _ ] => apply app_eq_appT2 in H; sD; subst
              end) ;
      repeat (match goal with
              | [H2 : [?a] = ?A ++ ?B |- _ ] => apply unit_eq_appT in H2; sD; subst
              end));
  repeat try rewrite app_nil_r; repeat try rewrite app_nil_l;
  repeat (match goal with
          | [ H3 : context[ ?x ++ [] ] |- _ ] => rewrite (app_nil_r x) in H3
          end);
  repeat (match goal with
          | [ H3 : context[ [] ++ ?x ] |- _ ] => rewrite (app_nil_l x) in H3
          end).


Lemma can_gen_contL_gen_derrec : forall  {V}  a (rules : rlsT (@LNS V)) G d Γ Γ' Δ,
    (forall ns : (@LNS V),
        pf rules ns ->
        can_gen_swapL rules ns) ->
    contracted_gen_spec a Γ Γ' ->
  (can_gen_contL_gen rules (G ++ [(Γ,Δ,d)])) ->
  pf rules (G ++ [(Γ',Δ,d)]).
Proof.
  intros until 0. intros Hexch Hcon Hcont.    
  edestruct (@can_gen_contL_gen_def' V) as [fwd bwd].
  clear bwd.
  eapply fwd.
  exact Hcont.
  eapply contracted_gen_spec_contracted_gen. eassumption.
  reflexivity. reflexivity.
Qed.

Lemma can_gen_contR_gen_derrec : forall  {V}  a (rules : rlsT (@LNS V)) G d Γ Δ' Δ,
    (forall ns : (@LNS V),
        pf rules ns ->
        can_gen_swapR rules ns) ->
    contracted_gen_spec a Δ Δ' ->
  (can_gen_contR_gen rules (G ++ [(Γ,Δ,d)])) ->
  pf rules (G ++ [(Γ,Δ',d)]).
Proof.
  intros until 0. intros Hexch Hcon Hcont.    
  edestruct (@can_gen_contR_gen_def' V) as [fwd bwd].
  clear bwd.
  eapply fwd.
  exact Hcont.
  eapply contracted_gen_spec_contracted_gen. eassumption.
  reflexivity. reflexivity.
Qed.


Ltac assoc_mid_list_arg Hcont L a :=
  match L with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 => idtac
    | ?l2 ++ ?l3 ++ ?l4 => rewrite (app_assoc l2) in Hcont; assoc_mid_list_arg Hcont ((l2 ++ l3) ++ l4) a
    end.
  
Ltac contL_brack_fstcont Hcont a :=
  match type of Hcont with
  | can_gen_contL_gen ?rules (?G ++ [(?Γ,?Δ,?d)]) => assoc_mid_list_arg Hcont Γ a
  end.

Ltac contL_brack_sndcont Hcont a :=
  match type of Hcont with
  | can_gen_contL_gen ?rules (?G ++ [(?Γ,?Δ,?d)]) =>
    match Γ with
    | [a] ++ ?l1 ++ [a] => idtac
    | [a] ++ ?l1 ++ [a] ++ ?l2 => idtac
    | ?l1 ++ [a] ++ ?l2 ++ [a] => idtac
    | ?l1 ++ [a] ++ ?l2 ++ [a] ++ ?l3 => idtac
    | [a] ++ ?l1 => assoc_mid_list_arg Hcont l1 a
    | ?l1 ++ [a] ++ ?l2 => assoc_mid_list_arg Hcont l2 a
    end end.

Ltac solve_derrec_swapL_cont V Hcont Hexch a :=
  list_assoc_r_single_arg Hcont;
  contL_brack_fstcont Hcont a;
  contL_brack_sndcont Hcont a;
  edestruct Hcont as [D1 D2]; try reflexivity;
  list_assoc_r_single;
  list_assoc_r_single_arg D1;
  list_assoc_r_single_arg D2;
  pose proof (@can_gen_swapL_derrec_nslcext_gen V) as H;
  unfold nslcext in H;
  split;
  [(eapply H; [ exact Hexch | | reflexivity| reflexivity|exact D1]) |
   (eapply H; [ exact Hexch | | reflexivity| reflexivity|exact D2])].

  
Ltac contR_brack_fstcont Hcont a :=
  match type of Hcont with
  | can_gen_contR_gen ?rules (?G ++ [(?Γ,?Δ,?d)]) => assoc_mid_list_arg Hcont Δ a
  end.

Ltac contR_brack_sndcont Hcont a :=
  match type of Hcont with
  | can_gen_contR_gen ?rules (?G ++ [(?Γ,?Δ,?d)]) =>
    match Δ with
    | [a] ++ ?l1 ++ [a] => idtac
    | [a] ++ ?l1 ++ [a] ++ ?l2 => idtac
    | ?l1 ++ [a] ++ ?l2 ++ [a] => idtac
    | ?l1 ++ [a] ++ ?l2 ++ [a] ++ ?l3 => idtac
    | [a] ++ ?l1 => assoc_mid_list_arg Hcont l1 a
    | ?l1 ++ [a] ++ ?l2 => assoc_mid_list_arg Hcont l2 a
    end end.

Ltac solve_derrec_swapR_cont V Hcont Hexch a :=
  list_assoc_r_single_arg Hcont;
  contR_brack_fstcont Hcont a;
  contR_brack_sndcont Hcont a;
  edestruct Hcont as [D1 D2]; try reflexivity;
  list_assoc_r_single;
  list_assoc_r_single_arg D1;
  list_assoc_r_single_arg D2;
  pose proof (@can_gen_swapR_derrec_nslcext_gen V) as H;
  unfold nslcext in H;
  split;
  [(eapply H; [ exact Hexch | | reflexivity| reflexivity|exact D1]) |
   (eapply H; [ exact Hexch | | reflexivity| reflexivity|exact D2])].



Lemma can_gen_contL_gen_swapped : forall {V} (rules : rlsT (@LNS V)) G d Γ Γ' Δ,
    (forall ns : LNS,
        pf rules ns -> can_gen_swapL rules ns) ->
    swapped Γ Γ' ->
    can_gen_contL_gen rules (G ++ [(Γ,Δ,d)]) ->
    can_gen_contL_gen rules (G ++ [(Γ',Δ,d)]).
Proof.
  intros until 0; intros Hexch Hswapped Hcont;
    unfold can_gen_contL_gen; intros until 0. intros H1 H2.
  subst.  
  app_eq_app_dest3.
  +{ rewrite <- app_assoc in Hcont. 
     edestruct Hcont.
     rewrite <- app_assoc. reflexivity.
     do 3 rewrite <- app_assoc. reflexivity.
     list_assoc_l.
     split;
     (eapply can_gen_swapL_imp; [ apply Hexch | | reflexivity | reflexivity]).
     do 3 rewrite <- (app_assoc). eassumption. eassumption.
     do 3 rewrite <- (app_assoc). eassumption. eassumption.
   }
  +{  list_assoc_r_single_arg Hswapped.
    inversion Hswapped. subst.   
    breakdownT; clear Hswapped;
      app_eq_app_dest3;
      try  solve[solve_derrec_swapL_cont V Hcont Hexch A; swap_gen_tac];
     try solve[  match goal with
            | H : ?L1 ++ ?L2 = [] |- _ => destruct L1; [simpl in H; subst; rem_nil_hyp | inversion H]
            end; solve_derrec_swapL_cont V Hcont Hexch A; swap_gen_tac];
     try solve[ do 2  match goal with
            | H : ?L1 ++ ?L2 = [] |- _ => destruct L1; [simpl in H; subst; rem_nil_hyp | inversion H]
            end; solve_derrec_swapL_cont V Hcont Hexch A; swap_gen_tac].
   }
Qed.

Lemma can_gen_contR_gen_swapped : forall {V} (rules : rlsT (@LNS V)) G d Γ Δ Δ',
    (forall ns : LNS,
        pf rules ns -> can_gen_swapR rules ns) ->
    swapped Δ Δ' ->
    can_gen_contR_gen rules (G ++ [(Γ,Δ,d)]) ->
    can_gen_contR_gen rules (G ++ [(Γ,Δ',d)]).
Proof.
  intros until 0; intros Hexch Hswapped Hcont;
    unfold can_gen_contR_gen; intros until 0. intros H1 H2.
  subst.  
  app_eq_app_dest3.
  +{ rewrite <- app_assoc in Hcont. 
     edestruct Hcont.
     rewrite <- app_assoc. reflexivity.
     do 3 rewrite <- app_assoc. reflexivity.
     list_assoc_l.
     split;
     (eapply can_gen_swapR_imp; [ apply Hexch | | reflexivity | reflexivity]).
     do 3 rewrite <- (app_assoc). eassumption. eassumption.
     do 3 rewrite <- (app_assoc). eassumption. eassumption.
   }
  +{  list_assoc_r_single_arg Hswapped.
    inversion Hswapped. subst.   
    breakdownT; clear Hswapped;
      app_eq_app_dest3;
      try  solve[solve_derrec_swapR_cont V Hcont Hexch A; swap_gen_tac];
     try solve[  match goal with
            | H : ?L1 ++ ?L2 = [] |- _ => destruct L1; [simpl in H; subst; rem_nil_hyp | inversion H]
            end; solve_derrec_swapR_cont V Hcont Hexch A; swap_gen_tac];
     try solve[ do 2  match goal with
            | H : ?L1 ++ ?L2 = [] |- _ => destruct L1; [simpl in H; subst; rem_nil_hyp | inversion H]
                      end; solve_derrec_swapR_cont V Hcont Hexch A; swap_gen_tac].
   }
Qed.

  
Lemma can_gen_contL_gen_derrec_nslcext : forall  {V}  a (rules : rlsT (@LNS V)) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2',
    (forall ns : (@LNS V),
        pf rules ns ->
        can_gen_swapL rules ns) ->
    contracted_gen_spec a (Γ1 ++ Γ2) (Γ1' ++ Γ2')->
  (can_gen_contL_gen rules (nslcext G d0 (seqext Γ1 Γ2 Ψ1 Ψ2 ps))) ->
  pf rules
         (nslcext G d0 (seqext Γ1' Γ2' Ψ1 Ψ2 ps)).
Proof.
  intros until 0. intros Hexch Hcon Hcont.
  unfold nslcext in *. unfold seqext in *.
  destruct ps as [ps1 ps2].

  pose proof (@can_gen_swapL_derrec_nslcext V) as H.
  unfold nslcext in H. eapply H; [ exact Hexch | | reflexivity | reflexivity |].

  eapply swapped_L.
  eapply swapped_simple'.

  eapply can_gen_contL_gen_derrec.
  exact Hexch.
  rewrite app_assoc.
  eapply cont_gen_spec_R. eassumption.
  list_assoc_r_single.
  eapply can_gen_contL_gen_swapped; [exact Hexch | | eapply Hcont].
  eapply swapped_L.
  eapply swapped_simple'.
Qed.

Lemma can_gen_contR_gen_derrec_nslcext : forall  {V}  a (rules : rlsT (@LNS V)) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Ψ1' Ψ2',
    (forall ns : (@LNS V),
        pf rules ns ->
        can_gen_swapR rules ns) ->
    contracted_gen_spec a (Ψ1 ++ Ψ2) ( Ψ1' ++ Ψ2')->
  (can_gen_contR_gen rules (nslcext G d0 (seqext Γ1 Γ2 Ψ1 Ψ2 ps))) ->
  pf rules
         (nslcext G d0 (seqext Γ1 Γ2 Ψ1' Ψ2' ps)).
Proof.
  intros until 0. intros Hexch Hcon Hcont.
  unfold nslcext in *. unfold seqext in *.
  destruct ps as [ps1 ps2].

  pose proof (@can_gen_swapR_derrec_nslcext V) as H.
  unfold nslcext in H. eapply H; [ exact Hexch | | reflexivity | reflexivity |].

  eapply swapped_L.
  eapply swapped_simple'.

  eapply can_gen_contR_gen_derrec.
  exact Hexch.
  rewrite app_assoc.
  eapply cont_gen_spec_R. eassumption.
  list_assoc_r_single.
  eapply can_gen_contR_gen_swapped; [exact Hexch | | eapply Hcont].
  eapply swapped_L.
  eapply swapped_simple'.
Qed.

Lemma can_gen_contL_gen_Forall_dersrec : forall  {V} (a : PropF V) (rules : rlsT (@LNS V)) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2',
    (forall ns : (@LNS V),
        pf rules ns ->
        can_gen_swapL rules ns) ->
    contracted_gen_spec a (Γ1 ++ Γ2) (Γ1' ++ Γ2')->
  ForallT (can_gen_contL_gen rules)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
  pfs rules
         (map (nslcext G d0) (map (seqext Γ1' Γ2' Ψ1 Ψ2) ps)).
Proof.
  intros until 0. intros Hexch Hcon Hcont.
  eapply dersrecI_all.  
  eapply ForallTI_forall.
  intros x Hinx.
  eapply InT_mapE in Hinx.
  destruct Hinx as [[Σ Π] [? Hinx]].
  subst x.
  eapply InT_mapE in Hinx.
  destruct Hinx as [x [Heq Hinx]].
  rewrite <- Heq.
  eapply can_gen_contL_gen_derrec_nslcext.
  exact Hexch.
  exact Hcon.
  eapply ForallTD_forall. eapply Hcont.
  repeat apply InT_map.
  assumption.
Qed.


Lemma can_gen_contL_gen_Forall_dersrec_ltac : forall  {V} (rules : rlsT (@LNS V)) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Γ1' Γ2',
    (forall ns : (@LNS V),
        pf rules ns ->
        can_gen_swapL rules ns) ->
    forall (a : PropF V),
    contracted_gen_spec a (Γ1 ++ Γ2) (Γ1' ++ Γ2')->
  ForallT (can_gen_contL_gen rules)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
  pfs rules
         (map (nslcext G d0) (map (seqext Γ1' Γ2' Ψ1 Ψ2) ps)).
Proof.
  intros *. intros H1 a.
  apply can_gen_contL_gen_Forall_dersrec; eassumption.
Qed.

Lemma can_gen_contR_gen_Forall_dersrec : forall  {V}  a (rules : rlsT (@LNS V)) ps G d0 Γ1 Γ2 Ψ1 Ψ2 Ψ1' Ψ2',
    (forall ns : (@LNS V),
        pf rules ns ->
        can_gen_swapR rules ns) ->
    contracted_gen_spec a (Ψ1 ++ Ψ2) (Ψ1' ++ Ψ2')->
  ForallT (can_gen_contR_gen rules)
         (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1 Ψ2) ps)) ->
  pfs rules
          (map (nslcext G d0) (map (seqext Γ1 Γ2 Ψ1' Ψ2') ps)).
Proof.
  intros until 0. intros Hexch Hcon Hcont.
  eapply dersrecI_all.  
  eapply ForallTI_forall.
  intros x Hinx.
  eapply InT_mapE in Hinx.
  destruct Hinx as [[Σ Π] [? Hinx]].
  subst x.
  eapply InT_mapE in Hinx.
  destruct Hinx as [x [Heq Hinx]].
  rewrite <- Heq.
  eapply can_gen_contR_gen_derrec_nslcext.
  exact Hexch.
  exact Hcon.
  eapply ForallTD_forall. eapply Hcont.
  repeat apply InT_map.
  assumption.
Qed.

Ltac derrec_swapL3 acm exch :=
      eapply (can_gen_swapL_derrec_nslcext_gen) in acm;
      [exact acm | exact exch | | reflexivity | reflexivity ]; swap_gen_tac.
Ltac derrec_swapR3 acm exch :=
      eapply (can_gen_swapR_derrec_nslcext_gen) in acm;
      [exact acm | exact exch | | reflexivity | reflexivity ]; swap_gen_tac.

Ltac destruct_princ :=
  match goal with
  | [ |- context[ (nslcext _ _  (seqext _ _ _ _ ?x)) ]] => destruct x
  end.

Lemma Sctxt_e'': forall (W : Type) (pr : rlsT (rel (list W))) ps U V Φ1 Φ2 Ψ1 Ψ2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) ((Φ1 ++ U) ++ Φ2, (Ψ1 ++ V) ++ Ψ2).
Proof. intros. do 2 rewrite <- app_assoc. apply Sctxt_e. assumption. Qed. 

Ltac nsgen_sw_contL_gen5 rs sppc c c' acm inps0 swap pr inmps exch := 
    derIrs rs  ;
[apply NSlcctxt'; apply Sctxt_e'; exact pr |];
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ;
rename_last inps0 ;  eapply in_map in inps0 ;
  eapply in_map in inps0 ;
subst;
eapply dersrec_forall in acm;
[| apply inps0];
destruct_princ;
derrec_swapL3 acm exch.

Lemma Sctxt_e''': forall (W : Type) (pr : rlsT (rel (list W))) ps U V Φ1 Φ2 Ψ1 Ψ2,
  pr ps (U, V) ->
  seqrule pr (map (seqext Φ1 Φ2 Ψ1 Ψ2) ps) (Φ1 ++ U ++ Φ2, (Ψ1 ++ V )++ Ψ2).
Proof.
  intros. rewrite <- app_assoc.
  rewrite <- seqext_def. apply Sctxt. assumption.
Qed.  

Ltac nsgen_sw_contR_gen5 rs sppc c c' acm inps0 swap pr inmps exch := 
    derIrs rs  ;
[apply NSlcctxt'; apply Sctxt_e''; exact pr |];
rewrite dersrec_forall ;
intros q qin ;
rewrite -> in_map_iff in qin ; cE ; 
rename_last inmps ;
rewrite -> in_map_iff in inmps ; cE ;
rename_last inps0 ;  eapply in_map in inps0 ;
  eapply in_map in inps0 ;
subst;
eapply dersrec_forall in acm;
[| apply inps0];
destruct_princ;
derrec_swapR3 acm exch.

(* Makes progress on princrules ps (l1, l2) goals *)

Ltac lt1 a acm Hexch :=
  list_assoc_r_single;
  eapply (@can_gen_contL_gen_Forall_dersrec _ a) in acm;
  [| exact Hexch | cont_solve].


Ltac lt2 a Hexch :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : Forall (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match Γ1 with
    | ?A ++ [?a] ++ ?B => eapply prop_contL_step_pr_L in acm
    | ?A ++ [?a] => eapply prop_contL_step_pr_L_end in acm
    | _ => match Γ2 with
           | ?A ++ [?a] ++ ?B => eapply prop_contL_step_pr_R in acm
           | [?a] ++ ?A => eapply prop_contL_step_pr_R_start in acm
           end
    end
  end.


Ltac lt3 a Hexch rs carry psfull loe :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      acm : Forall (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match l1 with
    | context[ a :: [] ] =>
      lt2 a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | context[ a :: ?l2 ] =>
      pose proof (rules_L_oe_cons_nil_blind _ _ _ _ _ loe pr); subst;
      lt2 a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | _ => lt1 a acm Hexch
    end
  end.

Ltac check_nil_contradiction :=
  repeat (try discriminate;
  match goal with
  | [ H : ?l1 ++ ?l2 = [] |- _ ] =>
    apply app_eq_nil_iff in H; destruct H as [H HH]
  end).

Ltac check_contradiction_prL_pre :=
  match goal with
  | [   rs : rsub (nslcrule (seqrule ?princrules)) ?rules,
        pr : ?princrules ?ps (?l1, ?l2),
        loe : forall (ps : list (rel (list (PropF ?V)))) (x y Δ : list (PropF ?V)),
            ?princrules ps (x ++ y, Δ) -> x = [] \/ y = [] |- _ ] =>
    match l1 with
    | ?A ++ ?B => let ph := fresh "H" in specialize (loe _ _ _ _ pr) as H;
                  destruct ph as [ph | ph]; rewrite ph in pr; check_nil_contradiction;
                  try rewrite app_nil_l in pr; try rewrite app_nil_r in pr
    end
  end.

Ltac check_contradiction_prL_preT :=
  match goal with
  | [   rs : rsub (nslcrule (seqrule ?princrules)) ?rules,
        pr : ?princrules ?ps (?l1, ?l2),
        loe : forall (ps : list (rel (list (PropF ?V)))) (x y Δ : list (PropF ?V)),
            ?princrules ps (x ++ y, Δ) -> (x = []) + (y = []) |- _ ] =>
    match l1 with
    | ?A ++ ?B => let ph := fresh "H" in specialize (loe _ _ _ _ pr) as H;
                  destruct ph as [ph | ph]; rewrite ph in pr; check_nil_contradiction;
                  try rewrite app_nil_l in pr; try rewrite app_nil_r in pr
    end
  end.

Ltac check_contradiction_prR_pre :=
  match goal with
  | [   rs : rsub (nslcrule (seqrule ?princrules)) ?rules,
        pr : ?princrules ?ps (?l1, ?l2),
        loe : forall (ps : list (rel (list (PropF ?V)))) (x y Γ : list (PropF ?V)),
            ?princrules ps (Γ, x ++ y) -> x = [] \/ y = [] |- _ ] =>
    match l2 with
    | ?A ++ ?B => let ph := fresh "H" in specialize (loe _ _ _ _ pr) as H;
                  destruct ph as [ph | ph]; rewrite ph in pr; check_nil_contradiction;
                  try rewrite app_nil_l in pr; try rewrite app_nil_r in pr
    end
  end.

Ltac check_contradiction_prR_preT :=
  match goal with
  | [   rs : rsub (nslcrule (seqrule ?princrules)) ?rules,
        pr : ?princrules ?ps (?l1, ?l2),
        loe : forall (ps : list (rel (list (PropF ?V)))) (x y Γ : list (PropF ?V)),
            ?princrules ps (Γ, x ++ y) -> (x = []) + (y = []) |- _ ] =>
    match l2 with
    | ?A ++ ?B => let ph := fresh "H" in specialize (loe _ _ _ _ pr) as H;
                  destruct ph as [ph | ph]; rewrite ph in pr; check_nil_contradiction;
                  try rewrite app_nil_l in pr; try rewrite app_nil_r in pr
    end
  end.

Ltac check_contradiction_pr :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    repeat (list_assoc_r_singleton_hyp2 pr;
            try check_contradiction_prL_pre;
            try check_contradiction_prR_pre)
  end.

Ltac check_contradiction_prT :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    repeat (list_assoc_r_singleton_hyp2 pr;
            try check_contradiction_prL_preT;
            try check_contradiction_prR_preT)
  end.

Ltac contL_setup_nil :=
  unf_pfs_all; match goal with
    | [ acm : dersrec _ _ (map _ (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
       add_empty_goal_R l1 || (rewrite app_assoc;  add_empty_goal_R l1)
  end.

Ltac contR_setup_nil :=
  unf_pfs_all; match goal with
    | [ acm : dersrec _ _ (map _ (map (seqext ?l1 ?l2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
       add_empty_goal_R Ψ1 || (rewrite app_assoc;  add_empty_goal_R Ψ1)
  end.


Ltac contL_setup  :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
            rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    match l1 with
    | nil => contL_setup_nil
    | _ => assoc_mid l1; rewrite app_assoc
    end
  end.

Ltac contR_setup  :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
            rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    match l2 with
    | nil => contR_setup_nil
    | _ => assoc_mid l2; rewrite app_assoc
    end
  end.

Ltac contR_setup_extra_pre  :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, []),
            rs  : rsub (nslcrule (seqrule ?princrules)) ?rules |- _ ] =>
    rewrite (app_assoc _ l1)
  end.

Ltac contR_setup_extra :=
  contR_setup; try contR_setup_extra_pre.

Ltac nsgen_sw_cont_genT rs sppc c c' acm inps0 swap :=
derIrs rs ; [>
  (assoc_mid c ; apply NSlctxt') ||
  (assoc_single_mid' c ; apply NSctxt') ||
  (list_assoc_l' ; apply NSlclctxt') ||
  (list_assoc_l' ; apply NSlcctxt') ;
  exact sppc |
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cD ; subst q ;
rename_last inps0 ;
eapply ForallT_forall in acm ;
[ | eapply InT_map in inps0; exact inps0 ]];
try eapply can_gen_contL_gen_def' in acm ;
  try eapply can_gen_contR_gen_def' in acm ;
unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  assoc_single_mid' c' ;
[ eapply acm | exact swap |
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  list_eq_assoc | (reflexivity || assumption) ].

Ltac tac_cons_singleton_arg_hyp a l H :=
    match l with
    | nil => idtac
    | _ => rewrite (cons_singleton l a) in H
    end.

Ltac tac_cons_singleton_hyps :=
  repeat
  match goal with
   | [ H : context [?a :: ?l] |- _] => progress (tac_cons_singleton_arg_hyp a l H)
  end.

Ltac lt2T a Hexch :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : ForallT (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match Γ1 with
    | ?A ++ [?a] ++ ?B => eapply prop_contL_step_pr_L in acm
    | ?A ++ [?a] => eapply prop_contL_step_pr_L_end in acm
    | _ => match Γ2 with
           | ?A ++ [?a] ++ ?B => eapply prop_contL_step_pr_R in acm
           | [?a] ++ ?A => eapply prop_contL_step_pr_R_start in acm
           end
    end
  end.

Ltac lt3T a Hexch rs carry psfull loe :=
  lazymatch goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      acm : ForallT (can_gen_contL_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
   lazymatch l1 with
    | context[ a :: [] ] =>  tac_cons_singleton_hyps;
      lt2T a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | context[ a :: _ ] =>  tac_cons_singleton_hyps ;
                           let H := fresh in 
                           pose proof (@rules_L_oe_cons_nil_blind _ _ _ _ _ _ loe pr) as H; rewrite H in pr;
                           try rewrite app_nil_r in H; subst ;
      lt2T a Hexch; [| exact carry | exact psfull| exact rs| exact pr] 
    | _ => tac_cons_singleton_hyps; lt1 a acm Hexch
    end
  end.

 Ltac nsgen_sw_contL_gen5T rs sppc c c' acm inps0 swap pr inmps exch := 
    unf_pfs_all; unf_pf_all; derIrs rs  ;
[apply NSlcctxt'; apply Sctxt_e'; exact pr |];
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cD ; 
rename_last inmps ;
eapply InT_map_iffT in inmps ; cD ;
rename_last inps0 ;  eapply InT_map in inps0 ;
  eapply InT_map in inps0 ;
subst;
eapply dersrec_forall in acm;
[| apply inps0];
destruct_princ;
derrec_swapL3 acm exch.



(* ------------------------------ *)
(* RIGHT WEAKENING FOR PRINCRULES *)
(* ------------------------------ *)

(* Makes progress on princrules ps (l1, l2) goals *)
Ltac lt1R a acm Hexch :=
  list_assoc_r_single;
  eapply (@can_gen_contR_gen_Forall_dersrec _ a) in acm; [| exact Hexch | cont_solve].

Ltac lt2R a Hexch :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : Forall (can_gen_contR_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match Ψ1 with
    | ?A ++ [?a] ++ ?B => eapply prop_contR_step1 in acm
    | ?A ++ [?a] => eapply prop_contR_step4 in acm
    | _ => match Ψ2 with
           | ?A ++ [?a] ++ ?B => eapply prop_contR_step1_OPP in acm
           | [?a] ++ ?A => eapply prop_contR_step2 in acm
           end
    end
  end.

Ltac lt2RT a Hexch :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      rs  : rsub (nslcrule (seqrule ?princrules)) ?rules,
      acm : ForallT (can_gen_contR_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match Ψ1 with
    | ?A ++ [?a] ++ ?B => eapply prop_contR_step1 in acm
    | ?A ++ [?a] => eapply prop_contR_step4 in acm
    | _ => match Ψ2 with
           | ?A ++ [?a] ++ ?B => eapply prop_contR_step1_OPP in acm
           | [?a] ++ ?A => eapply prop_contR_step2 in acm
           end
    end
  end.

Ltac lt3R a Hexch rs carry psfull loe :=
  match goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      acm : Forall (can_gen_contR_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    match l2 with
    | context[ a :: [] ] =>
      lt2R a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | context[ a :: ?l2 ] =>
      pose proof (rules_R_oe_cons_nil_blind _ _ _ _ _ loe pr); subst;
      lt2R a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | _ => lt1R a acm Hexch
    end
  end.

Ltac lt3RT a Hexch rs carry psfull loe :=
  lazymatch goal with
  | [ pr  : ?princrules ?ps (?l1, ?l2),
      acm : ForallT (can_gen_contR_gen ?rules)
                   (map (nslcext ?G ?d0) (map (seqext ?Γ1 ?Γ2 ?Ψ1 ?Ψ2) ?ps)) |- _ ] =>
    lazymatch l2 with
    | context[ a :: [] ] =>
      lt2RT a Hexch; [| exact carry | exact psfull| exact rs| exact pr]
    | context[ a :: _ ] => tac_cons_singleton_hyps ;
                           let H := fresh in 
                           pose proof (@rules_R_oe_cons_nil_blind _ _ _ _ _ _ loe pr) as H; rewrite H in pr;
                           try rewrite app_nil_r in H; subst ;
      lt2RT a Hexch; [| exact carry | exact psfull| exact rs| exact pr] 
    | _ => tac_cons_singleton_hyps; lt1R a acm Hexch
    end
  end.

Ltac nsgen_sw_contR_gen5T rs sppc c c' acm inps0 swap pr inmps exch := 
 unf_pfs_all;    derIrs rs  ;
[apply NSlcctxt'; apply Sctxt_e''; exact pr |];
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cD ; 
rename_last inmps ;
eapply InT_map_iffT in inmps ; cD ;
rename_last inps0 ;  eapply InT_map in inps0 ;
  eapply InT_map in inps0 ;
subst;
eapply dersrec_forall in acm;
[| apply inps0];
destruct_princ;
derrec_swapR3 acm exch.

(* ------- *)
(* TACTICS *)
(* ------- *)

Ltac ms_cgsTT1 acm :=
  unf_pfs_all; 
  try apply dersrec_map_2 ;
try apply dersrec_map_single ;
try (apply ForallT_map_2 in acm || apply ForallT_map_rev in acm );
try eapply can_gen_swapL_def' in acm ;
try eapply can_gen_swapR_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac ms_cgsTT2 acm :=
try apply dersrec_map_2 ;
unf_pfs_all; try match goal with
| [ |- dersrec _ _ _] => apply dersrec_map_single
end;  
try (apply ForallT_map_2 in acm || apply ForallT_map_rev in acm );
try eapply can_gen_swapL_def' in acm ;
try eapply can_gen_swapR_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac ms_cgsTT3 acm :=
try apply dersrec_map_2 ;
unf_pfs_all; try match goal with
| [ |- dersrec _ _ _] => apply dersrec_map_single
end;  
try (apply ForallT_map_2 in acm || apply ForallT_map_rev in acm );
try eapply can_gen_swapL_def' in acm ;
try eapply can_gen_swapR_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac ms_cgsTT4 acm :=
  unf_pfs_all; try match goal with
      | [ |- dersrec _ _ _ ] => apply dersrec_map_2
      end;
  try match goal with
      | [ |- dersrec _ _ _] => apply dersrec_map_single
      end;
  try match goal with
      | [ acm : ForallT _ _ |- _ ] => (apply ForallT_map_2 in acm || apply ForallT_map_rev in acm )
      | _ => idtac
      end;
try eapply can_gen_swapL_def' in acm ;
try eapply can_gen_swapR_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac ms_cgs_contT acm := 
eapply dersrec_map_single ;
eapply ForallT_map_rev in acm ;
try eapply can_gen_contL_gen_def' in acm ;
try eapply can_gen_contR_gen_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac use_acm_os_contT acm rs swap ith :=
(* swap in opposite side from where rule active *)
derIrs rs ; [> 
apply NSlclctxt || apply NSlctxt ;
apply ith | ms_cgs_contT acm ];
[exact acm |
exact swap |
reflexivity |
reflexivity].

Ltac nsgen_sw_contT rs sppc c c' acm inps0 swap :=
      derIrs rs ; [>
  (assoc_mid c ; apply NSlctxt') ||
  (assoc_single_mid' c ; apply NSctxt') ||
  (list_assoc_l' ; apply NSlclctxt') ||
  (list_assoc_l' ; apply NSlcctxt') ;
  exact sppc |
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cET ; subst q ;
rename_last inps0 ;
eapply ForallT_forall in acm ];
rename_last inps0 ;
[ | eapply InT_map in inps0 ; exact inps0];
try eapply can_gen_contL_gen_def' in acm ;
  try eapply can_gen_contR_gen_def' in acm ;
  [unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  assoc_single_mid' c' ;
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ; exact acm |
   exact swap | list_eq_assoc | reflexivity].

Ltac check_nil_cons_contr :=
  match goal with
  | [H : [] = ?l1 ++ ?a :: ?l2 |- _] => contradiction (nil_eq_list l1 l2 a H)
  | [H : ?l1 ++ ?a :: ?l2 = [] |- _] => symmetry in H; contradiction (nil_eq_list l1 l2 a H)
  | _ => idtac
  end.

Ltac cont_solve2 :=
   match goal with
   | [ |- context[?a :: ?l]] =>
     match l with
     | context[?a :: ?l2] =>  
   list_assoc_r_single;
   eapply (@contracted_gen_spec_contracted_gen _ a);
   cont_solve
     end
   end.

Ltac cont_setup_constr constr :=
  match goal with
  | [ |- context[ (@constr ?V ?A) :: ?l ] ] => list_assoc_r_single; assoc_mid ([@constr V A])
  end.

Ltac use_acm1_cont_constrT acm rs ith constr :=
        derIrs rs; [ 
apply NSlctxt2 || apply NSlclctxt' ;
cont_setup_constr constr;
apply ith | 
ms_cgs_contT acm ;
list_assoc_r' ; simpl] ;
 [ first [eapply acm | list_assoc_l'; rewrite <- app_assoc; eapply acm]
 |  | reflexivity | reflexivity]; cont_solve2.

Ltac use_acm2s_contT acm rs ith :=
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
apply ith |
ms_cgs_contT acm ;
list_assoc_r' ; simpl ;
rewrite ?list_rearr22  ] ; [> eapply acm | | reflexivity | reflexivity]; cont_solve2.

Ltac cont_setup_apply_constr constr :=
  unf_pf_all; list_assoc_r_single; 
  match goal with
  | [ acm : context[ @constr ?V ?A ] |- _ ] =>
    repeat match goal with
    | [ acm : context[ ?l1 ++ A :: ?l2 ++ ?l3 ] |-
        derrec ?rules ?p (?G1 ++ ?G2 ++ [(?K1,?K2,?d)]) ] =>
      match K1 with
      | ?l5 ++ l2 ++ ?l4 => idtac
      | ?l5 ++ ?l4 => rewrite (app_assoc l5)
      end
    end
  end.

Ltac cont_setup_apply_constr2 constr :=
  unf_pf_all; list_assoc_r_single;
  match goal with
  | [ acm : context[ @constr ?V ?A ] |- _ ] =>
    repeat match goal with
    | [ acm : context[ ?l1 ++ A :: ?l2 ++ ?l3 ] |-
        derrec ?rules ?p (?G1 ++ ?G2 ++ [(?K1,?K2,?d)]) ] =>
      match K1 with
      | ?l5 ++ l3 ++ ?l4 => idtac
      | ?l5 ++ ?l4 => rewrite (app_assoc l5)
      end
    end
  end.

Ltac cont_setup_apply_constr3 constr :=
  unf_pf_all; list_assoc_r_single;
  match goal with
  | [ acm : context[ @constr ?V ?A ] |- _ ] =>
    repeat match goal with
    | [ acm : context[ ?l1 ++ A :: ?l2 ] |-
        derrec ?rules ?p (?G1 ++ ?G2 ++ [(?K1,?K2,?d)]) ] =>
      match K1 with
      | ?l5 ++ l2 ++ ?l4 => idtac
      | ?l5 ++ ?l4 => rewrite (app_assoc l5)
      end
    end
  end.

Ltac use_acm2s_cont'T acm rs ith constr :=
   unf_pf_all;    derIrs rs ;
  [> apply NSlctxt2 || apply NSlclctxt' ;
   apply ith |
   ms_cgs_contT acm ;
   list_assoc_r' ; simpl ;
   rewrite ?list_rearr22 ] ; [> eapply acm | | reflexivity | reflexivity];
    cont_solve2.

Ltac use_acm_sw_sep_contT acm rs weak ith :=
unf_pf_all; derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
             ms_cgs_contT acm ]; try exact weak ;
[> (rewrite <- app_nil_r; rewrite <- app_assoc ; rewrite <- list_rearr21; eapply acm) ||
                                                                                      (eapply acm) | 
 apps_eq_tac | reflexivity ].

Ltac cont_setup_apply_constr4 constr :=
  unf_pf_all; list_assoc_r_single;
  repeat match goal with
         | [ acm : context[ ?l1 ++ @constr ?V ?A :: ?l2 ++ ?l3 ] |-
             derrec ?rules ?p (?G1 ++ [(?K1,?K2,?d)] ++ ?G2) ] =>
           match K1 with
           | ?l5 ++ l2 ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
         end.

Ltac cont_setup_apply_constr5 constr :=
  unf_pf_all; list_assoc_r_single;
  repeat match goal with
         | [ acm : context[ ?l1 ++ @constr ?V ?A :: ?l3 ++ ?l2 ] |-
             derrec ?rules ?p (?G1 ++ [(?K1,?K2,?d)] ++ ?G2) ] =>
           match K1 with
           | ?l5 ++ l2 ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
         end.

Ltac cont_setup_apply_constr6 constr :=
  unf_pf_all; list_assoc_r_single;
  repeat match goal with
         | [ acm : context[ ?l1 ++ @constr ?V ?A :: ?l2 ] |-
             derrec ?rules ?p (?G1 ++ [(?K1,?K2,?d)] ++ ?G2) ] =>
           match K1 with
           | ?l5 ++ l2 ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
         end.

Ltac cont_setup_apply_constr7 constr:=
  unf_pf_all; list_assoc_r_single;
  repeat match goal with
         | [ acm : context[ ?l1 ++ @constr ?V ?A :: ?l2 ] |-
             derrec ?rules ?p (?G1 ++ ?G2 ++ [(?K1,?K2,?d)]) ] =>
           match K1 with
           | ?l5 ++ [@constr V A] ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
         end.

Ltac no_use_acm_cont rs drs constr:=
  unf_pf_all; derIrs rs;
  [apply NSlclctxt'; apply constr |
   exact drs].

Ltac acmi_snr_cont acmi swap := 
 unf_pf_all;  eapply acmi ; [> apply nslclext_def | reflexivity ].

Ltac use_acm_2_contT acm rs swap ith :=
unf_pf_all; derIrs rs ; [>
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
inversion swap; (subst; split ; 
[ acmi_snr_cont acm1 swap | acmi_snr_cont acm2 swap ])
            ].

Lemma can_gen_contL_gen_imp: forall {V : Set} 
  (rules : rlsT (@LNS V)) ns,
  can_gen_contL_gen rules ns -> forall G K s Γ Δ Γ' (d : dir), 
  contracted_gen Γ Γ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
    pf rules (G ++ (pair Γ' Δ, d) :: K).
Proof.  intros until 0. intro H.
  eapply can_gen_contL_gen_def'. exact H. Qed.

Lemma can_gen_contR_gen_imp: forall {V : Set} 
  (rules : rlsT (@LNS V)) ns,
  can_gen_contR_gen rules ns -> forall G K s Γ Δ Δ' (d : dir), 
  contracted_gen Δ Δ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
    pf rules (G ++ (pair Γ Δ', d) :: K).
Proof.  intros until 0. intro H.
  eapply can_gen_contR_gen_def'. exact H. Qed.

Ltac contL2T rs sppc acm swap :=
unf_pf_all; derIrs rs ; [> list_assoc_l' ;
    apply NSlclctxt' || apply NSlctxt2 ; exact sppc | ] ;
eapply dersrec_forall ; intros L H ;
eapply InT_map_iffT in H ; destruct H as [H3 H]; destruct H as [H1 H2] ; subst ;
  eapply ForallT_forall in acm ;
  [ |  eapply InT_map in H2 ; eapply H2 ] ;
(eapply can_gen_contL_gen_imp in acm || eapply can_gen_contR_gen_imp in acm) ;
  [> | exact swap | | reflexivity ] ;
  [> unfold nslclext ; list_assoc_r' ; exact acm
    | unfold nslclext ; list_assoc_r' ; reflexivity].

Ltac acmi_snr_snd_weak acmi swap :=
  unf_pf_all; rewrite list_rearr16' ; eapply acmi ;
  [>  list_assoc_r' ; simpl ; apply nslclext_def |
    reflexivity ].

Ltac use_acm_2_snd_contT acm rs swap ith :=
unf_pf_all; derIrs rs ; [ list_assoc_r' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
inversion swap; (subst; split;
[ acmi_snr_snd_weak acm1 swap | acmi_snr_snd_weak acm2 swap ])
            ].

Ltac ltstart'T acm acm1 acm2 :=
 unf_pf_all;  ms_cgsTT4 acm ; destruct acm as [acm1 acm2];
  list_assoc_r_s_arg acm1;
  list_assoc_r_s_arg acm2;
  list_assoc_r_single.

Ltac ltsolve' acm1a acm1b acm2a acm2b :=
  list_assoc_r_s_arg acm1a;
  list_assoc_r_s_arg acm1b;
  list_assoc_r_s_arg acm2a;
  list_assoc_r_s_arg acm2b;
  list_assoc_r_single;
  split; [ exact acm1a || exact acm1b | exact acm2a || exact acm2b].

Ltac ltsolve_pre acm1a acm1b acm2a acm2b :=
  list_assoc_r_s_arg acm1a;
  list_assoc_r_s_arg acm1b;
  list_assoc_r_s_arg acm2a;
  list_assoc_r_s_arg acm2b;
  list_assoc_r_single.

Ltac ltsolve_end acm1a acm1b acm2a acm2b :=
    split; [ exact acm1a || exact acm1b | exact acm2a || exact acm2b].

Ltac ltmidacm' acm1 acm2 acm1a acm1b acm2a acm2b :=
  edestruct acm1 as [acm1a acm1b]; [reflexivity | reflexivity |];
  edestruct acm2 as [acm2a acm2b]; [reflexivity | reflexivity |].

Ltac ltmidacm'T acm1 acm2 acm1a acm1b acm2a acm2b :=
  edestruct acm1 as [acm1a acm1b]; [reflexivity | reflexivity |];
  edestruct acm2 as [acm2a acm2b]; [reflexivity | reflexivity |].

Ltac ltbrack1 acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G ([(?Γ, ?l, ?d)] ++ ?s)) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 => idtac
    | ?l2 ++ (?l3 ++ ?l4) => rewrite (app_assoc l2) in acm1
    end
         end.

Ltac ltbrack2 acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G ([(?Γ, ?l, ?d)] ++ ?s)) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ [a] ++ ?l4 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ ?l4 => rewrite (app_assoc l3) in acm1
    end
         end.

Ltac assoc_mid_hyp l H := 
  list_assoc_r_s_arg H ;
  rewrite ?app_comm_cons in H ;
  repeat ((rewrite - (app_assoc _ l _) in H; fail 1) || rewrite app_assoc in H) ;
  rewrite - (app_assoc _ l _)  in H.

Ltac ltbrack_concl_pre Γ l :=
  repeat match goal with
  | [ |- context[ (Γ, ?l1, ?d) ] ] =>
    match l1 with
    | l ++ ?l2 => idtac
    | ?l2 ++ ?l3 => rewrite (app_assoc l2)
    end
         end.

Ltac ltbrack_concl acm1 :=
  match type of acm1 with
  | context[ [(?Γ, ?l1 ++ [?A] ++ ?l2, ?d)] ++ ?s ] =>
    ltbrack_concl_pre Γ l1
  end.

Ltac ltapplyruleT rs WBox1Rs acm1 :=
  unf_pf_all; derIrs rs; [apply NSlclctxt'; simpl; apply WBox1Rs |
              list_assoc_r_single; ms_cgsTT4 acm1].

Ltac ltsolve_full_preT acm acm1 acm2 acm1a acm1b acm2a acm2b A rs WBox1Rs a :=
  unf_pf_all; ltstart'T acm acm1 acm2;
  assoc_mid_hyp [A] acm1;
  ltbrack_concl acm1;
  ltapplyruleT rs WBox1Rs acm1;
  list_assoc_r_s_arg acm1;
  list_assoc_r_s_arg acm2;
  ltbrack1 acm1 a;
  ltbrack2 acm1 a;
  ltbrack1 acm2 a;
  ltbrack2 acm2 a;
  ltmidacm' acm1 acm2 acm1a acm1b acm2a acm2b.

Ltac apply_exch Hexch :=
  eapply Hexch; [tauto | | reflexivity | reflexivity].

Ltac sep_nil :=
  match goal with
  | [ |- context[ [?a] ++ [?a] ++ ?l2] ] =>
    rewrite <- (app_nil_l ([a] ++ l2))
  end.

Ltac ltapplyrule2T rs rw WBox1Rs acm1 :=
  unf_pf_all; derIrs rs; [apply NSlclctxt'; rw; simpl; apply WBox1Rs |
  list_assoc_r_single; ms_cgsTT4 acm1].

Ltac ltbrack1_snd acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G (?s ++ [(?Γ, ?l, ?d)])) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 => idtac
    | ?l2 ++ (?l3 ++ ?l4) => rewrite (app_assoc l2) in acm1
    end
  end.

Ltac ltbrack2_snd acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G (?s ++ [(?Γ, ?l, ?d)])) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ [a] ++ ?l4 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ ?l4 => rewrite (app_assoc l3) in acm1
    end
  end.

Ltac ltbrack1_mid acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G (?s ++ [(?Γ, ?l, ?d)] ++ ?s2)) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 => idtac
    | ?l2 ++ (?l3 ++ ?l4) => rewrite (app_assoc l2) in acm1
    end
  end.

Ltac ltbrack2_mid acm1 a :=
  repeat match type of acm1 with
  | can_gen_contR_gen ?rules (nslclext ?G (?s ++ [(?Γ, ?l, ?d)] ++ ?s2)) =>
    match l with
    | [a] ++ ?l2 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ [a] ++ ?l4 => idtac
    | ?l2 ++ [a] ++ ?l3 ++ ?l4 => rewrite (app_assoc l3) in acm1
    end
  end.

Ltac ltmidacm'2 acm1 acm2 acm1a acm1b acm2a acm2b G :=
  unf_pf_all; edestruct acm1 as [acm1a acm1b];
  [unfold nslclext; rewrite (app_assoc G); reflexivity | reflexivity |];
  edestruct acm2 as [acm2a acm2b];
  [unfold nslclext; rewrite (app_assoc G); reflexivity | reflexivity |].  

Ltac ltsolve_full_pre2T acm acm1 acm2 acm1a acm1b acm2a acm2b A rs Constr WBox1Rs a G:=
  unf_pf_all; ltstart'T acm acm1 acm2;
  assoc_mid_hyp [A] acm1;
  ltbrack_concl acm1;
  ltapplyrule2T rs ltac : (assoc_mid [(@Constr _  A)]) WBox1Rs acm1;
  list_assoc_r_s_arg acm1;
  list_assoc_r_s_arg acm2;
  ltbrack1_snd acm1 a;
  ltbrack2_snd acm1 a;
  ltbrack1_mid acm2 a;
  ltbrack2_mid acm2 a;
  ltmidacm'2 acm1 acm2 acm1a acm1b acm2a acm2b G.

Ltac ltmidacm'3 acm1 acm2 acm1a acm1b acm2a acm2b G :=
  unf_pf_all; edestruct acm1 as [acm1a acm1b];
  [unfold nslclext; rewrite (app_assoc G); reflexivity | try sep_nil; reflexivity |];
  edestruct acm2 as [acm2a acm2b];
  [unfold nslclext; rewrite (app_assoc G); reflexivity | try sep_nil ; reflexivity |].

Ltac ltsolve_full_pre3T acm acm1 acm2 acm1a acm1b acm2a acm2b A rs Constr WBox1Rs a G:=
  unf_pf_all; ltstart'T acm acm1 acm2;
  ltbrack_concl acm1;
  ltapplyrule2T rs ltac : (assoc_mid [@Constr _ A]) WBox1Rs acm1;
  list_assoc_r_s_arg acm1;
  list_assoc_r_s_arg acm2;
  ltbrack1_snd acm1 a;
  ltbrack2_snd acm1 a;
  ltbrack1_mid acm2 a;
  ltbrack2_mid acm2 a;
  list_assoc_r_s_arg acm1;
  list_assoc_r_s_arg acm2;
  ltmidacm'3 acm1 acm2 acm1a acm1b acm2a acm2b G.

Ltac b1R_extra1 Hexch acm1b acm2a A0 :=
  split;
  [rewrite (app_assoc A0); apply_exch Hexch;
   list_assoc_r_single; apply_exch Hexch;
   exact acm1b |
   apply_exch Hexch; exact acm2a].

Ltac b1R_extra2 Hexch acm1b acm2b A0 H4 :=
  split;
  [rewrite (app_assoc A0); rewrite (app_assoc H4);
   apply_exch Hexch; list_assoc_r_single; exact acm1b |
   exact acm2b].

Ltac b1R_extra3 Hexch acm1b acm2b A0 :=
  split;
  [rewrite (app_assoc A0); apply_exch Hexch;
   list_assoc_r_single; exact acm1b | exact acm2b].

Ltac b1R_extra1_look Hexch acm1b acm2a :=
  match goal with
  | [ |- context[ _ ++ [(?Γ, ?A0 ++ ?l, ?d)] ++ _ ] ] =>
    b1R_extra1 Hexch acm1b acm2a A0
  end.

Ltac b1R_extra2_look Hexch acm1b acm2b :=
  match goal with
  | [ |- context[ _ ++ [(?Γ, ?A0 ++ ?l ++ ?H4 ++ ?l2, ?d)] ++ _ ] ] =>
    b1R_extra2 Hexch acm1b acm2b A0 H4
  end.

Ltac b1R_extra3_look Hexch acm1b acm2b :=
  match goal with
  | [ |- context[ _ ++ [(?Γ, ?A0 ++ ?l, ?d)] ++ _ ] ] =>
    b1R_extra3 Hexch acm1b acm2b A0
  end.

Ltac ltsolve_fullT acm A rs WBox1Rs a Hexch :=
 unf_pf_all;  let acm1 := fresh "acm1" in let acm2 := fresh "acm2" in
  let acm1a := fresh "acm1a" in let acm1b := fresh "acm1b" in
  let acm2a := fresh "acm2a" in let acm2b := fresh "acm2b" in               
  ltsolve_full_preT acm acm1 acm2 acm1a acm1b acm2a acm2b A rs WBox1Rs a;
  ltsolve_pre acm1a acm1b acm2a acm2b;
  try ltsolve_end acm1a acm1b acm2a acm2b;   
  b1R_extra1_look Hexch acm1b acm2a ||
  b1R_extra2_look Hexch acm1b acm2b ||
  b1R_extra3_look Hexch acm1b acm2b.

Ltac ltsolve_full23T acm A rs WBox WBox1Rs a G :=
  unf_pf_all; let acm1 := fresh "acm1" in let acm2 := fresh "acm2" in
  let acm1a := fresh "acm1a" in let acm1b := fresh "acm1b" in
  let acm2a := fresh "acm2a" in let acm2b := fresh "acm2b" in               
  (ltsolve_full_pre2T acm acm1 acm2 acm1a acm1b acm2a acm2b A rs WBox WBox1Rs a G ||
  ltsolve_full_pre3T acm acm1 acm2 acm1a acm1b acm2a acm2b A rs WBox WBox1Rs a G);
  ltsolve' acm1a acm1b acm2a acm2b.

Ltac processT swap :=
  inversion_clear swap; subst;
  repeat (acacDeT2 ; subst ; simpl ; rem_nil).


Ltac cont_setup_apply_constr5' constr :=
  unf_pf_all; list_assoc_r_single;
  repeat match goal with
         | [ |-
             derrec ?rules ?p (?G1 ++ [(?K1,?K2,?d)] ++ ?G2) ] =>
           match goal with
           | [  |- context[ @constr ?V ?A ] ] =>
             match goal with
               [  acm : context[ ?l1 ++ A :: ?l3 ++ ?l2 ] |- _ ] =>
           match K1 with
           | ?l5 ++ l2 ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
             end
           end
         end.

Ltac cont_setup_apply_constr6' constr :=
  unf_pf_all; list_assoc_r_single;
  repeat match goal with
         | [  |-
              derrec ?rules ?p (?G1 ++ [(?K1,?K2,?d)] ++ ?G2) ] =>
           match goal with
           | [  |- context[ @constr ?V ?A ] ] =>
             match goal with
               [  acm : context[ ?l1 ++ A :: ?l2 ] |- _ ] =>
           match K1 with
           | ?l5 ++ l2 ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
             end
           end
         end.

Ltac cont_setup_apply_constr7' constr:=
 unf_pf_all;  list_assoc_r_single;
  repeat match goal with
         | [  |-
             derrec ?rules ?p (?G1 ++ ?G2 ++ [(?K1,?K2,?d)]) ] =>
           match goal with
           | [  |- context[ @constr ?V ?A ] ] =>
             match goal with
               [  acm : context[ ?l1 ++ A :: ?l2 ] |- _ ] =>
           match K1 with
           | ?l5 ++ [@constr V A] ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
             end
           end
         end.

Ltac cont_setup_apply_constr4' constr :=
  unf_pf_all; list_assoc_r_single;
  repeat match goal with
         | [  |-
             derrec ?rules ?p (?G1 ++ [(?K1,?K2,?d)] ++ ?G2) ] =>
           match goal with
           | [  |- context[ @constr ?V ?A ] ] =>
             match goal with
               [  acm : context[ ?l1 ++ A :: ?l2 ++ ?l3 ] |- _ ] =>
           match K1 with
           | ?l5 ++ l2 ++ ?l4 => idtac 
           | ?l5 ++ ?l4 => rewrite (app_assoc l5)
           end
             end
           end
         end.

