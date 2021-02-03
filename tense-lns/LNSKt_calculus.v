Add LoadPath "../general".

Require Export require_general.
Require Export require_rules.
Require Import require_structural.
Require Import merge.

Set Implicit Arguments.

Inductive LNSKt_rules (V : Set) : rlsT (@LNS V) :=
  | b2r : forall ps c, nslclrule (@b2rrules V) ps c -> LNSKt_rules ps c
  | b1r : forall ps c, nslclrule (@b1rrules V) ps c -> LNSKt_rules ps c
  | b2l : forall ps c, nslclrule (@b2lrules V) ps c -> LNSKt_rules ps c
  | b1l : forall ps c, nslclrule (@b1lrules V) ps c -> LNSKt_rules ps c
  | nEW : forall ps c, nslclrule (@EW_rule V) ps c -> LNSKt_rules ps c
  | prop : forall ps c, 
      nslcrule (seqrule (@rs_prop V)) ps c -> LNSKt_rules ps c.

Definition pf_LNSKt {V : Set} ns := derrec (@LNSKt_rules V) (fun _ => False) ns.
Definition pfs_LNSKt {V : Set} lns := dersrec (@LNSKt_rules V) (fun _ => False) lns.

Ltac unf_pflnskt := unfold pf_LNSKt.
Ltac unf_pflnskt_all := unfold pf_LNSKt in *.

Ltac unf_pfslnskt := unfold pfs_LNSKt.
Ltac unf_pfslnskt_all := unfold pfs_LNSKt in *.

Ltac unf_pfall := unf_pflnskt_all; unf_pfslnskt_all; unf_pf_all; unf_pfs_all.


(* ----------------- *)
(* SOME AXIOM LEMMAS *)
(* ----------------- *)

Lemma Id_InT: forall {V : Set} GH Γ Δ d p,
    InT (Var p) Γ ->
    InT (Var p) Δ ->
    @pf_LNSKt V (GH ++ [(Γ,Δ,d)]).
Proof.
  intros until 0; intros Hin1 Hin2.
  destruct (InT_seqext Hin1 Hin2) as [H1 [H2 [H3 [H4 H5]]]].
  eapply derI. eapply prop.
  econstructor.
  eapply seqrule_same.
  econstructor.
  eapply Id.
  eassumption.
  econstructor.
Qed.

Lemma BotL_InT: forall {V : Set} GH Γ Δ d,
    InT (Bot V) Γ ->
    @pf_LNSKt V (GH ++ [(Γ,Δ,d)]).
Proof.
  intros until 0; intros Hin.
  destruct (@InT_seqextL _ _ Δ _ Hin) as [H1 [H2 H3]].
  eapply derI. eapply prop.
  econstructor.
  eapply seqrule_same.
  econstructor.
  eapply BotL.
  eassumption.
  econstructor.
Qed.

Lemma rsub_rs_prop_LNSKt_rules : forall V,
  rsub (nslcrule (seqrule (rs_prop (V:=V)))) (LNSKt_rules (V:=V)).
Proof. 
  unfold rsub. intros V u v H. 
  eapply prop. exact H.
Qed.


(* --------------------------------------------- *)
(* LEFT AND RIGHT EXCHANGE FOR THE FULL CALCULUS *)
(* --------------------------------------------- *)

Lemma LNSKt_exchL: forall (V : Set) ns
  (D : @pf_LNSKt V ns),
      can_gen_swapL (@LNSKt_rules V) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_indT in D.
exact D. tauto.
intros H1 H2 H3 H4 H5. inversion H3 ; subst ; [> pose gen_swapL_step_b2R_lc 
  | pose gen_swapL_step_b1R_lc
  | pose gen_swapL_step_b2L_lc
  | pose gen_swapL_step_b1L_lc
  | pose gen_swapL_step_EW_lc
  | pose gen_swapL_step_pr_lc ] ; 
unfold gen_swapL_step in g ; egx g ;
  clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.

Lemma LNSKt_exchR: forall (V : Set) ns
  (D : @pf_LNSKt V ns),
      can_gen_swapR (@LNSKt_rules V) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_indT in D.
exact D. tauto.
intros H1 H2 H3 H4 H5; inversion H3 ; subst ; [> pose gen_swapR_step_b2R_lc as g
  | pose gen_swapR_step_b1R_lc as g
  | pose gen_swapR_step_b2L_lc as g
  | pose gen_swapR_step_b1L_lc as g
  | pose gen_swapR_step_EW_lc as g
  | pose gen_swapR_step_pr_lc as g] ;
unfold gen_swapR_step in g ; egx g ;
  clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.


(* --------------------------------------- *)
(* FULL LEFT AND RIGHT WEAKENING FOR LNSKT *)
(* --------------------------------------- *)

Lemma LNSKt_weakR: forall (V : Set) ns
  (D : @pf_LNSKt V ns),
      can_gen_weakR (@LNSKt_rules V) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_indT in D.
exact D. tauto.
intros. inversion X ; subst ; [> pose gen_weakR_step_b2R_lc 
  | pose gen_weakR_step_b1R_lc; egx_app g LNSKt_exchR
  | pose gen_weakR_step_b2L_lc
  | pose gen_weakR_step_b1L_lc
  | pose gen_weakR_step_EW_lc
  | pose gen_weakR_step_pr_lc ] ; 
        unfold gen_weakR_step in g; try egx g;
  clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.

Lemma LNSKt_weakL: forall (V : Set) ns
  (D : @pf_LNSKt V ns),
      can_gen_weakL (@LNSKt_rules V) ns.
Proof.
intro.  intro.  intro.
eapply derrec_all_indT in D.
exact D. tauto.
intros. inversion X ; subst ; [> pose gen_weakL_step_b2R_lc 
  | pose gen_weakL_step_b1R_lc
  | pose gen_weakL_step_b2L_lc
  | pose gen_weakL_step_b1L_lc
  | pose gen_weakL_step_EW_lc
  | pose gen_weakL_step_pr_lc ] ; 
unfold gen_weakL_step in g ; egx g ;
  clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.


(* ----------------------------- *)
(* SOME GENERAL WEAKENING LEMMAS *)
(* ----------------------------- *)

Lemma external_weakeningR : forall {V : Set} ns1 ns2,
    @pf_LNSKt V ns1 ->
    @pf_LNSKt V (ns1 ++ ns2).
Proof.
  intros V ns1 ns2. revert ns1.
  induction ns2; intros ns1 Hder.
  rewrite app_nil_r. assumption.
  rewrite app_cons_single. eapply IHns2.
  eapply derI. eapply nEW. constructor.
  destruct a as [r d]. destruct r. constructor.
  unfold nslclext. simpl. rewrite app_nil_r.
  constructor. eapply Hder.
  eapply dlNil.
Qed.

Lemma derrec_weakened_multiL : forall {V : Set} Γ1 Γ2 Δ d X Y,
  weakened_multi Γ1 Γ2 ->
pf_LNSKt (X ++ [(Γ1, Δ, d)] ++ Y) ->
@pf_LNSKt V (X ++ [(Γ2, Δ, d)] ++ Y).
Proof.
  intros V Γ1 Γ2 Δ d X Y Hc Hd.
  revert X Y Δ d Hd.
  induction Hc; intros XX YY Δ d Hd.
  assumption.
  eapply IHHc.
  inversion w; subst;
  eapply LNSKt_weakL.
  eapply Hd. reflexivity. reflexivity.
Qed.

Lemma derrec_weakened_multiR : forall {V : Set} Γ Δ1 Δ2 d X Y,
  weakened_multi Δ1 Δ2 ->
pf_LNSKt (X ++ [(Γ, Δ1, d)] ++ Y) ->
@pf_LNSKt V (X ++ [(Γ, Δ2, d)] ++ Y).
Proof.
  intros V Γ Δ1 Δ2 d X Y Hc Hd.
  revert X Y Γ d Hd.
  induction Hc; intros XX YY Γ d Hd.
  assumption.
  eapply IHHc.
  inversion w; subst;
  eapply LNSKt_weakR.
  eapply Hd. reflexivity. reflexivity.
Qed.

Lemma derrec_weakened_seqL: forall {V : Set} s1 s2 X Y,
  weakened_seqL s1 s2 ->
pf_LNSKt (X ++ [s1] ++ Y) ->
@pf_LNSKt V (X ++ [s2] ++ Y).
Proof.
  intros V s1 s3 X Y Hc Hd.
  inversion Hc. subst.
  eapply derrec_weakened_multiL.
  exact H. assumption.
Qed.

Lemma derrec_weakened_seqR: forall {V : Set} s1 s2 X Y,
  weakened_seqR s1 s2 ->
pf_LNSKt (X ++ [s1] ++ Y) ->
@pf_LNSKt V (X ++ [s2] ++ Y).
Proof.
  intros V s1 s3 X Y Hc Hd.
  inversion Hc. subst.
  eapply derrec_weakened_multiR.
  exact H. assumption.
Qed.

Lemma derrec_weakened_seq: forall {V : Set} s1 s2 X Y,
  weakened_seq s1 s2 ->
pf_LNSKt (X ++ [s1] ++ Y) ->
@pf_LNSKt V (X ++ [s2] ++ Y).
Proof.
  intros V s1 s2 X Y Hc Hd.
  inversion Hc; subst.
  eapply derrec_weakened_seqL; eassumption.
  eapply derrec_weakened_seqR; eassumption.
  eapply derrec_weakened_seqR. eassumption.
  eapply derrec_weakened_seqL; eassumption.
Qed.

Lemma derrec_weakened_nseq_gen : forall {V : Set} ns1 ns2 X Y,
  weakened_nseq ns1 ns2 ->
pf_LNSKt (X ++ ns1 ++ Y) ->
@pf_LNSKt V (X ++ ns2 ++ Y).
Proof.
  intros V s1 s2 X Y Hc.
  revert X Y. 
  induction Hc as [ | ];
    intros X Y Hd; subst.
  +{ eapply Hd. }
  +{ simpl in Hd. 
     rewrite cons_singleton in Hd.
     eapply derrec_weakened_seq in Hd.
     2 : exact w.
     simpl. rewrite app_cons_single. eapply IHHc.
     rewrite <- app_cons_single. exact Hd. }
Qed.
  
Lemma derrec_weakened_nseq : forall {V : Set} G H,
  weakened_nseq H G ->
  pf_LNSKt H ->
  @pf_LNSKt V G.
Proof.
  intros until 0; intros Hc Hd.
  assert (G =  ([] ++ G ++ [])) as Hass1.
  rewrite app_nil_r. reflexivity.
  rewrite Hass1. eapply derrec_weakened_nseq_gen.
  eapply Hc.
  rewrite app_nil_r. assumption.
Qed.

Ltac inversion_input input :=
  match goal with
  | [ H : input |- _ ] => inversion H
  | [ H : input _ |- _ ] => inversion H
  | [ H : input _ _ |- _ ] => inversion H
  | [ H : input _ _ _ |- _ ] => inversion H                                 
  | [ H : input _ _ _ _ |- _ ] => inversion H
  | [ H : input _ _ _ _ _ |- _ ] => inversion H
  end.

Lemma derrec_nil_not: forall {V : Set},
    @pf_LNSKt V [] -> False.
Proof.
  intros V H.
  inversion H. contradiction.
  subst.
  inversion_input (@LNSKt_rules V);
    try inversion_input nslclrule;
    try inversion_input nslcrule;
    try inversion_input b2rrules;
    try inversion_input b1rrules;
    try inversion_input b1lrules;
    try inversion_input b2lrules;
    try inversion_input EW_rule;
    try inversion_input seqrule;
    try inversion_input rs_prop;
    subst;
      unfold nslclext in *;
      unfold nslcext in *;
      try match goal with
      | [ H : ?L ++ ?L2 = [] |- _ ] => destruct L; discriminate
      end.
Qed.

Lemma derrec_struct_equiv_mergeL : forall (V : Set) G H GH,
    struct_equiv_str G H ->
    merge G H GH ->
    pf_LNSKt G ->
    @pf_LNSKt V GH.
Proof.
  intros until 0; intros Hs Hm Hd.
  eapply derrec_weakened_nseq.
  eapply merge_weakened_nseqL.
  eassumption. eassumption.
  eassumption.
Qed.

Lemma derrec_struct_equiv_mergeR : forall (V : Set) G H GH,
    struct_equiv_str G H ->
    merge G H GH ->
    pf_LNSKt H ->
    @pf_LNSKt V GH.
Proof.
  intros until 0; intros Hs Hm Hd.
  eapply derrec_weakened_nseq.
  eapply merge_weakened_nseqR.
  eassumption. eassumption.
  eassumption.
Qed.

Lemma derrec_weakened_nseq_nslclext : forall {V : Set} X Y ns,
  weakened_nseq X Y ->
pf_LNSKt (nslclext X ns) ->
@pf_LNSKt V (nslclext Y ns).
Proof.
  intros until 0; intros Hw Hd.
  unfold nslclext in *.
  rewrite <- (app_nil_l X) in Hd.
  rewrite <- (app_nil_l Y).
  list_assoc_r.
  list_assoc_r_arg Hd.
  eapply derrec_weakened_nseq_gen;
  eassumption.
Qed.

Ltac solve_derrec_weak_arg D :=
  eapply derrec_weakened_nseq; [ | eapply D];
  list_assoc_r_single;
  weakened_nseq_solve2.



(* ----------------------------------------- *)
(* FULL LEFT AND RIGHT CONTRACTION FOR LNSKT *)
(* ----------------------------------------- *)

Lemma LNSKt_contR_gen: forall (V : Set) ns
  (D : @pf_LNSKt V ns),
      can_gen_contR_gen (@LNSKt_rules V) ns.
Proof.
  intros. eapply derrec_all_indT in D.
  exact D. tauto.
  intros until 0; intros H H1 H2. inversion H ; subst ;
          [> pose gen_contR_gen_step_b2R_lc as g
  | pose gen_contR_gen_step_b1R_lc as g; egx_app g LNSKt_exchR
  | pose gen_contR_gen_step_b2L_lc as g
  | pose gen_contR_gen_step_b1L_lc as g
  | pose gen_contR_gen_step_EW_lc as g
  | pose gen_contR_gen_step_pr_lc as g ;  egx_app g LNSKt_exchR ]; 
        unfold gen_contR_gen_step in g; try egx g;
          clear g ; unfold rsub ; intros ; [> 
  apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.

Lemma LNSKt_contL_gen: forall (V : Set) ns
  (D : @pf_LNSKt V ns),
      can_gen_contL_gen (@LNSKt_rules V) ns.
Proof.
  intros.  eapply derrec_all_indT in D.
  exact D. tauto.
  intros until 0; intros H H1 H2. inversion H ; subst ;
          [> pose gen_contL_gen_step_b2R_lc as g
  | pose gen_contL_gen_step_b1R_lc as g
  | pose gen_contL_gen_step_b2L_lc as g
  | pose gen_contL_gen_step_b1L_lc as g
  | pose gen_contL_gen_step_EW_lc as g
  | pose gen_contL_gen_step_pr_lc as g ; egx_app g LNSKt_exchL ]; 
  unfold gen_contL_gen_step in g; try egx g;
  clear g ; unfold rsub ; intros;
  [> apply b2r | apply b1r | apply b2l | apply b1l | apply nEW | apply prop ] ;
  assumption.
Qed.


(* ------------------------------- *)
(* SOME GENERAL CONTRACTION LEMMAS *)
(* ------------------------------- *)

Lemma derrec_contracted_multiL : forall {V : Set} Γ1 Γ2 Δ d X Y,
  contracted_multi Γ1 Γ2 ->
pf_LNSKt (X ++ [(Γ1, Δ, d)] ++ Y) ->
@pf_LNSKt V (X ++ [(Γ2, Δ, d)] ++ Y).
Proof.
  intros V Γ1 Γ2 Δ d X Y Hc Hd.
  revert X Y Δ d Hd.
  induction Hc; intros XX YY Δ d Hd.
  assumption.
  eapply IHHc.
  inversion c; subst;
  eapply LNSKt_contL_gen.
  eapply Hd. reflexivity. reflexivity.
  eapply Hd. reflexivity. reflexivity.
Qed.

Lemma derrec_contracted_multiR : forall {V : Set} Γ Δ1 Δ2 d X Y,
  contracted_multi Δ1 Δ2 ->
pf_LNSKt (X ++ [(Γ, Δ1, d)] ++ Y) ->
@pf_LNSKt V (X ++ [(Γ, Δ2, d)] ++ Y).
Proof.
  intros V Γ Δ1 Δ2 d X Y Hc Hd.
  revert X Y Γ d Hd.
  induction Hc; intros XX YY Γ d Hd.
  assumption.
  eapply IHHc.
  inversion c; subst;
  eapply LNSKt_contR_gen.
  eapply Hd. reflexivity. reflexivity.
  eapply Hd. reflexivity. reflexivity.
Qed.

Lemma derrec_contracted_seqL: forall {V : Set} s1 s2 X Y,
  contracted_seqL s1 s2 ->
pf_LNSKt (X ++ [s1] ++ Y) ->
@pf_LNSKt V (X ++ [s2] ++ Y).
Proof.
  intros V s1 s3 X Y Hc Hd.
  inversion Hc. subst.
  eapply derrec_contracted_multiL.
  exact H. assumption.
Qed.

Lemma derrec_contracted_seqR: forall {V : Set} s1 s2 X Y,
  contracted_seqR s1 s2 ->
pf_LNSKt (X ++ [s1] ++ Y) ->
@pf_LNSKt V (X ++ [s2] ++ Y).
Proof.
  intros V s1 s3 X Y Hc Hd.
  inversion Hc. subst.
  eapply derrec_contracted_multiR.
  exact H. assumption.
Qed.
  
Lemma derrec_contracted_seq: forall {V : Set} s1 s2 X Y,
  contracted_seq s1 s2 ->
pf_LNSKt (X ++ [s1] ++ Y) ->
@pf_LNSKt V (X ++ [s2] ++ Y).
Proof.
  intros V s1 s2 X Y Hc. revert X Y. 
  induction Hc as [s1 s2 Hc | s1 s2 Hc | s1 s2 s3 Hc Hc2 | s1 s2 s3 Hc Hc2 ];
    intros X Y Hd; subst; try eapply IHHc2;
      (eapply derrec_contracted_seqL; eassumption) ||
      (eapply derrec_contracted_seqR; eassumption).
Qed.

Lemma derrec_contracted_nseq_gen : forall {V : Set} ns1 ns2 X Y,
  contracted_nseq ns1 ns2 ->
pf_LNSKt (X ++ ns1 ++ Y) ->
@pf_LNSKt V (X ++ ns2 ++ Y).
Proof.
  intros V s1 s2 X Y Hc.
  revert X Y. 
  induction Hc as [ | ];
    intros X Y Hd; subst.
  +{ eapply Hd. }
  +{ simpl in Hd. 
     rewrite cons_singleton in Hd.
     eapply derrec_contracted_seq in Hd.
     2 : exact c.
     simpl. rewrite app_cons_single. eapply IHHc.
     rewrite <- app_cons_single. exact Hd. }
Qed.
  
Lemma derrec_contracted_nseq : forall {V : Set} G H,
  contracted_nseq H G ->
  pf_LNSKt H ->
  @pf_LNSKt V G.
Proof.
  intros until 0; intros Hc Hd.
  assert (G =  ([] ++ G ++ [])) as Hass1.
  rewrite app_nil_r. reflexivity.
  rewrite Hass1. eapply derrec_contracted_nseq_gen.
  eapply Hc.
  rewrite app_nil_r. assumption.
Qed.
  
Lemma derrec_merge_nseq_double : forall {V : Set} G H,
  merge G G H ->
  pf_LNSKt H ->
  @pf_LNSKt V G.
Proof.
  intros until 0; intros Hm Hd.
  eapply derrec_contracted_nseq.
  eapply merge_contracted_nseq. eassumption.
  assumption.
Qed.

Lemma derrec_mergeL : forall (V : Set) G1 G2 G3,
    merge G1 G1 G3 ->
    pf_LNSKt (G3 ++ G2) ->
    @pf_LNSKt V (G1 ++ G2).
Proof.
  intros until 0; intros Hm Hd.
  rewrite <- app_nil_l.
  rewrite <- app_nil_l in Hd.
  eapply derrec_contracted_nseq_gen.
  eapply merge_contracted_nseq. eassumption.
  assumption.
Qed.
