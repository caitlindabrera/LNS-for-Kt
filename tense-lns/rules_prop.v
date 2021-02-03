Add LoadPath "../general".

Require Import require_general.
Require Import LNS.
Require Import require_structural.

Set Implicit Arguments.


Inductive rs_prop {V : Set} : rlsT (@seq V) :=
  | Id : forall p, rs_prop [] ([Var p], [Var p])
  | ImpR : forall A B,
    rs_prop [pair [A] [Imp A B ; B]] (pair [] [Imp A B])
  | ImpL : forall A B, rs_prop
      [pair [Imp A B ; B] [] ; pair [Imp A B] [A]] (pair [Imp A B] [])
  | BotL : rs_prop [] (pair [Bot V] []).


Lemma rs_prop_L_carry : forall {V : Set} ps a x Δ,
  rs_prop ps (a :: x, Δ) ->
  ForallT (fun ps' : list (PropF V) * list (PropF V) => a = hd a (fst ps')) ps.
Proof.
  intros until 0; intros H; inversion H; subst;
    repeat constructor; reflexivity.
Qed.

Lemma rs_prop_L_carry' : forall V,
    rules_L_carryT (@rs_prop V).
Proof.
  unfold rules_L_carryT.  intros until 0; intros H.
  eapply rs_prop_L_carry.  exact H.
Qed.

Lemma rs_prop_R_carry : forall {V : Set} ps a x Γ,
  rs_prop ps (Γ, a :: x) ->
  ForallT (fun ps' : list (PropF V) * list (PropF V) => a = hd a (snd ps')) ps.
Proof.
  intros until 0; intros H; inversion H; subst;
    repeat constructor; reflexivity.
Qed.

Lemma rs_prop_R_carry' : forall V,
    rules_R_carryT (@rs_prop V).
Proof.
  unfold rules_R_carryT.  intros until 0; intros H.
  eapply rs_prop_R_carry.  exact H.
Qed.

Lemma rs_prop_L_ne : forall {V : Set} ps C,
  rs_prop ps C ->
  non_empty ps ->
  ForallT (fun p : list (PropF V) * list (PropF V) => fst p <> []) ps.
Proof.
  intros until 0; intros H1 H2; inversion H1; subst;
    repeat constructor; discriminate.
Qed.

Lemma rs_prop_L_ne' : forall V, rules_L_neT (@rs_prop V).
Proof.
  unfold rules_L_neT. intros until 0; intros H1 H2.
  eapply rs_prop_L_ne. exact H1. exact H2. 
Qed.

Lemma rs_prop_R_ne : forall {V : Set} ps C,
  rs_prop ps C ->
  non_empty ps ->
  non_empty (snd C) ->
  ForallT (fun p : list (PropF V) * list (PropF V) => snd p <> []) ps.
Proof.
  intros until 0; intros H1 H2.
  inversion H1; subst;
    repeat constructor.
  discriminate. inversion H. discriminate.
Qed.
  
Lemma rs_prop_R_ne' : forall V, rules_R_neT (@rs_prop V).
Proof.
  intros until 0; intros H1 H2.
  eapply rs_prop_R_ne. 
Qed.

(* ------------------------------- *)
(* EXCHANGE ON LEFT FOR PRINCRULES *)
(* ------------------------------- *)

Lemma rs_prop_LT : forall {V : Set} ps Γ Δ,
    @rs_prop V ps (Γ, Δ) ->
    (Γ = []) + (existsT E, Γ = [E]).
Proof.
  intros V ps Γ Δ P.
  inversion P as [ p P2| P2 | A B P2 | P2];
    try (left; reflexivity).
  right. exists (Var p). reflexivity.
  right. exists (Imp A B). reflexivity.
  right. exists (Bot V). reflexivity.
Qed.

Lemma rs_prop_L_oeT : forall {V : Set} ps x y Δ,
    @rs_prop V ps (x ++ y, Δ) -> (x = []) + (y = []).
Proof.
  intros until 0. intros H. apply rs_prop_LT in H.
  sD ; list_eq_ncT ; sD ; tauto. 
Qed.

Lemma rs_prop_L_oe'T: forall V, rules_L_oeT (@rs_prop V).
Proof.
  unfold rules_L_oeT.   intros until 0. intros H.
  eapply rs_prop_L_oeT.  exact H.
Qed.

Lemma gen_swapL_step_loe_lc : forall V ps concl princrules
  (last_rule rules : rlsT (@LNS V)),
  rules_L_oeT princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_swapL_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapL_step.
  intros loe lreq nsr drs acm rs. subst. clear drs.

  inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslcext in nsc.
  apply can_gen_swapL_def'.  intros until 0. intros swap pp ss.
  unfold nslcext in pp.

  apply partition_2_2T in pp.

  destruct c.
  sD ; subst.
  inversion ss. subst.
  { nsgen_swTT rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }

  { inversion pp1. inversion ss. subst.
   inversion sppc as [? ? ? ? ? ? pr mse se].
   destruct c.
   unfold seqext in se.
   subst.  clear sppc.
   injection se as sel ser.
   subst.

   unfold rules_L_oeT in loe.
   inversion_clear swap ; subst.

   acacD'T2 ; subst ;
     repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
             sD ; subst ; simpl ; simpl in pr ;
             try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
     
     nsprsameLT princrules rs pr q qin inmps acm inps0 x0.
  }

  { list_eq_nc. contradiction. }
  Unshelve. all : solve_unshelved.
Qed.

Lemma gen_swapL_step_pr_lc: forall V ps concl 
  (last_rule rules : rlsT (@LNS V)),
  last_rule = nslcrule (seqrule (@rs_prop V)) ->
  gen_swapL_step last_rule rules ps concl.
Proof.
  intros. eapply gen_swapL_step_loe_lc.
  apply rs_prop_L_oe'T. exact H.
Qed.

Lemma gen_swapL_lc: forall {V : Set} ns
  (D : pf (nslcrule (seqrule (@rs_prop V))) ns),
  can_gen_swapL (nslcrule (seqrule (@rs_prop V))) ns.
Proof. 
  intro.  intro.  intro.
  eapply derrec_all_indT in D.
  exact D. tauto.
  intros until 0; intros H1 H2 H3. inversion H1. 
  subst.
  pose gen_swapL_step_pr_lc.
  unfold gen_swapL_step in g.
  eapply g. reflexivity. eassumption. assumption. assumption.
  unfold rsub. clear g. 
  intros.  assumption.
Qed.





(* -------------------------------- *)
(* EXCHANGE ON RIGHT FOR PRINCRULES *)
(* -------------------------------- *)

Lemma rs_prop_RT : forall {V : Set} ps Γ Δ,
    @rs_prop V ps (Γ, Δ) ->
    (Δ = []) + existsT E, Δ = [E].
Proof.
  intros V ps Γ Δ P. inversion P as [ p P2| A B P2 | P2 | P2];
                       try (left; reflexivity).
  right. exists (Var p). reflexivity.
  right. exists (Imp A B). reflexivity.
Qed.

Lemma rs_prop_R_oeT : forall {V : Set} ps x y Γ,
    @rs_prop V ps (Γ, x ++ y) -> (x = []) + (y = []).
Proof.
  intros until 0. intros H. apply rs_prop_RT in H.
  sD ; list_eq_ncT ; tauto.
Qed.

Lemma rs_prop_R_oe'T: forall V, rules_R_oeT (@rs_prop V).
Proof.
  unfold rules_R_oeT.  intros until 0. intros H.
  eapply rs_prop_R_oeT.  exact H.
Qed.

Lemma gen_swapR_step_roe_lc: forall V ps concl princrules
  (last_rule rules : rlsT (@LNS V)),
  rules_R_oeT princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_swapR_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapR_step.
  intros roe lreq nsr drs acm rs. subst. clear drs.
  
  inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
  unfold nsext in nsc.
  apply can_gen_swapR_def'.  intros until 0. intros swap pp ss.
  unfold nslcext in pp.
  
  apply partition_2_2T in pp.
  
  destruct c.
  sD ; subst.
  
  { nsgen_swT rs sppc (l, l0, d) (Γ, Δ', d0) acm inps0 swap. }
  
  {
    injection ss as. subst.
    inversion sppc as [? ? ? ? ? ? pr mse se].
    destruct c.
    unfold seqext in se.
    subst. clear sppc.
    injection se as sel ser.
    subst.
    
    unfold rules_R_oeT in roe.
    inversion_clear swap ; subst.
    
    acacD'T2 ; subst ;
      repeat ((list_eq_ncT || (pose pr as Qpr ; apply roe in Qpr)) ;
              sD ; subst ; simpl ; simpl in pr ;
              try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
      nsprsameRT princrules rs pr q qin inmps acm inps0 x0. 
  }
  
  { list_eq_nc. contradiction. }
  Unshelve. all : solve_unshelved.
Qed.

Lemma gen_swapR_step_pr_lc: forall V ps concl 
  (last_rule rules : rlsT (@LNS V)),
    last_rule = nslcrule (seqrule (@rs_prop V)) ->
    gen_swapR_step last_rule rules ps concl.
Proof.
  intros. eapply gen_swapR_step_roe_lc.
  apply rs_prop_R_oe'T. exact H.
Qed.

Lemma gen_swapR_lc: forall {V : Set} ns
   (D : pf (nslcrule (seqrule (@rs_prop V))) ns),
    can_gen_swapR (nslcrule (seqrule (@rs_prop V))) ns.
Proof. 
  intros until 0. intros D.
  eapply derrec_all_indT in D.
  exact D. tauto.
  intros H1 H2 H3 H4 H5. inversion H3. 
  subst.
  pose gen_swapR_step_pr_lc.
  unfold gen_swapR_step in g.
  eapply g. reflexivity. eassumption. assumption. assumption.
  unfold rsub. clear g. 
  intros.  assumption.
Qed.


(* ----------------------------- *)
(* LEFT WEAKENING FOR PRINCRULES *)
(* ----------------------------- *)

Lemma gen_weakL_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rlsT (@LNS V)),
  rules_L_oeT princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_weakL_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_weakL_step.
  intros loe lreq nsr drs acm rs. subst. clear drs.
  
  inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslcext in nsc.
  apply can_gen_weakL_def'.  intros until 0. intros swap pp ss.
  unfold nslcext in pp.
  
  apply partition_2_2T in pp.
  
  destruct c.
  sD ; subst.
  
  {  nsgen_sw_weakT rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }
  {
    injection pp1 as. inversion ss. subst.
    inversion sppc as [? ? ? ? ? ? pr mse se].
    destruct c.
    unfold seqext in se.
    subst.  clear sppc.
    injection se as sel ser.
    subst.
    
    unfold rules_L_oeT in loe.
    inversion_clear swap ; subst.

    acacD'T2 ;  subst ;
      repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
              sD ; subst ; simpl ; simpl in pr ;
              try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
      nsprsameL_weakT princrules rs pr q qin inmps acm inps0 x0.
  }
  
  { list_eq_nc. contradiction. }
  Unshelve. all : solve_unshelved.
Qed.

Lemma gen_weakL_step_pr_lc: forall V ps concl 
  (last_rule rules : rlsT (@LNS V)),
  last_rule = nslcrule (seqrule (@rs_prop V)) ->
  gen_weakL_step last_rule rules ps concl.
Proof.
  intros. eapply gen_weakL_step_loe_lc.
  apply rs_prop_L_oe'T. exact H.
Qed.

Lemma gen_weakL_lc: forall {V : Set} ns
  (D : pf (nslcrule (seqrule (@rs_prop V))) ns),
  can_gen_weakL (nslcrule (seqrule (@rs_prop V))) ns.
Proof. 
  intro.  intro.  intro.
  eapply derrec_all_indT in D.
  exact D. tauto.
  intros. inversion X. 
  subst.
  pose gen_weakL_step_pr_lc.
  unfold gen_weakL_step in g.
  eapply g. reflexivity. eassumption. assumption. assumption.
  unfold rsub. clear g. 
  intros.  assumption.
Qed.


(* ------------------------------ *)
(* RIGHT WEAKENING FOR PRINCRULES *)
(* ------------------------------ *)

Lemma gen_weakR_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rlsT (@LNS V)),
  rules_R_oeT princrules -> 
  last_rule = nslcrule (seqrule princrules) ->
  gen_weakR_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_weakR_step.
  intros loe lreq nsr drs acm rs. subst. clear drs.
  
  inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslcext in nsc.
  eapply can_gen_weakR_def'.  intros until 0. intros swap pp ss.
  unfold nslcext in pp.
  
  apply partition_2_2T in pp.
  
  destruct c.
  sD ; subst.
  
  { nsgen_sw_weakT rs sppc (l, l0, d) (Γ, Δ, d0) acm inps0 swap. }
  
  {
    injection pp1 as. subst.
    inversion sppc as [? ? ? ? ? ? pr mse se].
    destruct c.
    unfold seqext in se.
    subst.  clear sppc.
    injection se as sel ser.
    subst.
    
    unfold rules_L_oeT in loe.
    inversion_clear swap ; subst.
    
    acacD'T2 ;
      subst ;
      repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
              sD ; subst ; simpl ; simpl in pr ;
              try (rewrite app_nil_r) ; try (rewrite app_nil_r in pr)) ;
      nsprsameR_weakT princrules rs pr q qin inmps acm inps0 x0.
  }
  
  { list_eq_nc. contradiction. }
  Unshelve. all : solve_unshelved.
Qed.

Lemma gen_weakR_step_pr_lc: forall V ps concl 
  (last_rule rules : rlsT (@LNS V)),
  last_rule = nslcrule (seqrule (@rs_prop V)) ->
  gen_weakR_step last_rule rules ps concl.
Proof.
  intros. eapply gen_weakR_step_loe_lc.
  apply rs_prop_R_oe'T. exact H.
Qed.

Lemma gen_weakR_lc: forall {V : Set} ns
  (D : pf (nslcrule (seqrule (@rs_prop V))) ns),
  can_gen_weakR (nslcrule (seqrule (@rs_prop V))) ns.
Proof. 
  intro.  intro.  intro.
  eapply derrec_all_indT in D.
  exact D. tauto.
  intros. inversion X. 
  subst.
  pose gen_weakR_step_pr_lc.
  unfold gen_weakR_step in g.
  eapply g. reflexivity. eassumption.
  assumption. assumption.
  unfold rsub. clear g. 
  intros.  assumption.
Qed.


(* ------------------------------- *)
(* LEFT CONTRACTION FOR PRINCRULES *)
(* ------------------------------- *)

Lemma gen_contL_gen_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rlsT (@LNS V)),
  rules_L_oeT princrules -> 
  rules_L_carryT princrules ->
  rules_L_neT princrules ->
  (forall ns : (@LNS V),
      pf rules ns ->
      can_gen_swapL rules ns) ->
  last_rule = nslcrule (seqrule princrules) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.
  unfold LNS. unfold seq. unf_pf_all.
  intros until 0.  unfold gen_contL_step.
  intros loe carry psfull Hexch lreq nsr drs acm rs. subst. clear drs.
  inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslcext in nsc.
  eapply can_gen_contL_gen_def'.  intros until 0. intros swap pp ss.
  unfold nslcext in pp.
  
  apply partition_2_2T in pp.
  
  destruct c.
  sD ; subst.
  
  { nsgen_sw_cont_genT rs sppc (l, l0, d) (Γ', Δ, d0) acm inps0 swap. }

  { inversion pp1. subst.
    inversion sppc as [? ? ? ? ? ? pr mse se].
    destruct c.
    unfold seqext in se.
    subst.  clear sppc.
    injection se as sel ser.
    subst.
    
    unfold rules_L_oeT in loe.
    inversion_clear swap ; subst.
    { unf_pf_all. unf_pfs_all.
      acacD'T2 ; subst ;
        repeat ((list_eq_ncT || (pose pr as Qpr ; apply loe in Qpr)) ;
                sD ; subst  ; simpl in pr);
        rem_nil;
        try solve [check_contradiction_prT];
        try solve [
              lt3T a Hexch rs carry psfull loe;
              repeat rewrite app_nil_l; contL_setup;
              nsgen_sw_contL_gen5T rs sppc c c' acm inps0 swap pr inmps Hexch].
    }
    
    {
      acacD'T2 ; subst ;
        repeat ((list_eq_ncT || (pose pr as Qpr ; apply loe in Qpr)) ;
                sD ; subst  ; simpl in pr);
        rem_nil;
        try solve [check_contradiction_prT];
        try (lt3T a Hexch rs carry psfull loe; repeat rewrite app_nil_l; contL_setup; 
             nsgen_sw_contL_gen5T rs sppc c c' acm inps0 swap pr inmps Hexch).
    }
  }
  { list_eq_nc. contradiction. }
Qed.

Lemma gen_contL_gen_step_pr_lc: forall V ps concl 
  (last_rule rules : rlsT (@LNS V)),
    (forall ns : (@LNS V),
        pf rules ns ->
        can_gen_swapL rules ns) ->
    last_rule = nslcrule (seqrule (@rs_prop V)) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.
  intros until 0. intros Hswap Hl H2 H3 H4 H5.
  subst.
  eapply gen_contL_gen_step_loe_lc.
  apply rs_prop_L_oe'T.
  apply rs_prop_L_carry'. 
  apply rs_prop_L_ne'.
  exact Hswap.
  reflexivity.
  exact H2.
  all : assumption.
Qed.


(* -------------------------------- *)
(* RIGHT CONTRACTION FOR PRINCRULES *)
(* -------------------------------- *)

Lemma gen_contR_gen_step_loe_lc: forall V ps concl princrules
  (last_rule rules : rlsT (@LNS V)),
  rules_R_oeT princrules -> 
  rules_R_carryT princrules ->
  rules_R_neT princrules -> 
  (forall ns : (@LNS V),
      pf rules ns ->
      can_gen_swapR rules ns) ->
  last_rule = nslcrule (seqrule princrules) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_contR_step.
  intros loe carry psfull exch lreq nsr drs acm rs. subst. clear drs.
  
  inversion nsr as [? ? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslcext in nsc.
  eapply can_gen_contR_gen_def'.  intros until 0. intros swap pp ss.
  unfold nslcext in pp.
  
  apply partition_2_2T in pp.
  
  destruct c.
  sD ; subst.

  { nsgen_sw_cont_genT rs sppc (l, l0, d) (Γ, Δ', d0) acm inps0 swap. }
  
  {
    injection pp1 as. subst.
    inversion sppc as [? ? ? ? ? ? pr mse se].
    destruct c.
    unfold seqext in se.
    subst.  clear sppc.
    injection se as sel ser.
    subst.
    
    unfold rules_L_oeT in loe.
    inversion_clear swap ; subst.
    {
      unfold rules_R_oeT in loe.
      acacD'T2 ; subst ;
        repeat ((list_eq_nc || (pose pr as Qpr ; apply loe in Qpr)) ;
                sD ; subst  ; simpl in pr);
        rem_nil;
        try solve [check_contradiction_prT];
        try (lt3RT a exch rs carry psfull loe; rem_nil; contR_setup_extra;
             nsgen_sw_contR_gen5T rs sppc c c' acm inps0 swap pr inmps exch).
    }

    {
      unfold rules_R_oeT in loe.
      acacD'T2 ; subst ;
        repeat ((list_eq_ncT || (pose pr as Qpr ; apply loe in Qpr)) ;
                sD ; subst  ; simpl in pr);
        rem_nil;
        try solve [check_contradiction_prT];
        try (lt3RT a exch rs carry psfull loe; rem_nil; contR_setup_extra;
             nsgen_sw_contR_gen5T rs sppc c c' acm inps0 swap pr inmps exch).
    }
  }
  { list_eq_nc. contradiction. }
Qed.

Lemma gen_contR_gen_step_pr_lc: forall V ps concl 
                                       (last_rule rules : rlsT (@LNS V)),
    (forall ns : (@LNS V),
        pf rules ns ->
        can_gen_swapR rules ns) ->
    last_rule = nslcrule (seqrule (@rs_prop V)) ->
    gen_contR_gen_step last_rule rules ps concl.
Proof.
  intros until 0. intros Hswap Hl H2 H3 H4 H5.
  subst.
  eapply gen_contR_gen_step_loe_lc.
  apply rs_prop_R_oe'T.
  apply rs_prop_R_carry'. 
  apply rs_prop_R_ne'. 
  exact Hswap.
  reflexivity.
  exact H2.
  all : assumption.
Qed.





