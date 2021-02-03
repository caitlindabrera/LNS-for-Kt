Add LoadPath "../general".

Require Import require_general.
Require Import LNS.
Require Import require_structural.

Set Implicit Arguments.


Inductive EW_rule (V : Set) : rlsT (@LNS V) :=
| EW : forall H K d, EW_rule [[]] [(pair H K, d)].


(* ---------------------------- *)
(* EXCHANGE ON LEFT FOR EW RULE *)
(* ---------------------------- *)

Lemma gen_swapL_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_swapL_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapL_step.
  intros lreq nsr drs acm rs. subst. 
  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_swapL_imp_rev.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.
  acacDeT2 ; subst ; rewrite -> ?app_nil_r in *. 
  - inversion sppc ; subst ; clear sppc.
    + derIrs rs.
      * apply NSlclctxt.  apply EW.
      * apply drs.
  - exchL2T rs sppc acm swap.
  - inversion sppc ; subst ; clear sppc.
    acacDeT2 ; subst ; rewrite -> ?app_nil_r in *.
    derIrs rs.
    + apply NSlclctxt.  apply EW.
    + apply drs.
Qed.


(* ----------------------------- *)
(* EXCHANGE ON RIGHT FOR EW RULE *)
(* ----------------------------- *)

Lemma gen_swapR_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_swapR_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapR_step.
  intros lreq nsr drs acm rs. subst.
  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_swapR_imp_rev.
  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.
  acacDeT2 ; subst ; rewrite -> ?app_nil_r in *. 
  - inversion sppc ; subst ; clear sppc.
    + derIrs rs.
      * apply NSlclctxt.  apply EW.
      * apply drs.
  - exchL2T rs sppc acm swap.
  - inversion sppc ; subst ; clear sppc.
    acacDeT2 ; subst ; rewrite -> ?app_nil_r in *.
    derIrs rs.
    + apply NSlclctxt.  apply EW.
    + apply drs.
Qed.


(* ---------------- *)
(* WEAKENING FOR EW *)
(* ---------------- *)

Lemma gen_weakR_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_weakR_step.
  intros lreq nsr drs acm rs. subst.
  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_weakR_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.
  acacDeT2 ; subst ; rewrite -> ?app_nil_r in *. 
  - inversion sppc ; subst ; clear sppc.
    + derIrs rs.
      * apply NSlclctxt.  apply EW.
      * apply drs.
  - weakL2T rs sppc acm swap.
  - inversion sppc ; subst ; clear sppc.
    acacDeT2 ; subst ; rewrite -> ?app_nil_r in *.
    derIrs rs.
    + apply NSlclctxt.  apply EW.
    + apply drs.
Qed.

Lemma gen_weakL_step_EW_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@EW_rule V) ->
    gen_weakL_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapL_step.
  intros lreq nsr drs acm rs. subst. 
  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_weakL_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.
  acacDeT2 ; subst ; rewrite -> ?app_nil_r in *. 
  - inversion sppc ; subst ; clear sppc.
    + derIrs rs.
      * apply NSlclctxt.  apply EW.
      * apply drs.
  - weakL2T rs sppc acm swap.
  - inversion sppc ; subst ; clear sppc.
    acacDeT2 ; subst ; rewrite -> ?app_nil_r in *.
    derIrs rs.
    + apply NSlclctxt.  apply EW.
    + apply drs.
Qed.



(* ------------------ *)
(* CONTRACTION FOR EW *)
(* ------------------ *)

Lemma gen_contR_gen_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_contR_gen_step.
  intros lreq nsr drs acm rs. subst. 
  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_contR_gen_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.
  acacDeT2 ; subst ; rewrite -> ?app_nil_r in *. 
  - inversion sppc ; subst ; clear sppc.
    + derIrs rs.
      * apply NSlclctxt.  apply EW.
      * apply drs.
  - contL2T rs sppc acm swap.
  - inversion sppc ; subst ; clear sppc.
    acacDeT2 ; subst ; rewrite -> ?app_nil_r in *.
    derIrs rs.
    + apply NSlclctxt.  apply EW.
    + apply drs.
Qed.

Lemma gen_contL_gen_step_EW_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@EW_rule V) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_contL_gen_step.
  intros lreq nsr drs acm rs. subst. 
  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_contL_gen_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.
  acacDeT2 ; subst ; rewrite -> ?app_nil_r in *. 
  - inversion sppc ; subst ; clear sppc.
    + derIrs rs.
      * apply NSlclctxt.  apply EW.
      * apply drs.
  - contL2T rs sppc acm swap.
  - inversion sppc ; subst ; clear sppc.
    acacDeT2 ; subst ; rewrite -> ?app_nil_r in *.
    derIrs rs.
    + apply NSlclctxt.  apply EW.
    + apply drs.
Qed.