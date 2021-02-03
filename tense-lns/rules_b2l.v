Add LoadPath "../general".

Require Import require_general.
Require Import LNS.
Require Import require_structural.

Set Implicit Arguments.

Inductive b2lrules (V : Set) : rlsT (@LNS V) :=
  | WBox2Ls : forall A d H1l H1r H2l H2r K1 K2, b2lrules 
      [[(pair (H1l ++ A :: H1r) K1, d) ]]
      [(pair (H1l ++ H1r) K1, d); 
        (pair (H2l ++ WBox A :: H2r) K2, bac)]
  | BBox2Ls : forall A d H1l H1r H2l H2r K1 K2, b2lrules 
      [[(pair (H1l ++ A :: H1r) K1, d) ]]
      [(pair (H1l ++ H1r) K1, d); 
         (pair (H2l ++ BBox A :: H2r) K2, fwd)].


(* ------------------------------ *)
(* EXCHANGE ON LEFT FOR B2L RULES *)
(* ------------------------------ *)

Lemma gen_swapL_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_swapL_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapL_step.
  intros lreq nsr drs acm rs. (* no clear drs. *) subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  apply can_gen_swapL_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
  -{ inversion sppc ; subst ; clear sppc. 
     +{ inversion_clear swap. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r.
        * use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H1). 
        * use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H3). 
        * use_acm2sT acm rs WBox2Ls list_assoc_l'. 
        * use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H). 
      }
     +{ inversion_clear swap. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H1). 
        * use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H3). 
        * use_acm2sT acm rs BBox2Ls list_assoc_l'. 
        * use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H). 
   } }

  -{ nsgen_swTT rs sppc c (Γ', Δ, d) acm inps0 swap. }

  -{ inversion sppc ; subst ; clear sppc. 

     (* WBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
        *{ inversion_clear swap. subst.
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
           ** use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H1). 
           ** use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H3). 
           ** use_acm2sT acm rs WBox2Ls list_assoc_l'. 
           ** use_acm2sT acm rs WBox2Ls ltac: (assoc_mid H). 
         }
         
        *{
            inversion_clear swap. subst. 
            acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
              use_drs_mid rs drs WBox2Ls. }
      }

     (* BBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        *{ inversion_clear swap. subst.
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
           ** use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H1). 
           ** use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H3). 
           ** use_acm2sT acm rs BBox2Ls list_assoc_l'. 
           ** use_acm2sT acm rs BBox2Ls ltac: (assoc_mid H). 
         }
        *{
            inversion_clear swap. subst. 
            acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
              use_drs_mid rs drs BBox2Ls. }
      }
   }
   Unshelve. all : solve_unshelved.
Qed.


(* ------------------------------- *)
(* EXCHANGE ON RIGHT FOR B2L RULES *)
(* ------------------------------- *)

Lemma gen_swapR_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_swapR_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapR_step.
  intros lreq nsr drs acm rs. (* no clear drs! *) subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  apply can_gen_swapR_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
  -{ inversion sppc ; subst ; 
     [> use_acm_sw_sepT acm rs swap WBox2Ls |
      use_acm_sw_sepT acm rs swap BBox2Ls ]. }
  -{ nsgen_swTT rs sppc c (Γ, Δ', d) acm inps0 swap. }
  -{ inversion sppc ; subst ; clear sppc. 
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm_sw_sepT acm rs swap WBox2Ls.
        * use_drs rs drs WBox2Ls.
      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm_sw_sepT acm rs swap BBox2Ls.
        * use_drs rs drs BBox2Ls.
      }
   }  
   Unshelve. all : solve_unshelved.
Qed.



(* ---------------------- *)
(* WEAKENING FOR B2LRULES *)
(* ---------------------- *)

Lemma gen_weakL_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_weakL_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_weakL_step.
  intros lreq nsr drs acm rs.  subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_weakL_def'.  intros until 0. intros weak pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *.
  -{ inversion sppc ; subst ; clear sppc.
     +{ inversion_clear weak. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm2s_weakT2 acm rs WBox2Ls ltac: (do 2 rewrite app_assoc). 
        * use_acm2s_weakT2 acm rs WBox2Ls ltac: (assoc_mid H). 
      }
     +{ inversion_clear weak. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm2s_weakT2 acm rs BBox2Ls ltac: (do 2 rewrite app_assoc). 
        * use_acm2s_weakT2 acm rs BBox2Ls ltac: (assoc_mid H).
   } }
  -{ nsgen_sw_weakT rs sppc c (Γ', Δ, d) acm inps0 weak. }
  -{ inversion sppc ; subst ; clear sppc.

     (* WBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
        *{ inversion_clear weak. subst.
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r.
           ** use_acm2s_weakT2 acm rs WBox2Ls ltac: (do 2 rewrite app_assoc). 
           ** use_acm2s_weakT2 acm rs WBox2Ls ltac: (assoc_mid H). 
         }
        *{
            inversion_clear weak. subst. 
            acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
              use_drs_mid rs drs WBox2Ls. }
      }

     (* BBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
        *{ inversion_clear weak. subst.
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
           ** use_acm2s_weakT2 acm rs BBox2Ls ltac: (do 2 rewrite app_assoc). 
           ** use_acm2s_weakT2 acm rs BBox2Ls ltac: (assoc_mid H). 
         }
        *{
            inversion_clear weak. subst. 
            acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
              use_drs_mid rs drs BBox2Ls. }
      }
   }
   Unshelve. all : solve_unshelved.
Qed.

Lemma gen_weakR_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_weakR_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_weakR_step.
  intros lreq nsr drs acm rs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_weakR_def'.  intros until 0. intros weak pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
  -{ inversion sppc ; subst ; 
     [> use_acm_sw_sep_weakT acm rs weak WBox2Ls |
      use_acm_sw_sep_weakT acm rs weak BBox2Ls ]. }
  -{ nsgen_sw_weakT rs sppc c (Γ, Δ', d) acm inps0 weak. }
  -{ inversion sppc ; subst ; clear sppc. 
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        *{ use_acm_sw_sep_weakT acm rs weak WBox2Ls. }
        *{ use_drs rs drs WBox2Ls. }
      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        *{ use_acm_sw_sep_weakT acm rs weak BBox2Ls. }
        *{ use_drs rs drs BBox2Ls. }
      }
   }
   Unshelve. all : solve_unshelved.
Qed.



(* ------------------------ *)
(* CONTRACTION FOR B2LRULES *)
(* ------------------------ *)
    
Lemma gen_contL_gen_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_contL_gen_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_contL_gen_step.
  intros lreq nsr drs acm rs.  subst.
  
  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_contL_gen_def'.  intros until 0. intros weak pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *.
  -{ inversion sppc ; subst ; clear sppc.
     +{ inversion_clear weak; subst;
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r; 
        acacDeT2; subst; rem_nil; 
        try (cont_setup_apply_constr4 WBox;
             use_acm2s_cont'T acm rs WBox2Ls WBox);
        try (cont_setup_apply_constr5' WBox;
             use_acm2s_cont'T acm rs WBox2Ls WBox);
        try (cont_setup_apply_constr6' WBox;
             use_acm2s_cont'T acm rs WBox2Ls WBox);
        try (cont_setup_apply_constr4' WBox;
             use_acm2s_cont'T acm rs WBox2Ls WBox).

      }
     +{ inversion_clear weak; subst;
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r; 
        acacDeT2; subst; rem_nil;
        try (cont_setup_apply_constr4' BBox;
             use_acm2s_cont'T acm rs BBox2Ls BBox);
        try (cont_setup_apply_constr5' BBox;
             use_acm2s_cont'T acm rs BBox2Ls BBox);
        try (cont_setup_apply_constr6' BBox;
             use_acm2s_cont'T acm rs BBox2Ls BBox);
        use_acm2s_cont'T acm rs BBox2Ls WBox.
      }
   }
  -{ nsgen_sw_contT rs sppc c (Γ', Δ, d) acm inps0 weak. }

  -{ inversion sppc ; subst ; clear sppc.

     (* WBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        +{ inversion_clear weak; subst;
           acacD'T2; subst ; simpl ; rewrite ?app_nil_r;
           acacDeT2; subst; rem_nil;
           try (cont_setup_apply_constr4' WBox;
                use_acm2s_cont'T acm rs WBox2Ls WBox);
           try (cont_setup_apply_constr5' WBox;
                use_acm2s_cont'T acm rs WBox2Ls WBox);
           try (cont_setup_apply_constr6' WBox;
                use_acm2s_cont'T acm rs WBox2Ls WBox);
           use_acm2s_cont'T acm rs WBox2Ls WBox.
         }

        +{ inversion_clear weak; subst;
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r;
           acacDeT2; subst; rem_nil;
           try  (list_assoc_r_single; no_use_acm_cont rs drs WBox2Ls);
           try (   list_assoc_r_single; cont_setup_apply_constr7' WBox;
                   no_use_acm_cont rs drs WBox2Ls).
         }
      }

     (* BBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        +{ inversion_clear weak; subst;
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r;
           acacDeT2; subst; rem_nil;
           try (cont_setup_apply_constr4' BBox;
                use_acm2s_cont'T acm rs BBox2Ls BBox);
           try (cont_setup_apply_constr5' BBox;
                use_acm2s_cont'T acm rs BBox2Ls BBox);
           try (cont_setup_apply_constr6' BBox;
                use_acm2s_cont'T acm rs BBox2Ls BBox);
           use_acm2s_cont'T acm rs BBox2Ls BBox.
         }
         
        +{ inversion_clear weak; subst;
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r; 
           acacDeT2; subst; rem_nil;
           try  (list_assoc_r_single; no_use_acm_cont rs drs BBox2Ls);
           try (   list_assoc_r_single; cont_setup_apply_constr7' BBox;
                   no_use_acm_cont rs drs BBox2Ls).
         }
      }
   }
Qed.

Lemma gen_contR_gen_step_b2L_lc: forall V ps concl last_rule rules,
  last_rule = nslclrule (@b2lrules V) ->
  gen_contR_gen_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_contR_gen_step.
  intros lreq nsr drs acm rs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_contR_gen_def'.  intros until 0. intros weak pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
  -{ inversion sppc ; subst ; 
     [> use_acm_sw_sep_contT acm rs weak WBox2Ls |
      use_acm_sw_sep_contT acm rs weak BBox2Ls ]. }
  -{ nsgen_sw_contT rs sppc c (Γ, Δ', d) acm inps0 weak. }
  -{ inversion sppc ; subst ; clear sppc.
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        *{ use_acm_sw_sep_contT acm rs weak WBox2Ls. }
        *{ use_drs rs drs WBox2Ls. }
      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        *{ use_acm_sw_sep_contT acm rs weak BBox2Ls. }
        *{ use_drs rs drs BBox2Ls. }
      }
   }  
Qed.
