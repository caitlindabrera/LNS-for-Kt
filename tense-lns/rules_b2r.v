Add LoadPath "../general".

Require Import require_general.
Require Import LNS.
Require Import require_structural.

Set Implicit Arguments.

Inductive b2rrules (V : Set) : rlsT (@LNS V) :=
  | WBox2Rs : forall A H1 K1l K1r, b2rrules 
      [[(pair H1 (K1l ++ WBox A :: K1r), fwd) ; (pair [] [A], fwd) ]]
      [(pair H1 (K1l ++ WBox A :: K1r), fwd)]
  | BBox2Rs : forall A H1 K1l K1r, b2rrules 
      [[(pair H1 (K1l ++ BBox A :: K1r), bac) ; (pair [] [A], bac) ]]
      [(pair H1 (K1l ++ BBox A :: K1r), bac)].


(* ------------------------------ *)
(* EXCHANGE ON LEFT FOR B2R RULES *)
(* ------------------------------ *)

Lemma gen_swapL_step_b2R_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b2rrules V) ->
    gen_swapL_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapL_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  apply can_gen_swapL_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.

  acacDeT2 ; subst ; rewrite -> ?app_nil_r in *.
  -{ inversion sppc ; subst ; clear sppc. 
     +     use_acm_osTT acm rs swap WBox2Rs.
     + use_acm_osTT acm rs swap BBox2Rs. }
  -{ nsgen_swTT rs sppc c (Γ', Δ, d) acm inps0 swap. }
  -{ inversion sppc ; subst ; clear sppc. 
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r ; 
        use_acm_osTT acm rs swap WBox2Rs.  }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r ; 
        use_acm_osTT acm rs swap BBox2Rs.  }
   }
   Unshelve. exact nat. intros. exact 0.
Qed.


(* ------------------------------- *)
(* EXCHANGE ON RIGHT FOR B2R RULES *)
(* ------------------------------- *)

Lemma gen_swapR_step_b2R_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b2rrules V) ->
    gen_swapR_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapR_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_swapR_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *.
  -{ inversion sppc ; subst ; clear sppc. 
     +{ inversion_clear swap. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
          use_acm1TT acm rs WBox2Rs. }
     +{ inversion_clear swap. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ;
          use_acm1TT acm rs BBox2Rs. }
   }
  -{ nsgen_swTT rs sppc c (Γ, Δ', d) acm inps0 swap. }
  -{ inversion sppc ; subst ; clear sppc.  
     (* WBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        inversion_clear swap. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
          use_acm1TT acm rs WBox2Rs. 
      }
     (* BBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        inversion_clear swap. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
          use_acm1TT acm rs BBox2Rs. 
   } }
   Unshelve. exact nat. intro. exact 0.
Qed.


(* ---------------------- *)
(* WEAKENING FOR B2RRULES *)
(* ---------------------- *)

Lemma gen_weakL_step_b2R_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b2rrules V) ->
    gen_weakL_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_weakL_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_weakL_def'.  intros until 0. intros weak pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
  -{ inversion sppc ; subst ; clear sppc. 
     +     use_acm_os_weakT acm rs weak WBox2Rs.
     +     use_acm_os_weakT acm rs weak BBox2Rs. }
  -{  nsgen_sw_weakT rs sppc c (Γ', Δ, d) acm inps0 weak. }
  -{ inversion sppc ; subst ; clear sppc.
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        *  use_acm_os_weakT acm rs weak WBox2Rs.
      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
        * use_acm_os_weakT acm rs weak BBox2Rs.
      }
   }
   Unshelve. all : solve_unshelved.
Qed.

Lemma gen_weakR_step_b2R_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b2rrules V) ->
    gen_weakR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
        intros lreq nsr drs acm rs. clear drs. subst.

        inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
        unfold nslclext in nsc.
        eapply can_gen_weakR_def'.  intros until 0. intros weak pp ss.
        unfold nslclext in pp. subst.

        acacD'T2 ; subst ; rewrite -> ?app_nil_r in *.
        -{ inversion sppc ; subst ; clear sppc. 
           +{ inversion_clear weak; subst;
              acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ;

              use_acm1_weakT acm rs WBox2Rs. }
           +{ inversion_clear weak. subst.
              acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
                use_acm1_weakT acm rs BBox2Rs. }
         }
        -{ nsgen_sw_weakT rs sppc c (Γ, Δ', d) acm inps0 weak. }
        -{ inversion sppc ; subst ; clear sppc. 
           (* WBox *)
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
              *{ inversion_clear weak. subst.
                 acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ;
                   use_acm1_weakT acm rs WBox2Rs. }
            }
           (* BBox *)
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
              *{ inversion_clear weak. subst.
                 acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
                   use_acm1_weakT acm rs BBox2Rs. }
         } }
         Unshelve. all : solve_unshelved.
Qed.


(* ------------------------ *)
(* CONTRACTION FOR B2RRULES *)
(* ------------------------ *)

Lemma gen_contL_gen_step_b2R_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b2rrules V) ->
    gen_contL_gen_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_contL_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_contL_gen_def'.  intros until 0. intros weak pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *.
  -{ inversion sppc ; subst ; clear sppc. 
     + use_acm_os_contT acm rs weak WBox2Rs.
     + use_acm_os_contT acm rs weak BBox2Rs. }
  -{
      nsgen_sw_contT rs sppc c (Γ', Δ, d) acm inps0 weak. }
  -{ inversion sppc ; subst ; clear sppc. 
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm_os_contT acm rs weak WBox2Rs.
      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm_os_contT acm rs weak BBox2Rs.
      }
   }
Qed.

Lemma gen_contR_gen_step_b2R_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b2rrules V) ->
    gen_contR_gen_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
        intros lreq nsr drs acm rs. clear drs. subst.

        inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
        unfold nslclext in nsc.
        eapply  can_gen_contR_gen_def'.  intros until 0. intros weak pp ss.
        unfold nslclext in pp. subst.

        acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
        -{ inversion sppc ; subst ; clear sppc.
           +{ inversion_clear weak; subst;
              repeat (acacD'T2 ; subst ; simpl ; rem_nil) ;
              try discriminate; rem_nil; subst;
              check_nil_cons_contr;
              try use_acm1_cont_constrT acm rs WBox2Rs WBox. }
           +{ inversion_clear weak; subst;
              repeat (acacD'T2 ; subst ; simpl ; rem_nil) ;
              try discriminate; rem_nil; subst;
              check_nil_cons_contr;
              use_acm1_cont_constrT acm rs BBox2Rs BBox.
            }
         }
        -{ nsgen_sw_contT rs sppc c (Γ, Δ', d) acm inps0 weak. }
        -{ inversion sppc ; subst ; clear sppc. 
           (* WBox *)
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
              *{ inversion_clear weak; subst;
                 repeat (acacD'T2 ; subst ; simpl ; rem_nil) ;
                 try discriminate; rem_nil; subst;
                 check_nil_cons_contr;   
                 use_acm1_cont_constrT acm rs WBox2Rs WBox. }
            }
           (* BBox *)
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
              *{ inversion_clear weak; subst;
                 repeat (acacD'T2 ; subst ; simpl ; rem_nil) ;
                 try discriminate; rem_nil; subst;
                 check_nil_cons_contr;   
                 use_acm1_cont_constrT acm rs BBox2Rs BBox. }
         } }
Qed.
