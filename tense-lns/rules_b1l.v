Add LoadPath "../general".

Require Import require_general.
Require Import LNS.
Require Import require_structural.

Set Implicit Arguments.


Inductive b1lrules (V : Set) : rlsT (@LNS V) :=
| WBox1Ls : forall A d H1l H1r H2l H2r K1 K2, b1lrules 
    [[(pair (H1l ++ WBox A :: H1r) K1, d);
      (pair (H2l ++ A :: H2r) K2, fwd)]]
    [(pair (H1l ++ WBox A :: H1r) K1, d); 
       (pair (H2l ++ H2r) K2, fwd)]
| BBox1Ls : forall A d H1l H1r H2l H2r K1 K2, b1lrules 
    [[(pair (H1l ++ BBox A :: H1r) K1, d);
      (pair (H2l ++ A :: H2r) K2, bac)]]
    [(pair (H1l ++ BBox A :: H1r) K1, d); 
      (pair (H2l ++ H2r) K2, bac)].


(* ------------------------------ *)
(* EXCHANGE ON LEFT FOR B1L RULES *)
(* ------------------------------ *)

Lemma gen_swapL_step_b1L_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b1lrules V) ->
    gen_swapL_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapL_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  apply can_gen_swapL_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 

  -{ inversion sppc ; subst ; clear sppc. 
     +{ inversion_clear swap. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
          use_acm1TT acm rs WBox1Ls. }
     +{ inversion_clear swap. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
          use_acm1TT acm rs BBox1Ls. }
   }
  -{ nsgen_swTT rs sppc c (Γ', Δ, d) acm inps0 swap. }

  -{ inversion sppc ; subst ; clear sppc.

     (* WBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        *{ inversion_clear swap. subst.
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
             use_acm1TT acm rs WBox1Ls. }
        *{
            inversion_clear swap. subst.
            acacD'T2 ; subst.
            use_acm2sT acm rs WBox1Ls ltac: (assoc_mid H1).
            use_acm2sT acm rs WBox1Ls ltac: (assoc_mid H3).
            use_acm2sT acm rs WBox1Ls list_assoc_l'.
            use_acm2sT acm rs WBox1Ls ltac: (assoc_mid H).
          }
      }

     (* BBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        *{ inversion_clear swap. subst.
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ;
             use_acm1TT acm rs BBox1Ls. }
        *{
            inversion_clear swap. subst.
            acacD'T2 ; subst.
            use_acm2sT acm rs BBox1Ls ltac: (assoc_mid H1).
            use_acm2sT acm rs BBox1Ls ltac: (assoc_mid H3).
            use_acm2sT acm rs BBox1Ls list_assoc_l'.
            use_acm2sT acm rs BBox1Ls ltac: (assoc_mid H).
          }
      }
   }
   Unshelve. all : solve_unshelved.
Qed.


(* A version that uses nslrule which *isn't* end-active.
Not used in the cut-elimination proof. *)
Lemma gen_swapL_step_b1L: forall V ps concl last_rule rules,
    last_rule = nslrule (@b1lrules V) ->
    gen_swapL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
        intros lreq nsr drs acm rs. clear drs. subst.

        inversion nsr as [? ? ? K sppc mnsp nsc]. clear nsr.
        unfold nslext in nsc.
        apply can_gen_swapL_def'.  intros until 0. intros swap pp ss.
        unfold nslext in pp. subst.

        acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
        - inversion sppc. 
        -{ inversion sppc ; subst ; clear sppc. 
           +{ inversion_clear swap. subst.
              acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
                use_acm1TT acm rs WBox1Ls. }
           +{ inversion_clear swap. subst.
              acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ;
                use_acm1TT acm rs BBox1Ls. }
         }
        -{ nsgen_swTT rs sppc c (Γ', Δ, d) acm inps0 swap. }
        -{ nsgen_swTT rs sppc pp (Γ', Δ, d) acm inps0 swap. }
        -{ inversion sppc ; subst ; clear sppc. 

           (* WBox *)
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
              *{ inversion_clear swap. subst.
                 acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
                   use_acm1TT acm rs WBox1Ls. }

              *{
                  inversion_clear swap. subst.
                  acacD'T2 ; subst.

                  { use_acm2sT acm rs WBox1Ls ltac: (assoc_mid H1). }
                  { use_acm2sT acm rs WBox1Ls ltac: (assoc_mid H3). }
                  { use_acm2sT acm rs WBox1Ls list_assoc_l'. }
                  { use_acm2sT acm rs WBox1Ls ltac: (assoc_mid H). }
                }
            }

           (* BBox *)
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
              *{ inversion_clear swap. subst.
                 acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
                   use_acm1TT acm rs BBox1Ls. }
              *{
                  inversion_clear swap. subst.
                  acacD'T2 ; subst.
                  { use_acm2sT acm rs BBox1Ls ltac: (assoc_mid H1). }
                  { use_acm2sT acm rs BBox1Ls ltac: (assoc_mid H3). }
                  { use_acm2sT acm rs BBox1Ls list_assoc_l'. }
                  { use_acm2sT acm rs BBox1Ls ltac: (assoc_mid H). }
                }
            }
         }
        -{ nsgen_swTT rs sppc c (Γ', Δ, d) acm inps0 swap. }
         Unshelve. all : solve_unshelved. 
Qed.


(* ------------------------------- *)
(* EXCHANGE ON RIGHT FOR B1L RULES *)
(* ------------------------------- *)

Lemma gen_swapR_step_b1L_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b1lrules V) ->
    gen_swapR_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapR_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  apply can_gen_swapR_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
  -{ inversion sppc ; subst ; [> 
                               use_acm_sw_sepT acm rs swap WBox1Ls |
                               use_acm_sw_sepT acm rs swap BBox1Ls ]. }
  -{ nsgen_swTT rs sppc c (Γ, Δ', d) acm inps0 swap. }

  -{ inversion sppc ; subst ; clear sppc. 
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm_sw_sepT acm rs swap WBox1Ls.
        * use_acm_sw_sepT3 acm rs swap WBox1Ls.
      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm_sw_sepT acm rs swap BBox1Ls.
        * use_acm_sw_sepT3 acm rs swap BBox1Ls.
      }
   }
   Unshelve. all : solve_unshelved.
Qed.

(* A version that uses nslrule which *isn't* end-active.
Not used in the cut-elimination proof. *)
Lemma gen_swapR_step_b1L: forall V ps concl last_rule rules,
    last_rule = nslrule (@b1lrules V) ->
    gen_swapR_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapR_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? K sppc mnsp nsc]. clear nsr.
  unfold nslext in nsc.
  apply can_gen_swapR_def'.  intros until 0. intros swap pp ss.
  unfold nslext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
  -inversion sppc. 
  -{ inversion sppc ; subst ; clear sppc ; 
     [> use_acm_sw_sepT acm rs swap WBox1Ls |
      use_acm_sw_sepT acm rs swap BBox1Ls ]. }
  -{ nsgen_swTT rs sppc c (Γ, Δ', d) acm inps0 swap. }
  -{ nsgen_swTT rs sppc pp (Γ, Δ', d) acm inps0 swap. }

  -{ inversion sppc ; subst ; clear sppc. 
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm_sw_sepT acm rs swap WBox1Ls.
        * use_acm_sw_sepT2 acm rs swap WBox1Ls.
      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm_sw_sepT acm rs swap BBox1Ls.
        * use_acm_sw_sepT2 acm rs swap BBox1Ls.
      }
   }  
  -{ nsgen_swTT rs sppc c (Γ, Δ', d) acm inps0 swap. }
   Unshelve. all: solve_unshelved. 
Qed.



(* ---------------------- *)
(* WEAKENING FOR B1LRULES *)
(* ---------------------- *)

Lemma gen_weakL_step_b1L_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b1lrules V) ->
    gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_weakL_step.
        intros lreq nsr drs acm rs. clear drs. subst.

        inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
        unfold nslclext in nsc.
        eapply  can_gen_weakL_def'.  intros until 0. intros weak pp ss.
        unfold nslclext in pp. subst.

        acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
        -{ inversion sppc ; subst ; clear sppc. 
           +{ inversion_clear weak. subst.
              acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ;
                use_acm1_weakT acm rs WBox1Ls. }
           +{ inversion_clear weak. subst.
              acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
                use_acm1_weakT acm rs BBox1Ls. }
         }

        -{ nsgen_sw_weakT rs sppc c (Γ', Δ, d) acm inps0 weak. }
        -{ inversion sppc ; subst ; clear sppc. 

           (* WBox *)
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
              *{ inversion_clear weak. subst.
                 acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
                   use_acm1_weakT acm rs WBox1Ls. }
              *{
                  inversion_clear weak. subst.
                  acacD'T2 ; subst.
                  { use_acm2s_weakT2 acm rs WBox1Ls ltac: (do 2 rewrite app_assoc). }
                  { use_acm2s_weakT2 acm rs WBox1Ls ltac: (assoc_mid H). }
                }
            }

           (* BBox *)
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
              *{ inversion_clear weak. subst.
                 acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ;
                   use_acm1_weakT acm rs BBox1Ls. }
              *{
                  inversion_clear weak. subst.
                  acacD'T2 ; subst.
                  { use_acm2s_weakT2 acm rs BBox1Ls ltac: (do 2 rewrite app_assoc). }
                  { use_acm2s_weakT2 acm rs BBox1Ls ltac: (assoc_mid H). } }
            }
         }
         Unshelve. all : solve_unshelved.
Qed.

Lemma gen_weakR_step_b1L_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b1lrules V) ->
    gen_weakR_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_weakR_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_weakR_def'.  intros until 0. intros weak pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
  -{ inversion sppc ; subst ;
     [> 
      use_acm_sw_sep_weakT acm rs weak WBox1Ls |
      use_acm_sw_sep_weakT acm rs weak BBox1Ls ]. }
  -{ nsgen_sw_weakT rs sppc c (Γ, Δ', d) acm inps0 weak. }

  -{ inversion sppc ; subst ; clear sppc. 
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        *{ use_acm_sw_sep_weakT acm rs weak WBox1Ls. }
        *{ use_acm2s_weakT2 acm rs WBox1Ls idtac; assumption. }
      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        *{ use_acm_sw_sep_weakT acm rs weak BBox1Ls. }
        *{ use_acm2s_weakT2 acm rs BBox1Ls idtac; assumption. }
      }
   }  
   Unshelve. all : solve_unshelved.
Qed.


(* ------------------------ *)
(* CONTRACTION FOR B1LRULES *)
(* ------------------------ *)

Lemma gen_contL_gen_step_b1L_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b1lrules V) ->
    gen_contL_gen_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_weakL_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_contL_gen_def'.  intros until 0. intros weak pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
  -{ inversion sppc ; subst ; clear sppc. 
     +{ inversion_clear weak; subst;
        repeat (acacD'T2 ; subst ; simpl ; rem_nil) ;
        try discriminate; rem_nil; subst;
        check_nil_cons_contr;
        use_acm1_cont_constrT acm rs WBox1Ls WBox.
      }
     +{ inversion_clear weak; subst;
        repeat (acacD'T2 ; subst ; simpl ; rem_nil) ;
        try discriminate; rem_nil; subst;
        check_nil_cons_contr;
        use_acm1_cont_constrT acm rs BBox1Ls BBox.
      }
   }
  -{ nsgen_sw_contT rs sppc c (Γ', Δ, d) acm inps0 weak. }
  -{ inversion sppc ; subst ; clear sppc.

     (* WBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
        *{ inversion_clear weak; subst;
           repeat (acacD'T2 ; subst ; simpl ; rem_nil) ;
           try discriminate; rem_nil; subst;
           check_nil_cons_contr;
           use_acm1_cont_constrT acm rs WBox1Ls WBox.
         }
        *{

            inversion_clear weak; subst;
            acacD'T2 ; subst;
            
            try (  acacDeT2; subst; rem_nil ;    
                   (cont_setup_apply_constr WBox;
                    use_acm2s_cont'T acm rs WBox1Ls WBox) ||
                      (cont_setup_apply_constr2 WBox;
                       use_acm2s_cont'T acm rs WBox1Ls WBox) ||
                      (cont_setup_apply_constr3 WBox;
                       use_acm2s_cont'T acm rs WBox1Ls WBox)).
            { use_acm2s_contT acm rs WBox1Ls. }
          }
      }

     (* WBox *)
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
        *{ inversion_clear weak; subst;
           repeat (acacD'T2 ; subst ; simpl ; rem_nil) ;
           try discriminate; rem_nil; subst;
           check_nil_cons_contr;
           use_acm1_cont_constrT acm rs BBox1Ls BBox.
         }
        *{
            inversion_clear weak; subst;
            acacD'T2 ; subst;
            try (  acacDeT2; subst; rem_nil;
                   (cont_setup_apply_constr BBox;
                    use_acm2s_cont'T acm rs BBox1Ls BBox) ||
                      (cont_setup_apply_constr2 BBox;
                         use_acm2s_cont'T acm rs BBox1Ls BBox) ||
                      (cont_setup_apply_constr3 BBox;
                         use_acm2s_cont'T acm rs BBox1Ls BBox)).

            { use_acm2s_contT acm rs BBox1Ls. }
          }
      }
   }
Qed.

Lemma gen_contR_gen_step_b1L_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b1lrules V) ->
    gen_contR_gen_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_contR_gen_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_contR_gen_def'.  intros until 0. intros weak pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *.
  -{ inversion sppc ; subst ;
     [> 
      use_acm_sw_sep_contT acm rs weak WBox1Ls |
      use_acm_sw_sep_contT acm rs weak BBox1Ls ]. }
  -{ nsgen_sw_contT rs sppc c (Γ, Δ', d) acm inps0 weak. }
  -{ inversion sppc ; subst ; clear sppc. 
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
        *{ use_acm_sw_sep_contT acm rs weak WBox1Ls. }
        *{ use_acm_sw_sep_contT acm rs weak WBox1Ls. }
      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
        *{ use_acm_sw_sep_contT acm rs weak BBox1Ls. }
        *{ use_acm_sw_sep_contT acm rs weak BBox1Ls. }
      }
   }  
Qed.



