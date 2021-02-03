Add LoadPath "../general".

Require Import require_general.
Require Import LNS.
Require Import require_structural.
Require Import ssreflect.

Set Implicit Arguments.


Inductive b1rrules (V : Set) : rlsT (@LNS V) :=
  | WBox1Rs : forall A d H1 H2 K1l K1r K2l K2r, b1rrules 
    [[(pair H1 (K1l ++ A :: K1r), d) ; (pair H2 (K2l ++ WBox A :: K2r), bac) ] ;
       [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ WBox A :: K2r), bac) ;
         (pair [] [A], fwd)] ]
      [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ WBox A :: K2r), bac)]
  | BBox1Rs : forall A d H1 H2 K1l K1r K2l K2r, b1rrules 
    [[(pair H1 (K1l ++ A :: K1r), d) ; (pair H2 (K2l ++ BBox A :: K2r), fwd) ] ;
       [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ BBox A :: K2r), fwd) ;
         (pair [] [A], bac)] ]
    [(pair H1 (K1l ++ K1r), d) ; (pair H2 (K2l ++ BBox A :: K2r), fwd)].


(* ------------------------------ *)
(* EXCHANGE ON LEFT FOR B1R RULES *)
(* ------------------------------ *)

Lemma gen_swapL_step_b1R_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b1rrules V) ->
    gen_swapL_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_swapL_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_swapL_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *.
  -{ inversion sppc ; subst ; clear sppc. 
     +     use_acm_2TT acm rs swap WBox1Rs.     
     + use_acm_2TT acm rs swap BBox1Rs. }

  - exchL2T rs sppc acm swap.

  -{ inversion sppc ; subst ; clear sppc. 
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm_2TT acm rs swap WBox1Rs.
        *  use_acm_2_sndTT acm rs swap WBox1Rs.
      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm_2TT acm rs swap BBox1Rs.
        * use_acm_2_sndTT acm rs swap BBox1Rs.
   } }
   
Qed.


(* ------------------------------- *)
(* EXCHANGE ON RIGHT FOR B1R RULES *)
(* ------------------------------- *)

Lemma gen_swapR_step_b1R_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b1rrules V) ->
    gen_swapR_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapR_step.
        intros lreq nsr drs acm rs. clear drs. subst.

        inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
        unfold nslclext in nsc.
        apply can_gen_swapR_def'.  intros until 0. intros swap pp ss.
        unfold nslclext in pp. subst.

        acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
        -{ inversion sppc ; subst ; clear sppc. 
           +{ inversion_clear swap. subst.
              acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
              * use_acm_2_swT acm rs swap ltac: (assoc_mid H1) WBox1Rs.
              * use_acm_2_swT acm rs swap ltac: (assoc_mid H4) WBox1Rs.
              * use_acm_2_swT acm rs swap list_assoc_l' WBox1Rs.
              * use_acm_2_swT acm rs swap ltac: (assoc_mid H) WBox1Rs.
            }
           +{ inversion_clear swap. subst.
              acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
              * use_acm_2_swT acm rs swap ltac: (assoc_mid H1) BBox1Rs.
              * use_acm_2_swT acm rs swap ltac: (assoc_mid H4) BBox1Rs.
              * use_acm_2_swT acm rs swap list_assoc_l' BBox1Rs.
              * use_acm_2_swT acm rs swap ltac: (assoc_mid H) BBox1Rs.
            } 
         }
        - exchL2T rs sppc acm swap. 

        -{ inversion sppc ; subst ; clear sppc.
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
              *{ inversion_clear swap. subst.
                 acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r.
                 ** use_acm_2_swT acm rs swap ltac: (assoc_mid H3) WBox1Rs.
                 ** use_acm_2_swT acm rs swap ltac: (assoc_mid H5) WBox1Rs.
                 ** use_acm_2_swT acm rs swap list_assoc_l' WBox1Rs.
                 ** use_acm_2_swT acm rs swap ltac: (assoc_mid H) WBox1Rs.
               }
              *{ inversion_clear swap. subst.
                 acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
                   use_acm_2_sw''T acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
                                                                             ltac: (rewrite list_rearr16') ltac: (rewrite <- list_rearr16') WBox1Rs.
               }
            }
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
              *{ inversion_clear swap. subst.
                 acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
                 ** use_acm_2_swT acm rs swap ltac: (assoc_mid H3) BBox1Rs.
                 ** use_acm_2_swT acm rs swap ltac: (assoc_mid H5) BBox1Rs.
                 ** use_acm_2_swT acm rs swap list_assoc_l' BBox1Rs.
                 ** use_acm_2_swT acm rs swap ltac: (assoc_mid H) BBox1Rs.
               }
              *{ inversion_clear swap. subst.
                 acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
                   use_acm_2_sw''T acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
                                                                             ltac: (rewrite list_rearr16') ltac: (rewrite <- list_rearr16') BBox1Rs. }

            }
         }
Qed.


(* ---------------------- *)
(* WEAKENING FOR B1RRULES *)
(* ---------------------- *)

Lemma gen_weakL_step_b1R_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b1rrules V) ->
    gen_weakL_step last_rule rules ps concl.
Proof.  intros until 0.  unfold gen_swapL_step.
        intros lreq nsr drs acm rs. clear drs. subst.

        inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
        unfold nslclext in nsc.
        eapply can_gen_weakL_def'.  intros until 0. intros swap pp ss.
        unfold nslclext in pp. subst.

        acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
        -{ inversion sppc ; subst ; clear sppc. 
           + use_acm_2_weakT acm rs swap WBox1Rs.
           + use_acm_2_weakT acm rs swap BBox1Rs. }
        - weakL2T rs sppc acm swap.

        -{ inversion sppc ; subst ; clear sppc.
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
              * use_acm_2_weakT acm rs swap WBox1Rs.
              *  use_acm_2_snd_weakT acm rs swap WBox1Rs.
            }
           +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
              * use_acm_2_weakT acm rs swap BBox1Rs.
              * use_acm_2_snd_weakT acm rs swap BBox1Rs.
         } }  
Qed.


Lemma gen_weakR_step_b1R_lc: forall V ps concl last_rule rules,
    (forall (V : Set) ns
            (D : pf rules ns),
        can_gen_swapR rules ns) ->
    last_rule = nslclrule (@b1rrules V) ->
    gen_weakR_step last_rule rules ps concl.
Proof.
  intros until 0. intros Hexch. unfold gen_weakR_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_weakR_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
  -{ inversion sppc ; subst ; clear sppc. 
     +{ inversion_clear swap. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r.
        * use_acm_2_sw_weak_exchT acm rs swap ltac : (assoc_mid H) WBox1Rs Hexch A B.
        * use_acm_2_sw_weakT acm rs swap ltac : (assoc_mid H) WBox1Rs B.
      }
     +{ inversion_clear swap. subst.
        acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
        * use_acm_2_sw_weak_exchT acm rs swap ltac : (assoc_mid H) BBox1Rs Hexch A B.
        * use_acm_2_sw_weakT acm rs swap ltac : (assoc_mid H) BBox1Rs B.
      } 
   }
  - weakL2T rs sppc acm swap. 

  -{ inversion sppc ; subst ; clear sppc.
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r. 
        *{ inversion_clear swap. subst.
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
           ** use_acm_2_sw_weak_exchT acm rs swap ltac: (assoc_mid H) WBox1Rs Hexch A B.
           ** use_acm_2_sw_weakT acm rs swap ltac: (assoc_mid H) WBox1Rs B.
         }
        *{ inversion_clear swap. subst.
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r .
           use_acm_2_sw''_weakT acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
                                                                          ltac: (rewrite list_rearr16';assoc_mid B) ltac: (rewrite - list_rearr16') WBox1Rs. 
           use_acm_2_sw''_weakT acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
                                                                          ltac: (rewrite list_rearr16';assoc_mid B) ltac: (rewrite - list_rearr16') WBox1Rs. 
           use_acm_2_sw''_weakT acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
                                                                          ltac: (rewrite list_rearr16';assoc_mid B) ltac: (rewrite - list_rearr16') WBox1Rs.
         }
      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
        *{ inversion_clear swap. subst.
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r. 
           ** use_acm_2_sw_weak_exchT acm rs swap ltac: (assoc_mid H) BBox1Rs Hexch A B.
           ** use_acm_2_sw_weakT acm rs swap ltac: (assoc_mid H) BBox1Rs B.
         }
        *{ inversion_clear swap. subst.
           acacD'T2 ; subst ; simpl ; rewrite ?app_nil_r ; 
             use_acm_2_sw''_weakT acm rs swap ltac: (list_assoc_r' ; simpl) assoc_single_mid
                                                                            ltac: (rewrite list_rearr16'; assoc_mid B) ltac: (rewrite - list_rearr16') BBox1Rs. }
      }
   }
Qed.



(* ------------------------ *)
(* CONTRACTION FOR B1RRULES *)
(* ------------------------ *)

Lemma gen_contL_gen_step_b1R_lc: forall V ps concl last_rule rules,
    last_rule = nslclrule (@b1rrules V) ->
    gen_contL_gen_step last_rule rules ps concl.
Proof.
  intros until 0.  unfold gen_contL_gen_step.
  intros lreq nsr drs acm rs. clear drs. subst.

  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_contL_gen_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.

  acacD'T2 ; subst ; rewrite -> ?app_nil_r in *. 
  -{ inversion sppc ; subst ; clear sppc. 
     + use_acm_2_contT acm rs swap WBox1Rs.
     + use_acm_2_contT acm rs swap BBox1Rs.
   }
  - contL2T rs sppc acm swap.

  -{ inversion sppc ; subst ; clear sppc. 
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
        * use_acm_2_contT acm rs swap WBox1Rs.
        * use_acm_2_snd_contT acm rs swap WBox1Rs.

      }
     +{ acacDeT2 ; subst ; simpl ; rewrite ?app_nil_r.
        * use_acm_2_contT acm rs swap BBox1Rs.
        * use_acm_2_snd_contT acm rs swap BBox1Rs.
      }
   } 
Qed.

Lemma gen_contR_gen_step_b1R_lc: forall V ps concl last_rule rules,
    (forall (V : Set) ns
            (D : pf rules ns),
        can_gen_swapR rules ns) ->
    last_rule = nslclrule (@b1rrules V) ->
    gen_contR_gen_step last_rule rules ps concl.
Proof.
  intros until 0. intros Hexch. unfold gen_contR_gen_step.
  intros lreq nsr drs acm rs. clear drs. subst.
  inversion nsr as [? ? ? sppc mnsp nsc]. clear nsr.
  unfold nslclext in nsc.
  eapply can_gen_contR_gen_def'.  intros until 0. intros swap pp ss.
  unfold nslclext in pp. subst.
  acacD'T2 ; subst ; rem_nil. 
  -{ inversion sppc ; subst ; clear sppc.
     +{ processT swap; ltsolve_fullT acm A rs WBox1Rs a Hexch. }
     +{ processT swap; ltsolve_fullT acm A rs BBox1Rs a Hexch. }
   }     
  -{ contL2T rs sppc acm swap. }
  -{ inversion sppc ; subst ; clear sppc.
     +{ acacDeT2 ; subst ; simpl ; rem_nil.
        *{ processT swap ; ltsolve_fullT acm A rs WBox1Rs a Hexch. }   
        *{ processT swap ; check_nil_cons_contr; 
           ltsolve_full23T acm A rs WBox WBox1Rs a G. }
      }      
     +{ acacDeT2 ; subst ; simpl ; rem_nil.
        *{ processT swap; ltsolve_fullT acm A rs BBox1Rs a Hexch. }   
        *{ processT swap; check_nil_cons_contr; 
           ltsolve_full23T acm A rs BBox BBox1Rs a G. }
      }
   }
Qed.