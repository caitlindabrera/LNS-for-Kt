Add LoadPath "../general".

Require Import Lemma_Sixteen_setup.
Require Import Lemma_Sixteen_SR_wb_fwd.
Require Import Lemma_Sixteen_SR_wb_bac.
Require Import Lemma_Sixteen_SR_wb.
Require Import Lemma_Sixteen_SR_bb_fwd.
Require Import Lemma_Sixteen_SR_bb_bac.
Require Import Lemma_Sixteen_SR_bb.

Require Import ssreflect.

Set Implicit Arguments.

(* -------------------------- *)
(* Lemma_Sixteen_SR_p_WBox2Rs *)
(* -------------------------- *)

Lemma dersrec_height_nil : forall {X : Type} rl prems (D : @dersrec X rl prems []),
    dersrec_height D = 0.
Proof.
  intros.
  remember [] as G.
  destruct D. reflexivity.
  discriminate.
Qed.

Lemma dersrec_height_nil_gen : forall {X : Type} rl prems G (D : @dersrec X rl prems G),
    G = [] ->
    dersrec_height D = 0.
Proof.
  intros. destruct D. reflexivity.
  discriminate.
Qed.

(* Move to Lemma_Sixteen_setup.v *)
Ltac get_SR_p_from_IH IH HSR n m :=   
  assert (SR_p (n,m)) as HSR;
  [eapply IH; ( (econstructor 1; try reflexivity; lia)
  || (econstructor 2; try reflexivity; lia) ) | ].

Ltac get_SR_p_pre_from_IH IH HSR n m :=
  assert (SR_p_pre n m) as HSR;
  [fold (SR_p ( n, m));
   apply IH; ( (econstructor 1; try reflexivity; lia)
  || (econstructor 2; try reflexivity; lia) ) | ].

Definition get_dersrecD {X} rules prems lG lH D pf :=
(let (D', HD') := (fun (X : Type) (rules : list X -> X -> Type) (prems : X -> Type) 
  (lG lH : list X) (D1 : dersrec rules prems lG) (H0 : lG = lH) =>
eq_rect_r
  (fun lG0 : list X =>
   forall D2 : dersrec rules prems lG0,
   existsT2 D3 : dersrec rules prems lH, dersrec_height D2 = dersrec_height D3)
  (fun D2 : dersrec rules prems lH =>
     existT (fun D3 : dersrec rules prems lH => dersrec_height D2 = dersrec_height D3) D2 eq_refl) H0 D1)
              X rules prems
lG lH D pf in D').

Definition get_dersrec_heightD {X : Type} (rules : list X -> X -> Type) (prems : X -> Type) (lG lH : list X) 
  (D : dersrec rules prems lG) (pf : lG = lH) :=
 EqdepFacts.internal_eq_rew_r_dep
   (fun (lG0 : list X) (pf0 : lG0 = lH) =>
    forall D0 : dersrec rules prems lG0, dersrec_height D0 = dersrec_height (get_dersrecD D0 pf0))
   (fun D0 : dersrec rules prems lH => eq_refl) pf D.


Ltac get_concl_of_derrec :=
  match goal with
  | [ |- derrec _ _ ?C ] => idtac C (*constr:(C)*)
  end.

Ltac get_snd_last_app_of_concl_of_derrec :=
  match goal with
  | [ |- derrec _ _ ?C ] => get_snd_last_app C
  | [ |- pf_LNSKt ?C ] => get_snd_last_app C
  | [ |- pf _ ?C ] => get_snd_last_app C
  end.

Ltac bracket_setup_SR_p1 rl :=
  match rl with
  | Id =>
    match goal with
    | [ |- context[?A ++ [Var ?p] ++ ?B ++ ?C] ] =>
      rewrite (app_assoc _ B); rewrite (app_assoc A)
    end
  | ImpR =>
    match goal with
    | [ H : context[seqext ?Γ1 ?Γ2 _ _ _] |- _] => rewrite (app_assoc Γ1)
    end
  end.


Ltac solve_SR_p_case_B_d_WBox2Rs D2' HSR rl :=
  list_assoc_l;
  match goal with
  | [ |- context[WBox ?AA] ] =>   assoc_mid_loc [WBox AA]
  end;
  fill_tac_WBox2Rs D2' WBox2Rs;
  econstructor; [  | econstructor ]; unfold nslcext || unfold nslclext; simpl;
  list_assoc_r_single;
  bracket_setup_SR_p1 rl;
  eapply HSR;
  [ match rl with
    | Id => econstructor
    | ImpR => econstructor 2
    end; [reflexivity | econstructor; reflexivity]
  |
  | simpl in *; (lia || eassumption)
  | econstructor; reflexivity
  | eassumption
  | eassumption].

Ltac solve_SR_p_case_B_d D2' HSR rl_box rl :=
  unf_pfall; list_assoc_l;
  match goal with
  | [ |- context[WBox ?AA] ] =>   assoc_mid_loc [WBox AA]
  | [ |- context[BBox ?AA] ] =>   assoc_mid_loc [BBox AA]
  end;
  unf_pfall;
  fill_tac_WBox2Rs D2' rl_box;
  econstructor; [  | econstructor ]; unfold nslcext || unfold nslclext; simpl;
  list_assoc_r_single;
  unf_pfall;
  bracket_setup_SR_p1 rl;
  unfold SR_p_pre in HSR; unf_pfall;
  eapply HSR;
  [ match rl with
    | Id => econstructor
    | ImpR => econstructor 2
    end; [reflexivity | econstructor; reflexivity]
  |
  | simpl in *; (lia || eassumption)
  | econstructor; reflexivity
  | eassumption
  | eassumption].

Ltac solve_LNSKt_rules_Id :=
  list_assoc_l; eapply prop;
  (eapply NSlcctxt_nil || idtac );
  list_assoc_r_single;
  (eapply Sctxt_eq || idtac);
  (reflexivity || econstructor).

    Ltac solve_LNSKt_rules_ImpR :=
      list_assoc_l; eapply prop;
  (eapply NSlcctxt_nil || eapply NSlcctxt );
  list_assoc_r_single;
  (eapply Sctxt_eq || eapply Sctxt);
  (reflexivity || econstructor 2).

    Ltac finish_SR_p_case_B_d Hdp :=
      unf_pfall;
  (simpl ; erewrite (dersrec_height_nil (dersrec_nil _ _));
   simpl; erewrite <- get_dpD; eapply Hdp) ||
  (simpl ; erewrite <- get_dersrec_heightD;
   erewrite <- get_dpD; eapply Hdp).

Ltac Hdp_rearr Hdp'' Hdp''' :=
  pose proof Hdp'' as Hdp''';
  simpl in Hdp''';
  rewrite <- PeanoNat.Nat.add_1_l in Hdp''';
  eapply PeanoNat.Nat.le_add_le_sub_l in Hdp'''.

         
(* 
Approach 2
Case B.d.
*)
Lemma Lemma_Sixteen_SR_p_WBox2Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA L1 L2 L3
  (Heqconcl : nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd); ([], [AA], fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  unf_pfall.
  intros.
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2' Hdp HdpD2 Hdp'' Hdp'.
  inversion Hprinc as [? ? ? X | ? ? ? X]; subst.
  +{ (* Last rule in D1 is Id *)
     inversion X. subst.
     simpl in Hdp''.  
     rewrite dersrec_height_nil in Hdp''.
     clear X Hdp' Hprinc D2 rl H1 Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       app_eq_app_dest3;  assoc_mid [WBox AA]; Hdp_rearr Hdp'' Hdp'''.
     ++{         unf_pfall.
         solve_SR_p_case_B_d D2' HSR WBox2Rs (@Id V).
         finish_SR_p_case_B_d Hdp'''.
        } 
       
     ++{         
         solve_SR_p_case_B_d D2' HSR WBox2Rs (@Id V).
         finish_SR_p_case_B_d Hdp'''.         
       }       
    }
    
  +{ (* Last rule in D1 is ImpR *)
     inversion X. subst.
     simpl in Hdp''. simpl in Hdp'.
     destruct (dersrec_derrec_dp D2 eq_refl) as [D1 HdpD1].
     assert (Hdp1'' : dp D1 + S (dp D2') <= m); [ rewrite HdpD1  |  ].
     apply Le.le_Sn_le. assumption.
     clear X Hprinc rl Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       app_eq_app_dest3; try discriminate; list_assoc_r_single.
     
     ++{
         solve_SR_p_case_B_d D2' HSR WBox2Rs (@ImpR V). 
         finish_SR_p_case_B_d Hdp'.           
       }
     ++{
         solve_SR_p_case_B_d D2' HSR WBox2Rs (@ImpR V). 
         finish_SR_p_case_B_d Hdp'. 
       }       
     ++{ destruct Hl2; discriminate. }
    }
    Unshelve.
   
   all : (solve [solve_LNSKt_rules_Id] ||
          solve [solve_LNSKt_rules_ImpR] ||
    (unfold nslclext; solve_eqs)).
Qed.

(* -------------------------- *)
(* Lemma_Sixteen_SR_p_BBox2Rs *)
(* -------------------------- *)


Ltac solve_SR_p_case_B_d_BBox2Rs D2' HSR rl :=
      list_assoc_l;
      match goal with
      | [ |- context[BBox ?AA] ] =>   assoc_mid [BBox AA]
      end;
  fill_tac_WBox2Rs D2' BBox2Rs;
      econstructor; [  | econstructor ]; unfold nslcext || unfold nslclext; simpl;
      list_assoc_r_single;
bracket_setup_SR_p1 rl;
      eapply HSR;
      [ match rl with
        | Id => econstructor
        | ImpR => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      |
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      | eassumption
      | eassumption].

(* Original. To be deleted if extraction works. *)
Ltac solve_SR_p_case_B_d_BBox2Rs' D2' HSR rl :=
      list_assoc_l;
      match goal with
      | [ |- context[BBox ?AA] ] =>   assoc_mid [BBox AA]
      end;
                  eapply derI;
            [eapply b2r; econstructor;
            simpl; eapply BBox2Rs | ];
      econstructor; [  | econstructor ]; unfold nslcext || unfold nslclext; simpl;
      list_assoc_r_single;
bracket_setup_SR_p1 rl;
      eapply HSR;
      [ match rl with
        | Id => econstructor
        | ImpR => econstructor 2
        end; [reflexivity | econstructor; reflexivity]
      |
      | simpl in *; (lia || eassumption)
      | econstructor; reflexivity
      | eassumption
      | eassumption].


(* 
Approach 2
Case B.d.
*)

Lemma Lemma_Sixteen_SR_p_BBox2Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA L1 L2 L3
  (Heqconcl : nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac); ([], [AA], bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.  
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2' Hdp HdpD2 Hdp'' Hdp'.
  inversion Hprinc as [? ? ? X | ? ? ? X]; subst.
  +{ (* Last rule in D1 is Id *)
     inversion X. subst.
     simpl in Hdp''.  
     rewrite dersrec_height_nil in Hdp''.
     clear X Hdp' Hprinc D2 rl H1 Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       app_eq_app_dest3;  assoc_mid [BBox AA]; Hdp_rearr Hdp'' Hdp'''.
     ++{
         solve_SR_p_case_B_d D2' HSR BBox2Rs (@Id V).
         finish_SR_p_case_B_d Hdp'''.
        } 
       
     ++{         
         solve_SR_p_case_B_d D2' HSR BBox2Rs (@Id V).
         finish_SR_p_case_B_d Hdp'''.         
       }       
    }
    
  +{ (* Last rule in D1 is ImpR *)
     inversion X. subst.
     simpl in Hdp''. simpl in Hdp'.
     destruct (dersrec_derrec_dp D2 eq_refl) as [D1 HdpD1].
     assert (Hdp1'' : dp D1 + S (dp D2') <= m); [ rewrite HdpD1  |  ].
     apply Le.le_Sn_le. assumption.
     clear X Hprinc rl Hbox.
     unfold nslclext in Heqconcl.
     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       app_eq_app_dest3; try discriminate; list_assoc_r_single.
     
     ++{
         solve_SR_p_case_B_d D2' HSR BBox2Rs (@ImpR V). 
         finish_SR_p_case_B_d Hdp'.           
       }
     ++{
         solve_SR_p_case_B_d D2' HSR BBox2Rs (@ImpR V). 
         finish_SR_p_case_B_d Hdp'. 
       }       
     ++{ destruct Hl2; discriminate. }
    }
    Unshelve.
   
   all : (solve [solve_LNSKt_rules_Id] ||
          solve [solve_LNSKt_rules_ImpR] ||
    (unfold nslclext; solve_eqs)).
Qed.

(* -------------------------- *)
(* Lemma_Sixteen_SR_p_WBox1Rs *)
(* -------------------------- *)


Lemma le_S_minus : forall n m,
    S n <= m -> n <= m - 1.
Proof. intros. lia. Qed.

Ltac solve_SR_p_WBox1Rs D1 D2a D2a' Hdpa' D2b D2b' Hdpb' HSR rl :=
  unf_pfall; solve_case_G_gen_draft_setup D2a D2a' D2b D2b';
  unfold nslclext in *;
  unf_pfall;
  fill_tac_case_G_b1r D1 D2a' D2b' rl;      
  econstructor; [  | econstructor; [  | econstructor ] ];
  unfold nslcext || unfold nslclext; simpl; list_assoc_r_single;
  unfold SR_p_pre in HSR; unf_pfall;
  [ eapply HSR; try eassumption;
    erewrite (dp_get_D D2a) in Hdpa'; eapply Hdpa' |
    eapply HSR; try eassumption;
    erewrite (dp_get_D D2b) in Hdpb'; eapply Hdpb'].


(* 
Approach 2
Case B.d.
*)

Lemma Lemma_Sixteen_SR_p_WBox1Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : @pf_LNSKt V (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d2); (L2, L5 ++ WBox AA :: L6, bac)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1, L3 ++ AA :: L4, d2); (L2, L5 ++ WBox AA :: L6, bac)];
          nslclext ctxt
            [(L1, L3 ++ L4, d2); (L2, L5 ++ WBox AA :: L6, bac); ([], [AA], fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hsize : fsize A <= S n)
  (Hbox : not_box A)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.  
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s Hmax1 Hmax2.
  app_eq_app_dest3.
  +{ (* A not in main components of D2 *)
      solve_SR_p_WBox1Rs D1 D2a D2a' Hdpa' D2b D2b' Hdpb' HSR WBox1Rs.
    }
    
  +{  (* A in second last component of D2 *)
      solve_SR_p_WBox1Rs D1 D2a D2a' Hdpa' D2b D2b' Hdpb' HSR WBox1Rs.
    } 

  +{ (* A in last component of D2 *)

      pose proof (merge_app_struct_equiv_strR _ _ Hme Hstr).
      sD. subst.

      unfold LNS in *; unfold seq in *; dest_pairs.
      eapply merge_app_single in Hme; [ | eassumption].
      sD. subst.
      list_assoc_r_single.

      solve_case_G_gen_draft_setup D2a D2a' D2b D2b'.
      unfold nslclext in *. list_assoc_r_single.       
      fill_tac_case_G_b1r D1 D2a' D2b' WBox1Rs.
      
      econstructor; [  | econstructor; [  | econstructor ] ];
        unfold nslcext || unfold nslclext; simpl; list_assoc_r_single.

      bracket_set_up1_pre D2a' A;
        repeat rewrite <- (app_assoc Γ);
        bracket_set_up2_extra;
      eapply HSR;
        [eassumption |
         erewrite (dp_get_D D2a) in Hdpa'; eapply Hdpa' |
         eassumption |
         eassumption |
         |
         merge_solve_primitive];
        eapply struct_equiv_str_app_single; eassumption.
      
      bracket_set_up1_pre D2a' A;
        repeat rewrite <- (app_assoc Γ);
        bracket_set_up2_extra;
      eapply HSR;
        [eassumption |
         erewrite (dp_get_D D2b) in Hdpb'; eapply Hdpb' |
         eassumption |
         eassumption |
         |
         merge_solve_primitive];
        eapply struct_equiv_str_app_single; eassumption.
    }

    Unshelve. all : (subst; solve_eqs).
Qed.

(* -------------------------- *)
(* Lemma_Sixteen_SR_p_BBox1Rs *)
(* -------------------------- *)

(* 
Approach 2
Case B.d.
*)

Lemma Lemma_Sixteen_SR_p_BBox1Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d2); (L2, L5 ++ BBox AA :: L6, fwd)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1, L3 ++ AA :: L4, d2); (L2, L5 ++ BBox AA :: L6, fwd)];
          nslclext ctxt
            [(L1, L3 ++ L4, d2); (L2, L5 ++ BBox AA :: L6, fwd); ([], [AA], bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hsize : fsize A <= S n)
  (Hbox : not_box A)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.  
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s Hmax1 Hmax2.
  app_eq_app_dest3.
  +{ (* A not in main components of D2 *)
      solve_SR_p_WBox1Rs D1 D2a D2a' Hdpa' D2b D2b' Hdpb' HSR BBox1Rs.
    }
    
  +{  (* A in second last component of D2 *)
      solve_SR_p_WBox1Rs D1 D2a D2a' Hdpa' D2b D2b' Hdpb' HSR BBox1Rs.
    } 

  +{ (* A in last component of D2 *)

      pose proof (merge_app_struct_equiv_strR _ _ Hme Hstr).
      sD. subst.

      unfold LNS in *; unfold seq in *; dest_pairs.
      eapply merge_app_single in Hme; [ | eassumption].
      sD. subst.
      list_assoc_r_single.

      solve_case_G_gen_draft_setup D2a D2a' D2b D2b'.
      unfold nslclext in *. list_assoc_r_single.       
      fill_tac_case_G_b1r D1 D2a' D2b' BBox1Rs.
      
      econstructor; [  | econstructor; [  | econstructor ] ];
        unfold nslcext || unfold nslclext; simpl; list_assoc_r_single.

      bracket_set_up1_pre D2a' A;
        repeat rewrite <- (app_assoc Γ);
        bracket_set_up2_extra;
      eapply HSR;
        [eassumption |
         erewrite (dp_get_D D2a) in Hdpa'; eapply Hdpa' |
         eassumption |
         eassumption |
         |
         merge_solve_primitive];
        eapply struct_equiv_str_app_single; eassumption.
      
      bracket_set_up1_pre D2a' A;
        repeat rewrite <- (app_assoc Γ);
        bracket_set_up2_extra;
      eapply HSR;
        [eassumption |
         erewrite (dp_get_D D2b) in Hdpb'; eapply Hdpb' |
         eassumption |
         eassumption |
         |
         merge_solve_primitive];
        eapply struct_equiv_str_app_single; eassumption.
    }

    Unshelve. all : (subst; solve_eqs).
Qed.



(* -------------------------- *)
(* Lemma_Sixteen_SR_p_WBox2Ls *)
(* -------------------------- *)

Ltac solve_SR_p_WBBox2Ls1 HSR D2 tac constr :=
  list_assoc_r_single;
  eapply derI;
  [eapply b2l;
   econstructor; tac;
   eapply constr
  |
  (econstructor; [ | econstructor]);
  unfold nslclext;
  list_assoc_r_single;
  rewrite <- (app_nil_r [_]);
  unfold SR_p_pre in HSR;
  simpl;
  solve_derrec_weak_arg D2
  ].

Ltac SR_p_WBBox2Ls_not_snd_last_comp2 D2 HSR Hdp' constr :=
      inv_app_hd_tl_full;
     tac_cons_singleton;     
     eapply derI; [
     eapply b2l;     
     list_assoc_l';
     eapply nslclrule_b2lrules2; [reflexivity | reflexivity |];
     list_assoc_r';
     eapply constr | ];
     
     econstructor; [ | econstructor];
     unfold nslclext;
     list_assoc_r; simpl;
     tac_cons_singleton;
     eapply HSR; try eassumption;
       erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
       eapply Hdp'.

Ltac SR_p_WBBox2Ls_not_snd_last_comp D2 HSR Hdp' constr :=
      simpl;
      inv_app_hd_tl_full;
      list_assoc_r_single;
      eapply derI;
      [eapply b2l ;
       eapply nslclrule_b2lrules2;
       [reflexivity | ((list_assoc_l'; reflexivity) || (rewrite <- app_assoc;  reflexivity)) | ];
       match goal with
       | |- context [BBox ?AA] =>
         bracket_list_assoc_r_arg_derrec2 D2 AA
       | |- context [WBox ?AA] =>
         bracket_list_assoc_r_arg_derrec2 D2 AA
         end;
      eapply constr | ];
     econstructor; [ | econstructor];
     simpl; list_assoc_r_single;
     match goal with
     | D2 : context[?AA:PropF _] |- context[?AA : PropF _] => fail
     | D2 : context[?A : PropF _] |- context[?AA : PropF _] => 
       bracket_list_assoc_r_arg_derrec3 D2 A
       end;
       subst;           
     eapply HSR; try eassumption;
       erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp';
       eapply Hdp'.

(* 
Approach 2
Case B.a.
*)

Lemma Lemma_Sixteen_SR_p_WBox2Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ L2, L5, d2); (L3 ++ WBox AA :: L4, L6, bac)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d2)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d D1 ctxt AA d2 L1 L2 L3 L4 L5 L6
  Heqconcl Hprinc D2s Hdp Hsize HBox Hstr Hme.
  unfold nslclext in *.
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  rename Heqconcl into Heqconcl'.
  
  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD; subst; simpl in Heqconcl';
    inv_app_hd_tl_full.
  +{
      app_eq_app_dest3; try contradiction;
      tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp';
      try solve [inversion HBox; discriminate];
      pose proof (merge_app_struct_equiv_strR _ _ Hme Hstr);
      sD; subst;
      unfold LNS in *; unfold seq in *; dest_pairs;
      (eapply merge_app_single in Hme; [ | eassumption]);
      sD; subst.
      solve_SR_p_WBBox2Ls1 HSR D2 ltac:(simpl; list_assoc_l) WBox2Ls.
      solve_SR_p_WBBox2Ls1 HSR D2 ltac:(
                                 match goal with
                         | |- context [WBox ?AA] => assoc_mid [WBox AA]
                         end; simpl) WBox2Ls.
    }

  +{
      app_eq_app_dest3; try contradiction;
      tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp';
      try solve [inversion HBox; discriminate].

SR_p_WBBox2Ls_not_snd_last_comp2 D2 HSR Hdp' WBox2Ls.
SR_p_WBBox2Ls_not_snd_last_comp D2 HSR Hdp' WBox2Ls.
SR_p_WBBox2Ls_not_snd_last_comp D2 HSR Hdp' WBox2Ls.
SR_p_WBBox2Ls_not_snd_last_comp D2 HSR Hdp' WBox2Ls.

Unshelve. all : solve_eqs.
    }
Qed.


(* -------------------------- *)
(* Lemma_Sixteen_SR_p_BBox2Ls *)
(* -------------------------- *)

(* 
Approach 2
Case B.a.
 *)

Lemma Lemma_Sixteen_SR_p_BBox2Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d 
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ L2, L5, d2); (L3 ++ BBox AA :: L4, L6, fwd)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d2)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d D1 ctxt AA d2 L1 L2 L3 L4 L5 L6
  Heqconcl Hprinc D2s Hdp Hsize HBox Hstr Hme.
  unfold nslclext in *.
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  rename Heqconcl into Heqconcl'.
  
  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD; subst; simpl in Heqconcl';
    inv_app_hd_tl_full.
  +{
      app_eq_app_dest3; try contradiction;
      tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp';
      try solve [inversion HBox; discriminate];
      pose proof (merge_app_struct_equiv_strR _ _ Hme Hstr);
      sD; subst;
      unfold LNS in *; unfold seq in *; dest_pairs;
      (eapply merge_app_single in Hme; [ | eassumption]);
      sD; subst.
      solve_SR_p_WBBox2Ls1 HSR D2 ltac:(simpl; list_assoc_l) BBox2Ls.
      solve_SR_p_WBBox2Ls1 HSR D2 ltac:(
                                 match goal with
                         | |- context [BBox ?AA] => assoc_mid [BBox AA]
                         end; simpl) BBox2Ls.
    }

  +{
      app_eq_app_dest3; try contradiction;
      tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp';
      try solve [inversion HBox; discriminate].

SR_p_WBBox2Ls_not_snd_last_comp2 D2 HSR Hdp' BBox2Ls.
SR_p_WBBox2Ls_not_snd_last_comp D2 HSR Hdp' BBox2Ls.
SR_p_WBBox2Ls_not_snd_last_comp D2 HSR Hdp' BBox2Ls.
SR_p_WBBox2Ls_not_snd_last_comp D2 HSR Hdp' BBox2Ls.

Unshelve. all : solve_eqs.
    }
Qed.


(* -------------------------- *)
(* Lemma_Sixteen_SR_p_WBox1Ls *)
(* -------------------------- *)

(* 
Approach 2
Case B.d.
 *)

Lemma Lemma_Sixteen_SR_p_WBox1Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d2); (L3 ++ L4, L6, fwd)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d2); (L3 ++ AA :: L4, L6, fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hsize : fsize A <= S n)
  (Hbox : not_box A)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  unf_pfall.
  intros.
  unfold nslclext in *.
  get_SR_p_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  Ltac fill_tac_WBox1Ls D2' rl :=
    unf_pfall;
  eapply derI;
  [eapply b1l ;
   rewrite <- app_assoc;
   econstructor;
   list_assoc_r_single;
   unf_pfall;
   bracket_set_up1_redo D2' rl;
   (*      assoc_mid_loc [WBox AA] ; *)
   simpl; eapply rl | ].

  
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate);

    
    (* Solves goal when merge clauses are straightforward *)
    try ( unf_pfall;
          list_assoc_r_arg_derrec2_spec D2 D2';
          list_assoc_r_single; list_assoc_l;
          unf_pfall;
  fill_tac_WBox1Ls D2' WBox1Ls;
  econstructor; [ | econstructor];
  unfold nslclext;
  list_assoc_r_single;
  unf_pfall;
  try (bracket_set_up1_pre_snd D2' A;
       repeat rewrite <- (app_assoc Γ));
  unfold SR_p in HSR; unfold SR_p_pre in HSR; unf_pfall;
  eapply HSR; try eassumption;
  erewrite <- (dp_get_D D2);
  eassumption);

    (* Solves goal when merge need work *)
    (    pose proof (merge_app_struct_equiv_strR _ _ Hme Hstr);
      sD; subst;

      unfold LNS in *; unfold seq in *; dest_pairs;
      eapply merge_app_single in Hme; [ | eassumption];
      sD; subst;
    
    list_assoc_r_arg_derrec2_spec D2 D2';
    list_assoc_r_single; list_assoc_l;
                           fill_tac_WBox1Ls D2' WBox1Ls;
  econstructor; [ | econstructor];
    
    unfold nslclext;
    list_assoc_r_single;


bracket_set_up1_pre D2' A;
repeat rewrite <- (app_assoc Γ);
bracket_set_up2_extra;
  unfold SR_p in HSR; unfold SR_p_pre in HSR; unf_pfall;
eapply HSR; try eassumption;
  
  [ erewrite <- (dp_get_D D2) ; eassumption |
    merge_solve_primitive ]).



    
    Unshelve. all : subst; solve_eqs.
Qed.

(* -------------------------- *)
(* Lemma_Sixteen_SR_p_BBox1Ls *)
(* -------------------------- *)

(* 
Approach 2
Case B.d.
 *)

Lemma Lemma_Sixteen_SR_p_BBox1Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt AA d2 L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d2); (L3 ++ L4, L6, bac)] =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d2); (L3 ++ AA :: L4, L6, bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hsize : fsize A <= S n)
  (Hbox : not_box A)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
  Proof.
  intros.
  unfold nslclext in *.
  get_SR_p_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate);

    
    (* Solves goal when merge clauses are straightforward *)
    try (
          list_assoc_r_arg_derrec2_spec D2 D2';
  list_assoc_r_single; list_assoc_l;
  fill_tac_WBox1Ls D2' BBox1Ls;
  econstructor; [ | econstructor];
  unfold nslclext;
  list_assoc_r_single;
  try (bracket_set_up1_pre_snd D2' A;
       repeat rewrite <- (app_assoc Γ));
  unfold SR_p in HSR; unfold SR_p_pre in HSR; unf_pfall;
  eapply HSR; try eassumption;
  erewrite <- (dp_get_D D2);
  eassumption);
    

    (* Solves goal when merge need work *)
    (    pose proof (merge_app_struct_equiv_strR _ _ Hme Hstr);
      sD; subst;

      unfold LNS in *; unfold seq in *; dest_pairs;
      eapply merge_app_single in Hme; [ | eassumption];
      sD; subst;
    
    list_assoc_r_arg_derrec2_spec D2 D2';
    list_assoc_r_single; list_assoc_l;
                           fill_tac_WBox1Ls D2' BBox1Ls;
  econstructor; [ | econstructor];
    
    unfold nslclext;
    list_assoc_r_single;


bracket_set_up1_pre D2' A;
repeat rewrite <- (app_assoc Γ);
bracket_set_up2_extra;
  unfold SR_p in HSR; unfold SR_p_pre in HSR; unf_pfall;
eapply HSR; try eassumption;
  
  [ erewrite <- (dp_get_D D2) ; eassumption |
    merge_solve_primitive ]).

    Unshelve. all : subst; solve_eqs.
Qed.


(* --------------------- *)
(* Lemma_Sixteen_SR_p_EW *)
(* --------------------- *)

(* 
Approach 2
Case B.b.
 *)

Lemma Lemma_Sixteen_SR_p_EW : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt L1 L2 d2
  (Heqconcl : nslclext ctxt [(L1, L2, d2)] = H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : pfs_LNSKt 
          [nslclext ctxt []])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : fsize A <= S n)
  (Hbox : not_box A)
  (Hsize : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.
  unfold nslclext in *.
  get_SR_p_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD; subst; simpl in Heqconcl.

  +{ (* A in last component. *)
      inv_app_hd_tl_full.
      eapply derrec_weakened_nseq.
      2:{ eapply derI.
          eapply nEW.
          econstructor.
          econstructor.

          simpl. econstructor; [ | econstructor].
          apply D2. }

      unfold nslclext.
      apply weakened_nseq_app_sameR.
      eapply merge_weakened_nseqR; eassumption.
    }
    
  +{ (*  A not in last component. *)
      inv_app_hd_tl_full.
      tac_cons_singleton.
      list_assoc_l.
      eapply derI.
      eapply nEW. econstructor. econstructor.
      simpl. econstructor; [ | econstructor].
      unfold nslclext.
      rewrite app_nil_r.
      list_assoc_r_single.

      eapply HSR; try eassumption.
      erewrite (@dp_get_D _ _ _ _ _ D2) in Hdp'.
      eapply Hdp'.

      Unshelve. repeat rewrite app_nil_r; solve_eqs.
    } 
Qed.


(* ------------------------- *)
(* Lemma_Sixteen_SR_p_Id *)
(* ------------------------- *)

(* Solves a goal of the form 
InT a l
where l is a series of cons and apps.
*)
Ltac solve_InT := 
  list_assoc_r; repeat (
                    (eapply InT_eq'; reflexivity) ||
                    (eapply InT_cons) ||
                    eapply InT_appR).

(* Solves a goal of the form
derrec (LNSKt_rules _) _ G
where it is a valid application of Id.
*)
Ltac solve_Id :=
  unf_pfall; list_assoc_l;
  match goal with 
  | |- derrec _ _ (?G ++ [(?l1,?l2,?d)])  =>
    match l1 with
    | context[ Var ?p ] =>
      match l2 with
      | context[ Var p ] =>
        eapply (@Id_InT _ _ _ _ _ p)
      end;
        solve_InT
    end
  end.

(* 
Approach 2
Case A.b + B.c.
 *)

Lemma Lemma_Sixteen_SR_p_Id : forall
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt d2 Φ1 Φ2 Ψ1 Ψ2 p
  (Heqconcl : nslcext ctxt d2 (Φ1 ++ Var p :: Φ2, Ψ1 ++ Var p :: Ψ2) =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (Hbox : not_box A),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.  
  inversion Hprinc as [? ? ? X | ? ? ? X]; subst;
    unfold nslcext in *;
    inversion X; subst;
      app_eq_app_dest3; try contradiction; try discriminate;
        solve_Id.
Qed.

(* --------------------------- *)
(* Lemma_Sixteen_SR_p_ImpR *)
(* --------------------------- *)

(* Solves a goal of the form
... ++ [a] = [] 
or
[] = ... ++ [a]
*)
Ltac discriminate_single_end :=
  repeat (match goal with
          | H : [] = ?l1 ++ ?l2 |- _ => apply nil_eq_appT in H
          | H : ?l1 ++ ?l2 = [] |- _ => symmetry in H
          end; sD; try discriminate).

 Lemma fold_app_lem : forall (A : Type) H2 Σ2, 
   (fix app (l m0 : list A) {struct l} : 
               list A :=
                 match l with
                 | [] => m0
                 | a :: l1 => a :: app l1 m0
                 end) H2 Σ2 = app H2 Σ2.
 Proof. reflexivity. Qed.

 Ltac fold_app := repeat rewrite fold_app_lem.
 
(* 
Approach 2
Case B.d.
 *)

Lemma Lemma_Sixteen_SR_p_ImpR : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt d2 Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d2 (Φ1 ++ Φ2, Ψ1 ++ Imp AA BB :: Ψ2) =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslcext ctxt d2 (Φ1 ++ AA :: Φ2, Ψ1 ++ Imp AA BB :: BB :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hsize : fsize A <= S n)
  (Hbox : not_box A)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.
  unfold nslclext in *.
  get_SR_p_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  unfold nslcext in *.
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate);


    (    list_assoc_r_arg_derrec2_spec D2 D2';
          list_assoc_r_single; list_assoc_l;
fill_tac_ImpR D2' (@ImpR V);
fold_app;
          econstructor; [ | econstructor];
  unfold nslcext;   unfold seqext;
  list_assoc_r_single;
  try (bracket_set_up1_pre D2' A;
       repeat rewrite <- (app_assoc Γ));
  unfold SR_p in HSR; unfold SR_p_pre in HSR; unf_pfall;  
  eapply HSR; try eassumption;
  erewrite <- (dp_get_D D2);
  eassumption).
  
  Unshelve. all : subst; solve_eqs.
Qed.


(* --------------------------- *)
(* Lemma_Sixteen_SR_p_ImpL *)
(* --------------------------- *)

Lemma map_singleton:
  forall (A B : Type) (f : A -> B) (x : A), map f [x] = [f x].
Proof. reflexivity. Qed.

Lemma map_double_singleton : forall {A B : Type} (f : A -> B) (x y : A),
    map f [x;y] = [f x; f y].
Proof. reflexivity. Qed.

(* From dd_fc *)
Ltac tfm_dersrec_derrec2_dp_keep D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
  Hmax1 Hmax2 :=
  assert (HeqD2s : dersrec_height D2s = dersrec_height D2s); [ reflexivity |  ];
   destruct (dersrec_derrec2_dp D2s HeqD2s) as [D2a [D2b HdpD2]]; clear HeqD2s;
   epose proof (Max.le_max_r _ _) as Hmax1; epose proof (Max.le_max_l _ _) as Hmax2;
   rewrite <- HdpD2 in Hmax1; rewrite <- HdpD2 in Hmax2;
   match goal with
   | H:dp ?D1 + S (dersrec_height D2s) <= ?m
     |- _ =>
         assert (Hdpa'' : dp D1 + S (dp D2a) <= m); [ lia |  ];
          assert (Hdpb'' : dp D1 + S (dp D2b) <= m); [ lia |  ];
          assert (Hdpa' : dp D1 + dp D2a <= m - 1); [ lia |  ];
          assert (Hdpb' : dp D1 + dp D2b <= m - 1); [ lia |  ]; clear HdpD2 Hdp
          Hmax1 Hmax2
   end.


     Ltac bracket_last_comp_centre_Imp:=
     repeat bracket_set_up2_extra;
       match goal with
       | |- context [Imp ?AA ?BB] => assoc_mid_loc [Imp AA BB]
       end.
     
         Ltac bracket_last_app L :=
     match get_last_app L with
     | ?l => 
       match goal with
       | |- context [l ++ ?l2 ++ ?l3] => assoc_mid_loc l2
       | |- context [l ++ ?l2] => assoc_mid_loc l;
                                     rewrite (app_assoc _ l);
                                     repeat rewrite <- (app_assoc _ _ l)
       end
     end.

     Ltac get_L_of_D D1 :=
          match type of D1 with
          | derrec _ _ (?G ++ [(?Γ,?Δ,?d)]) => constr:(Γ)
          | pf _ (?G ++ [(?Γ,?Δ,?d)]) => constr:(Γ)
          | pf_LNSKt (?G ++ [(?Γ,?Δ,?d)]) => constr:(Γ)
          end.

     Ltac bracket_last_app_L_of_D D1 :=
       bracket_last_app ltac:(get_L_of_D D1).


     Ltac bracket_snd_app_slot_A_in_D2 D2a :=
     match type of D2a with
     | context [Imp ?AA ?BB] =>
       match type of D2a with
       | context [[?A] ++ ?l] =>
         match A with
         | Imp AA BB => fail
         | _ => idtac
         end;
           match goal with
           | |- derrec _ _ (?G ++ [(?Γ ++ ?L,_,_)]) =>
             prep_apply_BBox2Ls_preL l L
           | |- pf _ (?G ++ [(?Γ ++ ?L,_,_)]) =>
             prep_apply_BBox2Ls_preL l L
           | |- pf_LNSKt (?G ++ [(?Γ ++ ?L,_,_)]) =>
             prep_apply_BBox2Ls_preL l L
           end
       end
     | context [[?A] ++ ?l] =>
       match goal with
       | |- derrec _ _ (?G ++ [(?Γ ++ ?L,_,_)]) =>
         prep_apply_BBox2Ls_preL l L
       | |- pf _ (?G ++ [(?Γ ++ ?L,_,_)]) =>
         prep_apply_BBox2Ls_preL l L
       | |- pf_LNSKt (?G ++ [(?Γ ++ ?L,_,_)]) =>
         prep_apply_BBox2Ls_preL l L
       end
     end.       

     Ltac bracket_R_app_arg l :=
       unf_pf; unf_pflnskt; repeat match goal with
     | |- derrec _ _ (?GH ++ [(_,?L,_)]) =>
       match L with
       | ?l1 ++ l => rewrite (app_assoc l1)
       | ?l1 ++ ?l2 ++ ?l3 => rewrite (app_assoc l1 l2)
       | ?l1 ++ ?l2 => idtac
       end
     end.

     Ltac bracket_match_R_D2a D2a :=
       unf_pf; unf_pflnskt; match type of D2a with
       | derrec _ _ (nslcext _ _ (_,?l)) =>
         bracket_R_app_arg l
       | derrec _ _ (_ ++ (_,?l,_)) =>
         bracket_R_app_arg l
       end.

          Ltac eassumption_rem_nil :=
            eassumption || solve [(repeat (rem_nil; try eassumption))].
          
     Ltac solve_SR_p_ImpL_Bd HSR D1 D2a D2b Hdpa' Hdpb' :=
     list_assoc_r_single;
     bracket_last_comp_centre_Imp;
     bracket_match_R_D2a D2a;

     eapply derI;
     [eapply prop;
     econstructor;
     eapply Sctxt_eq;
     [ eapply ImpL | reflexivity ..] | ];
     (econstructor; [ | econstructor; [ | econstructor]]);
     unfold nslcext; unfold seqext;
     list_assoc_r_single;

     [bracket_last_app_L_of_D D1;
      try bracket_snd_app_slot_A_in_D2 D2a;
      unfold SR_p in HSR; unfold SR_p_pre in HSR; unf_pfall;
     eapply HSR; try eassumption_rem_nil;
     rewrite <- get_dpD;
     eapply Hdpa' |

     bracket_last_app_L_of_D D1;
     try bracket_snd_app_slot_A_in_D2 D2b;
     unfold SR_p in HSR; unfold SR_p_pre in HSR; unf_pfall;
     eapply HSR; try eassumption_rem_nil;
     rewrite <- get_dpD;
     eapply Hdpb' ].
     
      Ltac subst_hyp H :=
        match type of H with
        | ?A = ?B => (subst A) || (subst B)
        end.
            Ltac rewrite_hyp_in_shape_hyps Hrewr shape :=
        repeat match goal with
        | H : context[shape] |- _ => rewrite Hrewr in H
               end.

            Ltac existential_goal_for_ImpR_der :=
           apply prop; rewrite <- map_singleton;
             econstructor;
             eapply Sctxt_eq;
               [eapply ImpR; reflexivity | reflexivity ..].


(* 
Approach 2
Case A.a + B.d.
 *)

Lemma Lemma_Sixteen_SR_p_ImpL : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt d2 Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d2 (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  ( D2s : pfs_LNSKt
          [nslcext ctxt d2 (Φ1 ++ Imp AA BB :: BB :: Φ2, Ψ1 ++ Ψ2);
          nslcext ctxt d2 (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ AA :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hsize : fsize A <= S n)
  (Hbox : not_box A)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.  
  get_SR_p_pre_from_IH IH HSR (S n) (m - 1).
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).

  pose proof Hdp as Hdp_keep.
  tfm_dersrec_derrec2_dp_keep D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
  Hmax1 Hmax2.
  inversion Hprinc as [? ? ? X | ? ? ? X]; subst.
  +{ (* Last rule in D1 is Id 
      Approach 2
      Case B.d.
      *)
      unf_pfall.
      unfold nslcext in Heqconcl.
      app_eq_app_dest3; try contradiction; try (inversion X; discriminate);
        solve_SR_p_ImpL_Bd HSR D1 D2a D2b Hdpa' Hdpb'.
      Unshelve.
      all : unfold nslcext; rem_nil;  solve_eqs.
  }    

  +{ (* Last rule in D1 is ImpR  *)
      destruct (@merge_ex_str _ GH GH) as [GHGH HmeGH].
      eapply struct_equiv_str_refl.
      destruct (@merge_ex_str _ GHGH GH) as [GHGHGH HmeGHGH].
      eapply struct_equiv_str_comm.
      eapply struct_equiv_str_mergeR.
      eapply struct_equiv_str_refl.
      eapply HmeGH.      
      
      inversion X as [? ? ? ? ? D1' rl H1 H2 H3 H4]. subst.


     simpl in Hdpa''.  
     simpl in Hdpb''.
     unfold nslclext in Heqconcl.
     simpl in Hdpa'.
     simpl in Hdpb'.
     simpl in *.
     clear X.

     destruct (dersrec_derrec_dp D1' eq_refl) as [D1'' HdpD1''].
     assert (Hdp1a'' : dp D1'' + S (dp D2a) <= m); [ rewrite HdpD1''  |  ].
     apply Le.le_Sn_le. assumption.
     assert (Hdp1b'' : dp D1'' + S (dp D2b) <= m); [ rewrite HdpD1''  |  ].
     apply Le.le_Sn_le. assumption.

     destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst;
       simpl in Heqconcl;
       unfold nslcext in Heqconcl;
       app_eq_app_dest3; try contradiction; try discriminate;
         discriminate_single_end.

     ++{ (* Approach 2
            Case B.d
          *)

         epose proof (derI _ _ D1') as D1.
         Unshelve.
         3:{ existential_goal_for_ImpR_der. }
         unfold nslcext in D1.
         solve_SR_p_ImpL_Bd HSR D1 D2a D2b Hdpa' Hdpb'.
         Unshelve. all : unfold nslcext; rem_nil; solve_eqs.
}

     ++{ (* Approach 2
            Case B.d
          *)
         
         epose proof (derI _ _ D1') as D1.
         Unshelve.
         3:{ existential_goal_for_ImpR_der. }
         unfold nslcext in D1.
         solve_SR_p_ImpL_Bd HSR D1 D2a D2b Hdpa' Hdpb'.
         Unshelve. all : unfold nslcext; rem_nil; solve_eqs.
       }

     ++{ (* Approach 2
            Case A.a
          *)
         rewrite app_nil_r in Hstr, Hme.
         inversion_Kt_fml. subst.
         eremember (derI _ _ D1') as D1.
         eremember (derI _ _ D2s) as D2.

         Unshelve.
         3:{  eapply prop.
              rewrite <- map_double_singleton. econstructor.
              eapply Sctxt_eq.
              eapply ImpL.
              reflexivity.
              reflexivity.
              reflexivity.
         }
         
         epose proof (HSL _ _ _ _ _ _ _ _ _ _ GH _ _ D1 D2a _ _ _ _) as CCa.
         epose proof (HSL _ _ _ _ _ _ _ _ _ _ GH _ _ D1 D2b _ _ _ _) as CCb.
         epose proof (HSL _ _ _ _ _ _ _ _ _ _ GH _ _ D1'' D2 _ _ _ _) as CC3.
         clear HSR_wb; clear HSR_bb; clear HSL.
         split_L16_IH IH.
         simpl in CCb. list_assoc_r_single_arg CCb.
         assoc_mid_hyp [AA] CCb.
         simpl in CC3. list_assoc_r_single_arg CC3.
         assoc_mid_hyp [AA] CC3.
         epose proof (HSL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CCb CC3 _ _ _ _) as CC4.
         simpl in CCa. list_assoc_r_single_arg CCa.
         assoc_mid_hyp [BB] CCa.
         rewrite (app_assoc _ Ψ2) in CC4.
         rewrite (app_assoc _ Δ1) in CC4.
         rewrite app_nil_r in CC4.
         epose proof (HSL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CC4 CCa _ _ _ _) as CC5.
         eapply derrec_contracted_nseq; [ | eapply CC5].
         repeat rewrite app_nil_r.
(*         eapply contracted_nseq_app; [eapply contracted_nseq_refl | ]. *)

         Unshelve.
         18:{ eapply Le.le_refl.  }
         16:{ eapply Le.le_refl. }
         22:{ eapply Le.le_refl.  }
         21:{ eapply Le.le_refl. }

         all : try (eassumption ||  (rewrite (app_nil_r); eassumption) ||
                    (rewrite HeqD1; simpl; eassumption) ||
                    (econstructor; [reflexivity | reflexivity | lia]) ||
                   eassumption_rem_nil).

         list_assoc_r_single.
         apply contracted_nseq_app.
         
           solve_contracted_nseq_merge_pre1.

           econstructor.
           eapply contracted_multi_seq.

 
           solve_contracted_multi.
           solve_contracted_multi.
           econstructor.

           
         
           subst. simpl.
           rewrite HdpD1''.
         eapply le_S_minus. eassumption.
         
         eapply struct_equiv_str_refl.

         eapply struct_equiv_str_comm.
         eapply struct_equiv_str_mergeR.
         eapply struct_equiv_str_refl.
         eapply HmeGH.
} 


            ++{ (* Approach 2
            Case B.d
          *)
                unf_pfall.
         epose proof (derI _ _ D1') as D1.
         Unshelve.
         3:{ existential_goal_for_ImpR_der. }

         unfold nslcext in D1.         
         solve_SR_p_ImpL_Bd HSR D1 D2a D2b Hdpa' Hdpb'.
         Unshelve. all : unfold nslcext; rem_nil; solve_eqs.
              }
              }
Qed.

(* --------------------------- *)
(* Lemma_Sixteen_SR_p_BotL *)
(* --------------------------- *)

(* Solves a goal of the form 
pf_LNSKt
    (... ++ [( ... ++ [Bot V] ++ ..., _, _)])
but apply BotL.
*)
Ltac der_BotL V :=
  assoc_mid [Bot V];
  eapply derI;
  [eapply prop; econstructor;
   eapply Sctxt_eq; [eapply BotL | reflexivity  ..]
  | econstructor ].

(* 
Approach 2
Case A.c + B.c.
 *)

Lemma Lemma_Sixteen_SR_p_BotL : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d
  (D1 : @pf_LNSKt V
         (G ++ [(Γ, Δ1 ++ A :: Δ2, d)]))
  ctxt d2 Φ1 Φ2 Ψ1 Ψ2
  (Heqconcl : nslcext ctxt d2 (Φ1 ++ Bot V :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ A :: Σ2, Π, d) :: I)
  (Hprinc : principal_not_box_R D1 A Γ Δ1 Δ2)
  (Hbox : not_box A),
  pf_LNSKt 
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HHSR_wb HHSR_bb IH;  
  split_L16_IH IH.
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d D1 ctxt d2 Φ1 Φ2 Ψ1 Ψ2 
          Heqconcl Hprinc HBox.
  unfold nslcext in *.
  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3; try contradiction; try discriminate; try der_BotL V.
  (* Impossible *)
  inversion Hprinc as [? ? ? H1 | ? ? ? H1]; inversion H1; discriminate.
Qed.

(* ------------------ *)
(* Lemma_Sixteen_SR_p *)
(* ------------------ *)

Lemma Lemma_Sixteen_SR_p : forall n m,
    SR_wb (S n, m) ->
    SR_bb (S n, m) ->
  (forall y : nat * nat, lt_lex_nat y (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y) ->
  SR_p (S n, m).
Proof.
  intros n m HSR_wb HSR_bb IH. unfold SR_p. unfold SR_p_pre.
  intros until 0. intros Hprinc Hdp Hsize Hbox Hstr Hme.
(*  inversion Hprinc. subst.
  (* A is atom *)
  +{  admit. }
  (* A is implication *)
  +{ 
*)
  remember D2 as D2'.
  remember  (H ++ [(Σ1 ++ [A] ++ Σ2, Π, d)] ++ I) as concl.
  destruct D2' as [|ps concl rl D2s]. contradiction.
  remember rl as rl'. 
  destruct rl' as [ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns ];
    remember Hns as Hns'.

  (* Box2Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA L1 L2 L3 | AA L1 L2 L3].
  (* WBox2Rs *)
  simpl in *. subst. eapply Lemma_Sixteen_SR_p_WBox2Rs; eassumption.
  (* BBox2Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_p_BBox2Rs; eassumption.

  
  (* Box1Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA d2 L1 L2 L3 L4 L5 L6 | AA d2 L1 L2 L3 L4 L5 L6].
  (* WBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_p_WBox1Rs; eassumption.

  (* BBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_p_BBox1Rs; eassumption.

  (* Box2Ls *)
  destruct Hns' as [ps c ctxt rl2];
    remember rl2 as rl2';
    destruct rl2' as [AA d2 L1 L2 L3 L4 L5 L6 | AA d2 L1 L2 L3 L4 L5 L6 ].
  (* WBox2Ls*)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_p_WBox2Ls; eassumption.
  simpl in *. subst.
  (* BBox2Ls *)
  eapply Lemma_Sixteen_SR_p_BBox2Ls; eassumption.

  (* Box1Ls *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [AA d2 L1 L2 L3 L4 L5 L6 | AA d2 L1 L2 L3 L4 L5 L6 ].
    (* WBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_p_WBox1Ls; eassumption.
   
    (* BBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_p_BBox1Ls; eassumption.

  (* EW *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [L1 L2 d2].
    (* EW_rule *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_p_EW; eassumption.

  (* prop *)
  destruct Hns' as [ps c ctxt d2 srl].
  remember srl as srl'.
  destruct srl as [ps c Φ1 Φ2 Ψ1 Ψ2 rl2].
  remember rl2 as rl2'.
  destruct rl2' as [p | AA BB | AA BB | ].
    (* Id *)
  simpl in *. subst.
  clear Hstr Hsize Hme Hdp D2s HSR_wb HSR_bb IH.
  
  eapply Lemma_Sixteen_SR_p_Id; eassumption.
 
    (* ImpR *)
    simpl in *. subst. 
    eapply Lemma_Sixteen_SR_p_ImpR; eassumption. 

    (* ImpL *) simpl in *. subst.
    eapply Lemma_Sixteen_SR_p_ImpL; eassumption.

    (* Bot  *) 
    simpl in *. subst.
    clear Hsize Hstr Hme Hdp D2s.
    eapply Lemma_Sixteen_SR_p_BotL; eassumption.
Qed.