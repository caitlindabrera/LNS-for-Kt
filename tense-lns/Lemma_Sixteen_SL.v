Add LoadPath "../general".

Require Import Lemma_Sixteen_setup.
Require Import Lemma_Sixteen_SR_wb_fwd.
Require Import Lemma_Sixteen_SR_wb_bac.
Require Import Lemma_Sixteen_SR_wb.
Require Import Lemma_Sixteen_SR_bb_fwd.
Require Import Lemma_Sixteen_SR_bb_bac.
Require Import Lemma_Sixteen_SR_bb.
Require Import Lemma_Sixteen_SR_p.

Require Import ssreflect.

Set Implicit Arguments.

  
Lemma merge_app_struct_equiv_strL : forall {V : Set} G H1 s GHs,
    merge (H1 ++ [s]) G GHs ->
    struct_equiv_str (H1 ++ [s]) G ->
    existsT2 G2 s2 GH s3,
  (G = G2 ++ [s2]) * (GHs = GH ++ [s3]) *
  (@merge V H1 G2 GH) * (struct_equiv_str H1 G2).
Proof.
  intros until 0; intros Hm Hs.
  destruct (list_nil_or_tail_singleton G); subst.
  inversion Hs; destruct H1; discriminate.
  sD. subst.
  destruct (list_nil_or_tail_singleton GHs). subst.
  inversion Hm; destruct H1; discriminate.
  sD. subst.
  pose proof (struct_equiv_str_length _ _ Hs) as Hsl.
  repeat rewrite app_length in Hsl. simpl in Hsl.
  repeat rewrite PeanoNat.Nat.add_1_r in Hsl.
  inversion Hsl.
  eapply merge_app_rev in Hm.
  destruct Hm as [Hm1 Hm2].
  repeat eexists.
  eapply Hm1.
  eapply struct_equiv_str_app_revR in Hs. eapply Hs.
  assumption.
  assumption.
  eapply merge_str_length in Hm.
  repeat rewrite app_length in Hm.
  simpl in Hm. repeat rewrite PeanoNat.Nat.add_1_r in Hm.
  inversion Hm. reflexivity.
  assumption.
Qed.


Lemma merge_app_struct_equiv_strL_explicit : forall {V : Set} G H GHs Γ Δ d,
  @merge V (H ++ [(Γ,Δ,d)]) G GHs ->
  struct_equiv_str (H ++ [(Γ,Δ,d)]) G ->
  existsT2 G' Γ' Δ' GH,
        (G = G' ++ [(Γ',Δ',d)]) *
        (GHs = GH ++ [(Γ++Γ',Δ++Δ',d)]) *
        (merge H G' GH) *
        (struct_equiv_str H G').
Proof.
  intros until 0; intros Hm Hstr.
  eapply merge_app_struct_equiv_strL in Hstr; [ |eapply Hm].
  sD; subst.
  inversion_prod.
  eapply merge_app_rev in Hm.
  sD. inversion Hm0; try discriminate.
  inv_singleton_str.
  inversion H3. inversion H4.
  subst.
  repeat eexists. eapply Hm. eapply Hstr5.
  eapply struct_equiv_str_length. assumption.
  symmetry. eapply merge_str_length. eassumption.
  eassumption.
Qed.

Lemma NSlclctxt_eq:
  forall (W : Type) (sr : rlsT (list W)) (ps : list (list W)) (c G : list W) P C,
    sr ps c -> P = (map (nslclext G) ps) -> C = (nslclext G c) ->
    nslclrule sr P C   .
Proof.
  intros. subst.
  econstructor. assumption.
Qed.

Lemma Lemma_Sixteen_SL_WBox2Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (HSR_p : SR_p_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3
  (Heqconcl : nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd)] =
             G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s : pfs_LNSKt
          [nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd); ([], [AA], fwd)]])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb HSR_p IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3
         Heqconcl D2 D1s Hdp Hsize Hstr Hme.
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).
  unfold nslclext in *.

  remember D1s as D1s'.
  pose proof Hdp as Hdp0.
  rewrite HeqD1s' in Hdp0.
  destruct (dersrec_derrec_dp D1s' eq_refl) as [D1 HdpD1];
    match goal with
    | H: S (dersrec_height D1s' + dp ?D2) <= ?m
      |- _ =>
      assert (Hdp'' : S (dp D1 + dp D2) <= m); [ rewrite HdpD1; assumption |  ];
        assert (Hdp' : dp D1 + dp D2 <= m - 1); [ lia |  ]; clear HdpD1 Hdp
    end.
  clear HeqD1s' D1s'.
  
  
  unfold nslcext in *.
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate).
  (* Produces 3 subgoals corresponding to A <> WBox AA, 
and the last subgoal corresponding to A = WBox AA. *)

  +{  unf_pfall.

      (* Bracket to be ready to apply WBox1Rs. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      list_assoc_l. assoc_mid [WBox AA].

      
      (* Apply WBox1Rs. *)

      eapply derI;
        [ eapply b2r; econstructor; list_assoc_r_single;
          simpl; eapply WBox2Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.

      unfold SL_pre in HSL; unf_pfall;

        (* Apply HSL and solve. *)
        eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      Unshelve.
      all : (subst; solve_eqs).
   }

  +{ unf_pfall.  

     (* Bracket to be ready to apply WBox1Rs. *)
     list_assoc_r_arg_derrec2_spec D2 D2'.
     list_assoc_r_single.

     
     (* Apply WBox1Rs. *)

     eapply derI;
       [ eapply b2r; econstructor; list_assoc_r_single;
         simpl; eapply WBox2Rs
       |  ].
     

     (* Prepare for next step. *)
     econstructor; [ |  econstructor];
       unfold nslclext;
       simpl;

       (* Bracket ready to apply HSL on D1. *)
       list_assoc_r_single.
     assoc_mid_loc Δ2.

     unfold SL_pre in HSL; unf_pfall;
       
       (* Apply HSL and solve. *)
       eapply HSL; try eassumption.
     erewrite <- (dp_get_D D1).
     erewrite <- (dp_get_D D2).
     eassumption.
     
     Unshelve.
     all : (subst; solve_eqs).
   } 

  +{ unf_pfall.  

     (* Bracket to be ready to apply WBox1Rs. *)
     list_assoc_r_arg_derrec2_spec D2 D2'.
     list_assoc_r_single.
     assoc_mid_loc [WBox AA].

     
     (* Apply WBox1Rs. *)

     eapply derI;
       [ eapply b2r; econstructor; 
         simpl; eapply WBox2Rs
       |  ].
     

     (* Prepare for next step. *)
     econstructor; [ |  econstructor];
       unfold nslclext;
       simpl;

       (* Bracket ready to apply HSL on D1. *)
       list_assoc_r_single.
     rewrite (app_assoc H1).
     rewrite (app_assoc _ L3).

     unfold SL_pre in HSL; unf_pfall;
       (* Apply HSL and solve. *)
       eapply HSL; try eassumption.
     erewrite <- (dp_get_D D1).
     erewrite <- (dp_get_D D2).
     eassumption.
     
     Unshelve.
     all : (subst; solve_eqs).
   } 

  +{ (* A = WBox AA *)
      
      epose proof (HSL _ _ _ _ _ _ _ _ _  _ _ _ _ (get_D D1 _) D2 _ _ _ _) as D3.
      unfold SR_wb_pre in HSR_wb.
      eapply (HSR_wb _ _ _ _ _ _ _ _ _ _ _ _ _ (derI _ _ D1s) D2 D3 _ _ _ _ _).

      Unshelve.
      2:{ rewrite app_nil_r.
          reflexivity.
      }

      simpl. rewrite <- dp_get_D. eassumption.
      eassumption.
      eassumption.
      eassumption.
      2:{ eapply b2r.

          eapply NSlclctxt_eq.
          eapply WBox2Rs.
          unfold nslclext. simpl.
          reflexivity.
          unfold nslclext. rewrite (app_cons_single ctxt).
          rewrite <- (app_nil_r Δ1) at 1.
          rewrite <- (app_nil_r (_ ++ _)).
          reflexivity.

      }

      simpl.
      eapply  princ_WB2Rs.
      econstructor ; [ | | | reflexivity | ..].

      reflexivity.
      reflexivity.
      unfold nslclext. solve_eqs.

      simpl. eassumption.
      eassumption.
      eassumption.
      eassumption.
    }
Qed.

Lemma Lemma_Sixteen_SL_BBox2Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (HSR_p : SR_p_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3
  (Heqconcl : nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac)] =
             G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s : pfs_LNSKt
          [nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac); ([], [AA], bac)]])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb HSR_p IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3
         Heqconcl D2 D1s Hdp Hsize Hstr Hme.
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).
  unfold nslclext in *.

  remember D1s as D1s'.
  pose proof Hdp as Hdp0.
  rewrite HeqD1s' in Hdp0.
  destruct (dersrec_derrec_dp D1s' eq_refl) as [D1 HdpD1];
    match goal with
    | H: S (dersrec_height D1s' + dp ?D2) <= ?m
      |- _ =>
      assert (Hdp'' : S (dp D1 + dp D2) <= m); [ rewrite HdpD1; assumption |  ];
        assert (Hdp' : dp D1 + dp D2 <= m - 1); [ lia |  ]; clear HdpD1 Hdp
    end.
  clear HeqD1s' D1s'.
  
  
  unfold nslcext in *.
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate).
  (* Produces 3 subgoals corresponding to A <> BBox AA, 
and the last subgoal corresponding to A = BBox AA. *)

  +{  
      unfold SL_pre in HSL; unf_pfall;
      (* Bracket to be ready to apply BBox1Rs. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      list_assoc_l. assoc_mid [BBox AA].

      
      (* Apply BBox1Rs. *)

      eapply derI;
        [ eapply b2r; econstructor; list_assoc_r_single;
          simpl; eapply BBox2Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.

      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      Unshelve.
      all : (subst; solve_eqs).
    }

  +{  unfold SL_pre in HSL; unf_pfall;  

      (* Bracket to be ready to apply BBox1Rs. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.

      
      (* Apply BBox1Rs. *)

      eapply derI;
        [ eapply b2r; econstructor; list_assoc_r_single;
          simpl; eapply BBox2Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.
      assoc_mid_loc Δ2.

      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      Unshelve.
      all : (subst; solve_eqs).
   } 

  +{ unfold SL_pre in HSL; unf_pfall.  

     (* Bracket to be ready to apply BBox1Rs. *)
     list_assoc_r_arg_derrec2_spec D2 D2'.
     list_assoc_r_single.
     assoc_mid_loc [BBox AA].

     
     (* Apply BBox1Rs. *)

     eapply derI;
       [ eapply b2r; econstructor; 
         simpl; eapply BBox2Rs
       |  ].
     

     (* Prepare for next step. *)
     econstructor; [ |  econstructor];
       unfold nslclext;
       simpl;

       (* Bracket ready to apply HSL on D1. *)
       list_assoc_r_single.
     rewrite (app_assoc H1).
     rewrite (app_assoc _ L3).

     (* Apply HSL and solve. *)
     eapply HSL; try eassumption.
     erewrite <- (dp_get_D D1).
     erewrite <- (dp_get_D D2).
     eassumption.
     
     Unshelve.
     all : (subst; solve_eqs).
   } 

  +{ (* A = BBox AA *)
      
      epose proof (HSL _ _ _ _ _ _ _ _ _  _ _ _ _ (get_D D1 _) D2 _ _ _ _) as D3.
      unfold SR_wb_pre in HSR_bb.
      eapply (HSR_bb _ _ _ _ _ _ _ _ _ _ _ _ _ (derI _ _ D1s) D2 D3 _ _ _ _ _).

      Unshelve.
      2:{ rewrite app_nil_r.
          reflexivity.
      }

      simpl. rewrite <- dp_get_D. eassumption.
      eassumption.
      eassumption.
      eassumption.
      2:{ eapply b2r.

          eapply NSlclctxt_eq.
          eapply BBox2Rs.
          unfold nslclext. simpl.
          reflexivity.
          unfold nslclext. rewrite (app_cons_single ctxt).
          rewrite <- (app_nil_r Δ1) at 1.
          rewrite <- (app_nil_r (_ ++ _)).
          reflexivity.

      }

      simpl.
      eapply  princ_BB2Rs.
      econstructor ; [ | | | reflexivity | ..].

      reflexivity.
      reflexivity.
      unfold nslclext. solve_eqs.

      simpl. eassumption.
      eassumption.
      eassumption.
      eassumption.
    }
Qed.

Lemma Lemma_Sixteen_SL_WBox1Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (HSR_p : SR_p_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d2); (L2, L5 ++ WBox AA :: L6, bac)] =
             G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s : pfs_LNSKt
          [nslclext ctxt [(L1, L3 ++ AA :: L4, d2); (L2, L5 ++ WBox AA :: L6, bac)];
          nslclext ctxt
            [(L1, L3 ++ L4, d2); (L2, L5 ++ WBox AA :: L6, bac); ([], [AA], fwd)]])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb HSR_p IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
         Heqconcl D2 D1s Hdp Hsize Hstr Hme.
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).
  unfold nslclext in *.

  remember D1s as D1s'.
  pose proof Hdp as Hdp0.
  rewrite HeqD1s' in Hdp0.
  
  assert (HeqD1s : dersrec_height D1s = dersrec_height D1s); [ reflexivity |  ];
    destruct (dersrec_derrec2_dp D1s HeqD1s) as [D1a [D1b HdpD1]]; clear HeqD1s;
      epose proof (Max.le_max_r _ _) as Hmax1; epose proof (Max.le_max_l _ _) as Hmax2;
        rewrite <- HdpD1 in Hmax1; rewrite <- HdpD1 in Hmax2.
  match goal with
  | H: S (dersrec_height D1s + dp ?D2) <= ?m
    |- _ => 
    assert (Hdpa'' : S (dp D1a + dp D2) <= m); [ lia |  ];
      assert (Hdpb'' : S (dp D1b + dp D2) <= m); [ lia |  ];
        assert (Hdpa' : dp D1a + dp D2 <= m - 1); [ lia |  ];
          assert (Hdpb' : dp D1b + dp D2 <= m - 1); [ lia |  ]; clear HdpD1  Hdp
                                                                      Hmax1 Hmax2
  end.
  
  unfold nslcext in *.
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate).
  (* Produces 6 subgoals corresponding to A <> WBox AA, 
and the last subgoal corresponding to A = WBox AA. *)
  +{  
      unfold SL_pre in HSL; unf_pfall.
      (* Bracket to be ready to apply WBox1Rs. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.

      
      (* Apply WBox1Rs. *)

      solve_case_G_gen_draft_setup D1a D1a' D1b D1b'.
      eapply derI;
        [ eapply b1r; econstructor; list_assoc_r_single;
          simpl; eapply WBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.

      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{  
      unfold SL_pre in HSL; unf_pfall;
      (* Bracket to be ready to apply WBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.

      
      (* Apply WBox1Ls. *)

      solve_case_G_gen_draft_setup D1a D1a' D1b D1b'.
      eapply derI;
        [ eapply b1r; econstructor; list_assoc_r_single;
          simpl; eapply WBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.
      
      rewrite (app_assoc L3);
        rewrite (app_assoc _ H3).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      rewrite (app_assoc L3).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{  
      unfold SL_pre in HSL; unf_pfall;
      (* Bracket to be ready to apply WBox1Rs. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      rewrite (app_assoc Δ1).
      
      (* Apply WBox1Rs. *)

      eapply derI;
        [ eapply b1r; econstructor;
          simpl; eapply WBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.

      rewrite (app_assoc H1).
      rewrite (app_assoc _ L4).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      rewrite (app_assoc H1).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      Unshelve.
      all : (subst; solve_eqs).

    }

  +{  
      unfold SL_pre in HSL; unf_pfall;
      (* Bracket to be ready to apply WBox1Rs. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      
      (* Apply WBox1Rs. *)

      eapply derI;
        [ eapply b1r; econstructor;
          simpl; eapply WBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.

      rewrite (app_assoc Δ1).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      Unshelve.
      all : (subst; solve_eqs).

    }  


  +{

      subst.
      eapply merge_app_struct_equiv_strL_explicit in Hme; [ | eassumption].
      sD; subst.

      unfold SL_pre in HSL; unf_pfall;
        (* Bracket to be ready to apply WBox1Rs. *)
        list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      
      (* Apply WBox1Rs. *)

      eapply derI;
        [ eapply b1r; econstructor;
          simpl; eapply WBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.
      
      rewrite (app_assoc Hme2).
      assoc_mid_loc Δ2.
      unfold SL_pre in HSL.
      
      (* Apply HSL and solve. *)
      eapply HSL; [ | eassumption | | ]. 
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      eapply struct_equiv_str_app_single. eapply Hme4.
      
      eapply merge_app;
        [eapply struct_equiv_str_length; eapply Hme4 | eassumption | ].
      assoc_mid_loc L4. rewrite (app_assoc _ L4).
      eapply merge_step; try reflexivity.
      eapply merge_nilL; reflexivity.


      rewrite (app_assoc Hme2).
      assoc_mid_loc Δ2.
      unfold SL_pre in HSL.
      
      (* Apply HSL and solve. *)
      eapply HSL; [ | eassumption | | ].
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      eapply struct_equiv_str_app_single. eapply Hme4.
      
      eapply merge_app;
        [eapply struct_equiv_str_length; eapply Hme4 | eassumption | ].
      assoc_mid_loc L4. rewrite (app_assoc _ L4).
      eapply merge_step; try reflexivity.
      eapply merge_nilL; reflexivity.
      Unshelve.
      all : (subst; solve_eqs).

    }


  +{

      subst.
      eapply merge_app_struct_equiv_strL_explicit in Hme; [ | eassumption].
      sD; subst.

      unfold SL_pre in HSL; unf_pfall;
        (* Bracket to be ready to apply WBox1Rs. *)
        list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      assoc_mid_loc [WBox AA].

      
      (* Apply WBox1Rs. *)

      eapply derI;
        [ eapply b1r; econstructor;
          simpl; eapply WBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.
      
      rewrite (app_assoc Hme2).
      rewrite (app_assoc H1).
      rewrite (app_assoc _ L6).
      unfold SL_pre in HSL.
      
      (* Apply HSL and solve. *)
      eapply HSL; [ | eassumption | | ]. 
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      eapply struct_equiv_str_app_single. eapply Hme4.
      
      eapply merge_app;
        [eapply struct_equiv_str_length; eapply Hme4 | eassumption | ].
      assoc_mid_loc L4. rewrite (app_assoc _ L4).
      eapply merge_step; try reflexivity.
      eapply merge_nilL; reflexivity.


      rewrite (app_assoc Hme2).
      rewrite (app_assoc H1).
      rewrite (app_assoc _ L6).
      unfold SL_pre in HSL.
      
      (* Apply HSL and solve. *)
      eapply HSL; [ | eassumption | | ].
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      eapply struct_equiv_str_app_single. eapply Hme4.
      
      eapply merge_app;
        [eapply struct_equiv_str_length; eapply Hme4 | eassumption | ].
      assoc_mid_loc L4. rewrite (app_assoc _ L4).
      eapply merge_step; try reflexivity.
      eapply merge_nilL; reflexivity.
      Unshelve.
      all : (subst; solve_eqs).

    }
    

  +{ (* A = WBox AA *)
      
      epose proof (HSL _ _ _ _ _ _ _ _ _  _ _ _ _ (get_D D1b _) D2 _ _ _ _) as D3.
      unfold SR_wb_pre in HSR_wb.
      eapply (HSR_wb _ _ _ _ _ _ _ _ _ _ _ _ _ (derI _ _ D1s) D2 D3 _ _ _ _ _).

      Unshelve.
      2:{ rewrite app_nil_r.
          rewrite app_cons_single.
          reflexivity.
      }

      simpl. rewrite <- dp_get_D. eassumption.
      eassumption.
      eassumption.
      eassumption.
      2:{ eapply b1r.

          eapply NSlclctxt_eq.
          eapply WBox1Rs.
          unfold nslclext. simpl.
          reflexivity.
          unfold nslclext. rewrite (app_cons_single ctxt).
          rewrite <- (app_nil_r Δ1) at 1.
          reflexivity.

      }

      simpl.
      eapply  princ_WB1Rs.
      econstructor.
      4:{  reflexivity. }

      rewrite <- app_assoc. reflexivity.
      reflexivity.
      unfold nslclext. solve_eqs.

      simpl. eassumption.
      eassumption.
      eassumption.
      eassumption.
    }
Qed.

Lemma Lemma_Sixteen_SL_BBox1Rs : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (HSR_p : SR_p_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d2); (L2, L5 ++ BBox AA :: L6, fwd)] =
             G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s : pfs_LNSKt
          [nslclext ctxt [(L1, L3 ++ AA :: L4, d2); (L2, L5 ++ BBox AA :: L6, fwd)];
          nslclext ctxt
            [(L1, L3 ++ L4, d2); (L2, L5 ++ BBox AA :: L6, fwd); ([], [AA], bac)]])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb HSR_p IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
         Heqconcl D2 D1s Hdp Hsize Hstr Hme.
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).
  unfold nslclext in *.

  remember D1s as D1s'.
  pose proof Hdp as Hdp0.
  rewrite HeqD1s' in Hdp0.
  
  assert (HeqD1s : dersrec_height D1s = dersrec_height D1s); [ reflexivity |  ];
    destruct (dersrec_derrec2_dp D1s HeqD1s) as [D1a [D1b HdpD1]]; clear HeqD1s;
      epose proof (Max.le_max_r _ _) as Hmax1; epose proof (Max.le_max_l _ _) as Hmax2;
        rewrite <- HdpD1 in Hmax1; rewrite <- HdpD1 in Hmax2.
  match goal with
  | H: S (dersrec_height D1s + dp ?D2) <= ?m
    |- _ => 
    assert (Hdpa'' : S (dp D1a + dp D2) <= m); [ lia |  ];
      assert (Hdpb'' : S (dp D1b + dp D2) <= m); [ lia |  ];
        assert (Hdpa' : dp D1a + dp D2 <= m - 1); [ lia |  ];
          assert (Hdpb' : dp D1b + dp D2 <= m - 1); [ lia |  ]; clear HdpD1  Hdp
                                                                      Hmax1 Hmax2
  end.
  
  unfold nslcext in *.
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate).
  (* Produces 6 subgoals corresponding to A <> BBox AA, 
and the last subgoal corresponding to A = BBox AA. *)
  +{  
      unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply BBox1Rs. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.

      
      (* Apply BBox1Rs. *)

      solve_case_G_gen_draft_setup D1a D1a' D1b D1b'.
      eapply derI;
        [ eapply b1r; econstructor; list_assoc_r_single;
          simpl; eapply BBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.

      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{  
      unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply BBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.

      
      (* Apply BBox1Ls. *)

      solve_case_G_gen_draft_setup D1a D1a' D1b D1b'.
      eapply derI;
        [ eapply b1r; econstructor; list_assoc_r_single;
          simpl; eapply BBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.
      
      rewrite (app_assoc L3);
        rewrite (app_assoc _ H3).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      rewrite (app_assoc L3).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{  
      unfold SL_pre in HSL; unf_pfall;
      (* Bracket to be ready to apply BBox1Rs. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      rewrite (app_assoc Δ1).
      
      (* Apply BBox1Rs. *)

      eapply derI;
        [ eapply b1r; econstructor;
          simpl; eapply BBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.

      rewrite (app_assoc H1).
      rewrite (app_assoc _ L4).

      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      rewrite (app_assoc H1).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      Unshelve.
      all : (subst; solve_eqs).

    }

  +{  
      unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply BBox1Rs. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      
      (* Apply BBox1Rs. *)

      eapply derI;
        [ eapply b1r; econstructor;
          simpl; eapply BBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.

      rewrite (app_assoc Δ1).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      Unshelve.
      all : (subst; solve_eqs).

    }  


  +{

      subst.
      eapply merge_app_struct_equiv_strL_explicit in Hme; [ | eassumption].
      sD; subst.

      unfold SL_pre in HSL; unf_pfall;

        (* Bracket to be ready to apply BBox1Rs. *)
        list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      
      (* Apply BBox1Rs. *)

      eapply derI;
        [ eapply b1r; econstructor;
          simpl; eapply BBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.
      
      rewrite (app_assoc Hme2).
      assoc_mid_loc Δ2.
      unfold SL_pre in HSL.
      
      (* Apply HSL and solve. *)
      eapply HSL; [ | eassumption | | ]. 
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      eapply struct_equiv_str_app_single. eapply Hme4.
      
      eapply merge_app;
        [eapply struct_equiv_str_length; eapply Hme4 | eassumption | ].
      assoc_mid_loc L4. rewrite (app_assoc _ L4).
      eapply merge_step; try reflexivity.
      eapply merge_nilL; reflexivity.


      rewrite (app_assoc Hme2).
      assoc_mid_loc Δ2.
      unfold SL_pre in HSL.
      
      (* Apply HSL and solve. *)
      eapply HSL; [ | eassumption | | ].
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      eapply struct_equiv_str_app_single. eapply Hme4.
      
      eapply merge_app;
        [eapply struct_equiv_str_length; eapply Hme4 | eassumption | ].
      assoc_mid_loc L4. rewrite (app_assoc _ L4).
      eapply merge_step; try reflexivity.
      eapply merge_nilL; reflexivity.
      Unshelve.
      all : (subst; solve_eqs).

    }


  +{

      subst.
      eapply merge_app_struct_equiv_strL_explicit in Hme; [ | eassumption].
      sD; subst.

      unfold SL_pre in HSL; unf_pfall;

        (* Bracket to be ready to apply BBox1Rs. *)
        list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      assoc_mid_loc [BBox AA].

      
      (* Apply BBox1Rs. *)

      eapply derI;
        [ eapply b1r; econstructor;
          simpl; eapply BBox1Rs
        |  ].
      

      (* Prepare for next step. *)
      econstructor; [ |  econstructor; [ | econstructor ]];
        unfold nslclext;
        simpl;

        (* Bracket ready to apply HSL on D1. *)
        list_assoc_r_single.
      
      rewrite (app_assoc Hme2).
      rewrite (app_assoc H1).
      rewrite (app_assoc _ L6).
      unfold SL_pre in HSL.
      
      (* Apply HSL and solve. *)
      eapply HSL; [ | eassumption | | ]. 
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      eapply struct_equiv_str_app_single. eapply Hme4.
      
      eapply merge_app;
        [eapply struct_equiv_str_length; eapply Hme4 | eassumption | ].
      assoc_mid_loc L4. rewrite (app_assoc _ L4).
      eapply merge_step; try reflexivity.
      eapply merge_nilL; reflexivity.


      rewrite (app_assoc Hme2).
      rewrite (app_assoc H1).
      rewrite (app_assoc _ L6).
      unfold SL_pre in HSL.
      
      (* Apply HSL and solve. *)
      eapply HSL; [ | eassumption | | ].
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.
      
      eapply struct_equiv_str_app_single. eapply Hme4.
      
      eapply merge_app;
        [eapply struct_equiv_str_length; eapply Hme4 | eassumption | ].
      assoc_mid_loc L4. rewrite (app_assoc _ L4).
      eapply merge_step; try reflexivity.
      eapply merge_nilL; reflexivity.
      Unshelve.
      all : (subst; solve_eqs).

    }
    

  +{ (* A = BBox AA *)
      
      epose proof (HSL _ _ _ _ _ _ _ _ _  _ _ _ _ (get_D D1b _) D2 _ _ _ _) as D3.
      unfold SR_wb_pre in HSR_wb.
      eapply (HSR_bb _ _ _ _ _ _ _ _ _ _ _ _ _ (derI _ _ D1s) D2 D3 _ _ _ _ _).

      Unshelve.
      2:{ rewrite app_nil_r.
          rewrite app_cons_single.
          reflexivity.
      }

      simpl. rewrite <- dp_get_D. eassumption.
      eassumption.
      eassumption.
      eassumption.
      2:{ eapply b1r.

          eapply NSlclctxt_eq.
          eapply BBox1Rs.
          unfold nslclext. simpl.
          reflexivity.
          unfold nslclext. rewrite (app_cons_single ctxt).
          rewrite <- (app_nil_r Δ1) at 1.
          reflexivity.

      }

      simpl.
      eapply  princ_BB1Rs.
      econstructor.
      4:{  reflexivity. }

      rewrite <- app_assoc. reflexivity.
      reflexivity.
      unfold nslclext. solve_eqs.

      simpl. eassumption.
      eassumption.
      eassumption.
      eassumption.
    }
Qed.


Lemma Lemma_Sixteen_SL_WBox2Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (HSR_p : SR_p_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
  (Heqconcl :  nslclext ctxt [(L1 ++ L2, L5, d2); (L3 ++ WBox AA :: L4, L6, bac)] =
             G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s : pfs_LNSKt
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d2)]])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb HSR_p IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
         Heqconcl D2 D1s Hdp Hsize Hstr Hme.
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).
  unfold nslclext in *.

  remember D1s as D1s'.
  pose proof Hdp as Hdp0.
  rewrite HeqD1s' in Hdp0.
  destruct (dersrec_derrec_dp D1s' eq_refl) as [D1 HdpD1];
    match goal with
    | H: S (dersrec_height D1s' + dp ?D2) <= ?m
      |- _ =>
      assert (Hdp'' : S (dp D1 + dp D2) <= m); [ rewrite HdpD1; assumption |  ];
        assert (Hdp' : dp D1 + dp D2 <= m - 1); [ lia |  ]; clear HdpD1 Hdp
    end.
  clear HeqD1s' D1s'.
  (*
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
   *)

  unfold nslcext in *.
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate).

  +{  
      unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply WBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.
      rewrite <- (app_assoc L3).

      
      (* Apply WBox1Ls. *)

      eapply derI;
        [ eapply b2l; rewrite <- app_assoc; econstructor; list_assoc_r_single;
          eapply WBox2Ls | ].

      (* Prepare for next step. *)
      econstructor; [ | econstructor ].
      unfold nslclext.
      simpl.

      (* Bracket ready to apply HSL on D1. *)
      list_assoc_r_single.
      

      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.

      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{  
      unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply WBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      rewrite (app_assoc GH).
      
      (* Apply WBox1Ls. *)

      eapply derI;
        [ eapply b2l; rewrite <- app_assoc; econstructor; list_assoc_r_single;
          eapply WBox2Ls | ].

      
      (* Prepare for next step. *)
      econstructor; [ | econstructor ].
      unfold nslclext.
      simpl.

      (* Bracket ready to apply HSL on D1. *)
      list_assoc_r_single.
      rewrite (app_assoc L1).
      rewrite (app_assoc _ L2).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.

      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{
      subst.
      eapply merge_app_struct_equiv_strL_explicit in Hme; [ | eassumption].
      sD; subst.

      
      eapply derrec_weakened_nseq.
      2:{
        eapply derI.
        eapply b2l.
        econstructor.
        eapply WBox2Ls.

        econstructor; [ | econstructor].
        unfold nslclext.
        eapply D1.
      }
      
      unfold nslclext.
      rewrite app_cons_single.
      rewrite <- app_assoc.
      rewrite <- (app_assoc Hme2).
      eapply weakened_nseq_app.
      eapply merge_weakened_nseqL. eapply Hme4.
      eassumption.
      eapply weakened_nseq_app.
      list_assoc_r_single.
      weakened_nseq_solve.
      eapply  weak_nseq_cons; [ | econstructor].
      eapply weak_seq_baseL.
      econstructor.

      eapply weakened_multi_same.
      rewrite app_cons_single.
      symmetry.
      rewrite <- app_assoc.
      rewrite <- app_assoc.
      rewrite <- (app_assoc).
      reflexivity.
    }
Qed.


Lemma Lemma_Sixteen_SL_BBox2Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (HSR_p : SR_p_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
  (Heqconcl :  nslclext ctxt [(L1 ++ L2, L5, d2); (L3 ++ BBox AA :: L4, L6, fwd)] =
             G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s : pfs_LNSKt
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d2)]])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb HSR_p IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
         Heqconcl D2 D1s Hdp Hsize Hstr Hme.
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).
  unfold nslclext in *.

  remember D1s as D1s'.
  pose proof Hdp as Hdp0.
  rewrite HeqD1s' in Hdp0.
  destruct (dersrec_derrec_dp D1s' eq_refl) as [D1 HdpD1];
    match goal with
    | H: S (dersrec_height D1s' + dp ?D2) <= ?m
      |- _ =>
      assert (Hdp'' : S (dp D1 + dp D2) <= m); [ rewrite HdpD1; assumption |  ];
        assert (Hdp' : dp D1 + dp D2 <= m - 1); [ lia |  ]; clear HdpD1 Hdp
    end.
  clear HeqD1s' D1s'.
  unfold nslcext in *.
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate).

  +{  
      unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply BBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.
      rewrite <- (app_assoc L3).
      
      (* Apply BBox1Ls. *)

      eapply derI;
        [ eapply b2l; rewrite <- app_assoc; econstructor; list_assoc_r_single;
          eapply BBox2Ls | ].

      (* Prepare for next step. *)
      econstructor; [ | econstructor ].
      unfold nslclext.
      simpl.

      (* Bracket ready to apply HSL on D1. *)
      list_assoc_r_single.
      

      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.

      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{  
      unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply BBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single.
      rewrite (app_assoc GH).
      
      (* Apply BBox1Ls. *)

      eapply derI;
        [ eapply b2l; rewrite <- app_assoc; econstructor; list_assoc_r_single;
          eapply BBox2Ls | ].

      
      (* Prepare for next step. *)
      econstructor; [ | econstructor ].
      unfold nslclext.
      simpl.

      (* Bracket ready to apply HSL on D1. *)
      list_assoc_r_single.
      rewrite (app_assoc L1).
      rewrite (app_assoc _ L2).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.

      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{
      subst.
      eapply merge_app_struct_equiv_strL_explicit in Hme; [ | eassumption].
      sD; subst.

      
      eapply derrec_weakened_nseq.
      2:{
        eapply derI.
        eapply b2l.
        econstructor.
        eapply BBox2Ls.

        econstructor; [ | econstructor].
        unfold nslclext.
        eapply D1.
      }
      
      unfold nslclext.
      rewrite app_cons_single.
      rewrite <- app_assoc.
      rewrite <- (app_assoc Hme2).
      eapply weakened_nseq_app.
      eapply merge_weakened_nseqL. eapply Hme4.
      eassumption.
      eapply weakened_nseq_app.
      list_assoc_r_single.
      weakened_nseq_solve.
      eapply  weak_nseq_cons; [ | econstructor].
      eapply weak_seq_baseL.
      econstructor.

      eapply weakened_multi_same.
      rewrite app_cons_single.
      symmetry.
      rewrite <- app_assoc.
      rewrite <- app_assoc.
      rewrite <- (app_assoc).
      reflexivity.
    }
Qed.

      
Lemma Lemma_Sixteen_SL_WBox1Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (HSR_p : SR_p_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
  (Heqconcl :  nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d2); (L3 ++ L4, L6, fwd)] =
             G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s :pfs_LNSKt
          [nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d2); (L3 ++ AA :: L4, L6, fwd)]])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb HSR_p IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
         Heqconcl D2 D1s Hdp Hsize Hstr Hme.
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).
  unfold nslclext in *.

  remember D1s as D1s'.
  pose proof Hdp as Hdp0.
  rewrite HeqD1s' in Hdp0.
  destruct (dersrec_derrec_dp D1s' eq_refl) as [D1 HdpD1];
    match goal with
    | H: S (dersrec_height D1s' + dp ?D2) <= ?m
      |- _ =>
      assert (Hdp'' : S (dp D1 + dp D2) <= m); [ rewrite HdpD1; assumption |  ];
        assert (Hdp' : dp D1 + dp D2 <= m - 1); [ lia |  ]; clear HdpD1 Hdp
    end.
  clear HeqD1s' D1s'.
  unfold nslcext in *.
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate).

  +{  
      unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply WBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.

      
      (* Apply WBox1Ls. *)

      eapply derI;
        [ eapply b1l; rewrite <- app_assoc; econstructor; list_assoc_r_single;
          eapply WBox1Ls | ].
      fold_app.

      (* Prepare for next step. *)
      econstructor; [ | econstructor ].
      unfold nslclext.
      simpl.

      (* Bracket ready to apply HSL on D1. *)
      list_assoc_r_single.

      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.

      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{  
      unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply WBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.

      
      (* Apply WBox1Ls. *)

      eapply derI;
        [ eapply b1l; rewrite <- app_assoc; econstructor; list_assoc_r_single;
          eapply WBox1Ls | ].
      fold_app.

      (* Prepare for next step. *)
      econstructor; [ | econstructor ].
      unfold nslclext.
      simpl.

      (* Bracket ready to apply HSL on D1. *)
      list_assoc_r_single.
      rewrite (app_assoc L1).
      rewrite (app_assoc _ L2).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.

      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{

      unfold SL_pre in HSL; unf_pfall;

      subst.
      eapply merge_app_struct_equiv_strL_explicit in Hme; [ | eassumption].
      sD; subst.

      (* Bracket to be ready to apply WBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.

      
      (* Apply WBox1Ls. *)

      eapply derI;
        [ eapply b1l; rewrite <- app_assoc; econstructor; list_assoc_r_single;
          eapply WBox1Ls | ].
      fold_app.

      (* Prepare for next step. *)
      econstructor; [ | econstructor ].
      unfold nslclext.
      simpl.

      (* Bracket ready to apply HSL on D1. *)
      list_assoc_r_single.
      rewrite (app_assoc Hme2).
      rewrite (app_assoc L3).
      rewrite (app_assoc _ L4).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      Unshelve.
      eassumption.

      list_assoc_r_single.
      eapply merge_app.
      eapply struct_equiv_str_length; eassumption.
      eassumption.
      eapply merge_step; try reflexivity.
      eapply merge_nilL; reflexivity.
      solve_eqs.
      
      Unshelve.
      all : (subst; solve_eqs).

    } 
Qed.

Lemma Lemma_Sixteen_SL_BBox1Ls : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (HSR_p : SR_p_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
  (Heqconcl :  nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d2); (L3 ++ L4, L6, bac)] =
             G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s :pfs_LNSKt
          [nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d2); (L3 ++ AA :: L4, L6, bac)]])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb HSR_p IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt AA L1 L2 L3 L4 L5 L6 d2
         Heqconcl D2 D1s Hdp Hsize Hstr Hme.
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).
  unfold nslclext in *.

  remember D1s as D1s'.
  pose proof Hdp as Hdp0.
  rewrite HeqD1s' in Hdp0.
  destruct (dersrec_derrec_dp D1s' eq_refl) as [D1 HdpD1];
    match goal with
    | H: S (dersrec_height D1s' + dp ?D2) <= ?m
      |- _ =>
      assert (Hdp'' : S (dp D1 + dp D2) <= m); [ rewrite HdpD1; assumption |  ];
        assert (Hdp' : dp D1 + dp D2 <= m - 1); [ lia |  ]; clear HdpD1 Hdp
    end.
  clear HeqD1s' D1s'.
  unfold nslcext in *.
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate).

  +{  
      unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply WBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.

      
      (* Apply WBox1Ls. *)

      eapply derI;
        [ eapply b1l; rewrite <- app_assoc; econstructor; list_assoc_r_single;
          eapply BBox1Ls | ].
      fold_app.

      (* Prepare for next step. *)
      econstructor; [ | econstructor ].
      unfold nslclext.
      simpl.

      (* Bracket ready to apply HSL on D1. *)
      list_assoc_r_single.

      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.

      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{  
      unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply WBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.

      
      (* Apply WBox1Ls. *)

      eapply derI;
        [ eapply b1l; rewrite <- app_assoc; econstructor; list_assoc_r_single;
          eapply BBox1Ls | ].
      fold_app.

      (* Prepare for next step. *)
      econstructor; [ | econstructor ].
      unfold nslclext.
      simpl.

      (* Bracket ready to apply HSL on D1. *)
      list_assoc_r_single.
      rewrite (app_assoc L1).
      rewrite (app_assoc _ L2).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.

      Unshelve.
      all : (subst; solve_eqs).

    } 

  +{

      unfold SL_pre in HSL; unf_pfall;

      subst.
      eapply merge_app_struct_equiv_strL_explicit in Hme; [ | eassumption].
      sD; subst.

      (* Bracket to be ready to apply WBox1Ls. *)
      list_assoc_r_arg_derrec2_spec D2 D2'.
      list_assoc_r_single. list_assoc_l.

      
      (* Apply WBox1Ls. *)

      eapply derI;
        [ eapply b1l; rewrite <- app_assoc; econstructor; list_assoc_r_single;
          eapply BBox1Ls | ].
      fold_app.

      (* Prepare for next step. *)
      econstructor; [ | econstructor ].
      unfold nslclext.
      simpl.

      (* Bracket ready to apply HSL on D1. *)
      list_assoc_r_single.
      rewrite (app_assoc Hme2).
      rewrite (app_assoc L3).
      rewrite (app_assoc _ L4).
      
      (* Apply HSL and solve. *)
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      Unshelve.
      eassumption.

      list_assoc_r_single.
      eapply merge_app.
      eapply struct_equiv_str_length; eassumption.
      eassumption.
      eapply merge_step; try reflexivity.
      eapply merge_nilL; reflexivity.
      solve_eqs.
      
      Unshelve.
      all : (subst; solve_eqs).

    } 
Qed.

Lemma Lemma_Sixteen_SL_EW : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (HSR_p : SR_p_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt L1 L2 d2
  (Heqconcl : nslclext ctxt [(L1, L2, d2)] = G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s :pfs_LNSKt [
            nslclext ctxt []])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.
  unfold nslclext in *.
  unfold nslclext in *.
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).

  remember D1s as D1s'.
  pose proof Hdp as Hdp0.
  rewrite HeqD1s' in Hdp0.
  destruct (dersrec_derrec_dp D1s' eq_refl) as [D1 HdpD1];
   match goal with
   | H: S (dersrec_height D1s' + dp ?D2) <= ?m
     |- _ =>
         assert (Hdp'' : S (dp D1 + dp D2) <= m); [ rewrite HdpD1; assumption |  ];
          assert (Hdp' : dp D1 + dp D2 <= m - 1); [ lia |  ]; clear HdpD1 Hdp
   end.
  clear HeqD1s' D1s'.
  unfold nslcext in *.
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate).

  +{
      list_assoc_l.
      eapply derI;
        [eapply nEW;
         econstructor;
         econstructor |
        ].
      unfold nslclext. simpl.
      rem_nil.
      list_assoc_r_single.
      econstructor; [ | econstructor].
      unfold SL_pre in HSL; unf_pfall;
        eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1).
      erewrite <- (dp_get_D D2).
      eassumption.
    }

  +{ eapply derrec_weakened_nseq;
         [ | eapply derI;
          [eapply nEW;
          econstructor;
          econstructor |
          eassumption] ].
     unfold nslclext.
     eapply weakened_nseq_app.
     weakened_nseq_solve2.
     eapply weakened_nseq_refl.
   } 

  Unshelve.
  all : (subst; rem_nil; solve_eqs).      
Qed.

Lemma Lemma_Sixteen_SL_Id : forall n m 
  V G Γ Δ1 Δ2 Σ1 Σ2 Π I GH H A d ctxt d2 Φ1 Φ2 Ψ1 Ψ2 p
  (HSR_p : SR_p_pre (S n) m)
  (Heqconcl : nslcext ctxt d2 (Φ1 ++ Var p :: Φ2, Ψ1 ++ Var p :: Ψ2) =
              G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s : @pfs_LNSKt V [])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m V G Γ Δ1 Δ2 Σ1 Σ2 Π I GH H A d ctxt d2 Φ1 Φ2 Ψ1 Ψ2 p HSR_p Heqconcl D2 D1s Hdp Hsize Hstr Hme.
  unfold nslcext in Heqconcl.
  app_eq_app_dest3; try contradiction; [solve_Id .. | ].
  (* A is princ in D1 *)
  rewrite <- (app_nil_r [_]).
  rewrite <- (app_assoc _ [_]).
  eremember (@derI _ _ _ _ _ _ D1s) as D1.
  eapply (HSR_p  _ _ _ _ _ _ _ _ _ _ _ _ _ D1); try eassumption.
  eapply princ_nb_Id. reflexivity.
  econstructor; try reflexivity.
  eassumption.
  rewrite HeqD1. simpl. eassumption.
  econstructor. reflexivity.
  
  Unshelve.
  solve_LNSKt_rules_Id.
Qed.

Lemma Lemma_Sixteen_SL_BotL : forall n m
    V G Γ Δ1 Δ2 Σ1 Σ2 Π I GH H A d ctxt d2 Φ1 Φ2 Ψ1 Ψ2
      (HSR_p : SR_p_pre (S n) m)
 (Heqconcl : nslcext ctxt d2 (Φ1 ++ Bot V :: Φ2, Ψ1 ++ Ψ2) =
             G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s : @pfs_LNSKt V [])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m V G Γ Δ1 Δ2 Σ1 Σ2 Π I GH H A d ctxt d2 Φ1 Φ2 Ψ1 Ψ2 HSR_p Heqconcl D2 D1s Hdp Hsize Hstr Hme.
  unfold nslcext in Heqconcl.
  app_eq_app_dest3; try contradiction;
  (list_assoc_l; der_BotL V).
Qed.

Lemma not_box_Imp : forall {V : Set} A B,
    @not_box V (Imp A B).
Proof. intros. eapply nb_Imp; reflexivity. Qed.

Lemma LNSKt_rules_nslcext_ImpR : forall {V : Set} G d Φ1 Φ2 Ψ1 Ψ2 A B,
    @LNSKt_rules V [nslcext G d (Φ1 ++ A :: Φ2, Ψ1 ++ Imp A B :: B :: Ψ2)]
                 (nslcext G d (Φ1 ++ Φ2, Ψ1 ++ Imp A B :: Ψ2)).
Proof.
  intros V G d Φ1 Φ2 Ψ1 Ψ2 A B.
  eapply prop.
  fold (map (nslcext G d) [(Φ1 ++ A :: Φ2, Ψ1 ++ Imp A B :: B :: Ψ2)]).
  econstructor.
  eapply Sctxt_eq.
  eapply ImpR.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Lemma LNSKt_rules_ImpR : forall {V : Set} G d Φ1 Φ2 Ψ1 Ψ2 A B,
    @LNSKt_rules V [G ++ [(Φ1 ++ A :: Φ2, Ψ1 ++ Imp A B :: B :: Ψ2, d)]]
                 (G ++ [(Φ1 ++ Φ2, Ψ1 ++ Imp A B :: Ψ2, d)]).
Proof.
  intros V G d Φ1 Φ2 Ψ1 Ψ2 A B.
  eapply prop.
  do 2 rewrite <- nslcext_def.
  fold (map (nslcext G d) [(Φ1 ++ A :: Φ2, Ψ1 ++ Imp A B :: B :: Ψ2)]).
  econstructor.
  eapply Sctxt_eq.
  eapply ImpR.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Lemma Lemma_Sixteen_SL_ImpR : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (HSR_p : SR_p_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt d2 Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl :nslcext ctxt d2 (Φ1 ++ Φ2, Ψ1 ++ Imp AA BB :: Ψ2) =
             G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s : pfs_LNSKt
          [nslcext ctxt d2 (Φ1 ++ AA :: Φ2, Ψ1 ++ Imp AA BB :: BB :: Ψ2)])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros.
  unfold nslclext in *.
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).

  remember D1s as D1s'.
  pose proof Hdp as Hdp0.
  rewrite HeqD1s' in Hdp0.
  destruct (dersrec_derrec_dp D1s' eq_refl) as [D1 HdpD1];
   match goal with
   | H: S (dersrec_height D1s' + dp ?D2) <= ?m
     |- _ =>
         assert (Hdp'' : S (dp D1 + dp D2) <= m); [ rewrite HdpD1; assumption |  ];
          assert (Hdp' : dp D1 + dp D2 <= m - 1); [ lia |  ]; clear HdpD1 Hdp
   end.
  clear HeqD1s' D1s'.
   unfold nslcext in *.
  app_eq_app_dest3; try contradiction; try discriminate;
    try (inversion Hbox; discriminate).

  +{  
        unfold SL_pre in HSL; unf_pfall;

      (* Bracket to be ready to apply ImpR. *)
  list_assoc_r_arg_derrec2_spec D2 D2'.
  list_assoc_r_single. list_assoc_l.
  
  (* Apply ImpR. *)
  eapply derI.
  eapply prop. econstructor.
  list_assoc_r_single.
  eapply Sctxt_eq.
  eapply ImpR.
  reflexivity.
  reflexivity.
  reflexivity.

  (* Prepare for next step. *)
  econstructor; [ | econstructor ].
  unfold nslcext.
  unfold seqext.

  (* Bracket ready to apply HSL on D1. *)
  list_assoc_r_single.

  (* Apply HSL and solve. *)
  eapply HSL; try eassumption.
  erewrite <- (dp_get_D D1).
  erewrite <- (dp_get_D D2).
  eassumption.

  Unshelve.
  all : (subst; solve_eqs).

  } 

  +{
              unfold SL_pre in HSL; unf_pfall;

  list_assoc_r_arg_derrec2_spec D2 D2'.
  list_assoc_r_single.
  eapply derI.
  eapply prop. econstructor.
  list_assoc_r_single.
  eapply Sctxt_eq.
  eapply ImpR.
  reflexivity.
  reflexivity.
  reflexivity.

  fold_app.
  econstructor; [ | econstructor ].
  unfold nslcext.
  unfold seqext.

  list_assoc_r_single.
  bracket_set_up1_pre D2' A.
  repeat rewrite <- (app_assoc Γ).

  list_assoc_l. rewrite <- (app_assoc _ Δ2).
  rewrite <- (app_assoc _ Σ1).
  eapply HSL; try eassumption.

  erewrite <- (dp_get_D D1).
  erewrite <- (dp_get_D D2).
  eassumption.

  Unshelve.
  all : (subst; solve_eqs).

  } 

    +{         unfold SL_pre in HSL; unf_pfall;

  list_assoc_r_arg_derrec2_spec D2 D2'.
  list_assoc_r_single.
  rewrite (app_assoc Δ1).
  eapply derI.
  eapply prop. econstructor.
  eapply Sctxt_eq.
  eapply ImpR.
  reflexivity.
  reflexivity.
  reflexivity.

  fold_app.
  econstructor; [ | econstructor ].
  unfold nslcext.
  unfold seqext.

  list_assoc_r_single.
  bracket_set_up1_pre D2' A.
  repeat rewrite <- (app_assoc Γ).

  list_assoc_r_single.
  rewrite (app_assoc _ [AA]).
  rewrite (app_assoc _ Φ2).
  rewrite (app_assoc H1).
  rewrite (app_assoc _ [BB]).
  rewrite (app_assoc _ Ψ2).
  rewrite <- (app_nil_r [_]).
  eapply HSL; try eassumption.
Unshelve.
  erewrite <- (dp_get_D D1).
  erewrite <- (dp_get_D D2).
  eassumption.

  Unshelve.
  all : (subst; solve_eqs).

  } 
    
  +{  (* A is Imp AA BB *)
  eapply (HSR_p _ _ _ _ _ _ _ _ _ _ _  _ _ (derI _ _ D1s) ); try eassumption.
  eapply princ_nb_ImpR; try reflexivity.
  econstructor; [ | | | reflexivity ];
  try solve [solve_eqs].
  simpl. eapply Hdp0.
  eapply not_box_Imp.

  Unshelve.
  list_assoc_r_single. simpl.
  eapply LNSKt_rules_ImpR.
    }
Qed.

Lemma Lemma_Sixteen_SL_ImpL : forall n m
  (HSR_wb : SR_wb_pre (S n) m)
  (HSR_bb : SR_bb_pre (S n) m)
  (HSR_p : SR_p_pre (S n) m)
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt d2 Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d2 (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ Ψ2) =
             G ++ (Γ, Δ1 ++ A :: Δ2, d) :: I)
  (D2 : @pf_LNSKt V
         (H ++ [(Σ1 ++ A :: Σ2, Π, d)]))
  (D1s : pfs_LNSKt
          [nslcext ctxt d2 (Φ1 ++ Imp AA BB :: BB :: Φ2, Ψ1 ++ Ψ2);
             nslcext ctxt d2 (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ AA :: Ψ2)])
  (Hdp : S (dersrec_height D1s + dp D2) <= m)
  (Hsize : fsize A <= S n)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH),
    pf_LNSKt
      (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d) :: I).
Proof.
  intros n m HSR_wb HSR_bb HSR_p IH V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d ctxt d2 Φ1 Φ2 Ψ1 Ψ2 AA BB
         Heqconcl D2 D1s Hdp Hsize Hstr Hme.
  unfold nslcext in *.
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).

  remember D1s as D1s'.
  pose proof Hdp as Hdp0.
  rewrite HeqD1s' in Hdp0.
  
  assert (HeqD1s : dersrec_height D1s = dersrec_height D1s); [ reflexivity |  ];
    destruct (dersrec_derrec2_dp D1s HeqD1s) as [D1a [D1b HdpD1]]; clear HeqD1s;
      epose proof (Max.le_max_r _ _) as Hmax1; epose proof (Max.le_max_l _ _) as Hmax2;
        rewrite <- HdpD1 in Hmax1; rewrite <- HdpD1 in Hmax2.
  match goal with
  | H: S (dersrec_height D1s + dp ?D2) <= ?m
    |- _ => 
    assert (Hdpa'' : S (dp D1a + dp D2) <= m); [ lia |  ];
      assert (Hdpb'' : S (dp D1b + dp D2) <= m); [ lia |  ];
        assert (Hdpa' : dp D1a + dp D2 <= m - 1); [ lia |  ];
          assert (Hdpb' : dp D1b + dp D2 <= m - 1); [ lia |  ]; clear HdpD1  Hdp
                                                                      Hmax1 Hmax2
  end.

  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3; try contradiction; try discriminate.

  +{ 
      solve_case_G_gen_draft_setup D1a D1a' D1b D1b'.

      eapply derI;
        [ eapply prop; econstructor; list_assoc_r_single;
          bracket_set_up1_redo_twoprem D1 D1a' D1b' (@ImpL V); simpl | ].

      eapply Sctxt_eq. eapply ImpL. reflexivity. reflexivity. reflexivity.

      econstructor; [  | econstructor; [  | econstructor ] ];
        unfold nslcext || unfold nslclext; simpl; list_assoc_r_single.

      fold_app.
      assoc_mid_loc Σ1.
      rewrite (app_assoc _ Ψ2).
      unfold SL_pre in HSL; unf_pfall;
        eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      fold_app.
      assoc_mid Σ1.
      rewrite (app_assoc H2).
      rewrite (app_assoc _ Ψ2).
      unfold SL_pre in HSL; unf_pfall;
        eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.

      Unshelve.
      all : (subst; solve_eqs).
    }
  +{ 
      solve_case_G_gen_draft_setup D1a D1a' D1b D1b'.

      eapply derI;
        [ eapply prop; econstructor; list_assoc_r_single;
          bracket_set_up1_redo_twoprem D1 D1a' D1b' (@ImpL V); simpl | ].

      eapply Sctxt_eq. eapply ImpL. reflexivity. reflexivity. reflexivity.

      econstructor; [  | econstructor; [  | econstructor ] ];
        unfold nslcext || unfold nslclext; simpl; list_assoc_r_single.

      fold_app.
      assoc_mid_loc Σ1.
      assoc_mid_loc Δ2.
      unfold SL_pre in HSL; unf_pfall;
        eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      fold_app.
      assoc_mid Σ1.
      assoc_mid_loc Δ2.
      unfold SL_pre in HSL; unf_pfall;
        eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.

      Unshelve.
      all : (subst; solve_eqs).
    }

  +{
      unfold SL_pre in HSL; unf_pfall;
      
      solve_case_G_gen_draft_setup D1a D1a' D1b D1b'.
      rewrite (app_assoc _ _ [_]).
      eapply derI;
        [ eapply prop; econstructor; list_assoc_r_single;
          bracket_set_up1_redo_twoprem D1 D1a' D1b' (@ImpL V); simpl | ].

      eapply Sctxt_eq. eapply ImpL. reflexivity. reflexivity. reflexivity.

      econstructor; [  | econstructor; [  | econstructor ] ];
        unfold nslcext || unfold nslclext; simpl; list_assoc_r_single.

      fold_app.
      assoc_mid_loc Σ1.
      assoc_mid_loc Δ2.
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1a).
      erewrite <- (dp_get_D D2).
      eassumption.

      fold_app.
      assoc_mid_loc Σ1.
      assoc_mid_loc Δ2.
      eapply HSL; try eassumption.
      erewrite <- (dp_get_D D1b).
      erewrite <- (dp_get_D D2).
      eassumption.

      Unshelve.
      all : (subst; solve_eqs).
    }
Qed.  

(* ---------------- *)
(* Lemma_Sixteen_SL *)
(* ---------------- *)

Lemma Lemma_Sixteen_SL : forall n m,
    SR_wb (S n, m) ->
    SR_bb (S n, m) ->
    SR_p (S n, m) ->
  (forall y : nat * nat, lt_lex_nat y (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y) ->
  SL (S n, m).
Proof.
  intros n m HSR_wb HSR_bb HSR_p IH. unfold SL. unfold SL_pre.
  intros until 0. intros Hdp Hsize Hstr Hme.
  remember D1 as D1'.
  remember (G ++ [(Γ, Δ1 ++ [A] ++ Δ2, d)] ++ I) as concl.
  destruct D1' as [|ps concl2 rl D1s]. contradiction.
  remember rl as rl'. 
  destruct rl' as [ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns ];
    remember Hns as Hns'.

  (* Box2Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA L1 L2 L3 | AA L1 L2 L3].
  (* WBox2Rs *)
  simpl in *. subst. eapply Lemma_Sixteen_SL_WBox2Rs; eassumption.
  (* BBox2Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SL_BBox2Rs; eassumption.
  
  (* Box1Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA d2 L1 L2 L3 L4 L5 L6 | AA d2 L1 L2 L3 L4 L5 L6].
  (* WBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SL_WBox1Rs; eassumption.

  (* BBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SL_BBox1Rs; eassumption.

  (* Box2Ls *)
  destruct Hns' as [ps c ctxt rl2];
    remember rl2 as rl2';
    destruct rl2' as [AA d2 L1 L2 L3 L4 L5 L6 | AA d2 L1 L2 L3 L4 L5 L6 ].
  (* WBox2Ls*)
  simpl in *. subst.
  eapply Lemma_Sixteen_SL_WBox2Ls; eassumption.
  
  simpl in *. subst.
  (* BBox2Ls *)
  eapply Lemma_Sixteen_SL_BBox2Ls; eassumption.

  (* Box1Ls *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [AA d2 L1 L2 L3 L4 L5 L6 | AA d2 L1 L2 L3 L4 L5 L6 ].
    (* WBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SL_WBox1Ls; eassumption.
    
    (* BBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SL_BBox1Ls; eassumption.

  (* EW *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [L1 L2 d2].
    (* EW_rule *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SL_EW; eassumption.

  (* prop *)
  destruct Hns' as [ps c ctxt d2 srl].
  remember srl as srl'.
  destruct srl as [ps c Φ1 Φ2 Ψ1 Ψ2 rl2].
  remember rl2 as rl2'.
  destruct rl2' as [p | AA BB | AA BB | ].
    (* Id *)
  simpl in *. subst. 
  eapply Lemma_Sixteen_SL_Id; eassumption.
 
    (* ImpR *)
    simpl in *. subst. 
    eapply Lemma_Sixteen_SL_ImpR; eassumption. 

    (* ImpL *) simpl in *. subst.
    eapply Lemma_Sixteen_SL_ImpL; eassumption.

    (* Bot  *) 
    simpl in *. subst.
    eapply Lemma_Sixteen_SL_BotL; eassumption.
Qed.