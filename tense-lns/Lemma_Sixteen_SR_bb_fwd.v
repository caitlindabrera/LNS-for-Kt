Add LoadPath "../general".

Require Import Lemma_Sixteen_setup.
Require Import Lemma_Sixteen_SR_wb_fwd.
Require Import Lemma_Sixteen_SR_wb_bac.
Require Import Lemma_Sixteen_SR_wb.


Set Implicit Arguments.

(* Just slightly adapted lemmas from SR_wb cases.

SR_bb_fwd, [.]^i_S   ---->   SR_wb_bac, [-]^i_S
where 
 * [.] \in { [ ], [X] }
 * i   \in { 1, 2 }
 * S   \in { L, R }
 * [-] :=  opposite of [.]

 *)

(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_WBox2Rs *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_fwd_WBox2Rs : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  (D1 : pf_LNSKt
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, fwd)]))
  ctxt AA L1 L2 L3
  (Heqconcl : nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, fwd) :: I)
  (D3 : pf_LNSKt
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], bac)]))
  (Hprinc : existsT2 Σ Π1 Π2 : list (PropF V),
             principal_BBox1Rs D1 (BBox A) Σ Π1 Π2 Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1, L2 ++ WBox AA :: L3, fwd); ([], [AA], fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros.
  get_SR_bb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslclext in *.
  destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full.

  solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' WBox2Rs fill_tac_BBox2Rs'.
  solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' WBox2Rs fill_tac_BBox2Rs.
  Unshelve. all : (subst ; solve_eqs).
Qed.

(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_BBox2Rs *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_fwd_BBox2Rs : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  (D1 : pf_LNSKt
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, fwd)]))
  ctxt AA L1 L2 L3
  (Heqconcl : nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, fwd) :: I)
  (D3 : pf_LNSKt
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], bac)]))
  (Hprinc : existsT2 Σ Π1 Π2 : list (PropF V),
             principal_BBox1Rs D1 (BBox A) Σ Π1 Π2 Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1, L2 ++ BBox AA :: L3, bac); ([], [AA], bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros.
  get_SR_bb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslclext in *.
  destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full.

  all : solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' BBox2Rs fill_tac_WBox2Rs.
  Unshelve. all : (subst ; solve_eqs).
Qed.

(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_WBox1Rs *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_fwd_WBox1Rs : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : pf_LNSKt
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, fwd)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d); (L2, L5 ++ WBox AA :: L6, bac)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, fwd) :: I)
  (D3 : pf_LNSKt
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], bac)]))
  (Hprinc : existsT2 Σ Π1 Π2 : list (PropF V),
             principal_BBox1Rs D1 (BBox A) Σ Π1 Π2 Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1, L3 ++ AA :: L4, d); (L2, L5 ++ WBox AA :: L6, bac)];
          nslclext ctxt
            [(L1, L3 ++ L4, d); (L2, L5 ++ WBox AA :: L6, bac); ([], [AA], fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  unf_pfall.
  intros n m IH;  
  split_L16_IH IH;
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt AA d L1 L2 L3 L4 L5 L6
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_bb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  unfold nslclext in *.
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
                         Hmax1 Hmax2.
  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3.

  all : solve_case_G_gen_draft2 D1 D2a D2b D2a' D2b' D3 HSR Hdpa' Hdpb' WBox1Rs fill_tac_case_G_b1r.

    Unshelve. all : ( subst; solve_eqs ).
Qed.


(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_BBox1Rs *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_fwd_BBox1Rs : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : pf_LNSKt
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, fwd)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1, L3 ++ L4, d); (L2, L5 ++ BBox AA :: L6, fwd)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, fwd) :: I)
  (D3 : pf_LNSKt
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], bac)]))
  (Hprinc : existsT2 Σ Π1 Π2 : list (PropF V),
             principal_BBox1Rs D1 (BBox A) Σ Π1 Π2 Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1, L3 ++ AA :: L4, d); (L2, L5 ++ BBox AA :: L6, fwd)];
          nslclext ctxt
            [(L1, L3 ++ L4, d); (L2, L5 ++ BBox AA :: L6, fwd); ([], [AA], bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  unf_pfall.
  intros n m IH;  
  split_L16_IH IH;
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt AA d L1 L2 L3 L4 L5 L6
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_bb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  unfold nslclext in *.
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
                         Hmax1 Hmax2.
  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3;
      subst;
      [eapply merge_app_struct_equiv_strR_explicit in Hme; [ | eassumption];
      sD; subst | | ];
      solve_case_G_gen_draft_setup D2a D2a' D2b D2b';
       fill_tac_case_G_b1r D1 D2a' D2b' BBox1Rs;
       try solve_case_G_gen_draft_finish D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb';
       solve_case_G_gen_draft_finish'' D1 D2a D2a' D2b D2b' D3 HSR Hdpa' Hdpb'.
       
    Unshelve. all : ( subst; solve_eqs ).
Qed.

(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_WBox2Ls *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_fwd_WBox2Ls : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : pf_LNSKt
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, fwd)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ L2, L5, d); (L3 ++ WBox AA :: L4, L6, bac)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, fwd) :: I)
  (D3 : pf_LNSKt
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], bac)]))
  (Hprinc : existsT2 Σ Π1 Π2 : list (PropF V),
             principal_BBox1Rs D1 (BBox A) Σ Π1 Π2 Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros.
  get_SR_bb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD; subst; simpl in Heqconcl.
  (* WBox A can't be in last component because of structural equivalence. *)
  inv_app_hd_tl_full.
    
  +{ (* WBox A not in last component. *)
      unfold nslclext in Heqconcl. tac_cons_singleton_eq_hyp.
      tac_cons_singleton.
      app_eq_app_dest3'.
      ++{ (* WBox A not in second last component. *)
          list_assoc_l. rewrite <- (app_assoc).
          eapply derI. eapply b2l.          
          econstructor. simpl. rewrite <- app_assoc. eapply WBox2Ls.

          simpl. list_assoc_r_single.
          econstructor; [ | econstructor].

          solve_HSR HSR D2 D3 Hdp'.
        }
        Unshelve. rem_nil. list_assoc_r_single. reflexivity.
      ++{ (* WBox A in second last component. *)
          (* AA left of WBox A in D2 but not adjacent. *)

          simpl. list_assoc_r_single.
          eapply derI. eapply b2l.          
          econstructor.
          rewrite (app_assoc Γ). eapply WBox2Ls.

          econstructor; [ | econstructor].

          list_assoc_r_single.
          list_assoc_r_single_arg D3.

          rewrite (app_assoc L1).
          rewrite (app_assoc (L1 ++ _)).
          solve_HSR_except_D3 HSR D2 D3 Hdp'.
          list_assoc_r_single.
          rewrite (app_assoc Γ).
          eapply LNSKt_weakL; [ | reflexivity | reflexivity].
          list_assoc_r_single.
          eapply D3.
        }
        Unshelve. rem_nil. list_assoc_r_single. reflexivity.
      ++{ (* WBox A in second last component. *)
          (* AA right of WBox A in D2. *)

          simpl. list_assoc_r_single.
          eapply derI. eapply b2l.          
          econstructor.
          rewrite (app_assoc Γ).
          rewrite (app_assoc (Γ ++ _)).
          eapply WBox2Ls.

          econstructor; [ | econstructor].

          list_assoc_r_single.
          list_assoc_r_single_arg D3.

          solve_HSR_except_D3 HSR D2 D3 Hdp'.
          list_assoc_r_single.
          rewrite (app_assoc Γ).
          rewrite (app_assoc (Γ ++ _)).
          eapply LNSKt_weakL; [ | reflexivity | reflexivity].
          list_assoc_r_single.
          eapply D3.
        }
                Unshelve. rem_nil. list_assoc_r_single. reflexivity.

      ++{ (* WBox A in second last component. *)
          (* AA left of WBox A in D2, adjacent. *)
          
          simpl. list_assoc_r_single.
          eapply derI. eapply b2l.          
          econstructor.
          rewrite (app_assoc Γ). eapply WBox2Ls.

          econstructor; [ | econstructor].

          list_assoc_r_single.
          list_assoc_r_single_arg D3.
          rewrite (app_assoc Σ1).
          
          solve_HSR_except_D3 HSR D2 D3 Hdp'.
          list_assoc_r_single.
          rewrite (app_assoc Γ).
          eapply LNSKt_weakL; [ | reflexivity | reflexivity].
          list_assoc_r_single.
          eapply D3.
        }
        Unshelve. rem_nil. list_assoc_r_single. reflexivity.
    }
Qed.


(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_BBox2Ls *)
(* ------------------------------- *)

Ltac SR_bb_fwd_BBox2Ls_snd_last_comp D2 D3 AA A HSR Hdp' :=
  app_eq_app_dest3; try contradiction;
   (eapply derI;
     [ eapply b2l; econstructor; unf_pfall; bracket_list_assoc_r_arg_derrec2 D2 AA;
        eapply BBox2Ls
     |  ]; econstructor; [  | constructor ]; unfold SR_bb_fwd_pre in HSR;
     unf_pfall; bracket_list_assoc_r_arg_derrec3 D2 (BBox A); eapply HSR;
     [ unf_pfall; prep_to_weaken_derrec D3; eapply LNSKt_weakL;
        [  | reflexivity | reflexivity ]; list_assoc_r; 
        list_assoc_r_arg D3; simpl in D3; exact D3
     | econstructor 1; eassumption
     | erewrite (dp_get_D D2) in Hdp'; eapply Hdp'
     | eassumption
     | eassumption
     | simpl; lia ]).

Ltac SR_bb_bac_BBox2Ls_not_snd_last_comp D2 D3 HSR Hdp' :=
  inv_app_hd_tl_full; tac_cons_singleton; eapply derI;
   [ eapply b2l; list_assoc_l'; eapply nslclrule_b2lrules2;
      [ reflexivity | reflexivity |  ]; list_assoc_r'; 
      eapply BBox2Ls
   |  ]; econstructor; [  | econstructor ]; unfold nslclext; list_assoc_r; 
   simpl; tac_cons_singleton; solve_HSR HSR D2 D3 Hdp'.

Lemma Lemma_Sixteen_SR_bb_fwd_BBox2Ls : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : pf_LNSKt
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, fwd)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ L2, L5, d); (L3 ++ BBox AA :: L4, L6, fwd)] =
              H ++ (Σ1 ++ BBox A :: Σ2, Π, fwd) :: I)
  (D2 : pf_LNSKt
         (nslclext ctxt [(L1 ++ L2, L5, d); (L3 ++ BBox AA :: L4, L6, fwd)]))
  (D3 : pf_LNSKt
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], bac)]))
  (Hprinc : existsT2 Σ Π1 Π2 : list (PropF V),
             principal_BBox1Rs D1 (BBox A) Σ Π1 Π2 Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1 ++ AA :: L2, L5, d)]])
  (HeqD2' : derI (nslclext ctxt [(L1 ++ L2, L5, d); (L3 ++ BBox AA :: L4, L6, fwd)])
             (b2l
                (NSlclctxt (b2lrules (V:=V)) [[(L1 ++ AA :: L2, L5, d)]]
                   [(L1 ++ L2, L5, d); (L3 ++ BBox AA :: L4, L6, fwd)] ctxt
                   (BBox2Ls AA d L1 L2 L3 L4 L5 L6))) D2s = D2)
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros n m IH V G γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1 ctxt AA d L1 L2 L3 L4 L5 L6
         Heqconcl D2kept D3 Hprinc D2s HeqD2' Hdp Hstr Hme Hsize.
  unfold nslclext in *.
  get_SR_bb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  get_SL_pre_from_IH2 IH HSL (S n) (m - 1).
  rename Heqconcl into Heqconcl'. 
  (* WBox not in last component because of structural equivalence. *)

  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD. 
  +{ subst I; simpl in Heqconcl'.
     inv_app_hd_tl_full.
     tac_cons_singleton_hyp Heqconcl.

     subst D2kept.
     tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
     app_eq_app_dest3; try contradiction.

     ++{ (* WBox A somewhere to the left of the component containing principle WBox. *)
         (*          
          SR_wb_fwd_WBox2Ls_not_snd_last_comp D2 D3 HSR Hdp'.
          *)
         pose proof (merge_app_struct_equiv_strR _ _ Hme Hstr).
         sD. subst.

         unfold LNS in *; unfold seq in *; dest_pairs.
         eapply merge_app_single in Hme; [ | eassumption].
         sD. subst.

         app_eq_app_dest3; try contradiction; try discriminate.
         list_assoc_r_single.

         (eapply derI; [
            eapply b2l;
            econstructor;
            list_assoc_r_single;
            assoc_mid [BBox AA];
            econstructor 2 | 
            econstructor; [ | econstructor];
            (eapply derrec_weakened_nseq; [ | eapply D2]);
            eapply weakened_nseq_app]).
         eapply merge_weakened_nseqR;
           eassumption. 
         weakened_nseq_solve.
       }

     ++{  (* WBox A in same component as principle WBox but to its right. *)
         pose proof (merge_app_struct_equiv_strR _ _ Hme Hstr).
         sD. subst.

         unfold LNS in *; unfold seq in *; dest_pairs.
         eapply merge_app_single in Hme; [ | eassumption].
         sD. subst.

         app_eq_app_dest3; try contradiction; try discriminate.
         list_assoc_r_single.

         (eapply derI; [
            eapply b2l;
            econstructor;
            list_assoc_r_single;
            assoc_mid [BBox AA];
            econstructor 2 | 
            econstructor; [ | econstructor];
            (eapply derrec_weakened_nseq; [ | eapply D2]);
            eapply weakened_nseq_app]).
         eapply merge_weakened_nseqR;
           eassumption. 
         weakened_nseq_solve.
       }
       
     ++{ (* WBox A is princ WBox. *)

         pose proof (merge_app_struct_equiv_strR _ _ Hme Hstr).
         sD. subst.
         unfold LNS in *; unfold seq in *; dest_pairs.
         eapply merge_app_single in Hme; [ | eassumption].
         sD. subst.

         inversion_Kt_fml. subst.
         inversion Hprinc2 as  [ ? ? ? ? ? ? ? H1 H2 H3 ].
         unfold nslclext in H2.
         simpl map in H2.
         assoc_mid_hyp [BBox B] H2.
         rewrite <- (app_nil_r) in H2.
         subst. inversion_Kt_fml. subst.
         app_eq_app_dest3; try contradiction.
         simpl in Hdp''.
         simpl in Hdp'.    

         epose proof (dersrec_derrec2_dp D0 eq_refl) as [HD01 [HD02 HD03]].
         unfold SL_pre in HSL.
         epose proof (HSL _ _ _ _ _ _ _ _ _ _
                          (X1 ++ [(Hprinc ++ L1 ++ L2, ((Hprinc0 ++ [B]) ++ Hprinc1) ++ L5, d0)])
                          _ _ HD01 (derI ((ctxt ++ [(L1 ++ L2, L5, d0)]) ++ [(L3 ++ BBox B :: L4, Π, fwd)]) _ (dlCons D2 (dlNil _ _))) _ _ _ _) as D4.

         
         list_assoc_r_arg D4. simpl in D4.
         clear HSL.
         get_SL_pre_from_IH1 IH HSL (n) (plus (dp D4) (dp D2)).
         edestruct (@merge_ex V).
         eapply struct_equiv_str_weak.
         eapply struct_equiv_str_comm.
         eapply struct_equiv_str_mergeR.
         eapply X5. eassumption.

         epose proof (HSL _ _ _ _ _ _ _ _ _ _ x _ _ D4 D2 _ _ _ _) as D5.

         eapply derrec_contracted_nseq; [ | eapply D5].

         
         list_assoc_r. simpl.
         eapply contracted_nseq_app.

         eapply merge_merge_contractedR.
         eassumption. eassumption.

         econstructor.
         eapply cont_seq_stepL; [ | eapply cont_seq_baseR]; econstructor.
         eapply contracted_multi_L.
         assert (contracted_multi ((L1 ++ L2) ++ (L1 ++ L2)) (L1 ++ L2)) as Hass.
         eapply contracted_multi_double.
         list_assoc_r_arg Hass.
         eassumption.
         eapply contracted_multi_L.
         eapply contracted_multi_L.
         eapply contracted_multi_double.

         eapply contracted_nseq_refl.
         

         Unshelve.
         eapply b2l.
         change [ctxt ++ [(L1 ++ B :: L2, L5, d0)]] with (map (nslclext ctxt) [[(L1 ++ B :: L2, L5, d0)]]).
         rewrite <- app_assoc.
         econstructor.
         eapply BBox2Ls.
         
         
         simpl. unfold dp in Hdp''.
         rewrite Max.max_0_r.
         assert ( S (( Nat.max (dp HD01) (dp HD02)) + S (derrec_height D2)) <= m) as Hass2. rewrite <- HD03. assumption.
         assert (forall a1 a2, S a1 <= a2 -> a1 <= a2 - 1) as Hass3.
         intros. lia.
         eapply Hass3 in Hass2.
         assert (forall a1 a2 a3 a4, a1 + a2 <= a3 -> a4 <= a1 -> a4 + a2 <= a3) as Hass4. intros. lia.
         eapply Hass4. eapply Hass2.
         eapply PeanoNat.Nat.le_max_l.
         
         simpl. lia. 

         eapply struct_equiv_str_app_single.
         assumption.
         
         eapply merge_app_single_rev. assumption. eassumption. 

         eapply le_n.

         eassumption.

         eapply struct_equiv_str_comm.
         eapply struct_equiv_str_mergeR.
         eassumption. eassumption.

         eassumption.
       }
   }
   
  +{ unf_pfall.
     subst; simpl in Heqconcl'.
     inv_app_hd_tl_full.
     inv_app_hd_tl_full.
     tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
     eapply partition_singleton_app in Heqconcl'. sD; subst.
     ++{ (* WBox A in snd last component *)
         SR_bb_fwd_BBox2Ls_snd_last_comp D2 D3 AA A HSR Hdp'.
       }
     ++{
         SR_bb_bac_BBox2Ls_not_snd_last_comp D2 D3 HSR Hdp'.
       }
   }
   Unshelve. all : try solve [subst; solve_eqs].
Qed.   

(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_WBox1Ls *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_fwd_WBox1Ls : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : pf_LNSKt
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, fwd)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d); (L3 ++ L4, L6, fwd)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, fwd) :: I)
  (D3 : pf_LNSKt
               (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], bac)]))
  (Hprinc : existsT2 Σ Π1 Π2 : list (PropF V),
             principal_BBox1Rs D1 (BBox A) Σ Π1 Π2 Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1 ++ WBox AA :: L2, L5, d); (L3 ++ AA :: L4, L6, fwd)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  unf_pfall.
  intros.
  get_SR_bb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslclext in *.
  destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full;
  app_eq_app_dest3; try contradiction; try discriminate;
    subst;
     try (eapply merge_app_struct_equiv_strR_explicit in Hme; [ | eassumption]);
     sD; subst;
  
  (solve [solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' WBox1Ls fill_tac_BBox1Ls]) ||
     (solve [solve_case_F_gen_draft3 D1 D2 D2' D3 HSR Hdp' WBox1Ls fill_tac_BBox1Ls]).
  
  Unshelve. all : (subst ; solve_eqs).
Qed.

(* ------------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_BBox1Ls *)
(* ------------------------------- *)

Lemma Lemma_Sixteen_SR_bb_fwd_BBox1Ls : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A 
  (D1 : pf_LNSKt
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, fwd)]))
  ctxt AA d L1 L2 L3 L4 L5 L6
  (Heqconcl : nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d); (L3 ++ L4, L6, bac)] =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, fwd) :: I)
  (D3 : pf_LNSKt
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], bac)]))
  (Hprinc : existsT2 Σ Π1 Π2 : list (PropF V),
             principal_BBox1Rs D1 (BBox A) Σ Π1 Π2 Γ Δ1 Δ2)
  (D2s : pfs_LNSKt
          [nslclext ctxt [(L1 ++ BBox AA :: L2, L5, d); (L3 ++ AA :: L4, L6, bac)]])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros n m IH;  
  split_L16_IH IH;
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A D1  ctxt AA d L1 L2 L3 L4 L5 L6
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_bb_fwd_pre_from_IH IH HSR (S n) (m - 1).
  unfold nslclext in *.
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl.
  +{ (* WBox A in last component. *)
      (* Therefore not principal. To be treated in CASE (F). *)

      tac_cons_singleton_hyp Heqconcl.
      app_eq_app_dest3; try contradiction.
    }
  +{ tac_cons_singleton_hyp Heqconcl.
     app_eq_app_dest3; try contradiction.

     ++{ (* WBox A somewhere to the left of the component containing principle WBox. *)
         solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' BBox1Ls fill_tac_WBox1Ls.
       } 
     ++{ (* WBox A in same component as principle WBox but to its right. *)
         solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' BBox1Ls fill_tac_WBox1Ls.
       }
     ++{ (* WBox A in same component as principle WBox but to its left. *)
         unf_pfall.
         solve_case_F_gen_draft_setup D2 D2'.
         fill_tac_WBox1Ls D2' BBox1Ls. 
   solve_case_F_gen_draft_finish D1 D2 D2' D3 HSR Hdp'.
(*         solve_case_F_gen_draft2 D1 D2 D2' D3 HSR Hdp' WBox1Ls fill_tac_WBox1Ls. *)
       }

       Unshelve. all : (subst; solve_eqs).
        ++{ (* WBox A is princ WBox. *)
         (* Case could be cleaned up but low priority since it is a once-off proof. *)
         inv_singleton_str.
         unfold SR_bb_pre in HSR_bb.
         unfold SL_pre in HSL.

         edestruct (derrec_dp_same2 D2) as [D2' HdpD2'].
         repeat rewrite app_nil_r.
         list_assoc_r_single.
         reflexivity.
         rewrite HdpD2' in Hdp', Hdp''.
         clear HdpD2' D2.

         edestruct (@merge_ex V GH GH) as [XX HmergeXX].
         eapply struct_equiv_weak_refl.
         
         epose proof (@HSR_bb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D1 D2' D3  _ _ _ _ _ ) as D6.
         rewrite (app_assoc GH) in D6.
         
         list_assoc_l'_arg D3.
         rewrite <- (app_nil_r [([],_,_)]) in D3.
         change ([A]) with ([] ++ [A] ++ []) in D3.
         
         epose proof (@HSL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D3 D6 _ _ _ _) as D7.
         repeat rewrite app_nil_r in D7.
         simpl in D7.
         list_assoc_r_single.
         
         eapply derrec_contracted_nseq.
         list_assoc_l.
         eapply contracted_nseq_app.
         eapply contracted_nseq_app.
         eapply merge_contracted_nseq. eapply HmergeXX.
         eapply contracted_nseq_refl.
         eapply contracted_nseq_refl.
         
         eapply derrec_contracted_nseq;
           [ | eapply D7 ].
         eapply contracted_nseq_app.
         eapply contracted_nseq_app.
         eapply contracted_nseq_refl.
         list_assoc_r. eapply contracted_nseq_single.
         eapply contracted_nseq_refl.
         Unshelve.
         exact (S n). 
         exact (m-1).
         econstructor 2; try reflexivity. lia.
         econstructor 1. eassumption.
         eassumption.
         assumption.
         assumption.
         simpl. lia.
         exact n.
         exact (plus (dp D3) (dp D6)).
         econstructor; try reflexivity. lia.
         eapply PeanoNat.Nat.le_refl.
         assumption.
         list_assoc_r.
         eapply struct_equiv_str_refl.
         eapply merge_app. reflexivity.
         assumption.
         list_assoc_r.
         econstructor 3; try reflexivity.
         econstructor; reflexivity.
         solve_eqs.
          }         
} 
Qed.

(* -------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_EW *)
(* -------------------------- *)

Lemma Lemma_Sixteen_SR_bb_fwd_EW : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A
  (D1 : pf_LNSKt
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, fwd)]))
  ctxt L1 L2 d
  (Heqconcl : nslclext ctxt [(L1, L2, d)] = H ++ (Σ1 ++ BBox A :: Σ2, Π, fwd) :: I)
  (D3 : pf_LNSKt
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd); ([], [A], bac)]))
  (Hprinc : existsT2 Σ Π1 Π2 : list (PropF V),
             principal_BBox1Rs D1 (BBox A) Σ Π1 Π2 Γ Δ1 Δ2)
  (D2s : pfs_LNSKt 
          [nslclext ctxt []])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, fwd) :: I).
Proof.
  intros.
  unfold nslclext in *.
  get_SR_bb_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.

  destruct (list_nil_or_tail_singleton I) as [ | HI]; sD; subst; simpl in Heqconcl.

  +{ (* WBox A in last component. *)
      inv_app_hd_tl_full.
      eapply derI.
      eapply nEW.
      econstructor.      
      econstructor.

      simpl. econstructor; [| econstructor].
      unfold nslclext. rewrite app_nil_r.

      eapply derrec_struct_equiv_mergeR.
      eassumption. eassumption.
      eapply (@get_D _ _ _ _ _ D2).
      repeat rewrite app_nil_r; solve_eqs.      
    }
  +{ (* WBox A not in last component. *)
      inv_app_hd_tl_full.
      tac_cons_singleton.
      list_assoc_l.
      eapply external_weakeningR.
      list_assoc_r. simpl.
      solve_HSR HSR D2 D3 Hdp'.
    }
    Unshelve. repeat rewrite app_nil_r; solve_eqs.
Qed.


(* -------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_Id *)
(* -------------------------- *)


Lemma Lemma_Sixteen_SR_bb_Id : forall {V : Set} GH H I ctxt d d2 Γ Σ1 Σ2 Δ1 Δ2 Π Φ1 Φ2 Ψ1 Ψ2 p A,
    (nslcext ctxt d (Φ1 ++ Var p :: Φ2, Ψ1 ++ Var p :: Ψ2) =
     H ++ (Σ1 ++ [BBox A] ++ Σ2, Π, d2) :: I) ->
    @pf_LNSKt V
           (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2) :: I).
Proof.
  intros until 0; intros Heqconcl.
  unfold nslcext in Heqconcl.
  apply partition_singleton_app in Heqconcl.
  destruct Heqconcl as [[[HH1 HH2] HH3] | [HH1 [HH2 HH3]]].
  subst.
  inversion HH3. subst.
  assert ((Var p) <> (BBox A)) as Hneq.
  intros. discriminate.
  epose proof (InT_singleton_mid _ _ _ _ Hneq H1) as Hin.
  destruct Hin as [Hin | Hin].
  epose proof (@Id_InT V _ _ _ _ p) as DD.
  eapply DD.
  eapply InT_appR. apply InT_appL. assumption.
  eapply InT_appR. apply InT_appR.
  eapply InT_appR. econstructor. reflexivity.
  epose proof (@Id_InT V _ _ _ _ p) as DD.
  eapply DD.
  eapply InT_appR. apply InT_appR. assumption.
  eapply InT_appR. apply InT_appR.
  eapply InT_appR. econstructor. reflexivity.

  subst.  
  eapply derI.  
  eapply prop.
  rewrite cons_singleton. repeat rewrite app_assoc.
  econstructor.
  eapply seqrule_same.
  econstructor. apply Id.
  reflexivity. econstructor.
Qed.

(* ---------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_ImpR *)
(* ---------------------------- *)


Lemma Lemma_Sixteen_SR_bb_fwd_ImpR : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d2
  (D1 : pf_LNSKt
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, d2)]))
  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d (Φ1 ++ Φ2, Ψ1 ++ Imp AA BB :: Ψ2) =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, d2) :: I)
  (D3 : pf_LNSKt
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2); ([], [A], bac)]))
  (Hprinc : {Σ : list (PropF V) &
           {Π1 : list (PropF V) &
           {Π2 : list (PropF V) & principal_BBox1Rs D1 (BBox A) Σ Π1 Π2 Γ Δ1 Δ2}}})
  (D2s : pfs_LNSKt
          [nslcext ctxt d (Φ1 ++ AA :: Φ2, Ψ1 ++ Imp AA BB :: BB :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2) :: I).
Proof.
  unf_pfall.
  intros.
  get_SR_bb_from_IH IH HSR (S n) (m - 1).
  tfm_dersrec_derrec_dp D2s D2 Hdp HdpD2 Hdp'' Hdp'.
  unfold nslcext in *.
  (destruct (list_nil_or_tail_singleton I); sD; subst;
    inv_app_hd_tl_full;              
    [app_eq_app_dest3; try contradiction; try discriminate | ]);
    (solve_case_F_gen_draft_setup D2 D2';
  fill_tac_ImpR D2' (@ImpR V);
  econstructor; [  | econstructor ]; unfold nslcext || unfold nslclext; simpl;
   list_assoc_r_single; bracket_set_up2 D1 D2';
   solve_HSR_except_D3 HSR D2 D3 Hdp'; solve_D3_weakened D3).

       Unshelve. all : (subst ; solve_eqs).
Qed.


(* ---------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_ImpL *)
(* ---------------------------- *)

Lemma Lemma_Sixteen_SR_bb_fwd_ImpL : forall n m
  (IH : forall y : nat * nat, y << (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y)
  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d2
  (D1 : pf_LNSKt
         (G ++ [(Γ, Δ1 ++ BBox A :: Δ2, d2)]))
  ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
  (Heqconcl : nslcext ctxt d (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ BBox A :: Σ2, Π, d2) :: I)
  (D3 : pf_LNSKt
         (GH ++ [(Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2); ([], [A], bac)]))
  (Hprinc : {Σ : list (PropF V) &
           {Π1 : list (PropF V) &
           {Π2 : list (PropF V) & principal_BBox1Rs D1 (BBox A) Σ Π1 Π2 Γ Δ1 Δ2}}})
  (D2s : pfs_LNSKt
          [nslcext ctxt d (Φ1 ++ Imp AA BB :: BB :: Φ2, Ψ1 ++ Ψ2);
          nslcext ctxt d (Φ1 ++ Imp AA BB :: Φ2, Ψ1 ++ AA :: Ψ2)])
  (Hdp : dp D1 + S (dersrec_height D2s) <= m)
  (Hstr : struct_equiv_str G H)
  (Hme : merge G H GH)
  (Hsize : fsize A <= n),
  pf_LNSKt
         (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d2) :: I).
Proof.
  intros n m IH;  
    split_L16_IH IH.
  intros  V G Γ Δ1 Δ2 H Σ1 Σ2 Π I GH A d2 D1 ctxt d Φ1 Φ2 Ψ1 Ψ2 AA BB
          Heqconcl D3 Hprinc D2s Hdp Hstr Hme Hsize.
  get_SR_bb_from_IH IH HSR (S n) (m - 1).
  unfold nslclext in *.
  tfm_dersrec_derrec2_dp D2s D2 Hdp HdpD2 Hdpa'' Hdpb'' Hdpa' Hdpb' HeqD2s
                         Hmax1 Hmax2.

  unfold nslcext in *.
  destruct (list_nil_or_tail_singleton I) as [ | Hl2]; sD; subst; simpl in Heqconcl;
    app_eq_app_dest3; try contradiction; try discriminate.
  +{ unf_pfall.
     solve_case_G_gen_draft_setup D2a D2a' D2b D2b'.

     eapply derI;
       [ eapply prop; econstructor; list_assoc_r_single;
         bracket_set_up1_redo_twoprem D1 D2a' D2b' (@ImpL V); simpl | ].

     eapply Sctxt_eq. eapply ImpL. reflexivity. reflexivity. reflexivity.

     

     econstructor; [  | econstructor; [  | econstructor ] ];
       unfold nslcext || unfold nslclext; simpl; list_assoc_r_single.

     
     solve_HSR_except_D3' HSR D2a D3 Hdpa'.
     solve_D3_weakened D3. struct_equiv_str_solve_primitive.
     solve_HSR_except_D3' HSR D2b D3 Hdpb'.
     solve_D3_weakened D3. struct_equiv_str_solve_primitive.
   }
   Unshelve.
   all : try solve [subst; solve_eqs].
  +{ 
      unf_pfall.
      solve_case_G_gen_draft_setup D2a D2a' D2b D2b'.

      eapply derI;
        [ eapply prop; econstructor; list_assoc_r_single;
          bracket_set_up1_redo_twoprem D1 D2a' D2b' (@ImpL V); simpl | ].

      eapply Sctxt_eq. eapply ImpL.
      
      reflexivity.
      reflexivity.
      reflexivity.

      econstructor; [  | econstructor; [  | econstructor ] ];
        unfold nslcext || unfold nslclext; unfold seqext;
          list_assoc_r_single.

      assoc_mid_loc H1. rewrite <- (app_assoc Γ).
      rewrite (app_assoc _ H1).

      solve_HSR_except_D3' HSR D2a D3 Hdpa'.
      solve_D3_weakened D3. struct_equiv_str_solve_primitive.
      
      assoc_mid_loc H1. rewrite <- (app_assoc Γ).
      rewrite (app_assoc _ H1).

      solve_HSR_except_D3' HSR D2b D3 Hdpb'.
      solve_D3_weakened D3. struct_equiv_str_solve_primitive.
    }

    Unshelve.
   all : (subst; solve_eqs).

  +{ 
      unf_pfall.
      solve_case_G_gen_draft_setup D2a D2a' D2b D2b'.
      rewrite (app_assoc _ Hl2).

      eapply derI;
        [ eapply prop; econstructor; list_assoc_r_single;
          bracket_set_up1_redo_twoprem D1 D2a' D2b' (@ImpL V); simpl | ].

      eapply Sctxt_eq. eapply ImpL.
      
      reflexivity.
      reflexivity.
      reflexivity.

      econstructor; [  | econstructor; [  | econstructor ] ];
        unfold nslcext || unfold nslclext; unfold seqext;
          list_assoc_r_single.


      solve_HSR_except_D3' HSR D2a D3 Hdpa'.
      solve_D3_weakened D3. struct_equiv_str_solve_primitive.

      solve_HSR_except_D3' HSR D2b D3 Hdpb'.
      solve_D3_weakened D3. struct_equiv_str_solve_primitive.
    } 
    Unshelve.
   all : (subst; solve_eqs).
Qed.


(* ---------------------------- *)
(* Lemma_Sixteen_SR_bb_fwd_BotL *)
(* ---------------------------- *)

Lemma Lemma_Sixteen_SR_bb_BotL : forall {V : Set} GH H I ctxt d d2 d3 Γ Σ1 Σ2 Δ1 Δ2 Π Φ1 Φ2 Ψ1 Ψ2 A,
 nslcext ctxt d (Φ1 ++ Bot V :: Φ2, Ψ1 ++ Ψ2) =
             H ++ (Σ1 ++ [BBox A] ++ Σ2, Π, d2) :: I ->
  pf_LNSKt
    (GH ++ (Γ ++ Σ1 ++ Σ2, Δ1 ++ Δ2 ++ Π, d3) :: I).
Proof.
  intros until 0; intros Heqconcl.
  unfold nslcext in Heqconcl.
  apply partition_singleton_app in Heqconcl.
  destruct Heqconcl as [[[HH1 HH2] HH3] | [HH1 [HH2 HH3]]].
  subst.
  inversion HH3. subst.
  assert ((Bot V) <> (BBox A)) as Hneq. intros; discriminate.
  epose proof (InT_singleton_mid _ _ _ _ Hneq H1) as Hin.
  destruct Hin as [Hin | Hin].
  epose proof (@BotL_InT V _ _ _ _) as DD.
  eapply DD.
  eapply InT_appR. eapply InT_appL. assumption.
  epose proof (@BotL_InT V _ _ _ _) as DD.
  eapply DD.
  eapply InT_appR. apply InT_appR. assumption.

  subst.  
  eapply derI.  
  eapply prop.
  rewrite cons_singleton. repeat rewrite app_assoc.
  econstructor.
  eapply seqrule_same.
  econstructor. apply BotL.
  reflexivity. econstructor.
Qed.


(* ----------------------- *)
(* Lemma_Sixteen_SR_bb_fwd *)
(* ----------------------- *)


Lemma Lemma_Sixteen_SR_bb_fwd : forall n m,
  (forall y : nat * nat, lt_lex_nat y (S n, m) -> SR_wb y * SR_bb y * SR_p y * SL y) ->
  SR_bb_fwd (S n, m).
Proof.
  intros n m IH. unfold SR_bb_fwd. unfold SR_bb_fwd_pre.
  intros until 0. intros D3 Hprinc Hdp Hstr Hme Hsize.
  eapply principal_BBR_fwd in Hprinc ; [ | reflexivity].
  simpl in Hsize. apply le_S_n in Hsize.

  remember D2 as D2'.
  remember  (H ++ [(Σ1 ++ [BBox A] ++ Σ2, Π, fwd)] ++ I) as concl.
  destruct D2' as [|ps concl rl D2s]. contradiction.
  remember rl as rl'. 
  destruct rl' as [ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns | ps c Hns ];
    remember Hns as Hns'.

  (* Box2Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA L1 L2 L3 | AA L1 L2 L3].
  (* WBox2Rs *)
  simpl in *. subst. eapply Lemma_Sixteen_SR_bb_fwd_WBox2Rs; eassumption.
  (* BBox2Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_bb_fwd_BBox2Rs; try eassumption.

  
  (* Box1Rs *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';
  destruct rl2' as [AA d L1 L2 L3 L4 L5 L6 | AA d L1 L2 L3 L4 L5 L6].
  (* WBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_bb_fwd_WBox1Rs; eassumption.

  (* BBox1Rs *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_bb_fwd_BBox1Rs; try eassumption.

  (* Box2Ls *)
  destruct Hns' as [ps c ctxt rl2];
    remember rl2 as rl2';
    destruct rl2' as [AA d L1 L2 L3 L4 L5 L6 | AA d L1 L2 L3 L4 L5 L6 ].
  (* WBox2Ls *)
  simpl in *. subst.
  eapply Lemma_Sixteen_SR_bb_fwd_WBox2Ls; eassumption.
  simpl in *. subst.
  (* BBox2Ls *)
  eapply Lemma_Sixteen_SR_bb_fwd_BBox2Ls; try eassumption. reflexivity.

  (* Box1Ls *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [AA d L1 L2 L3 L4 L5 L6 | AA d L1 L2 L3 L4 L5 L6 ].
    (* WBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_bb_fwd_WBox1Ls; eassumption.
   
    (* BBox1Ls *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_bb_fwd_BBox1Ls; eassumption.

  (* EW *)
  destruct Hns' as [ps c ctxt rl2];
  remember rl2 as rl2';  
  destruct rl2' as [L1 L2 d].
    (* EW_rule *)
    simpl in *. subst.
    eapply Lemma_Sixteen_SR_bb_fwd_EW; eassumption.

  (* prop *)
  destruct Hns' as [ps c ctxt d srl].
  remember srl as srl'.
  destruct srl as [ps c Φ1 Φ2 Ψ1 Ψ2 rl2].
  remember rl2 as rl2'.
  destruct rl2' as [p | AA BB | AA BB | ].
    (* Id *)
    simpl in *. subst.
    clear Hsize D3 Hme Hdp D2s Hprinc.
    clear D1 IH.
    eapply Lemma_Sixteen_SR_bb_Id. eassumption.
 
    (* ImpR *)
    simpl in *. subst. 
    eapply Lemma_Sixteen_SR_bb_fwd_ImpR; eassumption. 

    (* ImpL *) simpl in *. subst.
    eapply Lemma_Sixteen_SR_bb_fwd_ImpL; eassumption.

    (* Bot  *) 
    simpl in *. subst.
    clear Hsize D3 Hme Hdp D2s Hprinc.
    clear D1 IH.
    eapply Lemma_Sixteen_SR_bb_BotL. eassumption.
Qed.
