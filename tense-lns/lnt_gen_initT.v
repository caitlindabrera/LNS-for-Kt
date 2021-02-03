Add LoadPath "../general".
Require Import ssreflect.
 
Require Import gen genT gen_seq.
Require Import ddT.
Require Import List_lemmasT.
Require Import gen_tacs lntT lntacsT lntlsT lntbRT lntmtacsT.
Require Import lntb1LT lntb2LT.
Require Import lnt_weakeningT.
Require Import lntkt_exchT.
Require Import swappedT.
Require Import existsT. 


Inductive PropF_basic (V : Set) (A : PropF V) : Type :=
 | Var_basic p : A = Var p -> PropF_basic V A
 | Bot_basic : A = Bot V -> PropF_basic V A
 | Imp_basic B C : A = Imp B C -> PropF_basic V B -> PropF_basic V C -> PropF_basic V A.

Lemma LNSKt_gen_init_basic : forall (V : Set) A ns,
    PropF_basic V A -> can_gen_init (@LNSKt_rules V) ns A.
Proof.
  induction A; unfold can_gen_init in *;
    intros ns Hprop G s d Γ1 Γ2 Δ1 Δ2 Heq1 Heq2;
    inversion Hprop; subst; try discriminate.
  (* Id_pfc *)
  + eapply derI. apply prop.
(*    pose proof NSlcctxt_nil as H2.
    specialize (H2 _ ). *)
    apply NSlcctxt_nil.
    rewrite <- seqext_def.
    apply Sctxt_nil. apply Id_pfc.
    apply dersrec_nil.
  (* BotL_pfc *)
  + eapply derI. apply prop.
    apply NSlcctxt_nil.
    rewrite <- (app_nil_l ([Bot V] ++ Δ2)).
    rewrite <- seqext_def.
    apply Sctxt_nil.  apply BotL_pfc.
    apply dersrec_nil.
  (* Imp *)
  + eapply derI. apply prop.
    apply NSlcctxt'.
    rewrite <- (app_nil_l ([Imp A1 A2] ++ Γ2)).
    rewrite <- seqext_def. eapply Sctxt.
    (* application of ImpR_pfc *)
    apply ImpR_pfc.  apply dlCons.
    eapply derI. apply prop.
    apply NSlcctxt'.  unfold seqext. 
    rewrite <- (app_nil_l ([Imp A1 A2;A2] ++ _)).
    rewrite (app_assoc Γ1).  rewrite <- seqext_def.
    eapply Sctxt.
    (* application of ImpL_pfc *)
    apply ImpL_pfc.
    inversion H; subst.
    apply dlCons;
    unfold nslcext;
    unfold seqext;
    list_assoc_r_single.
    assoc_mid ([C]).  rewrite (app_assoc Δ1).
    eapply IHA2; auto.
    apply dlCons.
    eapply IHA1; auto.
    all : apply dersrec_nil.
Qed.

Lemma LNSKt_gen_init_basic_original : forall (V : Set),
  forall A G (d : dir) Γ1 Γ2 Δ1 Δ2,
    PropF_basic V A ->
    derrec (@LNSKt_rules V) (fun _ => False)
         (G ++ [(Γ1 ++ [A] ++ Γ2, Δ1 ++ [A] ++ Δ2, d)]).
Proof.
  induction A; intros G d Γ1 Γ2 Δ1 Δ2 Hprop;
    inversion Hprop; subst; try discriminate.
  (* Id_pfc *)
  + eapply derI.
    apply prop. apply NSlcctxt_nil.
    rewrite <- seqext_def.
    apply Sctxt_nil. apply Id_pfc.
    apply dersrec_nil.
  (* BotL_pfc *)
  + eapply derI. apply prop.
    apply NSlcctxt_nil.
    rewrite <- (app_nil_l ([Bot V] ++ Δ2)).
    rewrite <- seqext_def.
    apply Sctxt_nil.  apply BotL_pfc.
    apply dersrec_nil.
  (* Imp *)
  + eapply derI. apply prop.
    apply NSlcctxt'.
    rewrite <- (app_nil_l ([Imp A1 A2] ++ Γ2)).
    rewrite <- seqext_def. eapply Sctxt.
    (* application of ImpR_pfc *)
    apply ImpR_pfc.  apply dlCons.
    eapply derI. apply prop.
    apply NSlcctxt'.  unfold seqext. 
    rewrite <- (app_nil_l ([Imp A1 A2;A2] ++ _)).
    rewrite (app_assoc Γ1).  rewrite <- seqext_def.
    eapply Sctxt.
    (* application of ImpL_pfc *)
    apply ImpL_pfc.  apply dlCons;
    unfold nslcext;
    unfold seqext;
    list_assoc_r_single.
    assoc_mid ([A2]).  rewrite (app_assoc Δ1).
    eapply IHA2. inversion H. subst. auto.
    apply dlCons.
    eapply IHA1. inversion H. subst. auto.
    all : apply dersrec_nil.
Qed.

(* Added to lntkt_exchT.v 

Lemma Id_InT: forall {V : Set} GH Γ Δ d p,
    InT (Var p) Γ ->
    InT (Var p) Δ ->
    derrec (@LNSKt_rules V) (fun _ => False) (GH ++ [(Γ,Δ,d)]).
Proof.
  intros until 0; intros Hin1 Hin2.
  destruct (InT_seqext Hin1 Hin2) as [H1 [H2 [H3 [H4 H5]]]].
  eapply derI. eapply prop.
  econstructor.
  eapply seqrule_same.
  econstructor.
  eapply Id_pfc.
  eassumption.
  econstructor.
Qed.


Lemma BotL_InT: forall {V : Set} GH Γ Δ d,
    InT (Bot V) Γ ->
    derrec (@LNSKt_rules V) (fun _ => False) (GH ++ [(Γ,Δ,d)]).
Proof.
  intros until 0; intros Hin.
  destruct (@InT_seqextL _ _ Δ _ Hin) as [H1 [H2 H3]].
  eapply derI. eapply prop.
  econstructor.
  eapply seqrule_same.
  econstructor.
  eapply BotL_pfc.
  eassumption.
  econstructor.
Qed.
*)

Inductive gt_zero_elem {T : Type} (l : list T) :=
| gt_zeroI a l2 : l = a :: l2 -> gt_zero_elem l.

Inductive gt_one_elem {T : Type} (l : list T) :=
| gt_oneI a b l2 : l = a :: b :: l2 -> gt_one_elem l.

Lemma gt_one_elem_app_single_end : forall {T : Type} (l : list T) a,
    gt_one_elem (l ++ [a]) -> gt_zero_elem l.
Proof.
  intros T l a H.
  destruct l. inversion H. discriminate.
  econstructor. reflexivity.
Qed.

Lemma gt_one_elem_appL : forall {T : Type} (l1 l2 l3 : list T),
    gt_one_elem (l1 ++ l2) -> length l2 = length l3 -> gt_one_elem (l1 ++ l3).
Proof.
  intros T l1 l2 l3 Hgt Hlength.
  destruct l2 as [ | t l2]; destruct l3 as [ | s l3];
    inversion Hgt as [? ? ? H]; try discriminate.
  destruct l1 as [ | u l1]. discriminate.
  destruct l1 as [ | v l1]. discriminate.
  simpl in *. econstructor. reflexivity.

  destruct l1. simpl in *.
  destruct l2 as [ | t' l2]; destruct l3 as [ | s' l3];
    inversion Hgt as [? ? ? H']; try discriminate.
  econstructor. reflexivity.
  destruct l1; econstructor; reflexivity.
Qed.

Lemma gt_one_elem_end : forall {T : Type} l1 l2 a b,
    @gt_one_elem T (l1 ++ a :: b :: l2).
Proof.
  intros *. destruct l1 as [ | ? l1]. econstructor; reflexivity.
  destruct l1; econstructor; reflexivity.
Qed.

Inductive one_comp_fwd {V : Set} : forall ns, (derrec (@LNSKt_rules V) (fun _ => False) ns) -> Type :=
| one_comp_fwd_single s1 s2 D : one_comp_fwd [(s1, s2, fwd)] D
| one_comp_fwd_cons s1 s2 ds t1 t2 dt G D
  : one_comp_fwd ((s1, s2, ds) :: (t1, t2, dt) :: G) D.

Definition can_gen_init' {V : Set}
  (rules : rlsT (list (rel (list (PropF V)) * dir))) ns A :=
  forall G s (d : dir) Γ1 Γ2 Δ1 Δ2,
    ns = G ++ [(s, d)] -> s = pair (Γ1 ++ [A] ++ Γ2) (Δ1 ++ [A] ++ Δ2) ->
  (existsT2 (D : derrec (@LNSKt_rules V) (fun _ => False) ns), one_comp_fwd ns D).

Lemma existsT2_backward_chaining :
  forall {T : Type}  (P : T -> Type) (t : T),
    P t -> 
    existsT2 (t : T), P t.
Proof.
  intros T P t H. exists t. assumption.
Qed.

(*
Require Import Coq.Program.Tactics.

Lemma LNSKt_gen_init' : forall (V : Set) A ns,
    can_gen_init' (@LNSKt_rules V) ns A.
Proof.
  induction A; unfold can_gen_init' in *;
    intros ns G s d Γ1 Γ2 Δ1 Δ2 Heq1 Heq2.
  (* Id_pfc *)
  + subst.
    assert (D : derrec (LNSKt_rules (V:=V)) (fun _ : list (rel (list (PropF V)) * dir) => False)
                       (G ++ [(Γ1 ++ [Var v] ++ Γ2, Δ1 ++ [Var v] ++ Δ2, d)])).
    eapply derI. apply prop.
(*    pose proof NSlcctxt_nil as H2.
    specialize (H2 _ ). *)
    apply NSlcctxt_nil.
    rewrite <- seqext_def.
    apply Sctxt_nil. apply Id_pfc.
    apply dersrec_nil.
    eexists D.
  (* BotL_pfc *)
  + subst. eapply derI. apply prop.
    apply NSlcctxt_nil.
    rewrite <- (app_nil_l ([Bot V] ++ Δ2)).
    rewrite <- seqext_def.
    apply Sctxt_nil.  apply BotL_pfc.
    apply dersrec_nil.
  (* Imp *)
  + subst. eapply derI. apply prop.
    apply NSlcctxt'.
    rewrite <- (app_nil_l ([Imp A1 A2] ++ Γ2)).
    rewrite <- seqext_def. eapply Sctxt.
    (* application of ImpR_pfc *)
    apply ImpR_pfc.  apply dlCons.
    eapply derI. apply prop.
    apply NSlcctxt'.  unfold seqext. 
    rewrite <- (app_nil_l ([Imp A1 A2;A2] ++ _)).
    rewrite (app_assoc Γ1).  rewrite <- seqext_def.
    eapply Sctxt.
    (* application of ImpL_pfc *)
    apply ImpL_pfc.
    apply dlCons;
    unfold nslcext;
    unfold seqext;
    list_assoc_r_single.
    assoc_mid ([A2]).  rewrite (app_assoc Δ1).
    eapply IHA2; auto.
    eapply gt_one_elem_appL. eapply Hgt. reflexivity.
    apply dlCons.
    eapply IHA1; auto.
    eapply gt_one_elem_appL. eapply Hgt. reflexivity.    
    all : apply dersrec_nil.
  (* WBox *)
  + subst.
    destruct (list_nil_or_tail_singleton G) as [ | [G' [s Heq]]]; subst.
    inversion Hgt; discriminate.
    destruct d.
    ++{ eapply derI.
        eapply b2r.
        apply NSlclctxt'.
        eapply WBox2Rs.
        eapply dlCons; [ | eapply dlNil].

        eapply derI.
        eapply b1l.
        apply NSlclctxt'.
        rewrite <- (app_nil_r []).
        eapply WBox1Ls.
        eapply dlCons; [ | eapply dlNil].
        simpl.
        eapply IHA.
        unfold nslclext.
        list_assoc_r_single.
        eapply gt_one_elem_end. 
        unfold nslclext.
        rewrite cons_single.
        list_assoc_l.
        reflexivity.
        repeat erewrite app_nil_r.
        repeat erewrite app_nil_l.
        reflexivity.
      } 
    ++{ list_assoc_r_single.
        destruct s as [[s1 s2] ds].
        rewrite <- (app_nil_r s2).
        eapply derI.
        eapply b1r.
        apply NSlclctxt'.
        simpl. eapply WBox1Rs.
        eapply dlCons.
        +++{
            rewrite <- (app_nil_r s1).
        eapply derI.
        eapply b2l.
        apply NSlclctxt'.
        eapply WBox2Ls.
        eapply dlCons; [ | eapply dlNil].
        eapply IHA.
(* Fail as G' could be empty. *)        
        unfold nslclext.
        rewrite cons_single.
        list_assoc_l.
        reflexivity.
        repeat erewrite app_nil_r.
        repeat erewrite app_nil_l.
        reflexivity.
      }     
Qed.
*)


(*
Lemma LNSKt_gen_init : forall (V : Set) A ns,
    gt_one_elem ns ->
    can_gen_init (@LNSKt_rules V) ns A.
Proof.
  induction A; unfold can_gen_init in *;
    intros ns Hgt G s d Γ1 Γ2 Δ1 Δ2 Heq1 Heq2.
  (* Id_pfc *)
  + subst. eapply derI. apply prop.
(*    pose proof NSlcctxt_nil as H2.
    specialize (H2 _ ). *)
    apply NSlcctxt_nil.
    rewrite <- seqext_def.
    apply Sctxt_nil. apply Id_pfc.
    apply dersrec_nil.
  (* BotL_pfc *)
  + subst. eapply derI. apply prop.
    apply NSlcctxt_nil.
    rewrite <- (app_nil_l ([Bot V] ++ Δ2)).
    rewrite <- seqext_def.
    apply Sctxt_nil.  apply BotL_pfc.
    apply dersrec_nil.
  (* Imp *)
  + subst. eapply derI. apply prop.
    apply NSlcctxt'.
    rewrite <- (app_nil_l ([Imp A1 A2] ++ Γ2)).
    rewrite <- seqext_def. eapply Sctxt.
    (* application of ImpR_pfc *)
    apply ImpR_pfc.  apply dlCons.
    eapply derI. apply prop.
    apply NSlcctxt'.  unfold seqext. 
    rewrite <- (app_nil_l ([Imp A1 A2;A2] ++ _)).
    rewrite (app_assoc Γ1).  rewrite <- seqext_def.
    eapply Sctxt.
    (* application of ImpL_pfc *)
    apply ImpL_pfc.
    apply dlCons;
    unfold nslcext;
    unfold seqext;
    list_assoc_r_single.
    assoc_mid ([A2]).  rewrite (app_assoc Δ1).
    eapply IHA2; auto.
    eapply gt_one_elem_appL. eapply Hgt. reflexivity.
    apply dlCons.
    eapply IHA1; auto.
    eapply gt_one_elem_appL. eapply Hgt. reflexivity.    
    all : apply dersrec_nil.
  (* WBox *)
  + subst.
    destruct (list_nil_or_tail_singleton G) as [ | [G' [s Heq]]]; subst.
    inversion Hgt; discriminate.
    destruct d.
    ++{ eapply derI.
        eapply b2r.
        apply NSlclctxt'.
        eapply WBox2Rs.
        eapply dlCons; [ | eapply dlNil].

        eapply derI.
        eapply b1l.
        apply NSlclctxt'.
        rewrite <- (app_nil_r []).
        eapply WBox1Ls.
        eapply dlCons; [ | eapply dlNil].
        simpl.
        eapply IHA.
        unfold nslclext.
        list_assoc_r_single.
        eapply gt_one_elem_end. 
        unfold nslclext.
        rewrite cons_single.
        list_assoc_l.
        reflexivity.
        repeat erewrite app_nil_r.
        repeat erewrite app_nil_l.
        reflexivity.
      } 
    ++{ list_assoc_r_single.
        destruct s as [[s1 s2] ds].
        rewrite <- (app_nil_r s2).
        eapply derI.
        eapply b1r.
        apply NSlclctxt'.
        simpl. eapply WBox1Rs.
        eapply dlCons.
        +++{
            rewrite <- (app_nil_r s1).
        eapply derI.
        eapply b2l.
        apply NSlclctxt'.
        eapply WBox2Ls.
        eapply dlCons; [ | eapply dlNil].
        eapply IHA.
(* Fail as G' could be empty. *)        
        unfold nslclext.
        rewrite cons_single.
        list_assoc_l.
        reflexivity.
        repeat erewrite app_nil_r.
        repeat erewrite app_nil_l.
        reflexivity.
      }     
Qed.
*)