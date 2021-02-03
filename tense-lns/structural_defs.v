Add LoadPath "../general".

Require Import require_general.
Require Import LNS.
Require Import ssreflect.

Set Implicit Arguments.


Definition can_gen_moveL {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ1 Γ2 Γ3 (Q : PropF V) Δ,
    ns = G ++ (s, d) :: K -> s = pair (Γ1 ++ Q :: Γ2 ++ Γ3) Δ ->
    pf rules (G ++ (pair (Γ1 ++ Γ2 ++ Q :: Γ3) Δ, d) ::K).

Definition can_gen_moveR {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Δ1 Δ2 Δ3 (Q : PropF V) Γ,
    ns = G ++ (s, d) :: K -> s = pair Γ (Δ1 ++ Q :: Δ2 ++ Δ3) ->
    pf rules (G ++ (pair Γ (Δ1 ++ Δ2 ++ Q :: Δ3), d) :: K).

Definition can_gen_swapL {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ1 Γ2 Γ3 Γ4 Δ,
    ns = G ++ (s, d) :: K -> s = pair (Γ1 ++ Γ2 ++ Γ3 ++ Γ4) Δ ->
    pf rules (G ++ (pair (Γ1 ++ Γ3 ++ Γ2 ++ Γ4) Δ, d) :: K).

Definition can_gen_swapR {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Δ1 Δ2 Δ3 Δ4 Γ,
    ns = G ++ (s, d) :: K -> s = pair Γ (Δ1 ++ Δ2 ++ Δ3 ++ Δ4) ->
    pf rules (G ++ (pair Γ (Δ1 ++ Δ3 ++ Δ2 ++ Δ4), d) :: K).

(* alternative definition of can_gen_swapL(R) in terms of swapped *)
Lemma can_gen_swapL_def': forall {V : Set} 
                                 (rules : rlsT (@LNS V)) ns,
    iffT (can_gen_swapL rules ns)
         (forall G K s Γ Δ Γ' d, 
             swapped Γ Γ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
             pf rules (G ++ (pair Γ' Δ, d) :: K)).
Proof.  intros.  unfold iffT.  split ; intros. 
        destruct H. subst. unfold can_gen_swapL in X.
        eapply X. reflexivity.  reflexivity.
        unfold can_gen_swapL. intros. eapply X.
        2: exact H.  2: exact H0. apply swapped_I'. Qed.

Lemma can_gen_swapR_def': forall {V : Set} 
                                 (rules : rlsT (@LNS V)) ns,
    iffT (can_gen_swapR rules ns)
         (forall G K s Γ Δ Δ' d, 
             swapped Δ Δ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
             pf rules (G ++ (pair Γ Δ', d) :: K)).
Proof.  intros.  unfold iffT.  split ; intros. 
        destruct H. subst. unfold can_gen_swapR in X.
        eapply X. reflexivity.  reflexivity.
        unfold can_gen_swapR. intros. eapply X.
        2: exact H.  2: exact H0. apply swapped_I'. Qed.

Lemma can_gen_swapL_imp: forall {V : Set} 
                                (rules : rlsT (@LNS V)) ns,
    can_gen_swapL rules ns -> forall G K s Γ Δ Γ' d, 
      swapped Γ Γ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
      pf rules (G ++ (pair Γ' Δ, d) :: K).
Proof.
  intros until 0. intro H; intros.
  edestruct (@can_gen_swapL_def' V) as [HH1 HH2].
  eapply HH1; eassumption.
Qed.

Lemma can_gen_swapR_imp: forall {V : Set} 
                                (rules : rlsT (@LNS V)) ns,
    can_gen_swapR rules ns -> forall G K s Γ Δ Δ' d, 
      swapped Δ Δ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
      pf rules (G ++ (pair Γ Δ', d) :: K).
Proof.
  intros until 0. intro H; intros.
  edestruct (@can_gen_swapR_def' V) as [HH1 HH2].
  eapply HH1; eassumption.
Qed.

Lemma can_gen_swapL_imp_rev: forall {V : Set} 
                                    (rules : rlsT (@LNS V)) ns,
    (forall G K s Γ Δ Γ' d, 
        swapped Γ Γ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
        pf rules (G ++ (pair Γ' Δ, d) :: K)) ->
    can_gen_swapL rules ns.
Proof.
  intros until 0. intro H; intros.
  edestruct (@can_gen_swapL_def' V) as [HH1 HH2].
  eapply HH2; eassumption.
Qed.

Lemma can_gen_swapR_imp_rev: forall {V : Set} 
                                    (rules : rlsT (@LNS V)) ns,
    (forall G K s Γ Δ Δ' d, 
        swapped Δ Δ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
        pf rules (G ++ (pair Γ Δ', d) :: K)) ->
    can_gen_swapR rules ns.
Proof.
  intros until 0. intro H; intros.
  edestruct (@can_gen_swapR_def' V) as [HH1 HH2].
  eapply HH2; eassumption.
Qed.

Lemma can_gen_moveL_mono: forall {V : Set}
                                 (rulesa rulesb : rlsT (@LNS V)) ns,
    rsub rulesa rulesb ->
    can_gen_moveL rulesa ns -> can_gen_moveL rulesb ns.
Proof.
  intros until 0; intros Hr H.
  unfold can_gen_moveL. intros until 0; intros Hn1 Hn2.
  eapply derrec_rmono. exact Hr. eapply H; eassumption.
Qed.

Lemma can_gen_moveR_mono: forall {V : Set}
                                 (rulesa rulesb : rlsT (@LNS V)) ns,
    rsub rulesa rulesb ->
    can_gen_moveR rulesa ns -> can_gen_moveR rulesb ns.
Proof.
  intros until 0; intros Hr H.
  unfold can_gen_moveR. intros until 0; intros Hn1 Hn2.
  eapply derrec_rmono. exact Hr. eapply H; eassumption.
Qed.

Lemma can_gen_swapL_mono: forall {V : Set}
                                 (rulesa rulesb : rlsT (@LNS V)) ns,
    rsub rulesa rulesb ->
    can_gen_swapL rulesa ns -> can_gen_swapL rulesb ns.
Proof.
  intros until 0; intros Hr H.
  unfold can_gen_swapL. intros until 0; intros Hn1 Hn2.
  eapply derrec_rmono. exact Hr. eapply H; eassumption.
Qed.

Lemma can_gen_swapR_mono: forall {V : Set}
                                 (rulesa rulesb : rlsT (@LNS V)) ns,
    rsub rulesa rulesb ->
    can_gen_swapR rulesa ns -> can_gen_swapR rulesb ns.
Proof.
  intros until 0; intros Hr H.
  unfold can_gen_swapR. intros until 0; intros Hn1 Hn2.
  eapply derrec_rmono. exact Hr. eapply H; eassumption.
Qed.

Definition gen_moveL_step {V : Set}
           (last_rule rules : rlsT (@LNS V)) ps concl :=
  last_rule ps concl -> pfs rules ps ->
  ForallT (can_gen_moveL rules) ps -> rsub last_rule rules -> 
  can_gen_moveL rules concl.

Definition gen_moveR_step {V : Set}
           (last_rule rules : rlsT (@LNS V)) ps concl :=
  last_rule ps concl -> pfs rules ps ->
  ForallT (can_gen_moveR rules) ps -> rsub last_rule rules -> 
  can_gen_moveR rules concl.

Definition gen_swapL_step {V : Set}
           (last_rule rules : rlsT (@LNS V)) ps concl :=
  last_rule ps concl -> pfs rules ps ->
  ForallT (can_gen_swapL rules) ps -> rsub last_rule rules -> 
  can_gen_swapL rules concl.

Definition gen_swapR_step {V : Set}
           (last_rule rules : rlsT (@LNS V)) ps concl :=
  last_rule ps concl -> pfs rules ps ->
  ForallT (can_gen_swapR rules) ps -> rsub last_rule rules -> 
  can_gen_swapR rules concl.

Definition can_gen_init {V : Set}
           (rules : rlsT (@LNS V)) ns A :=
  forall G s d Γ1 Γ2 Δ1 Δ2,
    ns = G ++ [(s, d)] -> s = pair (Γ1 ++ [A] ++ Γ2) (Δ1 ++ [A] ++ Δ2) ->
    pf rules ns.


(* -------------------------- *)
(* LEFT WEAKENING DEFINITIONS *)
(* -------------------------- *)

Definition can_gen_weakL {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ1 Γ2 Γ3 Δ,
    ns = G ++ (s, d) :: K -> s = pair (Γ1 ++ Γ3) Δ ->
    pf rules (G ++ (pair (Γ1 ++ Γ2 ++ Γ3) Δ, d) :: K).

Definition gen_weakL_step {V : Set}
           (last_rule rules : rlsT (@LNS V)) ps concl :=
  last_rule ps concl -> pfs rules ps ->
  ForallT (can_gen_weakL rules) ps -> rsub last_rule rules -> 
  can_gen_weakL rules concl.

Lemma can_gen_weakL_def': forall {V : Set} 
                                 (rules : rlsT (@LNS V)) ns,
    iffT (can_gen_weakL rules ns) (forall G K s Γ Δ Γ' d, 
                                      weakened Γ Γ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
                                      pf rules (G ++ (pair Γ' Δ, d) :: K)).
Proof.  intros.  unfold iffT.  split ; intros. 
        destruct H. subst. unfold can_gen_weakL in X.
        eapply X. reflexivity.  reflexivity.
        unfold can_gen_weakL. intros. eapply X.
        2: exact H.  2: exact H0. apply weakened_I'. auto. Qed.

(* --------------------------- *)
(* RIGHT WEAKENING DEFINITIONS *)
(* --------------------------- *)

Definition can_gen_weakR {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ Δ1 Δ2 Δ3,
    ns = G ++ (s, d) :: K -> s = pair Γ (Δ1 ++ Δ3)->
    pf rules (G ++ (pair Γ (Δ1 ++ Δ2 ++ Δ3), d) :: K).

Definition gen_weakR_step {V : Set}
           (last_rule rules : rlsT (@LNS V)) ps concl :=
  last_rule ps concl -> pfs rules ps ->
  ForallT (can_gen_weakR rules) ps -> rsub last_rule rules -> 
  can_gen_weakR rules concl.

Lemma can_gen_weakR_def': forall {V : Set} 
                                 (rules : rlsT (@LNS V)) ns,
    iffT (can_gen_weakR rules ns)
         (forall G K s Γ Δ Δ' d, 
             weakened Δ Δ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
             pf rules (G ++ (pair Γ Δ', d) :: K)).
Proof.  intros.  unfold iffT.  split ; intros. 
        destruct H. subst. unfold can_gen_weakR in X.
        eapply X. reflexivity.  reflexivity.
        unfold can_gen_weakR. intros. eapply X.
        2: exact H.  2: exact H0. apply weakened_I'. auto. Qed.

Lemma can_gen_weakL_imp: forall {V : Set} 
                                (rules : rlsT (@LNS V)) ns,
    can_gen_weakL rules ns -> forall G K s Γ Δ Γ' d, 
      weakened Γ Γ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
      pf rules (G ++ (pair Γ' Δ, d) :: K).
Proof.  intros until 0. intro.
        eapply can_gen_weakL_def'. exact X. Qed.

Lemma can_gen_weakR_imp: forall {V : Set} 
                                (rules : rlsT (@LNS V)) ns,
    can_gen_weakR rules ns -> forall G K s Γ Δ Δ' d, 
      weakened Δ Δ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
      pf rules (G ++ (pair Γ Δ', d) :: K).
Proof.  intros until 0. intro.
        apply can_gen_weakR_def'. exact X. Qed.

(* ---------------------------- *)
(* LEFT CONTRACTION DEFINITIONS *)
(* ---------------------------- *)

Definition can_gen_contL {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ1 Γ2 A Δ,
    ns = G ++ (s, d) :: K -> s = pair (Γ1 ++ [A;A] ++ Γ2) Δ ->
    pf rules 
       (G ++ (pair (Γ1 ++ [A] ++ Γ2) Δ, d) :: K).

Definition can_gen_contL_genL {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ1 Γ2 Γ3 A Δ,
    ns = G ++ (s, d) :: K ->
    (s = pair (Γ1 ++ [A] ++ Γ2 ++ [A] ++ Γ3) Δ) ->
    pf rules 
       (G ++ (pair (Γ1 ++ [A] ++ Γ2 ++ Γ3) Δ, d) :: K) .

Definition can_gen_contL_genR {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ1 Γ2 Γ3 A Δ,
    ns = G ++ (s, d) :: K -> s = pair (Γ1 ++ [A] ++ Γ2 ++ [A] ++ Γ3) Δ ->
    pf rules (G ++ (pair (Γ1 ++ Γ2 ++ [A] ++ Γ3) Δ, d) :: K).

Definition can_gen_contL_gen {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ1 Γ2 Γ3 A Δ,
    ns = G ++ (s, d) :: K ->
    (s = pair (Γ1 ++ [A] ++ Γ2 ++ [A] ++ Γ3) Δ) ->
    (pf rules (G ++ (pair (Γ1 ++ [A] ++ Γ2 ++ Γ3) Δ, d) :: K)) *
    (pf rules (G ++ (pair (Γ1 ++ Γ2 ++ [A] ++ Γ3) Δ, d) :: K)).

Definition gen_contL_step {V : Set}
           (last_rule rules : rlsT (@LNS V)) ps concl :=
  last_rule ps concl -> pfs rules ps ->
  ForallT (can_gen_contL rules) ps -> rsub last_rule rules -> 
  can_gen_contL rules concl.

Definition gen_contL_gen_step {V : Set}
           (last_rule rules : rlsT (@LNS V)) ps concl :=
  last_rule ps concl -> pfs rules ps ->
  ForallT (can_gen_contL_gen rules) ps -> rsub last_rule rules -> 
  can_gen_contL_gen rules concl.

Lemma can_gen_contL_def': forall {V : Set} 
                                 (rules : rlsT (@LNS V)) ns,
    iffT (can_gen_contL rules ns) (forall G K s Γ Δ Γ' d, 
                                      contracted Γ Γ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
                                      pf rules (G ++ (pair Γ' Δ, d) :: K)).
Proof.
  intros.  unfold iffT. unfold can_gen_contL.
  split ; intros X; intros until 0;  intros H H0.
  intros H1. inversion H. subst. unfold can_gen_contL in X.
  eapply X. reflexivity.  reflexivity.
  subst. eapply X. 2 : reflexivity. 2 : reflexivity.
  apply contracted_I'.
Qed.

Lemma can_gen_contL_gen_def': forall {V : Set} 
                                     (rules : rlsT (@LNS V)) ns,
    iffT (can_gen_contL_gen rules ns) (forall G K s Γ Δ Γ' d, 
                                          contracted_gen Γ Γ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
                                          pf rules (G ++ (pair Γ' Δ, d) :: K)).
Proof.
  intros.  unfold iffT. unfold can_gen_contL_gen.
  split ; intros X; intros until 0; intros H H0. 
  intros H1. destruct H. subst. eapply X. reflexivity.    
  reflexivity. subst. eapply X. reflexivity.
  reflexivity. subst. split. eapply X. 2 : reflexivity.
  2 : reflexivity. apply contracted_genL_I'.
  eapply X. 2 : reflexivity. 2: reflexivity.
  eapply contracted_genR_I'.
Qed.

(* ----------------------------- *)
(* RIGHT CONTRACTION DEFINITIONS *)
(* ----------------------------- *)

Definition can_gen_contR {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ Δ1 Δ2 A,
    ns = G ++ (s, d) :: K -> s = pair Γ (Δ1 ++ [A;A] ++ Δ2)->
    pf rules (G ++ (pair Γ (Δ1 ++ [A] ++ Δ2), d) :: K).

Definition gen_contR_step {V : Set}
           (last_rule rules : rlsT (@LNS V)) ps concl :=
  last_rule ps concl -> pfs rules ps ->
  ForallT (can_gen_contR rules) ps -> rsub last_rule rules -> 
  can_gen_contR rules concl.

Lemma can_gen_contR_def': forall {V : Set} 
                                 (rules : rlsT (@LNS V)) ns,
    iffT (can_gen_contR rules ns) (forall G K s Γ Δ Δ' d, 
                                      contracted Δ Δ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
                                      pf rules (G ++ (pair Γ Δ', d) :: K)).
Proof.
  intros.  unfold iffT.  unfold can_gen_contR.
  split ; intros X; intros until 0; intros H0 H1.
  intros H2. inversion H0. subst. eapply X.
  reflexivity. reflexivity. subst. eapply X.
  2 : reflexivity. 2 : reflexivity.
  eapply contracted_I'.
Qed.

Definition can_gen_contR_genL {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ Δ1 Δ2 Δ3 A,
    ns = G ++ (s, d) :: K ->
    s = pair Γ (Δ1 ++ [A] ++ Δ2 ++ [A] ++ Δ3) ->
    pf rules (G ++ (pair Γ (Δ1 ++ [A] ++ Δ2 ++ Δ3), d) :: K) .

Definition can_gen_contR_genR {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ Δ1 Δ2 Δ3 A,
    ns = G ++ (s, d) :: K ->
    s = pair Γ (Δ1 ++ [A] ++ Δ2 ++ [A] ++ Δ3) ->
    pf rules (G ++ (pair Γ (Δ1 ++ Δ2 ++ [A] ++ Δ3), d) :: K) .

Definition can_gen_contR_gen {V : Set}
           (rules : rlsT (@LNS V)) ns :=
  forall G K s d Γ Δ1 Δ2 Δ3 A,
    ns = G ++ (s, d) :: K ->
    s = pair Γ (Δ1 ++ [A] ++ Δ2 ++ [A] ++ Δ3) ->
    (pf rules (G ++ (pair Γ (Δ1 ++ [A] ++ Δ2 ++ Δ3), d) :: K)) *
    (pf rules (G ++ (pair Γ (Δ1 ++ Δ2 ++ [A] ++ Δ3), d) :: K)).

Definition gen_contR_gen_step {V : Set}
           (last_rule rules : rlsT (@LNS V)) ps concl :=
  last_rule ps concl -> pfs rules ps ->
  ForallT (can_gen_contR_gen rules) ps -> rsub last_rule rules -> 
  can_gen_contR_gen rules concl.

Lemma can_gen_contR_gen_def': forall {V : Set} 
                                     (rules : rlsT (@LNS V)) ns,
    iffT (can_gen_contR_gen rules ns) (forall G K s Γ Δ Δ' d, 
                                          contracted_gen Δ Δ' -> ns = G ++ (s, d) :: K -> s = pair Γ Δ ->
                                          pf rules (G ++ (pair Γ Δ', d) :: K)).
Proof.
  intros.  unfold iffT. unfold can_gen_contR_gen.
  split ; intros X; intros until 0; intros H0 H1.
  intros H2.  destruct H0; subst; eapply X; reflexivity.    
  split; subst; eapply X; auto.
  apply contracted_genL_I'.
  apply contracted_genR_I'.
Qed.



(* -------------- *)
(* TYPES OF RULES *)
(* -------------- *)

Definition rules_L_oe {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps x y Δ, rules ps (x ++ y, Δ) -> x = [] \/ y = [].

Definition rules_R_oe {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps x y Γ, rules ps (Γ, x ++ y) -> x = [] \/ y = [].

Definition rules_L_oeT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps x y Δ, rules ps (x ++ y, Δ) -> (x = []) + (y = []).

Definition rules_R_oeT {W : Set} (rules : rlsT (rel (list W))) := 
  forall ps x y Γ, rules ps (Γ, x ++ y) -> (x = []) + (y = []).



(* ------- *)
(* TACTICS *)
(* ------- *)

Ltac use_prX princrule_X pr := 
  pose pr as Qpr ;
  apply princrule_X in Qpr ;
  repeat (sD_list_eq ; subst ; simpl ; simpl in pr ;
          rewrite -> ?app_nil_r in * ; rewrite ?app_nil_r).

Ltac use_cgm cgmX H1 := 
  rewrite -> Forall_forall in H1 ;
  simpl in H1 ;
  specialize_full H1 ;
  [ | unfold cgmX in H1 ; unfold nsext ;
      rewrite <- app_assoc ;
      eapply H1 ; reflexivity ] ;
  unfold nsext ; tauto.

Ltac use_cgmL H1 := use_cgm can_gen_moveL H1.
Ltac use_cgmR H1 := use_cgm can_gen_moveR H1.

Ltac stage2 H1 qin1 qin3 := 
  rewrite dersrec_forall ;
  intros q qin ; rewrite -> in_map_iff in qin ; cD ;
  rename_last qin1 ;
  rewrite -> in_map_iff in qin1 ; cD ;
  rename_last qin3 ;
  destruct qin1 ; subst ;
  rewrite -> Forall_forall in H1 ;
  eapply in_map in qin3 ;
  eapply in_map in qin3 ;
  apply H1 in qin3 ;
  unfold can_gen_moveL in qin3 ;
  unfold nsext.

Ltac stage2alt H0 H1 qin1 qin3 := 
  rewrite dersrec_forall ;
  rewrite -> dersrec_forall in H0 ;
  intros q qin ; rewrite -> in_map_iff in qin ; cD ;
  rename_last qin1 ;
  rewrite -> in_map_iff in qin1 ; cD ;
  rename_last qin3 ;
  destruct qin1 ; subst ;
  rewrite -> Forall_forall in H1 ;
  eapply in_map in qin3 ;
  eapply in_map in qin3 ;
  (* see if can solve goal without swapping premises *)
  try (apply H0 in qin3 ; unfold seqext in qin3 ; exact qin3) ;
  apply H1 in qin3 ;
  unfold can_gen_moveL in qin3 ;
  unfold nsext.

Ltac stage3 qin3 l l1 := 
  eapply qin3 ; [ apply nsext_def |
                  rewrite seqext_def ; list_eq_assoc ].

Ltac stage2altds H0 H1 qin1 qin3 := 
  stage2alt H0 H1 qin1 qin3 ; (eapply derrec_same ; [
                                 eapply qin3 ; [ apply nsext_def | unfold seqext ] | ]).

Ltac stage2ds H1 qin1 qin3 := 
  stage2 H1 qin1 qin3 ; eapply derrec_same ; [
    eapply qin3 ; [ apply nsext_def | unfold seqext ] | ].

Ltac srs pr := eapply seqrule_same ; [ exact pr |
                                       apply pair_eqI ; try reflexivity ]. 

Ltac amt l0 := eapply eq_trans ; [> assoc_mid l0 .. ] ; [> reflexivity ..].

Ltac stage1 rs pr :=
  subst ;
  rewrite -> ?app_nil_r in * ;
  eapply derI ; [
    unfold rsub in rs ; apply rs ;
    rewrite <- nsext_def ; apply NSctxt ;
    eapply Sctxt in pr ;
    unfold seqext in pr ;
    simpl in pr | idtac ].

Ltac stage12altds rs H0 H1 qin1 qin3 pr l0 := 
  stage1 rs pr ; [ srs pr ; amt l0 | stage2altds H0 H1 qin1 qin3 ].

Ltac stage12ds rs H1 qin1 qin3 pr l0 := 
  stage1 rs pr ; [ srs pr ; amt l0 | stage2ds H1 qin1 qin3 ].

Ltac stage12altdsLg princrules rs H0 H1 qin1 qin3 pr := 
  match goal with
  | [ H : princrules _ (?x, _) |- _ ] =>
    stage12altds rs H0 H1 qin1 qin3 pr x end.

Ltac stage12altdsRg princrules rs H0 H1 qin1 qin3 pr := 
  match goal with
  | [ H : princrules _ (_, ?x) |- _ ] =>
    stage12altds rs H0 H1 qin1 qin3 pr x end.

Ltac midLg princrules := 
  match goal with | [ H : princrules _ (?x, _) |- _ ] => assoc_mid x end.

Ltac midRg princrules := 
  match goal with | [ H : princrules _ (_, ?x) |- _ ] => assoc_mid x end.

Ltac app_cancel := 
  (list_assoc_l' ; rewrite ?appr_cong ;
   list_assoc_r' ; rewrite ?appl_cong).

Ltac derIrs rs := eapply derI ; [> unfold rsub in rs ; apply rs ; clear rs | ].

Ltac solve_eqs := 
  prgt 33 ;
  repeat clear_one ;
  try (apply nsI) ;
  repeat (apply pair_eqI) ;
  try refl_ni ;
  assoc_single_mid ;
  try (apply midI) ;
  try (first [check_app_app | reflexivity]) ;
  repeat app_cancel ;
  try (first [check_app_app | reflexivity]) ;
  try refl_ni ;
  prgt 44.

(* tactic for when principal formula to be moved *)
Ltac mpv use_prL use_cgmL H1 H0 rs pr := 
  subst ; use_prL pr ; stage1 rs pr ; [ 
    rewrite !app_assoc ; rewrite !app_assoc in pr ; apply pr |
    destruct pr ; simpl ; repeat (apply dlNil || apply dlCons) ;
    try (use_cgmL H1) ;
    rewrite -> dersrec_forall in H0 ; apply H0 ; simpl ;
    rewrite <- app_assoc ;  tauto ].

(* tactic for admissibility proof in nested sequents,
  case where the rule is applied in a sequent to the right
  of where the move takes place *)

(* version of nsright suitable for case where 
  rs : rsub (nsrule ...) rules, and rest of goal involves rules *)
Ltac nsright pp G0 se d0 x Ge HeqGe K d ps ps0 inps0 pse K0 drs nsr acm
     G s rs := 
  clear drs nsr ;  clear pp ;  cE ;
  (* case where the rule is applied in a sequent to the right
  of where the swap takes place *)
  remember (G0 ++ (se, d0) :: x) as Ge ;
  remember (map (nsext Ge K d) ps0) as pse ;
  apply derI with pse ; [
    subst pse ; subst K0 ; rewrite list_rearr14 ;
    unfold rsub in rs ; apply rs ;
    (* it must be easier than this
    to rewrite using the inverse of the definition of nsext *)
    rewrite <- nsext_def ;  subst se ;  rewrite <- HeqGe ;
    apply NSctxt ; assumption |
    rewrite dersrec_forall ;
    intros q qin ;  subst pse ;  rewrite -> in_map_iff in qin ; cE ;
    subst q ;  subst ps ;
    rewrite -> Forall_forall in acm ;
    rename_last inps0 ;  eapply in_map in inps0 ; 
    apply acm in inps0 ;
    unfold can_gen_swapL in inps0 ;
    unfold nsext ; subst Ge ; subst se ;
    rewrite <- list_rearr14 ;
    eapply inps0 ; [> | reflexivity ] ;
    unfold nsext ; subst G ; subst s ;
    list_eq_assoc ].

Ltac nsleft pp G0 se d0 x He HeqHe K d ps ps0 inps0 pse K0 drs nsr acm
     G s rs := 
  clear drs nsr ;  clear pp ;  cE ;
  (* case where the rule is applied in a sequent to the left
  of where the swap takes place *)
  remember (x ++ (se, d0) :: K0) as He ;
  remember (map (nsext G He d) ps0) as pse ;
  apply derI with pse ; [
    subst pse ; subst G0 ; rewrite <- list_rearr14 ;
    unfold rsub in rs ; apply rs ;
    (* it must be easier than this
    to rewrite using the inverse of the definition of nsext *)
    rewrite <- nsext_def ;  subst se ;  rewrite <- HeqHe ;
    apply NSctxt ; assumption |
    rewrite dersrec_forall ;
    intros q qin ;  subst pse ;  rewrite -> in_map_iff in qin ; cE ;
    subst q ;  subst ps ;
    rewrite -> Forall_forall in acm ;
    rename_last inps0 ;  eapply in_map in inps0 ; 
    apply acm in inps0 ;
    unfold can_gen_swapL in inps0 ;
    unfold nsext ; subst He ; subst se ;
    rewrite list_rearr14 ;
    eapply inps0 ; [> | reflexivity ] ;
    unfold nsext ; subst K ; subst s ;
    list_eq_assoc ].

(* for using swap in the case when the rule affects a list of
  sequents or a single sequent, plus context (ie nslext or nsext), and
  the operation of the rule is distinct from the sequent where the swap is;
  note, where the context is on the left only,
  exchL2 rs sppc acm swap. generally seems to work also *)
Ltac nsgen_sw rs sppc c c' acm inps0 swap :=
  derIrs rs ; [>
               (assoc_mid c ; apply NSlctxt') ||
                                              (assoc_single_mid' c ; apply NSctxt') ||
                                              (list_assoc_l' ; apply NSlclctxt') ||
                                              (list_assoc_l' ; apply NSlcctxt') ;
               exact sppc |
               rewrite dersrec_forall ;
               intros q qin ;
               rewrite -> in_map_iff in qin ; cE ; subst q ;
               rewrite -> Forall_forall in acm ;
               rename_last inps0 ;  eapply in_map in inps0 ;
               eapply acm in inps0 ;
               rewrite -> ?can_gen_swapL_def' in inps0 ;
               rewrite -> ?can_gen_swapR_def' in inps0 ;
               unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
               assoc_single_mid' c' ;
               eapply inps0 ; [> exact swap |
                               unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
                               list_eq_assoc | reflexivity ]].

Ltac nsgen_swT rs sppc c c' acm inps0 swap :=
  derIrs rs ; [>
               (assoc_mid c ; apply NSlctxt') ||
                                              (assoc_single_mid' c ; apply NSctxt') ||
                                              (list_assoc_l' ; apply NSlclctxt') ||
                                              (list_assoc_l' ; apply NSlcctxt') ;
               exact sppc | 
               apply dersrec_forall ;
               intros q qin ;
               apply InT_map_iffT in qin ;
               do 2 cET_nr ;
               subst ;
               rename_last inps0 ;
               eapply ForallT_forall in acm ;
               eapply InT_map in inps0 ; 
               [ | eexact inps0 ] ];
  (eapply can_gen_swapL_def' in acm ||
                                eapply can_gen_swapR_def' in acm );
  [unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
   assoc_single_mid' c' ;
   eapply acm |
   exact swap |
   unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
   list_eq_assoc | assumption]. 

Ltac nsgen_swTT rs sppc c c' acm inps0 swap :=
  derIrs rs ; [>
               (assoc_mid c ; apply NSlctxt') ||
                                              (assoc_single_mid' c ; apply NSctxt') ||
                                              (list_assoc_l' ; apply NSlclctxt') ||
                                              (list_assoc_l' ; apply NSlcctxt') ;
               exact sppc |
               apply dersrec_forall ;
               intros q qin ;
               apply InT_map_iffT in qin ; cET ; subst q ;
               rename_last inps0 ;
               eapply ForallT_forall in acm ;
               eapply InT_map in inps0 ;
               [ | eexact inps0 ] ];
  (eapply can_gen_swapL_def' in acm ||
                                eapply can_gen_swapR_def' in acm );
  [unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
   assoc_single_mid' c' ;
   eapply acm |
   exact swap |
   unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
   list_eq_assoc | reflexivity ].

Ltac nsprsame rs pr q qin inmps acm inps0 x0 := 
  derIrs rs ; [> apply NSctxt' || apply NSlcctxt' ;
               apply Sctxt_e || apply Sctxt_e' ; exact pr |] ;
  rewrite dersrec_forall ;
  intros q qin ;
  rewrite -> in_map_iff in qin ; cE ; 
  rename_last inmps ;
  rewrite -> in_map_iff in inmps ; cE ; 
  rewrite -> Forall_forall in acm ;
  rename_last inps0 ;  eapply in_map in inps0 ;
  eapply in_map in inps0 ;
  eapply acm in inps0 ;
  clear acm ;
  rewrite -> ?can_gen_swapL_def' in inps0 ;
  rewrite -> ?can_gen_swapR_def' in inps0 ;
  subst ;
  destruct x0 ;
  unfold seqext ;
  unfold nsext ; unfold nslcext ;
  eapply inps0 ;
  [> | unfold nsext ; unfold nslcext ; reflexivity |
   unfold seqext ; reflexivity ] ;
  swap_tac.

Ltac nsprsameL princrules rs pr q qin inmps acm inps0 x0 := 
  match goal with | [ H : princrules _ (?x, _) |- _ ] => assoc_mid x end ;
  nsprsame rs pr q qin inmps acm inps0 x0.

Ltac nsprsameR princrules rs pr q qin inmps acm inps0 x0 := 
  match goal with | [ H : princrules _ (_, ?x) |- _ ] => assoc_mid x end ;
  nsprsame rs pr q qin inmps acm inps0 x0.

Ltac nsprsameT rs pr q qin inmps acm inps0 x0 :=
  derIrs rs ; [> apply NSctxt' || apply NSlcctxt' ;
               apply Sctxt_e || apply Sctxt_e' ; exact pr |] ;
  eapply dersrec_forall ;
  intros q qin ;
  eapply InT_map_iffT in qin ; cET ;
  rename_last inmps ;
  eapply InT_map_iffT in inmps ; cET ; subst ;
  rename_last inps0 ;
  eapply ForallT_forall in acm ; [ | eapply InT_map; eapply InT_map; exact inps0];
  destruct x0;
  try eapply can_gen_swapL_def' in acm ;
  try eapply can_gen_swapR_def' in acm ;
  [ eapply acm | |
    unfold nsext ; unfold nslcext ; reflexivity |
    unfold seqext; reflexivity ]; swap_tac.

Ltac nsprsameLT princrules rs pr q qin inmps acm inps0 x0 := 
  match goal with | [ H : princrules _ (?x, _) |- _ ] => assoc_mid x end ;
  nsprsameT rs pr q qin inmps acm inps0 x0.

Ltac nsprsameRT princrules rs pr q qin inmps acm inps0 x0 := 
  match goal with | [ H : princrules _ (_, ?x) |- _ ] => assoc_mid x end ;
  nsprsameT rs pr q qin inmps acm inps0 x0.

Ltac ms_cgs acm := 
  rewrite ?dersrec_map_2 ;
  rewrite ?dersrec_map_single ;
  rewrite -> ?Forall_map_single in acm ;
  rewrite -> ?Forall_map_2 in acm ;
  rewrite -> ?can_gen_swapL_def' in acm ;
  rewrite -> ?can_gen_swapR_def' in acm ;
  unfold nslclext ; unfold nslext.


Ltac ms_cgsTT1 acm :=
  try apply dersrec_map_2 ;
  try apply dersrec_map_single ;
  try (apply ForallT_map_2 in acm || apply ForallT_map_rev in acm );
  try eapply can_gen_swapL_def' in acm ;
  try eapply can_gen_swapR_def' in acm ;
  unfold nslclext ; unfold nslext.

Ltac ms_cgsT_fst acm :=
  try apply dersrec_map_2 ;
  try apply dersrec_map_single ;
  try (apply ForallT_map_2 in acm || apply ForallT_map_rev in acm ).

Ltac ms_cgsT_snd acm acm1 acm2 :=
  (destruct acm as [acm1 acm2];
   ((eapply can_gen_swapL_def' in acm1; eapply can_gen_swapL_def' in acm2) ||
    (eapply can_gen_swapR_def' in acm1; eapply can_gen_swapR_def' in acm2))) ||
                                                                             (eapply can_gen_swapL_def' in acm || eapply can_gen_swapR_def' in acm).

Ltac ms_cgsT_all acm acm1 acm2 :=
  ms_cgsT_fst acm; ms_cgsT_snd acm acm1 acm2.

(* where exchange is in the first of two sequents of the modal rule *)
Ltac use_acm1 acm rs ith := 
  (* interchange two sublists of list of formulae *)
  derIrs rs ; [> 
               apply NSlctxt2 || apply NSlclctxt' ;
               assoc_single_mid ;
               apply ith |
               ms_cgs acm ;
               list_assoc_r' ; simpl ; eapply acm ] ; [> | 
                                                       unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
                                                       reflexivity ] ; 
  swap_tac.

Ltac use_acm1TT acm rs ith := 
  (* interchange two sublists of list of formulae *)
  derIrs rs ; [> 
               apply NSlctxt2 || apply NSlclctxt' ;
               assoc_single_mid ;
               apply ith |
               ms_cgsTT1 acm ;
               list_assoc_r' ; simpl] ; [>  eassumption | | 
                                         unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
                                         reflexivity ] ; 
  swap_tac.


(* where swapping is in second sequent of modal rule,
  in which conclusion has no principal formula *)
Ltac use_acm2s acm rs ith rw :=
  derIrs rs ; [> 
               list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
               rw ; (* rewrite so as to identify two parts of context *)
               apply ith |
               ms_cgs acm ;
               list_assoc_r' ; simpl ;
               rewrite ?list_rearr22 ; eapply acm ] ; [> | 
                                                       unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
                                                       reflexivity ] ; swap_tac.

Ltac use_acm_sw_sep acm rs swap ith :=
  (* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
  derIrs rs ; [> 
               list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
               apply ith |
               ms_cgs acm ;
               eapply acm in swap ] ;
  [> (rewrite - list_rearr21 ; eapply swap) || 
                                            (list_assoc_r' ; simpl ; eapply swap) |
   unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
   reflexivity ].

Ltac use_drs rs drs ith :=
  (* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
  derIrs rs ; [> 
               list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
               apply ith | exact drs].

Ltac use_drs_mid rs drs ith :=
  (* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
  derIrs rs ; [> 
               list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
               assoc_single_mid ; apply ith | exact drs].

Ltac use_acm_os acm rs swap ith :=
  (* swap in opposite side from where rule active *)
  derIrs rs ; [> 
               apply NSlclctxt || apply NSlctxt ;
               apply ith |
               ms_cgs acm ;
               eapply acm in swap ] ;
  [> eapply swap |
   unfold nslext ; unfold nslclext ; reflexivity |
   reflexivity ].

Ltac use_acm_osTT acm rs swap ith :=
  (* swap in opposite side from where rule active *)
  derIrs rs ; [> 
               apply NSlclctxt || apply NSlctxt ;
               apply ith |
               ms_cgsTT1 acm ] ;
  [> apply acm | eapply swap |
   unfold nslext ; unfold nslclext ; reflexivity |
   reflexivity ].

Ltac acmi_snr acmi swap := 
  eapply acmi ; [> exact swap | apply nslclext_def | reflexivity ].

Ltac use_acm_2 acm rs swap ith :=
  derIrs rs ; [>
               apply NSlclctxt' || apply NSlctxt2 ;
               apply ith |
               ms_cgs acm ; destruct acm as [acm1 acm2] ; 
               split ; [> acmi_snr acm1 swap | acmi_snr acm2 swap ]
              ].

Ltac use_acm_2TT acm rs swap ith :=
  derIrs rs ; [>
               apply NSlclctxt' || apply NSlctxt2 ;
               apply ith |
               let acm1 := fresh "acm" in
               let acm2 := fresh "acm" in
               ms_cgsT_all acm acm1 acm2 ;
               unfold nslclext;
               (exact swap || apply nslclext_def || reflexivity || split);
               [eapply acm1 | eapply acm2]].

Ltac acmi_snr_ass acmi swap := list_assoc_r' ; eapply acmi ;
                               [> exact swap | 
                                list_assoc_l' ; apply nslclext_def |
                                reflexivity ].

Ltac use_acm_2_ass acm rs swap ith :=
  derIrs rs ; [> list_assoc_l' ;
               apply NSlclctxt' || apply NSlctxt2 ;
               apply ith |
               ms_cgs acm ; destruct acm as [acm1 acm2] ; 
               split ; [> acmi_snr_ass acm1 swap | acmi_snr_ass acm2 swap ]
              ].

Ltac acmi_snr_snd acmi swap := rewrite list_rearr16' ; eapply acmi ;
                               [> exact swap | 
                                list_assoc_r' ; simpl ; apply nslclext_def |
                                reflexivity ].

Ltac use_acm_2_snd acm rs swap ith :=
  derIrs rs ; [> list_assoc_r' ;
               apply NSlclctxt' || apply NSlctxt2 ;
               apply ith |
               ms_cgs acm ; destruct acm as [acm1 acm2] ; 
               split ; [> acmi_snr_snd acm1 swap | acmi_snr_snd acm2 swap ]
              ].

Ltac acmi_snr_sw acmi swap := eapply acmi ;
                              [> | apply nslclext_def | reflexivity ] ; [> swap_tac ].

Ltac acmi_snr_sw'' acmi swap rw3 rw4 := rw3 ; eapply acmi ;
                                        [> | rw4 ; apply nslclext_def | reflexivity ] ; [> swap_tac ].

Ltac use_acm_2_sw acm rs swap rw ith :=
  derIrs rs ; [> 
               apply NSlclctxt' || apply NSlctxt2 ;
               rw ; apply ith |
               ms_cgs acm ; destruct acm as [acm1 acm2] ; 
               split ; [> acmi_snr_sw acm1 swap | acmi_snr_sw acm2 swap ]
              ].

Ltac use_acm_2_swT acm rs swap rw ith :=
  derIrs rs ; [> 
               apply NSlclctxt' || apply NSlctxt2 ;
               rw ; apply ith |];
  let acm1 := fresh "acm" in
  let acm2 := fresh "acm" in
  ms_cgsT_all acm acm1 acm2  ; 
  (apply nslclext_def || reflexivity || (split; [eapply acm1 | eapply acm2]) || idtac);
  (list_assoc_r'; swap_tac).

Ltac use_acm_2_sw'' acm rs swap rw1 rw2 rw3 rw4 ith :=
  derIrs rs ; [> rw1 ;
               apply NSlclctxt' || apply NSlctxt2 ;
               rw2 ; apply ith |
               ms_cgs acm ; destruct acm as [acm1 acm2] ; 
               split ; [> acmi_snr_sw'' acm1 swap rw3 rw4 | 
                        acmi_snr_sw'' acm2 swap rw3 rw4 ]
              ].

Ltac use_acm_2_sw''T acm rs swap rw1 rw2 rw3 rw4 ith :=
  derIrs rs ; [> rw1 ;
               apply NSlclctxt' || apply NSlctxt2 ;
               rw2 ; apply ith | ];
  let acm1 := fresh "acm" in
  let acm2 := fresh "acm" in
  ms_cgsT_all acm acm1 acm2;
  ((unfold nslclext; rw4; apply nslclext_def) ||
   reflexivity ||
   (unfold nslclext; split; [rw3; eapply acm1 | rw3; eapply acm2]) || idtac); swap_tac.

(* case of exchange in sequent to the left of where rule applied,
  no need to expand sppc *) 
Ltac exchL2 rs sppc acm swap :=
  derIrs rs ; [> list_assoc_l' ;
               apply NSlclctxt' || apply NSlctxt2 ; exact sppc | ] ;
  rewrite dersrec_forall ; intros L H ;
  rewrite -> in_map_iff in H ; destruct H ; destruct H as [H1 H2] ; subst ;
  rewrite -> Forall_forall in acm ; eapply in_map in H2 ; eapply acm in H2 ;
  eapply can_gen_swapL_imp in H2 || eapply can_gen_swapR_imp in H2 ;
  [> | exact swap | | reflexivity ] ;
  [> unfold nslclext ; list_assoc_r' ; exact H2
  | unfold nslclext ; list_assoc_r' ; reflexivity].

Ltac exchL2T rs sppc acm swap :=
  derIrs rs ; [> list_assoc_l' ;
               apply NSlclctxt' || apply NSlctxt2 ; exact sppc | ] ;
  apply dersrec_forall ; intros L H ;
  apply InT_mapE in H ; destruct H as [x H] ; destruct H as [H1 H2] ; subst ;
  eapply InT_map in H2; eapply ForallTD_forall in acm ; [|exact H2];
  eapply can_gen_swapL_imp in acm || eapply can_gen_swapR_imp in acm ;
  [> | exact swap | | reflexivity ] ;
  [> unfold nslclext ; list_assoc_r' ; exact acm
  | unfold nslclext ; list_assoc_r' ; reflexivity].


Ltac use_acm2sT acm rs ith rw :=
  derIrs rs ; [> 
               list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
               rw ; (* rewrite so as to identify two parts of context *)
               apply ith |
               ms_cgsTT1 acm] ;
  [list_assoc_r' ; simpl ; rewrite ?list_rearr22 ; eapply acm | |
   unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
   reflexivity ] ; swap_tac.

Ltac use_acm_sw_sepT acm rs swap ith :=
  (* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
  derIrs rs ; [> 
               list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
               apply ith |
               ms_cgsTT1 acm ] ;
  [eapply acm | exact swap | reflexivity | reflexivity].

Ltac use_acm_sw_sepT2 acm rs swap ith :=
  (* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
  derIrs rs ; [> 
               list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
               apply ith |
               ms_cgsTT1 acm ] ;
  [rewrite <- list_rearr21; eapply acm | exact swap |
   rewrite list_rearr21; reflexivity | reflexivity].

Ltac use_acm_sw_sepT3 acm rs swap ith :=
  (* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
  derIrs rs ; [> 
               list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
               apply ith |
               ms_cgsTT1 acm ] ;
  [  rewrite <- app_nil_r; rewrite <- app_assoc; rewrite <- list_rearr21;
     eapply acm | exact swap | ..]; list_assoc_r'; reflexivity.

Ltac use_acm_2_sndTT acm rs swap ith :=
  derIrs rs ; [> list_assoc_r' ;
               apply NSlclctxt' || apply NSlctxt2 ;
               apply ith |]; unfold nslclext;
  let acm1 := fresh "acm" in
  let acm2 := fresh "acm" in
  ms_cgsT_all acm acm1 acm2;
  (exact swap ||
   (unfold nslclext; rewrite (list_rearr16' _ (_ :: _ :: _)); reflexivity) ||
   (unfold nslclext; rewrite (list_rearr16' _ (_ :: _)); reflexivity)             
   || reflexivity || idtac);
  split; rewrite list_rearr16'; (eapply acm1 || eapply acm2).


