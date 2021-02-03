Add LoadPath "../general".

Require Import require_general.
Require Import LNS.
Require Import weakenedT contractedT.
Require Import structural_defs.
Require Import ssreflect.

Set Implicit Arguments.



(* -------------------------- *)
(* WEAKENING LEMMAS & TACTICS *)
(* -------------------------- *)

Ltac nsgen_sw_weak rs sppc c c' acm inps0 swap :=
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
rewrite -> ?can_gen_weakL_def' in inps0 ;
rewrite -> ?can_gen_weakR_def' in inps0 ; 
unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
assoc_single_mid' c' ;
eapply inps0 ; [> exact swap |
  unfold nsext ; unfold nslext ;  unfold nslcext ; unfold nslclext ;
  list_eq_assoc | reflexivity ]].


Ltac nsprsame_weak rs pr q qin inmps acm inps0 x0 := 
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
rewrite -> ?can_gen_weakL_def' in inps0 ;
rewrite -> ?can_gen_weakR_def' in inps0 ;
subst ;
destruct x0 ;
unfold seqext ;
unfold nsext ; unfold nslcext ;
eapply inps0 ;
  [> | unfold nsext ; unfold nslcext ; reflexivity |
    unfold seqext ; reflexivity ] ;
  weak_tacX.


Ltac nsprsameL_weak princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (?x, _) |- _ ] => assoc_mid x end ;
nsprsame_weak rs pr q qin inmps acm inps0 x0.

Ltac nsprsameR_weak princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (_, ?x) |- _ ] => assoc_mid x end ;
nsprsame_weak rs pr q qin inmps acm inps0 x0.

Ltac ms_cgs_weak acm := 
rewrite dersrec_map_single ;
rewrite -> Forall_map_single in acm ;
rewrite -> ?can_gen_weakL_def' in acm ;
rewrite -> ?can_gen_weakR_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac ms_cgs_weakT acm := 
eapply dersrec_map_single ;
eapply ForallT_map in acm ;
try eapply can_gen_weakL_def' in acm ;
try eapply can_gen_weakR_def' in acm ;
unfold nslclext ; unfold nslext.

Ltac use_acm1_weak acm rs ith :=
derIrs rs; [> 
apply NSlctxt2 || apply NSlclctxt' ;
assoc_single_mid ;
apply ith | 
ms_cgs acm ;
  list_assoc_r' ; simpl];
(* unfold can_gen_weakR in acm. *)
   (*   assoc_mid B; *)

   first [eapply acm | list_assoc_l'; rewrite <- app_assoc; eapply acm];
   unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl; reflexivity.

Ltac use_acm_os_weak acm rs swap ith :=
(* swap in opposite side from where rule active *)
derIrs rs ; [> 
apply NSlclctxt || apply NSlctxt ;
apply ith |
ms_cgs_weak acm ;
eapply acm in swap ] ;
[> eapply swap |
  unfold nslext ; unfold nslclext ; reflexivity |
  reflexivity ].

Ltac use_acm2s_weak acm rs ith rw:=
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
rw ; (* rewrite so as to identify two parts of context *)
apply ith |
ms_cgs_weak acm ;
list_assoc_r' ; simpl ;
rewrite ?list_rearr22 ; eapply acm ] ; [> | 
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; weak_tacX.

Ltac use_acm_sw_sep_weak acm rs weak ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs_weak acm ;
eapply acm in weak ] ;
[> (rewrite - list_rearr21 ; eapply weak) || 
  (list_assoc_r' ; simpl ; eapply weak) |
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ].


Ltac acmi_snr_sw_weak acmi := eapply acmi ;
  [>  apply nslclext_def|] ;  [>swap_tac; reflexivity].

Ltac use_acm_2_sw_weak_exch acm rs swap rw ith Hexch A B :=
derIrs rs ; [> 
apply NSlclctxt' || apply NSlctxt2 ;
rw ; apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split; [>
        try tac_cons_singleton; eapply Hexch; auto | ];
     assoc_mid B; [>  acmi_snr_sw_weak acm1 | acmi_snr_sw_weak acm2]].

Ltac use_acm_2_sw_weak acm rs swap rw ith B :=
derIrs rs ; [> 
apply NSlclctxt' || apply NSlctxt2 ;
rw ; apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split; assoc_mid B; [>  acmi_snr_sw_weak acm1 | acmi_snr_sw_weak acm2]].


Ltac weakL2 rs sppc acm swap :=
derIrs rs ; [> list_assoc_l' ;
    apply NSlclctxt' || apply NSlctxt2 ; exact sppc | ] ;
rewrite dersrec_forall ; intros L H ;
rewrite -> in_map_iff in H ; destruct H ; destruct H as [H1 H2] ; subst ;
rewrite -> Forall_forall in acm ; eapply in_map in H2 ; eapply acm in H2 ;
eapply can_gen_weakL_imp in H2 || eapply can_gen_weakR_imp in H2 ;
  [> | exact swap | | reflexivity ] ;
  [> unfold nslclext ; list_assoc_r' ; exact H2
    | unfold nslclext ; list_assoc_r' ; reflexivity].

Ltac acmi_snr_sw''_weak acmi swap rw3 rw4 := rw3 ; eapply acmi ;
  [> rw4 ;  apply nslclext_def | swap_tac; reflexivity ].

Ltac use_acm_2_sw''_weak acm rs swap rw1 rw2 rw3 rw4 ith :=
derIrs rs ; [> rw1 ;
apply NSlclctxt' || apply NSlctxt2 ;
rw2 ; apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; [> acmi_snr_sw''_weak acm1 swap rw3 rw4 | 
        acmi_snr_sw''_weak acm2 swap rw3 rw4 ]
            ].

Ltac acmi_snr_weak acmi swap := 
  eapply acmi ; [> apply nslclext_def | reflexivity ].

Ltac use_acm_2_weak acm rs swap ith :=
derIrs rs ; [>
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; inversion swap; subst;
[> acmi_snr_weak acm1 swap | acmi_snr_weak acm2 swap ]
].     

Ltac acmi_snr_snd_weak acmi swap := rewrite list_rearr16' ; eapply acmi ;
  [>  list_assoc_r' ; simpl ; apply nslclext_def |
    reflexivity ].

Ltac use_acm_2_snd_weak acm rs swap ith :=
derIrs rs ; [> list_assoc_r' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgs acm ; destruct acm as [acm1 acm2] ; 
split ; inversion swap; subst;
[> acmi_snr_snd_weak acm1 swap | acmi_snr_snd_weak acm2 swap ]
            ].

Ltac egx_app g exch := eapply g; [> intros; apply exch; assumption |
                                  reflexivity | eassumption | assumption | assumption | ].






(* REQUIRED FOR WEAKENING *)


Ltac nsgen_sw_weakT rs sppc c c' acm inps0 swap :=
derIrs rs ; [>
  (assoc_mid c ; apply NSlctxt') ||
  (assoc_single_mid' c ; apply NSctxt') ||
  (list_assoc_l' ; apply NSlclctxt') ||
  (list_assoc_l' ; apply NSlcctxt') ;
  exact sppc |
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cD ; subst q ;
rename_last inps0 ; 
eapply ForallT_forall in acm ;
eapply InT_map in inps0 ;
[ | eapply inps0];
try eapply can_gen_weakL_def' in acm ;
  try eapply can_gen_weakR_def' in acm ;
[>unfold nslclext; unfold nslcext; assoc_single_mid' c'; eapply acm |
 exact swap | unfold nslcext; list_eq_assoc | (assumption || reflexivity) ]].

Ltac nsprsame_weakT rs pr q qin inmps acm inps0 x0 := 
derIrs rs ; [> apply NSctxt' || apply NSlcctxt' ;
  apply Sctxt_e || apply Sctxt_e' ; exact pr |] ;
eapply dersrec_forall ;
intros q qin ;
eapply InT_map_iffT in qin ; cD ;
rename_last inmps ;
eapply InT_map_iffT in inmps ; cD ;
rename_last inps0 ; destruct inmps ; subst ;
  eapply ForallT_forall in acm ;
[ | eapply InT_map; eapply InT_map; eapply inps0];
try eapply can_gen_weakL_def' in acm ;
try eapply can_gen_weakR_def' in acm ;
[> eapply  acm | |
 unfold nsext ; unfold nslcext ; reflexivity |
    unfold seqext ; reflexivity ] ;
  weak_tacX.


Ltac nsprsameL_weakT princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (?x, _) |- _ ] => assoc_mid x end ;
nsprsame_weakT rs pr q qin inmps acm inps0 x0.

Ltac nsprsameR_weakT princrules rs pr q qin inmps acm inps0 x0 := 
match goal with | [ H : princrules _ (_, ?x) |- _ ] => assoc_mid x end ;
nsprsame_weakT rs pr q qin inmps acm inps0 x0.


(* ----- *)


(* ---------------------- *)
(* WEAKENING FOR B2RRULES *)
(* ---------------------- *)

Ltac use_acm_os_weakT acm rs swap ith :=
(* swap in opposite side from where rule active *)
derIrs rs ; [> 
apply NSlclctxt || apply NSlctxt ;
apply ith |
             ms_cgsTT1 acm ];
try eapply can_gen_weakL_def' in acm;
try eapply can_gen_weakR_def' in acm;
[exact acm | exact swap | reflexivity | reflexivity].


Ltac use_acm1_weakT acm rs ith :=
derIrs rs; [> 
apply NSlctxt2 || apply NSlclctxt' ;
assoc_single_mid ;
apply ith | 
ms_cgsTT1 acm ;
  list_assoc_r' ; simpl];
(* unfold can_gen_weakR in acm. *)
   (*   assoc_mid B; *)

   first [eapply acm | list_assoc_l'; rewrite <- app_assoc; eapply acm];
   unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl; reflexivity.






(* ---------------------- *)
(* WEAKENING FOR B1LRULES *)
(* ---------------------- *)

Ltac use_acm2s_weakT2 acm rs ith rw:=
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlctxt2 || apply NSlclctxt' ;
rw ; (* rewrite so as to identify two parts of context *)
apply ith |
ms_cgsTT1 acm ;
list_assoc_r' ; simpl ;
rewrite ?list_rearr22 ;
try eapply can_gen_weakL_def' in acm;
try eapply can_gen_weakR_def' in acm ] ; [> eapply acm | |
  unfold nslext ; unfold nslclext ; list_assoc_r' ; simpl ; reflexivity |
  reflexivity ] ; weak_tacX.


Ltac use_acm_sw_sep_weakT acm rs weak ith :=
(* interchange two sublists of list of formulae,
  no need to expand swap (swap separate from where rule is applied) *)
derIrs rs ; [> 
list_assoc_r' ; simpl ; apply NSlclctxt' || apply NSlctxt2 ;
             apply ith |
             ms_cgsTT1 acm ;
try eapply can_gen_weakR_def' in acm;
try eapply can_gen_weakL_def' in acm ];
[eapply acm | exact weak | reflexivity | reflexivity].



(* ---------------------- *)
(* WEAKENING FOR B1RRULES *)
(* ---------------------- *)

Ltac use_acm_2_weakT acm rs swap ith :=
derIrs rs ; [>
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
split ; inversion swap; subst;
[> acmi_snr_weak acm1 swap | acmi_snr_weak acm2 swap ]
].     

Ltac weakL2T rs sppc acm swap :=
derIrs rs ; [> list_assoc_l' ;
    apply NSlclctxt' || apply NSlctxt2 ; exact sppc | ] ;
eapply dersrec_forall ; intros L H ;
eapply InT_map_iffT in H ;
destruct H as [H3 H]; destruct H as [H1 H2] ; subst ;
  eapply ForallT_forall in acm  ; [ | eapply InT_map in H2 ; eapply H2] ;
(eapply can_gen_weakL_imp in acm || eapply can_gen_weakR_imp in acm ) ;
 [> |  exact swap | | reflexivity ] ;
  [> unfold nslclext ; list_assoc_r' ; exact acm
  | unfold nslclext ; list_assoc_r' ; reflexivity].

Ltac use_acm_2_snd_weakT acm rs swap ith :=
derIrs rs ; [> list_assoc_r' ;
apply NSlclctxt' || apply NSlctxt2 ;
apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
split ; inversion swap; subst;
[> acmi_snr_snd_weak acm1 swap | acmi_snr_snd_weak acm2 swap ]
            ].

Ltac use_acm_2_sw_weak_exchT acm rs swap rw ith Hexch A B :=
derIrs rs ; [> 
apply NSlclctxt' || apply NSlctxt2 ;
rw ; apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
split; [>
        try tac_cons_singleton; eapply Hexch; auto | ];
     assoc_mid B; [>  acmi_snr_sw_weak acm1 | acmi_snr_sw_weak acm2]].

Ltac use_acm_2_sw_weakT acm rs swap rw ith B :=
derIrs rs ; [> 
apply NSlclctxt' || apply NSlctxt2 ;
rw ; apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
split; assoc_mid B; [>  acmi_snr_sw_weak acm1 | acmi_snr_sw_weak acm2]].

Ltac use_acm_2_sw''_weakT acm rs swap rw1 rw2 rw3 rw4 ith :=
derIrs rs ; [> rw1 ;
apply NSlclctxt' || apply NSlctxt2 ;
rw2 ; apply ith |
ms_cgsTT1 acm ; destruct acm as [acm1 acm2] ; 
split ; [> acmi_snr_sw''_weak acm1 swap rw3 rw4 | 
        acmi_snr_sw''_weak acm2 swap rw3 rw4 ]
            ].