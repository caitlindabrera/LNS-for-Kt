module Cut_extraction_example where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Logic
import qualified Cut
import qualified DdT
import qualified Gen_seq
import qualified Gen_tacs
import qualified LntT
import qualified Lntb1LT
import qualified Lntkt_exchT
import qualified Merge
import qualified Structural_equivalence

nslcrule_gen :: (Datatypes.Coq_list a1) -> a1 -> (Datatypes.Coq_list
                (Datatypes.Coq_prod a1 LntT.Coq_dir)) -> LntT.Coq_dir ->
                (Datatypes.Coq_list
                (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir))) ->
                (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir)) ->
                a2 -> LntT.Coq_nslcrule a1 a2
nslcrule_gen ps c g d pS c0 x =
  Logic.eq_rect_r (List.map (LntT.nslcext g d) ps)
    (Logic.eq_rect_r (LntT.nslcext g d c) (LntT.NSlcctxt ps c g d x) c0) pS

coq_Ds_nil :: DdT.Coq_dersrec
              (Datatypes.Coq_list
              (Datatypes.Coq_prod
              (Gen_tacs.Coq_rel
              (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
              LntT.Coq_dir)) (Cut.LNSKt_cut_rules Datatypes.Coq_nat) 
              ()
coq_Ds_nil =
  DdT.Coq_dlNil

concl4_0 :: Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Datatypes.Coq_prod
            (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))
            (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
            LntT.Coq_dir)
concl4_0 =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.WBox (LntT.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp
    (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
    Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)

concl4_00 :: Datatypes.Coq_list
             (Datatypes.Coq_prod
             (Datatypes.Coq_prod
             (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))
             (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
             LntT.Coq_dir)
concl4_00 =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.WBox (LntT.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)

concl4_000 :: Datatypes.Coq_list
              (Datatypes.Coq_prod
              (Datatypes.Coq_prod
              (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))
              (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
              LntT.Coq_dir)
concl4_000 =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.WBox (LntT.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
    Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
    Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)

concl4_01 :: Datatypes.Coq_list
             (Datatypes.Coq_prod
             (Datatypes.Coq_prod
             (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))
             (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
             LntT.Coq_dir)
concl4_01 =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Imp (LntT.Var
    (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O)) Datatypes.Coq_nil))
    LntT.Coq_fwd) Datatypes.Coq_nil)

concl4_010 :: Datatypes.Coq_list
              (Datatypes.Coq_prod
              (Datatypes.Coq_prod
              (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))
              (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
              LntT.Coq_dir)
concl4_010 =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) (Datatypes.Coq_cons (LntT.Var (Datatypes.S Datatypes.O))
    Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp (LntT.Var (Datatypes.S
    Datatypes.O)) (LntT.Var Datatypes.O)) (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil))) LntT.Coq_fwd) Datatypes.Coq_nil)

pf4_000 :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf4_000 =
  Cut.LNSKt_rules_woc Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox
    (LntT.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil)
    LntT.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil))
    LntT.Coq_fwd) Datatypes.Coq_nil))
    (Logic.eq_rect_r
      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox (LntT.Var
        Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LntT.Coq_fwd)
        Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
        Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
        Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil))
      (Lntkt_exchT.Coq_prop Datatypes.Coq_nil
      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox (LntT.Var
        Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LntT.Coq_fwd)
        Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
        Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
        Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil))
      (nslcrule_gen Datatypes.Coq_nil (Datatypes.Coq_pair (Datatypes.Coq_cons
        (LntT.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons
        (LntT.Var Datatypes.O) Datatypes.Coq_nil)) (Datatypes.Coq_cons
        (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons
        (LntT.WBox (LntT.Var Datatypes.O)) Datatypes.Coq_nil)
        Datatypes.Coq_nil) LntT.Coq_fwd) Datatypes.Coq_nil) LntT.Coq_fwd
        Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
          (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox (LntT.Var
          Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LntT.Coq_fwd)
          Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
          (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
          Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
          Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil))
        (Gen_seq.seqrule_id Datatypes.Coq_nil (Datatypes.Coq_pair
          (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
          (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil))
          (LntT.Id_pfc Datatypes.O)))) (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox
      (LntT.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil)
      LntT.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
      Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)))

pf4_010 :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf4_010 =
  Cut.LNSKt_rules_woc Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil
    Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
    (Datatypes.Coq_cons (LntT.Var (Datatypes.S Datatypes.O))
    Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp (LntT.Var (Datatypes.S
    Datatypes.O)) (LntT.Var Datatypes.O)) (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil))) LntT.Coq_fwd) Datatypes.Coq_nil))
    (Logic.eq_rect_r
      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil)
        LntT.Coq_fwd) Datatypes.Coq_nil) (Datatypes.Coq_cons
        (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
        Datatypes.O) (Datatypes.Coq_cons (LntT.Var (Datatypes.S Datatypes.O))
        Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp (LntT.Var
        (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
        (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)))
        LntT.Coq_fwd) Datatypes.Coq_nil)) (Lntkt_exchT.Coq_prop
      Datatypes.Coq_nil
      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil)
        LntT.Coq_fwd) Datatypes.Coq_nil) (Datatypes.Coq_cons
        (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
        Datatypes.O) (Datatypes.Coq_cons (LntT.Var (Datatypes.S Datatypes.O))
        Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp (LntT.Var
        (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
        (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)))
        LntT.Coq_fwd) Datatypes.Coq_nil))
      (nslcrule_gen Datatypes.Coq_nil (Datatypes.Coq_pair (Datatypes.Coq_cons
        (LntT.Var Datatypes.O) (Datatypes.Coq_cons (LntT.Var (Datatypes.S
        Datatypes.O)) Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp
        (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
        (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)))
        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
        Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd) Datatypes.Coq_nil)
        LntT.Coq_fwd Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
          (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil)
          LntT.Coq_fwd) Datatypes.Coq_nil) (Datatypes.Coq_cons
          (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons
          (LntT.Var Datatypes.O) (Datatypes.Coq_cons (LntT.Var (Datatypes.S
          Datatypes.O)) Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp
          (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
          (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)))
          LntT.Coq_fwd) Datatypes.Coq_nil))
        (Gen_seq.seqrule_same Datatypes.Coq_nil
          (Gen_seq.seqext Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Var
            (Datatypes.S Datatypes.O)) Datatypes.Coq_nil) (Datatypes.Coq_cons
            (LntT.Imp (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var
            Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil
            (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
            Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
            Datatypes.Coq_nil))) (Datatypes.Coq_pair (Datatypes.Coq_cons
          (LntT.Var Datatypes.O) (Datatypes.Coq_cons (LntT.Var (Datatypes.S
          Datatypes.O)) Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp
          (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
          (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)))
          (Gen_seq.coq_Sctxt_nil (Datatypes.Coq_pair (Datatypes.Coq_cons
            (LntT.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons
            (LntT.Var Datatypes.O) Datatypes.Coq_nil)) Datatypes.Coq_nil
            (Datatypes.Coq_cons (LntT.Var (Datatypes.S Datatypes.O))
            Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Imp (LntT.Var
            (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
            Datatypes.Coq_nil) Datatypes.Coq_nil (LntT.Id_pfc Datatypes.O)))))
      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
      Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
      Datatypes.O) (Datatypes.Coq_cons (LntT.Var (Datatypes.S Datatypes.O))
      Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp (LntT.Var
      (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O)) (Datatypes.Coq_cons
      (LntT.Var Datatypes.O) Datatypes.Coq_nil))) LntT.Coq_fwd)
      Datatypes.Coq_nil)))

nslclrule_gen :: (Datatypes.Coq_list
                 (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir)))
                 -> (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir))
                 -> (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir))
                 -> (Datatypes.Coq_list
                 (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir)))
                 -> (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir))
                 -> a2 -> LntT.Coq_nslclrule
                 (Datatypes.Coq_prod a1 LntT.Coq_dir) a2
nslclrule_gen ps c g pS c0 hsr =
  Logic.eq_rect_r (List.map (LntT.nslclext g) ps)
    (Logic.eq_rect_r (LntT.nslclext g c) (LntT.NSlclctxt ps c g hsr) c0) pS

pf4_00 :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf4_00 =
  Cut.LNSKt_rules_woc (Datatypes.Coq_cons concl4_000 Datatypes.Coq_nil)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.WBox (LntT.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil))
    (Lntkt_exchT.Coq_b1l (Datatypes.Coq_cons concl4_000 Datatypes.Coq_nil)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.WBox (LntT.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil))
    (nslclrule_gen (Datatypes.Coq_cons (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair
      (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.WBox
        (LntT.Var Datatypes.O))
        (let {
          app0 l m =
            case l of {
             Datatypes.Coq_nil -> m;
             Datatypes.Coq_cons a l1 -> Datatypes.Coq_cons a (app0 l1 m)}}
         in app0 Datatypes.Coq_nil Datatypes.Coq_nil)))
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app Datatypes.Coq_nil Datatypes.Coq_nil))) LntT.Coq_fwd)
      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
      (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Var
        Datatypes.O) (Datatypes.app Datatypes.Coq_nil Datatypes.Coq_nil)))
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LntT.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil))) LntT.Coq_fwd)
      Datatypes.Coq_nil)) Datatypes.Coq_nil) (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox
      (LntT.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil)
      LntT.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Var
      Datatypes.O) Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil))
      Datatypes.Coq_nil (Datatypes.Coq_cons concl4_000 Datatypes.Coq_nil)
      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
      (Datatypes.Coq_cons (LntT.WBox (LntT.Var Datatypes.O))
      Datatypes.Coq_nil) Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil
      (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil))
      LntT.Coq_fwd) Datatypes.Coq_nil)) (Lntb1LT.WBox1Ls (LntT.Var
      Datatypes.O) LntT.Coq_fwd Datatypes.Coq_nil Datatypes.Coq_nil
      Datatypes.Coq_nil (Datatypes.app Datatypes.Coq_nil Datatypes.Coq_nil)
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app Datatypes.Coq_nil Datatypes.Coq_nil))
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LntT.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil)))))

pf4_01 :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf4_01 =
  Cut.LNSKt_rules_woc (Datatypes.Coq_cons (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil
    Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
    (Datatypes.Coq_cons (LntT.Var (Datatypes.S Datatypes.O))
    Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp (LntT.Var (Datatypes.S
    Datatypes.O)) (LntT.Var Datatypes.O)) (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil))) LntT.Coq_fwd) Datatypes.Coq_nil))
    Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.Coq_cons (LntT.Imp (LntT.Var (Datatypes.S Datatypes.O))
    (LntT.Var Datatypes.O)) Datatypes.Coq_nil)) LntT.Coq_fwd)
    Datatypes.Coq_nil)) (Lntkt_exchT.Coq_prop (Datatypes.Coq_cons
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) (Datatypes.Coq_cons (LntT.Var (Datatypes.S Datatypes.O))
    Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp (LntT.Var (Datatypes.S
    Datatypes.O)) (LntT.Var Datatypes.O)) (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil))) LntT.Coq_fwd) Datatypes.Coq_nil))
    Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.Coq_cons (LntT.Imp (LntT.Var (Datatypes.S Datatypes.O))
    (LntT.Var Datatypes.O)) Datatypes.Coq_nil)) LntT.Coq_fwd)
    Datatypes.Coq_nil))
    (nslcrule_gen
      (List.map
        (Gen_seq.seqext (Datatypes.Coq_cons (LntT.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil Datatypes.Coq_nil
          Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_cons (LntT.Var (Datatypes.S Datatypes.O))
        Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Imp (LntT.Var
        (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
        (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)))
        Datatypes.Coq_nil)) (Datatypes.Coq_pair
      (Datatypes.app (Datatypes.Coq_cons (LntT.Var Datatypes.O)
        Datatypes.Coq_nil) Datatypes.Coq_nil)
      (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp
        (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
        Datatypes.Coq_nil))) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd)
      Datatypes.Coq_nil) LntT.Coq_fwd (Datatypes.Coq_cons (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil
      Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
      Datatypes.O) (Datatypes.Coq_cons (LntT.Var (Datatypes.S Datatypes.O))
      Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp (LntT.Var
      (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O)) (Datatypes.Coq_cons
      (LntT.Var Datatypes.O) Datatypes.Coq_nil))) LntT.Coq_fwd)
      Datatypes.Coq_nil)) Datatypes.Coq_nil) (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil
      Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
      Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Imp (LntT.Var
      (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O)) Datatypes.Coq_nil))
      LntT.Coq_fwd) Datatypes.Coq_nil))
      (Gen_seq.seqrule_same
        (List.map
          (Gen_seq.seqext (Datatypes.Coq_cons (LntT.Var Datatypes.O)
            Datatypes.Coq_nil) Datatypes.Coq_nil Datatypes.Coq_nil
            Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
          (Datatypes.Coq_cons (LntT.Var (Datatypes.S Datatypes.O))
          Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Imp (LntT.Var
          (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
          (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)))
          Datatypes.Coq_nil))
        (Gen_seq.seqext (Datatypes.Coq_cons (LntT.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil Datatypes.Coq_nil
          Datatypes.Coq_nil (Datatypes.Coq_pair Datatypes.Coq_nil
          (Datatypes.Coq_cons (LntT.Imp (LntT.Var (Datatypes.S Datatypes.O))
          (LntT.Var Datatypes.O)) Datatypes.Coq_nil))) (Datatypes.Coq_pair
        (Datatypes.app (Datatypes.Coq_cons (LntT.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil)
        (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp
          (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
          Datatypes.Coq_nil))) (Gen_seq.Sctxt (Datatypes.Coq_cons
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var (Datatypes.S
        Datatypes.O)) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Imp
        (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
        (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)))
        Datatypes.Coq_nil) (Datatypes.Coq_pair Datatypes.Coq_nil
        (Datatypes.Coq_cons (LntT.Imp (LntT.Var (Datatypes.S Datatypes.O))
        (LntT.Var Datatypes.O)) Datatypes.Coq_nil)) (Datatypes.Coq_cons
        (LntT.Var Datatypes.O) Datatypes.Coq_nil) Datatypes.Coq_nil
        Datatypes.Coq_nil Datatypes.Coq_nil (LntT.ImpR_pfc (LntT.Var
        (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))))))

pf4_0 :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf4_0 =
  Cut.LNSKt_rules_wc (Datatypes.Coq_cons
    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox (LntT.Var
      Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LntT.Coq_fwd)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LntT.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil))) LntT.Coq_fwd)
      Datatypes.Coq_nil)) (Datatypes.Coq_cons
    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LntT.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil)) (Datatypes.Coq_cons
      (LntT.Imp (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
      Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil))
    Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox (LntT.Var
    Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LntT.Coq_fwd)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp (LntT.Var (Datatypes.S
    Datatypes.O)) (LntT.Var Datatypes.O)) Datatypes.Coq_nil)) LntT.Coq_fwd)
    Datatypes.Coq_nil)) (Cut.Cut (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox (LntT.Var
    Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LntT.Coq_fwd)
    Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd)
    Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox (LntT.Var
    Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LntT.Coq_fwd)
    Datatypes.Coq_nil) (Datatypes.Coq_pair Datatypes.Coq_nil
    (Datatypes.app Datatypes.Coq_nil
      (Datatypes.app (Datatypes.Coq_cons (LntT.Var Datatypes.O)
        Datatypes.Coq_nil) Datatypes.Coq_nil))) (Datatypes.Coq_pair
    (Datatypes.app Datatypes.Coq_nil
      (Datatypes.app (Datatypes.Coq_cons (LntT.Var Datatypes.O)
        Datatypes.Coq_nil) Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Imp
    (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
    Datatypes.Coq_nil)) (Datatypes.Coq_pair Datatypes.Coq_nil
    (Datatypes.Coq_cons (LntT.Imp (LntT.Var (Datatypes.S Datatypes.O))
    (LntT.Var Datatypes.O)) Datatypes.Coq_nil))
    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox (LntT.Var
      Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LntT.Coq_fwd)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LntT.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil))) LntT.Coq_fwd)
      Datatypes.Coq_nil))
    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LntT.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil)) (Datatypes.Coq_cons
      (LntT.Imp (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
      Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil))
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.WBox (LntT.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp
    (LntT.Var (Datatypes.S Datatypes.O)) (LntT.Var Datatypes.O))
    Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)) LntT.Coq_fwd
    Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil
    Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp (LntT.Var (Datatypes.S
    Datatypes.O)) (LntT.Var Datatypes.O)) Datatypes.Coq_nil) (LntT.Var
    Datatypes.O) (Merge.Coq_merge_step (Datatypes.Coq_cons (LntT.WBox
    (LntT.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil
    Datatypes.Coq_nil Datatypes.Coq_nil LntT.Coq_fwd Datatypes.Coq_nil
    Datatypes.Coq_nil Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox
    (LntT.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil)
    LntT.Coq_fwd) Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd)
    Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox (LntT.Var
    Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LntT.Coq_fwd)
    Datatypes.Coq_nil) (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.WBox (LntT.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_pair (Datatypes.Coq_pair
    Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd) (Datatypes.Coq_pair
    (Datatypes.Coq_pair
    (Datatypes.app (Datatypes.Coq_cons (LntT.WBox (LntT.Var Datatypes.O))
      Datatypes.Coq_nil) Datatypes.Coq_nil)
    (Datatypes.app Datatypes.Coq_nil Datatypes.Coq_nil)) LntT.Coq_fwd)
    (Merge.Coq_merge_nilL Datatypes.Coq_nil Datatypes.Coq_nil
    Datatypes.Coq_nil)) (Structural_equivalence.Coq_se_step2
    (Datatypes.Coq_cons (LntT.WBox (LntT.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil LntT.Coq_fwd Datatypes.Coq_nil Datatypes.Coq_nil
    Datatypes.Coq_nil Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.WBox
    (LntT.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil)
    LntT.Coq_fwd) Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LntT.Coq_fwd)
    Datatypes.Coq_nil) Structural_equivalence.Coq_se_nil2))

der4_000 :: DdT.Coq_derrec
            (Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Gen_tacs.Coq_rel
            (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
            LntT.Coq_dir)) (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
der4_000 =
  DdT.Coq_derI Datatypes.Coq_nil concl4_000 pf4_000 coq_Ds_nil

der4_010 :: DdT.Coq_derrec
            (Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Gen_tacs.Coq_rel
            (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
            LntT.Coq_dir)) (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
der4_010 =
  DdT.Coq_derI Datatypes.Coq_nil concl4_010 pf4_010 coq_Ds_nil

der4_00 :: DdT.Coq_derrec
           (Datatypes.Coq_list
           (Datatypes.Coq_prod
           (Gen_tacs.Coq_rel
           (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir))
           (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
der4_00 =
  DdT.Coq_derI (Datatypes.Coq_cons concl4_000 Datatypes.Coq_nil) concl4_00
    pf4_00 (DdT.Coq_dlCons concl4_000 Datatypes.Coq_nil der4_000 coq_Ds_nil)

der4_01 :: DdT.Coq_derrec
           (Datatypes.Coq_list
           (Datatypes.Coq_prod
           (Gen_tacs.Coq_rel
           (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir))
           (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
der4_01 =
  DdT.Coq_derI (Datatypes.Coq_cons concl4_010 Datatypes.Coq_nil) concl4_01
    pf4_01 (DdT.Coq_dlCons concl4_010 Datatypes.Coq_nil der4_010 coq_Ds_nil)

der4_0 :: DdT.Coq_derrec
          (Datatypes.Coq_list
          (Datatypes.Coq_prod
          (Gen_tacs.Coq_rel
          (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir))
          (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
der4_0 =
  DdT.Coq_derI (Datatypes.Coq_cons concl4_00 (Datatypes.Coq_cons concl4_01
    Datatypes.Coq_nil)) concl4_0 pf4_0 (DdT.Coq_dlCons concl4_00
    (Datatypes.Coq_cons concl4_01 Datatypes.Coq_nil) der4_00 (DdT.Coq_dlCons
    concl4_01 Datatypes.Coq_nil der4_01 coq_Ds_nil))

example4 :: DdT.Coq_derrec
            (Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Gen_tacs.Coq_rel
            (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
            LntT.Coq_dir)) (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
example4 =
  der4_0

cut_example4 :: DdT.Coq_derrec
                (Datatypes.Coq_list
                (Datatypes.Coq_prod
                (Gen_tacs.Coq_rel
                (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
                LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Datatypes.Coq_nat) 
                ()
cut_example4 =
  Cut.coq_LNSKt_cut_elimination concl4_0 example4

