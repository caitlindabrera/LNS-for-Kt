module Cut_extraction_example_pre where

import qualified Prelude
import qualified Datatypes
import qualified LNS
import qualified LNSKt_calculus
import qualified List
import qualified Logic
import qualified Cut
import qualified DdT
import qualified Gen_seq
import qualified Merge
import qualified Rules_b1l
import qualified Rules_prop
import qualified Structural_equivalence

coq_Ds_nil :: DdT.Coq_dersrec (LNS.LNS Datatypes.Coq_nat)
              (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
coq_Ds_nil =
  DdT.Coq_dlNil

concl3_0 :: Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Datatypes.Coq_prod
            (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))
            (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))) LNS.Coq_dir)
concl3_0 =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Imp
    (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
    Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil)

concl3_00 :: Datatypes.Coq_list
             (Datatypes.Coq_prod
             (Datatypes.Coq_prod
             (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))
             (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))) LNS.Coq_dir)
concl3_00 =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Var
    Datatypes.O) Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil)

concl3_000 :: Datatypes.Coq_list
              (Datatypes.Coq_prod
              (Datatypes.Coq_prod
              (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))
              (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat)))
              LNS.Coq_dir)
concl3_000 =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
    Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Var Datatypes.O)
    Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil)

concl3_01 :: Datatypes.Coq_list
             (Datatypes.Coq_prod
             (Datatypes.Coq_prod
             (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))
             (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))) LNS.Coq_dir)
concl3_01 =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var
    Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Imp (LNS.Var
    (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O)) Datatypes.Coq_nil))
    LNS.Coq_fwd) Datatypes.Coq_nil)

concl3_010 :: Datatypes.Coq_list
              (Datatypes.Coq_prod
              (Datatypes.Coq_prod
              (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))
              (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat)))
              LNS.Coq_dir)
concl3_010 =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var
    Datatypes.O) (Datatypes.Coq_cons (LNS.Var (Datatypes.S Datatypes.O))
    Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S
    Datatypes.O)) (LNS.Var Datatypes.O)) (Datatypes.Coq_cons (LNS.Var
    Datatypes.O) Datatypes.Coq_nil))) LNS.Coq_fwd) Datatypes.Coq_nil)

pf3_000 :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf3_000 =
  Cut.LNSKt_rules_woc Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox
    (LNS.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil))
    LNS.Coq_fwd) Datatypes.Coq_nil))
    (Logic.eq_rect_r
      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox (LNS.Var
        Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd)
        Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
        Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Var Datatypes.O)
        Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
      (LNSKt_calculus.Coq_prop Datatypes.Coq_nil
      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox (LNS.Var
        Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd)
        Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
        Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Var Datatypes.O)
        Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
      (LNS.nslcrule_gen Datatypes.Coq_nil (Datatypes.Coq_pair
        (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil)
        (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil))
        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
        (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O))
        Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd) Datatypes.Coq_nil)
        LNS.Coq_fwd Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
          (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox (LNS.Var
          Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd)
          Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
          (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
          Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Var Datatypes.O)
          Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
        (Gen_seq.seqrule_id Datatypes.Coq_nil (Datatypes.Coq_pair
          (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil)
          (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil))
          (Rules_prop.Id Datatypes.O)))) (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox
      (LNS.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil)
      LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Var Datatypes.O)
      Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil)))

pf3_010 :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf3_010 =
  Cut.LNSKt_rules_woc Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil
    Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
    (Datatypes.Coq_cons (LNS.Var (Datatypes.S Datatypes.O))
    Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S
    Datatypes.O)) (LNS.Var Datatypes.O)) (Datatypes.Coq_cons (LNS.Var
    Datatypes.O) Datatypes.Coq_nil))) LNS.Coq_fwd) Datatypes.Coq_nil))
    (Logic.eq_rect_r
      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd)
        Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
        (Datatypes.Coq_cons (LNS.Var (Datatypes.S Datatypes.O))
        Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp (LNS.Var
        (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O)) (Datatypes.Coq_cons
        (LNS.Var Datatypes.O) Datatypes.Coq_nil))) LNS.Coq_fwd)
        Datatypes.Coq_nil)) (LNSKt_calculus.Coq_prop Datatypes.Coq_nil
      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd)
        Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
        (Datatypes.Coq_cons (LNS.Var (Datatypes.S Datatypes.O))
        Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp (LNS.Var
        (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O)) (Datatypes.Coq_cons
        (LNS.Var Datatypes.O) Datatypes.Coq_nil))) LNS.Coq_fwd)
        Datatypes.Coq_nil))
      (LNS.nslcrule_gen Datatypes.Coq_nil (Datatypes.Coq_pair
        (Datatypes.Coq_cons (LNS.Var Datatypes.O) (Datatypes.Coq_cons
        (LNS.Var (Datatypes.S Datatypes.O)) Datatypes.Coq_nil))
        (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S Datatypes.O))
        (LNS.Var Datatypes.O)) (Datatypes.Coq_cons (LNS.Var Datatypes.O)
        Datatypes.Coq_nil))) (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd)
        Datatypes.Coq_nil) LNS.Coq_fwd Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
          (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil)
          LNS.Coq_fwd) Datatypes.Coq_nil) (Datatypes.Coq_cons
          (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons
          (LNS.Var Datatypes.O) (Datatypes.Coq_cons (LNS.Var (Datatypes.S
          Datatypes.O)) Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp
          (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
          (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil)))
          LNS.Coq_fwd) Datatypes.Coq_nil))
        (Gen_seq.seqrule_same Datatypes.Coq_nil
          (Gen_seq.seqext Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Var
            (Datatypes.S Datatypes.O)) Datatypes.Coq_nil) (Datatypes.Coq_cons
            (LNS.Imp (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var
            Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil
            (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
            Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Var Datatypes.O)
            Datatypes.Coq_nil))) (Datatypes.Coq_pair (Datatypes.Coq_cons
          (LNS.Var Datatypes.O) (Datatypes.Coq_cons (LNS.Var (Datatypes.S
          Datatypes.O)) Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp
          (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
          (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil)))
          (Gen_seq.coq_Sctxt_nil (Datatypes.Coq_pair (Datatypes.Coq_cons
            (LNS.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons
            (LNS.Var Datatypes.O) Datatypes.Coq_nil)) Datatypes.Coq_nil
            (Datatypes.Coq_cons (LNS.Var (Datatypes.S Datatypes.O))
            Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Imp (LNS.Var
            (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
            Datatypes.Coq_nil) Datatypes.Coq_nil (Rules_prop.Id Datatypes.O)))))
      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
      Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var
      Datatypes.O) (Datatypes.Coq_cons (LNS.Var (Datatypes.S Datatypes.O))
      Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S
      Datatypes.O)) (LNS.Var Datatypes.O)) (Datatypes.Coq_cons (LNS.Var
      Datatypes.O) Datatypes.Coq_nil))) LNS.Coq_fwd) Datatypes.Coq_nil)))

pf3_00 :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf3_00 =
  Cut.LNSKt_rules_woc (Datatypes.Coq_cons concl3_000 Datatypes.Coq_nil)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Var
    Datatypes.O) Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
    (LNSKt_calculus.Coq_b1l (Datatypes.Coq_cons concl3_000 Datatypes.Coq_nil)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Var
    Datatypes.O) Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
    (LNS.nslclrule_gen (Datatypes.Coq_cons (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair
      (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.WBox (LNS.Var
        Datatypes.O))
        (let {
          app0 l m =
            case l of {
             Datatypes.Coq_nil -> m;
             Datatypes.Coq_cons a l1 -> Datatypes.Coq_cons a (app0 l1 m)}}
         in app0 Datatypes.Coq_nil Datatypes.Coq_nil)))
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app Datatypes.Coq_nil Datatypes.Coq_nil))) LNS.Coq_fwd)
      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
      (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Var
        Datatypes.O) (Datatypes.app Datatypes.Coq_nil Datatypes.Coq_nil)))
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LNS.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil))) LNS.Coq_fwd)
      Datatypes.Coq_nil)) Datatypes.Coq_nil) (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox
      (LNS.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil)
      LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Var
      Datatypes.O) Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
      Datatypes.Coq_nil (Datatypes.Coq_cons concl3_000 Datatypes.Coq_nil)
      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
      (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O)) Datatypes.Coq_nil)
      Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Var
      Datatypes.O) Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
      (Rules_b1l.WBox1Ls (LNS.Var Datatypes.O) LNS.Coq_fwd Datatypes.Coq_nil
      Datatypes.Coq_nil Datatypes.Coq_nil
      (Datatypes.app Datatypes.Coq_nil Datatypes.Coq_nil)
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app Datatypes.Coq_nil Datatypes.Coq_nil))
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LNS.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil)))))

pf3_01 :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf3_01 =
  Cut.LNSKt_rules_woc (Datatypes.Coq_cons (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil
    Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
    (Datatypes.Coq_cons (LNS.Var (Datatypes.S Datatypes.O))
    Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S
    Datatypes.O)) (LNS.Var Datatypes.O)) (Datatypes.Coq_cons (LNS.Var
    Datatypes.O) Datatypes.Coq_nil))) LNS.Coq_fwd) Datatypes.Coq_nil))
    Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var
    Datatypes.O)) Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
    (LNSKt_calculus.Coq_prop (Datatypes.Coq_cons (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil
    Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
    (Datatypes.Coq_cons (LNS.Var (Datatypes.S Datatypes.O))
    Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S
    Datatypes.O)) (LNS.Var Datatypes.O)) (Datatypes.Coq_cons (LNS.Var
    Datatypes.O) Datatypes.Coq_nil))) LNS.Coq_fwd) Datatypes.Coq_nil))
    Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var
    Datatypes.O)) Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
    (LNS.nslcrule_gen
      (List.map
        (Gen_seq.seqext (Datatypes.Coq_cons (LNS.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil Datatypes.Coq_nil
          Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_cons (LNS.Var (Datatypes.S Datatypes.O))
        Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S
        Datatypes.O)) (LNS.Var Datatypes.O)) (Datatypes.Coq_cons (LNS.Var
        Datatypes.O) Datatypes.Coq_nil))) Datatypes.Coq_nil))
      (Datatypes.Coq_pair
      (Datatypes.app (Datatypes.Coq_cons (LNS.Var Datatypes.O)
        Datatypes.Coq_nil) Datatypes.Coq_nil)
      (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Imp (LNS.Var
        (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O)) Datatypes.Coq_nil)))
      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
      Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd) Datatypes.Coq_nil)
      LNS.Coq_fwd (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd)
      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
      (Datatypes.Coq_cons (LNS.Var Datatypes.O) (Datatypes.Coq_cons (LNS.Var
      (Datatypes.S Datatypes.O)) Datatypes.Coq_nil)) (Datatypes.Coq_cons
      (LNS.Imp (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
      (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil)))
      LNS.Coq_fwd) Datatypes.Coq_nil)) Datatypes.Coq_nil) (Datatypes.Coq_cons
      (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil
      Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var Datatypes.O)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S
      Datatypes.O)) (LNS.Var Datatypes.O)) Datatypes.Coq_nil)) LNS.Coq_fwd)
      Datatypes.Coq_nil))
      (Gen_seq.seqrule_same
        (List.map
          (Gen_seq.seqext (Datatypes.Coq_cons (LNS.Var Datatypes.O)
            Datatypes.Coq_nil) Datatypes.Coq_nil Datatypes.Coq_nil
            Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
          (Datatypes.Coq_cons (LNS.Var (Datatypes.S Datatypes.O))
          Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Imp (LNS.Var
          (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
          (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil)))
          Datatypes.Coq_nil))
        (Gen_seq.seqext (Datatypes.Coq_cons (LNS.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil Datatypes.Coq_nil
          Datatypes.Coq_nil (Datatypes.Coq_pair Datatypes.Coq_nil
          (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S Datatypes.O))
          (LNS.Var Datatypes.O)) Datatypes.Coq_nil))) (Datatypes.Coq_pair
        (Datatypes.app (Datatypes.Coq_cons (LNS.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil)
        (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Imp
          (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
          Datatypes.Coq_nil))) (Gen_seq.Sctxt (Datatypes.Coq_cons
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.Var (Datatypes.S
        Datatypes.O)) Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Imp
        (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
        (Datatypes.Coq_cons (LNS.Var Datatypes.O) Datatypes.Coq_nil)))
        Datatypes.Coq_nil) (Datatypes.Coq_pair Datatypes.Coq_nil
        (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S Datatypes.O))
        (LNS.Var Datatypes.O)) Datatypes.Coq_nil)) (Datatypes.Coq_cons
        (LNS.Var Datatypes.O) Datatypes.Coq_nil) Datatypes.Coq_nil
        Datatypes.Coq_nil Datatypes.Coq_nil (Rules_prop.ImpR (LNS.Var
        (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))))))

pf3_0 :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf3_0 =
  Cut.LNSKt_rules_wc (Datatypes.Coq_cons
    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox (LNS.Var
      Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LNS.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil))) LNS.Coq_fwd)
      Datatypes.Coq_nil)) (Datatypes.Coq_cons
    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LNS.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp
      (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
      Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
    Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O))
    Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil
    (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var
    Datatypes.O)) Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
    (Cut.Cut (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LNS.Coq_fwd) Datatypes.Coq_nil) (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil
    Datatypes.Coq_nil) LNS.Coq_fwd) Datatypes.Coq_nil) (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox
    (LNS.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd)
    Datatypes.Coq_nil) (Datatypes.Coq_pair Datatypes.Coq_nil
    (Datatypes.app Datatypes.Coq_nil
      (Datatypes.app (Datatypes.Coq_cons (LNS.Var Datatypes.O)
        Datatypes.Coq_nil) Datatypes.Coq_nil))) (Datatypes.Coq_pair
    (Datatypes.app Datatypes.Coq_nil
      (Datatypes.app (Datatypes.Coq_cons (LNS.Var Datatypes.O)
        Datatypes.Coq_nil) Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp
    (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
    Datatypes.Coq_nil)) (Datatypes.Coq_pair Datatypes.Coq_nil
    (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var
    Datatypes.O)) Datatypes.Coq_nil))
    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox (LNS.Var
      Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LNS.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil))) LNS.Coq_fwd)
      Datatypes.Coq_nil))
    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app (Datatypes.Coq_cons (LNS.Var Datatypes.O)
          Datatypes.Coq_nil) Datatypes.Coq_nil)) (Datatypes.Coq_cons (LNS.Imp
      (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
      Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil))
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Imp
    (LNS.Var (Datatypes.S Datatypes.O)) (LNS.Var Datatypes.O))
    Datatypes.Coq_nil)) LNS.Coq_fwd) Datatypes.Coq_nil)) LNS.Coq_fwd
    Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil
    Datatypes.Coq_nil (Datatypes.Coq_cons (LNS.Imp (LNS.Var (Datatypes.S
    Datatypes.O)) (LNS.Var Datatypes.O)) Datatypes.Coq_nil) (LNS.Var
    Datatypes.O) (Merge.Coq_merge_step (Datatypes.Coq_cons (LNS.WBox (LNS.Var
    Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil Datatypes.Coq_nil
    Datatypes.Coq_nil LNS.Coq_fwd Datatypes.Coq_nil Datatypes.Coq_nil
    Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O))
    Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd) Datatypes.Coq_nil)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd) Datatypes.Coq_nil)
    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil) LNS.Coq_fwd) Datatypes.Coq_nil) (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O))
    Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd) (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd)
    (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.app (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O))
      Datatypes.Coq_nil) Datatypes.Coq_nil)
    (Datatypes.app Datatypes.Coq_nil Datatypes.Coq_nil)) LNS.Coq_fwd)
    (Merge.Coq_merge_nilL Datatypes.Coq_nil Datatypes.Coq_nil
    Datatypes.Coq_nil)) (Structural_equivalence.Coq_se_step2
    (Datatypes.Coq_cons (LNS.WBox (LNS.Var Datatypes.O)) Datatypes.Coq_nil)
    Datatypes.Coq_nil LNS.Coq_fwd Datatypes.Coq_nil Datatypes.Coq_nil
    Datatypes.Coq_nil Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LNS.WBox
    (LNS.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) LNS.Coq_fwd)
    Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair Datatypes.Coq_nil Datatypes.Coq_nil) LNS.Coq_fwd)
    Datatypes.Coq_nil) Structural_equivalence.Coq_se_nil2))

der3_000 :: DdT.Coq_derrec
            (Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Datatypes.Coq_prod
            (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))
            (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))) LNS.Coq_dir))
            (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
der3_000 =
  DdT.Coq_derI Datatypes.Coq_nil concl3_000 pf3_000 coq_Ds_nil

der3_010 :: DdT.Coq_derrec
            (Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Datatypes.Coq_prod
            (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))
            (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))) LNS.Coq_dir))
            (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
der3_010 =
  DdT.Coq_derI Datatypes.Coq_nil concl3_010 pf3_010 coq_Ds_nil

der3_00 :: DdT.Coq_derrec
           (Datatypes.Coq_list
           (Datatypes.Coq_prod
           (Datatypes.Coq_prod
           (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))
           (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))) LNS.Coq_dir))
           (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
der3_00 =
  DdT.Coq_derI (Datatypes.Coq_cons concl3_000 Datatypes.Coq_nil) concl3_00
    pf3_00 (DdT.Coq_dlCons concl3_000 Datatypes.Coq_nil der3_000 coq_Ds_nil)

der3_01 :: DdT.Coq_derrec
           (Datatypes.Coq_list
           (Datatypes.Coq_prod
           (Datatypes.Coq_prod
           (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))
           (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))) LNS.Coq_dir))
           (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
der3_01 =
  DdT.Coq_derI (Datatypes.Coq_cons concl3_010 Datatypes.Coq_nil) concl3_01
    pf3_01 (DdT.Coq_dlCons concl3_010 Datatypes.Coq_nil der3_010 coq_Ds_nil)

der3_0 :: DdT.Coq_derrec
          (Datatypes.Coq_list
          (Datatypes.Coq_prod
          (Datatypes.Coq_prod
          (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))
          (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))) LNS.Coq_dir))
          (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
der3_0 =
  DdT.Coq_derI (Datatypes.Coq_cons concl3_00 (Datatypes.Coq_cons concl3_01
    Datatypes.Coq_nil)) concl3_0 pf3_0 (DdT.Coq_dlCons concl3_00
    (Datatypes.Coq_cons concl3_01 Datatypes.Coq_nil) der3_00 (DdT.Coq_dlCons
    concl3_01 Datatypes.Coq_nil der3_01 coq_Ds_nil))

example3 :: DdT.Coq_derrec
            (Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Datatypes.Coq_prod
            (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))
            (Datatypes.Coq_list (LNS.PropF Datatypes.Coq_nat))) LNS.Coq_dir))
            (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
example3 =
  der3_0

cut_example3 :: LNSKt_calculus.Coq_pf_LNSKt Datatypes.Coq_nat
cut_example3 =
  Cut.coq_LNSKt_cut_elimination concl3_0 example3

