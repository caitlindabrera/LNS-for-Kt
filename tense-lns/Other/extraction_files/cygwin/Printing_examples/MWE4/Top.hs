module Top where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Logic
import qualified Gen_seq
import qualified Gen_tacs
import qualified LntT

data Coq_derrec x rules prems =
   Coq_dpI x prems
 | Coq_derI (Datatypes.Coq_list x) x rules (Coq_dersrec x rules prems)
data Coq_dersrec x rules prems =
   Coq_dlNil
 | Coq_dlCons x (Datatypes.Coq_list x) (Coq_derrec x rules prems) (Coq_dersrec 
                                                                  x rules prems)

derrec_same :: a1 -> a1 -> (Coq_derrec a1 a2 a3) -> Coq_derrec a1 a2 a3
derrec_same c c' x0 =
  Logic.eq_rect_r c' (\x1 -> x1) c x0

data Coq_b2rrules v =
   WBox2Rs (LntT.PropF v) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                              (LntT.PropF v)) 
 (Datatypes.Coq_list (LntT.PropF v))
 | BBox2Rs (LntT.PropF v) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                              (LntT.PropF v)) 
 (Datatypes.Coq_list (LntT.PropF v))

data Coq_b1rrules v =
   WBox1Rs (LntT.PropF v) LntT.Coq_dir (Datatypes.Coq_list (LntT.PropF v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                                         (LntT.PropF
                                                                         v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v))
 | BBox1Rs (LntT.PropF v) LntT.Coq_dir (Datatypes.Coq_list (LntT.PropF v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                                         (LntT.PropF
                                                                         v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v))

data Coq_b1lrules v =
   WBox1Ls (LntT.PropF v) LntT.Coq_dir (Datatypes.Coq_list (LntT.PropF v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                                         (LntT.PropF
                                                                         v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v))
 | BBox1Ls (LntT.PropF v) LntT.Coq_dir (Datatypes.Coq_list (LntT.PropF v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                                         (LntT.PropF
                                                                         v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v))

data Coq_b2lrules v =
   WBox2Ls (LntT.PropF v) LntT.Coq_dir (Datatypes.Coq_list (LntT.PropF v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                                         (LntT.PropF
                                                                         v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v))
 | BBox2Ls (LntT.PropF v) LntT.Coq_dir (Datatypes.Coq_list (LntT.PropF v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                                         (LntT.PropF
                                                                         v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v))

data EW_rule v =
   EW (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) 
 LntT.Coq_dir

data LNSKt_rules v =
   Coq_b2r (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod
           (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
 LntT.Coq_dir)) (LntT.Coq_nslclrule
                (Datatypes.Coq_prod
                (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                LntT.Coq_dir) (Coq_b2rrules v))
 | Coq_b1r (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod
           (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
 LntT.Coq_dir)) (LntT.Coq_nslclrule
                (Datatypes.Coq_prod
                (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                LntT.Coq_dir) (Coq_b1rrules v))
 | Coq_b2l (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod
           (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
 LntT.Coq_dir)) (LntT.Coq_nslclrule
                (Datatypes.Coq_prod
                (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                LntT.Coq_dir) (Coq_b2lrules v))
 | Coq_b1l (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod
           (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
 LntT.Coq_dir)) (LntT.Coq_nslclrule
                (Datatypes.Coq_prod
                (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                LntT.Coq_dir) (Coq_b1lrules v))
 | Coq_nEW (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod
           (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
 LntT.Coq_dir)) (LntT.Coq_nslclrule
                (Datatypes.Coq_prod
                (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                LntT.Coq_dir) (EW_rule v))
 | Coq_prop (Datatypes.Coq_list
            (Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
 LntT.Coq_dir)) (LntT.Coq_nslcrule
                (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                (Gen_seq.Coq_seqrule (LntT.PropF v) (LntT.Coq_princrule_pfc v)))

nslcrule_gen :: (Datatypes.Coq_list a1) -> a1 -> (Datatypes.Coq_list
                (Datatypes.Coq_prod a1 LntT.Coq_dir)) -> LntT.Coq_dir ->
                (Datatypes.Coq_list
                (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir))) ->
                (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir)) -> a2 ->
                LntT.Coq_nslcrule a1 a2
nslcrule_gen ps c g d pS c0 x =
  Logic.eq_rect_r (List.map (LntT.nslcext g d) ps)
    (Logic.eq_rect_r (LntT.nslcext g d c) (LntT.NSlcctxt ps c g d x) c0) pS

pf :: LNSKt_rules Datatypes.Coq_nat
pf =
  Coq_prop Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
    Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
    Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)
    (nslcrule_gen Datatypes.Coq_nil (Datatypes.Coq_pair (Datatypes.Coq_cons
      (LntT.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
      Datatypes.O) Datatypes.Coq_nil)) Datatypes.Coq_nil LntT.Coq_fwd
      Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
      (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
      (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)) LntT.Coq_fwd)
      Datatypes.Coq_nil)
      (Logic.eq_rect
        (Gen_seq.seqext Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil
          Datatypes.Coq_nil (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
          Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
          Datatypes.O) Datatypes.Coq_nil)))
        (Gen_seq.coq_Sctxt_nil (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
          Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
          Datatypes.O) Datatypes.Coq_nil)) Datatypes.Coq_nil Datatypes.Coq_nil
          Datatypes.Coq_nil Datatypes.Coq_nil (LntT.Id_pfc Datatypes.O))
        (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
        Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
        Datatypes.Coq_nil))))

example1 :: Coq_derrec
            (Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
            LntT.Coq_dir)) (LNSKt_rules Datatypes.Coq_nat) ()
example1 =
  Coq_derI Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
    Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
    Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil) pf Coq_dlNil

swap_example2 :: Coq_derrec
                 (Datatypes.Coq_list
                 (Datatypes.Coq_prod
                 (Gen_tacs.Coq_rel
                 (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir))
                 (LNSKt_rules Datatypes.Coq_nat) ()
swap_example2 =
  derrec_same (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)) LntT.Coq_fwd)
    Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Var Datatypes.O)
      Datatypes.Coq_nil)) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
    Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil) example1

