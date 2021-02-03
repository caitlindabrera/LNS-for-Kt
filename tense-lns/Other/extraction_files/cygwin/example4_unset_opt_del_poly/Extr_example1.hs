module Extr_example1 where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Logic
import qualified Cut
import qualified DdT
import qualified Gen_seq
import qualified Gen_tacs
import qualified LntT
import qualified Lntkt_exchT

nslcrule_gen :: (Datatypes.Coq_list a1) -> a1 -> (Datatypes.Coq_list
                (Datatypes.Coq_prod a1 LntT.Coq_dir)) -> LntT.Coq_dir ->
                (Datatypes.Coq_list
                (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir))) ->
                (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir)) ->
                a2 -> LntT.Coq_nslcrule a1 a2
nslcrule_gen ps c g d pS c0 x =
  Logic.eq_rect_r (List.map (LntT.nslcext g d) ps)
    (Logic.eq_rect_r (LntT.nslcext g d c) (LntT.NSlcctxt ps c g d x) c0) pS

pf_wc :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf_wc =
  Cut.LNSKt_rules_woc Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)
    (Lntkt_exchT.Coq_prop Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)
    (nslcrule_gen Datatypes.Coq_nil (Datatypes.Coq_pair (Datatypes.Coq_cons
      (LntT.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
      Datatypes.O) Datatypes.Coq_nil)) Datatypes.Coq_nil LntT.Coq_fwd
      Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
      Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)
      (Logic.eq_rect
        (Gen_seq.seqext Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil
          Datatypes.Coq_nil (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
          Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
          Datatypes.O) Datatypes.Coq_nil)))
        (Gen_seq.coq_Sctxt_nil (Datatypes.Coq_pair (Datatypes.Coq_cons
          (LntT.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons
          (LntT.Var Datatypes.O) Datatypes.Coq_nil)) Datatypes.Coq_nil
          Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil (LntT.Id_pfc
          Datatypes.O)) (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
        Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
        Datatypes.O) Datatypes.Coq_nil)))))

seq :: Datatypes.Coq_list
       (Datatypes.Coq_prod
       (Datatypes.Coq_prod
       (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))
       (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir)
seq =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil))
    LntT.Coq_fwd) Datatypes.Coq_nil

example2 :: DdT.Coq_derrec
            (Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Gen_tacs.Coq_rel
            (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
            LntT.Coq_dir)) (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
example2 =
  DdT.Coq_derI Datatypes.Coq_nil seq pf_wc DdT.Coq_dlNil

cut_example2 :: DdT.Coq_derrec
                (Datatypes.Coq_list
                (Datatypes.Coq_prod
                (Gen_tacs.Coq_rel
                (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
                LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Datatypes.Coq_nat) 
                ()
cut_example2 =
  Cut.coq_LNSKt_cut_elimination seq example2

