module LNS where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Logic
import qualified Gen_tacs

data PropF v =
   Var v
 | Bot
 | Imp (PropF v) (PropF v)
 | WBox (PropF v)
 | BBox (PropF v)

data Coq_dir =
   Coq_fwd
 | Coq_bac

type Coq_seq v = Gen_tacs.Coq_rel (Datatypes.Coq_list (PropF v))

type LNS v = Datatypes.Coq_list (Datatypes.Coq_prod (Coq_seq v) Coq_dir)

nslcext :: (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)) -> Coq_dir ->
           a1 -> Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)
nslcext g d s =
  Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d)
    Datatypes.Coq_nil)

data Coq_nslcrule w sr =
   NSlcctxt (Datatypes.Coq_list w) w (Datatypes.Coq_list
                                     (Datatypes.Coq_prod w Coq_dir)) 
 Coq_dir sr

coq_NSlcctxt_nil :: (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)) ->
                    Coq_dir -> a1 -> a2 -> Coq_nslcrule a1 a2
coq_NSlcctxt_nil g d c h =
  NSlcctxt Datatypes.Coq_nil c g d h

coq_NSlcctxt' :: (Datatypes.Coq_list a1) -> a1 -> (Datatypes.Coq_list
                 (Datatypes.Coq_prod a1 Coq_dir)) -> Coq_dir -> a2 ->
                 Coq_nslcrule a1 a2
coq_NSlcctxt' ps c g d x =
  Logic.eq_rect (nslcext g d c) (NSlcctxt ps c g d x)
    (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair c d)
      Datatypes.Coq_nil))

nslclext :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
            Datatypes.Coq_list a1
nslclext =
  Datatypes.app

data Coq_nslclrule w sr =
   NSlclctxt (Datatypes.Coq_list (Datatypes.Coq_list w)) (Datatypes.Coq_list
                                                         w) (Datatypes.Coq_list
                                                            w) sr

coq_NSlclctxt' :: (Datatypes.Coq_list (Datatypes.Coq_list a1)) ->
                  (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> a2 ->
                  Coq_nslclrule a1 a2
coq_NSlclctxt' ps c g x =
  Logic.eq_rect (nslclext g c) (NSlclctxt ps c g x) (Datatypes.app g c)

nslcrule_gen :: (Datatypes.Coq_list a1) -> a1 -> (Datatypes.Coq_list
                (Datatypes.Coq_prod a1 Coq_dir)) -> Coq_dir ->
                (Datatypes.Coq_list
                (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir))) ->
                (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)) -> a2 ->
                Coq_nslcrule a1 a2
nslcrule_gen ps c g d pS c0 x =
  Logic.eq_rect_r (List.map (nslcext g d) ps)
    (Logic.eq_rect_r (nslcext g d c) (NSlcctxt ps c g d x) c0) pS

nslclrule_gen :: (Datatypes.Coq_list
                 (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir))) ->
                 (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)) ->
                 (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)) ->
                 (Datatypes.Coq_list
                 (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir))) ->
                 (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)) -> a2
                 -> Coq_nslclrule (Datatypes.Coq_prod a1 Coq_dir) a2
nslclrule_gen ps c g pS c0 hsr =
  Logic.eq_rect_r (List.map (nslclext g) ps)
    (Logic.eq_rect_r (nslclext g c) (NSlclctxt ps c g hsr) c0) pS

