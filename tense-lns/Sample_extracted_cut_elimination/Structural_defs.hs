module Structural_defs where

import qualified Prelude
import qualified CRelationClasses
import qualified Datatypes
import qualified LNS
import qualified Logic
import qualified ContractedT
import qualified DdT
import qualified Gen_tacs
import qualified SwappedT
import qualified WeakenedT

__ :: any
__ = Prelude.error "Logical or arity value used"

type Coq_can_gen_swapL v rules =
  (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_prod
  (Datatypes.Coq_list (LNS.PropF v)) (Datatypes.Coq_list (LNS.PropF v))) ->
  LNS.Coq_dir -> (Datatypes.Coq_list (LNS.PropF v)) -> (Datatypes.Coq_list
  (LNS.PropF v)) -> (Datatypes.Coq_list (LNS.PropF v)) -> (Datatypes.Coq_list
  (LNS.PropF v)) -> (Datatypes.Coq_list (LNS.PropF v)) -> () -> () ->
  DdT.Coq_pf (LNS.LNS v) rules

type Coq_can_gen_swapR v rules =
  (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_prod
  (Datatypes.Coq_list (LNS.PropF v)) (Datatypes.Coq_list (LNS.PropF v))) ->
  LNS.Coq_dir -> (Datatypes.Coq_list (LNS.PropF v)) -> (Datatypes.Coq_list
  (LNS.PropF v)) -> (Datatypes.Coq_list (LNS.PropF v)) -> (Datatypes.Coq_list
  (LNS.PropF v)) -> (Datatypes.Coq_list (LNS.PropF v)) -> () -> () ->
  DdT.Coq_pf (LNS.LNS v) rules

can_gen_swapL_def' :: (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      CRelationClasses.Coq_iffT (Coq_can_gen_swapL a1 a2)
                      ((Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir ->
                      (SwappedT.Coq_swapped (LNS.PropF a1)) -> () -> () ->
                      DdT.Coq_pf (LNS.LNS a1) a2)
can_gen_swapL_def' ns =
  Datatypes.Coq_pair (\x g k s _ _UU0394_ _ d h _ _ ->
    (case h of {
      SwappedT.Coq_swapped_I x0 y a b c d0 -> (\_ ->
       Logic.eq_rect_r
         (Datatypes.app a (Datatypes.app b (Datatypes.app c d0))) (\_ ->
         Logic.eq_rect_r
           (Datatypes.app a (Datatypes.app c (Datatypes.app b d0)))
           (Logic.eq_rect_r
             (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d)
               k)) (\x1 ->
             Logic.eq_rect_r (Datatypes.Coq_pair
               (Datatypes.app a (Datatypes.app b (Datatypes.app c d0)))
               _UU0394_) (\x2 ->
               x2 g k (Datatypes.Coq_pair
                 (Datatypes.app a (Datatypes.app b (Datatypes.app c d0)))
                 _UU0394_) d a b c d0 _UU0394_ __ __) s x1) ns x) y) x0 __)})
      __) (\x g k s d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ _ _ ->
    x g k s
      (Datatypes.app _UU0393_1
        (Datatypes.app _UU0393_2 (Datatypes.app _UU0393_3 _UU0393_4)))
      _UU0394_
      (Datatypes.app _UU0393_1
        (Datatypes.app _UU0393_3 (Datatypes.app _UU0393_2 _UU0393_4))) d
      (SwappedT.swapped_I' _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4) __ __)

can_gen_swapR_def' :: (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      CRelationClasses.Coq_iffT (Coq_can_gen_swapR a1 a2)
                      ((Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir ->
                      (SwappedT.Coq_swapped (LNS.PropF a1)) -> () -> () ->
                      DdT.Coq_pf (LNS.LNS a1) a2)
can_gen_swapR_def' ns =
  Datatypes.Coq_pair (\x g k s _UU0393_ _ _ d h _ _ ->
    (case h of {
      SwappedT.Coq_swapped_I x0 y a b c d0 -> (\_ ->
       Logic.eq_rect_r
         (Datatypes.app a (Datatypes.app b (Datatypes.app c d0))) (\_ ->
         Logic.eq_rect_r
           (Datatypes.app a (Datatypes.app c (Datatypes.app b d0)))
           (Logic.eq_rect_r
             (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d)
               k)) (\x1 ->
             Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_
               (Datatypes.app a (Datatypes.app b (Datatypes.app c d0))))
               (\x2 ->
               x2 g k (Datatypes.Coq_pair _UU0393_
                 (Datatypes.app a (Datatypes.app b (Datatypes.app c d0)))) d
                 a b c d0 _UU0393_ __ __) s x1) ns x) y) x0 __)}) __)
    (\x g k s d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ _ _ ->
    x g k s _UU0393_
      (Datatypes.app _UU0394_1
        (Datatypes.app _UU0394_2 (Datatypes.app _UU0394_3 _UU0394_4)))
      (Datatypes.app _UU0394_1
        (Datatypes.app _UU0394_3 (Datatypes.app _UU0394_2 _UU0394_4))) d
      (SwappedT.swapped_I' _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4) __ __)

can_gen_swapL_imp :: (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Coq_can_gen_swapL a1 a2) -> (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir ->
                     (SwappedT.Coq_swapped (LNS.PropF a1)) -> DdT.Coq_pf
                     (LNS.LNS a1) a2
can_gen_swapL_imp ns h g k s _UU0393_ _UU0394_ _UU0393_' d h0 =
  let {i = can_gen_swapL_def' ns} in
  case i of {
   Datatypes.Coq_pair hH1 _ ->
    hH1 h g k s _UU0393_ _UU0394_ _UU0393_' d h0 __ __}

can_gen_swapR_imp :: (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Coq_can_gen_swapR a1 a2) -> (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir ->
                     (SwappedT.Coq_swapped (LNS.PropF a1)) -> DdT.Coq_pf
                     (LNS.LNS a1) a2
can_gen_swapR_imp ns h g k s _UU0393_ _UU0394_ _UU0394_' d h0 =
  let {i = can_gen_swapR_def' ns} in
  case i of {
   Datatypes.Coq_pair hH1 _ ->
    hH1 h g k s _UU0393_ _UU0394_ _UU0394_' d h0 __ __}

can_gen_swapL_imp_rev :: (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> ((Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir
                         -> (SwappedT.Coq_swapped (LNS.PropF a1)) -> () -> ()
                         -> DdT.Coq_pf (LNS.LNS a1) a2) ->
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir
                         -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) -> DdT.Coq_pf
                         (LNS.LNS a1) a2
can_gen_swapL_imp_rev ns h g k s d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ =
  let {i = can_gen_swapL_def' ns} in
  (case i of {
    Datatypes.Coq_pair _ hH2 -> hH2 h}) g k s d _UU0393_1 _UU0393_2 _UU0393_3
    _UU0393_4 _UU0394_ __ __

can_gen_swapR_imp_rev :: (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> ((Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir
                         -> (SwappedT.Coq_swapped (LNS.PropF a1)) -> () -> ()
                         -> DdT.Coq_pf (LNS.LNS a1) a2) ->
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir
                         -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) ->
                         (Datatypes.Coq_list (LNS.PropF a1)) -> DdT.Coq_pf
                         (LNS.LNS a1) a2
can_gen_swapR_imp_rev ns h g k s d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ =
  let {i = can_gen_swapR_def' ns} in
  (case i of {
    Datatypes.Coq_pair _ hH2 -> hH2 h}) g k s d _UU0394_1 _UU0394_2 _UU0394_3
    _UU0394_4 _UU0393_ __ __

type Coq_can_gen_weakL v rules =
  (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_prod
  (Datatypes.Coq_list (LNS.PropF v)) (Datatypes.Coq_list (LNS.PropF v))) ->
  LNS.Coq_dir -> (Datatypes.Coq_list (LNS.PropF v)) -> (Datatypes.Coq_list
  (LNS.PropF v)) -> (Datatypes.Coq_list (LNS.PropF v)) -> (Datatypes.Coq_list
  (LNS.PropF v)) -> () -> () -> DdT.Coq_pf (LNS.LNS v) rules

can_gen_weakL_def' :: (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      CRelationClasses.Coq_iffT (Coq_can_gen_weakL a1 a2)
                      ((Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir ->
                      (WeakenedT.Coq_weakened (LNS.PropF a1)) -> () -> () ->
                      DdT.Coq_pf (LNS.LNS a1) a2)
can_gen_weakL_def' ns =
  Datatypes.Coq_pair (\x g k s _ _UU0394_ _ d h _ _ ->
    (case h of {
      WeakenedT.Coq_weakened_I x0 y a b c -> (\_ ->
       Logic.eq_rect_r (Datatypes.app a c) (\_ ->
         Logic.eq_rect_r (Datatypes.app a (Datatypes.app b c))
           (Logic.eq_rect_r
             (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d)
               k)) (\x1 ->
             Logic.eq_rect_r (Datatypes.Coq_pair (Datatypes.app a c)
               _UU0394_) (\x2 ->
               x2 g k (Datatypes.Coq_pair (Datatypes.app a c) _UU0394_) d a b
                 c _UU0394_ __ __) s x1) ns x) y) x0 __)}) __)
    (\x g k s d _UU0393_1 _UU0393_2 _UU0393_3 _UU0394_ _ _ ->
    x g k s (Datatypes.app _UU0393_1 _UU0393_3) _UU0394_
      (Datatypes.app _UU0393_1 (Datatypes.app _UU0393_2 _UU0393_3)) d
      (WeakenedT.weakened_I' _UU0393_1 _UU0393_2 _UU0393_3 _UU0394_) __ __)

type Coq_can_gen_weakR v rules =
  (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_prod
  (Datatypes.Coq_list (LNS.PropF v)) (Datatypes.Coq_list (LNS.PropF v))) ->
  LNS.Coq_dir -> (Datatypes.Coq_list (LNS.PropF v)) -> (Datatypes.Coq_list
  (LNS.PropF v)) -> (Datatypes.Coq_list (LNS.PropF v)) -> (Datatypes.Coq_list
  (LNS.PropF v)) -> () -> () -> DdT.Coq_pf (LNS.LNS v) rules

can_gen_weakR_def' :: (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      CRelationClasses.Coq_iffT (Coq_can_gen_weakR a1 a2)
                      ((Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                      (Datatypes.Coq_list (LNS.PropF a1))) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) ->
                      (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir ->
                      (WeakenedT.Coq_weakened (LNS.PropF a1)) -> () -> () ->
                      DdT.Coq_pf (LNS.LNS a1) a2)
can_gen_weakR_def' ns =
  Datatypes.Coq_pair (\x g k s _UU0393_ _ _ d h _ _ ->
    (case h of {
      WeakenedT.Coq_weakened_I x0 y a b c -> (\_ ->
       Logic.eq_rect_r (Datatypes.app a c) (\_ ->
         Logic.eq_rect_r (Datatypes.app a (Datatypes.app b c))
           (Logic.eq_rect_r
             (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d)
               k)) (\x1 ->
             Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_
               (Datatypes.app a c)) (\x2 ->
               x2 g k (Datatypes.Coq_pair _UU0393_ (Datatypes.app a c)) d
                 _UU0393_ a b c __ __) s x1) ns x) y) x0 __)}) __)
    (\x g k s d _UU0393_ _UU0394_1 _UU0394_2 _UU0394_3 _ _ ->
    x g k s _UU0393_ (Datatypes.app _UU0394_1 _UU0394_3)
      (Datatypes.app _UU0394_1 (Datatypes.app _UU0394_2 _UU0394_3)) d
      (WeakenedT.weakened_I' _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_3) __ __)

can_gen_weakL_imp :: (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Coq_can_gen_weakL a1 a2) -> (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir ->
                     (WeakenedT.Coq_weakened (LNS.PropF a1)) -> DdT.Coq_pf
                     (LNS.LNS a1) a2
can_gen_weakL_imp ns x g k s _UU0393_ _UU0394_ _UU0393_' d x0 =
  (case can_gen_weakL_def' ns of {
    Datatypes.Coq_pair x1 _ -> x1}) x g k s _UU0393_ _UU0394_ _UU0393_' d x0
    __ __

can_gen_weakR_imp :: (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Coq_can_gen_weakR a1 a2) -> (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                     (Datatypes.Coq_list (LNS.PropF a1))) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) ->
                     (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir ->
                     (WeakenedT.Coq_weakened (LNS.PropF a1)) -> DdT.Coq_pf
                     (LNS.LNS a1) a2
can_gen_weakR_imp ns x g k s _UU0393_ _UU0394_ _UU0394_' d x0 =
  (case can_gen_weakR_def' ns of {
    Datatypes.Coq_pair x1 _ -> x1}) x g k s _UU0393_ _UU0394_ _UU0394_' d x0
    __ __

type Coq_can_gen_contL_gen v rules =
  (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_prod
  (Datatypes.Coq_list (LNS.PropF v)) (Datatypes.Coq_list (LNS.PropF v))) ->
  LNS.Coq_dir -> (Datatypes.Coq_list (LNS.PropF v)) -> (Datatypes.Coq_list
  (LNS.PropF v)) -> (Datatypes.Coq_list (LNS.PropF v)) -> (LNS.PropF 
  v) -> (Datatypes.Coq_list (LNS.PropF v)) -> () -> () -> Datatypes.Coq_prod
  (DdT.Coq_pf (LNS.LNS v) rules) (DdT.Coq_pf (LNS.LNS v) rules)

can_gen_contL_gen_def' :: (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> CRelationClasses.Coq_iffT
                          (Coq_can_gen_contL_gen a1 a2)
                          ((Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) ->
                          (Datatypes.Coq_list (LNS.PropF a1)) ->
                          (Datatypes.Coq_list (LNS.PropF a1)) ->
                          (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir
                          -> (ContractedT.Coq_contracted_gen (LNS.PropF a1))
                          -> () -> () -> DdT.Coq_pf (LNS.LNS a1) a2)
can_gen_contL_gen_def' ns =
  Datatypes.Coq_pair (\x g k s _ _UU0394_ _ d h _ _ ->
    (case h of {
      ContractedT.Coq_contracted_genL_I a x0 y a0 b c -> (\_ ->
       Logic.eq_rect_r
         (Datatypes.app a0
           (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
             (Datatypes.app b
               (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil) c))))
         (\_ ->
         Logic.eq_rect_r
           (Datatypes.app a0
             (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
               (Datatypes.app b c)))
           (Logic.eq_rect_r
             (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d)
               k)) (\x1 ->
             Logic.eq_rect_r (Datatypes.Coq_pair
               (Datatypes.app a0
                 (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                   (Datatypes.app b
                     (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                       c)))) _UU0394_) (\x2 ->
               let {
                s0 = Datatypes.Coq_pair
                 (Datatypes.app a0
                   (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                     (Datatypes.app b
                       (Datatypes.app (Datatypes.Coq_cons a
                         Datatypes.Coq_nil) c)))) _UU0394_}
               in
               case x2 g k s0 d a0 b c a _UU0394_ __ __ of {
                Datatypes.Coq_pair x3 _ -> x3}) s x1) ns x) y) x0 __);
      ContractedT.Coq_contracted_genR_I a x0 y a0 b c -> (\_ ->
       Logic.eq_rect_r
         (Datatypes.app a0
           (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
             (Datatypes.app b
               (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil) c))))
         (\_ ->
         Logic.eq_rect_r
           (Datatypes.app a0
             (Datatypes.app b
               (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil) c)))
           (Logic.eq_rect_r
             (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d)
               k)) (\x1 ->
             Logic.eq_rect_r (Datatypes.Coq_pair
               (Datatypes.app a0
                 (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                   (Datatypes.app b
                     (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                       c)))) _UU0394_) (\x2 ->
               let {
                s0 = Datatypes.Coq_pair
                 (Datatypes.app a0
                   (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                     (Datatypes.app b
                       (Datatypes.app (Datatypes.Coq_cons a
                         Datatypes.Coq_nil) c)))) _UU0394_}
               in
               case x2 g k s0 d a0 b c a _UU0394_ __ __ of {
                Datatypes.Coq_pair _ x3 -> x3}) s x1) ns x) y) x0 __)}) __)
    (\x g k s d _UU0393_1 _UU0393_2 _UU0393_3 a _UU0394_ _ _ ->
    Logic.eq_rect_r
      (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d) k))
      (\x0 ->
      Logic.eq_rect_r (Datatypes.Coq_pair
        (Datatypes.app _UU0393_1
          (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
            (Datatypes.app _UU0393_2
              (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                _UU0393_3)))) _UU0394_) (\x1 -> Datatypes.Coq_pair
        (x1 g k (Datatypes.Coq_pair
          (Datatypes.app _UU0393_1
            (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
              (Datatypes.app _UU0393_2
                (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                  _UU0393_3)))) _UU0394_)
          (Datatypes.app _UU0393_1
            (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
              (Datatypes.app _UU0393_2
                (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                  _UU0393_3)))) _UU0394_
          (Datatypes.app _UU0393_1
            (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
              (Datatypes.app _UU0393_2 _UU0393_3))) d
          (ContractedT.contracted_genL_I' a _UU0393_1 _UU0393_2 _UU0393_3) __
          __)
        (x1 g k (Datatypes.Coq_pair
          (Datatypes.app _UU0393_1
            (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
              (Datatypes.app _UU0393_2
                (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                  _UU0393_3)))) _UU0394_)
          (Datatypes.app _UU0393_1
            (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
              (Datatypes.app _UU0393_2
                (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                  _UU0393_3)))) _UU0394_
          (Datatypes.app _UU0393_1
            (Datatypes.app _UU0393_2
              (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                _UU0393_3))) d
          (ContractedT.contracted_genR_I' a _UU0393_1 _UU0393_2 _UU0393_3) __
          __)) s x0) ns x)

type Coq_can_gen_contR_gen v rules =
  (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF v))
  (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) -> (Datatypes.Coq_prod
  (Datatypes.Coq_list (LNS.PropF v)) (Datatypes.Coq_list (LNS.PropF v))) ->
  LNS.Coq_dir -> (Datatypes.Coq_list (LNS.PropF v)) -> (Datatypes.Coq_list
  (LNS.PropF v)) -> (Datatypes.Coq_list (LNS.PropF v)) -> (Datatypes.Coq_list
  (LNS.PropF v)) -> (LNS.PropF v) -> () -> () -> Datatypes.Coq_prod
  (DdT.Coq_pf (LNS.LNS v) rules) (DdT.Coq_pf (LNS.LNS v) rules)

can_gen_contR_gen_def' :: (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> CRelationClasses.Coq_iffT
                          (Coq_can_gen_contR_gen a1 a2)
                          ((Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) ->
                          (Datatypes.Coq_list (LNS.PropF a1)) ->
                          (Datatypes.Coq_list (LNS.PropF a1)) ->
                          (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir
                          -> (ContractedT.Coq_contracted_gen (LNS.PropF a1))
                          -> () -> () -> DdT.Coq_pf (LNS.LNS a1) a2)
can_gen_contR_gen_def' ns =
  Datatypes.Coq_pair (\x g k s _UU0393_ _ _ d h0 _ _ ->
    (case h0 of {
      ContractedT.Coq_contracted_genL_I a x0 y a0 b c -> (\_ ->
       Logic.eq_rect_r
         (Datatypes.app a0
           (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
             (Datatypes.app b
               (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil) c))))
         (\_ ->
         Logic.eq_rect_r
           (Datatypes.app a0
             (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
               (Datatypes.app b c)))
           (Logic.eq_rect_r
             (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d)
               k)) (\x1 ->
             Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_
               (Datatypes.app a0
                 (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                   (Datatypes.app b
                     (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                       c))))) (\x2 ->
               let {
                s0 = Datatypes.Coq_pair _UU0393_
                 (Datatypes.app a0
                   (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                     (Datatypes.app b
                       (Datatypes.app (Datatypes.Coq_cons a
                         Datatypes.Coq_nil) c))))}
               in
               case x2 g k s0 d _UU0393_ a0 b c a __ __ of {
                Datatypes.Coq_pair x3 _ -> x3}) s x1) ns x) y) x0 __);
      ContractedT.Coq_contracted_genR_I a x0 y a0 b c -> (\_ ->
       Logic.eq_rect_r
         (Datatypes.app a0
           (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
             (Datatypes.app b
               (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil) c))))
         (\_ ->
         Logic.eq_rect_r
           (Datatypes.app a0
             (Datatypes.app b
               (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil) c)))
           (Logic.eq_rect_r
             (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d)
               k)) (\x1 ->
             Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_
               (Datatypes.app a0
                 (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                   (Datatypes.app b
                     (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                       c))))) (\x2 ->
               let {
                s0 = Datatypes.Coq_pair _UU0393_
                 (Datatypes.app a0
                   (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                     (Datatypes.app b
                       (Datatypes.app (Datatypes.Coq_cons a
                         Datatypes.Coq_nil) c))))}
               in
               case x2 g k s0 d _UU0393_ a0 b c a __ __ of {
                Datatypes.Coq_pair _ x3 -> x3}) s x1) ns x) y) x0 __)}) __)
    (\x g k s d _UU0393_ _UU0394_1 _UU0394_2 _UU0394_3 a _ _ ->
    Datatypes.Coq_pair
    (Logic.eq_rect_r
      (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d) k))
      (\x0 ->
      Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_
        (Datatypes.app _UU0394_1
          (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
            (Datatypes.app _UU0394_2
              (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                _UU0394_3))))) (\x1 ->
        x1 g k (Datatypes.Coq_pair _UU0393_
          (Datatypes.app _UU0394_1
            (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
              (Datatypes.app _UU0394_2
                (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                  _UU0394_3))))) _UU0393_
          (Datatypes.app _UU0394_1
            (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
              (Datatypes.app _UU0394_2
                (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                  _UU0394_3))))
          (Datatypes.app _UU0394_1
            (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
              (Datatypes.app _UU0394_2 _UU0394_3))) d
          (ContractedT.contracted_genL_I' a _UU0394_1 _UU0394_2 _UU0394_3) __
          __) s x0) ns x)
    (Logic.eq_rect_r
      (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair s d) k))
      (\x0 ->
      Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_
        (Datatypes.app _UU0394_1
          (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
            (Datatypes.app _UU0394_2
              (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                _UU0394_3))))) (\x1 ->
        x1 g k (Datatypes.Coq_pair _UU0393_
          (Datatypes.app _UU0394_1
            (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
              (Datatypes.app _UU0394_2
                (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                  _UU0394_3))))) _UU0393_
          (Datatypes.app _UU0394_1
            (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
              (Datatypes.app _UU0394_2
                (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                  _UU0394_3))))
          (Datatypes.app _UU0394_1
            (Datatypes.app _UU0394_2
              (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                _UU0394_3))) d
          (ContractedT.contracted_genR_I' a _UU0394_1 _UU0394_2 _UU0394_3) __
          __) s x0) ns x))

type Coq_rules_L_oeT w rules =
  (Datatypes.Coq_list (Gen_tacs.Coq_rel (Datatypes.Coq_list w))) ->
  (Datatypes.Coq_list w) -> (Datatypes.Coq_list w) -> (Datatypes.Coq_list 
  w) -> rules -> Datatypes.Coq_sum () ()

type Coq_rules_R_oeT w rules =
  (Datatypes.Coq_list (Gen_tacs.Coq_rel (Datatypes.Coq_list w))) ->
  (Datatypes.Coq_list w) -> (Datatypes.Coq_list w) -> (Datatypes.Coq_list 
  w) -> rules -> Datatypes.Coq_sum () ()

