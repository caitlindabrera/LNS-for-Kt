module LntacsT where

import qualified Prelude
import qualified CRelationClasses
import qualified Datatypes
import qualified Logic
import qualified DdT
import qualified Gen_tacs
import qualified LntT
import qualified SwappedT

__ :: any
__ = Prelude.error "Logical or arity value used"

type Coq_can_gen_swapL v rules =
  (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF v))
  (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) -> (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF v))
  (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) -> (Datatypes.Coq_prod
  (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v))) -> LntT.Coq_dir
  -> (Datatypes.Coq_list (LntT.PropF v)) -> (Datatypes.Coq_list (LntT.PropF v)) ->
  (Datatypes.Coq_list (LntT.PropF v)) -> (Datatypes.Coq_list (LntT.PropF v)) ->
  (Datatypes.Coq_list (LntT.PropF v)) -> () -> () -> DdT.Coq_derrec
  (Datatypes.Coq_list
  (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))
  rules ()

type Coq_can_gen_swapR v rules =
  (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF v))
  (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) -> (Datatypes.Coq_list
  (Datatypes.Coq_prod
  (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF v))
  (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) -> (Datatypes.Coq_prod
  (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v))) -> LntT.Coq_dir
  -> (Datatypes.Coq_list (LntT.PropF v)) -> (Datatypes.Coq_list (LntT.PropF v)) ->
  (Datatypes.Coq_list (LntT.PropF v)) -> (Datatypes.Coq_list (LntT.PropF v)) ->
  (Datatypes.Coq_list (LntT.PropF v)) -> () -> () -> DdT.Coq_derrec
  (Datatypes.Coq_list
  (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))
  rules ()

can_gen_swapL_def' :: (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                      (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                      CRelationClasses.Coq_iffT (Coq_can_gen_swapL a1 a2)
                      ((Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                      (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                      (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                      (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                      (Datatypes.Coq_list (LntT.PropF a1))) -> (Datatypes.Coq_list
                      (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                      (Datatypes.Coq_list (LntT.PropF a1)) -> LntT.Coq_dir ->
                      (SwappedT.Coq_swapped (LntT.PropF a1)) -> () -> () -> DdT.Coq_derrec
                      (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                      LntT.Coq_dir)) a2 ())
can_gen_swapL_def' ns =
  Datatypes.Coq_pair (\x g k seq _ _UU0394_ _ d h _ _ ->
    case h of {
     SwappedT.Coq_swapped_I x0 y a b c d0 ->
      Logic.eq_rect_r (Datatypes.app a (Datatypes.app b (Datatypes.app c d0))) (\_ ->
        Logic.eq_rect_r (Datatypes.app a (Datatypes.app c (Datatypes.app b d0)))
          (Logic.eq_rect_r
            (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair seq d) k)) (\x1 ->
            Logic.eq_rect_r (Datatypes.Coq_pair
              (Datatypes.app a (Datatypes.app b (Datatypes.app c d0))) _UU0394_) (\x2 ->
              x2 g k (Datatypes.Coq_pair
                (Datatypes.app a (Datatypes.app b (Datatypes.app c d0))) _UU0394_) d a b c
                d0 _UU0394_ __ __) seq x1) ns x) y) x0 __})
    (\x g k seq d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ _ _ ->
    x g k seq
      (Datatypes.app _UU0393_1
        (Datatypes.app _UU0393_2 (Datatypes.app _UU0393_3 _UU0393_4))) _UU0394_
      (Datatypes.app _UU0393_1
        (Datatypes.app _UU0393_3 (Datatypes.app _UU0393_2 _UU0393_4))) d
      (SwappedT.swapped_I' _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4) __ __)

can_gen_swapR_def' :: (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                      (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                      CRelationClasses.Coq_iffT (Coq_can_gen_swapR a1 a2)
                      ((Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                      (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                      (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                      (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                      (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                      (Datatypes.Coq_list (LntT.PropF a1))) -> (Datatypes.Coq_list
                      (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                      (Datatypes.Coq_list (LntT.PropF a1)) -> LntT.Coq_dir ->
                      (SwappedT.Coq_swapped (LntT.PropF a1)) -> () -> () -> DdT.Coq_derrec
                      (Datatypes.Coq_list
                      (Datatypes.Coq_prod
                      (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                      LntT.Coq_dir)) a2 ())
can_gen_swapR_def' ns =
  Datatypes.Coq_pair (\x g k seq _UU0393_ _ _ d h _ _ ->
    case h of {
     SwappedT.Coq_swapped_I x0 y a b c d0 ->
      Logic.eq_rect_r (Datatypes.app a (Datatypes.app b (Datatypes.app c d0))) (\_ ->
        Logic.eq_rect_r (Datatypes.app a (Datatypes.app c (Datatypes.app b d0)))
          (Logic.eq_rect_r
            (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair seq d) k)) (\x1 ->
            Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_
              (Datatypes.app a (Datatypes.app b (Datatypes.app c d0)))) (\x2 ->
              x2 g k (Datatypes.Coq_pair _UU0393_
                (Datatypes.app a (Datatypes.app b (Datatypes.app c d0)))) d a b c d0
                _UU0393_ __ __) seq x1) ns x) y) x0 __})
    (\x g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ _ _ ->
    x g k seq _UU0393_
      (Datatypes.app _UU0394_1
        (Datatypes.app _UU0394_2 (Datatypes.app _UU0394_3 _UU0394_4)))
      (Datatypes.app _UU0394_1
        (Datatypes.app _UU0394_3 (Datatypes.app _UU0394_2 _UU0394_4))) d
      (SwappedT.swapped_I' _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4) __ __)

can_gen_swapL_imp :: (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                     (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                     (Coq_can_gen_swapL a1 a2) -> (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                     (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                     (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                     (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                     (Datatypes.Coq_list (LntT.PropF a1))) -> (Datatypes.Coq_list
                     (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                     (Datatypes.Coq_list (LntT.PropF a1)) -> LntT.Coq_dir ->
                     (SwappedT.Coq_swapped (LntT.PropF a1)) -> DdT.Coq_derrec
                     (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                     a2 ()
can_gen_swapL_imp ns h g k seq _UU0393_ _UU0394_ _UU0393_' d h0 =
  let {i = can_gen_swapL_def' ns} in
  case i of {
   Datatypes.Coq_pair hH1 _ -> hH1 h g k seq _UU0393_ _UU0394_ _UU0393_' d h0 __ __}

can_gen_swapR_imp :: (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                     (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                     (Coq_can_gen_swapR a1 a2) -> (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                     (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                     (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                     (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                     (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                     (Datatypes.Coq_list (LntT.PropF a1))) -> (Datatypes.Coq_list
                     (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                     (Datatypes.Coq_list (LntT.PropF a1)) -> LntT.Coq_dir ->
                     (SwappedT.Coq_swapped (LntT.PropF a1)) -> DdT.Coq_derrec
                     (Datatypes.Coq_list
                     (Datatypes.Coq_prod
                     (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                     a2 ()
can_gen_swapR_imp ns h g k seq _UU0393_ _UU0394_ _UU0394_' d h0 =
  let {i = can_gen_swapR_def' ns} in
  case i of {
   Datatypes.Coq_pair hH1 _ -> hH1 h g k seq _UU0393_ _UU0394_ _UU0394_' d h0 __ __}

can_gen_swapL_imp_rev :: (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         ((Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) -> (Datatypes.Coq_list
                         (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                         (Datatypes.Coq_list (LntT.PropF a1)) -> LntT.Coq_dir ->
                         (SwappedT.Coq_swapped (LntT.PropF a1)) -> () -> () ->
                         DdT.Coq_derrec
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                         LntT.Coq_dir)) a2 ()) -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) -> LntT.Coq_dir ->
                         (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                         (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                         (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                         (LntT.PropF a1)) -> DdT.Coq_derrec
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                         LntT.Coq_dir)) a2 ()
can_gen_swapL_imp_rev ns h g k seq d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ =
  let {i = can_gen_swapL_def' ns} in
  case i of {
   Datatypes.Coq_pair _ hH2 ->
    hH2 h g k seq d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ __ __}

can_gen_swapR_imp_rev :: (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         ((Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) -> (Datatypes.Coq_list
                         (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                         (Datatypes.Coq_list (LntT.PropF a1)) -> LntT.Coq_dir ->
                         (SwappedT.Coq_swapped (LntT.PropF a1)) -> () -> () ->
                         DdT.Coq_derrec
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                         LntT.Coq_dir)) a2 ()) -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) -> LntT.Coq_dir ->
                         (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                         (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                         (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                         (LntT.PropF a1)) -> DdT.Coq_derrec
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                         LntT.Coq_dir)) a2 ()
can_gen_swapR_imp_rev ns h g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ =
  let {i = can_gen_swapR_def' ns} in
  case i of {
   Datatypes.Coq_pair _ hH2 ->
    hH2 h g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ __ __}

