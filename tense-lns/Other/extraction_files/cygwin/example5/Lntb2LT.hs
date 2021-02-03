{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Lntb2LT where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified List_lemmasT
import qualified Logic
import qualified Specif
import qualified DdT
import qualified Gen
import qualified GenT
import qualified Gen_tacs
import qualified LntT
import qualified LntacsT
import qualified SwappedT

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_b2lrules v =
   WBox2Ls (LntT.PropF v) LntT.Coq_dir (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                                                                                                                   (LntT.PropF v)) (Datatypes.Coq_list
                                                                                                                                                                   (LntT.PropF
                                                                                                                                                                   v)) 
 (Datatypes.Coq_list (LntT.PropF v))
 | BBox2Ls (LntT.PropF v) LntT.Coq_dir (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                                                                                                                   (LntT.PropF v)) (Datatypes.Coq_list
                                                                                                                                                                   (LntT.PropF
                                                                                                                                                                   v)) 
 (Datatypes.Coq_list (LntT.PropF v))

gen_swapL_step_b2L_lc :: (Datatypes.Coq_list (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))) ->
                         (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) -> a2 -> (DdT.Coq_dersrec
                         (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) a3 ()) -> (GenT.ForallT
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                         (LntacsT.Coq_can_gen_swapL a1 a3)) -> (Gen.Coq_rsub
                         (Datatypes.Coq_list (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)))
                         (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) a2 a3) -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) -> LntT.Coq_dir -> (Datatypes.Coq_list
                         (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                         (Datatypes.Coq_list (LntT.PropF a1)) -> DdT.Coq_derrec
                         (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) a3 ()
gen_swapL_step_b2L_lc ps concl nsr drs acm rs g k seq d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LntT.NSlclctxt ps0 c g0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LntT.nslclext g0) ps0) (\_ ->
         Logic.eq_rect (LntT.nslclext g0 c) (\sppc0 ->
           let {ns = LntT.nslclext g0 c} in
           (case LntacsT.can_gen_swapL_def' ns of {
             Datatypes.Coq_pair _ x -> x}) (\g1 k0 seq0 _UU0393_ _UU0394_0 _UU0393_' d0 swap _ _ ->
             Logic.eq_rect (List.map (LntT.nslclext g0) ps0) (\drs0 acm0 ->
               Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_ _UU0394_0) (\_ ->
                 let {pp = List_lemmasT.app_eq_appT2 g0 c g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) k0)} in
                 case pp of {
                  Specif.Coq_existT pp0 pp1 ->
                   case pp1 of {
                    Datatypes.Coq_inl _ ->
                     let {pp2 = List_lemmasT.cons_eq_appT2 k0 pp0 c (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0)} in
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                         Logic.eq_rect_r Datatypes.Coq_nil (\drs2 acm2 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) k0) (\sppc1 ->
                             let {drs3 = Logic.eq_rect (Datatypes.app g1 Datatypes.Coq_nil) drs2 g1} in
                             let {acm3 = Logic.eq_rect (Datatypes.app g1 Datatypes.Coq_nil) acm2 g1} in
                             (case sppc1 of {
                               WBox2Ls a d1 h1l h1r h2l h2r k1 k2 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r))
                                  k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect (Datatypes.app h1l h1r) (\_ ->
                                    Logic.eq_rect_r _UU0394_0 (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r))
                                          k2) LntT.Coq_bac) Datatypes.Coq_nil)
                                          (Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                            (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\acm4 drs4 sppc2 ->
                                            Logic.eq_rect (Datatypes.app h1l h1r) (\sppc3 swap0 ->
                                              Logic.eq_rect_r _UU0394_0 (\drs5 acm5 sppc4 ->
                                                Logic.eq_rect_r d0 (\acm6 drs6 sppc5 ->
                                                  Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                    (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil) (\_ ->
                                                    (case swap0 of {
                                                      SwappedT.Coq_swapped_I x y a0 b c0 d2 -> (\_ _ ->
                                                       Logic.eq_rect_r (Datatypes.app h1l h1r) (\_ ->
                                                         Logic.eq_rect_r _UU0393_' (\_ _ ->
                                                           Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b d2)))
                                                             (let {h = List_lemmasT.app_eq_appT2 h1l h1r a0 (Datatypes.app b (Datatypes.app c0 d2))} in
                                                              case h of {
                                                               Specif.Coq_existT h0 h1 ->
                                                                case h1 of {
                                                                 Datatypes.Coq_inl _ ->
                                                                  let {h2 = List_lemmasT.app_eq_appT2 b (Datatypes.app c0 d2) h0 h1r} in
                                                                  case h2 of {
                                                                   Specif.Coq_existT h3 h4 ->
                                                                    case h4 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                      Logic.eq_rect_r (Datatypes.app a0 h0) (\drs7 acm7 ->
                                                                        Logic.eq_rect_r (Datatypes.app h0 h3)
                                                                          (Logic.eq_rect_r (Datatypes.app h3 (Datatypes.app c0 d2)) (\acm8 _ -> DdT.Coq_derI
                                                                            (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                              (Datatypes.Coq_pair
                                                                              (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                (Datatypes.app h3 d2))) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                            (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                              (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app (Datatypes.app h0 h3) d2))) _UU0394_0) d0)
                                                                              (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                              (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                              Datatypes.Coq_nil)))
                                                                            (unsafeCoerce rs0
                                                                              (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                (Datatypes.Coq_pair
                                                                                (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                  (Datatypes.app h3 d2))) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                              (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app (Datatypes.app h0 h3) d2))) _UU0394_0) d0)
                                                                                (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                Datatypes.Coq_nil)))
                                                                              (let {
                                                                                _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                             (Datatypes.Coq_pair
                                                                                             (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h3 d2))) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil)
                                                                                             (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app h0 (Datatypes.app h3 d2))))
                                                                                             _UU0394_0) d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                             Datatypes.Coq_nil)) g1
                                                                                             (let {
                                                                                               _evar_0_ = let {
                                                                                                           _evar_0_ = let {
                                                                                                                       _evar_0_ = let {
                                                                                                                                   _evar_0_ = WBox2Ls a d0
                                                                                                                                    (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                                                    (Datatypes.app h3 d2) h2l h2r _UU0394_0
                                                                                                                                    k2}
                                                                                                                                  in
                                                                                                                                  Logic.eq_rect
                                                                                                                                    (Datatypes.app
                                                                                                                                      (Datatypes.app (Datatypes.app a0 c0)
                                                                                                                                        h0) (Datatypes.app h3 d2)) _evar_0_
                                                                                                                                    (Datatypes.app
                                                                                                                                      (Datatypes.app
                                                                                                                                        (Datatypes.app (Datatypes.app a0 c0)
                                                                                                                                          h0) h3) d2)}
                                                                                                                      in
                                                                                                                      Logic.eq_rect_r
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app
                                                                                                                            (Datatypes.app (Datatypes.app a0 c0) h0) h3) d2)
                                                                                                                        _evar_0_
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                                          (Datatypes.app h3 d2))}
                                                                                                          in
                                                                                                          Logic.eq_rect_r
                                                                                                            (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                              (Datatypes.app h3 d2)) _evar_0_
                                                                                                            (Datatypes.app (Datatypes.app a0 c0)
                                                                                                              (Datatypes.app h0 (Datatypes.app h3 d2)))}
                                                                                              in
                                                                                              Logic.eq_rect_r
                                                                                                (Datatypes.app (Datatypes.app a0 c0)
                                                                                                  (Datatypes.app h0 (Datatypes.app h3 d2))) _evar_0_
                                                                                                (Datatypes.app a0
                                                                                                  (Datatypes.app c0 (Datatypes.app h0 (Datatypes.app h3 d2)))))}
                                                                               in
                                                                               Logic.eq_rect (Datatypes.app h0 (Datatypes.app h3 d2)) _evar_0_
                                                                                 (Datatypes.app (Datatypes.app h0 h3) d2)))
                                                                            (let {f = LntT.nslclext g1} in
                                                                             let {
                                                                              c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                               (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                 (Datatypes.app h3 d2))) _UU0394_0) d0) Datatypes.Coq_nil}
                                                                             in
                                                                             (case DdT.dersrec_map_single f c1 of {
                                                                               Datatypes.Coq_pair _ x0 -> x0})
                                                                               (let {
                                                                                 x0 = \_ _ _ f0 x0 ->
                                                                                  case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                   Datatypes.Coq_pair _ x1 -> x1}}
                                                                                in
                                                                                let {
                                                                                 acm9 = x0 __ __ __ (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                          (Datatypes.Coq_pair
                                                                                          (Datatypes.app (Datatypes.app a0 h0) (Datatypes.Coq_cons a
                                                                                            (Datatypes.app h3 (Datatypes.app c0 d2)))) _UU0394_0) d0) Datatypes.Coq_nil) acm8}
                                                                                in
                                                                                let {x1 = \_ ns0 -> case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                                     Datatypes.Coq_pair x1 _ -> x1}}
                                                                                in
                                                                                let {
                                                                                 acm10 = x1 __
                                                                                           (LntT.nslclext g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app (Datatypes.app a0 h0) (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h3 (Datatypes.app c0 d2)))) _UU0394_0) d0) Datatypes.Coq_nil))
                                                                                           acm9 g1 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                           (Datatypes.app a0
                                                                                             (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h3 (Datatypes.app c0 d2))))) _UU0394_0)
                                                                                           (Datatypes.app a0
                                                                                             (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h3 (Datatypes.app c0 d2))))) _UU0394_0
                                                                                           (Datatypes.app a0
                                                                                             (Datatypes.app c0
                                                                                               (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2))))) d0
                                                                                           (SwappedT.swapped_L
                                                                                             (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h3 (Datatypes.app c0 d2))))
                                                                                             (Datatypes.app c0
                                                                                               (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2)))) a0
                                                                                             (Logic.eq_rec_r (Datatypes.app (Datatypes.app h3 c0) d2)
                                                                                               (Logic.eq_rec_r
                                                                                                 (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons a
                                                                                                   (Datatypes.app h3 d2)))
                                                                                                 (Logic.eq_rec_r
                                                                                                   (Datatypes.app (Datatypes.Coq_cons a (Datatypes.app h3 c0)) d2)
                                                                                                   (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h3) c0)
                                                                                                     (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h3) d2)
                                                                                                       (Logic.eq_rec_r
                                                                                                         (Datatypes.app
                                                                                                           (Datatypes.app h0 (Datatypes.app (Datatypes.Coq_cons a h3) c0))
                                                                                                           d2)
                                                                                                         (Logic.eq_rec_r
                                                                                                           (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons a h3)) c0)
                                                                                                           (Logic.eq_rec_r
                                                                                                             (Datatypes.app
                                                                                                               (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons a
                                                                                                                 h3)) d2)
                                                                                                             (SwappedT.swapped_R
                                                                                                               (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons a h3))
                                                                                                                 c0)
                                                                                                               (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons a
                                                                                                                 h3)) d2
                                                                                                               (let {
                                                                                                                 _evar_0_ = let {
                                                                                                                             _evar_0_ = let {
                                                                                                                                         _evar_0_ = Gen.arg1_cong_imp
                                                                                                                                                      (Datatypes.app
                                                                                                                                                        (Datatypes.app h0
                                                                                                                                                          (Datatypes.Coq_cons
                                                                                                                                                          a h3)) c0)
                                                                                                                                                      (Datatypes.app h0
                                                                                                                                                        (Datatypes.Coq_cons a
                                                                                                                                                        (Datatypes.app h3 c0)))
                                                                                                                                                      (Datatypes.app c0
                                                                                                                                                        (Datatypes.app h0
                                                                                                                                                          (Datatypes.Coq_cons
                                                                                                                                                          a h3)))
                                                                                                                                                      (SwappedT.swapped_simpleR
                                                                                                                                                        c0
                                                                                                                                                        (Datatypes.app h0
                                                                                                                                                          (Datatypes.Coq_cons
                                                                                                                                                          a h3))
                                                                                                                                                        (Datatypes.app h0
                                                                                                                                                          (Datatypes.Coq_cons
                                                                                                                                                          a h3)))}
                                                                                                                                        in
                                                                                                                                        Logic.eq_rec (Datatypes.Coq_cons a
                                                                                                                                          (Datatypes.app h3 c0)) _evar_0_
                                                                                                                                          (Datatypes.app (Datatypes.Coq_cons
                                                                                                                                            a h3) c0)}
                                                                                                                            in
                                                                                                                            Logic.eq_rec
                                                                                                                              (Datatypes.app c0
                                                                                                                                (Datatypes.app h0 (Datatypes.Coq_cons a h3)))
                                                                                                                              _evar_0_
                                                                                                                              (Datatypes.app (Datatypes.app c0 h0)
                                                                                                                                (Datatypes.Coq_cons a h3))}
                                                                                                                in
                                                                                                                Logic.eq_rec
                                                                                                                  (Datatypes.app h0
                                                                                                                    (Datatypes.app (Datatypes.Coq_cons a h3) c0)) _evar_0_
                                                                                                                  (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons a h3))
                                                                                                                    c0)))
                                                                                                             (Datatypes.app (Datatypes.app c0 h0)
                                                                                                               (Datatypes.app (Datatypes.Coq_cons a h3) d2)))
                                                                                                           (Datatypes.app h0 (Datatypes.app (Datatypes.Coq_cons a h3) c0)))
                                                                                                         (Datatypes.app h0
                                                                                                           (Datatypes.app (Datatypes.app (Datatypes.Coq_cons a h3) c0) d2)))
                                                                                                       (Datatypes.Coq_cons a (Datatypes.app h3 d2))) (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h3 c0))) (Datatypes.Coq_cons a
                                                                                                   (Datatypes.app (Datatypes.app h3 c0) d2)))
                                                                                                 (Datatypes.app c0
                                                                                                   (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2)))))
                                                                                               (Datatypes.app h3 (Datatypes.app c0 d2)))) __ __}
                                                                                in
                                                                                let {
                                                                                 _evar_0_ = Logic.eq_rect
                                                                                              (Datatypes.app a0
                                                                                                (Datatypes.app c0
                                                                                                  (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2))))) acm10
                                                                                              (Datatypes.app (Datatypes.app a0 c0)
                                                                                                (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2))))}
                                                                                in
                                                                                Logic.eq_rect
                                                                                  (Datatypes.app (Datatypes.app a0 c0)
                                                                                    (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2)))) _evar_0_
                                                                                  (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                    (Datatypes.app h3 d2)))))) h1r acm7 drs7) b) h1l drs6 acm6;
                                                                     Datatypes.Coq_inr _ ->
                                                                      let {h5 = List_lemmasT.app_eq_appT2 c0 d2 h3 h1r} in
                                                                      case h5 of {
                                                                       Specif.Coq_existT h6 h7 ->
                                                                        case h7 of {
                                                                         Datatypes.Coq_inl _ ->
                                                                          Logic.eq_rect_r (Datatypes.app a0 h0) (\drs7 acm7 ->
                                                                            Logic.eq_rect_r (Datatypes.app b h3) (\acm8 drs8 ->
                                                                              Logic.eq_rect_r (Datatypes.app h3 h6)
                                                                                (Logic.eq_rect_r (Datatypes.app h6 d2) (\_ acm9 -> DdT.Coq_derI
                                                                                  (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                    (Datatypes.Coq_pair
                                                                                    (Datatypes.app (Datatypes.app a0 h3) (Datatypes.Coq_cons a
                                                                                      (Datatypes.app h6 (Datatypes.app b d2)))) _UU0394_0) d0) Datatypes.Coq_nil)
                                                                                    Datatypes.Coq_nil))
                                                                                  (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app a0 (Datatypes.app (Datatypes.app h3 h6) (Datatypes.app b d2))) _UU0394_0)
                                                                                    d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                    Datatypes.Coq_nil)))
                                                                                  (unsafeCoerce rs0
                                                                                    (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                      (Datatypes.Coq_pair
                                                                                      (Datatypes.app (Datatypes.app a0 h3) (Datatypes.Coq_cons a
                                                                                        (Datatypes.app h6 (Datatypes.app b d2)))) _UU0394_0) d0) Datatypes.Coq_nil)
                                                                                      Datatypes.Coq_nil))
                                                                                    (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app a0 (Datatypes.app (Datatypes.app h3 h6) (Datatypes.app b d2)))
                                                                                      _UU0394_0) d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                      Datatypes.Coq_nil)))
                                                                                    (let {
                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                   (Datatypes.app (Datatypes.app a0 h3) (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h6 (Datatypes.app b d2)))) _UU0394_0) d0)
                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                   (Datatypes.app a0
                                                                                                     (Datatypes.app h3 (Datatypes.app h6 (Datatypes.app b d2)))) _UU0394_0)
                                                                                                   d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                   (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2)
                                                                                                   LntT.Coq_bac) Datatypes.Coq_nil)) g1
                                                                                                   (let {
                                                                                                     _evar_0_ = let {
                                                                                                                 _evar_0_ = let {
                                                                                                                             _evar_0_ = WBox2Ls a d0 (Datatypes.app a0 h3)
                                                                                                                              (Datatypes.app h6 (Datatypes.app b d2)) h2l h2r
                                                                                                                              _UU0394_0 k2}
                                                                                                                            in
                                                                                                                            Logic.eq_rect
                                                                                                                              (Datatypes.app (Datatypes.app a0 h3)
                                                                                                                                (Datatypes.app h6 (Datatypes.app b d2)))
                                                                                                                              _evar_0_
                                                                                                                              (Datatypes.app
                                                                                                                                (Datatypes.app (Datatypes.app a0 h3) h6)
                                                                                                                                (Datatypes.app b d2))}
                                                                                                                in
                                                                                                                Logic.eq_rect_r
                                                                                                                  (Datatypes.app (Datatypes.app (Datatypes.app a0 h3) h6)
                                                                                                                    (Datatypes.app b d2)) _evar_0_
                                                                                                                  (Datatypes.app (Datatypes.app a0 h3)
                                                                                                                    (Datatypes.app h6 (Datatypes.app b d2)))}
                                                                                                    in
                                                                                                    Logic.eq_rect_r
                                                                                                      (Datatypes.app (Datatypes.app a0 h3)
                                                                                                        (Datatypes.app h6 (Datatypes.app b d2))) _evar_0_
                                                                                                      (Datatypes.app a0
                                                                                                        (Datatypes.app h3 (Datatypes.app h6 (Datatypes.app b d2)))))}
                                                                                     in
                                                                                     Logic.eq_rect (Datatypes.app h3 (Datatypes.app h6 (Datatypes.app b d2))) _evar_0_
                                                                                       (Datatypes.app (Datatypes.app h3 h6) (Datatypes.app b d2))))
                                                                                  (let {f = LntT.nslclext g1} in
                                                                                   let {
                                                                                    c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app (Datatypes.app a0 h3) (Datatypes.Coq_cons a
                                                                                       (Datatypes.app h6 (Datatypes.app b d2)))) _UU0394_0) d0) Datatypes.Coq_nil}
                                                                                   in
                                                                                   (case DdT.dersrec_map_single f c1 of {
                                                                                     Datatypes.Coq_pair _ x0 -> x0})
                                                                                     (let {
                                                                                       x0 = \_ _ _ f0 x0 ->
                                                                                        case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                         Datatypes.Coq_pair _ x1 -> x1}}
                                                                                      in
                                                                                      let {
                                                                                       acm10 = x0 __ __ __ (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                 (Datatypes.Coq_pair
                                                                                                 (Datatypes.app (Datatypes.app a0 (Datatypes.app b h3)) (Datatypes.Coq_cons a
                                                                                                   (Datatypes.app h6 d2))) _UU0394_0) d0) Datatypes.Coq_nil) acm9}
                                                                                      in
                                                                                      let {
                                                                                       x1 = \_ ns0 ->
                                                                                        case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                         Datatypes.Coq_pair x1 _ -> x1}}
                                                                                      in
                                                                                      let {
                                                                                       acm11 = x1 __
                                                                                                 (LntT.nslclext g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                   (Datatypes.Coq_pair
                                                                                                   (Datatypes.app (Datatypes.app a0 (Datatypes.app b h3)) (Datatypes.Coq_cons
                                                                                                     a (Datatypes.app h6 d2))) _UU0394_0) d0) Datatypes.Coq_nil)) acm10 g1
                                                                                                 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app h3 (Datatypes.Coq_cons a (Datatypes.app h6 d2)))))
                                                                                                 _UU0394_0)
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app h3 (Datatypes.Coq_cons a (Datatypes.app h6 d2)))))
                                                                                                 _UU0394_0
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app h3 (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h6 (Datatypes.app b d2))))) d0
                                                                                                 (SwappedT.swapped_L
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app h3 (Datatypes.Coq_cons a (Datatypes.app h6 d2))))
                                                                                                   (Datatypes.app h3 (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h6 (Datatypes.app b d2)))) a0
                                                                                                   (Logic.eq_rec_r
                                                                                                     (Datatypes.app (Datatypes.app b h3) (Datatypes.Coq_cons a
                                                                                                       (Datatypes.app h6 d2)))
                                                                                                     (Logic.eq_rec_r (Datatypes.app (Datatypes.app h6 b) d2)
                                                                                                       (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h6) d2)
                                                                                                         (Logic.eq_rec_r
                                                                                                           (Datatypes.app (Datatypes.Coq_cons a (Datatypes.app h6 b)) d2)
                                                                                                           (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h6) b)
                                                                                                             (Logic.eq_rec_r
                                                                                                               (Datatypes.app
                                                                                                                 (Datatypes.app (Datatypes.app b h3) (Datatypes.Coq_cons a
                                                                                                                   h6)) d2)
                                                                                                               (Logic.eq_rec_r
                                                                                                                 (Datatypes.app
                                                                                                                   (Datatypes.app h3
                                                                                                                     (Datatypes.app (Datatypes.Coq_cons a h6) b)) d2)
                                                                                                                 (Logic.eq_rec_r
                                                                                                                   (Datatypes.app
                                                                                                                     (Datatypes.app h3 (Datatypes.Coq_cons a h6)) b)
                                                                                                                   (SwappedT.swapped_R
                                                                                                                     (Datatypes.app (Datatypes.app b h3) (Datatypes.Coq_cons
                                                                                                                       a h6))
                                                                                                                     (Datatypes.app
                                                                                                                       (Datatypes.app h3 (Datatypes.Coq_cons a h6)) b) d2
                                                                                                                     (let {
                                                                                                                       _evar_0_ = let {
                                                                                                                                   _evar_0_ = let {
                                                                                                                                               _evar_0_ = Gen.arg_cong_imp
                                                                                                                                                            (Datatypes.app
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h3
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h6)) b)
                                                                                                                                                            (Datatypes.app h3
                                                                                                                                                              (Datatypes.Coq_cons
                                                                                                                                                              a
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h6 b)))
                                                                                                                                                            (SwappedT.swapped_simpleL
                                                                                                                                                              b
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h3
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h6))
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h3
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h6)))}
                                                                                                                                              in
                                                                                                                                              Logic.eq_rec
                                                                                                                                                (Datatypes.Coq_cons a
                                                                                                                                                (Datatypes.app h6 b))
                                                                                                                                                _evar_0_
                                                                                                                                                (Datatypes.app
                                                                                                                                                  (Datatypes.Coq_cons a h6)
                                                                                                                                                  b)}
                                                                                                                                  in
                                                                                                                                  Logic.eq_rec
                                                                                                                                    (Datatypes.app h3
                                                                                                                                      (Datatypes.app (Datatypes.Coq_cons a
                                                                                                                                        h6) b)) _evar_0_
                                                                                                                                    (Datatypes.app
                                                                                                                                      (Datatypes.app h3 (Datatypes.Coq_cons a
                                                                                                                                        h6)) b)}
                                                                                                                      in
                                                                                                                      Logic.eq_rec
                                                                                                                        (Datatypes.app b
                                                                                                                          (Datatypes.app h3 (Datatypes.Coq_cons a h6)))
                                                                                                                        _evar_0_
                                                                                                                        (Datatypes.app (Datatypes.app b h3)
                                                                                                                          (Datatypes.Coq_cons a h6))))
                                                                                                                   (Datatypes.app h3
                                                                                                                     (Datatypes.app (Datatypes.Coq_cons a h6) b)))
                                                                                                                 (Datatypes.app h3
                                                                                                                   (Datatypes.app (Datatypes.app (Datatypes.Coq_cons a h6) b)
                                                                                                                     d2)))
                                                                                                               (Datatypes.app (Datatypes.app b h3)
                                                                                                                 (Datatypes.app (Datatypes.Coq_cons a h6) d2)))
                                                                                                             (Datatypes.Coq_cons a (Datatypes.app h6 b))) (Datatypes.Coq_cons
                                                                                                           a (Datatypes.app (Datatypes.app h6 b) d2))) (Datatypes.Coq_cons a
                                                                                                         (Datatypes.app h6 d2))) (Datatypes.app h6 (Datatypes.app b d2)))
                                                                                                     (Datatypes.app b
                                                                                                       (Datatypes.app h3 (Datatypes.Coq_cons a (Datatypes.app h6 d2)))))) __
                                                                                                 __}
                                                                                      in
                                                                                      Logic.eq_rect
                                                                                        (Datatypes.app a0
                                                                                          (Datatypes.app h3 (Datatypes.Coq_cons a (Datatypes.app h6 (Datatypes.app b d2)))))
                                                                                        acm11
                                                                                        (Datatypes.app (Datatypes.app a0 h3) (Datatypes.Coq_cons a
                                                                                          (Datatypes.app h6 (Datatypes.app b d2))))))) h1r drs8 acm8) c0) h0 acm7 drs7) h1l
                                                                            drs6 acm6;
                                                                         Datatypes.Coq_inr _ ->
                                                                          Logic.eq_rect_r (Datatypes.app a0 h0) (\drs7 acm7 ->
                                                                            Logic.eq_rect_r (Datatypes.app b h3) (\acm8 drs8 ->
                                                                              Logic.eq_rect_r (Datatypes.app c0 h6) (\_ acm9 ->
                                                                                Logic.eq_rect_r (Datatypes.app h6 h1r) (DdT.Coq_derI
                                                                                  (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                    (Datatypes.Coq_pair
                                                                                    (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                      (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                  (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h6 h1r)))) _UU0394_0)
                                                                                    d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                    Datatypes.Coq_nil)))
                                                                                  (unsafeCoerce rs0
                                                                                    (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                      (Datatypes.Coq_pair
                                                                                      (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                        (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                    (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h6 h1r))))
                                                                                      _UU0394_0) d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                      Datatypes.Coq_nil)))
                                                                                    (LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                      (Datatypes.Coq_pair
                                                                                      (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                        (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil)
                                                                                      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h6 h1r))))
                                                                                      _UU0394_0) d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                      Datatypes.Coq_nil)) g1
                                                                                      (let {
                                                                                        _evar_0_ = let {
                                                                                                    _evar_0_ = let {
                                                                                                                _evar_0_ = WBox2Ls a d0
                                                                                                                 (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                                                 h1r h2l h2r _UU0394_0 k2}
                                                                                                               in
                                                                                                               Logic.eq_rect_r
                                                                                                                 (Datatypes.app
                                                                                                                   (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                                                   h1r) _evar_0_
                                                                                                                 (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                                   (Datatypes.app h6 h1r))}
                                                                                                   in
                                                                                                   Logic.eq_rect_r
                                                                                                     (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                       (Datatypes.app h6 h1r)) _evar_0_
                                                                                                     (Datatypes.app (Datatypes.app a0 c0)
                                                                                                       (Datatypes.app b (Datatypes.app h6 h1r)))}
                                                                                       in
                                                                                       Logic.eq_rect_r
                                                                                         (Datatypes.app (Datatypes.app a0 c0) (Datatypes.app b (Datatypes.app h6 h1r)))
                                                                                         _evar_0_
                                                                                         (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h6 h1r)))))))
                                                                                  (let {f = LntT.nslclext g1} in
                                                                                   let {
                                                                                    c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                       (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil}
                                                                                   in
                                                                                   (case DdT.dersrec_map_single f c1 of {
                                                                                     Datatypes.Coq_pair _ x0 -> x0})
                                                                                     (let {
                                                                                       x0 = \_ _ _ f0 x0 ->
                                                                                        case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                         Datatypes.Coq_pair _ x1 -> x1}}
                                                                                      in
                                                                                      let {
                                                                                       acm10 = x0 __ __ __ (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                 (Datatypes.Coq_pair
                                                                                                 (Datatypes.app (Datatypes.app a0 (Datatypes.app b (Datatypes.app c0 h6)))
                                                                                                   (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil) acm9}
                                                                                      in
                                                                                      let {
                                                                                       x1 = \_ ns0 ->
                                                                                        case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                         Datatypes.Coq_pair x1 _ -> x1}}
                                                                                      in
                                                                                      let {
                                                                                       acm11 = x1 __
                                                                                                 (LntT.nslclext g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                   (Datatypes.Coq_pair
                                                                                                   (Datatypes.app (Datatypes.app a0 (Datatypes.app b (Datatypes.app c0 h6)))
                                                                                                     (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil)) acm10 g1
                                                                                                 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app c0 (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))))
                                                                                                 _UU0394_0)
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app c0 (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))))
                                                                                                 _UU0394_0
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app c0
                                                                                                     (Datatypes.app b (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))) d0
                                                                                                 (SwappedT.swapped_L
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app c0 (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))
                                                                                                   (Datatypes.app c0
                                                                                                     (Datatypes.app b (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))) a0
                                                                                                   (Logic.eq_rec_r
                                                                                                     (Datatypes.app (Datatypes.app b c0)
                                                                                                       (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))
                                                                                                     (Logic.eq_rec_r
                                                                                                       (Datatypes.app (Datatypes.app (Datatypes.app b c0) h6)
                                                                                                         (Datatypes.Coq_cons a h1r))
                                                                                                       (Logic.eq_rec_r
                                                                                                         (Datatypes.app (Datatypes.app c0 b)
                                                                                                           (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))
                                                                                                         (Logic.eq_rec_r
                                                                                                           (Datatypes.app (Datatypes.app (Datatypes.app c0 b) h6)
                                                                                                             (Datatypes.Coq_cons a h1r))
                                                                                                           (SwappedT.swapped_R (Datatypes.app (Datatypes.app b c0) h6)
                                                                                                             (Datatypes.app (Datatypes.app c0 b) h6) (Datatypes.Coq_cons a
                                                                                                             h1r)
                                                                                                             (SwappedT.swapped_R (Datatypes.app b c0) (Datatypes.app c0 b) h6
                                                                                                               (Gen.arg_cong_imp (Datatypes.app c0 b) (Datatypes.app c0 b)
                                                                                                                 (SwappedT.swapped_simpleL b c0 c0))))
                                                                                                           (Datatypes.app (Datatypes.app c0 b)
                                                                                                             (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))
                                                                                                         (Datatypes.app c0
                                                                                                           (Datatypes.app b (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))))
                                                                                                       (Datatypes.app (Datatypes.app b c0)
                                                                                                         (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))
                                                                                                     (Datatypes.app b
                                                                                                       (Datatypes.app c0 (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))))) __
                                                                                                 __}
                                                                                      in
                                                                                      let {
                                                                                       _evar_0_ = let {
                                                                                                   _evar_0_ = Logic.eq_rect
                                                                                                                (Datatypes.app a0
                                                                                                                  (Datatypes.app c0
                                                                                                                    (Datatypes.app b
                                                                                                                      (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))) acm11
                                                                                                                (Datatypes.app (Datatypes.app a0 c0)
                                                                                                                  (Datatypes.app b
                                                                                                                    (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))}
                                                                                                  in
                                                                                                  Logic.eq_rect
                                                                                                    (Datatypes.app (Datatypes.app a0 c0)
                                                                                                      (Datatypes.app b (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))
                                                                                                    _evar_0_
                                                                                                    (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                      (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))}
                                                                                      in
                                                                                      Logic.eq_rect
                                                                                        (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                          (Datatypes.app h6 (Datatypes.Coq_cons a h1r))) _evar_0_
                                                                                        (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                          (Datatypes.Coq_cons a h1r))))) d2) h3 drs8 acm8) h0 acm7 drs7) h1l drs6 acm6}}}};
                                                                 Datatypes.Coq_inr _ ->
                                                                  Logic.eq_rect_r (Datatypes.app h1l h0)
                                                                    (Logic.eq_rect_r (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))) (\_ acm7 -> DdT.Coq_derI
                                                                      (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                        (Datatypes.Coq_pair
                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))))
                                                                        _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                      (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                        (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2))) _UU0394_0) d0)
                                                                        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil)))
                                                                      (unsafeCoerce rs0
                                                                        (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                          (Datatypes.Coq_pair
                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                            (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) _UU0394_0) d0) Datatypes.Coq_nil)
                                                                          Datatypes.Coq_nil))
                                                                        (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                          (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2))) _UU0394_0) d0)
                                                                          (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil)))
                                                                        (let {
                                                                          _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                       (Datatypes.Coq_pair
                                                                                       (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                         (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) _UU0394_0) d0)
                                                                                       Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                       (Datatypes.Coq_pair
                                                                                       (Datatypes.app h1l (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))
                                                                                       _UU0394_0) d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                       (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                       Datatypes.Coq_nil)) g1
                                                                                       (let {
                                                                                         _evar_0_ = let {
                                                                                                     _evar_0_ = WBox2Ls a d0 h1l
                                                                                                      (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))) h2l h2r
                                                                                                      _UU0394_0 k2}
                                                                                                    in
                                                                                                    Logic.eq_rect
                                                                                                      (Datatypes.app h1l
                                                                                                        (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))) _evar_0_
                                                                                                      (Datatypes.app (Datatypes.app h1l h0)
                                                                                                        (Datatypes.app c0 (Datatypes.app b d2)))}
                                                                                        in
                                                                                        Logic.eq_rect_r
                                                                                          (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2)))
                                                                                          _evar_0_
                                                                                          (Datatypes.app h1l (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))))}
                                                                         in
                                                                         Logic.eq_rect (Datatypes.app h1l (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))
                                                                           _evar_0_ (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2)))))
                                                                      (let {f = LntT.nslclext g1} in
                                                                       let {
                                                                        c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                         (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                           (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) _UU0394_0) d0) Datatypes.Coq_nil}
                                                                       in
                                                                       (case DdT.dersrec_map_single f c1 of {
                                                                         Datatypes.Coq_pair _ x0 -> x0})
                                                                         (let {x0 = \_ _ _ f0 x0 -> case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                                     Datatypes.Coq_pair _ x1 -> x1}}
                                                                          in
                                                                          let {
                                                                           acm8 = x0 __ __ __ (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                      (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) _UU0394_0) d0)
                                                                                    Datatypes.Coq_nil) acm7}
                                                                          in
                                                                          let {
                                                                           ns0 = LntT.nslclext g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) _UU0394_0) d0)
                                                                                   Datatypes.Coq_nil)}
                                                                          in
                                                                          (case LntacsT.can_gen_swapL_def' ns0 of {
                                                                            Datatypes.Coq_pair x1 _ -> x1}) acm8 g1 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                            (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                              (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) _UU0394_0)
                                                                            (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                              (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) _UU0394_0
                                                                            (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                              (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) d0
                                                                            (SwappedT.swapped_L (Datatypes.Coq_cons a
                                                                              (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2)))) (Datatypes.Coq_cons a
                                                                              (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))) h1l
                                                                              (SwappedT.swapped_cons a (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2)))
                                                                                (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))
                                                                                (SwappedT.swapped_L (Datatypes.app b (Datatypes.app c0 d2))
                                                                                  (Datatypes.app c0 (Datatypes.app b d2)) h0
                                                                                  (Logic.eq_rec_r (Datatypes.app (Datatypes.app b c0) d2)
                                                                                    (Logic.eq_rec_r (Datatypes.app (Datatypes.app c0 b) d2)
                                                                                      (SwappedT.swapped_R (Datatypes.app b c0) (Datatypes.app c0 b) d2
                                                                                        (Gen.arg_cong_imp (Datatypes.app c0 b) (Datatypes.app c0 b)
                                                                                          (SwappedT.swapped_simpleL b c0 c0))) (Datatypes.app c0 (Datatypes.app b d2)))
                                                                                    (Datatypes.app b (Datatypes.app c0 d2)))))) __ __))) h1r drs6 acm6) a0}}) _UU0393_') y) x
                                                         __ __ __)}) __ __) k0 sppc5) d1 acm5 drs5 sppc4) k1 drs4 acm4 sppc3) _UU0393_ sppc2 swap) ps0 acm3 drs3 sppc1) k0)
                                        d1) k1) _UU0393_ __ __ __) ps0 __);
                               BBox2Ls a d1 h1l h1r h2l h2r k1 k2 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r))
                                  k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect (Datatypes.app h1l h1r) (\_ ->
                                    Logic.eq_rect_r _UU0394_0 (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r))
                                          k2) LntT.Coq_fwd) Datatypes.Coq_nil)
                                          (Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                            (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\acm4 drs4 sppc2 ->
                                            Logic.eq_rect (Datatypes.app h1l h1r) (\sppc3 swap0 ->
                                              Logic.eq_rect_r _UU0394_0 (\drs5 acm5 sppc4 ->
                                                Logic.eq_rect_r d0 (\acm6 drs6 sppc5 ->
                                                  Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                    (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil) (\_ ->
                                                    (case swap0 of {
                                                      SwappedT.Coq_swapped_I x y a0 b c0 d2 -> (\_ _ ->
                                                       Logic.eq_rect_r (Datatypes.app h1l h1r) (\_ ->
                                                         Logic.eq_rect_r _UU0393_' (\_ _ ->
                                                           Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b d2)))
                                                             (let {h = List_lemmasT.app_eq_appT2 h1l h1r a0 (Datatypes.app b (Datatypes.app c0 d2))} in
                                                              case h of {
                                                               Specif.Coq_existT h0 h1 ->
                                                                case h1 of {
                                                                 Datatypes.Coq_inl _ ->
                                                                  let {h2 = List_lemmasT.app_eq_appT2 b (Datatypes.app c0 d2) h0 h1r} in
                                                                  case h2 of {
                                                                   Specif.Coq_existT h3 h4 ->
                                                                    case h4 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                      Logic.eq_rect_r (Datatypes.app a0 h0) (\drs7 acm7 ->
                                                                        Logic.eq_rect_r (Datatypes.app h0 h3)
                                                                          (Logic.eq_rect_r (Datatypes.app h3 (Datatypes.app c0 d2)) (\acm8 _ -> DdT.Coq_derI
                                                                            (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                              (Datatypes.Coq_pair
                                                                              (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                (Datatypes.app h3 d2))) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                            (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                              (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app (Datatypes.app h0 h3) d2))) _UU0394_0) d0)
                                                                              (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                              (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                              Datatypes.Coq_nil)))
                                                                            (unsafeCoerce rs0
                                                                              (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                (Datatypes.Coq_pair
                                                                                (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                  (Datatypes.app h3 d2))) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                              (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app (Datatypes.app h0 h3) d2))) _UU0394_0) d0)
                                                                                (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                Datatypes.Coq_nil)))
                                                                              (let {
                                                                                _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                             (Datatypes.Coq_pair
                                                                                             (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h3 d2))) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil)
                                                                                             (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app h0 (Datatypes.app h3 d2))))
                                                                                             _UU0394_0) d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                             Datatypes.Coq_nil)) g1
                                                                                             (let {
                                                                                               _evar_0_ = let {
                                                                                                           _evar_0_ = let {
                                                                                                                       _evar_0_ = let {
                                                                                                                                   _evar_0_ = BBox2Ls a d0
                                                                                                                                    (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                                                    (Datatypes.app h3 d2) h2l h2r _UU0394_0
                                                                                                                                    k2}
                                                                                                                                  in
                                                                                                                                  Logic.eq_rect
                                                                                                                                    (Datatypes.app
                                                                                                                                      (Datatypes.app (Datatypes.app a0 c0)
                                                                                                                                        h0) (Datatypes.app h3 d2)) _evar_0_
                                                                                                                                    (Datatypes.app
                                                                                                                                      (Datatypes.app
                                                                                                                                        (Datatypes.app (Datatypes.app a0 c0)
                                                                                                                                          h0) h3) d2)}
                                                                                                                      in
                                                                                                                      Logic.eq_rect_r
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app
                                                                                                                            (Datatypes.app (Datatypes.app a0 c0) h0) h3) d2)
                                                                                                                        _evar_0_
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                                          (Datatypes.app h3 d2))}
                                                                                                          in
                                                                                                          Logic.eq_rect_r
                                                                                                            (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                              (Datatypes.app h3 d2)) _evar_0_
                                                                                                            (Datatypes.app (Datatypes.app a0 c0)
                                                                                                              (Datatypes.app h0 (Datatypes.app h3 d2)))}
                                                                                              in
                                                                                              Logic.eq_rect_r
                                                                                                (Datatypes.app (Datatypes.app a0 c0)
                                                                                                  (Datatypes.app h0 (Datatypes.app h3 d2))) _evar_0_
                                                                                                (Datatypes.app a0
                                                                                                  (Datatypes.app c0 (Datatypes.app h0 (Datatypes.app h3 d2)))))}
                                                                               in
                                                                               Logic.eq_rect (Datatypes.app h0 (Datatypes.app h3 d2)) _evar_0_
                                                                                 (Datatypes.app (Datatypes.app h0 h3) d2)))
                                                                            (let {f = LntT.nslclext g1} in
                                                                             let {
                                                                              c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                               (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                 (Datatypes.app h3 d2))) _UU0394_0) d0) Datatypes.Coq_nil}
                                                                             in
                                                                             (case DdT.dersrec_map_single f c1 of {
                                                                               Datatypes.Coq_pair _ x0 -> x0})
                                                                               (let {
                                                                                 x0 = \_ _ _ f0 x0 ->
                                                                                  case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                   Datatypes.Coq_pair _ x1 -> x1}}
                                                                                in
                                                                                let {
                                                                                 acm9 = x0 __ __ __ (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                          (Datatypes.Coq_pair
                                                                                          (Datatypes.app (Datatypes.app a0 h0) (Datatypes.Coq_cons a
                                                                                            (Datatypes.app h3 (Datatypes.app c0 d2)))) _UU0394_0) d0) Datatypes.Coq_nil) acm8}
                                                                                in
                                                                                let {x1 = \_ ns0 -> case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                                     Datatypes.Coq_pair x1 _ -> x1}}
                                                                                in
                                                                                let {
                                                                                 acm10 = x1 __
                                                                                           (LntT.nslclext g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app (Datatypes.app a0 h0) (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h3 (Datatypes.app c0 d2)))) _UU0394_0) d0) Datatypes.Coq_nil))
                                                                                           acm9 g1 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                           (Datatypes.app a0
                                                                                             (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h3 (Datatypes.app c0 d2))))) _UU0394_0)
                                                                                           (Datatypes.app a0
                                                                                             (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h3 (Datatypes.app c0 d2))))) _UU0394_0
                                                                                           (Datatypes.app a0
                                                                                             (Datatypes.app c0
                                                                                               (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2))))) d0
                                                                                           (SwappedT.swapped_L
                                                                                             (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h3 (Datatypes.app c0 d2))))
                                                                                             (Datatypes.app c0
                                                                                               (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2)))) a0
                                                                                             (Logic.eq_rec_r (Datatypes.app (Datatypes.app h3 c0) d2)
                                                                                               (Logic.eq_rec_r
                                                                                                 (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons a
                                                                                                   (Datatypes.app h3 d2)))
                                                                                                 (Logic.eq_rec_r
                                                                                                   (Datatypes.app (Datatypes.Coq_cons a (Datatypes.app h3 c0)) d2)
                                                                                                   (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h3) c0)
                                                                                                     (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h3) d2)
                                                                                                       (Logic.eq_rec_r
                                                                                                         (Datatypes.app
                                                                                                           (Datatypes.app h0 (Datatypes.app (Datatypes.Coq_cons a h3) c0))
                                                                                                           d2)
                                                                                                         (Logic.eq_rec_r
                                                                                                           (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons a h3)) c0)
                                                                                                           (Logic.eq_rec_r
                                                                                                             (Datatypes.app
                                                                                                               (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons a
                                                                                                                 h3)) d2)
                                                                                                             (SwappedT.swapped_R
                                                                                                               (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons a h3))
                                                                                                                 c0)
                                                                                                               (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons a
                                                                                                                 h3)) d2
                                                                                                               (let {
                                                                                                                 _evar_0_ = let {
                                                                                                                             _evar_0_ = let {
                                                                                                                                         _evar_0_ = Gen.arg1_cong_imp
                                                                                                                                                      (Datatypes.app
                                                                                                                                                        (Datatypes.app h0
                                                                                                                                                          (Datatypes.Coq_cons
                                                                                                                                                          a h3)) c0)
                                                                                                                                                      (Datatypes.app h0
                                                                                                                                                        (Datatypes.Coq_cons a
                                                                                                                                                        (Datatypes.app h3 c0)))
                                                                                                                                                      (Datatypes.app c0
                                                                                                                                                        (Datatypes.app h0
                                                                                                                                                          (Datatypes.Coq_cons
                                                                                                                                                          a h3)))
                                                                                                                                                      (SwappedT.swapped_simpleR
                                                                                                                                                        c0
                                                                                                                                                        (Datatypes.app h0
                                                                                                                                                          (Datatypes.Coq_cons
                                                                                                                                                          a h3))
                                                                                                                                                        (Datatypes.app h0
                                                                                                                                                          (Datatypes.Coq_cons
                                                                                                                                                          a h3)))}
                                                                                                                                        in
                                                                                                                                        Logic.eq_rec (Datatypes.Coq_cons a
                                                                                                                                          (Datatypes.app h3 c0)) _evar_0_
                                                                                                                                          (Datatypes.app (Datatypes.Coq_cons
                                                                                                                                            a h3) c0)}
                                                                                                                            in
                                                                                                                            Logic.eq_rec
                                                                                                                              (Datatypes.app c0
                                                                                                                                (Datatypes.app h0 (Datatypes.Coq_cons a h3)))
                                                                                                                              _evar_0_
                                                                                                                              (Datatypes.app (Datatypes.app c0 h0)
                                                                                                                                (Datatypes.Coq_cons a h3))}
                                                                                                                in
                                                                                                                Logic.eq_rec
                                                                                                                  (Datatypes.app h0
                                                                                                                    (Datatypes.app (Datatypes.Coq_cons a h3) c0)) _evar_0_
                                                                                                                  (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons a h3))
                                                                                                                    c0)))
                                                                                                             (Datatypes.app (Datatypes.app c0 h0)
                                                                                                               (Datatypes.app (Datatypes.Coq_cons a h3) d2)))
                                                                                                           (Datatypes.app h0 (Datatypes.app (Datatypes.Coq_cons a h3) c0)))
                                                                                                         (Datatypes.app h0
                                                                                                           (Datatypes.app (Datatypes.app (Datatypes.Coq_cons a h3) c0) d2)))
                                                                                                       (Datatypes.Coq_cons a (Datatypes.app h3 d2))) (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h3 c0))) (Datatypes.Coq_cons a
                                                                                                   (Datatypes.app (Datatypes.app h3 c0) d2)))
                                                                                                 (Datatypes.app c0
                                                                                                   (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2)))))
                                                                                               (Datatypes.app h3 (Datatypes.app c0 d2)))) __ __}
                                                                                in
                                                                                let {
                                                                                 _evar_0_ = Logic.eq_rect
                                                                                              (Datatypes.app a0
                                                                                                (Datatypes.app c0
                                                                                                  (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2))))) acm10
                                                                                              (Datatypes.app (Datatypes.app a0 c0)
                                                                                                (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2))))}
                                                                                in
                                                                                Logic.eq_rect
                                                                                  (Datatypes.app (Datatypes.app a0 c0)
                                                                                    (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h3 d2)))) _evar_0_
                                                                                  (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                    (Datatypes.app h3 d2)))))) h1r acm7 drs7) b) h1l drs6 acm6;
                                                                     Datatypes.Coq_inr _ ->
                                                                      let {h5 = List_lemmasT.app_eq_appT2 c0 d2 h3 h1r} in
                                                                      case h5 of {
                                                                       Specif.Coq_existT h6 h7 ->
                                                                        case h7 of {
                                                                         Datatypes.Coq_inl _ ->
                                                                          Logic.eq_rect_r (Datatypes.app a0 h0) (\drs7 acm7 ->
                                                                            Logic.eq_rect_r (Datatypes.app b h3) (\acm8 drs8 ->
                                                                              Logic.eq_rect_r (Datatypes.app h3 h6)
                                                                                (Logic.eq_rect_r (Datatypes.app h6 d2) (\_ acm9 -> DdT.Coq_derI
                                                                                  (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                    (Datatypes.Coq_pair
                                                                                    (Datatypes.app (Datatypes.app a0 h3) (Datatypes.Coq_cons a
                                                                                      (Datatypes.app h6 (Datatypes.app b d2)))) _UU0394_0) d0) Datatypes.Coq_nil)
                                                                                    Datatypes.Coq_nil))
                                                                                  (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app a0 (Datatypes.app (Datatypes.app h3 h6) (Datatypes.app b d2))) _UU0394_0)
                                                                                    d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                    Datatypes.Coq_nil)))
                                                                                  (unsafeCoerce rs0
                                                                                    (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                      (Datatypes.Coq_pair
                                                                                      (Datatypes.app (Datatypes.app a0 h3) (Datatypes.Coq_cons a
                                                                                        (Datatypes.app h6 (Datatypes.app b d2)))) _UU0394_0) d0) Datatypes.Coq_nil)
                                                                                      Datatypes.Coq_nil))
                                                                                    (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app a0 (Datatypes.app (Datatypes.app h3 h6) (Datatypes.app b d2)))
                                                                                      _UU0394_0) d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                      Datatypes.Coq_nil)))
                                                                                    (let {
                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                   (Datatypes.app (Datatypes.app a0 h3) (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h6 (Datatypes.app b d2)))) _UU0394_0) d0)
                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                   (Datatypes.app a0
                                                                                                     (Datatypes.app h3 (Datatypes.app h6 (Datatypes.app b d2)))) _UU0394_0)
                                                                                                   d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                   (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2)
                                                                                                   LntT.Coq_fwd) Datatypes.Coq_nil)) g1
                                                                                                   (let {
                                                                                                     _evar_0_ = let {
                                                                                                                 _evar_0_ = let {
                                                                                                                             _evar_0_ = BBox2Ls a d0 (Datatypes.app a0 h3)
                                                                                                                              (Datatypes.app h6 (Datatypes.app b d2)) h2l h2r
                                                                                                                              _UU0394_0 k2}
                                                                                                                            in
                                                                                                                            Logic.eq_rect
                                                                                                                              (Datatypes.app (Datatypes.app a0 h3)
                                                                                                                                (Datatypes.app h6 (Datatypes.app b d2)))
                                                                                                                              _evar_0_
                                                                                                                              (Datatypes.app
                                                                                                                                (Datatypes.app (Datatypes.app a0 h3) h6)
                                                                                                                                (Datatypes.app b d2))}
                                                                                                                in
                                                                                                                Logic.eq_rect_r
                                                                                                                  (Datatypes.app (Datatypes.app (Datatypes.app a0 h3) h6)
                                                                                                                    (Datatypes.app b d2)) _evar_0_
                                                                                                                  (Datatypes.app (Datatypes.app a0 h3)
                                                                                                                    (Datatypes.app h6 (Datatypes.app b d2)))}
                                                                                                    in
                                                                                                    Logic.eq_rect_r
                                                                                                      (Datatypes.app (Datatypes.app a0 h3)
                                                                                                        (Datatypes.app h6 (Datatypes.app b d2))) _evar_0_
                                                                                                      (Datatypes.app a0
                                                                                                        (Datatypes.app h3 (Datatypes.app h6 (Datatypes.app b d2)))))}
                                                                                     in
                                                                                     Logic.eq_rect (Datatypes.app h3 (Datatypes.app h6 (Datatypes.app b d2))) _evar_0_
                                                                                       (Datatypes.app (Datatypes.app h3 h6) (Datatypes.app b d2))))
                                                                                  (let {f = LntT.nslclext g1} in
                                                                                   let {
                                                                                    c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app (Datatypes.app a0 h3) (Datatypes.Coq_cons a
                                                                                       (Datatypes.app h6 (Datatypes.app b d2)))) _UU0394_0) d0) Datatypes.Coq_nil}
                                                                                   in
                                                                                   (case DdT.dersrec_map_single f c1 of {
                                                                                     Datatypes.Coq_pair _ x0 -> x0})
                                                                                     (let {
                                                                                       x0 = \_ _ _ f0 x0 ->
                                                                                        case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                         Datatypes.Coq_pair _ x1 -> x1}}
                                                                                      in
                                                                                      let {
                                                                                       acm10 = x0 __ __ __ (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                 (Datatypes.Coq_pair
                                                                                                 (Datatypes.app (Datatypes.app a0 (Datatypes.app b h3)) (Datatypes.Coq_cons a
                                                                                                   (Datatypes.app h6 d2))) _UU0394_0) d0) Datatypes.Coq_nil) acm9}
                                                                                      in
                                                                                      let {
                                                                                       x1 = \_ ns0 ->
                                                                                        case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                         Datatypes.Coq_pair x1 _ -> x1}}
                                                                                      in
                                                                                      let {
                                                                                       acm11 = x1 __
                                                                                                 (LntT.nslclext g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                   (Datatypes.Coq_pair
                                                                                                   (Datatypes.app (Datatypes.app a0 (Datatypes.app b h3)) (Datatypes.Coq_cons
                                                                                                     a (Datatypes.app h6 d2))) _UU0394_0) d0) Datatypes.Coq_nil)) acm10 g1
                                                                                                 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app h3 (Datatypes.Coq_cons a (Datatypes.app h6 d2)))))
                                                                                                 _UU0394_0)
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app h3 (Datatypes.Coq_cons a (Datatypes.app h6 d2)))))
                                                                                                 _UU0394_0
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app h3 (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h6 (Datatypes.app b d2))))) d0
                                                                                                 (SwappedT.swapped_L
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app h3 (Datatypes.Coq_cons a (Datatypes.app h6 d2))))
                                                                                                   (Datatypes.app h3 (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h6 (Datatypes.app b d2)))) a0
                                                                                                   (Logic.eq_rec_r
                                                                                                     (Datatypes.app (Datatypes.app b h3) (Datatypes.Coq_cons a
                                                                                                       (Datatypes.app h6 d2)))
                                                                                                     (Logic.eq_rec_r (Datatypes.app (Datatypes.app h6 b) d2)
                                                                                                       (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h6) d2)
                                                                                                         (Logic.eq_rec_r
                                                                                                           (Datatypes.app (Datatypes.Coq_cons a (Datatypes.app h6 b)) d2)
                                                                                                           (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h6) b)
                                                                                                             (Logic.eq_rec_r
                                                                                                               (Datatypes.app
                                                                                                                 (Datatypes.app (Datatypes.app b h3) (Datatypes.Coq_cons a
                                                                                                                   h6)) d2)
                                                                                                               (Logic.eq_rec_r
                                                                                                                 (Datatypes.app
                                                                                                                   (Datatypes.app h3
                                                                                                                     (Datatypes.app (Datatypes.Coq_cons a h6) b)) d2)
                                                                                                                 (Logic.eq_rec_r
                                                                                                                   (Datatypes.app
                                                                                                                     (Datatypes.app h3 (Datatypes.Coq_cons a h6)) b)
                                                                                                                   (SwappedT.swapped_R
                                                                                                                     (Datatypes.app (Datatypes.app b h3) (Datatypes.Coq_cons
                                                                                                                       a h6))
                                                                                                                     (Datatypes.app
                                                                                                                       (Datatypes.app h3 (Datatypes.Coq_cons a h6)) b) d2
                                                                                                                     (let {
                                                                                                                       _evar_0_ = let {
                                                                                                                                   _evar_0_ = let {
                                                                                                                                               _evar_0_ = Gen.arg_cong_imp
                                                                                                                                                            (Datatypes.app
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h3
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h6)) b)
                                                                                                                                                            (Datatypes.app h3
                                                                                                                                                              (Datatypes.Coq_cons
                                                                                                                                                              a
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h6 b)))
                                                                                                                                                            (SwappedT.swapped_simpleL
                                                                                                                                                              b
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h3
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h6))
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h3
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h6)))}
                                                                                                                                              in
                                                                                                                                              Logic.eq_rec
                                                                                                                                                (Datatypes.Coq_cons a
                                                                                                                                                (Datatypes.app h6 b))
                                                                                                                                                _evar_0_
                                                                                                                                                (Datatypes.app
                                                                                                                                                  (Datatypes.Coq_cons a h6)
                                                                                                                                                  b)}
                                                                                                                                  in
                                                                                                                                  Logic.eq_rec
                                                                                                                                    (Datatypes.app h3
                                                                                                                                      (Datatypes.app (Datatypes.Coq_cons a
                                                                                                                                        h6) b)) _evar_0_
                                                                                                                                    (Datatypes.app
                                                                                                                                      (Datatypes.app h3 (Datatypes.Coq_cons a
                                                                                                                                        h6)) b)}
                                                                                                                      in
                                                                                                                      Logic.eq_rec
                                                                                                                        (Datatypes.app b
                                                                                                                          (Datatypes.app h3 (Datatypes.Coq_cons a h6)))
                                                                                                                        _evar_0_
                                                                                                                        (Datatypes.app (Datatypes.app b h3)
                                                                                                                          (Datatypes.Coq_cons a h6))))
                                                                                                                   (Datatypes.app h3
                                                                                                                     (Datatypes.app (Datatypes.Coq_cons a h6) b)))
                                                                                                                 (Datatypes.app h3
                                                                                                                   (Datatypes.app (Datatypes.app (Datatypes.Coq_cons a h6) b)
                                                                                                                     d2)))
                                                                                                               (Datatypes.app (Datatypes.app b h3)
                                                                                                                 (Datatypes.app (Datatypes.Coq_cons a h6) d2)))
                                                                                                             (Datatypes.Coq_cons a (Datatypes.app h6 b))) (Datatypes.Coq_cons
                                                                                                           a (Datatypes.app (Datatypes.app h6 b) d2))) (Datatypes.Coq_cons a
                                                                                                         (Datatypes.app h6 d2))) (Datatypes.app h6 (Datatypes.app b d2)))
                                                                                                     (Datatypes.app b
                                                                                                       (Datatypes.app h3 (Datatypes.Coq_cons a (Datatypes.app h6 d2)))))) __
                                                                                                 __}
                                                                                      in
                                                                                      Logic.eq_rect
                                                                                        (Datatypes.app a0
                                                                                          (Datatypes.app h3 (Datatypes.Coq_cons a (Datatypes.app h6 (Datatypes.app b d2)))))
                                                                                        acm11
                                                                                        (Datatypes.app (Datatypes.app a0 h3) (Datatypes.Coq_cons a
                                                                                          (Datatypes.app h6 (Datatypes.app b d2))))))) h1r drs8 acm8) c0) h0 acm7 drs7) h1l
                                                                            drs6 acm6;
                                                                         Datatypes.Coq_inr _ ->
                                                                          Logic.eq_rect_r (Datatypes.app a0 h0) (\drs7 acm7 ->
                                                                            Logic.eq_rect_r (Datatypes.app b h3) (\acm8 drs8 ->
                                                                              Logic.eq_rect_r (Datatypes.app c0 h6) (\_ acm9 ->
                                                                                Logic.eq_rect_r (Datatypes.app h6 h1r) (DdT.Coq_derI
                                                                                  (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                    (Datatypes.Coq_pair
                                                                                    (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                      (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                  (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h6 h1r)))) _UU0394_0)
                                                                                    d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                    Datatypes.Coq_nil)))
                                                                                  (unsafeCoerce rs0
                                                                                    (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                      (Datatypes.Coq_pair
                                                                                      (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                        (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                    (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h6 h1r))))
                                                                                      _UU0394_0) d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                      Datatypes.Coq_nil)))
                                                                                    (LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                      (Datatypes.Coq_pair
                                                                                      (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                        (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil)
                                                                                      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h6 h1r))))
                                                                                      _UU0394_0) d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                      Datatypes.Coq_nil)) g1
                                                                                      (let {
                                                                                        _evar_0_ = let {
                                                                                                    _evar_0_ = let {
                                                                                                                _evar_0_ = BBox2Ls a d0
                                                                                                                 (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                                                 h1r h2l h2r _UU0394_0 k2}
                                                                                                               in
                                                                                                               Logic.eq_rect_r
                                                                                                                 (Datatypes.app
                                                                                                                   (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                                                   h1r) _evar_0_
                                                                                                                 (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                                   (Datatypes.app h6 h1r))}
                                                                                                   in
                                                                                                   Logic.eq_rect_r
                                                                                                     (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                       (Datatypes.app h6 h1r)) _evar_0_
                                                                                                     (Datatypes.app (Datatypes.app a0 c0)
                                                                                                       (Datatypes.app b (Datatypes.app h6 h1r)))}
                                                                                       in
                                                                                       Logic.eq_rect_r
                                                                                         (Datatypes.app (Datatypes.app a0 c0) (Datatypes.app b (Datatypes.app h6 h1r)))
                                                                                         _evar_0_
                                                                                         (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h6 h1r)))))))
                                                                                  (let {f = LntT.nslclext g1} in
                                                                                   let {
                                                                                    c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                       (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil}
                                                                                   in
                                                                                   (case DdT.dersrec_map_single f c1 of {
                                                                                     Datatypes.Coq_pair _ x0 -> x0})
                                                                                     (let {
                                                                                       x0 = \_ _ _ f0 x0 ->
                                                                                        case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                         Datatypes.Coq_pair _ x1 -> x1}}
                                                                                      in
                                                                                      let {
                                                                                       acm10 = x0 __ __ __ (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                 (Datatypes.Coq_pair
                                                                                                 (Datatypes.app (Datatypes.app a0 (Datatypes.app b (Datatypes.app c0 h6)))
                                                                                                   (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil) acm9}
                                                                                      in
                                                                                      let {
                                                                                       x1 = \_ ns0 ->
                                                                                        case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                         Datatypes.Coq_pair x1 _ -> x1}}
                                                                                      in
                                                                                      let {
                                                                                       acm11 = x1 __
                                                                                                 (LntT.nslclext g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                   (Datatypes.Coq_pair
                                                                                                   (Datatypes.app (Datatypes.app a0 (Datatypes.app b (Datatypes.app c0 h6)))
                                                                                                     (Datatypes.Coq_cons a h1r)) _UU0394_0) d0) Datatypes.Coq_nil)) acm10 g1
                                                                                                 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app c0 (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))))
                                                                                                 _UU0394_0)
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app c0 (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))))
                                                                                                 _UU0394_0
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app c0
                                                                                                     (Datatypes.app b (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))) d0
                                                                                                 (SwappedT.swapped_L
                                                                                                   (Datatypes.app b
                                                                                                     (Datatypes.app c0 (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))
                                                                                                   (Datatypes.app c0
                                                                                                     (Datatypes.app b (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))) a0
                                                                                                   (Logic.eq_rec_r
                                                                                                     (Datatypes.app (Datatypes.app b c0)
                                                                                                       (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))
                                                                                                     (Logic.eq_rec_r
                                                                                                       (Datatypes.app (Datatypes.app (Datatypes.app b c0) h6)
                                                                                                         (Datatypes.Coq_cons a h1r))
                                                                                                       (Logic.eq_rec_r
                                                                                                         (Datatypes.app (Datatypes.app c0 b)
                                                                                                           (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))
                                                                                                         (Logic.eq_rec_r
                                                                                                           (Datatypes.app (Datatypes.app (Datatypes.app c0 b) h6)
                                                                                                             (Datatypes.Coq_cons a h1r))
                                                                                                           (SwappedT.swapped_R (Datatypes.app (Datatypes.app b c0) h6)
                                                                                                             (Datatypes.app (Datatypes.app c0 b) h6) (Datatypes.Coq_cons a
                                                                                                             h1r)
                                                                                                             (SwappedT.swapped_R (Datatypes.app b c0) (Datatypes.app c0 b) h6
                                                                                                               (Gen.arg_cong_imp (Datatypes.app c0 b) (Datatypes.app c0 b)
                                                                                                                 (SwappedT.swapped_simpleL b c0 c0))))
                                                                                                           (Datatypes.app (Datatypes.app c0 b)
                                                                                                             (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))
                                                                                                         (Datatypes.app c0
                                                                                                           (Datatypes.app b (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))))
                                                                                                       (Datatypes.app (Datatypes.app b c0)
                                                                                                         (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))
                                                                                                     (Datatypes.app b
                                                                                                       (Datatypes.app c0 (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))))) __
                                                                                                 __}
                                                                                      in
                                                                                      let {
                                                                                       _evar_0_ = let {
                                                                                                   _evar_0_ = Logic.eq_rect
                                                                                                                (Datatypes.app a0
                                                                                                                  (Datatypes.app c0
                                                                                                                    (Datatypes.app b
                                                                                                                      (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))) acm11
                                                                                                                (Datatypes.app (Datatypes.app a0 c0)
                                                                                                                  (Datatypes.app b
                                                                                                                    (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))}
                                                                                                  in
                                                                                                  Logic.eq_rect
                                                                                                    (Datatypes.app (Datatypes.app a0 c0)
                                                                                                      (Datatypes.app b (Datatypes.app h6 (Datatypes.Coq_cons a h1r))))
                                                                                                    _evar_0_
                                                                                                    (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                      (Datatypes.app h6 (Datatypes.Coq_cons a h1r)))}
                                                                                      in
                                                                                      Logic.eq_rect
                                                                                        (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                          (Datatypes.app h6 (Datatypes.Coq_cons a h1r))) _evar_0_
                                                                                        (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h6)
                                                                                          (Datatypes.Coq_cons a h1r))))) d2) h3 drs8 acm8) h0 acm7 drs7) h1l drs6 acm6}}}};
                                                                 Datatypes.Coq_inr _ ->
                                                                  Logic.eq_rect_r (Datatypes.app h1l h0)
                                                                    (Logic.eq_rect_r (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))) (\_ acm7 -> DdT.Coq_derI
                                                                      (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                        (Datatypes.Coq_pair
                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))))
                                                                        _UU0394_0) d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                      (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                        (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2))) _UU0394_0) d0)
                                                                        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil)))
                                                                      (unsafeCoerce rs0
                                                                        (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                          (Datatypes.Coq_pair
                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                            (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) _UU0394_0) d0) Datatypes.Coq_nil)
                                                                          Datatypes.Coq_nil))
                                                                        (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                          (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2))) _UU0394_0) d0)
                                                                          (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil)))
                                                                        (let {
                                                                          _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                       (Datatypes.Coq_pair
                                                                                       (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                         (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) _UU0394_0) d0)
                                                                                       Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                       (Datatypes.Coq_pair
                                                                                       (Datatypes.app h1l (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))
                                                                                       _UU0394_0) d0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                       (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                       Datatypes.Coq_nil)) g1
                                                                                       (let {
                                                                                         _evar_0_ = let {
                                                                                                     _evar_0_ = BBox2Ls a d0 h1l
                                                                                                      (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))) h2l h2r
                                                                                                      _UU0394_0 k2}
                                                                                                    in
                                                                                                    Logic.eq_rect
                                                                                                      (Datatypes.app h1l
                                                                                                        (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))) _evar_0_
                                                                                                      (Datatypes.app (Datatypes.app h1l h0)
                                                                                                        (Datatypes.app c0 (Datatypes.app b d2)))}
                                                                                        in
                                                                                        Logic.eq_rect_r
                                                                                          (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2)))
                                                                                          _evar_0_
                                                                                          (Datatypes.app h1l (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))))}
                                                                         in
                                                                         Logic.eq_rect (Datatypes.app h1l (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))
                                                                           _evar_0_ (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2)))))
                                                                      (let {f = LntT.nslclext g1} in
                                                                       let {
                                                                        c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                         (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                           (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) _UU0394_0) d0) Datatypes.Coq_nil}
                                                                       in
                                                                       (case DdT.dersrec_map_single f c1 of {
                                                                         Datatypes.Coq_pair _ x0 -> x0})
                                                                         (let {x0 = \_ _ _ f0 x0 -> case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                                     Datatypes.Coq_pair _ x1 -> x1}}
                                                                          in
                                                                          let {
                                                                           acm8 = x0 __ __ __ (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                      (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) _UU0394_0) d0)
                                                                                    Datatypes.Coq_nil) acm7}
                                                                          in
                                                                          let {
                                                                           ns0 = LntT.nslclext g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) _UU0394_0) d0)
                                                                                   Datatypes.Coq_nil)}
                                                                          in
                                                                          (case LntacsT.can_gen_swapL_def' ns0 of {
                                                                            Datatypes.Coq_pair x1 _ -> x1}) acm8 g1 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                            (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                              (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) _UU0394_0)
                                                                            (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                              (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) _UU0394_0
                                                                            (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                              (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) d0
                                                                            (SwappedT.swapped_L (Datatypes.Coq_cons a
                                                                              (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2)))) (Datatypes.Coq_cons a
                                                                              (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))) h1l
                                                                              (SwappedT.swapped_cons a (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2)))
                                                                                (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))
                                                                                (SwappedT.swapped_L (Datatypes.app b (Datatypes.app c0 d2))
                                                                                  (Datatypes.app c0 (Datatypes.app b d2)) h0
                                                                                  (Logic.eq_rec_r (Datatypes.app (Datatypes.app b c0) d2)
                                                                                    (Logic.eq_rec_r (Datatypes.app (Datatypes.app c0 b) d2)
                                                                                      (SwappedT.swapped_R (Datatypes.app b c0) (Datatypes.app c0 b) d2
                                                                                        (Gen.arg_cong_imp (Datatypes.app c0 b) (Datatypes.app c0 b)
                                                                                          (SwappedT.swapped_simpleL b c0 c0))) (Datatypes.app c0 (Datatypes.app b d2)))
                                                                                    (Datatypes.app b (Datatypes.app c0 d2)))))) __ __))) h1r drs6 acm6) a0}}) _UU0393_') y) x
                                                         __ __ __)}) __ __) k0 sppc5) d1 acm5 drs5 sppc4) k1 drs4 acm4 sppc3) _UU0393_ sppc2 swap) ps0 acm3 drs3 sppc1) k0)
                                        d1) k1) _UU0393_ __ __ __) ps0 __)}) __ __) c sppc0) pp0 drs1 acm1) g0 acm0 drs0;
                      Datatypes.Coq_inr pp3 ->
                       case pp3 of {
                        Specif.Coq_existT pp4 _ ->
                         Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) pp4) (\_ acm2 ->
                             Logic.eq_rect_r (Datatypes.app pp4 c) (DdT.Coq_derI
                               (List.map (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4))) ps0)
                               (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) (Datatypes.app pp4 c)))
                               (unsafeCoerce rs0
                                 (List.map (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4))) ps0)
                                 (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) (Datatypes.app pp4 c)))
                                 (let {
                                   _evar_0_ = let {
                                               _evar_0_ = LntT.coq_NSlclctxt' ps0 c
                                                            (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4))
                                                            sppc0}
                                              in
                                              Logic.eq_rect_r
                                                (Datatypes.app (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4))
                                                  c) _evar_0_
                                                (Datatypes.app g1
                                                  (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4) c))}
                                  in
                                  Logic.eq_rect_r (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4) c) _evar_0_
                                    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) (Datatypes.app pp4 c))))
                               (let {
                                 cs = List.map (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4)))
                                        ps0}
                                in
                                (case DdT.dersrec_forall cs of {
                                  Datatypes.Coq_pair _ x -> x}) (\q qin ->
                                  let {x = \_ _ f l y -> case GenT.coq_InT_map_iffT f l y of {
                                                          Datatypes.Coq_pair x _ -> x}} in
                                  let {
                                   qin0 = x __ __
                                            (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4))) ps0
                                            q qin}
                                  in
                                  case qin0 of {
                                   Specif.Coq_existT x0 h ->
                                    case h of {
                                     Datatypes.Coq_pair _ h1 ->
                                      Logic.eq_rect
                                        (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4)) x0)
                                        (let {x1 = \_ _ l -> case GenT.coq_ForallT_forall l of {
                                                              Datatypes.Coq_pair x1 _ -> x1}} in
                                         let {
                                          acm3 = x1 __ __
                                                   (List.map
                                                     (LntT.nslclext
                                                       (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) pp4))) ps0) acm2
                                                   (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) pp4))
                                                     x0)
                                                   (GenT.coq_InT_map
                                                     (LntT.nslclext
                                                       (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) pp4))) ps0 x0
                                                     h1)}
                                         in
                                         let {x2 = \_ ns0 -> case LntacsT.can_gen_swapL_def' ns0 of {
                                                              Datatypes.Coq_pair x2 _ -> x2}} in
                                         let {
                                          acm4 = x2 __
                                                   (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) pp4))
                                                     x0) acm3 g1 (Datatypes.app pp4 x0) (Datatypes.Coq_pair _UU0393_ _UU0394_0) _UU0393_ _UU0394_0 _UU0393_' d0 swap __ __}
                                         in
                                         let {
                                          _evar_0_ = Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0)
                                                       (Datatypes.app pp4 x0)) acm4
                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4) x0)}
                                         in
                                         Logic.eq_rect
                                           (Datatypes.app g1 (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4) x0))
                                           _evar_0_
                                           (Datatypes.app (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4)) x0)) q}})))
                               k0) pp0 drs1 acm1) g0 acm0 drs0}};
                    Datatypes.Coq_inr _ ->
                     Logic.eq_rect_r (Datatypes.app g0 pp0)
                       (Logic.eq_rect_r (Datatypes.app pp0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) k0)) (\sppc1 ->
                         (case sppc1 of {
                           WBox2Ls a d1 h1l h1r h2l h2r k1 k2 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1)
                              d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil))
                                (Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r))
                                  k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\acm1 drs1 _ ->
                                  let {
                                   h1 = List_lemmasT.cons_eq_appT2 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil) pp0 (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) k0) (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r)
                                          k1) d1)}
                                  in
                                  case h1 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r (Datatypes.app h1l h1r) (\swap0 ->
                                        Logic.eq_rect_r k1
                                          (Logic.eq_rect_r d1
                                            (Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                              (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil)
                                              (let {
                                                _evar_0_ = (case swap0 of {
                                                             SwappedT.Coq_swapped_I x y a0 b c0 d2 -> (\_ _ ->
                                                              Logic.eq_rect_r (Datatypes.app h1l h1r) (\_ ->
                                                                Logic.eq_rect_r _UU0393_' (\_ _ ->
                                                                  Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b d2)))
                                                                    (let {h = List_lemmasT.app_eq_appT2 h1l h1r a0 (Datatypes.app b (Datatypes.app c0 d2))} in
                                                                     case h of {
                                                                      Specif.Coq_existT h0 h2 ->
                                                                       case h2 of {
                                                                        Datatypes.Coq_inl _ ->
                                                                         let {h3 = List_lemmasT.app_eq_appT2 b (Datatypes.app c0 d2) h0 h1r} in
                                                                         case h3 of {
                                                                          Specif.Coq_existT h4 h5 ->
                                                                           case h5 of {
                                                                            Datatypes.Coq_inl _ ->
                                                                             Logic.eq_rect_r (Datatypes.app a0 h0) (\drs2 acm2 ->
                                                                               Logic.eq_rect_r (Datatypes.app h0 h4)
                                                                                 (Logic.eq_rect_r (Datatypes.app h4 (Datatypes.app c0 d2)) (\acm3 _ -> DdT.Coq_derI
                                                                                   (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                     (Datatypes.Coq_pair
                                                                                     (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                       (Datatypes.app h4 d2))) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                   (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app (Datatypes.app h0 h4) d2))) k1) d1)
                                                                                     (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                     Datatypes.Coq_nil)))
                                                                                   (unsafeCoerce rs0
                                                                                     (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                       (Datatypes.Coq_pair
                                                                                       (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                         (Datatypes.app h4 d2))) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                     (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                       (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app (Datatypes.app h0 h4) d2))) k1) d1)
                                                                                       (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                       (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                       Datatypes.Coq_nil)))
                                                                                     (let {
                                                                                       _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                    (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                      (Datatypes.Coq_cons a (Datatypes.app h4 d2))) k1) d1)
                                                                                                    Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                    (Datatypes.app a0
                                                                                                      (Datatypes.app c0 (Datatypes.app h0 (Datatypes.app h4 d2)))) k1) d1)
                                                                                                    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                    (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2)
                                                                                                    LntT.Coq_bac) Datatypes.Coq_nil)) g0
                                                                                                    (let {
                                                                                                      _evar_0_ = let {
                                                                                                                  _evar_0_ = let {
                                                                                                                              _evar_0_ = let {
                                                                                                                                          _evar_0_ = WBox2Ls a d1
                                                                                                                                           (Datatypes.app
                                                                                                                                             (Datatypes.app a0 c0) h0)
                                                                                                                                           (Datatypes.app h4 d2) h2l h2r k1
                                                                                                                                           k2}
                                                                                                                                         in
                                                                                                                                         Logic.eq_rect
                                                                                                                                           (Datatypes.app
                                                                                                                                             (Datatypes.app
                                                                                                                                               (Datatypes.app a0 c0) h0)
                                                                                                                                             (Datatypes.app h4 d2)) _evar_0_
                                                                                                                                           (Datatypes.app
                                                                                                                                             (Datatypes.app
                                                                                                                                               (Datatypes.app
                                                                                                                                                 (Datatypes.app a0 c0) h0)
                                                                                                                                               h4) d2)}
                                                                                                                             in
                                                                                                                             Logic.eq_rect_r
                                                                                                                               (Datatypes.app
                                                                                                                                 (Datatypes.app
                                                                                                                                   (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                                                   h4) d2) _evar_0_
                                                                                                                               (Datatypes.app
                                                                                                                                 (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                                                 (Datatypes.app h4 d2))}
                                                                                                                 in
                                                                                                                 Logic.eq_rect_r
                                                                                                                   (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                                     (Datatypes.app h4 d2)) _evar_0_
                                                                                                                   (Datatypes.app (Datatypes.app a0 c0)
                                                                                                                     (Datatypes.app h0 (Datatypes.app h4 d2)))}
                                                                                                     in
                                                                                                     Logic.eq_rect_r
                                                                                                       (Datatypes.app (Datatypes.app a0 c0)
                                                                                                         (Datatypes.app h0 (Datatypes.app h4 d2))) _evar_0_
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app c0 (Datatypes.app h0 (Datatypes.app h4 d2)))))}
                                                                                      in
                                                                                      Logic.eq_rect (Datatypes.app h0 (Datatypes.app h4 d2)) _evar_0_
                                                                                        (Datatypes.app (Datatypes.app h0 h4) d2)))
                                                                                   (let {f = LntT.nslclext g0} in
                                                                                    let {
                                                                                     c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                        (Datatypes.app h4 d2))) k1) d1) Datatypes.Coq_nil}
                                                                                    in
                                                                                    (case DdT.dersrec_map_single f c1 of {
                                                                                      Datatypes.Coq_pair _ x0 -> x0})
                                                                                      (let {
                                                                                        x0 = \_ _ _ f0 x0 ->
                                                                                         case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                          Datatypes.Coq_pair _ x1 -> x1}}
                                                                                       in
                                                                                       let {
                                                                                        acm4 = x0 __ __ __ (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                 (Datatypes.Coq_pair
                                                                                                 (Datatypes.app (Datatypes.app a0 h0) (Datatypes.Coq_cons a
                                                                                                   (Datatypes.app h4 (Datatypes.app c0 d2)))) k1) d1) Datatypes.Coq_nil) acm3}
                                                                                       in
                                                                                       let {
                                                                                        x1 = \_ ns0 ->
                                                                                         case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                          Datatypes.Coq_pair x1 _ -> x1}}
                                                                                       in
                                                                                       let {
                                                                                        acm5 = x1 __
                                                                                                 (LntT.nslclext g0 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                   (Datatypes.Coq_pair
                                                                                                   (Datatypes.app (Datatypes.app a0 h0) (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h4 (Datatypes.app c0 d2)))) k1) d1) Datatypes.Coq_nil))
                                                                                                 acm4 g0 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h4 (Datatypes.app c0 d2))))) k1)
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h4 (Datatypes.app c0 d2))))) k1
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app c0
                                                                                                     (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2))))) d1
                                                                                                 (SwappedT.swapped_L
                                                                                                   (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h4 (Datatypes.app c0 d2))))
                                                                                                   (Datatypes.app c0
                                                                                                     (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2)))) a0
                                                                                                   (Logic.eq_rec_r (Datatypes.app (Datatypes.app h4 c0) d2)
                                                                                                     (Logic.eq_rec_r
                                                                                                       (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons a
                                                                                                         (Datatypes.app h4 d2)))
                                                                                                       (Logic.eq_rec_r
                                                                                                         (Datatypes.app (Datatypes.Coq_cons a (Datatypes.app h4 c0)) d2)
                                                                                                         (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h4) c0)
                                                                                                           (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h4) d2)
                                                                                                             (Logic.eq_rec_r
                                                                                                               (Datatypes.app
                                                                                                                 (Datatypes.app h0
                                                                                                                   (Datatypes.app (Datatypes.Coq_cons a h4) c0)) d2)
                                                                                                               (Logic.eq_rec_r
                                                                                                                 (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons a h4))
                                                                                                                   c0)
                                                                                                                 (Logic.eq_rec_r
                                                                                                                   (Datatypes.app
                                                                                                                     (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons
                                                                                                                       a h4)) d2)
                                                                                                                   (SwappedT.swapped_R
                                                                                                                     (Datatypes.app
                                                                                                                       (Datatypes.app h0 (Datatypes.Coq_cons a h4)) c0)
                                                                                                                     (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons
                                                                                                                       a h4)) d2
                                                                                                                     (let {
                                                                                                                       _evar_0_ = let {
                                                                                                                                   _evar_0_ = let {
                                                                                                                                               _evar_0_ = Gen.arg1_cong_imp
                                                                                                                                                            (Datatypes.app
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h0
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h4)) c0)
                                                                                                                                                            (Datatypes.app h0
                                                                                                                                                              (Datatypes.Coq_cons
                                                                                                                                                              a
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h4 c0)))
                                                                                                                                                            (Datatypes.app c0
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h0
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h4)))
                                                                                                                                                            (SwappedT.swapped_simpleR
                                                                                                                                                              c0
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h0
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h4))
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h0
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h4)))}
                                                                                                                                              in
                                                                                                                                              Logic.eq_rec
                                                                                                                                                (Datatypes.Coq_cons a
                                                                                                                                                (Datatypes.app h4 c0))
                                                                                                                                                _evar_0_
                                                                                                                                                (Datatypes.app
                                                                                                                                                  (Datatypes.Coq_cons a h4)
                                                                                                                                                  c0)}
                                                                                                                                  in
                                                                                                                                  Logic.eq_rec
                                                                                                                                    (Datatypes.app c0
                                                                                                                                      (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                                                                        h4))) _evar_0_
                                                                                                                                    (Datatypes.app (Datatypes.app c0 h0)
                                                                                                                                      (Datatypes.Coq_cons a h4))}
                                                                                                                      in
                                                                                                                      Logic.eq_rec
                                                                                                                        (Datatypes.app h0
                                                                                                                          (Datatypes.app (Datatypes.Coq_cons a h4) c0))
                                                                                                                        _evar_0_
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app h0 (Datatypes.Coq_cons a h4)) c0)))
                                                                                                                   (Datatypes.app (Datatypes.app c0 h0)
                                                                                                                     (Datatypes.app (Datatypes.Coq_cons a h4) d2)))
                                                                                                                 (Datatypes.app h0
                                                                                                                   (Datatypes.app (Datatypes.Coq_cons a h4) c0)))
                                                                                                               (Datatypes.app h0
                                                                                                                 (Datatypes.app (Datatypes.app (Datatypes.Coq_cons a h4) c0)
                                                                                                                   d2))) (Datatypes.Coq_cons a (Datatypes.app h4 d2)))
                                                                                                           (Datatypes.Coq_cons a (Datatypes.app h4 c0))) (Datatypes.Coq_cons
                                                                                                         a (Datatypes.app (Datatypes.app h4 c0) d2)))
                                                                                                       (Datatypes.app c0
                                                                                                         (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2)))))
                                                                                                     (Datatypes.app h4 (Datatypes.app c0 d2)))) __ __}
                                                                                       in
                                                                                       let {
                                                                                        _evar_0_ = Logic.eq_rect
                                                                                                     (Datatypes.app a0
                                                                                                       (Datatypes.app c0
                                                                                                         (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2)))))
                                                                                                     acm5
                                                                                                     (Datatypes.app (Datatypes.app a0 c0)
                                                                                                       (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2))))}
                                                                                       in
                                                                                       Logic.eq_rect
                                                                                         (Datatypes.app (Datatypes.app a0 c0)
                                                                                           (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2)))) _evar_0_
                                                                                         (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                           (Datatypes.app h4 d2)))))) h1r acm2 drs2) b) h1l drs1 acm1;
                                                                            Datatypes.Coq_inr _ ->
                                                                             let {h6 = List_lemmasT.app_eq_appT2 c0 d2 h4 h1r} in
                                                                             case h6 of {
                                                                              Specif.Coq_existT h7 h8 ->
                                                                               case h8 of {
                                                                                Datatypes.Coq_inl _ ->
                                                                                 Logic.eq_rect_r (Datatypes.app a0 h0) (\drs2 acm2 ->
                                                                                   Logic.eq_rect_r (Datatypes.app b h4) (\acm3 drs3 ->
                                                                                     Logic.eq_rect_r (Datatypes.app h4 h7)
                                                                                       (Logic.eq_rect_r (Datatypes.app h7 d2) (\_ acm4 -> DdT.Coq_derI
                                                                                         (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                           (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app (Datatypes.app a0 h4) (Datatypes.Coq_cons a
                                                                                             (Datatypes.app h7 (Datatypes.app b d2)))) k1) d1) Datatypes.Coq_nil)
                                                                                           Datatypes.Coq_nil))
                                                                                         (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app a0 (Datatypes.app (Datatypes.app h4 h7) (Datatypes.app b d2))) k1)
                                                                                           d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                           Datatypes.Coq_nil)))
                                                                                         (unsafeCoerce rs0
                                                                                           (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app (Datatypes.app a0 h4) (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h7 (Datatypes.app b d2)))) k1) d1) Datatypes.Coq_nil)
                                                                                             Datatypes.Coq_nil))
                                                                                           (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.app (Datatypes.app h4 h7) (Datatypes.app b d2)))
                                                                                             k1) d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                             Datatypes.Coq_nil)))
                                                                                           (let {
                                                                                             _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app (Datatypes.app a0 h4) (Datatypes.Coq_cons a
                                                                                                            (Datatypes.app h7 (Datatypes.app b d2)))) k1) d1)
                                                                                                          Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app a0
                                                                                                            (Datatypes.app h4 (Datatypes.app h7 (Datatypes.app b d2)))) k1)
                                                                                                          d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2)
                                                                                                          LntT.Coq_bac) Datatypes.Coq_nil)) g0
                                                                                                          (let {
                                                                                                            _evar_0_ = let {
                                                                                                                        _evar_0_ = let {
                                                                                                                                    _evar_0_ = WBox2Ls a d1
                                                                                                                                     (Datatypes.app a0 h4)
                                                                                                                                     (Datatypes.app h7 (Datatypes.app b d2))
                                                                                                                                     h2l h2r k1 k2}
                                                                                                                                   in
                                                                                                                                   Logic.eq_rect
                                                                                                                                     (Datatypes.app (Datatypes.app a0 h4)
                                                                                                                                       (Datatypes.app h7
                                                                                                                                         (Datatypes.app b d2))) _evar_0_
                                                                                                                                     (Datatypes.app
                                                                                                                                       (Datatypes.app (Datatypes.app a0 h4)
                                                                                                                                         h7) (Datatypes.app b d2))}
                                                                                                                       in
                                                                                                                       Logic.eq_rect_r
                                                                                                                         (Datatypes.app
                                                                                                                           (Datatypes.app (Datatypes.app a0 h4) h7)
                                                                                                                           (Datatypes.app b d2)) _evar_0_
                                                                                                                         (Datatypes.app (Datatypes.app a0 h4)
                                                                                                                           (Datatypes.app h7 (Datatypes.app b d2)))}
                                                                                                           in
                                                                                                           Logic.eq_rect_r
                                                                                                             (Datatypes.app (Datatypes.app a0 h4)
                                                                                                               (Datatypes.app h7 (Datatypes.app b d2))) _evar_0_
                                                                                                             (Datatypes.app a0
                                                                                                               (Datatypes.app h4 (Datatypes.app h7 (Datatypes.app b d2)))))}
                                                                                            in
                                                                                            Logic.eq_rect (Datatypes.app h4 (Datatypes.app h7 (Datatypes.app b d2))) _evar_0_
                                                                                              (Datatypes.app (Datatypes.app h4 h7) (Datatypes.app b d2))))
                                                                                         (let {f = LntT.nslclext g0} in
                                                                                          let {
                                                                                           c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app (Datatypes.app a0 h4) (Datatypes.Coq_cons a
                                                                                              (Datatypes.app h7 (Datatypes.app b d2)))) k1) d1) Datatypes.Coq_nil}
                                                                                          in
                                                                                          (case DdT.dersrec_map_single f c1 of {
                                                                                            Datatypes.Coq_pair _ x0 -> x0})
                                                                                            (let {
                                                                                              x0 = \_ _ _ f0 x0 ->
                                                                                               case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                                Datatypes.Coq_pair _ x1 -> x1}}
                                                                                             in
                                                                                             let {
                                                                                              acm5 = x0 __ __ __ (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair
                                                                                                       (Datatypes.app (Datatypes.app a0 (Datatypes.app b h4))
                                                                                                         (Datatypes.Coq_cons a (Datatypes.app h7 d2))) k1) d1)
                                                                                                       Datatypes.Coq_nil) acm4}
                                                                                             in
                                                                                             let {
                                                                                              x1 = \_ ns0 ->
                                                                                               case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                                Datatypes.Coq_pair x1 _ -> x1}}
                                                                                             in
                                                                                             let {
                                                                                              acm6 = x1 __
                                                                                                       (LntT.nslclext g0 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app (Datatypes.app a0 (Datatypes.app b h4))
                                                                                                           (Datatypes.Coq_cons a (Datatypes.app h7 d2))) k1) d1)
                                                                                                         Datatypes.Coq_nil)) acm5 g0 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app h4 (Datatypes.Coq_cons a (Datatypes.app h7 d2)))))
                                                                                                       k1)
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app h4 (Datatypes.Coq_cons a (Datatypes.app h7 d2)))))
                                                                                                       k1
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app h4 (Datatypes.Coq_cons a
                                                                                                           (Datatypes.app h7 (Datatypes.app b d2))))) d1
                                                                                                       (SwappedT.swapped_L
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app h4 (Datatypes.Coq_cons a (Datatypes.app h7 d2))))
                                                                                                         (Datatypes.app h4 (Datatypes.Coq_cons a
                                                                                                           (Datatypes.app h7 (Datatypes.app b d2)))) a0
                                                                                                         (Logic.eq_rec_r
                                                                                                           (Datatypes.app (Datatypes.app b h4) (Datatypes.Coq_cons a
                                                                                                             (Datatypes.app h7 d2)))
                                                                                                           (Logic.eq_rec_r (Datatypes.app (Datatypes.app h7 b) d2)
                                                                                                             (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h7) d2)
                                                                                                               (Logic.eq_rec_r
                                                                                                                 (Datatypes.app (Datatypes.Coq_cons a (Datatypes.app h7 b))
                                                                                                                   d2)
                                                                                                                 (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h7) b)
                                                                                                                   (Logic.eq_rec_r
                                                                                                                     (Datatypes.app
                                                                                                                       (Datatypes.app (Datatypes.app b h4)
                                                                                                                         (Datatypes.Coq_cons a h7)) d2)
                                                                                                                     (Logic.eq_rec_r
                                                                                                                       (Datatypes.app
                                                                                                                         (Datatypes.app h4
                                                                                                                           (Datatypes.app (Datatypes.Coq_cons a h7) b)) d2)
                                                                                                                       (Logic.eq_rec_r
                                                                                                                         (Datatypes.app
                                                                                                                           (Datatypes.app h4 (Datatypes.Coq_cons a h7)) b)
                                                                                                                         (SwappedT.swapped_R
                                                                                                                           (Datatypes.app (Datatypes.app b h4)
                                                                                                                             (Datatypes.Coq_cons a h7))
                                                                                                                           (Datatypes.app
                                                                                                                             (Datatypes.app h4 (Datatypes.Coq_cons a h7)) b)
                                                                                                                           d2
                                                                                                                           (let {
                                                                                                                             _evar_0_ = let {
                                                                                                                                         _evar_0_ = let {
                                                                                                                                                     _evar_0_ = Gen.arg_cong_imp
                                                                                                                                                                  (Datatypes.app
                                                                                                                                                                    (Datatypes.app
                                                                                                                                                                    h4
                                                                                                                                                                    (Datatypes.Coq_cons
                                                                                                                                                                    a h7)) b)
                                                                                                                                                                  (Datatypes.app
                                                                                                                                                                    h4
                                                                                                                                                                    (Datatypes.Coq_cons
                                                                                                                                                                    a
                                                                                                                                                                    (Datatypes.app
                                                                                                                                                                    h7 b)))
                                                                                                                                                                  (SwappedT.swapped_simpleL
                                                                                                                                                                    b
                                                                                                                                                                    (Datatypes.app
                                                                                                                                                                    h4
                                                                                                                                                                    (Datatypes.Coq_cons
                                                                                                                                                                    a h7))
                                                                                                                                                                    (Datatypes.app
                                                                                                                                                                    h4
                                                                                                                                                                    (Datatypes.Coq_cons
                                                                                                                                                                    a h7)))}
                                                                                                                                                    in
                                                                                                                                                    Logic.eq_rec
                                                                                                                                                      (Datatypes.Coq_cons a
                                                                                                                                                      (Datatypes.app h7 b))
                                                                                                                                                      _evar_0_
                                                                                                                                                      (Datatypes.app
                                                                                                                                                        (Datatypes.Coq_cons a
                                                                                                                                                        h7) b)}
                                                                                                                                        in
                                                                                                                                        Logic.eq_rec
                                                                                                                                          (Datatypes.app h4
                                                                                                                                            (Datatypes.app
                                                                                                                                              (Datatypes.Coq_cons a h7) b))
                                                                                                                                          _evar_0_
                                                                                                                                          (Datatypes.app
                                                                                                                                            (Datatypes.app h4
                                                                                                                                              (Datatypes.Coq_cons a h7)) b)}
                                                                                                                            in
                                                                                                                            Logic.eq_rec
                                                                                                                              (Datatypes.app b
                                                                                                                                (Datatypes.app h4 (Datatypes.Coq_cons a h7)))
                                                                                                                              _evar_0_
                                                                                                                              (Datatypes.app (Datatypes.app b h4)
                                                                                                                                (Datatypes.Coq_cons a h7))))
                                                                                                                         (Datatypes.app h4
                                                                                                                           (Datatypes.app (Datatypes.Coq_cons a h7) b)))
                                                                                                                       (Datatypes.app h4
                                                                                                                         (Datatypes.app
                                                                                                                           (Datatypes.app (Datatypes.Coq_cons a h7) b) d2)))
                                                                                                                     (Datatypes.app (Datatypes.app b h4)
                                                                                                                       (Datatypes.app (Datatypes.Coq_cons a h7) d2)))
                                                                                                                   (Datatypes.Coq_cons a (Datatypes.app h7 b)))
                                                                                                                 (Datatypes.Coq_cons a
                                                                                                                 (Datatypes.app (Datatypes.app h7 b) d2)))
                                                                                                               (Datatypes.Coq_cons a (Datatypes.app h7 d2)))
                                                                                                             (Datatypes.app h7 (Datatypes.app b d2)))
                                                                                                           (Datatypes.app b
                                                                                                             (Datatypes.app h4 (Datatypes.Coq_cons a (Datatypes.app h7 d2))))))
                                                                                                       __ __}
                                                                                             in
                                                                                             Logic.eq_rect
                                                                                               (Datatypes.app a0
                                                                                                 (Datatypes.app h4 (Datatypes.Coq_cons a
                                                                                                   (Datatypes.app h7 (Datatypes.app b d2))))) acm6
                                                                                               (Datatypes.app (Datatypes.app a0 h4) (Datatypes.Coq_cons a
                                                                                                 (Datatypes.app h7 (Datatypes.app b d2))))))) h1r drs3 acm3) c0) h0 acm2 drs2)
                                                                                   h1l drs1 acm1;
                                                                                Datatypes.Coq_inr _ ->
                                                                                 Logic.eq_rect_r (Datatypes.app a0 h0) (\drs2 acm2 ->
                                                                                   Logic.eq_rect_r (Datatypes.app b h4) (\acm3 drs3 ->
                                                                                     Logic.eq_rect_r (Datatypes.app c0 h7) (\_ acm4 ->
                                                                                       Logic.eq_rect_r (Datatypes.app h7 h1r) (DdT.Coq_derI
                                                                                         (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                           (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h7)
                                                                                             (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                         (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h7 h1r)))) k1)
                                                                                           d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                           Datatypes.Coq_nil)))
                                                                                         (unsafeCoerce rs0
                                                                                           (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h7)
                                                                                               (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                           (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h7 h1r))))
                                                                                             k1) d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                             Datatypes.Coq_nil)))
                                                                                           (LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                             (Datatypes.Coq_pair
                                                                                             (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h7)
                                                                                               (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil)
                                                                                             (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h7 h1r))))
                                                                                             k1) d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                             Datatypes.Coq_nil)) g0
                                                                                             (let {
                                                                                               _evar_0_ = let {
                                                                                                           _evar_0_ = let {
                                                                                                                       _evar_0_ = WBox2Ls a d1
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app (Datatypes.app a0 c0) b) h7) h1r h2l
                                                                                                                        h2r k1 k2}
                                                                                                                      in
                                                                                                                      Logic.eq_rect_r
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app
                                                                                                                            (Datatypes.app (Datatypes.app a0 c0) b) h7) h1r)
                                                                                                                        _evar_0_
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                                          (Datatypes.app h7 h1r))}
                                                                                                          in
                                                                                                          Logic.eq_rect_r
                                                                                                            (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                              (Datatypes.app h7 h1r)) _evar_0_
                                                                                                            (Datatypes.app (Datatypes.app a0 c0)
                                                                                                              (Datatypes.app b (Datatypes.app h7 h1r)))}
                                                                                              in
                                                                                              Logic.eq_rect_r
                                                                                                (Datatypes.app (Datatypes.app a0 c0)
                                                                                                  (Datatypes.app b (Datatypes.app h7 h1r))) _evar_0_
                                                                                                (Datatypes.app a0
                                                                                                  (Datatypes.app c0 (Datatypes.app b (Datatypes.app h7 h1r)))))))
                                                                                         (let {f = LntT.nslclext g0} in
                                                                                          let {
                                                                                           c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h7)
                                                                                              (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil}
                                                                                          in
                                                                                          (case DdT.dersrec_map_single f c1 of {
                                                                                            Datatypes.Coq_pair _ x0 -> x0})
                                                                                            (let {
                                                                                              x0 = \_ _ _ f0 x0 ->
                                                                                               case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                                Datatypes.Coq_pair _ x1 -> x1}}
                                                                                             in
                                                                                             let {
                                                                                              acm5 = x0 __ __ __ (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair
                                                                                                       (Datatypes.app
                                                                                                         (Datatypes.app a0 (Datatypes.app b (Datatypes.app c0 h7)))
                                                                                                         (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) acm4}
                                                                                             in
                                                                                             let {
                                                                                              x1 = \_ ns0 ->
                                                                                               case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                                Datatypes.Coq_pair x1 _ -> x1}}
                                                                                             in
                                                                                             let {
                                                                                              acm6 = x1 __
                                                                                                       (LntT.nslclext g0 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app
                                                                                                           (Datatypes.app a0 (Datatypes.app b (Datatypes.app c0 h7)))
                                                                                                           (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)) acm5 g0
                                                                                                       Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app c0 (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))))
                                                                                                       k1)
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app c0 (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))))
                                                                                                       k1
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app c0
                                                                                                           (Datatypes.app b (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))))
                                                                                                       d1
                                                                                                       (SwappedT.swapped_L
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app c0 (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))
                                                                                                         (Datatypes.app c0
                                                                                                           (Datatypes.app b (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))
                                                                                                         a0
                                                                                                         (Logic.eq_rec_r
                                                                                                           (Datatypes.app (Datatypes.app b c0)
                                                                                                             (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))
                                                                                                           (Logic.eq_rec_r
                                                                                                             (Datatypes.app (Datatypes.app (Datatypes.app b c0) h7)
                                                                                                               (Datatypes.Coq_cons a h1r))
                                                                                                             (Logic.eq_rec_r
                                                                                                               (Datatypes.app (Datatypes.app c0 b)
                                                                                                                 (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))
                                                                                                               (Logic.eq_rec_r
                                                                                                                 (Datatypes.app (Datatypes.app (Datatypes.app c0 b) h7)
                                                                                                                   (Datatypes.Coq_cons a h1r))
                                                                                                                 (SwappedT.swapped_R (Datatypes.app (Datatypes.app b c0) h7)
                                                                                                                   (Datatypes.app (Datatypes.app c0 b) h7)
                                                                                                                   (Datatypes.Coq_cons a h1r)
                                                                                                                   (SwappedT.swapped_R (Datatypes.app b c0)
                                                                                                                     (Datatypes.app c0 b) h7
                                                                                                                     (Gen.arg_cong_imp (Datatypes.app c0 b)
                                                                                                                       (Datatypes.app c0 b)
                                                                                                                       (SwappedT.swapped_simpleL b c0 c0))))
                                                                                                                 (Datatypes.app (Datatypes.app c0 b)
                                                                                                                   (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))
                                                                                                               (Datatypes.app c0
                                                                                                                 (Datatypes.app b
                                                                                                                   (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))))
                                                                                                             (Datatypes.app (Datatypes.app b c0)
                                                                                                               (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))
                                                                                                           (Datatypes.app b
                                                                                                             (Datatypes.app c0 (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))))
                                                                                                       __ __}
                                                                                             in
                                                                                             let {
                                                                                              _evar_0_ = let {
                                                                                                          _evar_0_ = Logic.eq_rect
                                                                                                                       (Datatypes.app a0
                                                                                                                         (Datatypes.app c0
                                                                                                                           (Datatypes.app b
                                                                                                                             (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))))
                                                                                                                       acm6
                                                                                                                       (Datatypes.app (Datatypes.app a0 c0)
                                                                                                                         (Datatypes.app b
                                                                                                                           (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))}
                                                                                                         in
                                                                                                         Logic.eq_rect
                                                                                                           (Datatypes.app (Datatypes.app a0 c0)
                                                                                                             (Datatypes.app b (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))
                                                                                                           _evar_0_
                                                                                                           (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                             (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))}
                                                                                             in
                                                                                             Logic.eq_rect
                                                                                               (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                 (Datatypes.app h7 (Datatypes.Coq_cons a h1r))) _evar_0_
                                                                                               (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h7)
                                                                                                 (Datatypes.Coq_cons a h1r))))) d2) h4 drs3 acm3) h0 acm2 drs2) h1l drs1 acm1}}}};
                                                                        Datatypes.Coq_inr _ ->
                                                                         Logic.eq_rect_r (Datatypes.app h1l h0)
                                                                           (Logic.eq_rect_r (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))) (\_ acm2 ->
                                                                             DdT.Coq_derI
                                                                             (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                               (Datatypes.Coq_pair
                                                                               (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                 (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) k1) d1) Datatypes.Coq_nil)
                                                                               Datatypes.Coq_nil))
                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                               (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2))) k1) d1)
                                                                               (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                               (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                               Datatypes.Coq_nil)))
                                                                             (unsafeCoerce rs0
                                                                               (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair
                                                                                 (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                   (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) k1) d1) Datatypes.Coq_nil)
                                                                                 Datatypes.Coq_nil))
                                                                               (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2))) k1) d1)
                                                                                 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                 Datatypes.Coq_nil)))
                                                                               (let {
                                                                                 _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                              (Datatypes.Coq_pair
                                                                                              (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                                (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) k1) d1)
                                                                                              Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                              (Datatypes.Coq_pair
                                                                                              (Datatypes.app h1l (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))
                                                                                              k1) d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                              (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                              Datatypes.Coq_nil)) g0
                                                                                              (let {
                                                                                                _evar_0_ = let {
                                                                                                            _evar_0_ = WBox2Ls a d1 h1l
                                                                                                             (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))) h2l
                                                                                                             h2r k1 k2}
                                                                                                           in
                                                                                                           Logic.eq_rect
                                                                                                             (Datatypes.app h1l
                                                                                                               (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))
                                                                                                             _evar_0_
                                                                                                             (Datatypes.app (Datatypes.app h1l h0)
                                                                                                               (Datatypes.app c0 (Datatypes.app b d2)))}
                                                                                               in
                                                                                               Logic.eq_rect_r
                                                                                                 (Datatypes.app (Datatypes.app h1l h0)
                                                                                                   (Datatypes.app c0 (Datatypes.app b d2))) _evar_0_
                                                                                                 (Datatypes.app h1l
                                                                                                   (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))))}
                                                                                in
                                                                                Logic.eq_rect (Datatypes.app h1l (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))
                                                                                  _evar_0_ (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2)))))
                                                                             (let {f = LntT.nslclext g0} in
                                                                              let {
                                                                               c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                  (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) k1) d1) Datatypes.Coq_nil}
                                                                              in
                                                                              (case DdT.dersrec_map_single f c1 of {
                                                                                Datatypes.Coq_pair _ x0 -> x0})
                                                                                (let {
                                                                                  x0 = \_ _ _ f0 x0 ->
                                                                                   case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                    Datatypes.Coq_pair _ x1 -> x1}}
                                                                                 in
                                                                                 let {
                                                                                  acm3 = x0 __ __ __ (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                           (Datatypes.Coq_pair
                                                                                           (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                             (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) k1) d1)
                                                                                           Datatypes.Coq_nil) acm2}
                                                                                 in
                                                                                 let {
                                                                                  ns0 = LntT.nslclext g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                            (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) k1) d1)
                                                                                          Datatypes.Coq_nil)}
                                                                                 in
                                                                                 (case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                   Datatypes.Coq_pair x1 _ -> x1}) acm3 g0 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) k1)
                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) k1
                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) d1
                                                                                   (SwappedT.swapped_L (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2)))) (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))) h1l
                                                                                     (SwappedT.swapped_cons a (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2)))
                                                                                       (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))
                                                                                       (SwappedT.swapped_L (Datatypes.app b (Datatypes.app c0 d2))
                                                                                         (Datatypes.app c0 (Datatypes.app b d2)) h0
                                                                                         (Logic.eq_rec_r (Datatypes.app (Datatypes.app b c0) d2)
                                                                                           (Logic.eq_rec_r (Datatypes.app (Datatypes.app c0 b) d2)
                                                                                             (SwappedT.swapped_R (Datatypes.app b c0) (Datatypes.app c0 b) d2
                                                                                               (Gen.arg_cong_imp (Datatypes.app c0 b) (Datatypes.app c0 b)
                                                                                                 (SwappedT.swapped_simpleL b c0 c0)))
                                                                                             (Datatypes.app c0 (Datatypes.app b d2)))
                                                                                           (Datatypes.app b (Datatypes.app c0 d2)))))) __ __))) h1r drs1 acm1) a0}})
                                                                    _UU0393_') y) x __ __ __)}) __ __}
                                               in
                                               Logic.eq_rect_r g0 _evar_0_ (Datatypes.app g0 Datatypes.Coq_nil)) k0) d0) _UU0394_0) _UU0393_ swap) pp0;
                                   Datatypes.Coq_inr h2 ->
                                    case h2 of {
                                     Specif.Coq_existT h3 _ ->
                                      let {
                                       h4 = List_lemmasT.cons_eq_appT2 Datatypes.Coq_nil h3 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0)
                                              d0) k0) (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)}
                                      in
                                      case h4 of {
                                       Datatypes.Coq_inl _ ->
                                        Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1) h3)
                                          (Logic.eq_rect_r Datatypes.Coq_nil
                                            (Logic.eq_rect_r (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) (\swap0 ->
                                              Logic.eq_rect_r k2
                                                (Logic.eq_rect_r LntT.Coq_bac
                                                  (Logic.eq_rect_r Datatypes.Coq_nil
                                                    ((case swap0 of {
                                                       SwappedT.Coq_swapped_I x y a0 b c0 d2 -> (\_ _ ->
                                                        Logic.eq_rect_r (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) (\_ ->
                                                          Logic.eq_rect_r _UU0393_' (\_ _ ->
                                                            Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b d2)))
                                                              (let {
                                                                h = List_lemmasT.app_eq_appT2 h2l (Datatypes.Coq_cons (LntT.WBox a) h2r) a0
                                                                      (Datatypes.app b (Datatypes.app c0 d2))}
                                                               in
                                                               case h of {
                                                                Specif.Coq_existT h0 h5 ->
                                                                 case h5 of {
                                                                  Datatypes.Coq_inl _ ->
                                                                   let {h6 = List_lemmasT.app_eq_appT2 b (Datatypes.app c0 d2) h0 (Datatypes.Coq_cons (LntT.WBox a) h2r)} in
                                                                   case h6 of {
                                                                    Specif.Coq_existT h7 h8 ->
                                                                     case h8 of {
                                                                      Datatypes.Coq_inl _ ->
                                                                       let {h9 = List_lemmasT.cons_eq_appT2 h2r h7 (Datatypes.app c0 d2) (LntT.WBox a)} in
                                                                       case h9 of {
                                                                        Datatypes.Coq_inl _ ->
                                                                         let {h10 = List_lemmasT.app_eq_consT2 h2r c0 d2 (LntT.WBox a)} in
                                                                         case h10 of {
                                                                          Datatypes.Coq_inl _ ->
                                                                           Logic.eq_rect_r (Datatypes.app h0 h7)
                                                                             (Logic.eq_rect_r Datatypes.Coq_nil
                                                                               (Logic.eq_rect_r Datatypes.Coq_nil
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.WBox a) h2r)
                                                                                   (let {
                                                                                     _evar_0_ = DdT.Coq_derI
                                                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                        Datatypes.Coq_nil))
                                                                                      (Datatypes.app
                                                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app a0 (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a) h2r))) k2)
                                                                                        LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                      (unsafeCoerce rs0
                                                                                        (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                          Datatypes.Coq_nil))
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app a0 (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a) h2r))) k2)
                                                                                          LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                        (let {
                                                                                          _evar_0_ = let {
                                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app a0
                                                                                                                     (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                       h2r))) k2) LntT.Coq_bac) Datatypes.Coq_nil)) g0
                                                                                                                   (let {
                                                                                                                     _evar_0_ = WBox2Ls a d1 h1l h1r (Datatypes.app a0 h0)
                                                                                                                      h2r k1 k2}
                                                                                                                    in
                                                                                                                    Logic.eq_rect_r
                                                                                                                      (Datatypes.app (Datatypes.app a0 h0)
                                                                                                                        (Datatypes.Coq_cons (LntT.WBox a) h2r)) _evar_0_
                                                                                                                      (Datatypes.app a0
                                                                                                                        (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                          h2r))))}
                                                                                                     in
                                                                                                     Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                       (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0
                                                                                                           (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a) h2r))) k2)
                                                                                                         LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                         Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0
                                                                                                           (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a) h2r))) k2)
                                                                                                         LntT.Coq_bac) Datatypes.Coq_nil))}
                                                                                         in
                                                                                         Logic.eq_rect
                                                                                           (Datatypes.app g0
                                                                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app a0 (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a) h2r)))
                                                                                               k2) LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                           (Datatypes.app
                                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a) h2r))) k2)
                                                                                             LntT.Coq_bac) Datatypes.Coq_nil)))) drs1}
                                                                                    in
                                                                                    Logic.eq_rect_r h0 _evar_0_ (Datatypes.app h0 Datatypes.Coq_nil)) d2) c0) h7) b;
                                                                          Datatypes.Coq_inr h11 ->
                                                                           case h11 of {
                                                                            Specif.Coq_existT h12 _ ->
                                                                             Logic.eq_rect_r (Datatypes.app h0 h7)
                                                                               (Logic.eq_rect_r Datatypes.Coq_nil
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.WBox a) h12)
                                                                                   (let {
                                                                                     _evar_0_ = DdT.Coq_derI
                                                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                        Datatypes.Coq_nil))
                                                                                      (Datatypes.app
                                                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app a0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                          (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                      (unsafeCoerce rs0
                                                                                        (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                          Datatypes.Coq_nil))
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app a0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                            (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                        (let {
                                                                                          _evar_0_ = let {
                                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app a0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                     (Datatypes.app h12 (Datatypes.app h0 d2)))) k2)
                                                                                                                   LntT.Coq_bac) Datatypes.Coq_nil)) g0 (WBox2Ls a d1 h1l h1r
                                                                                                                   a0 (Datatypes.app h12 (Datatypes.app h0 d2)) k1 k2)}
                                                                                                     in
                                                                                                     Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                       (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                           (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_bac)
                                                                                                         Datatypes.Coq_nil))) _evar_0_
                                                                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                         Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                           (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_bac)
                                                                                                         Datatypes.Coq_nil))}
                                                                                         in
                                                                                         Logic.eq_rect
                                                                                           (Datatypes.app g0
                                                                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app a0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                 (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_bac)
                                                                                               Datatypes.Coq_nil))) _evar_0_
                                                                                           (Datatypes.app
                                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                               (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_bac)
                                                                                             Datatypes.Coq_nil)))) drs1}
                                                                                    in
                                                                                    Logic.eq_rect_r h0 _evar_0_ (Datatypes.app h0 Datatypes.Coq_nil)) c0) h7) b}};
                                                                        Datatypes.Coq_inr h10 ->
                                                                         case h10 of {
                                                                          Specif.Coq_existT h11 _ ->
                                                                           Logic.eq_rect_r (Datatypes.app h0 h7)
                                                                             (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.WBox a) h11) (DdT.Coq_derI
                                                                               (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                 Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                               (Datatypes.app
                                                                                 (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                   (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                 (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app a0
                                                                                   (Datatypes.app c0
                                                                                     (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a) h11)) d2))) k2)
                                                                                 LntT.Coq_bac) Datatypes.Coq_nil))
                                                                               (unsafeCoerce rs0
                                                                                 (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                   (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                 (Datatypes.app
                                                                                   (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                   (Datatypes.app a0
                                                                                     (Datatypes.app c0
                                                                                       (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a) h11)) d2))) k2)
                                                                                   LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                 (let {
                                                                                   _evar_0_ = let {
                                                                                               _evar_0_ = let {
                                                                                                           _evar_0_ = let {
                                                                                                                       _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons
                                                                                                                                    (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                                    (Datatypes.Coq_pair
                                                                                                                                    (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                                                                      h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                                                                    Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                                    (Datatypes.app h1l h1r) k1) d1)
                                                                                                                                    (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                                    (Datatypes.Coq_pair
                                                                                                                                    (Datatypes.app a0
                                                                                                                                      (Datatypes.app c0
                                                                                                                                        (Datatypes.app h0 (Datatypes.Coq_cons
                                                                                                                                          (LntT.WBox a)
                                                                                                                                          (Datatypes.app h11 d2))))) k2)
                                                                                                                                    LntT.Coq_bac) Datatypes.Coq_nil)) g0
                                                                                                                                    (let {
                                                                                                                                      _evar_0_ = let {
                                                                                                                                                  _evar_0_ = WBox2Ls a d1 h1l
                                                                                                                                                   h1r
                                                                                                                                                   (Datatypes.app a0
                                                                                                                                                     (Datatypes.app c0 h0))
                                                                                                                                                   (Datatypes.app h11 d2) k1
                                                                                                                                                   k2}
                                                                                                                                                 in
                                                                                                                                                 Logic.eq_rect_r
                                                                                                                                                   (Datatypes.app
                                                                                                                                                     (Datatypes.app a0
                                                                                                                                                       (Datatypes.app c0 h0))
                                                                                                                                                     (Datatypes.Coq_cons
                                                                                                                                                     (LntT.WBox a)
                                                                                                                                                     (Datatypes.app h11 d2)))
                                                                                                                                                   _evar_0_
                                                                                                                                                   (Datatypes.app a0
                                                                                                                                                     (Datatypes.app
                                                                                                                                                       (Datatypes.app c0 h0)
                                                                                                                                                       (Datatypes.Coq_cons
                                                                                                                                                       (LntT.WBox a)
                                                                                                                                                       (Datatypes.app h11 d2))))}
                                                                                                                                     in
                                                                                                                                     Logic.eq_rect_r
                                                                                                                                       (Datatypes.app (Datatypes.app c0 h0)
                                                                                                                                         (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                                         (Datatypes.app h11 d2))) _evar_0_
                                                                                                                                       (Datatypes.app c0
                                                                                                                                         (Datatypes.app h0
                                                                                                                                           (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                                           (Datatypes.app h11 d2)))))}
                                                                                                                      in
                                                                                                                      Logic.eq_rect (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                        (Datatypes.app h11 d2)) _evar_0_
                                                                                                                        (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a) h11)
                                                                                                                          d2)}
                                                                                                          in
                                                                                                          Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                            (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                            (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                              (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                              (Datatypes.app a0
                                                                                                                (Datatypes.app c0
                                                                                                                  (Datatypes.app h0
                                                                                                                    (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a) h11) d2))))
                                                                                                              k2) LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                                            (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                              (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                              Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                              (Datatypes.Coq_pair
                                                                                                              (Datatypes.app a0
                                                                                                                (Datatypes.app c0
                                                                                                                  (Datatypes.app h0
                                                                                                                    (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a) h11) d2))))
                                                                                                              k2) LntT.Coq_bac) Datatypes.Coq_nil))}
                                                                                              in
                                                                                              Logic.eq_rect
                                                                                                (Datatypes.app h0 (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a) h11) d2))
                                                                                                _evar_0_
                                                                                                (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a) h11)) d2)}
                                                                                  in
                                                                                  Logic.eq_rect
                                                                                    (Datatypes.app g0
                                                                                      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app a0
                                                                                          (Datatypes.app c0
                                                                                            (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a) h11)) d2)))
                                                                                        k2) LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                    (Datatypes.app
                                                                                      (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app a0
                                                                                        (Datatypes.app c0
                                                                                          (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons (LntT.WBox a) h11)) d2))) k2)
                                                                                      LntT.Coq_bac) Datatypes.Coq_nil)))) drs1) h7) b}};
                                                                      Datatypes.Coq_inr _ ->
                                                                       let {h9 = List_lemmasT.app_eq_appT2 c0 d2 h7 (Datatypes.Coq_cons (LntT.WBox a) h2r)} in
                                                                       case h9 of {
                                                                        Specif.Coq_existT h10 h11 ->
                                                                         case h11 of {
                                                                          Datatypes.Coq_inl _ ->
                                                                           let {h12 = List_lemmasT.cons_eq_appT2 h2r h10 d2 (LntT.WBox a)} in
                                                                           case h12 of {
                                                                            Datatypes.Coq_inl _ ->
                                                                             Logic.eq_rect_r (Datatypes.app h7 h10)
                                                                               (Logic.eq_rect_r Datatypes.Coq_nil
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.WBox a) h2r)
                                                                                   (let {
                                                                                     _evar_0_ = DdT.Coq_derI
                                                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                        Datatypes.Coq_nil))
                                                                                      (Datatypes.app
                                                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app a0
                                                                                          (Datatypes.app h7 (Datatypes.app b (Datatypes.Coq_cons (LntT.WBox a) h2r)))) k2)
                                                                                        LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                      (unsafeCoerce rs0
                                                                                        (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                          Datatypes.Coq_nil))
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app a0
                                                                                            (Datatypes.app h7 (Datatypes.app b (Datatypes.Coq_cons (LntT.WBox a) h2r)))) k2)
                                                                                          LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                        (let {
                                                                                          _evar_0_ = let {
                                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app a0
                                                                                                                     (Datatypes.app h7
                                                                                                                       (Datatypes.app b (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                         h2r)))) k2) LntT.Coq_bac) Datatypes.Coq_nil)) g0
                                                                                                                   (let {
                                                                                                                     _evar_0_ = let {
                                                                                                                                 _evar_0_ = WBox2Ls a d1 h1l h1r
                                                                                                                                  (Datatypes.app a0 (Datatypes.app h7 b)) h2r
                                                                                                                                  k1 k2}
                                                                                                                                in
                                                                                                                                Logic.eq_rect_r
                                                                                                                                  (Datatypes.app
                                                                                                                                    (Datatypes.app a0 (Datatypes.app h7 b))
                                                                                                                                    (Datatypes.Coq_cons (LntT.WBox a) h2r))
                                                                                                                                  _evar_0_
                                                                                                                                  (Datatypes.app a0
                                                                                                                                    (Datatypes.app (Datatypes.app h7 b)
                                                                                                                                      (Datatypes.Coq_cons (LntT.WBox a) h2r)))}
                                                                                                                    in
                                                                                                                    Logic.eq_rect_r
                                                                                                                      (Datatypes.app (Datatypes.app h7 b) (Datatypes.Coq_cons
                                                                                                                        (LntT.WBox a) h2r)) _evar_0_
                                                                                                                      (Datatypes.app h7
                                                                                                                        (Datatypes.app b (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                          h2r))))}
                                                                                                     in
                                                                                                     Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                       (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0
                                                                                                           (Datatypes.app h7
                                                                                                             (Datatypes.app b (Datatypes.Coq_cons (LntT.WBox a) h2r)))) k2)
                                                                                                         LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                         Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0
                                                                                                           (Datatypes.app h7
                                                                                                             (Datatypes.app b (Datatypes.Coq_cons (LntT.WBox a) h2r)))) k2)
                                                                                                         LntT.Coq_bac) Datatypes.Coq_nil))}
                                                                                         in
                                                                                         Logic.eq_rect
                                                                                           (Datatypes.app g0
                                                                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app a0
                                                                                                 (Datatypes.app h7 (Datatypes.app b (Datatypes.Coq_cons (LntT.WBox a) h2r))))
                                                                                               k2) LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                           (Datatypes.app
                                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0
                                                                                               (Datatypes.app h7 (Datatypes.app b (Datatypes.Coq_cons (LntT.WBox a) h2r))))
                                                                                             k2) LntT.Coq_bac) Datatypes.Coq_nil)))) drs1}
                                                                                    in
                                                                                    Logic.eq_rect_r h7 _evar_0_ (Datatypes.app h7 Datatypes.Coq_nil)) d2) h10) c0;
                                                                            Datatypes.Coq_inr h13 ->
                                                                             case h13 of {
                                                                              Specif.Coq_existT h14 _ ->
                                                                               Logic.eq_rect_r (Datatypes.app h7 h10)
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.WBox a) h14) (DdT.Coq_derI
                                                                                   (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                     (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                     Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                   (Datatypes.app
                                                                                     (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                       (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app a0
                                                                                       (Datatypes.app (Datatypes.app h7 (Datatypes.Coq_cons (LntT.WBox a) h14))
                                                                                         (Datatypes.app b d2))) k2) LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                   (unsafeCoerce rs0
                                                                                     (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                       Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                     (Datatypes.app
                                                                                       (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                         (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                       (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                       (Datatypes.app a0
                                                                                         (Datatypes.app (Datatypes.app h7 (Datatypes.Coq_cons (LntT.WBox a) h14))
                                                                                           (Datatypes.app b d2))) k2) LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                     (let {
                                                                                       _evar_0_ = let {
                                                                                                   _evar_0_ = let {
                                                                                                               _evar_0_ = let {
                                                                                                                           _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons
                                                                                                                                        (Datatypes.Coq_cons
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.app h1l
                                                                                                                                          (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                                        Datatypes.Coq_nil) Datatypes.Coq_nil)
                                                                                                                                        (Datatypes.Coq_cons
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.app h1l h1r) k1) d1)
                                                                                                                                        (Datatypes.Coq_cons
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.app a0
                                                                                                                                          (Datatypes.app h7
                                                                                                                                            (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                                            (Datatypes.app h14
                                                                                                                                              (Datatypes.app b d2))))) k2)
                                                                                                                                        LntT.Coq_bac) Datatypes.Coq_nil)) g0
                                                                                                                                        (let {
                                                                                                                                          _evar_0_ = WBox2Ls a d1 h1l h1r
                                                                                                                                           (Datatypes.app a0 h7)
                                                                                                                                           (Datatypes.app h14
                                                                                                                                             (Datatypes.app b d2)) k1 k2}
                                                                                                                                         in
                                                                                                                                         Logic.eq_rect_r
                                                                                                                                           (Datatypes.app
                                                                                                                                             (Datatypes.app a0 h7)
                                                                                                                                             (Datatypes.Coq_cons (LntT.WBox
                                                                                                                                             a)
                                                                                                                                             (Datatypes.app h14
                                                                                                                                               (Datatypes.app b d2))))
                                                                                                                                           _evar_0_
                                                                                                                                           (Datatypes.app a0
                                                                                                                                             (Datatypes.app h7
                                                                                                                                               (Datatypes.Coq_cons (LntT.WBox
                                                                                                                                               a)
                                                                                                                                               (Datatypes.app h14
                                                                                                                                                 (Datatypes.app b d2))))))}
                                                                                                                          in
                                                                                                                          Logic.eq_rect (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                            (Datatypes.app h14 (Datatypes.app b d2)))
                                                                                                                            _evar_0_
                                                                                                                            (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                              h14) (Datatypes.app b d2))}
                                                                                                              in
                                                                                                              Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                                (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                                  (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                  (Datatypes.app a0
                                                                                                                    (Datatypes.app h7
                                                                                                                      (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a) h14)
                                                                                                                        (Datatypes.app b d2)))) k2) LntT.Coq_bac)
                                                                                                                  Datatypes.Coq_nil))) _evar_0_
                                                                                                                (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                  (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                                  Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                  (Datatypes.Coq_pair
                                                                                                                  (Datatypes.app a0
                                                                                                                    (Datatypes.app h7
                                                                                                                      (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a) h14)
                                                                                                                        (Datatypes.app b d2)))) k2) LntT.Coq_bac)
                                                                                                                  Datatypes.Coq_nil))}
                                                                                                  in
                                                                                                  Logic.eq_rect
                                                                                                    (Datatypes.app h7
                                                                                                      (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a) h14)
                                                                                                        (Datatypes.app b d2))) _evar_0_
                                                                                                    (Datatypes.app (Datatypes.app h7 (Datatypes.Coq_cons (LntT.WBox a) h14))
                                                                                                      (Datatypes.app b d2))}
                                                                                      in
                                                                                      Logic.eq_rect
                                                                                        (Datatypes.app g0
                                                                                          (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                            (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app a0
                                                                                              (Datatypes.app (Datatypes.app h7 (Datatypes.Coq_cons (LntT.WBox a) h14))
                                                                                                (Datatypes.app b d2))) k2) LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app a0
                                                                                            (Datatypes.app (Datatypes.app h7 (Datatypes.Coq_cons (LntT.WBox a) h14))
                                                                                              (Datatypes.app b d2))) k2) LntT.Coq_bac) Datatypes.Coq_nil)))) drs1) h10) c0}};
                                                                          Datatypes.Coq_inr _ ->
                                                                           Logic.eq_rect_r (Datatypes.app h10 (Datatypes.Coq_cons (LntT.WBox a) h2r)) (DdT.Coq_derI
                                                                             (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                               (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                               Datatypes.Coq_nil))
                                                                             (Datatypes.app
                                                                               (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                               (Datatypes.Coq_pair
                                                                               (Datatypes.app a0
                                                                                 (Datatypes.app c0
                                                                                   (Datatypes.app b (Datatypes.app h10 (Datatypes.Coq_cons (LntT.WBox a) h2r))))) k2)
                                                                               LntT.Coq_bac) Datatypes.Coq_nil))
                                                                             (unsafeCoerce rs0
                                                                               (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                 Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                               (Datatypes.app
                                                                                 (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                   (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                 (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app a0
                                                                                   (Datatypes.app c0
                                                                                     (Datatypes.app b (Datatypes.app h10 (Datatypes.Coq_cons (LntT.WBox a) h2r))))) k2)
                                                                                 LntT.Coq_bac) Datatypes.Coq_nil))
                                                                               (let {
                                                                                 _evar_0_ = let {
                                                                                             _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                          Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1)
                                                                                                          d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app a0
                                                                                                            (Datatypes.app c0
                                                                                                              (Datatypes.app b
                                                                                                                (Datatypes.app h10 (Datatypes.Coq_cons (LntT.WBox a) h2r)))))
                                                                                                          k2) LntT.Coq_bac) Datatypes.Coq_nil)) g0
                                                                                                          (let {
                                                                                                            _evar_0_ = let {
                                                                                                                        _evar_0_ = let {
                                                                                                                                    _evar_0_ = WBox2Ls a d1 h1l h1r
                                                                                                                                     (Datatypes.app a0
                                                                                                                                       (Datatypes.app c0
                                                                                                                                         (Datatypes.app b h10))) h2r k1 k2}
                                                                                                                                   in
                                                                                                                                   Logic.eq_rect_r
                                                                                                                                     (Datatypes.app
                                                                                                                                       (Datatypes.app a0
                                                                                                                                         (Datatypes.app c0
                                                                                                                                           (Datatypes.app b h10)))
                                                                                                                                       (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                                       h2r)) _evar_0_
                                                                                                                                     (Datatypes.app a0
                                                                                                                                       (Datatypes.app
                                                                                                                                         (Datatypes.app c0
                                                                                                                                           (Datatypes.app b h10))
                                                                                                                                         (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                                         h2r)))}
                                                                                                                       in
                                                                                                                       Logic.eq_rect_r
                                                                                                                         (Datatypes.app
                                                                                                                           (Datatypes.app c0 (Datatypes.app b h10))
                                                                                                                           (Datatypes.Coq_cons (LntT.WBox a) h2r)) _evar_0_
                                                                                                                         (Datatypes.app c0
                                                                                                                           (Datatypes.app (Datatypes.app b h10)
                                                                                                                             (Datatypes.Coq_cons (LntT.WBox a) h2r)))}
                                                                                                           in
                                                                                                           Logic.eq_rect_r
                                                                                                             (Datatypes.app (Datatypes.app b h10) (Datatypes.Coq_cons
                                                                                                               (LntT.WBox a) h2r)) _evar_0_
                                                                                                             (Datatypes.app b
                                                                                                               (Datatypes.app h10 (Datatypes.Coq_cons (LntT.WBox a) h2r))))}
                                                                                            in
                                                                                            Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                              (Datatypes.app h1l h1r) k1) d1)
                                                                                              (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                (Datatypes.Coq_pair
                                                                                                (Datatypes.app a0
                                                                                                  (Datatypes.app c0
                                                                                                    (Datatypes.app b
                                                                                                      (Datatypes.app h10 (Datatypes.Coq_cons (LntT.WBox a) h2r))))) k2)
                                                                                                LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                              (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                (Datatypes.app a0
                                                                                                  (Datatypes.app c0
                                                                                                    (Datatypes.app b
                                                                                                      (Datatypes.app h10 (Datatypes.Coq_cons (LntT.WBox a) h2r))))) k2)
                                                                                                LntT.Coq_bac) Datatypes.Coq_nil))}
                                                                                in
                                                                                Logic.eq_rect
                                                                                  (Datatypes.app g0
                                                                                    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app a0
                                                                                        (Datatypes.app c0
                                                                                          (Datatypes.app b (Datatypes.app h10 (Datatypes.Coq_cons (LntT.WBox a) h2r))))) k2)
                                                                                      LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                  (Datatypes.app
                                                                                    (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app a0
                                                                                      (Datatypes.app c0
                                                                                        (Datatypes.app b (Datatypes.app h10 (Datatypes.Coq_cons (LntT.WBox a) h2r))))) k2)
                                                                                    LntT.Coq_bac) Datatypes.Coq_nil)))) drs1) d2}}}};
                                                                  Datatypes.Coq_inr _ ->
                                                                   let {h6 = List_lemmasT.cons_eq_appT2 h2r h0 (Datatypes.app b (Datatypes.app c0 d2)) (LntT.WBox a)} in
                                                                   case h6 of {
                                                                    Datatypes.Coq_inl _ ->
                                                                     let {h7 = List_lemmasT.app_eq_consT2 h2r b (Datatypes.app c0 d2) (LntT.WBox a)} in
                                                                     case h7 of {
                                                                      Datatypes.Coq_inl _ ->
                                                                       let {h8 = List_lemmasT.app_eq_consT2 h2r c0 d2 (LntT.WBox a)} in
                                                                       case h8 of {
                                                                        Datatypes.Coq_inl _ ->
                                                                         Logic.eq_rect_r (Datatypes.app h2l h0)
                                                                           (Logic.eq_rect_r Datatypes.Coq_nil
                                                                             (Logic.eq_rect_r Datatypes.Coq_nil
                                                                               (Logic.eq_rect_r Datatypes.Coq_nil
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.WBox a) h2r)
                                                                                   (let {
                                                                                     _evar_0_ = DdT.Coq_derI
                                                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                        Datatypes.Coq_nil))
                                                                                      (Datatypes.app
                                                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                        Datatypes.Coq_nil))
                                                                                      (unsafeCoerce rs0
                                                                                        (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                          Datatypes.Coq_nil))
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                          Datatypes.Coq_nil))
                                                                                        (let {
                                                                                          _evar_0_ = let {
                                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r))
                                                                                                                   k2) LntT.Coq_bac) Datatypes.Coq_nil)) g0 (WBox2Ls a d1 h1l
                                                                                                                   h1r h2l h2r k1 k2)}
                                                                                                     in
                                                                                                     Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                       (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                         (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2)
                                                                                                         LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                         Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2)
                                                                                                         LntT.Coq_bac) Datatypes.Coq_nil))}
                                                                                         in
                                                                                         Logic.eq_rect
                                                                                           (Datatypes.app g0
                                                                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                               Datatypes.Coq_nil))) _evar_0_
                                                                                           (Datatypes.app
                                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)
                                                                                             Datatypes.Coq_nil)))) drs1}
                                                                                    in
                                                                                    Logic.eq_rect_r h2l _evar_0_ (Datatypes.app h2l Datatypes.Coq_nil)) d2) c0) b) h0) a0;
                                                                        Datatypes.Coq_inr h9 ->
                                                                         case h9 of {
                                                                          Specif.Coq_existT h10 _ ->
                                                                           Logic.eq_rect_r (Datatypes.app h2l h0)
                                                                             (Logic.eq_rect_r Datatypes.Coq_nil
                                                                               (Logic.eq_rect_r Datatypes.Coq_nil
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.WBox a) h10)
                                                                                   (let {
                                                                                     _evar_0_ = DdT.Coq_derI
                                                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                        Datatypes.Coq_nil))
                                                                                      (Datatypes.app
                                                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) (Datatypes.app h10 d2))) k2)
                                                                                        LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                      (unsafeCoerce rs0
                                                                                        (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                          Datatypes.Coq_nil))
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) (Datatypes.app h10 d2))) k2)
                                                                                          LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                        (let {
                                                                                          _evar_0_ = let {
                                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                     (Datatypes.app h10 d2))) k2) LntT.Coq_bac)
                                                                                                                   Datatypes.Coq_nil)) g0 (WBox2Ls a d1 h1l h1r h2l
                                                                                                                   (Datatypes.app h10 d2) k1 k2)}
                                                                                                     in
                                                                                                     Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                       (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                         (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                           (Datatypes.app h10 d2))) k2) LntT.Coq_bac) Datatypes.Coq_nil)))
                                                                                                       _evar_0_
                                                                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                         Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                           (Datatypes.app h10 d2))) k2) LntT.Coq_bac) Datatypes.Coq_nil))}
                                                                                         in
                                                                                         Logic.eq_rect
                                                                                           (Datatypes.app g0
                                                                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) (Datatypes.app h10 d2)))
                                                                                               k2) LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                           (Datatypes.app
                                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) (Datatypes.app h10 d2)))
                                                                                             k2) LntT.Coq_bac) Datatypes.Coq_nil)))) drs1}
                                                                                    in
                                                                                    Logic.eq_rect_r h2l _evar_0_ (Datatypes.app h2l Datatypes.Coq_nil)) c0) b) h0) a0}};
                                                                      Datatypes.Coq_inr h8 ->
                                                                       case h8 of {
                                                                        Specif.Coq_existT h9 _ ->
                                                                         Logic.eq_rect_r (Datatypes.app h2l h0)
                                                                           (Logic.eq_rect_r Datatypes.Coq_nil
                                                                             (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.WBox a) h9)
                                                                               (let {
                                                                                 _evar_0_ = DdT.Coq_derI
                                                                                  (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                    (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                    Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                  (Datatypes.app
                                                                                    (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h2l
                                                                                      (Datatypes.app c0 (Datatypes.Coq_cons (LntT.WBox a) (Datatypes.app h9 d2)))) k2)
                                                                                    LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                  (unsafeCoerce rs0
                                                                                    (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                      (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                      Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                    (Datatypes.app
                                                                                      (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h2l
                                                                                        (Datatypes.app c0 (Datatypes.Coq_cons (LntT.WBox a) (Datatypes.app h9 d2)))) k2)
                                                                                      LntT.Coq_bac) Datatypes.Coq_nil))
                                                                                    (let {
                                                                                      _evar_0_ = let {
                                                                                                  _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                               (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                               Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                               (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                               (Datatypes.app h2l
                                                                                                                 (Datatypes.app c0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                   (Datatypes.app h9 d2)))) k2) LntT.Coq_bac)
                                                                                                               Datatypes.Coq_nil)) g0
                                                                                                               (let {
                                                                                                                 _evar_0_ = WBox2Ls a d1 h1l h1r (Datatypes.app h2l c0)
                                                                                                                  (Datatypes.app h9 d2) k1 k2}
                                                                                                                in
                                                                                                                Logic.eq_rect_r
                                                                                                                  (Datatypes.app (Datatypes.app h2l c0) (Datatypes.Coq_cons
                                                                                                                    (LntT.WBox a) (Datatypes.app h9 d2))) _evar_0_
                                                                                                                  (Datatypes.app h2l
                                                                                                                    (Datatypes.app c0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                      (Datatypes.app h9 d2)))))}
                                                                                                 in
                                                                                                 Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                   (Datatypes.app h1l h1r) k1) d1)
                                                                                                   (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                     (Datatypes.Coq_pair
                                                                                                     (Datatypes.app h2l
                                                                                                       (Datatypes.app c0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                         (Datatypes.app h9 d2)))) k2) LntT.Coq_bac) Datatypes.Coq_nil)))
                                                                                                   _evar_0_
                                                                                                   (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                     (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                     (Datatypes.app h2l
                                                                                                       (Datatypes.app c0 (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                         (Datatypes.app h9 d2)))) k2) LntT.Coq_bac) Datatypes.Coq_nil))}
                                                                                     in
                                                                                     Logic.eq_rect
                                                                                       (Datatypes.app g0
                                                                                         (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                           (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app h2l
                                                                                             (Datatypes.app c0 (Datatypes.Coq_cons (LntT.WBox a) (Datatypes.app h9 d2)))) k2)
                                                                                           LntT.Coq_bac) Datatypes.Coq_nil))) _evar_0_
                                                                                       (Datatypes.app
                                                                                         (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                         (Datatypes.app h2l
                                                                                           (Datatypes.app c0 (Datatypes.Coq_cons (LntT.WBox a) (Datatypes.app h9 d2)))) k2)
                                                                                         LntT.Coq_bac) Datatypes.Coq_nil)))) drs1}
                                                                                in
                                                                                Logic.eq_rect_r h2l _evar_0_ (Datatypes.app h2l Datatypes.Coq_nil)) b) h0) a0}};
                                                                    Datatypes.Coq_inr h7 ->
                                                                     case h7 of {
                                                                      Specif.Coq_existT h8 _ ->
                                                                       Logic.eq_rect_r (Datatypes.app h2l h0)
                                                                         (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.WBox a) h8) (DdT.Coq_derI
                                                                           (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                             (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                             Datatypes.Coq_nil))
                                                                           (Datatypes.app
                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                             (Datatypes.Coq_pair
                                                                             (Datatypes.app (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h8))
                                                                               (Datatypes.app c0 (Datatypes.app b d2))) k2) LntT.Coq_bac) Datatypes.Coq_nil))
                                                                           (unsafeCoerce rs0
                                                                             (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                               (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                               Datatypes.Coq_nil))
                                                                             (Datatypes.app
                                                                               (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                               (Datatypes.Coq_pair
                                                                               (Datatypes.app (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h8))
                                                                                 (Datatypes.app c0 (Datatypes.app b d2))) k2) LntT.Coq_bac) Datatypes.Coq_nil))
                                                                             (let {
                                                                               _evar_0_ = let {
                                                                                           _evar_0_ = let {
                                                                                                       _evar_0_ = let {
                                                                                                                   _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons
                                                                                                                                (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                                (Datatypes.Coq_pair
                                                                                                                                (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                                                                  h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                                                                Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                                (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                                (Datatypes.app h1l h1r) k1) d1)
                                                                                                                                (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                                (Datatypes.Coq_pair
                                                                                                                                (Datatypes.app h2l (Datatypes.Coq_cons
                                                                                                                                  (LntT.WBox a)
                                                                                                                                  (Datatypes.app h8
                                                                                                                                    (Datatypes.app c0 (Datatypes.app b d2)))))
                                                                                                                                k2) LntT.Coq_bac) Datatypes.Coq_nil)) g0
                                                                                                                                (WBox2Ls a d1 h1l h1r h2l
                                                                                                                                (Datatypes.app h8
                                                                                                                                  (Datatypes.app c0 (Datatypes.app b d2))) k1
                                                                                                                                k2)}
                                                                                                                  in
                                                                                                                  Logic.eq_rect (Datatypes.Coq_cons (LntT.WBox a)
                                                                                                                    (Datatypes.app h8
                                                                                                                      (Datatypes.app c0 (Datatypes.app b d2)))) _evar_0_
                                                                                                                    (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a) h8)
                                                                                                                      (Datatypes.app c0 (Datatypes.app b d2)))}
                                                                                                      in
                                                                                                      Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                        (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                        (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app h2l
                                                                                                            (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a) h8)
                                                                                                              (Datatypes.app c0 (Datatypes.app b d2)))) k2) LntT.Coq_bac)
                                                                                                          Datatypes.Coq_nil))) _evar_0_
                                                                                                        (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                          (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                          Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                          (Datatypes.Coq_pair
                                                                                                          (Datatypes.app h2l
                                                                                                            (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a) h8)
                                                                                                              (Datatypes.app c0 (Datatypes.app b d2)))) k2) LntT.Coq_bac)
                                                                                                          Datatypes.Coq_nil))}
                                                                                          in
                                                                                          Logic.eq_rect
                                                                                            (Datatypes.app h2l
                                                                                              (Datatypes.app (Datatypes.Coq_cons (LntT.WBox a) h8)
                                                                                                (Datatypes.app c0 (Datatypes.app b d2)))) _evar_0_
                                                                                            (Datatypes.app (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h8))
                                                                                              (Datatypes.app c0 (Datatypes.app b d2)))}
                                                                              in
                                                                              Logic.eq_rect
                                                                                (Datatypes.app g0
                                                                                  (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h8))
                                                                                      (Datatypes.app c0 (Datatypes.app b d2))) k2) LntT.Coq_bac) Datatypes.Coq_nil)))
                                                                                _evar_0_
                                                                                (Datatypes.app
                                                                                  (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                  (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                  (Datatypes.app (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h8))
                                                                                    (Datatypes.app c0 (Datatypes.app b d2))) k2) LntT.Coq_bac) Datatypes.Coq_nil)))) drs1)
                                                                           h0) a0}}}}) _UU0393_') y) x __ __ __)}) __ __) k0) d0) _UU0394_0) _UU0393_ swap) h3) pp0;
                                       Datatypes.Coq_inr h5 -> case h5 of {
                                                                Specif.Coq_existT _ _ -> Logic.coq_False_rect}}}}) ps0 acm0 drs0 sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) k0))) ps0 __);
                           BBox2Ls a d1 h1l h1r h2l h2r k1 k2 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1)
                              d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil))
                                (Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r))
                                  k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\acm1 drs1 _ ->
                                  let {
                                   h1 = List_lemmasT.cons_eq_appT2 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil) pp0 (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) k0) (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r)
                                          k1) d1)}
                                  in
                                  case h1 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r (Datatypes.app h1l h1r) (\swap0 ->
                                        Logic.eq_rect_r k1
                                          (Logic.eq_rect_r d1
                                            (Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                              (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil)
                                              (let {
                                                _evar_0_ = (case swap0 of {
                                                             SwappedT.Coq_swapped_I x y a0 b c0 d2 -> (\_ _ ->
                                                              Logic.eq_rect_r (Datatypes.app h1l h1r) (\_ ->
                                                                Logic.eq_rect_r _UU0393_' (\_ _ ->
                                                                  Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b d2)))
                                                                    (let {h = List_lemmasT.app_eq_appT2 h1l h1r a0 (Datatypes.app b (Datatypes.app c0 d2))} in
                                                                     case h of {
                                                                      Specif.Coq_existT h0 h2 ->
                                                                       case h2 of {
                                                                        Datatypes.Coq_inl _ ->
                                                                         let {h3 = List_lemmasT.app_eq_appT2 b (Datatypes.app c0 d2) h0 h1r} in
                                                                         case h3 of {
                                                                          Specif.Coq_existT h4 h5 ->
                                                                           case h5 of {
                                                                            Datatypes.Coq_inl _ ->
                                                                             Logic.eq_rect_r (Datatypes.app a0 h0) (\drs2 acm2 ->
                                                                               Logic.eq_rect_r (Datatypes.app h0 h4)
                                                                                 (Logic.eq_rect_r (Datatypes.app h4 (Datatypes.app c0 d2)) (\acm3 _ -> DdT.Coq_derI
                                                                                   (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                     (Datatypes.Coq_pair
                                                                                     (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                       (Datatypes.app h4 d2))) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                   (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app (Datatypes.app h0 h4) d2))) k1) d1)
                                                                                     (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                     Datatypes.Coq_nil)))
                                                                                   (unsafeCoerce rs0
                                                                                     (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                       (Datatypes.Coq_pair
                                                                                       (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                         (Datatypes.app h4 d2))) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                     (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                       (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app (Datatypes.app h0 h4) d2))) k1) d1)
                                                                                       (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                       (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                       Datatypes.Coq_nil)))
                                                                                     (let {
                                                                                       _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                    (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                      (Datatypes.Coq_cons a (Datatypes.app h4 d2))) k1) d1)
                                                                                                    Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                    (Datatypes.app a0
                                                                                                      (Datatypes.app c0 (Datatypes.app h0 (Datatypes.app h4 d2)))) k1) d1)
                                                                                                    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                    (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2)
                                                                                                    LntT.Coq_fwd) Datatypes.Coq_nil)) g0
                                                                                                    (let {
                                                                                                      _evar_0_ = let {
                                                                                                                  _evar_0_ = let {
                                                                                                                              _evar_0_ = let {
                                                                                                                                          _evar_0_ = BBox2Ls a d1
                                                                                                                                           (Datatypes.app
                                                                                                                                             (Datatypes.app a0 c0) h0)
                                                                                                                                           (Datatypes.app h4 d2) h2l h2r k1
                                                                                                                                           k2}
                                                                                                                                         in
                                                                                                                                         Logic.eq_rect
                                                                                                                                           (Datatypes.app
                                                                                                                                             (Datatypes.app
                                                                                                                                               (Datatypes.app a0 c0) h0)
                                                                                                                                             (Datatypes.app h4 d2)) _evar_0_
                                                                                                                                           (Datatypes.app
                                                                                                                                             (Datatypes.app
                                                                                                                                               (Datatypes.app
                                                                                                                                                 (Datatypes.app a0 c0) h0)
                                                                                                                                               h4) d2)}
                                                                                                                             in
                                                                                                                             Logic.eq_rect_r
                                                                                                                               (Datatypes.app
                                                                                                                                 (Datatypes.app
                                                                                                                                   (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                                                   h4) d2) _evar_0_
                                                                                                                               (Datatypes.app
                                                                                                                                 (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                                                 (Datatypes.app h4 d2))}
                                                                                                                 in
                                                                                                                 Logic.eq_rect_r
                                                                                                                   (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0)
                                                                                                                     (Datatypes.app h4 d2)) _evar_0_
                                                                                                                   (Datatypes.app (Datatypes.app a0 c0)
                                                                                                                     (Datatypes.app h0 (Datatypes.app h4 d2)))}
                                                                                                     in
                                                                                                     Logic.eq_rect_r
                                                                                                       (Datatypes.app (Datatypes.app a0 c0)
                                                                                                         (Datatypes.app h0 (Datatypes.app h4 d2))) _evar_0_
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app c0 (Datatypes.app h0 (Datatypes.app h4 d2)))))}
                                                                                      in
                                                                                      Logic.eq_rect (Datatypes.app h0 (Datatypes.app h4 d2)) _evar_0_
                                                                                        (Datatypes.app (Datatypes.app h0 h4) d2)))
                                                                                   (let {f = LntT.nslclext g0} in
                                                                                    let {
                                                                                     c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                        (Datatypes.app h4 d2))) k1) d1) Datatypes.Coq_nil}
                                                                                    in
                                                                                    (case DdT.dersrec_map_single f c1 of {
                                                                                      Datatypes.Coq_pair _ x0 -> x0})
                                                                                      (let {
                                                                                        x0 = \_ _ _ f0 x0 ->
                                                                                         case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                          Datatypes.Coq_pair _ x1 -> x1}}
                                                                                       in
                                                                                       let {
                                                                                        acm4 = x0 __ __ __ (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                 (Datatypes.Coq_pair
                                                                                                 (Datatypes.app (Datatypes.app a0 h0) (Datatypes.Coq_cons a
                                                                                                   (Datatypes.app h4 (Datatypes.app c0 d2)))) k1) d1) Datatypes.Coq_nil) acm3}
                                                                                       in
                                                                                       let {
                                                                                        x1 = \_ ns0 ->
                                                                                         case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                          Datatypes.Coq_pair x1 _ -> x1}}
                                                                                       in
                                                                                       let {
                                                                                        acm5 = x1 __
                                                                                                 (LntT.nslclext g0 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                   (Datatypes.Coq_pair
                                                                                                   (Datatypes.app (Datatypes.app a0 h0) (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h4 (Datatypes.app c0 d2)))) k1) d1) Datatypes.Coq_nil))
                                                                                                 acm4 g0 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h4 (Datatypes.app c0 d2))))) k1)
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h4 (Datatypes.app c0 d2))))) k1
                                                                                                 (Datatypes.app a0
                                                                                                   (Datatypes.app c0
                                                                                                     (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2))))) d1
                                                                                                 (SwappedT.swapped_L
                                                                                                   (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                                     (Datatypes.app h4 (Datatypes.app c0 d2))))
                                                                                                   (Datatypes.app c0
                                                                                                     (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2)))) a0
                                                                                                   (Logic.eq_rec_r (Datatypes.app (Datatypes.app h4 c0) d2)
                                                                                                     (Logic.eq_rec_r
                                                                                                       (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons a
                                                                                                         (Datatypes.app h4 d2)))
                                                                                                       (Logic.eq_rec_r
                                                                                                         (Datatypes.app (Datatypes.Coq_cons a (Datatypes.app h4 c0)) d2)
                                                                                                         (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h4) c0)
                                                                                                           (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h4) d2)
                                                                                                             (Logic.eq_rec_r
                                                                                                               (Datatypes.app
                                                                                                                 (Datatypes.app h0
                                                                                                                   (Datatypes.app (Datatypes.Coq_cons a h4) c0)) d2)
                                                                                                               (Logic.eq_rec_r
                                                                                                                 (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons a h4))
                                                                                                                   c0)
                                                                                                                 (Logic.eq_rec_r
                                                                                                                   (Datatypes.app
                                                                                                                     (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons
                                                                                                                       a h4)) d2)
                                                                                                                   (SwappedT.swapped_R
                                                                                                                     (Datatypes.app
                                                                                                                       (Datatypes.app h0 (Datatypes.Coq_cons a h4)) c0)
                                                                                                                     (Datatypes.app (Datatypes.app c0 h0) (Datatypes.Coq_cons
                                                                                                                       a h4)) d2
                                                                                                                     (let {
                                                                                                                       _evar_0_ = let {
                                                                                                                                   _evar_0_ = let {
                                                                                                                                               _evar_0_ = Gen.arg1_cong_imp
                                                                                                                                                            (Datatypes.app
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h0
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h4)) c0)
                                                                                                                                                            (Datatypes.app h0
                                                                                                                                                              (Datatypes.Coq_cons
                                                                                                                                                              a
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h4 c0)))
                                                                                                                                                            (Datatypes.app c0
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h0
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h4)))
                                                                                                                                                            (SwappedT.swapped_simpleR
                                                                                                                                                              c0
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h0
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h4))
                                                                                                                                                              (Datatypes.app
                                                                                                                                                                h0
                                                                                                                                                                (Datatypes.Coq_cons
                                                                                                                                                                a h4)))}
                                                                                                                                              in
                                                                                                                                              Logic.eq_rec
                                                                                                                                                (Datatypes.Coq_cons a
                                                                                                                                                (Datatypes.app h4 c0))
                                                                                                                                                _evar_0_
                                                                                                                                                (Datatypes.app
                                                                                                                                                  (Datatypes.Coq_cons a h4)
                                                                                                                                                  c0)}
                                                                                                                                  in
                                                                                                                                  Logic.eq_rec
                                                                                                                                    (Datatypes.app c0
                                                                                                                                      (Datatypes.app h0 (Datatypes.Coq_cons a
                                                                                                                                        h4))) _evar_0_
                                                                                                                                    (Datatypes.app (Datatypes.app c0 h0)
                                                                                                                                      (Datatypes.Coq_cons a h4))}
                                                                                                                      in
                                                                                                                      Logic.eq_rec
                                                                                                                        (Datatypes.app h0
                                                                                                                          (Datatypes.app (Datatypes.Coq_cons a h4) c0))
                                                                                                                        _evar_0_
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app h0 (Datatypes.Coq_cons a h4)) c0)))
                                                                                                                   (Datatypes.app (Datatypes.app c0 h0)
                                                                                                                     (Datatypes.app (Datatypes.Coq_cons a h4) d2)))
                                                                                                                 (Datatypes.app h0
                                                                                                                   (Datatypes.app (Datatypes.Coq_cons a h4) c0)))
                                                                                                               (Datatypes.app h0
                                                                                                                 (Datatypes.app (Datatypes.app (Datatypes.Coq_cons a h4) c0)
                                                                                                                   d2))) (Datatypes.Coq_cons a (Datatypes.app h4 d2)))
                                                                                                           (Datatypes.Coq_cons a (Datatypes.app h4 c0))) (Datatypes.Coq_cons
                                                                                                         a (Datatypes.app (Datatypes.app h4 c0) d2)))
                                                                                                       (Datatypes.app c0
                                                                                                         (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2)))))
                                                                                                     (Datatypes.app h4 (Datatypes.app c0 d2)))) __ __}
                                                                                       in
                                                                                       let {
                                                                                        _evar_0_ = Logic.eq_rect
                                                                                                     (Datatypes.app a0
                                                                                                       (Datatypes.app c0
                                                                                                         (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2)))))
                                                                                                     acm5
                                                                                                     (Datatypes.app (Datatypes.app a0 c0)
                                                                                                       (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2))))}
                                                                                       in
                                                                                       Logic.eq_rect
                                                                                         (Datatypes.app (Datatypes.app a0 c0)
                                                                                           (Datatypes.app h0 (Datatypes.Coq_cons a (Datatypes.app h4 d2)))) _evar_0_
                                                                                         (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) h0) (Datatypes.Coq_cons a
                                                                                           (Datatypes.app h4 d2)))))) h1r acm2 drs2) b) h1l drs1 acm1;
                                                                            Datatypes.Coq_inr _ ->
                                                                             let {h6 = List_lemmasT.app_eq_appT2 c0 d2 h4 h1r} in
                                                                             case h6 of {
                                                                              Specif.Coq_existT h7 h8 ->
                                                                               case h8 of {
                                                                                Datatypes.Coq_inl _ ->
                                                                                 Logic.eq_rect_r (Datatypes.app a0 h0) (\drs2 acm2 ->
                                                                                   Logic.eq_rect_r (Datatypes.app b h4) (\acm3 drs3 ->
                                                                                     Logic.eq_rect_r (Datatypes.app h4 h7)
                                                                                       (Logic.eq_rect_r (Datatypes.app h7 d2) (\_ acm4 -> DdT.Coq_derI
                                                                                         (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                           (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app (Datatypes.app a0 h4) (Datatypes.Coq_cons a
                                                                                             (Datatypes.app h7 (Datatypes.app b d2)))) k1) d1) Datatypes.Coq_nil)
                                                                                           Datatypes.Coq_nil))
                                                                                         (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app a0 (Datatypes.app (Datatypes.app h4 h7) (Datatypes.app b d2))) k1)
                                                                                           d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                           Datatypes.Coq_nil)))
                                                                                         (unsafeCoerce rs0
                                                                                           (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app (Datatypes.app a0 h4) (Datatypes.Coq_cons a
                                                                                               (Datatypes.app h7 (Datatypes.app b d2)))) k1) d1) Datatypes.Coq_nil)
                                                                                             Datatypes.Coq_nil))
                                                                                           (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.app (Datatypes.app h4 h7) (Datatypes.app b d2)))
                                                                                             k1) d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                             Datatypes.Coq_nil)))
                                                                                           (let {
                                                                                             _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app (Datatypes.app a0 h4) (Datatypes.Coq_cons a
                                                                                                            (Datatypes.app h7 (Datatypes.app b d2)))) k1) d1)
                                                                                                          Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app a0
                                                                                                            (Datatypes.app h4 (Datatypes.app h7 (Datatypes.app b d2)))) k1)
                                                                                                          d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2)
                                                                                                          LntT.Coq_fwd) Datatypes.Coq_nil)) g0
                                                                                                          (let {
                                                                                                            _evar_0_ = let {
                                                                                                                        _evar_0_ = let {
                                                                                                                                    _evar_0_ = BBox2Ls a d1
                                                                                                                                     (Datatypes.app a0 h4)
                                                                                                                                     (Datatypes.app h7 (Datatypes.app b d2))
                                                                                                                                     h2l h2r k1 k2}
                                                                                                                                   in
                                                                                                                                   Logic.eq_rect
                                                                                                                                     (Datatypes.app (Datatypes.app a0 h4)
                                                                                                                                       (Datatypes.app h7
                                                                                                                                         (Datatypes.app b d2))) _evar_0_
                                                                                                                                     (Datatypes.app
                                                                                                                                       (Datatypes.app (Datatypes.app a0 h4)
                                                                                                                                         h7) (Datatypes.app b d2))}
                                                                                                                       in
                                                                                                                       Logic.eq_rect_r
                                                                                                                         (Datatypes.app
                                                                                                                           (Datatypes.app (Datatypes.app a0 h4) h7)
                                                                                                                           (Datatypes.app b d2)) _evar_0_
                                                                                                                         (Datatypes.app (Datatypes.app a0 h4)
                                                                                                                           (Datatypes.app h7 (Datatypes.app b d2)))}
                                                                                                           in
                                                                                                           Logic.eq_rect_r
                                                                                                             (Datatypes.app (Datatypes.app a0 h4)
                                                                                                               (Datatypes.app h7 (Datatypes.app b d2))) _evar_0_
                                                                                                             (Datatypes.app a0
                                                                                                               (Datatypes.app h4 (Datatypes.app h7 (Datatypes.app b d2)))))}
                                                                                            in
                                                                                            Logic.eq_rect (Datatypes.app h4 (Datatypes.app h7 (Datatypes.app b d2))) _evar_0_
                                                                                              (Datatypes.app (Datatypes.app h4 h7) (Datatypes.app b d2))))
                                                                                         (let {f = LntT.nslclext g0} in
                                                                                          let {
                                                                                           c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app (Datatypes.app a0 h4) (Datatypes.Coq_cons a
                                                                                              (Datatypes.app h7 (Datatypes.app b d2)))) k1) d1) Datatypes.Coq_nil}
                                                                                          in
                                                                                          (case DdT.dersrec_map_single f c1 of {
                                                                                            Datatypes.Coq_pair _ x0 -> x0})
                                                                                            (let {
                                                                                              x0 = \_ _ _ f0 x0 ->
                                                                                               case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                                Datatypes.Coq_pair _ x1 -> x1}}
                                                                                             in
                                                                                             let {
                                                                                              acm5 = x0 __ __ __ (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair
                                                                                                       (Datatypes.app (Datatypes.app a0 (Datatypes.app b h4))
                                                                                                         (Datatypes.Coq_cons a (Datatypes.app h7 d2))) k1) d1)
                                                                                                       Datatypes.Coq_nil) acm4}
                                                                                             in
                                                                                             let {
                                                                                              x1 = \_ ns0 ->
                                                                                               case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                                Datatypes.Coq_pair x1 _ -> x1}}
                                                                                             in
                                                                                             let {
                                                                                              acm6 = x1 __
                                                                                                       (LntT.nslclext g0 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app (Datatypes.app a0 (Datatypes.app b h4))
                                                                                                           (Datatypes.Coq_cons a (Datatypes.app h7 d2))) k1) d1)
                                                                                                         Datatypes.Coq_nil)) acm5 g0 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app h4 (Datatypes.Coq_cons a (Datatypes.app h7 d2)))))
                                                                                                       k1)
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app h4 (Datatypes.Coq_cons a (Datatypes.app h7 d2)))))
                                                                                                       k1
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app h4 (Datatypes.Coq_cons a
                                                                                                           (Datatypes.app h7 (Datatypes.app b d2))))) d1
                                                                                                       (SwappedT.swapped_L
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app h4 (Datatypes.Coq_cons a (Datatypes.app h7 d2))))
                                                                                                         (Datatypes.app h4 (Datatypes.Coq_cons a
                                                                                                           (Datatypes.app h7 (Datatypes.app b d2)))) a0
                                                                                                         (Logic.eq_rec_r
                                                                                                           (Datatypes.app (Datatypes.app b h4) (Datatypes.Coq_cons a
                                                                                                             (Datatypes.app h7 d2)))
                                                                                                           (Logic.eq_rec_r (Datatypes.app (Datatypes.app h7 b) d2)
                                                                                                             (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h7) d2)
                                                                                                               (Logic.eq_rec_r
                                                                                                                 (Datatypes.app (Datatypes.Coq_cons a (Datatypes.app h7 b))
                                                                                                                   d2)
                                                                                                                 (Logic.eq_rec_r (Datatypes.app (Datatypes.Coq_cons a h7) b)
                                                                                                                   (Logic.eq_rec_r
                                                                                                                     (Datatypes.app
                                                                                                                       (Datatypes.app (Datatypes.app b h4)
                                                                                                                         (Datatypes.Coq_cons a h7)) d2)
                                                                                                                     (Logic.eq_rec_r
                                                                                                                       (Datatypes.app
                                                                                                                         (Datatypes.app h4
                                                                                                                           (Datatypes.app (Datatypes.Coq_cons a h7) b)) d2)
                                                                                                                       (Logic.eq_rec_r
                                                                                                                         (Datatypes.app
                                                                                                                           (Datatypes.app h4 (Datatypes.Coq_cons a h7)) b)
                                                                                                                         (SwappedT.swapped_R
                                                                                                                           (Datatypes.app (Datatypes.app b h4)
                                                                                                                             (Datatypes.Coq_cons a h7))
                                                                                                                           (Datatypes.app
                                                                                                                             (Datatypes.app h4 (Datatypes.Coq_cons a h7)) b)
                                                                                                                           d2
                                                                                                                           (let {
                                                                                                                             _evar_0_ = let {
                                                                                                                                         _evar_0_ = let {
                                                                                                                                                     _evar_0_ = Gen.arg_cong_imp
                                                                                                                                                                  (Datatypes.app
                                                                                                                                                                    (Datatypes.app
                                                                                                                                                                    h4
                                                                                                                                                                    (Datatypes.Coq_cons
                                                                                                                                                                    a h7)) b)
                                                                                                                                                                  (Datatypes.app
                                                                                                                                                                    h4
                                                                                                                                                                    (Datatypes.Coq_cons
                                                                                                                                                                    a
                                                                                                                                                                    (Datatypes.app
                                                                                                                                                                    h7 b)))
                                                                                                                                                                  (SwappedT.swapped_simpleL
                                                                                                                                                                    b
                                                                                                                                                                    (Datatypes.app
                                                                                                                                                                    h4
                                                                                                                                                                    (Datatypes.Coq_cons
                                                                                                                                                                    a h7))
                                                                                                                                                                    (Datatypes.app
                                                                                                                                                                    h4
                                                                                                                                                                    (Datatypes.Coq_cons
                                                                                                                                                                    a h7)))}
                                                                                                                                                    in
                                                                                                                                                    Logic.eq_rec
                                                                                                                                                      (Datatypes.Coq_cons a
                                                                                                                                                      (Datatypes.app h7 b))
                                                                                                                                                      _evar_0_
                                                                                                                                                      (Datatypes.app
                                                                                                                                                        (Datatypes.Coq_cons a
                                                                                                                                                        h7) b)}
                                                                                                                                        in
                                                                                                                                        Logic.eq_rec
                                                                                                                                          (Datatypes.app h4
                                                                                                                                            (Datatypes.app
                                                                                                                                              (Datatypes.Coq_cons a h7) b))
                                                                                                                                          _evar_0_
                                                                                                                                          (Datatypes.app
                                                                                                                                            (Datatypes.app h4
                                                                                                                                              (Datatypes.Coq_cons a h7)) b)}
                                                                                                                            in
                                                                                                                            Logic.eq_rec
                                                                                                                              (Datatypes.app b
                                                                                                                                (Datatypes.app h4 (Datatypes.Coq_cons a h7)))
                                                                                                                              _evar_0_
                                                                                                                              (Datatypes.app (Datatypes.app b h4)
                                                                                                                                (Datatypes.Coq_cons a h7))))
                                                                                                                         (Datatypes.app h4
                                                                                                                           (Datatypes.app (Datatypes.Coq_cons a h7) b)))
                                                                                                                       (Datatypes.app h4
                                                                                                                         (Datatypes.app
                                                                                                                           (Datatypes.app (Datatypes.Coq_cons a h7) b) d2)))
                                                                                                                     (Datatypes.app (Datatypes.app b h4)
                                                                                                                       (Datatypes.app (Datatypes.Coq_cons a h7) d2)))
                                                                                                                   (Datatypes.Coq_cons a (Datatypes.app h7 b)))
                                                                                                                 (Datatypes.Coq_cons a
                                                                                                                 (Datatypes.app (Datatypes.app h7 b) d2)))
                                                                                                               (Datatypes.Coq_cons a (Datatypes.app h7 d2)))
                                                                                                             (Datatypes.app h7 (Datatypes.app b d2)))
                                                                                                           (Datatypes.app b
                                                                                                             (Datatypes.app h4 (Datatypes.Coq_cons a (Datatypes.app h7 d2))))))
                                                                                                       __ __}
                                                                                             in
                                                                                             Logic.eq_rect
                                                                                               (Datatypes.app a0
                                                                                                 (Datatypes.app h4 (Datatypes.Coq_cons a
                                                                                                   (Datatypes.app h7 (Datatypes.app b d2))))) acm6
                                                                                               (Datatypes.app (Datatypes.app a0 h4) (Datatypes.Coq_cons a
                                                                                                 (Datatypes.app h7 (Datatypes.app b d2))))))) h1r drs3 acm3) c0) h0 acm2 drs2)
                                                                                   h1l drs1 acm1;
                                                                                Datatypes.Coq_inr _ ->
                                                                                 Logic.eq_rect_r (Datatypes.app a0 h0) (\drs2 acm2 ->
                                                                                   Logic.eq_rect_r (Datatypes.app b h4) (\acm3 drs3 ->
                                                                                     Logic.eq_rect_r (Datatypes.app c0 h7) (\_ acm4 ->
                                                                                       Logic.eq_rect_r (Datatypes.app h7 h1r) (DdT.Coq_derI
                                                                                         (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                           (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h7)
                                                                                             (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                         (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h7 h1r)))) k1)
                                                                                           d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                           Datatypes.Coq_nil)))
                                                                                         (unsafeCoerce rs0
                                                                                           (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h7)
                                                                                               (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                           (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h7 h1r))))
                                                                                             k1) d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                             Datatypes.Coq_nil)))
                                                                                           (LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                             (Datatypes.Coq_pair
                                                                                             (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h7)
                                                                                               (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil)
                                                                                             (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b (Datatypes.app h7 h1r))))
                                                                                             k1) d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                             Datatypes.Coq_nil)) g0
                                                                                             (let {
                                                                                               _evar_0_ = let {
                                                                                                           _evar_0_ = let {
                                                                                                                       _evar_0_ = BBox2Ls a d1
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app (Datatypes.app a0 c0) b) h7) h1r h2l
                                                                                                                        h2r k1 k2}
                                                                                                                      in
                                                                                                                      Logic.eq_rect_r
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app
                                                                                                                            (Datatypes.app (Datatypes.app a0 c0) b) h7) h1r)
                                                                                                                        _evar_0_
                                                                                                                        (Datatypes.app
                                                                                                                          (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                                          (Datatypes.app h7 h1r))}
                                                                                                          in
                                                                                                          Logic.eq_rect_r
                                                                                                            (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                              (Datatypes.app h7 h1r)) _evar_0_
                                                                                                            (Datatypes.app (Datatypes.app a0 c0)
                                                                                                              (Datatypes.app b (Datatypes.app h7 h1r)))}
                                                                                              in
                                                                                              Logic.eq_rect_r
                                                                                                (Datatypes.app (Datatypes.app a0 c0)
                                                                                                  (Datatypes.app b (Datatypes.app h7 h1r))) _evar_0_
                                                                                                (Datatypes.app a0
                                                                                                  (Datatypes.app c0 (Datatypes.app b (Datatypes.app h7 h1r)))))))
                                                                                         (let {f = LntT.nslclext g0} in
                                                                                          let {
                                                                                           c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h7)
                                                                                              (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil}
                                                                                          in
                                                                                          (case DdT.dersrec_map_single f c1 of {
                                                                                            Datatypes.Coq_pair _ x0 -> x0})
                                                                                            (let {
                                                                                              x0 = \_ _ _ f0 x0 ->
                                                                                               case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                                Datatypes.Coq_pair _ x1 -> x1}}
                                                                                             in
                                                                                             let {
                                                                                              acm5 = x0 __ __ __ (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair
                                                                                                       (Datatypes.app
                                                                                                         (Datatypes.app a0 (Datatypes.app b (Datatypes.app c0 h7)))
                                                                                                         (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) acm4}
                                                                                             in
                                                                                             let {
                                                                                              x1 = \_ ns0 ->
                                                                                               case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                                Datatypes.Coq_pair x1 _ -> x1}}
                                                                                             in
                                                                                             let {
                                                                                              acm6 = x1 __
                                                                                                       (LntT.nslclext g0 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app
                                                                                                           (Datatypes.app a0 (Datatypes.app b (Datatypes.app c0 h7)))
                                                                                                           (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)) acm5 g0
                                                                                                       Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app c0 (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))))
                                                                                                       k1)
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app c0 (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))))
                                                                                                       k1
                                                                                                       (Datatypes.app a0
                                                                                                         (Datatypes.app c0
                                                                                                           (Datatypes.app b (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))))
                                                                                                       d1
                                                                                                       (SwappedT.swapped_L
                                                                                                         (Datatypes.app b
                                                                                                           (Datatypes.app c0 (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))
                                                                                                         (Datatypes.app c0
                                                                                                           (Datatypes.app b (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))
                                                                                                         a0
                                                                                                         (Logic.eq_rec_r
                                                                                                           (Datatypes.app (Datatypes.app b c0)
                                                                                                             (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))
                                                                                                           (Logic.eq_rec_r
                                                                                                             (Datatypes.app (Datatypes.app (Datatypes.app b c0) h7)
                                                                                                               (Datatypes.Coq_cons a h1r))
                                                                                                             (Logic.eq_rec_r
                                                                                                               (Datatypes.app (Datatypes.app c0 b)
                                                                                                                 (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))
                                                                                                               (Logic.eq_rec_r
                                                                                                                 (Datatypes.app (Datatypes.app (Datatypes.app c0 b) h7)
                                                                                                                   (Datatypes.Coq_cons a h1r))
                                                                                                                 (SwappedT.swapped_R (Datatypes.app (Datatypes.app b c0) h7)
                                                                                                                   (Datatypes.app (Datatypes.app c0 b) h7)
                                                                                                                   (Datatypes.Coq_cons a h1r)
                                                                                                                   (SwappedT.swapped_R (Datatypes.app b c0)
                                                                                                                     (Datatypes.app c0 b) h7
                                                                                                                     (Gen.arg_cong_imp (Datatypes.app c0 b)
                                                                                                                       (Datatypes.app c0 b)
                                                                                                                       (SwappedT.swapped_simpleL b c0 c0))))
                                                                                                                 (Datatypes.app (Datatypes.app c0 b)
                                                                                                                   (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))
                                                                                                               (Datatypes.app c0
                                                                                                                 (Datatypes.app b
                                                                                                                   (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))))
                                                                                                             (Datatypes.app (Datatypes.app b c0)
                                                                                                               (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))
                                                                                                           (Datatypes.app b
                                                                                                             (Datatypes.app c0 (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))))
                                                                                                       __ __}
                                                                                             in
                                                                                             let {
                                                                                              _evar_0_ = let {
                                                                                                          _evar_0_ = Logic.eq_rect
                                                                                                                       (Datatypes.app a0
                                                                                                                         (Datatypes.app c0
                                                                                                                           (Datatypes.app b
                                                                                                                             (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))))
                                                                                                                       acm6
                                                                                                                       (Datatypes.app (Datatypes.app a0 c0)
                                                                                                                         (Datatypes.app b
                                                                                                                           (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))}
                                                                                                         in
                                                                                                         Logic.eq_rect
                                                                                                           (Datatypes.app (Datatypes.app a0 c0)
                                                                                                             (Datatypes.app b (Datatypes.app h7 (Datatypes.Coq_cons a h1r))))
                                                                                                           _evar_0_
                                                                                                           (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                             (Datatypes.app h7 (Datatypes.Coq_cons a h1r)))}
                                                                                             in
                                                                                             Logic.eq_rect
                                                                                               (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b)
                                                                                                 (Datatypes.app h7 (Datatypes.Coq_cons a h1r))) _evar_0_
                                                                                               (Datatypes.app (Datatypes.app (Datatypes.app (Datatypes.app a0 c0) b) h7)
                                                                                                 (Datatypes.Coq_cons a h1r))))) d2) h4 drs3 acm3) h0 acm2 drs2) h1l drs1 acm1}}}};
                                                                        Datatypes.Coq_inr _ ->
                                                                         Logic.eq_rect_r (Datatypes.app h1l h0)
                                                                           (Logic.eq_rect_r (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))) (\_ acm2 ->
                                                                             DdT.Coq_derI
                                                                             (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                               (Datatypes.Coq_pair
                                                                               (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                 (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) k1) d1) Datatypes.Coq_nil)
                                                                               Datatypes.Coq_nil))
                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                               (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2))) k1) d1)
                                                                               (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                               (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                               Datatypes.Coq_nil)))
                                                                             (unsafeCoerce rs0
                                                                               (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair
                                                                                 (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                   (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) k1) d1) Datatypes.Coq_nil)
                                                                                 Datatypes.Coq_nil))
                                                                               (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2))) k1) d1)
                                                                                 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                 Datatypes.Coq_nil)))
                                                                               (let {
                                                                                 _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                              (Datatypes.Coq_pair
                                                                                              (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                                (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) k1) d1)
                                                                                              Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                              (Datatypes.Coq_pair
                                                                                              (Datatypes.app h1l (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))
                                                                                              k1) d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                              (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                              Datatypes.Coq_nil)) g0
                                                                                              (let {
                                                                                                _evar_0_ = let {
                                                                                                            _evar_0_ = BBox2Ls a d1 h1l
                                                                                                             (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))) h2l
                                                                                                             h2r k1 k2}
                                                                                                           in
                                                                                                           Logic.eq_rect
                                                                                                             (Datatypes.app h1l
                                                                                                               (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))
                                                                                                             _evar_0_
                                                                                                             (Datatypes.app (Datatypes.app h1l h0)
                                                                                                               (Datatypes.app c0 (Datatypes.app b d2)))}
                                                                                               in
                                                                                               Logic.eq_rect_r
                                                                                                 (Datatypes.app (Datatypes.app h1l h0)
                                                                                                   (Datatypes.app c0 (Datatypes.app b d2))) _evar_0_
                                                                                                 (Datatypes.app h1l
                                                                                                   (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))))}
                                                                                in
                                                                                Logic.eq_rect (Datatypes.app h1l (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))
                                                                                  _evar_0_ (Datatypes.app (Datatypes.app h1l h0) (Datatypes.app c0 (Datatypes.app b d2)))))
                                                                             (let {f = LntT.nslclext g0} in
                                                                              let {
                                                                               c1 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                  (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) k1) d1) Datatypes.Coq_nil}
                                                                              in
                                                                              (case DdT.dersrec_map_single f c1 of {
                                                                                Datatypes.Coq_pair _ x0 -> x0})
                                                                                (let {
                                                                                  x0 = \_ _ _ f0 x0 ->
                                                                                   case GenT.coq_ForallT_map_rev f0 x0 of {
                                                                                    Datatypes.Coq_pair _ x1 -> x1}}
                                                                                 in
                                                                                 let {
                                                                                  acm3 = x0 __ __ __ (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                           (Datatypes.Coq_pair
                                                                                           (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                             (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) k1) d1)
                                                                                           Datatypes.Coq_nil) acm2}
                                                                                 in
                                                                                 let {
                                                                                  ns0 = LntT.nslclext g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                            (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) k1) d1)
                                                                                          Datatypes.Coq_nil)}
                                                                                 in
                                                                                 (case LntacsT.can_gen_swapL_def' ns0 of {
                                                                                   Datatypes.Coq_pair x1 _ -> x1}) acm3 g0 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) k1)
                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2))))) k1
                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2))))) d1
                                                                                   (SwappedT.swapped_L (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2)))) (Datatypes.Coq_cons a
                                                                                     (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))) h1l
                                                                                     (SwappedT.swapped_cons a (Datatypes.app h0 (Datatypes.app b (Datatypes.app c0 d2)))
                                                                                       (Datatypes.app h0 (Datatypes.app c0 (Datatypes.app b d2)))
                                                                                       (SwappedT.swapped_L (Datatypes.app b (Datatypes.app c0 d2))
                                                                                         (Datatypes.app c0 (Datatypes.app b d2)) h0
                                                                                         (Logic.eq_rec_r (Datatypes.app (Datatypes.app b c0) d2)
                                                                                           (Logic.eq_rec_r (Datatypes.app (Datatypes.app c0 b) d2)
                                                                                             (SwappedT.swapped_R (Datatypes.app b c0) (Datatypes.app c0 b) d2
                                                                                               (Gen.arg_cong_imp (Datatypes.app c0 b) (Datatypes.app c0 b)
                                                                                                 (SwappedT.swapped_simpleL b c0 c0)))
                                                                                             (Datatypes.app c0 (Datatypes.app b d2)))
                                                                                           (Datatypes.app b (Datatypes.app c0 d2)))))) __ __))) h1r drs1 acm1) a0}})
                                                                    _UU0393_') y) x __ __ __)}) __ __}
                                               in
                                               Logic.eq_rect_r g0 _evar_0_ (Datatypes.app g0 Datatypes.Coq_nil)) k0) d0) _UU0394_0) _UU0393_ swap) pp0;
                                   Datatypes.Coq_inr h2 ->
                                    case h2 of {
                                     Specif.Coq_existT h3 _ ->
                                      let {
                                       h4 = List_lemmasT.cons_eq_appT2 Datatypes.Coq_nil h3 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0)
                                              d0) k0) (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)}
                                      in
                                      case h4 of {
                                       Datatypes.Coq_inl _ ->
                                        Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1) h3)
                                          (Logic.eq_rect_r Datatypes.Coq_nil
                                            (Logic.eq_rect_r (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) (\swap0 ->
                                              Logic.eq_rect_r k2
                                                (Logic.eq_rect_r LntT.Coq_fwd
                                                  (Logic.eq_rect_r Datatypes.Coq_nil
                                                    ((case swap0 of {
                                                       SwappedT.Coq_swapped_I x y a0 b c0 d2 -> (\_ _ ->
                                                        Logic.eq_rect_r (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) (\_ ->
                                                          Logic.eq_rect_r _UU0393_' (\_ _ ->
                                                            Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app c0 (Datatypes.app b d2)))
                                                              (let {
                                                                h = List_lemmasT.app_eq_appT2 h2l (Datatypes.Coq_cons (LntT.BBox a) h2r) a0
                                                                      (Datatypes.app b (Datatypes.app c0 d2))}
                                                               in
                                                               case h of {
                                                                Specif.Coq_existT h0 h5 ->
                                                                 case h5 of {
                                                                  Datatypes.Coq_inl _ ->
                                                                   let {h6 = List_lemmasT.app_eq_appT2 b (Datatypes.app c0 d2) h0 (Datatypes.Coq_cons (LntT.BBox a) h2r)} in
                                                                   case h6 of {
                                                                    Specif.Coq_existT h7 h8 ->
                                                                     case h8 of {
                                                                      Datatypes.Coq_inl _ ->
                                                                       let {h9 = List_lemmasT.cons_eq_appT2 h2r h7 (Datatypes.app c0 d2) (LntT.BBox a)} in
                                                                       case h9 of {
                                                                        Datatypes.Coq_inl _ ->
                                                                         let {h10 = List_lemmasT.app_eq_consT2 h2r c0 d2 (LntT.BBox a)} in
                                                                         case h10 of {
                                                                          Datatypes.Coq_inl _ ->
                                                                           Logic.eq_rect_r (Datatypes.app h0 h7)
                                                                             (Logic.eq_rect_r Datatypes.Coq_nil
                                                                               (Logic.eq_rect_r Datatypes.Coq_nil
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.BBox a) h2r)
                                                                                   (let {
                                                                                     _evar_0_ = DdT.Coq_derI
                                                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                        Datatypes.Coq_nil))
                                                                                      (Datatypes.app
                                                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app a0 (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a) h2r))) k2)
                                                                                        LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                      (unsafeCoerce rs0
                                                                                        (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                          Datatypes.Coq_nil))
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app a0 (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a) h2r))) k2)
                                                                                          LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                        (let {
                                                                                          _evar_0_ = let {
                                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app a0
                                                                                                                     (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                       h2r))) k2) LntT.Coq_fwd) Datatypes.Coq_nil)) g0
                                                                                                                   (let {
                                                                                                                     _evar_0_ = BBox2Ls a d1 h1l h1r (Datatypes.app a0 h0)
                                                                                                                      h2r k1 k2}
                                                                                                                    in
                                                                                                                    Logic.eq_rect_r
                                                                                                                      (Datatypes.app (Datatypes.app a0 h0)
                                                                                                                        (Datatypes.Coq_cons (LntT.BBox a) h2r)) _evar_0_
                                                                                                                      (Datatypes.app a0
                                                                                                                        (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                          h2r))))}
                                                                                                     in
                                                                                                     Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                       (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0
                                                                                                           (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a) h2r))) k2)
                                                                                                         LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                         Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0
                                                                                                           (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a) h2r))) k2)
                                                                                                         LntT.Coq_fwd) Datatypes.Coq_nil))}
                                                                                         in
                                                                                         Logic.eq_rect
                                                                                           (Datatypes.app g0
                                                                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app a0 (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a) h2r)))
                                                                                               k2) LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                           (Datatypes.app
                                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a) h2r))) k2)
                                                                                             LntT.Coq_fwd) Datatypes.Coq_nil)))) drs1}
                                                                                    in
                                                                                    Logic.eq_rect_r h0 _evar_0_ (Datatypes.app h0 Datatypes.Coq_nil)) d2) c0) h7) b;
                                                                          Datatypes.Coq_inr h11 ->
                                                                           case h11 of {
                                                                            Specif.Coq_existT h12 _ ->
                                                                             Logic.eq_rect_r (Datatypes.app h0 h7)
                                                                               (Logic.eq_rect_r Datatypes.Coq_nil
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.BBox a) h12)
                                                                                   (let {
                                                                                     _evar_0_ = DdT.Coq_derI
                                                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                        Datatypes.Coq_nil))
                                                                                      (Datatypes.app
                                                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app a0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                          (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                      (unsafeCoerce rs0
                                                                                        (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                          Datatypes.Coq_nil))
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app a0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                            (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                        (let {
                                                                                          _evar_0_ = let {
                                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app a0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                     (Datatypes.app h12 (Datatypes.app h0 d2)))) k2)
                                                                                                                   LntT.Coq_fwd) Datatypes.Coq_nil)) g0 (BBox2Ls a d1 h1l h1r
                                                                                                                   a0 (Datatypes.app h12 (Datatypes.app h0 d2)) k1 k2)}
                                                                                                     in
                                                                                                     Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                       (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                           (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_fwd)
                                                                                                         Datatypes.Coq_nil))) _evar_0_
                                                                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                         Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                           (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_fwd)
                                                                                                         Datatypes.Coq_nil))}
                                                                                         in
                                                                                         Logic.eq_rect
                                                                                           (Datatypes.app g0
                                                                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app a0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                 (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_fwd)
                                                                                               Datatypes.Coq_nil))) _evar_0_
                                                                                           (Datatypes.app
                                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                               (Datatypes.app h12 (Datatypes.app h0 d2)))) k2) LntT.Coq_fwd)
                                                                                             Datatypes.Coq_nil)))) drs1}
                                                                                    in
                                                                                    Logic.eq_rect_r h0 _evar_0_ (Datatypes.app h0 Datatypes.Coq_nil)) c0) h7) b}};
                                                                        Datatypes.Coq_inr h10 ->
                                                                         case h10 of {
                                                                          Specif.Coq_existT h11 _ ->
                                                                           Logic.eq_rect_r (Datatypes.app h0 h7)
                                                                             (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.BBox a) h11) (DdT.Coq_derI
                                                                               (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                 Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                               (Datatypes.app
                                                                                 (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                   (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                 (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app a0
                                                                                   (Datatypes.app c0
                                                                                     (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a) h11)) d2))) k2)
                                                                                 LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                               (unsafeCoerce rs0
                                                                                 (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                   (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                 (Datatypes.app
                                                                                   (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                   (Datatypes.app a0
                                                                                     (Datatypes.app c0
                                                                                       (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a) h11)) d2))) k2)
                                                                                   LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                 (let {
                                                                                   _evar_0_ = let {
                                                                                               _evar_0_ = let {
                                                                                                           _evar_0_ = let {
                                                                                                                       _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons
                                                                                                                                    (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                                    (Datatypes.Coq_pair
                                                                                                                                    (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                                                                      h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                                                                    Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                                    (Datatypes.app h1l h1r) k1) d1)
                                                                                                                                    (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                                    (Datatypes.Coq_pair
                                                                                                                                    (Datatypes.app a0
                                                                                                                                      (Datatypes.app c0
                                                                                                                                        (Datatypes.app h0 (Datatypes.Coq_cons
                                                                                                                                          (LntT.BBox a)
                                                                                                                                          (Datatypes.app h11 d2))))) k2)
                                                                                                                                    LntT.Coq_fwd) Datatypes.Coq_nil)) g0
                                                                                                                                    (let {
                                                                                                                                      _evar_0_ = let {
                                                                                                                                                  _evar_0_ = BBox2Ls a d1 h1l
                                                                                                                                                   h1r
                                                                                                                                                   (Datatypes.app a0
                                                                                                                                                     (Datatypes.app c0 h0))
                                                                                                                                                   (Datatypes.app h11 d2) k1
                                                                                                                                                   k2}
                                                                                                                                                 in
                                                                                                                                                 Logic.eq_rect_r
                                                                                                                                                   (Datatypes.app
                                                                                                                                                     (Datatypes.app a0
                                                                                                                                                       (Datatypes.app c0 h0))
                                                                                                                                                     (Datatypes.Coq_cons
                                                                                                                                                     (LntT.BBox a)
                                                                                                                                                     (Datatypes.app h11 d2)))
                                                                                                                                                   _evar_0_
                                                                                                                                                   (Datatypes.app a0
                                                                                                                                                     (Datatypes.app
                                                                                                                                                       (Datatypes.app c0 h0)
                                                                                                                                                       (Datatypes.Coq_cons
                                                                                                                                                       (LntT.BBox a)
                                                                                                                                                       (Datatypes.app h11 d2))))}
                                                                                                                                     in
                                                                                                                                     Logic.eq_rect_r
                                                                                                                                       (Datatypes.app (Datatypes.app c0 h0)
                                                                                                                                         (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                                         (Datatypes.app h11 d2))) _evar_0_
                                                                                                                                       (Datatypes.app c0
                                                                                                                                         (Datatypes.app h0
                                                                                                                                           (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                                           (Datatypes.app h11 d2)))))}
                                                                                                                      in
                                                                                                                      Logic.eq_rect (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                        (Datatypes.app h11 d2)) _evar_0_
                                                                                                                        (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a) h11)
                                                                                                                          d2)}
                                                                                                          in
                                                                                                          Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                            (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                            (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                              (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                              (Datatypes.app a0
                                                                                                                (Datatypes.app c0
                                                                                                                  (Datatypes.app h0
                                                                                                                    (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a) h11) d2))))
                                                                                                              k2) LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                                            (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                              (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                              Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                              (Datatypes.Coq_pair
                                                                                                              (Datatypes.app a0
                                                                                                                (Datatypes.app c0
                                                                                                                  (Datatypes.app h0
                                                                                                                    (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a) h11) d2))))
                                                                                                              k2) LntT.Coq_fwd) Datatypes.Coq_nil))}
                                                                                              in
                                                                                              Logic.eq_rect
                                                                                                (Datatypes.app h0 (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a) h11) d2))
                                                                                                _evar_0_
                                                                                                (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a) h11)) d2)}
                                                                                  in
                                                                                  Logic.eq_rect
                                                                                    (Datatypes.app g0
                                                                                      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app a0
                                                                                          (Datatypes.app c0
                                                                                            (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a) h11)) d2)))
                                                                                        k2) LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                    (Datatypes.app
                                                                                      (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app a0
                                                                                        (Datatypes.app c0
                                                                                          (Datatypes.app (Datatypes.app h0 (Datatypes.Coq_cons (LntT.BBox a) h11)) d2))) k2)
                                                                                      LntT.Coq_fwd) Datatypes.Coq_nil)))) drs1) h7) b}};
                                                                      Datatypes.Coq_inr _ ->
                                                                       let {h9 = List_lemmasT.app_eq_appT2 c0 d2 h7 (Datatypes.Coq_cons (LntT.BBox a) h2r)} in
                                                                       case h9 of {
                                                                        Specif.Coq_existT h10 h11 ->
                                                                         case h11 of {
                                                                          Datatypes.Coq_inl _ ->
                                                                           let {h12 = List_lemmasT.cons_eq_appT2 h2r h10 d2 (LntT.BBox a)} in
                                                                           case h12 of {
                                                                            Datatypes.Coq_inl _ ->
                                                                             Logic.eq_rect_r (Datatypes.app h7 h10)
                                                                               (Logic.eq_rect_r Datatypes.Coq_nil
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.BBox a) h2r)
                                                                                   (let {
                                                                                     _evar_0_ = DdT.Coq_derI
                                                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                        Datatypes.Coq_nil))
                                                                                      (Datatypes.app
                                                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app a0
                                                                                          (Datatypes.app h7 (Datatypes.app b (Datatypes.Coq_cons (LntT.BBox a) h2r)))) k2)
                                                                                        LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                      (unsafeCoerce rs0
                                                                                        (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                          Datatypes.Coq_nil))
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app a0
                                                                                            (Datatypes.app h7 (Datatypes.app b (Datatypes.Coq_cons (LntT.BBox a) h2r)))) k2)
                                                                                          LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                        (let {
                                                                                          _evar_0_ = let {
                                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app a0
                                                                                                                     (Datatypes.app h7
                                                                                                                       (Datatypes.app b (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                         h2r)))) k2) LntT.Coq_fwd) Datatypes.Coq_nil)) g0
                                                                                                                   (let {
                                                                                                                     _evar_0_ = let {
                                                                                                                                 _evar_0_ = BBox2Ls a d1 h1l h1r
                                                                                                                                  (Datatypes.app a0 (Datatypes.app h7 b)) h2r
                                                                                                                                  k1 k2}
                                                                                                                                in
                                                                                                                                Logic.eq_rect_r
                                                                                                                                  (Datatypes.app
                                                                                                                                    (Datatypes.app a0 (Datatypes.app h7 b))
                                                                                                                                    (Datatypes.Coq_cons (LntT.BBox a) h2r))
                                                                                                                                  _evar_0_
                                                                                                                                  (Datatypes.app a0
                                                                                                                                    (Datatypes.app (Datatypes.app h7 b)
                                                                                                                                      (Datatypes.Coq_cons (LntT.BBox a) h2r)))}
                                                                                                                    in
                                                                                                                    Logic.eq_rect_r
                                                                                                                      (Datatypes.app (Datatypes.app h7 b) (Datatypes.Coq_cons
                                                                                                                        (LntT.BBox a) h2r)) _evar_0_
                                                                                                                      (Datatypes.app h7
                                                                                                                        (Datatypes.app b (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                          h2r))))}
                                                                                                     in
                                                                                                     Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                       (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0
                                                                                                           (Datatypes.app h7
                                                                                                             (Datatypes.app b (Datatypes.Coq_cons (LntT.BBox a) h2r)))) k2)
                                                                                                         LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                         Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app a0
                                                                                                           (Datatypes.app h7
                                                                                                             (Datatypes.app b (Datatypes.Coq_cons (LntT.BBox a) h2r)))) k2)
                                                                                                         LntT.Coq_fwd) Datatypes.Coq_nil))}
                                                                                         in
                                                                                         Logic.eq_rect
                                                                                           (Datatypes.app g0
                                                                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app a0
                                                                                                 (Datatypes.app h7 (Datatypes.app b (Datatypes.Coq_cons (LntT.BBox a) h2r))))
                                                                                               k2) LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                           (Datatypes.app
                                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app a0
                                                                                               (Datatypes.app h7 (Datatypes.app b (Datatypes.Coq_cons (LntT.BBox a) h2r))))
                                                                                             k2) LntT.Coq_fwd) Datatypes.Coq_nil)))) drs1}
                                                                                    in
                                                                                    Logic.eq_rect_r h7 _evar_0_ (Datatypes.app h7 Datatypes.Coq_nil)) d2) h10) c0;
                                                                            Datatypes.Coq_inr h13 ->
                                                                             case h13 of {
                                                                              Specif.Coq_existT h14 _ ->
                                                                               Logic.eq_rect_r (Datatypes.app h7 h10)
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.BBox a) h14) (DdT.Coq_derI
                                                                                   (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                     (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                     Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                   (Datatypes.app
                                                                                     (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                       (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                     (Datatypes.app a0
                                                                                       (Datatypes.app (Datatypes.app h7 (Datatypes.Coq_cons (LntT.BBox a) h14))
                                                                                         (Datatypes.app b d2))) k2) LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                   (unsafeCoerce rs0
                                                                                     (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                       Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                     (Datatypes.app
                                                                                       (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                         (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                       (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                       (Datatypes.app a0
                                                                                         (Datatypes.app (Datatypes.app h7 (Datatypes.Coq_cons (LntT.BBox a) h14))
                                                                                           (Datatypes.app b d2))) k2) LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                     (let {
                                                                                       _evar_0_ = let {
                                                                                                   _evar_0_ = let {
                                                                                                               _evar_0_ = let {
                                                                                                                           _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons
                                                                                                                                        (Datatypes.Coq_cons
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.app h1l
                                                                                                                                          (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                                        Datatypes.Coq_nil) Datatypes.Coq_nil)
                                                                                                                                        (Datatypes.Coq_cons
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.app h1l h1r) k1) d1)
                                                                                                                                        (Datatypes.Coq_cons
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.Coq_pair
                                                                                                                                        (Datatypes.app a0
                                                                                                                                          (Datatypes.app h7
                                                                                                                                            (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                                            (Datatypes.app h14
                                                                                                                                              (Datatypes.app b d2))))) k2)
                                                                                                                                        LntT.Coq_fwd) Datatypes.Coq_nil)) g0
                                                                                                                                        (let {
                                                                                                                                          _evar_0_ = BBox2Ls a d1 h1l h1r
                                                                                                                                           (Datatypes.app a0 h7)
                                                                                                                                           (Datatypes.app h14
                                                                                                                                             (Datatypes.app b d2)) k1 k2}
                                                                                                                                         in
                                                                                                                                         Logic.eq_rect_r
                                                                                                                                           (Datatypes.app
                                                                                                                                             (Datatypes.app a0 h7)
                                                                                                                                             (Datatypes.Coq_cons (LntT.BBox
                                                                                                                                             a)
                                                                                                                                             (Datatypes.app h14
                                                                                                                                               (Datatypes.app b d2))))
                                                                                                                                           _evar_0_
                                                                                                                                           (Datatypes.app a0
                                                                                                                                             (Datatypes.app h7
                                                                                                                                               (Datatypes.Coq_cons (LntT.BBox
                                                                                                                                               a)
                                                                                                                                               (Datatypes.app h14
                                                                                                                                                 (Datatypes.app b d2))))))}
                                                                                                                          in
                                                                                                                          Logic.eq_rect (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                            (Datatypes.app h14 (Datatypes.app b d2)))
                                                                                                                            _evar_0_
                                                                                                                            (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                              h14) (Datatypes.app b d2))}
                                                                                                              in
                                                                                                              Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                                (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                                  (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                  (Datatypes.app a0
                                                                                                                    (Datatypes.app h7
                                                                                                                      (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a) h14)
                                                                                                                        (Datatypes.app b d2)))) k2) LntT.Coq_fwd)
                                                                                                                  Datatypes.Coq_nil))) _evar_0_
                                                                                                                (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                  (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                                  Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                  (Datatypes.Coq_pair
                                                                                                                  (Datatypes.app a0
                                                                                                                    (Datatypes.app h7
                                                                                                                      (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a) h14)
                                                                                                                        (Datatypes.app b d2)))) k2) LntT.Coq_fwd)
                                                                                                                  Datatypes.Coq_nil))}
                                                                                                  in
                                                                                                  Logic.eq_rect
                                                                                                    (Datatypes.app h7
                                                                                                      (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a) h14)
                                                                                                        (Datatypes.app b d2))) _evar_0_
                                                                                                    (Datatypes.app (Datatypes.app h7 (Datatypes.Coq_cons (LntT.BBox a) h14))
                                                                                                      (Datatypes.app b d2))}
                                                                                      in
                                                                                      Logic.eq_rect
                                                                                        (Datatypes.app g0
                                                                                          (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                            (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app a0
                                                                                              (Datatypes.app (Datatypes.app h7 (Datatypes.Coq_cons (LntT.BBox a) h14))
                                                                                                (Datatypes.app b d2))) k2) LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app a0
                                                                                            (Datatypes.app (Datatypes.app h7 (Datatypes.Coq_cons (LntT.BBox a) h14))
                                                                                              (Datatypes.app b d2))) k2) LntT.Coq_fwd) Datatypes.Coq_nil)))) drs1) h10) c0}};
                                                                          Datatypes.Coq_inr _ ->
                                                                           Logic.eq_rect_r (Datatypes.app h10 (Datatypes.Coq_cons (LntT.BBox a) h2r)) (DdT.Coq_derI
                                                                             (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                               (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                               Datatypes.Coq_nil))
                                                                             (Datatypes.app
                                                                               (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                               (Datatypes.Coq_pair
                                                                               (Datatypes.app a0
                                                                                 (Datatypes.app c0
                                                                                   (Datatypes.app b (Datatypes.app h10 (Datatypes.Coq_cons (LntT.BBox a) h2r))))) k2)
                                                                               LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                             (unsafeCoerce rs0
                                                                               (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                 Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                               (Datatypes.app
                                                                                 (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                   (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                 (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app a0
                                                                                   (Datatypes.app c0
                                                                                     (Datatypes.app b (Datatypes.app h10 (Datatypes.Coq_cons (LntT.BBox a) h2r))))) k2)
                                                                                 LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                               (let {
                                                                                 _evar_0_ = let {
                                                                                             _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                          Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1)
                                                                                                          d1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app a0
                                                                                                            (Datatypes.app c0
                                                                                                              (Datatypes.app b
                                                                                                                (Datatypes.app h10 (Datatypes.Coq_cons (LntT.BBox a) h2r)))))
                                                                                                          k2) LntT.Coq_fwd) Datatypes.Coq_nil)) g0
                                                                                                          (let {
                                                                                                            _evar_0_ = let {
                                                                                                                        _evar_0_ = let {
                                                                                                                                    _evar_0_ = BBox2Ls a d1 h1l h1r
                                                                                                                                     (Datatypes.app a0
                                                                                                                                       (Datatypes.app c0
                                                                                                                                         (Datatypes.app b h10))) h2r k1 k2}
                                                                                                                                   in
                                                                                                                                   Logic.eq_rect_r
                                                                                                                                     (Datatypes.app
                                                                                                                                       (Datatypes.app a0
                                                                                                                                         (Datatypes.app c0
                                                                                                                                           (Datatypes.app b h10)))
                                                                                                                                       (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                                       h2r)) _evar_0_
                                                                                                                                     (Datatypes.app a0
                                                                                                                                       (Datatypes.app
                                                                                                                                         (Datatypes.app c0
                                                                                                                                           (Datatypes.app b h10))
                                                                                                                                         (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                                         h2r)))}
                                                                                                                       in
                                                                                                                       Logic.eq_rect_r
                                                                                                                         (Datatypes.app
                                                                                                                           (Datatypes.app c0 (Datatypes.app b h10))
                                                                                                                           (Datatypes.Coq_cons (LntT.BBox a) h2r)) _evar_0_
                                                                                                                         (Datatypes.app c0
                                                                                                                           (Datatypes.app (Datatypes.app b h10)
                                                                                                                             (Datatypes.Coq_cons (LntT.BBox a) h2r)))}
                                                                                                           in
                                                                                                           Logic.eq_rect_r
                                                                                                             (Datatypes.app (Datatypes.app b h10) (Datatypes.Coq_cons
                                                                                                               (LntT.BBox a) h2r)) _evar_0_
                                                                                                             (Datatypes.app b
                                                                                                               (Datatypes.app h10 (Datatypes.Coq_cons (LntT.BBox a) h2r))))}
                                                                                            in
                                                                                            Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                              (Datatypes.app h1l h1r) k1) d1)
                                                                                              (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                (Datatypes.Coq_pair
                                                                                                (Datatypes.app a0
                                                                                                  (Datatypes.app c0
                                                                                                    (Datatypes.app b
                                                                                                      (Datatypes.app h10 (Datatypes.Coq_cons (LntT.BBox a) h2r))))) k2)
                                                                                                LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                              (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                (Datatypes.app a0
                                                                                                  (Datatypes.app c0
                                                                                                    (Datatypes.app b
                                                                                                      (Datatypes.app h10 (Datatypes.Coq_cons (LntT.BBox a) h2r))))) k2)
                                                                                                LntT.Coq_fwd) Datatypes.Coq_nil))}
                                                                                in
                                                                                Logic.eq_rect
                                                                                  (Datatypes.app g0
                                                                                    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app a0
                                                                                        (Datatypes.app c0
                                                                                          (Datatypes.app b (Datatypes.app h10 (Datatypes.Coq_cons (LntT.BBox a) h2r))))) k2)
                                                                                      LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                  (Datatypes.app
                                                                                    (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app a0
                                                                                      (Datatypes.app c0
                                                                                        (Datatypes.app b (Datatypes.app h10 (Datatypes.Coq_cons (LntT.BBox a) h2r))))) k2)
                                                                                    LntT.Coq_fwd) Datatypes.Coq_nil)))) drs1) d2}}}};
                                                                  Datatypes.Coq_inr _ ->
                                                                   let {h6 = List_lemmasT.cons_eq_appT2 h2r h0 (Datatypes.app b (Datatypes.app c0 d2)) (LntT.BBox a)} in
                                                                   case h6 of {
                                                                    Datatypes.Coq_inl _ ->
                                                                     let {h7 = List_lemmasT.app_eq_consT2 h2r b (Datatypes.app c0 d2) (LntT.BBox a)} in
                                                                     case h7 of {
                                                                      Datatypes.Coq_inl _ ->
                                                                       let {h8 = List_lemmasT.app_eq_consT2 h2r c0 d2 (LntT.BBox a)} in
                                                                       case h8 of {
                                                                        Datatypes.Coq_inl _ ->
                                                                         Logic.eq_rect_r (Datatypes.app h2l h0)
                                                                           (Logic.eq_rect_r Datatypes.Coq_nil
                                                                             (Logic.eq_rect_r Datatypes.Coq_nil
                                                                               (Logic.eq_rect_r Datatypes.Coq_nil
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.BBox a) h2r)
                                                                                   (let {
                                                                                     _evar_0_ = DdT.Coq_derI
                                                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                        Datatypes.Coq_nil))
                                                                                      (Datatypes.app
                                                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                        Datatypes.Coq_nil))
                                                                                      (unsafeCoerce rs0
                                                                                        (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                          Datatypes.Coq_nil))
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                          Datatypes.Coq_nil))
                                                                                        (let {
                                                                                          _evar_0_ = let {
                                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r))
                                                                                                                   k2) LntT.Coq_fwd) Datatypes.Coq_nil)) g0 (BBox2Ls a d1 h1l
                                                                                                                   h1r h2l h2r k1 k2)}
                                                                                                     in
                                                                                                     Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                       (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                         (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2)
                                                                                                         LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                         Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2)
                                                                                                         LntT.Coq_fwd) Datatypes.Coq_nil))}
                                                                                         in
                                                                                         Logic.eq_rect
                                                                                           (Datatypes.app g0
                                                                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                               Datatypes.Coq_nil))) _evar_0_
                                                                                           (Datatypes.app
                                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)
                                                                                             Datatypes.Coq_nil)))) drs1}
                                                                                    in
                                                                                    Logic.eq_rect_r h2l _evar_0_ (Datatypes.app h2l Datatypes.Coq_nil)) d2) c0) b) h0) a0;
                                                                        Datatypes.Coq_inr h9 ->
                                                                         case h9 of {
                                                                          Specif.Coq_existT h10 _ ->
                                                                           Logic.eq_rect_r (Datatypes.app h2l h0)
                                                                             (Logic.eq_rect_r Datatypes.Coq_nil
                                                                               (Logic.eq_rect_r Datatypes.Coq_nil
                                                                                 (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.BBox a) h10)
                                                                                   (let {
                                                                                     _evar_0_ = DdT.Coq_derI
                                                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                        Datatypes.Coq_nil))
                                                                                      (Datatypes.app
                                                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) (Datatypes.app h10 d2))) k2)
                                                                                        LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                      (unsafeCoerce rs0
                                                                                        (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                          Datatypes.Coq_nil))
                                                                                        (Datatypes.app
                                                                                          (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                            (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) (Datatypes.app h10 d2))) k2)
                                                                                          LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                        (let {
                                                                                          _evar_0_ = let {
                                                                                                      _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                                   Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                   (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                     (Datatypes.app h10 d2))) k2) LntT.Coq_fwd)
                                                                                                                   Datatypes.Coq_nil)) g0 (BBox2Ls a d1 h1l h1r h2l
                                                                                                                   (Datatypes.app h10 d2) k1 k2)}
                                                                                                     in
                                                                                                     Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                       (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                       (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                         (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                           (Datatypes.app h10 d2))) k2) LntT.Coq_fwd) Datatypes.Coq_nil)))
                                                                                                       _evar_0_
                                                                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                         Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                         (Datatypes.Coq_pair
                                                                                                         (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                           (Datatypes.app h10 d2))) k2) LntT.Coq_fwd) Datatypes.Coq_nil))}
                                                                                         in
                                                                                         Logic.eq_rect
                                                                                           (Datatypes.app g0
                                                                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) (Datatypes.app h10 d2)))
                                                                                               k2) LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                           (Datatypes.app
                                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) (Datatypes.app h10 d2)))
                                                                                             k2) LntT.Coq_fwd) Datatypes.Coq_nil)))) drs1}
                                                                                    in
                                                                                    Logic.eq_rect_r h2l _evar_0_ (Datatypes.app h2l Datatypes.Coq_nil)) c0) b) h0) a0}};
                                                                      Datatypes.Coq_inr h8 ->
                                                                       case h8 of {
                                                                        Specif.Coq_existT h9 _ ->
                                                                         Logic.eq_rect_r (Datatypes.app h2l h0)
                                                                           (Logic.eq_rect_r Datatypes.Coq_nil
                                                                             (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.BBox a) h9)
                                                                               (let {
                                                                                 _evar_0_ = DdT.Coq_derI
                                                                                  (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                    (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                    Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                  (Datatypes.app
                                                                                    (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h2l
                                                                                      (Datatypes.app c0 (Datatypes.Coq_cons (LntT.BBox a) (Datatypes.app h9 d2)))) k2)
                                                                                    LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                  (unsafeCoerce rs0
                                                                                    (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                      (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                      Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                                                    (Datatypes.app
                                                                                      (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                        (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                      (Datatypes.app h2l
                                                                                        (Datatypes.app c0 (Datatypes.Coq_cons (LntT.BBox a) (Datatypes.app h9 d2)))) k2)
                                                                                      LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                                    (let {
                                                                                      _evar_0_ = let {
                                                                                                  _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons
                                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                               (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                                               Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                               (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                                                                                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                               (Datatypes.app h2l
                                                                                                                 (Datatypes.app c0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                   (Datatypes.app h9 d2)))) k2) LntT.Coq_fwd)
                                                                                                               Datatypes.Coq_nil)) g0
                                                                                                               (let {
                                                                                                                 _evar_0_ = BBox2Ls a d1 h1l h1r (Datatypes.app h2l c0)
                                                                                                                  (Datatypes.app h9 d2) k1 k2}
                                                                                                                in
                                                                                                                Logic.eq_rect_r
                                                                                                                  (Datatypes.app (Datatypes.app h2l c0) (Datatypes.Coq_cons
                                                                                                                    (LntT.BBox a) (Datatypes.app h9 d2))) _evar_0_
                                                                                                                  (Datatypes.app h2l
                                                                                                                    (Datatypes.app c0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                      (Datatypes.app h9 d2)))))}
                                                                                                 in
                                                                                                 Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                   (Datatypes.app h1l h1r) k1) d1)
                                                                                                   (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                     (Datatypes.Coq_pair
                                                                                                     (Datatypes.app h2l
                                                                                                       (Datatypes.app c0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                         (Datatypes.app h9 d2)))) k2) LntT.Coq_fwd) Datatypes.Coq_nil)))
                                                                                                   _evar_0_
                                                                                                   (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                     (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                     (Datatypes.app h2l
                                                                                                       (Datatypes.app c0 (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                         (Datatypes.app h9 d2)))) k2) LntT.Coq_fwd) Datatypes.Coq_nil))}
                                                                                     in
                                                                                     Logic.eq_rect
                                                                                       (Datatypes.app g0
                                                                                         (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                           (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app h2l
                                                                                             (Datatypes.app c0 (Datatypes.Coq_cons (LntT.BBox a) (Datatypes.app h9 d2)))) k2)
                                                                                           LntT.Coq_fwd) Datatypes.Coq_nil))) _evar_0_
                                                                                       (Datatypes.app
                                                                                         (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                           (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                         (Datatypes.app h2l
                                                                                           (Datatypes.app c0 (Datatypes.Coq_cons (LntT.BBox a) (Datatypes.app h9 d2)))) k2)
                                                                                         LntT.Coq_fwd) Datatypes.Coq_nil)))) drs1}
                                                                                in
                                                                                Logic.eq_rect_r h2l _evar_0_ (Datatypes.app h2l Datatypes.Coq_nil)) b) h0) a0}};
                                                                    Datatypes.Coq_inr h7 ->
                                                                     case h7 of {
                                                                      Specif.Coq_existT h8 _ ->
                                                                       Logic.eq_rect_r (Datatypes.app h2l h0)
                                                                         (Logic.eq_rect_r (Datatypes.Coq_cons (LntT.BBox a) h8) (DdT.Coq_derI
                                                                           (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                             (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                             Datatypes.Coq_nil))
                                                                           (Datatypes.app
                                                                             (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                               (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                             (Datatypes.Coq_pair
                                                                             (Datatypes.app (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h8))
                                                                               (Datatypes.app c0 (Datatypes.app b d2))) k2) LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                           (unsafeCoerce rs0
                                                                             (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                               (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)
                                                                               Datatypes.Coq_nil))
                                                                             (Datatypes.app
                                                                               (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                 (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                               (Datatypes.Coq_pair
                                                                               (Datatypes.app (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h8))
                                                                                 (Datatypes.app c0 (Datatypes.app b d2))) k2) LntT.Coq_fwd) Datatypes.Coq_nil))
                                                                             (let {
                                                                               _evar_0_ = let {
                                                                                           _evar_0_ = let {
                                                                                                       _evar_0_ = let {
                                                                                                                   _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons
                                                                                                                                (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                                (Datatypes.Coq_pair
                                                                                                                                (Datatypes.app h1l (Datatypes.Coq_cons a
                                                                                                                                  h1r)) k1) d1) Datatypes.Coq_nil)
                                                                                                                                Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                                                                (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                                                (Datatypes.app h1l h1r) k1) d1)
                                                                                                                                (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                                                (Datatypes.Coq_pair
                                                                                                                                (Datatypes.app h2l (Datatypes.Coq_cons
                                                                                                                                  (LntT.BBox a)
                                                                                                                                  (Datatypes.app h8
                                                                                                                                    (Datatypes.app c0 (Datatypes.app b d2)))))
                                                                                                                                k2) LntT.Coq_fwd) Datatypes.Coq_nil)) g0
                                                                                                                                (BBox2Ls a d1 h1l h1r h2l
                                                                                                                                (Datatypes.app h8
                                                                                                                                  (Datatypes.app c0 (Datatypes.app b d2))) k1
                                                                                                                                k2)}
                                                                                                                  in
                                                                                                                  Logic.eq_rect (Datatypes.Coq_cons (LntT.BBox a)
                                                                                                                    (Datatypes.app h8
                                                                                                                      (Datatypes.app c0 (Datatypes.app b d2)))) _evar_0_
                                                                                                                    (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a) h8)
                                                                                                                      (Datatypes.app c0 (Datatypes.app b d2)))}
                                                                                                      in
                                                                                                      Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                        (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                        (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons
                                                                                                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                                          (Datatypes.app h2l
                                                                                                            (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a) h8)
                                                                                                              (Datatypes.app c0 (Datatypes.app b d2)))) k2) LntT.Coq_fwd)
                                                                                                          Datatypes.Coq_nil))) _evar_0_
                                                                                                        (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                          (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                                                          Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                                          (Datatypes.Coq_pair
                                                                                                          (Datatypes.app h2l
                                                                                                            (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a) h8)
                                                                                                              (Datatypes.app c0 (Datatypes.app b d2)))) k2) LntT.Coq_fwd)
                                                                                                          Datatypes.Coq_nil))}
                                                                                          in
                                                                                          Logic.eq_rect
                                                                                            (Datatypes.app h2l
                                                                                              (Datatypes.app (Datatypes.Coq_cons (LntT.BBox a) h8)
                                                                                                (Datatypes.app c0 (Datatypes.app b d2)))) _evar_0_
                                                                                            (Datatypes.app (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h8))
                                                                                              (Datatypes.app c0 (Datatypes.app b d2)))}
                                                                              in
                                                                              Logic.eq_rect
                                                                                (Datatypes.app g0
                                                                                  (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h8))
                                                                                      (Datatypes.app c0 (Datatypes.app b d2))) k2) LntT.Coq_fwd) Datatypes.Coq_nil)))
                                                                                _evar_0_
                                                                                (Datatypes.app
                                                                                  (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                    (Datatypes.app h1l h1r) k1) d1) Datatypes.Coq_nil)) (Datatypes.Coq_cons
                                                                                  (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                                  (Datatypes.app (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h8))
                                                                                    (Datatypes.app c0 (Datatypes.app b d2))) k2) LntT.Coq_fwd) Datatypes.Coq_nil)))) drs1)
                                                                           h0) a0}}}}) _UU0393_') y) x __ __ __)}) __ __) k0) d0) _UU0394_0) _UU0393_ swap) h3) pp0;
                                       Datatypes.Coq_inr h5 -> case h5 of {
                                                                Specif.Coq_existT _ _ -> Logic.coq_False_rect}}}}) ps0 acm0 drs0 sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) k0))) ps0 __)}) __ __) c sppc0) g1}})
                 seq0 __) ps drs acm)) concl) ps __ sppc)}) __ __) __ nsr rs g k seq d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ __ __

gen_swapR_step_b2L_lc :: (Datatypes.Coq_list (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))) ->
                         (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) -> a2 -> (DdT.Coq_dersrec
                         (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) a3 ()) -> (GenT.ForallT
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                         (LntacsT.Coq_can_gen_swapR a1 a3)) -> (Gen.Coq_rsub
                         (Datatypes.Coq_list (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)))
                         (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) a2 a3) -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) -> LntT.Coq_dir -> (Datatypes.Coq_list
                         (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                         (Datatypes.Coq_list (LntT.PropF a1)) -> DdT.Coq_derrec
                         (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) a3 ()
gen_swapR_step_b2L_lc ps concl nsr drs acm rs g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LntT.NSlclctxt ps0 c g0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LntT.nslclext g0) ps0) (\_ ->
         Logic.eq_rect (LntT.nslclext g0 c) (\sppc0 ->
           let {ns = LntT.nslclext g0 c} in
           (case LntacsT.can_gen_swapR_def' ns of {
             Datatypes.Coq_pair _ x -> x}) (\g1 k0 seq0 _UU0393_0 _UU0394_ _UU0394_' d0 swap _ _ ->
             Logic.eq_rect (List.map (LntT.nslclext g0) ps0) (\drs0 acm0 ->
               Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_0 _UU0394_) (\_ ->
                 let {pp = List_lemmasT.app_eq_appT2 g0 c g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) k0)} in
                 case pp of {
                  Specif.Coq_existT pp0 pp1 ->
                   case pp1 of {
                    Datatypes.Coq_inl _ ->
                     let {pp2 = List_lemmasT.cons_eq_appT2 k0 pp0 c (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0)} in
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                         Logic.eq_rect_r Datatypes.Coq_nil (\drs2 acm2 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) k0) (\sppc1 ->
                             let {drs3 = Logic.eq_rect (Datatypes.app g1 Datatypes.Coq_nil) drs2 g1} in
                             let {acm3 = Logic.eq_rect (Datatypes.app g1 Datatypes.Coq_nil) acm2 g1} in
                             (case sppc1 of {
                               WBox2Ls a d1 h1l h1r h2l h2r k1 k2 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r))
                                  k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect (Datatypes.app h1l h1r) (\_ ->
                                    Logic.eq_rect_r _UU0394_ (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r))
                                          k2) LntT.Coq_bac) Datatypes.Coq_nil)
                                          (Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                            (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\acm4 drs4 sppc2 ->
                                            Logic.eq_rect (Datatypes.app h1l h1r) (\sppc3 ->
                                              Logic.eq_rect_r _UU0394_ (\drs5 acm5 sppc4 ->
                                                Logic.eq_rect_r d0 (\acm6 _ sppc5 ->
                                                  Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                    (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil) (\_ -> DdT.Coq_derI
                                                    (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                      (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                    (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d0)
                                                      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r))
                                                      k2) LntT.Coq_bac) Datatypes.Coq_nil)))
                                                    (unsafeCoerce rs0
                                                      (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                      (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d0)
                                                        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil)))
                                                      (LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d0) Datatypes.Coq_nil) Datatypes.Coq_nil)
                                                        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d0)
                                                        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil)) g1 (WBox2Ls a d0 h1l
                                                        h1r h2l h2r _UU0394_' k2)))
                                                    (let {f = LntT.nslclext g1} in
                                                     let {
                                                      c0 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r))
                                                       _UU0394_') d0) Datatypes.Coq_nil}
                                                     in
                                                     (case DdT.dersrec_map_single f c0 of {
                                                       Datatypes.Coq_pair _ x -> x})
                                                       (let {x = \_ _ _ f0 x -> case GenT.coq_ForallT_map_rev f0 x of {
                                                                                 Datatypes.Coq_pair _ x0 -> x0}} in
                                                        let {
                                                         acm7 = x __ __ __ (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                  (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_) d0) Datatypes.Coq_nil) acm6}
                                                        in
                                                        let {
                                                         ns0 = LntT.nslclext g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                 (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_) d0) Datatypes.Coq_nil)}
                                                        in
                                                        (case LntacsT.can_gen_swapR_def' ns0 of {
                                                          Datatypes.Coq_pair x0 _ -> x0}) acm7 g1 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_) (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_
                                                          _UU0394_' d0 swap __ __))) k0 sppc5) d1 acm5 drs5 sppc4) k1 drs4 acm4 sppc3) _UU0393_0 sppc2) ps0 acm3 drs3 sppc1)
                                          k0) d1) k1) _UU0393_0 __ __ __) ps0 __);
                               BBox2Ls a d1 h1l h1r h2l h2r k1 k2 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r))
                                  k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect (Datatypes.app h1l h1r) (\_ ->
                                    Logic.eq_rect_r _UU0394_ (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r))
                                          k2) LntT.Coq_fwd) Datatypes.Coq_nil)
                                          (Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                            (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\acm4 drs4 sppc2 ->
                                            Logic.eq_rect (Datatypes.app h1l h1r) (\sppc3 ->
                                              Logic.eq_rect_r _UU0394_ (\drs5 acm5 sppc4 ->
                                                Logic.eq_rect_r d0 (\acm6 _ sppc5 ->
                                                  Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                    (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil) (\_ -> DdT.Coq_derI
                                                    (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                      (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                    (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d0)
                                                      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r))
                                                      k2) LntT.Coq_fwd) Datatypes.Coq_nil)))
                                                    (unsafeCoerce rs0
                                                      (List.map (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d0) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                      (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d0)
                                                        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil)))
                                                      (LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d0) Datatypes.Coq_nil) Datatypes.Coq_nil)
                                                        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d0)
                                                        (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil)) g1 (BBox2Ls a d0 h1l
                                                        h1r h2l h2r _UU0394_' k2)))
                                                    (let {f = LntT.nslclext g1} in
                                                     let {
                                                      c0 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r))
                                                       _UU0394_') d0) Datatypes.Coq_nil}
                                                     in
                                                     (case DdT.dersrec_map_single f c0 of {
                                                       Datatypes.Coq_pair _ x -> x})
                                                       (let {x = \_ _ _ f0 x -> case GenT.coq_ForallT_map_rev f0 x of {
                                                                                 Datatypes.Coq_pair _ x0 -> x0}} in
                                                        let {
                                                         acm7 = x __ __ __ (LntT.nslclext g1) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                  (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_) d0) Datatypes.Coq_nil) acm6}
                                                        in
                                                        let {
                                                         ns0 = LntT.nslclext g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                 (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_) d0) Datatypes.Coq_nil)}
                                                        in
                                                        (case LntacsT.can_gen_swapR_def' ns0 of {
                                                          Datatypes.Coq_pair x0 _ -> x0}) acm7 g1 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                          (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_) (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_
                                                          _UU0394_' d0 swap __ __))) k0 sppc5) d1 acm5 drs5 sppc4) k1 drs4 acm4 sppc3) _UU0393_0 sppc2) ps0 acm3 drs3 sppc1)
                                          k0) d1) k1) _UU0393_0 __ __ __) ps0 __)}) __ __) c sppc0) pp0 drs1 acm1) g0 acm0 drs0;
                      Datatypes.Coq_inr pp3 ->
                       case pp3 of {
                        Specif.Coq_existT pp4 _ ->
                         Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) pp4) (\_ acm2 ->
                             Logic.eq_rect_r (Datatypes.app pp4 c) (DdT.Coq_derI
                               (List.map (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4))) ps0)
                               (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) (Datatypes.app pp4 c)))
                               (unsafeCoerce rs0
                                 (List.map (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4))) ps0)
                                 (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) (Datatypes.app pp4 c)))
                                 (let {
                                   _evar_0_ = let {
                                               _evar_0_ = LntT.coq_NSlclctxt' ps0 c
                                                            (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4))
                                                            sppc0}
                                              in
                                              Logic.eq_rect_r
                                                (Datatypes.app (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4))
                                                  c) _evar_0_
                                                (Datatypes.app g1
                                                  (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4) c))}
                                  in
                                  Logic.eq_rect_r (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4) c) _evar_0_
                                    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) (Datatypes.app pp4 c))))
                               (let {
                                 cs = List.map (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4)))
                                        ps0}
                                in
                                (case DdT.dersrec_forall cs of {
                                  Datatypes.Coq_pair _ x -> x}) (\q qin ->
                                  let {x = \_ _ f l y -> case GenT.coq_InT_map_iffT f l y of {
                                                          Datatypes.Coq_pair x _ -> x}} in
                                  let {
                                   qin0 = x __ __
                                            (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4))) ps0
                                            q qin}
                                  in
                                  case qin0 of {
                                   Specif.Coq_existT x0 h ->
                                    case h of {
                                     Datatypes.Coq_pair _ h1 ->
                                      Logic.eq_rect
                                        (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4)) x0)
                                        (let {x1 = \_ _ l -> case GenT.coq_ForallT_forall l of {
                                                              Datatypes.Coq_pair x1 _ -> x1}} in
                                         let {
                                          acm3 = x1 __ __
                                                   (List.map
                                                     (LntT.nslclext
                                                       (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) pp4))) ps0) acm2
                                                   (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) pp4))
                                                     x0)
                                                   (GenT.coq_InT_map
                                                     (LntT.nslclext
                                                       (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) pp4))) ps0 x0
                                                     h1)}
                                         in
                                         let {x2 = \_ ns0 -> case LntacsT.can_gen_swapR_def' ns0 of {
                                                              Datatypes.Coq_pair x2 _ -> x2}} in
                                         let {
                                          acm4 = x2 __
                                                   (LntT.nslclext (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) pp4))
                                                     x0) acm3 g1 (Datatypes.app pp4 x0) (Datatypes.Coq_pair _UU0393_0 _UU0394_) _UU0393_0 _UU0394_ _UU0394_' d0 swap __ __}
                                         in
                                         let {
                                          _evar_0_ = Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0)
                                                       (Datatypes.app pp4 x0)) acm4
                                                       (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4) x0)}
                                         in
                                         Logic.eq_rect
                                           (Datatypes.app g1 (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4) x0))
                                           _evar_0_
                                           (Datatypes.app (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4)) x0)) q}})))
                               k0) pp0 drs1 acm1) g0 acm0 drs0}};
                    Datatypes.Coq_inr _ ->
                     Logic.eq_rect_r (Datatypes.app g0 pp0)
                       (Logic.eq_rect_r (Datatypes.app pp0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) k0)) (\sppc1 ->
                         (case sppc1 of {
                           WBox2Ls a d1 h1l h1r h2l h2r k1 k2 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1)
                              d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil))
                                (Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r))
                                  k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\acm1 drs1 _ ->
                                  let {
                                   h1 = List_lemmasT.cons_eq_appT2 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil) pp0 (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) k0) (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r)
                                          k1) d1)}
                                  in
                                  case h1 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r (Datatypes.app h1l h1r)
                                        (Logic.eq_rect_r k1 (\swap0 ->
                                          Logic.eq_rect_r d1
                                            (Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                              (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil)
                                              (let {
                                                _evar_0_ = DdT.Coq_derI
                                                 (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                 (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d1)
                                                   (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2)
                                                   LntT.Coq_bac) Datatypes.Coq_nil)))
                                                 (unsafeCoerce rs0
                                                   (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                     (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                   (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d1)
                                                     (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r))
                                                     k2) LntT.Coq_bac) Datatypes.Coq_nil)))
                                                   (LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                     (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d1) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                     (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac) Datatypes.Coq_nil)) g0
                                                     (WBox2Ls a d1 h1l h1r h2l h2r _UU0394_' k2)))
                                                 (let {f = LntT.nslclext g0} in
                                                  let {
                                                   c0 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_')
                                                    d1) Datatypes.Coq_nil}
                                                  in
                                                  (case DdT.dersrec_map_single f c0 of {
                                                    Datatypes.Coq_pair _ x -> x})
                                                    (let {x = \_ _ _ f0 x -> case GenT.coq_ForallT_map_rev f0 x of {
                                                                              Datatypes.Coq_pair _ x0 -> x0}} in
                                                     let {
                                                      acm2 = x __ __ __ (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                               (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) acm1}
                                                     in
                                                     let {
                                                      ns0 = LntT.nslclext g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                              (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)}
                                                     in
                                                     (case LntacsT.can_gen_swapR_def' ns0 of {
                                                       Datatypes.Coq_pair x0 _ -> x0}) acm2 g0 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                       (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1 _UU0394_' d1
                                                       swap0 __ __))}
                                               in
                                               Logic.eq_rect_r g0 _evar_0_ (Datatypes.app g0 Datatypes.Coq_nil)) k0) d0) _UU0394_ swap) _UU0393_0) pp0;
                                   Datatypes.Coq_inr h2 ->
                                    case h2 of {
                                     Specif.Coq_existT h3 _ ->
                                      let {
                                       h4 = List_lemmasT.cons_eq_appT2 Datatypes.Coq_nil h3 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_)
                                              d0) k0) (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) k2) LntT.Coq_bac)}
                                      in
                                      case h4 of {
                                       Datatypes.Coq_inl _ ->
                                        Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1) h3)
                                          (Logic.eq_rect_r Datatypes.Coq_nil
                                            (Logic.eq_rect_r (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r))
                                              (Logic.eq_rect_r k2 (\_ ->
                                                Logic.eq_rect_r LntT.Coq_bac
                                                  (Logic.eq_rect_r Datatypes.Coq_nil (DdT.Coq_derI
                                                    (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                      (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                    (Datatypes.app
                                                      (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                        Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                      (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) _UU0394_') LntT.Coq_bac) Datatypes.Coq_nil))
                                                    (unsafeCoerce rs0
                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                      (Datatypes.app
                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                          Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) _UU0394_') LntT.Coq_bac) Datatypes.Coq_nil))
                                                      (let {
                                                        _evar_0_ = let {
                                                                    _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                 Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) _UU0394_')
                                                                                 LntT.Coq_bac) Datatypes.Coq_nil)) g0 (WBox2Ls a d1 h1l h1r h2l h2r k1 _UU0394_')}
                                                                   in
                                                                   Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                     (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                       (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) _UU0394_') LntT.Coq_bac)
                                                                       Datatypes.Coq_nil))) _evar_0_
                                                                     (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1)
                                                                       d1) Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                       (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) _UU0394_') LntT.Coq_bac)
                                                                       Datatypes.Coq_nil))}
                                                       in
                                                       Logic.eq_rect
                                                         (Datatypes.app g0
                                                           (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                             Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) _UU0394_') LntT.Coq_bac) Datatypes.Coq_nil)))
                                                         _evar_0_
                                                         (Datatypes.app
                                                           (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                             Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                           (Datatypes.app h2l (Datatypes.Coq_cons (LntT.WBox a) h2r)) _UU0394_') LntT.Coq_bac) Datatypes.Coq_nil)))) drs1)
                                                    k0) d0) _UU0394_ swap) _UU0393_0) h3) pp0;
                                       Datatypes.Coq_inr h5 -> case h5 of {
                                                                Specif.Coq_existT _ _ -> Logic.coq_False_rect}}}}) ps0 acm0 drs0 sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) k0))) ps0 __);
                           BBox2Ls a d1 h1l h1r h2l h2r k1 k2 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1)
                              d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons
                                (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil))
                                (Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r))
                                  k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (\acm1 drs1 _ ->
                                  let {
                                   h1 = List_lemmasT.cons_eq_appT2 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                          (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil) pp0 (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) k0) (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r)
                                          k1) d1)}
                                  in
                                  case h1 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r (Datatypes.app h1l h1r)
                                        (Logic.eq_rect_r k1 (\swap0 ->
                                          Logic.eq_rect_r d1
                                            (Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                              (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil)
                                              (let {
                                                _evar_0_ = DdT.Coq_derI
                                                 (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                   (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                 (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d1)
                                                   (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2)
                                                   LntT.Coq_fwd) Datatypes.Coq_nil)))
                                                 (unsafeCoerce rs0
                                                   (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                     (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                   (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d1)
                                                     (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r))
                                                     k2) LntT.Coq_fwd) Datatypes.Coq_nil)))
                                                   (LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                     (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_') d1) Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) _UU0394_') d1) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                     (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd) Datatypes.Coq_nil)) g0
                                                     (BBox2Ls a d1 h1l h1r h2l h2r _UU0394_' k2)))
                                                 (let {f = LntT.nslclext g0} in
                                                  let {
                                                   c0 = Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) _UU0394_')
                                                    d1) Datatypes.Coq_nil}
                                                  in
                                                  (case DdT.dersrec_map_single f c0 of {
                                                    Datatypes.Coq_pair _ x -> x})
                                                    (let {x = \_ _ _ f0 x -> case GenT.coq_ForallT_map_rev f0 x of {
                                                                              Datatypes.Coq_pair _ x0 -> x0}} in
                                                     let {
                                                      acm2 = x __ __ __ (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                               (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) acm1}
                                                     in
                                                     let {
                                                      ns0 = LntT.nslclext g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                              (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil)}
                                                     in
                                                     (case LntacsT.can_gen_swapR_def' ns0 of {
                                                       Datatypes.Coq_pair x0 _ -> x0}) acm2 g0 Datatypes.Coq_nil (Datatypes.Coq_pair
                                                       (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1 _UU0394_' d1
                                                       swap0 __ __))}
                                               in
                                               Logic.eq_rect_r g0 _evar_0_ (Datatypes.app g0 Datatypes.Coq_nil)) k0) d0) _UU0394_ swap) _UU0393_0) pp0;
                                   Datatypes.Coq_inr h2 ->
                                    case h2 of {
                                     Specif.Coq_existT h3 _ ->
                                      let {
                                       h4 = List_lemmasT.cons_eq_appT2 Datatypes.Coq_nil h3 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_)
                                              d0) k0) (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) k2) LntT.Coq_fwd)}
                                      in
                                      case h4 of {
                                       Datatypes.Coq_inl _ ->
                                        Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1) h3)
                                          (Logic.eq_rect_r Datatypes.Coq_nil
                                            (Logic.eq_rect_r (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r))
                                              (Logic.eq_rect_r k2 (\_ ->
                                                Logic.eq_rect_r LntT.Coq_fwd
                                                  (Logic.eq_rect_r Datatypes.Coq_nil (DdT.Coq_derI
                                                    (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                      (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                    (Datatypes.app
                                                      (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                        Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                      (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) _UU0394_') LntT.Coq_fwd) Datatypes.Coq_nil))
                                                    (unsafeCoerce rs0
                                                      (List.map (LntT.nslclext g0) (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                                      (Datatypes.app
                                                        (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                          Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                        (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) _UU0394_') LntT.Coq_fwd) Datatypes.Coq_nil))
                                                      (let {
                                                        _evar_0_ = let {
                                                                    _evar_0_ = LntT.coq_NSlclctxt' (Datatypes.Coq_cons (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair (Datatypes.app h1l (Datatypes.Coq_cons a h1r)) k1) d1)
                                                                                 Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1) (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                                                 (Datatypes.Coq_pair (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) _UU0394_')
                                                                                 LntT.Coq_fwd) Datatypes.Coq_nil)) g0 (BBox2Ls a d1 h1l h1r h2l h2r k1 _UU0394_')}
                                                                   in
                                                                   Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                                     (Datatypes.app Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                       (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) _UU0394_') LntT.Coq_fwd)
                                                                       Datatypes.Coq_nil))) _evar_0_
                                                                     (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1)
                                                                       d1) Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                                       (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) _UU0394_') LntT.Coq_fwd)
                                                                       Datatypes.Coq_nil))}
                                                       in
                                                       Logic.eq_rect
                                                         (Datatypes.app g0
                                                           (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                             Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                             (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) _UU0394_') LntT.Coq_fwd) Datatypes.Coq_nil)))
                                                         _evar_0_
                                                         (Datatypes.app
                                                           (Datatypes.app g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app h1l h1r) k1) d1)
                                                             Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                           (Datatypes.app h2l (Datatypes.Coq_cons (LntT.BBox a) h2r)) _UU0394_') LntT.Coq_fwd) Datatypes.Coq_nil)))) drs1)
                                                    k0) d0) _UU0394_ swap) _UU0393_0) h3) pp0;
                                       Datatypes.Coq_inr h5 -> case h5 of {
                                                                Specif.Coq_existT _ _ -> Logic.coq_False_rect}}}}) ps0 acm0 drs0 sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) k0))) ps0 __)}) __ __) c sppc0) g1}})
                 seq0 __) ps drs acm)) concl) ps __ sppc)}) __ __) __ nsr rs g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ __ __

