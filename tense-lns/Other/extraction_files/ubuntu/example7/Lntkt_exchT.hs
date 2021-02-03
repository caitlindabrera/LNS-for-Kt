{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Lntkt_exchT where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified List_lemmasT
import qualified Logic
import qualified Specif
import qualified DdT
import qualified Gen
import qualified GenT
import qualified Gen_seq
import qualified Gen_tacs
import qualified LntT
import qualified LntacsT
import qualified Lntb1LT
import qualified Lntb2LT
import qualified LntbRT
import qualified LntlsT
import qualified LntrsT

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

data EW_rule v =
   EW (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) LntT.Coq_dir

gen_swapR_step_EW_lc :: (Datatypes.Coq_list
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir))) -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir)) -> a2 -> (DdT.Coq_dersrec
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir)) a3 ()) -> (GenT.ForallT
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                        (LntacsT.Coq_can_gen_swapR a1 a3)) -> (Gen.Coq_rsub
                        (Datatypes.Coq_list
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir)))
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir)) a2 a3) -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) -> (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) ->
                        LntT.Coq_dir -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                        (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                        (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1))
                        -> DdT.Coq_derrec
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir)) a3 ()
gen_swapR_step_EW_lc ps concl nsr drs acm rs g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LntT.NSlclctxt ps0 c g0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LntT.nslclext g0) ps0) (\_ ->
         Logic.eq_rect (LntT.nslclext g0 c) (\sppc0 x x0 x1 x2 x3 x4 x5 x6 x7 _ _ ->
           LntacsT.can_gen_swapR_imp_rev (LntT.nslclext g0 c)
             (\g1 k0 seq0 _UU0393_0 _UU0394_ _UU0394_' d0 swap _ _ ->
             Logic.eq_rect (List.map (LntT.nslclext g0) ps0) (\drs0 acm0 ->
               Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_0 _UU0394_) (\_ ->
                 let {
                  pp = List_lemmasT.app_eq_appT2 g0 c g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                         (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) k0)}
                 in
                 case pp of {
                  Specif.Coq_existT pp0 pp1 ->
                   case pp1 of {
                    Datatypes.Coq_inl _ ->
                     let {
                      pp2 = List_lemmasT.cons_eq_appT2 k0 pp0 c (Datatypes.Coq_pair
                              (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0)}
                     in
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                         Logic.eq_rect_r Datatypes.Coq_nil (\drs2 acm2 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair
                             (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) k0) (\sppc1 ->
                             let {drs3 = Logic.eq_rect (Datatypes.app g1 Datatypes.Coq_nil) drs2 g1}
                             in
                             let {acm3 = Logic.eq_rect (Datatypes.app g1 Datatypes.Coq_nil) acm2 g1}
                             in
                             (case sppc1 of {
                               EW h k1 d1 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons Datatypes.Coq_nil
                                  Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect_r _UU0393_0 (\_ ->
                                    Logic.eq_rect_r _UU0394_ (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect Datatypes.Coq_nil
                                          (Logic.eq_rect (Datatypes.Coq_cons Datatypes.Coq_nil
                                            Datatypes.Coq_nil) (\_ drs4 sppc2 ->
                                            Logic.eq_rect Datatypes.Coq_nil (\_ -> DdT.Coq_derI
                                              (List.map (LntT.nslclext g1) (Datatypes.Coq_cons
                                                Datatypes.Coq_nil Datatypes.Coq_nil))
                                              (Datatypes.app g1 (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                                                _UU0394_') d0) Datatypes.Coq_nil))
                                              (unsafeCoerce rs0
                                                (List.map (LntT.nslclext g1) (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil Datatypes.Coq_nil))
                                                (Datatypes.app g1 (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                                                  _UU0394_') d0) Datatypes.Coq_nil)) (LntT.NSlclctxt
                                                (Datatypes.Coq_cons Datatypes.Coq_nil
                                                Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                                                _UU0394_') d0) Datatypes.Coq_nil) g1 (EW _UU0393_0
                                                _UU0394_' d0))) drs4) k0 sppc2) ps0 acm3 drs3 sppc1)
                                          k0) d1) k1) h __ __ __) ps0 __)}) __ __) c sppc0) pp0 drs1
                           acm1) g0 acm0 drs0;
                      Datatypes.Coq_inr pp3 ->
                       case pp3 of {
                        Specif.Coq_existT pp4 _ ->
                         Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair
                             (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) pp4) (\_ acm2 ->
                             Logic.eq_rect_r (Datatypes.app pp4 c) (DdT.Coq_derI
                               (List.map
                                 (LntT.nslclext
                                   (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                     (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4))) ps0)
                               (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                 (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) (Datatypes.app pp4 c)))
                               (unsafeCoerce rs0
                                 (List.map
                                   (LntT.nslclext
                                     (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                       (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4))) ps0)
                                 (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                   (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0)
                                   (Datatypes.app pp4 c)))
                                 (let {
                                   _evar_0_ = let {
                                               _evar_0_ = LntT.coq_NSlclctxt' ps0 c
                                                            (Datatypes.app g1 (Datatypes.Coq_cons
                                                              (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                              _UU0393_0 _UU0394_') d0) pp4)) sppc0}
                                              in
                                              Logic.eq_rect_r
                                                (Datatypes.app
                                                  (Datatypes.app g1 (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                                                    _UU0394_') d0) pp4)) c) _evar_0_
                                                (Datatypes.app g1
                                                  (Datatypes.app (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                                                    _UU0394_') d0) pp4) c))}
                                  in
                                  Logic.eq_rect_r
                                    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                      (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4) c) _evar_0_
                                    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                    _UU0393_0 _UU0394_') d0) (Datatypes.app pp4 c))))
                               (let {
                                 cs = List.map
                                        (LntT.nslclext
                                          (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4))) ps0}
                                in
                                (case DdT.dersrec_forall cs of {
                                  Datatypes.Coq_pair _ x8 -> x8}) (\l h ->
                                  let {
                                   h0 = GenT.coq_InT_mapE
                                          (LntT.nslclext
                                            (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                              (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4))) ps0
                                          l h}
                                  in
                                  case h0 of {
                                   Specif.Coq_existT x8 h1 ->
                                    case h1 of {
                                     Datatypes.Coq_pair _ h2 ->
                                      Logic.eq_rect
                                        (LntT.nslclext
                                          (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4)) x8)
                                        (let {
                                          h3 = GenT.coq_InT_map
                                                 (LntT.nslclext
                                                   (Datatypes.app g1 (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                     _UU0393_0 _UU0394_) d0) pp4))) ps0 x8 h2}
                                         in
                                         let {
                                          acm3 = GenT.coq_ForallTD_forall
                                                   (List.map
                                                     (LntT.nslclext
                                                       (Datatypes.app g1 (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                         _UU0393_0 _UU0394_) d0) pp4))) ps0) acm2
                                                   (LntT.nslclext
                                                     (Datatypes.app g1 (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_) d0) pp4)) x8) h3}
                                         in
                                         let {
                                          acm4 = LntacsT.can_gen_swapR_imp
                                                   (LntT.nslclext
                                                     (Datatypes.app g1 (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_) d0) pp4)) x8) acm3 g1
                                                   (Datatypes.app pp4 x8) (Datatypes.Coq_pair
                                                   _UU0393_0 _UU0394_) _UU0393_0 _UU0394_ _UU0394_'
                                                   d0 swap}
                                         in
                                         let {
                                          _evar_0_ = Logic.eq_rect (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_') d0)
                                                       (Datatypes.app pp4 x8)) acm4
                                                       (Datatypes.app (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                         _UU0393_0 _UU0394_') d0) pp4) x8)}
                                         in
                                         Logic.eq_rect
                                           (Datatypes.app g1
                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_0 _UU0394_') d0) pp4) x8))
                                           _evar_0_
                                           (Datatypes.app
                                             (Datatypes.app g1 (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                                               _UU0394_') d0) pp4)) x8)) l}}))) k0) pp0 drs1 acm1) g0
                           acm0 drs0}};
                    Datatypes.Coq_inr _ ->
                     Logic.eq_rect_r (Datatypes.app g0 pp0)
                       (Logic.eq_rect_r
                         (Datatypes.app pp0 (Datatypes.Coq_cons (Datatypes.Coq_pair
                           (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) k0)) (\sppc1 ->
                         (case sppc1 of {
                           EW h k1 d1 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons Datatypes.Coq_nil Datatypes.Coq_nil)
                              (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                (Datatypes.Coq_pair h k1) d1) Datatypes.Coq_nil)
                                (Logic.eq_rect (Datatypes.Coq_cons Datatypes.Coq_nil
                                  Datatypes.Coq_nil) (\_ drs1 _ ->
                                  let {
                                   h2 = List_lemmasT.cons_eq_appT2 Datatypes.Coq_nil pp0
                                          (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                          _UU0393_0 _UU0394_) d0) k0) (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair h k1) d1)}
                                  in
                                  case h2 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r h
                                        (Logic.eq_rect_r k1 (\_ ->
                                          Logic.eq_rect_r d1
                                            (Logic.eq_rect_r Datatypes.Coq_nil
                                              (Logic.eq_rect_r g0 (DdT.Coq_derI
                                                (List.map (LntT.nslclext g0) (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil Datatypes.Coq_nil))
                                                (Datatypes.app g0 (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair (Datatypes.Coq_pair h
                                                  _UU0394_') d1) Datatypes.Coq_nil))
                                                (unsafeCoerce rs0
                                                  (List.map (LntT.nslclext g0) (Datatypes.Coq_cons
                                                    Datatypes.Coq_nil Datatypes.Coq_nil))
                                                  (Datatypes.app g0 (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair h
                                                    _UU0394_') d1) Datatypes.Coq_nil))
                                                  (LntT.NSlclctxt (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil Datatypes.Coq_nil)
                                                  (Datatypes.Coq_cons (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair h _UU0394_') d1)
                                                  Datatypes.Coq_nil) g0 (EW h _UU0394_' d1))) drs1)
                                                (Datatypes.app g0 Datatypes.Coq_nil)) k0) d0)
                                          _UU0394_ swap) _UU0393_0) pp0;
                                   Datatypes.Coq_inr h3 ->
                                    case h3 of {
                                     Specif.Coq_existT _ _ -> Logic.coq_False_rect}}) ps0 acm0 drs0
                                  sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                  (Datatypes.Coq_pair _UU0393_0 _UU0394_) d0) k0))) ps0 __)}) __ __)
                         c sppc0) g1}}) seq0 __) ps drs acm) x x0 x1 x2 x3 x4 x5 x6 x7) concl) ps __
         sppc)}) __ __) __ nsr rs g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ __ __

gen_swapL_step_EW_lc :: (Datatypes.Coq_list
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir))) -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir)) -> a2 -> (DdT.Coq_dersrec
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir)) a3 ()) -> (GenT.ForallT
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                        (LntacsT.Coq_can_gen_swapL a1 a3)) -> (Gen.Coq_rsub
                        (Datatypes.Coq_list
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir)))
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir)) a2 a3) -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) -> (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) ->
                        LntT.Coq_dir -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                        (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                        (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1))
                        -> DdT.Coq_derrec
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                        LntT.Coq_dir)) a3 ()
gen_swapL_step_EW_lc ps concl nsr drs acm rs g k seq d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LntT.NSlclctxt ps0 c g0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LntT.nslclext g0) ps0) (\_ ->
         Logic.eq_rect (LntT.nslclext g0 c) (\sppc0 x x0 x1 x2 x3 x4 x5 x6 x7 _ _ ->
           LntacsT.can_gen_swapL_imp_rev (LntT.nslclext g0 c)
             (\g1 k0 seq0 _UU0393_ _UU0394_0 _UU0393_' d0 swap _ _ ->
             Logic.eq_rect (List.map (LntT.nslclext g0) ps0) (\drs0 acm0 ->
               Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_ _UU0394_0) (\_ ->
                 let {
                  pp = List_lemmasT.app_eq_appT2 g0 c g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                         (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) k0)}
                 in
                 case pp of {
                  Specif.Coq_existT pp0 pp1 ->
                   case pp1 of {
                    Datatypes.Coq_inl _ ->
                     let {
                      pp2 = List_lemmasT.cons_eq_appT2 k0 pp0 c (Datatypes.Coq_pair
                              (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0)}
                     in
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                         Logic.eq_rect_r Datatypes.Coq_nil (\drs2 acm2 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair
                             (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) k0) (\sppc1 ->
                             let {drs3 = Logic.eq_rect (Datatypes.app g1 Datatypes.Coq_nil) drs2 g1}
                             in
                             let {acm3 = Logic.eq_rect (Datatypes.app g1 Datatypes.Coq_nil) acm2 g1}
                             in
                             (case sppc1 of {
                               EW h k1 d1 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons Datatypes.Coq_nil
                                  Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect_r _UU0393_ (\_ ->
                                    Logic.eq_rect_r _UU0394_0 (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect Datatypes.Coq_nil
                                          (Logic.eq_rect (Datatypes.Coq_cons Datatypes.Coq_nil
                                            Datatypes.Coq_nil) (\_ drs4 sppc2 ->
                                            Logic.eq_rect Datatypes.Coq_nil (\_ -> DdT.Coq_derI
                                              (List.map (LntT.nslclext g1) (Datatypes.Coq_cons
                                                Datatypes.Coq_nil Datatypes.Coq_nil))
                                              (Datatypes.app g1 (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_'
                                                _UU0394_0) d0) Datatypes.Coq_nil))
                                              (unsafeCoerce rs0
                                                (List.map (LntT.nslclext g1) (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil Datatypes.Coq_nil))
                                                (Datatypes.app g1 (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_'
                                                  _UU0394_0) d0) Datatypes.Coq_nil)) (LntT.NSlclctxt
                                                (Datatypes.Coq_cons Datatypes.Coq_nil
                                                Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_'
                                                _UU0394_0) d0) Datatypes.Coq_nil) g1 (EW _UU0393_'
                                                _UU0394_0 d0))) drs4) k0 sppc2) ps0 acm3 drs3 sppc1)
                                          k0) d1) k1) h __ __ __) ps0 __)}) __ __) c sppc0) pp0 drs1
                           acm1) g0 acm0 drs0;
                      Datatypes.Coq_inr pp3 ->
                       case pp3 of {
                        Specif.Coq_existT pp4 _ ->
                         Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons (Datatypes.Coq_pair
                             (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) pp4) (\_ acm2 ->
                             Logic.eq_rect_r (Datatypes.app pp4 c) (DdT.Coq_derI
                               (List.map
                                 (LntT.nslclext
                                   (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                     (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4))) ps0)
                               (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                 (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) (Datatypes.app pp4 c)))
                               (unsafeCoerce rs0
                                 (List.map
                                   (LntT.nslclext
                                     (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                       (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4))) ps0)
                                 (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                   (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0)
                                   (Datatypes.app pp4 c)))
                                 (let {
                                   _evar_0_ = let {
                                               _evar_0_ = LntT.coq_NSlclctxt' ps0 c
                                                            (Datatypes.app g1 (Datatypes.Coq_cons
                                                              (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                              _UU0393_' _UU0394_0) d0) pp4)) sppc0}
                                              in
                                              Logic.eq_rect_r
                                                (Datatypes.app
                                                  (Datatypes.app g1 (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_'
                                                    _UU0394_0) d0) pp4)) c) _evar_0_
                                                (Datatypes.app g1
                                                  (Datatypes.app (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_'
                                                    _UU0394_0) d0) pp4) c))}
                                  in
                                  Logic.eq_rect_r
                                    (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                      (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4) c) _evar_0_
                                    (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                    _UU0393_' _UU0394_0) d0) (Datatypes.app pp4 c))))
                               (let {
                                 cs = List.map
                                        (LntT.nslclext
                                          (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4))) ps0}
                                in
                                (case DdT.dersrec_forall cs of {
                                  Datatypes.Coq_pair _ x8 -> x8}) (\l h ->
                                  let {
                                   h0 = GenT.coq_InT_mapE
                                          (LntT.nslclext
                                            (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                              (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4))) ps0
                                          l h}
                                  in
                                  case h0 of {
                                   Specif.Coq_existT x8 h1 ->
                                    case h1 of {
                                     Datatypes.Coq_pair _ h2 ->
                                      Logic.eq_rect
                                        (LntT.nslclext
                                          (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4)) x8)
                                        (let {
                                          h3 = GenT.coq_InT_map
                                                 (LntT.nslclext
                                                   (Datatypes.app g1 (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                                                     _UU0394_0) d0) pp4))) ps0 x8 h2}
                                         in
                                         let {
                                          acm3 = GenT.coq_ForallTD_forall
                                                   (List.map
                                                     (LntT.nslclext
                                                       (Datatypes.app g1 (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                         _UU0393_ _UU0394_0) d0) pp4))) ps0) acm2
                                                   (LntT.nslclext
                                                     (Datatypes.app g1 (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                       _UU0393_ _UU0394_0) d0) pp4)) x8) h3}
                                         in
                                         let {
                                          acm4 = LntacsT.can_gen_swapL_imp
                                                   (LntT.nslclext
                                                     (Datatypes.app g1 (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                       _UU0393_ _UU0394_0) d0) pp4)) x8) acm3 g1
                                                   (Datatypes.app pp4 x8) (Datatypes.Coq_pair
                                                   _UU0393_ _UU0394_0) _UU0393_ _UU0394_0 _UU0393_'
                                                   d0 swap}
                                         in
                                         let {
                                          _evar_0_ = Logic.eq_rect (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                       _UU0393_' _UU0394_0) d0)
                                                       (Datatypes.app pp4 x8)) acm4
                                                       (Datatypes.app (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair (Datatypes.Coq_pair
                                                         _UU0393_' _UU0394_0) d0) pp4) x8)}
                                         in
                                         Logic.eq_rect
                                           (Datatypes.app g1
                                             (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_' _UU0394_0) d0) pp4) x8))
                                           _evar_0_
                                           (Datatypes.app
                                             (Datatypes.app g1 (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_'
                                               _UU0394_0) d0) pp4)) x8)) l}}))) k0) pp0 drs1 acm1) g0
                           acm0 drs0}};
                    Datatypes.Coq_inr _ ->
                     Logic.eq_rect_r (Datatypes.app g0 pp0)
                       (Logic.eq_rect_r
                         (Datatypes.app pp0 (Datatypes.Coq_cons (Datatypes.Coq_pair
                           (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) k0)) (\sppc1 ->
                         (case sppc1 of {
                           EW h k1 d1 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons Datatypes.Coq_nil Datatypes.Coq_nil)
                              (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons (Datatypes.Coq_pair
                                (Datatypes.Coq_pair h k1) d1) Datatypes.Coq_nil)
                                (Logic.eq_rect (Datatypes.Coq_cons Datatypes.Coq_nil
                                  Datatypes.Coq_nil) (\_ drs1 _ ->
                                  let {
                                   h2 = List_lemmasT.cons_eq_appT2 Datatypes.Coq_nil pp0
                                          (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                          _UU0393_ _UU0394_0) d0) k0) (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair h k1) d1)}
                                  in
                                  case h2 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r h (\_ ->
                                        Logic.eq_rect_r k1
                                          (Logic.eq_rect_r d1
                                            (Logic.eq_rect_r Datatypes.Coq_nil
                                              (Logic.eq_rect_r g0 (DdT.Coq_derI
                                                (List.map (LntT.nslclext g0) (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil Datatypes.Coq_nil))
                                                (Datatypes.app g0 (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_'
                                                  k1) d1) Datatypes.Coq_nil))
                                                (unsafeCoerce rs0
                                                  (List.map (LntT.nslclext g0) (Datatypes.Coq_cons
                                                    Datatypes.Coq_nil Datatypes.Coq_nil))
                                                  (Datatypes.app g0 (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_'
                                                    k1) d1) Datatypes.Coq_nil)) (LntT.NSlclctxt
                                                  (Datatypes.Coq_cons Datatypes.Coq_nil
                                                  Datatypes.Coq_nil) (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_'
                                                  k1) d1) Datatypes.Coq_nil) g0 (EW _UU0393_' k1
                                                  d1))) drs1) (Datatypes.app g0 Datatypes.Coq_nil))
                                              k0) d0) _UU0394_0) _UU0393_ swap) pp0;
                                   Datatypes.Coq_inr h3 ->
                                    case h3 of {
                                     Specif.Coq_existT _ _ -> Logic.coq_False_rect}}) ps0 acm0 drs0
                                  sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons (Datatypes.Coq_pair
                                  (Datatypes.Coq_pair _UU0393_ _UU0394_0) d0) k0))) ps0 __)}) __ __)
                         c sppc0) g1}}) seq0 __) ps drs acm) x x0 x1 x2 x3 x4 x5 x6 x7) concl) ps __
         sppc)}) __ __) __ nsr rs g k seq d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ __ __

data LNSKt_rules v =
   Coq_b2r (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (LntT.Coq_nslclrule
                                                                                           (Datatypes.Coq_prod
                                                                                           (Gen_tacs.Coq_rel
                                                                                           (Datatypes.Coq_list
                                                                                           (LntT.PropF
                                                                                           v)))
                                                                                           LntT.Coq_dir)
                                                                                           (LntbRT.Coq_b2rrules
                                                                                           v))
 | Coq_b1r (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (LntT.Coq_nslclrule
                                                                                           (Datatypes.Coq_prod
                                                                                           (Gen_tacs.Coq_rel
                                                                                           (Datatypes.Coq_list
                                                                                           (LntT.PropF
                                                                                           v)))
                                                                                           LntT.Coq_dir)
                                                                                           (LntbRT.Coq_b1rrules
                                                                                           v))
 | Coq_b2l (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (LntT.Coq_nslclrule
                                                                                           (Datatypes.Coq_prod
                                                                                           (Gen_tacs.Coq_rel
                                                                                           (Datatypes.Coq_list
                                                                                           (LntT.PropF
                                                                                           v)))
                                                                                           LntT.Coq_dir)
                                                                                           (Lntb2LT.Coq_b2lrules
                                                                                           v))
 | Coq_b1l (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (LntT.Coq_nslclrule
                                                                                           (Datatypes.Coq_prod
                                                                                           (Gen_tacs.Coq_rel
                                                                                           (Datatypes.Coq_list
                                                                                           (LntT.PropF
                                                                                           v)))
                                                                                           LntT.Coq_dir)
                                                                                           (Lntb1LT.Coq_b1lrules
                                                                                           v))
 | Coq_nEW (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (LntT.Coq_nslclrule
                                                                                           (Datatypes.Coq_prod
                                                                                           (Gen_tacs.Coq_rel
                                                                                           (Datatypes.Coq_list
                                                                                           (LntT.PropF
                                                                                           v)))
                                                                                           LntT.Coq_dir)
                                                                                           (EW_rule
                                                                                           v))
 | Coq_prop (Datatypes.Coq_list
            (Datatypes.Coq_list
            (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (LntT.Coq_nslcrule
                                                                                           (Gen_tacs.Coq_rel
                                                                                           (Datatypes.Coq_list
                                                                                           (LntT.PropF
                                                                                           v)))
                                                                                           (Gen_seq.Coq_seqrule
                                                                                           (LntT.PropF
                                                                                           v)
                                                                                           (LntT.Coq_princrule_pfc
                                                                                           v)))

coq_LNSKt_exchR :: (Datatypes.Coq_list
                   (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                   LntT.Coq_dir)) -> (DdT.Coq_derrec
                   (Datatypes.Coq_list
                   (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                   LntT.Coq_dir)) (LNSKt_rules a1) ()) -> (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                   (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) -> (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                   (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) -> (Datatypes.Coq_prod
                   (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) ->
                   LntT.Coq_dir -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                   (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                   (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> DdT.Coq_derrec
                   (Datatypes.Coq_list
                   (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                   LntT.Coq_dir)) (LNSKt_rules a1) ()
coq_LNSKt_exchR ns d g k seq d0 _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ =
  DdT.derrec_all_indT (\_ _ -> Logic.coq_False_rect) (\h1 h2 h3 h4 h5 ->
    (case h3 of {
      Coq_b2r ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b2r u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           LntbRT.gen_swapR_step_b2R_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x);
      Coq_b1r ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b1r u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           LntbRT.gen_swapR_step_b1R_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x);
      Coq_b2l ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b2l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Lntb2LT.gen_swapR_step_b2L_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x);
      Coq_b1l ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b1l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Lntb1LT.gen_swapR_step_b1L_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x);
      Coq_nEW ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_nEW u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           gen_swapR_step_EW_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x);
      Coq_prop ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_prop u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           LntrsT.gen_swapR_step_pr_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x)})
      __ __) ns d g k seq d0 _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ __ __

coq_LNSKt_exchL :: (Datatypes.Coq_list
                   (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                   LntT.Coq_dir)) -> (DdT.Coq_derrec
                   (Datatypes.Coq_list
                   (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                   LntT.Coq_dir)) (LNSKt_rules a1) ()) -> (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                   (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) -> (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                   (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) -> (Datatypes.Coq_prod
                   (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) ->
                   LntT.Coq_dir -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                   (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                   (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> DdT.Coq_derrec
                   (Datatypes.Coq_list
                   (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                   LntT.Coq_dir)) (LNSKt_rules a1) ()
coq_LNSKt_exchL ns d g k seq d0 _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ =
  DdT.derrec_all_indT (\_ _ -> Logic.coq_False_rect) (\h1 h2 h3 h4 h5 ->
    (case h3 of {
      Coq_b2r ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b2r u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           LntbRT.gen_swapL_step_b2R_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x);
      Coq_b1r ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b1r u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           LntbRT.gen_swapL_step_b1R_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x);
      Coq_b2l ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b2l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Lntb2LT.gen_swapL_step_b2L_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x);
      Coq_b1l ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b1l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Lntb1LT.gen_swapL_step_b1L_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x);
      Coq_nEW ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_nEW u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           gen_swapL_step_EW_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x);
      Coq_prop ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_prop u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           LntlsT.gen_swapL_step_pr_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)) c) ps __ x)})
      __ __) ns d g k seq d0 _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ __ __

