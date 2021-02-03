{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Rules_EW where

import qualified Prelude
import qualified Datatypes
import qualified LNS
import qualified List
import qualified List_lemmasT
import qualified Logic
import qualified Specif
import qualified DdT
import qualified Gen
import qualified GenT
import qualified Structural_cont
import qualified Structural_defs

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
   EW (Datatypes.Coq_list (LNS.PropF v)) (Datatypes.Coq_list (LNS.PropF v)) 
 LNS.Coq_dir

gen_swapL_step_EW_lc :: (Datatypes.Coq_list (LNS.LNS a1)) -> (LNS.LNS 
                        a1) -> a2 -> (DdT.Coq_pfs (LNS.LNS a1) a3) ->
                        (GenT.ForallT
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                        (Structural_defs.Coq_can_gen_swapL a1 a3)) ->
                        (Gen.Coq_rsub (Datatypes.Coq_list (LNS.LNS a1))
                        (LNS.LNS a1) a2 a3) -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir
                        -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) -> DdT.Coq_pf
                        (LNS.LNS a1) a3
gen_swapL_step_EW_lc ps concl nsr drs acm rs g k s d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LNS.NSlclctxt ps0 c g0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\_ ->
         Logic.eq_rect (LNS.nslclext g0 c)
           (\sppc0 x x0 x1 x2 x3 x4 x5 x6 x7 _ _ ->
           Structural_defs.can_gen_swapL_imp_rev (LNS.nslclext g0 c)
             (\g1 k0 s0 _UU0393_ _UU0394_0 _UU0393_' d0 swap _ _ ->
             Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\drs0 acm0 ->
               Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_ _UU0394_0) (\_ ->
                 let {
                  pp = List_lemmasT.app_eq_appT2 g0 c g1 (Datatypes.Coq_cons
                         (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                         _UU0394_0) d0) k0)}
                 in
                 case pp of {
                  Specif.Coq_existT pp0 pp1 ->
                   case pp1 of {
                    Datatypes.Coq_inl _ ->
                     let {
                      pp2 = List_lemmasT.cons_eq_appT2 k0 pp0 c
                              (Datatypes.Coq_pair (Datatypes.Coq_pair
                              _UU0393_ _UU0394_0) d0)}
                     in
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                         Logic.eq_rect_r Datatypes.Coq_nil (\drs2 acm2 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                             _UU0394_0) d0) k0) (\sppc1 ->
                             let {
                              drs3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       drs2 g1}
                             in
                             let {
                              acm3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       acm2 g1}
                             in
                             (case sppc1 of {
                               EW h k1 d1 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect_r _UU0393_ (\_ ->
                                    Logic.eq_rect_r _UU0394_0 (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect Datatypes.Coq_nil
                                          (Logic.eq_rect (Datatypes.Coq_cons
                                            Datatypes.Coq_nil
                                            Datatypes.Coq_nil)
                                            (\_ drs4 sppc2 ->
                                            Logic.eq_rect Datatypes.Coq_nil
                                              (\_ -> DdT.Coq_derI
                                              (List.map (LNS.nslclext g1)
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil))
                                              (Datatypes.app g1
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_'
                                                _UU0394_0) d0)
                                                Datatypes.Coq_nil))
                                              (unsafeCoerce rs0
                                                (List.map (LNS.nslclext g1)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g1
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_' _UU0394_0) d0)
                                                  Datatypes.Coq_nil))
                                                (LNS.NSlclctxt
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil)
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_'
                                                _UU0394_0) d0)
                                                Datatypes.Coq_nil) g1 (EW
                                                _UU0393_' _UU0394_0 d0)))
                                              drs4) k0 sppc2) ps0 acm3 drs3
                                            sppc1) k0) d1) k1) h __ __ __)
                                  ps0 __)}) __ __) c sppc0) pp0 drs1 acm1) g0
                         acm0 drs0;
                      Datatypes.Coq_inr pp3 ->
                       case pp3 of {
                        Specif.Coq_existT pp4 _ ->
                         Logic.eq_rect_r (Datatypes.app g1 pp0)
                           (\acm1 drs1 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                             _UU0394_0) d0) pp4) (\_ acm2 ->
                             Logic.eq_rect_r (Datatypes.app pp4 c)
                               (DdT.Coq_derI
                               (List.map
                                 (LNS.nslclext
                                   (Datatypes.app g1 (Datatypes.Coq_cons
                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                     _UU0393_' _UU0394_0) d0) pp4))) ps0)
                               (Datatypes.app g1 (Datatypes.Coq_cons
                                 (Datatypes.Coq_pair (Datatypes.Coq_pair
                                 _UU0393_' _UU0394_0) d0)
                                 (Datatypes.app pp4 c)))
                               (unsafeCoerce rs0
                                 (List.map
                                   (LNS.nslclext
                                     (Datatypes.app g1 (Datatypes.Coq_cons
                                       (Datatypes.Coq_pair
                                       (Datatypes.Coq_pair _UU0393_'
                                       _UU0394_0) d0) pp4))) ps0)
                                 (Datatypes.app g1 (Datatypes.Coq_cons
                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                   _UU0393_' _UU0394_0) d0)
                                   (Datatypes.app pp4 c)))
                                 (let {
                                   _evar_0_ = let {
                                               _evar_0_ = LNS.coq_NSlclctxt'
                                                            ps0 c
                                                            (Datatypes.app g1
                                                              (Datatypes.Coq_cons
                                                              (Datatypes.Coq_pair
                                                              (Datatypes.Coq_pair
                                                              _UU0393_'
                                                              _UU0394_0) d0)
                                                              pp4)) sppc0}
                                              in
                                              Logic.eq_rect_r
                                                (Datatypes.app
                                                  (Datatypes.app g1
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_' _UU0394_0) d0)
                                                    pp4)) c) _evar_0_
                                                (Datatypes.app g1
                                                  (Datatypes.app
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_' _UU0394_0) d0)
                                                    pp4) c))}
                                  in
                                  Logic.eq_rect_r
                                    (Datatypes.app (Datatypes.Coq_cons
                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                      _UU0393_' _UU0394_0) d0) pp4) c)
                                    _evar_0_ (Datatypes.Coq_cons
                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                    _UU0393_' _UU0394_0) d0)
                                    (Datatypes.app pp4 c))))
                               (let {
                                 cs = List.map
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_'
                                            _UU0394_0) d0) pp4))) ps0}
                                in
                                (case DdT.dersrec_forall cs of {
                                  Datatypes.Coq_pair _ x8 -> x8}) (\l h ->
                                  let {
                                   h0 = GenT.coq_InT_mapE
                                          (LNS.nslclext
                                            (Datatypes.app g1
                                              (Datatypes.Coq_cons
                                              (Datatypes.Coq_pair
                                              (Datatypes.Coq_pair _UU0393_'
                                              _UU0394_0) d0) pp4))) ps0 l h}
                                  in
                                  case h0 of {
                                   Specif.Coq_existT x8 h1 ->
                                    case h1 of {
                                     Datatypes.Coq_pair _ h2 ->
                                      Logic.eq_rect
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_'
                                            _UU0394_0) d0) pp4)) x8)
                                        (let {
                                          h3 = GenT.coq_InT_map
                                                 (LNS.nslclext
                                                   (Datatypes.app g1
                                                     (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair
                                                     (Datatypes.Coq_pair
                                                     _UU0393_ _UU0394_0) d0)
                                                     pp4))) ps0 x8 h2}
                                         in
                                         let {
                                          acm3 = GenT.coq_ForallTD_forall
                                                   (List.map
                                                     (LNS.nslclext
                                                       (Datatypes.app g1
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_ _UU0394_0)
                                                         d0) pp4))) ps0) acm2
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_ _UU0394_0)
                                                       d0) pp4)) x8) h3}
                                         in
                                         let {
                                          acm4 = Structural_defs.can_gen_swapL_imp
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_ _UU0394_0)
                                                       d0) pp4)) x8) acm3 g1
                                                   (Datatypes.app pp4 x8)
                                                   (Datatypes.Coq_pair
                                                   _UU0393_ _UU0394_0)
                                                   _UU0393_ _UU0394_0
                                                   _UU0393_' d0 swap}
                                         in
                                         let {
                                          _evar_0_ = Logic.eq_rect
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_' _UU0394_0)
                                                       d0)
                                                       (Datatypes.app pp4 x8))
                                                       acm4
                                                       (Datatypes.app
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_' _UU0394_0)
                                                         d0) pp4) x8)}
                                         in
                                         Logic.eq_rect
                                           (Datatypes.app g1
                                             (Datatypes.app
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_'
                                               _UU0394_0) d0) pp4) x8))
                                           _evar_0_
                                           (Datatypes.app
                                             (Datatypes.app g1
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_'
                                               _UU0394_0) d0) pp4)) x8)) l}})))
                               k0) pp0 drs1 acm1) g0 acm0 drs0}};
                    Datatypes.Coq_inr _ ->
                     Logic.eq_rect_r (Datatypes.app g0 pp0)
                       (Logic.eq_rect_r
                         (Datatypes.app pp0 (Datatypes.Coq_cons
                           (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                           _UU0394_0) d0) k0)) (\sppc1 ->
                         (case sppc1 of {
                           EW h k1 d1 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons
                              Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons
                                (Datatypes.Coq_pair (Datatypes.Coq_pair h k1)
                                d1) Datatypes.Coq_nil)
                                (Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil)
                                  (\_ drs1 _ ->
                                  let {
                                   h2 = List_lemmasT.cons_eq_appT2
                                          Datatypes.Coq_nil pp0
                                          (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair _UU0393_
                                          _UU0394_0) d0) k0)
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair h k1) d1)}
                                  in
                                  case h2 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r h (\_ ->
                                        Logic.eq_rect_r k1
                                          (Logic.eq_rect_r d1
                                            (Logic.eq_rect_r
                                              Datatypes.Coq_nil
                                              (Logic.eq_rect_r g0
                                                (DdT.Coq_derI
                                                (List.map (LNS.nslclext g0)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g0
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_' k1) d1)
                                                  Datatypes.Coq_nil))
                                                (unsafeCoerce rs0
                                                  (List.map (LNS.nslclext g0)
                                                    (Datatypes.Coq_cons
                                                    Datatypes.Coq_nil
                                                    Datatypes.Coq_nil))
                                                  (Datatypes.app g0
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_' k1) d1)
                                                    Datatypes.Coq_nil))
                                                  (LNS.NSlclctxt
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil)
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_' k1) d1)
                                                  Datatypes.Coq_nil) g0 (EW
                                                  _UU0393_' k1 d1))) drs1)
                                                (Datatypes.app g0
                                                  Datatypes.Coq_nil)) k0) d0)
                                          _UU0394_0) _UU0393_ swap) pp0;
                                   Datatypes.Coq_inr h3 ->
                                    case h3 of {
                                     Specif.Coq_existT _ _ ->
                                      Logic.coq_False_rect}}) ps0 acm0 drs0
                                  sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons
                                  (Datatypes.Coq_pair (Datatypes.Coq_pair
                                  _UU0393_ _UU0394_0) d0) k0))) ps0 __)}) __
                           __) c sppc0) g1}}) s0 __) ps drs acm) x x0 x1 x2
             x3 x4 x5 x6 x7) concl) ps __ sppc)}) __ __) __ nsr rs g k s d
    _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ __ __

gen_swapR_step_EW_lc :: (Datatypes.Coq_list (LNS.LNS a1)) -> (LNS.LNS 
                        a1) -> a2 -> (DdT.Coq_pfs (LNS.LNS a1) a3) ->
                        (GenT.ForallT
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                        (Structural_defs.Coq_can_gen_swapR a1 a3)) ->
                        (Gen.Coq_rsub (Datatypes.Coq_list (LNS.LNS a1))
                        (LNS.LNS a1) a2 a3) -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir
                        -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) -> DdT.Coq_pf
                        (LNS.LNS a1) a3
gen_swapR_step_EW_lc ps concl nsr drs acm rs g k s d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LNS.NSlclctxt ps0 c g0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\_ ->
         Logic.eq_rect (LNS.nslclext g0 c)
           (\sppc0 x x0 x1 x2 x3 x4 x5 x6 x7 _ _ ->
           Structural_defs.can_gen_swapR_imp_rev (LNS.nslclext g0 c)
             (\g1 k0 s0 _UU0393_0 _UU0394_ _UU0394_' d0 swap _ _ ->
             Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\drs0 acm0 ->
               Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_0 _UU0394_) (\_ ->
                 let {
                  pp = List_lemmasT.app_eq_appT2 g0 c g1 (Datatypes.Coq_cons
                         (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                         _UU0394_) d0) k0)}
                 in
                 case pp of {
                  Specif.Coq_existT pp0 pp1 ->
                   case pp1 of {
                    Datatypes.Coq_inl _ ->
                     let {
                      pp2 = List_lemmasT.cons_eq_appT2 k0 pp0 c
                              (Datatypes.Coq_pair (Datatypes.Coq_pair
                              _UU0393_0 _UU0394_) d0)}
                     in
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                         Logic.eq_rect_r Datatypes.Coq_nil (\drs2 acm2 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                             _UU0393_0 _UU0394_) d0) k0) (\sppc1 ->
                             let {
                              drs3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       drs2 g1}
                             in
                             let {
                              acm3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       acm2 g1}
                             in
                             (case sppc1 of {
                               EW h k1 d1 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect_r _UU0393_0 (\_ ->
                                    Logic.eq_rect_r _UU0394_ (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect Datatypes.Coq_nil
                                          (Logic.eq_rect (Datatypes.Coq_cons
                                            Datatypes.Coq_nil
                                            Datatypes.Coq_nil)
                                            (\_ drs4 sppc2 ->
                                            Logic.eq_rect Datatypes.Coq_nil
                                              (\_ -> DdT.Coq_derI
                                              (List.map (LNS.nslclext g1)
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil))
                                              (Datatypes.app g1
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_0
                                                _UU0394_') d0)
                                                Datatypes.Coq_nil))
                                              (unsafeCoerce rs0
                                                (List.map (LNS.nslclext g1)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g1
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_0 _UU0394_') d0)
                                                  Datatypes.Coq_nil))
                                                (LNS.NSlclctxt
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil)
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_0
                                                _UU0394_') d0)
                                                Datatypes.Coq_nil) g1 (EW
                                                _UU0393_0 _UU0394_' d0)))
                                              drs4) k0 sppc2) ps0 acm3 drs3
                                            sppc1) k0) d1) k1) h __ __ __)
                                  ps0 __)}) __ __) c sppc0) pp0 drs1 acm1) g0
                         acm0 drs0;
                      Datatypes.Coq_inr pp3 ->
                       case pp3 of {
                        Specif.Coq_existT pp4 _ ->
                         Logic.eq_rect_r (Datatypes.app g1 pp0)
                           (\acm1 drs1 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                             _UU0393_0 _UU0394_) d0) pp4) (\_ acm2 ->
                             Logic.eq_rect_r (Datatypes.app pp4 c)
                               (DdT.Coq_derI
                               (List.map
                                 (LNS.nslclext
                                   (Datatypes.app g1 (Datatypes.Coq_cons
                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                     _UU0393_0 _UU0394_') d0) pp4))) ps0)
                               (Datatypes.app g1 (Datatypes.Coq_cons
                                 (Datatypes.Coq_pair (Datatypes.Coq_pair
                                 _UU0393_0 _UU0394_') d0)
                                 (Datatypes.app pp4 c)))
                               (unsafeCoerce rs0
                                 (List.map
                                   (LNS.nslclext
                                     (Datatypes.app g1 (Datatypes.Coq_cons
                                       (Datatypes.Coq_pair
                                       (Datatypes.Coq_pair _UU0393_0
                                       _UU0394_') d0) pp4))) ps0)
                                 (Datatypes.app g1 (Datatypes.Coq_cons
                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                   _UU0393_0 _UU0394_') d0)
                                   (Datatypes.app pp4 c)))
                                 (let {
                                   _evar_0_ = let {
                                               _evar_0_ = LNS.coq_NSlclctxt'
                                                            ps0 c
                                                            (Datatypes.app g1
                                                              (Datatypes.Coq_cons
                                                              (Datatypes.Coq_pair
                                                              (Datatypes.Coq_pair
                                                              _UU0393_0
                                                              _UU0394_') d0)
                                                              pp4)) sppc0}
                                              in
                                              Logic.eq_rect_r
                                                (Datatypes.app
                                                  (Datatypes.app g1
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_0 _UU0394_') d0)
                                                    pp4)) c) _evar_0_
                                                (Datatypes.app g1
                                                  (Datatypes.app
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_0 _UU0394_') d0)
                                                    pp4) c))}
                                  in
                                  Logic.eq_rect_r
                                    (Datatypes.app (Datatypes.Coq_cons
                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                      _UU0393_0 _UU0394_') d0) pp4) c)
                                    _evar_0_ (Datatypes.Coq_cons
                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                    _UU0393_0 _UU0394_') d0)
                                    (Datatypes.app pp4 c))))
                               (let {
                                 cs = List.map
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_0
                                            _UU0394_') d0) pp4))) ps0}
                                in
                                (case DdT.dersrec_forall cs of {
                                  Datatypes.Coq_pair _ x8 -> x8}) (\l h ->
                                  let {
                                   h0 = GenT.coq_InT_mapE
                                          (LNS.nslclext
                                            (Datatypes.app g1
                                              (Datatypes.Coq_cons
                                              (Datatypes.Coq_pair
                                              (Datatypes.Coq_pair _UU0393_0
                                              _UU0394_') d0) pp4))) ps0 l h}
                                  in
                                  case h0 of {
                                   Specif.Coq_existT x8 h1 ->
                                    case h1 of {
                                     Datatypes.Coq_pair _ h2 ->
                                      Logic.eq_rect
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_0
                                            _UU0394_') d0) pp4)) x8)
                                        (let {
                                          h3 = GenT.coq_InT_map
                                                 (LNS.nslclext
                                                   (Datatypes.app g1
                                                     (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair
                                                     (Datatypes.Coq_pair
                                                     _UU0393_0 _UU0394_) d0)
                                                     pp4))) ps0 x8 h2}
                                         in
                                         let {
                                          acm3 = GenT.coq_ForallTD_forall
                                                   (List.map
                                                     (LNS.nslclext
                                                       (Datatypes.app g1
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_0 _UU0394_)
                                                         d0) pp4))) ps0) acm2
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_)
                                                       d0) pp4)) x8) h3}
                                         in
                                         let {
                                          acm4 = Structural_defs.can_gen_swapR_imp
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_)
                                                       d0) pp4)) x8) acm3 g1
                                                   (Datatypes.app pp4 x8)
                                                   (Datatypes.Coq_pair
                                                   _UU0393_0 _UU0394_)
                                                   _UU0393_0 _UU0394_
                                                   _UU0394_' d0 swap}
                                         in
                                         let {
                                          _evar_0_ = Logic.eq_rect
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_')
                                                       d0)
                                                       (Datatypes.app pp4 x8))
                                                       acm4
                                                       (Datatypes.app
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_0 _UU0394_')
                                                         d0) pp4) x8)}
                                         in
                                         Logic.eq_rect
                                           (Datatypes.app g1
                                             (Datatypes.app
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_0
                                               _UU0394_') d0) pp4) x8))
                                           _evar_0_
                                           (Datatypes.app
                                             (Datatypes.app g1
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_0
                                               _UU0394_') d0) pp4)) x8)) l}})))
                               k0) pp0 drs1 acm1) g0 acm0 drs0}};
                    Datatypes.Coq_inr _ ->
                     Logic.eq_rect_r (Datatypes.app g0 pp0)
                       (Logic.eq_rect_r
                         (Datatypes.app pp0 (Datatypes.Coq_cons
                           (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                           _UU0394_) d0) k0)) (\sppc1 ->
                         (case sppc1 of {
                           EW h k1 d1 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons
                              Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons
                                (Datatypes.Coq_pair (Datatypes.Coq_pair h k1)
                                d1) Datatypes.Coq_nil)
                                (Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil)
                                  (\_ drs1 _ ->
                                  let {
                                   h2 = List_lemmasT.cons_eq_appT2
                                          Datatypes.Coq_nil pp0
                                          (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair _UU0393_0
                                          _UU0394_) d0) k0)
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair h k1) d1)}
                                  in
                                  case h2 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r h
                                        (Logic.eq_rect_r k1 (\_ ->
                                          Logic.eq_rect_r d1
                                            (Logic.eq_rect_r
                                              Datatypes.Coq_nil
                                              (Logic.eq_rect_r g0
                                                (DdT.Coq_derI
                                                (List.map (LNS.nslclext g0)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g0
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair h
                                                  _UU0394_') d1)
                                                  Datatypes.Coq_nil))
                                                (unsafeCoerce rs0
                                                  (List.map (LNS.nslclext g0)
                                                    (Datatypes.Coq_cons
                                                    Datatypes.Coq_nil
                                                    Datatypes.Coq_nil))
                                                  (Datatypes.app g0
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair h
                                                    _UU0394_') d1)
                                                    Datatypes.Coq_nil))
                                                  (LNS.NSlclctxt
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil)
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair h
                                                  _UU0394_') d1)
                                                  Datatypes.Coq_nil) g0 (EW h
                                                  _UU0394_' d1))) drs1)
                                                (Datatypes.app g0
                                                  Datatypes.Coq_nil)) k0) d0)
                                          _UU0394_ swap) _UU0393_0) pp0;
                                   Datatypes.Coq_inr h3 ->
                                    case h3 of {
                                     Specif.Coq_existT _ _ ->
                                      Logic.coq_False_rect}}) ps0 acm0 drs0
                                  sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons
                                  (Datatypes.Coq_pair (Datatypes.Coq_pair
                                  _UU0393_0 _UU0394_) d0) k0))) ps0 __)}) __
                           __) c sppc0) g1}}) s0 __) ps drs acm) x x0 x1 x2
             x3 x4 x5 x6 x7) concl) ps __ sppc)}) __ __) __ nsr rs g k s d
    _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ __ __

gen_weakR_step_EW_lc :: (Datatypes.Coq_list (LNS.LNS a1)) -> (LNS.LNS 
                        a1) -> a2 -> (DdT.Coq_pfs (LNS.LNS a1) a3) ->
                        (GenT.ForallT
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                        (Structural_defs.Coq_can_gen_weakR a1 a3)) ->
                        (Gen.Coq_rsub (Datatypes.Coq_list (LNS.LNS a1))
                        (LNS.LNS a1) a2 a3) -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir
                        -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) -> DdT.Coq_pf
                        (LNS.LNS a1) a3
gen_weakR_step_EW_lc ps concl nsr drs acm rs g k s d _UU0393_ _UU0394_1 _UU0394_2 _UU0394_3 =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LNS.NSlclctxt ps0 c g0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\_ ->
         Logic.eq_rect (LNS.nslclext g0 c) (\sppc0 ->
           let {ns = LNS.nslclext g0 c} in
           (case Structural_defs.can_gen_weakR_def' ns of {
             Datatypes.Coq_pair _ x -> x})
             (\g1 k0 s0 _UU0393_0 _UU0394_ _UU0394_' d0 swap _ _ ->
             Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\drs0 acm0 ->
               Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_0 _UU0394_) (\_ ->
                 let {
                  pp = List_lemmasT.app_eq_appT2 g0 c g1 (Datatypes.Coq_cons
                         (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                         _UU0394_) d0) k0)}
                 in
                 case pp of {
                  Specif.Coq_existT pp0 pp1 ->
                   case pp1 of {
                    Datatypes.Coq_inl _ ->
                     let {
                      pp2 = List_lemmasT.cons_eq_appT2 k0 pp0 c
                              (Datatypes.Coq_pair (Datatypes.Coq_pair
                              _UU0393_0 _UU0394_) d0)}
                     in
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                         Logic.eq_rect_r Datatypes.Coq_nil (\drs2 acm2 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                             _UU0393_0 _UU0394_) d0) k0) (\sppc1 ->
                             let {
                              drs3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       drs2 g1}
                             in
                             let {
                              acm3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       acm2 g1}
                             in
                             (case sppc1 of {
                               EW h k1 d1 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect_r _UU0393_0 (\_ ->
                                    Logic.eq_rect_r _UU0394_ (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect Datatypes.Coq_nil
                                          (Logic.eq_rect (Datatypes.Coq_cons
                                            Datatypes.Coq_nil
                                            Datatypes.Coq_nil)
                                            (\_ drs4 sppc2 ->
                                            Logic.eq_rect Datatypes.Coq_nil
                                              (\_ -> DdT.Coq_derI
                                              (List.map (LNS.nslclext g1)
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil))
                                              (Datatypes.app g1
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_0
                                                _UU0394_') d0)
                                                Datatypes.Coq_nil))
                                              (unsafeCoerce rs0
                                                (List.map (LNS.nslclext g1)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g1
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_0 _UU0394_') d0)
                                                  Datatypes.Coq_nil))
                                                (LNS.NSlclctxt
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil)
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_0
                                                _UU0394_') d0)
                                                Datatypes.Coq_nil) g1 (EW
                                                _UU0393_0 _UU0394_' d0)))
                                              drs4) k0 sppc2) ps0 acm3 drs3
                                            sppc1) k0) d1) k1) h __ __ __)
                                  ps0 __)}) __ __) c sppc0) pp0 drs1 acm1) g0
                         acm0 drs0;
                      Datatypes.Coq_inr pp3 ->
                       case pp3 of {
                        Specif.Coq_existT pp4 _ ->
                         Logic.eq_rect_r (Datatypes.app g1 pp0)
                           (\acm1 drs1 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                             _UU0393_0 _UU0394_) d0) pp4) (\_ acm2 ->
                             Logic.eq_rect_r (Datatypes.app pp4 c)
                               (DdT.Coq_derI
                               (List.map
                                 (LNS.nslclext
                                   (Datatypes.app g1 (Datatypes.Coq_cons
                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                     _UU0393_0 _UU0394_') d0) pp4))) ps0)
                               (Datatypes.app g1 (Datatypes.Coq_cons
                                 (Datatypes.Coq_pair (Datatypes.Coq_pair
                                 _UU0393_0 _UU0394_') d0)
                                 (Datatypes.app pp4 c)))
                               (unsafeCoerce rs0
                                 (List.map
                                   (LNS.nslclext
                                     (Datatypes.app g1 (Datatypes.Coq_cons
                                       (Datatypes.Coq_pair
                                       (Datatypes.Coq_pair _UU0393_0
                                       _UU0394_') d0) pp4))) ps0)
                                 (Datatypes.app g1 (Datatypes.Coq_cons
                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                   _UU0393_0 _UU0394_') d0)
                                   (Datatypes.app pp4 c)))
                                 (let {
                                   _evar_0_ = let {
                                               _evar_0_ = LNS.coq_NSlclctxt'
                                                            ps0 c
                                                            (Datatypes.app g1
                                                              (Datatypes.Coq_cons
                                                              (Datatypes.Coq_pair
                                                              (Datatypes.Coq_pair
                                                              _UU0393_0
                                                              _UU0394_') d0)
                                                              pp4)) sppc0}
                                              in
                                              Logic.eq_rect_r
                                                (Datatypes.app
                                                  (Datatypes.app g1
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_0 _UU0394_') d0)
                                                    pp4)) c) _evar_0_
                                                (Datatypes.app g1
                                                  (Datatypes.app
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_0 _UU0394_') d0)
                                                    pp4) c))}
                                  in
                                  Logic.eq_rect_r
                                    (Datatypes.app (Datatypes.Coq_cons
                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                      _UU0393_0 _UU0394_') d0) pp4) c)
                                    _evar_0_ (Datatypes.Coq_cons
                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                    _UU0393_0 _UU0394_') d0)
                                    (Datatypes.app pp4 c))))
                               (let {
                                 cs = List.map
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_0
                                            _UU0394_') d0) pp4))) ps0}
                                in
                                (case DdT.dersrec_forall cs of {
                                  Datatypes.Coq_pair _ x -> x}) (\l h ->
                                  let {
                                   x = \_ _ f l0 y ->
                                    case GenT.coq_InT_map_iffT f l0 y of {
                                     Datatypes.Coq_pair x _ -> x}}
                                  in
                                  let {
                                   h0 = x __ __
                                          (LNS.nslclext
                                            (Datatypes.app g1
                                              (Datatypes.Coq_cons
                                              (Datatypes.Coq_pair
                                              (Datatypes.Coq_pair _UU0393_0
                                              _UU0394_') d0) pp4))) ps0 l h}
                                  in
                                  case h0 of {
                                   Specif.Coq_existT h3 h1 ->
                                    case h1 of {
                                     Datatypes.Coq_pair _ h2 ->
                                      Logic.eq_rect
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_0
                                            _UU0394_') d0) pp4)) h3)
                                        (let {
                                          x0 = \_ _ l0 ->
                                           case GenT.coq_ForallT_forall l0 of {
                                            Datatypes.Coq_pair x0 _ -> x0}}
                                         in
                                         let {
                                          acm3 = x0 __ __
                                                   (List.map
                                                     (LNS.nslclext
                                                       (Datatypes.app g1
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_0 _UU0394_)
                                                         d0) pp4))) ps0) acm2
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_)
                                                       d0) pp4)) h3)
                                                   (GenT.coq_InT_map
                                                     (LNS.nslclext
                                                       (Datatypes.app g1
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_0 _UU0394_)
                                                         d0) pp4))) ps0 h3
                                                     h2)}
                                         in
                                         let {
                                          acm4 = Structural_defs.can_gen_weakR_imp
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_)
                                                       d0) pp4)) h3) acm3 g1
                                                   (Datatypes.app pp4 h3)
                                                   (Datatypes.Coq_pair
                                                   _UU0393_0 _UU0394_)
                                                   _UU0393_0 _UU0394_
                                                   _UU0394_' d0 swap}
                                         in
                                         let {
                                          _evar_0_ = Logic.eq_rect
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_')
                                                       d0)
                                                       (Datatypes.app pp4 h3))
                                                       acm4
                                                       (Datatypes.app
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_0 _UU0394_')
                                                         d0) pp4) h3)}
                                         in
                                         Logic.eq_rect
                                           (Datatypes.app g1
                                             (Datatypes.app
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_0
                                               _UU0394_') d0) pp4) h3))
                                           _evar_0_
                                           (Datatypes.app
                                             (Datatypes.app g1
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_0
                                               _UU0394_') d0) pp4)) h3)) l}})))
                               k0) pp0 drs1 acm1) g0 acm0 drs0}};
                    Datatypes.Coq_inr _ ->
                     Logic.eq_rect_r (Datatypes.app g0 pp0)
                       (Logic.eq_rect_r
                         (Datatypes.app pp0 (Datatypes.Coq_cons
                           (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                           _UU0394_) d0) k0)) (\sppc1 ->
                         (case sppc1 of {
                           EW h k1 d1 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons
                              Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons
                                (Datatypes.Coq_pair (Datatypes.Coq_pair h k1)
                                d1) Datatypes.Coq_nil)
                                (Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil)
                                  (\_ drs1 _ ->
                                  let {
                                   h2 = List_lemmasT.cons_eq_appT2
                                          Datatypes.Coq_nil pp0
                                          (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair _UU0393_0
                                          _UU0394_) d0) k0)
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair h k1) d1)}
                                  in
                                  case h2 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r h
                                        (Logic.eq_rect_r k1 (\_ ->
                                          Logic.eq_rect_r d1
                                            (Logic.eq_rect_r
                                              Datatypes.Coq_nil
                                              (Logic.eq_rect_r g0
                                                (DdT.Coq_derI
                                                (List.map (LNS.nslclext g0)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g0
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair h
                                                  _UU0394_') d1)
                                                  Datatypes.Coq_nil))
                                                (unsafeCoerce rs0
                                                  (List.map (LNS.nslclext g0)
                                                    (Datatypes.Coq_cons
                                                    Datatypes.Coq_nil
                                                    Datatypes.Coq_nil))
                                                  (Datatypes.app g0
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair h
                                                    _UU0394_') d1)
                                                    Datatypes.Coq_nil))
                                                  (LNS.NSlclctxt
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil)
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair h
                                                  _UU0394_') d1)
                                                  Datatypes.Coq_nil) g0 (EW h
                                                  _UU0394_' d1))) drs1)
                                                (Datatypes.app g0
                                                  Datatypes.Coq_nil)) k0) d0)
                                          _UU0394_ swap) _UU0393_0) pp0;
                                   Datatypes.Coq_inr h3 ->
                                    case h3 of {
                                     Specif.Coq_existT _ _ ->
                                      Logic.coq_False_rect}}) ps0 acm0 drs0
                                  sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons
                                  (Datatypes.Coq_pair (Datatypes.Coq_pair
                                  _UU0393_0 _UU0394_) d0) k0))) ps0 __)}) __
                           __) c sppc0) g1}}) s0 __) ps drs acm)) concl) ps
         __ sppc)}) __ __) __ nsr rs g k s d _UU0393_ _UU0394_1 _UU0394_2
    _UU0394_3 __ __

gen_weakL_step_EW_lc :: (Datatypes.Coq_list (LNS.LNS a1)) -> (LNS.LNS 
                        a1) -> a2 -> (DdT.Coq_pfs (LNS.LNS a1) a3) ->
                        (GenT.ForallT
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                        (Structural_defs.Coq_can_gen_weakL a1 a3)) ->
                        (Gen.Coq_rsub (Datatypes.Coq_list (LNS.LNS a1))
                        (LNS.LNS a1) a2 a3) -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir
                        -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) ->
                        (Datatypes.Coq_list (LNS.PropF a1)) -> DdT.Coq_pf
                        (LNS.LNS a1) a3
gen_weakL_step_EW_lc ps concl nsr drs acm rs g k s d _UU0393_1 _UU0393_2 _UU0393_3 _UU0394_ =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LNS.NSlclctxt ps0 c g0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\_ ->
         Logic.eq_rect (LNS.nslclext g0 c) (\sppc0 ->
           let {ns = LNS.nslclext g0 c} in
           (case Structural_defs.can_gen_weakL_def' ns of {
             Datatypes.Coq_pair _ x -> x})
             (\g1 k0 s0 _UU0393_ _UU0394_0 _UU0393_' d0 swap _ _ ->
             Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\drs0 acm0 ->
               Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_ _UU0394_0) (\_ ->
                 let {
                  pp = List_lemmasT.app_eq_appT2 g0 c g1 (Datatypes.Coq_cons
                         (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                         _UU0394_0) d0) k0)}
                 in
                 case pp of {
                  Specif.Coq_existT pp0 pp1 ->
                   case pp1 of {
                    Datatypes.Coq_inl _ ->
                     let {
                      pp2 = List_lemmasT.cons_eq_appT2 k0 pp0 c
                              (Datatypes.Coq_pair (Datatypes.Coq_pair
                              _UU0393_ _UU0394_0) d0)}
                     in
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                         Logic.eq_rect_r Datatypes.Coq_nil (\drs2 acm2 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                             _UU0394_0) d0) k0) (\sppc1 ->
                             let {
                              drs3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       drs2 g1}
                             in
                             let {
                              acm3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       acm2 g1}
                             in
                             (case sppc1 of {
                               EW h k1 d1 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect_r _UU0393_ (\_ ->
                                    Logic.eq_rect_r _UU0394_0 (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect Datatypes.Coq_nil
                                          (Logic.eq_rect (Datatypes.Coq_cons
                                            Datatypes.Coq_nil
                                            Datatypes.Coq_nil)
                                            (\_ drs4 sppc2 ->
                                            Logic.eq_rect Datatypes.Coq_nil
                                              (\_ -> DdT.Coq_derI
                                              (List.map (LNS.nslclext g1)
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil))
                                              (Datatypes.app g1
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_'
                                                _UU0394_0) d0)
                                                Datatypes.Coq_nil))
                                              (unsafeCoerce rs0
                                                (List.map (LNS.nslclext g1)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g1
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_' _UU0394_0) d0)
                                                  Datatypes.Coq_nil))
                                                (LNS.NSlclctxt
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil)
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_'
                                                _UU0394_0) d0)
                                                Datatypes.Coq_nil) g1 (EW
                                                _UU0393_' _UU0394_0 d0)))
                                              drs4) k0 sppc2) ps0 acm3 drs3
                                            sppc1) k0) d1) k1) h __ __ __)
                                  ps0 __)}) __ __) c sppc0) pp0 drs1 acm1) g0
                         acm0 drs0;
                      Datatypes.Coq_inr pp3 ->
                       case pp3 of {
                        Specif.Coq_existT pp4 _ ->
                         Logic.eq_rect_r (Datatypes.app g1 pp0)
                           (\acm1 drs1 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                             _UU0394_0) d0) pp4) (\_ acm2 ->
                             Logic.eq_rect_r (Datatypes.app pp4 c)
                               (DdT.Coq_derI
                               (List.map
                                 (LNS.nslclext
                                   (Datatypes.app g1 (Datatypes.Coq_cons
                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                     _UU0393_' _UU0394_0) d0) pp4))) ps0)
                               (Datatypes.app g1 (Datatypes.Coq_cons
                                 (Datatypes.Coq_pair (Datatypes.Coq_pair
                                 _UU0393_' _UU0394_0) d0)
                                 (Datatypes.app pp4 c)))
                               (unsafeCoerce rs0
                                 (List.map
                                   (LNS.nslclext
                                     (Datatypes.app g1 (Datatypes.Coq_cons
                                       (Datatypes.Coq_pair
                                       (Datatypes.Coq_pair _UU0393_'
                                       _UU0394_0) d0) pp4))) ps0)
                                 (Datatypes.app g1 (Datatypes.Coq_cons
                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                   _UU0393_' _UU0394_0) d0)
                                   (Datatypes.app pp4 c)))
                                 (let {
                                   _evar_0_ = let {
                                               _evar_0_ = LNS.coq_NSlclctxt'
                                                            ps0 c
                                                            (Datatypes.app g1
                                                              (Datatypes.Coq_cons
                                                              (Datatypes.Coq_pair
                                                              (Datatypes.Coq_pair
                                                              _UU0393_'
                                                              _UU0394_0) d0)
                                                              pp4)) sppc0}
                                              in
                                              Logic.eq_rect_r
                                                (Datatypes.app
                                                  (Datatypes.app g1
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_' _UU0394_0) d0)
                                                    pp4)) c) _evar_0_
                                                (Datatypes.app g1
                                                  (Datatypes.app
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_' _UU0394_0) d0)
                                                    pp4) c))}
                                  in
                                  Logic.eq_rect_r
                                    (Datatypes.app (Datatypes.Coq_cons
                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                      _UU0393_' _UU0394_0) d0) pp4) c)
                                    _evar_0_ (Datatypes.Coq_cons
                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                    _UU0393_' _UU0394_0) d0)
                                    (Datatypes.app pp4 c))))
                               (let {
                                 cs = List.map
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_'
                                            _UU0394_0) d0) pp4))) ps0}
                                in
                                (case DdT.dersrec_forall cs of {
                                  Datatypes.Coq_pair _ x -> x}) (\l h ->
                                  let {
                                   x = \_ _ f l0 y ->
                                    case GenT.coq_InT_map_iffT f l0 y of {
                                     Datatypes.Coq_pair x _ -> x}}
                                  in
                                  let {
                                   h0 = x __ __
                                          (LNS.nslclext
                                            (Datatypes.app g1
                                              (Datatypes.Coq_cons
                                              (Datatypes.Coq_pair
                                              (Datatypes.Coq_pair _UU0393_'
                                              _UU0394_0) d0) pp4))) ps0 l h}
                                  in
                                  case h0 of {
                                   Specif.Coq_existT h3 h1 ->
                                    case h1 of {
                                     Datatypes.Coq_pair _ h2 ->
                                      Logic.eq_rect
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_'
                                            _UU0394_0) d0) pp4)) h3)
                                        (let {
                                          x0 = \_ _ l0 ->
                                           case GenT.coq_ForallT_forall l0 of {
                                            Datatypes.Coq_pair x0 _ -> x0}}
                                         in
                                         let {
                                          acm3 = x0 __ __
                                                   (List.map
                                                     (LNS.nslclext
                                                       (Datatypes.app g1
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_ _UU0394_0)
                                                         d0) pp4))) ps0) acm2
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_ _UU0394_0)
                                                       d0) pp4)) h3)
                                                   (GenT.coq_InT_map
                                                     (LNS.nslclext
                                                       (Datatypes.app g1
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_ _UU0394_0)
                                                         d0) pp4))) ps0 h3
                                                     h2)}
                                         in
                                         let {
                                          acm4 = Structural_defs.can_gen_weakL_imp
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_ _UU0394_0)
                                                       d0) pp4)) h3) acm3 g1
                                                   (Datatypes.app pp4 h3)
                                                   (Datatypes.Coq_pair
                                                   _UU0393_ _UU0394_0)
                                                   _UU0393_ _UU0394_0
                                                   _UU0393_' d0 swap}
                                         in
                                         let {
                                          _evar_0_ = Logic.eq_rect
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_' _UU0394_0)
                                                       d0)
                                                       (Datatypes.app pp4 h3))
                                                       acm4
                                                       (Datatypes.app
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_' _UU0394_0)
                                                         d0) pp4) h3)}
                                         in
                                         Logic.eq_rect
                                           (Datatypes.app g1
                                             (Datatypes.app
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_'
                                               _UU0394_0) d0) pp4) h3))
                                           _evar_0_
                                           (Datatypes.app
                                             (Datatypes.app g1
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_'
                                               _UU0394_0) d0) pp4)) h3)) l}})))
                               k0) pp0 drs1 acm1) g0 acm0 drs0}};
                    Datatypes.Coq_inr _ ->
                     Logic.eq_rect_r (Datatypes.app g0 pp0)
                       (Logic.eq_rect_r
                         (Datatypes.app pp0 (Datatypes.Coq_cons
                           (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                           _UU0394_0) d0) k0)) (\sppc1 ->
                         (case sppc1 of {
                           EW h k1 d1 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons
                              Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons
                                (Datatypes.Coq_pair (Datatypes.Coq_pair h k1)
                                d1) Datatypes.Coq_nil)
                                (Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil)
                                  (\_ drs1 _ ->
                                  let {
                                   h2 = List_lemmasT.cons_eq_appT2
                                          Datatypes.Coq_nil pp0
                                          (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair _UU0393_
                                          _UU0394_0) d0) k0)
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair h k1) d1)}
                                  in
                                  case h2 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r h (\_ ->
                                        Logic.eq_rect_r k1
                                          (Logic.eq_rect_r d1
                                            (Logic.eq_rect_r
                                              Datatypes.Coq_nil
                                              (Logic.eq_rect_r g0
                                                (DdT.Coq_derI
                                                (List.map (LNS.nslclext g0)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g0
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_' k1) d1)
                                                  Datatypes.Coq_nil))
                                                (unsafeCoerce rs0
                                                  (List.map (LNS.nslclext g0)
                                                    (Datatypes.Coq_cons
                                                    Datatypes.Coq_nil
                                                    Datatypes.Coq_nil))
                                                  (Datatypes.app g0
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_' k1) d1)
                                                    Datatypes.Coq_nil))
                                                  (LNS.NSlclctxt
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil)
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_' k1) d1)
                                                  Datatypes.Coq_nil) g0 (EW
                                                  _UU0393_' k1 d1))) drs1)
                                                (Datatypes.app g0
                                                  Datatypes.Coq_nil)) k0) d0)
                                          _UU0394_0) _UU0393_ swap) pp0;
                                   Datatypes.Coq_inr h3 ->
                                    case h3 of {
                                     Specif.Coq_existT _ _ ->
                                      Logic.coq_False_rect}}) ps0 acm0 drs0
                                  sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons
                                  (Datatypes.Coq_pair (Datatypes.Coq_pair
                                  _UU0393_ _UU0394_0) d0) k0))) ps0 __)}) __
                           __) c sppc0) g1}}) s0 __) ps drs acm)) concl) ps
         __ sppc)}) __ __) __ nsr rs g k s d _UU0393_1 _UU0393_2 _UU0393_3
    _UU0394_ __ __

gen_contR_gen_step_EW_lc :: (Datatypes.Coq_list (LNS.LNS a1)) -> (LNS.LNS 
                            a1) -> a2 -> (DdT.Coq_pfs (LNS.LNS a1) a3) ->
                            (GenT.ForallT
                            (Datatypes.Coq_list
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_list (LNS.PropF a1))
                            (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                            (Structural_defs.Coq_can_gen_contR_gen a1 a3)) ->
                            (Gen.Coq_rsub (Datatypes.Coq_list (LNS.LNS a1))
                            (LNS.LNS a1) a2 a3) -> (Datatypes.Coq_list
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
                            LNS.Coq_dir -> (Datatypes.Coq_list
                            (LNS.PropF a1)) -> (Datatypes.Coq_list
                            (LNS.PropF a1)) -> (Datatypes.Coq_list
                            (LNS.PropF a1)) -> (Datatypes.Coq_list
                            (LNS.PropF a1)) -> (LNS.PropF a1) ->
                            Datatypes.Coq_prod (DdT.Coq_pf (LNS.LNS a1) a3)
                            (DdT.Coq_pf (LNS.LNS a1) a3)
gen_contR_gen_step_EW_lc ps concl nsr drs acm rs g k s d _UU0393_ _UU0394_1 _UU0394_2 _UU0394_3 a =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LNS.NSlclctxt ps0 c g0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\_ ->
         Logic.eq_rect (LNS.nslclext g0 c) (\sppc0 ->
           let {ns = LNS.nslclext g0 c} in
           (case Structural_defs.can_gen_contR_gen_def' ns of {
             Datatypes.Coq_pair _ x -> x})
             (\g1 k0 s0 _UU0393_0 _UU0394_ _UU0394_' d0 swap _ _ ->
             Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\drs0 acm0 ->
               Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_0 _UU0394_) (\_ ->
                 let {
                  pp = List_lemmasT.app_eq_appT2 g0 c g1 (Datatypes.Coq_cons
                         (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                         _UU0394_) d0) k0)}
                 in
                 case pp of {
                  Specif.Coq_existT pp0 pp1 ->
                   case pp1 of {
                    Datatypes.Coq_inl _ ->
                     let {
                      pp2 = List_lemmasT.cons_eq_appT2 k0 pp0 c
                              (Datatypes.Coq_pair (Datatypes.Coq_pair
                              _UU0393_0 _UU0394_) d0)}
                     in
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                         Logic.eq_rect_r Datatypes.Coq_nil (\drs2 acm2 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                             _UU0393_0 _UU0394_) d0) k0) (\sppc1 ->
                             let {
                              drs3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       drs2 g1}
                             in
                             let {
                              acm3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       acm2 g1}
                             in
                             (case sppc1 of {
                               EW h k1 d1 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect_r _UU0393_0 (\_ ->
                                    Logic.eq_rect_r _UU0394_ (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect Datatypes.Coq_nil
                                          (Logic.eq_rect (Datatypes.Coq_cons
                                            Datatypes.Coq_nil
                                            Datatypes.Coq_nil)
                                            (\_ drs4 sppc2 ->
                                            Logic.eq_rect Datatypes.Coq_nil
                                              (\_ -> DdT.Coq_derI
                                              (List.map (LNS.nslclext g1)
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil))
                                              (Datatypes.app g1
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_0
                                                _UU0394_') d0)
                                                Datatypes.Coq_nil))
                                              (unsafeCoerce rs0
                                                (List.map (LNS.nslclext g1)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g1
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_0 _UU0394_') d0)
                                                  Datatypes.Coq_nil))
                                                (LNS.NSlclctxt
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil)
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_0
                                                _UU0394_') d0)
                                                Datatypes.Coq_nil) g1 (EW
                                                _UU0393_0 _UU0394_' d0)))
                                              drs4) k0 sppc2) ps0 acm3 drs3
                                            sppc1) k0) d1) k1) h __ __ __)
                                  ps0 __)}) __ __) c sppc0) pp0 drs1 acm1) g0
                         acm0 drs0;
                      Datatypes.Coq_inr pp3 ->
                       case pp3 of {
                        Specif.Coq_existT pp4 _ ->
                         Logic.eq_rect_r (Datatypes.app g1 pp0)
                           (\acm1 drs1 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair
                             _UU0393_0 _UU0394_) d0) pp4) (\_ acm2 ->
                             Logic.eq_rect_r (Datatypes.app pp4 c)
                               (DdT.Coq_derI
                               (List.map
                                 (LNS.nslclext
                                   (Datatypes.app g1 (Datatypes.Coq_cons
                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                     _UU0393_0 _UU0394_') d0) pp4))) ps0)
                               (Datatypes.app g1 (Datatypes.Coq_cons
                                 (Datatypes.Coq_pair (Datatypes.Coq_pair
                                 _UU0393_0 _UU0394_') d0)
                                 (Datatypes.app pp4 c)))
                               (unsafeCoerce rs0
                                 (List.map
                                   (LNS.nslclext
                                     (Datatypes.app g1 (Datatypes.Coq_cons
                                       (Datatypes.Coq_pair
                                       (Datatypes.Coq_pair _UU0393_0
                                       _UU0394_') d0) pp4))) ps0)
                                 (Datatypes.app g1 (Datatypes.Coq_cons
                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                   _UU0393_0 _UU0394_') d0)
                                   (Datatypes.app pp4 c)))
                                 (let {
                                   _evar_0_ = let {
                                               _evar_0_ = LNS.coq_NSlclctxt'
                                                            ps0 c
                                                            (Datatypes.app g1
                                                              (Datatypes.Coq_cons
                                                              (Datatypes.Coq_pair
                                                              (Datatypes.Coq_pair
                                                              _UU0393_0
                                                              _UU0394_') d0)
                                                              pp4)) sppc0}
                                              in
                                              Logic.eq_rect_r
                                                (Datatypes.app
                                                  (Datatypes.app g1
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_0 _UU0394_') d0)
                                                    pp4)) c) _evar_0_
                                                (Datatypes.app g1
                                                  (Datatypes.app
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_0 _UU0394_') d0)
                                                    pp4) c))}
                                  in
                                  Logic.eq_rect_r
                                    (Datatypes.app (Datatypes.Coq_cons
                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                      _UU0393_0 _UU0394_') d0) pp4) c)
                                    _evar_0_ (Datatypes.Coq_cons
                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                    _UU0393_0 _UU0394_') d0)
                                    (Datatypes.app pp4 c))))
                               (let {
                                 cs = List.map
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_0
                                            _UU0394_') d0) pp4))) ps0}
                                in
                                (case DdT.dersrec_forall cs of {
                                  Datatypes.Coq_pair _ x -> x}) (\l h ->
                                  let {
                                   x = \_ _ f l0 y ->
                                    case GenT.coq_InT_map_iffT f l0 y of {
                                     Datatypes.Coq_pair x _ -> x}}
                                  in
                                  let {
                                   h0 = x __ __
                                          (LNS.nslclext
                                            (Datatypes.app g1
                                              (Datatypes.Coq_cons
                                              (Datatypes.Coq_pair
                                              (Datatypes.Coq_pair _UU0393_0
                                              _UU0394_') d0) pp4))) ps0 l h}
                                  in
                                  case h0 of {
                                   Specif.Coq_existT h3 h1 ->
                                    case h1 of {
                                     Datatypes.Coq_pair _ h2 ->
                                      Logic.eq_rect
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_0
                                            _UU0394_') d0) pp4)) h3)
                                        (let {
                                          x0 = \_ _ l0 ->
                                           case GenT.coq_ForallT_forall l0 of {
                                            Datatypes.Coq_pair x0 _ -> x0}}
                                         in
                                         let {
                                          acm3 = x0 __ __
                                                   (List.map
                                                     (LNS.nslclext
                                                       (Datatypes.app g1
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_0 _UU0394_)
                                                         d0) pp4))) ps0) acm2
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_)
                                                       d0) pp4)) h3)
                                                   (GenT.coq_InT_map
                                                     (LNS.nslclext
                                                       (Datatypes.app g1
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_0 _UU0394_)
                                                         d0) pp4))) ps0 h3
                                                     h2)}
                                         in
                                         let {
                                          acm4 = Structural_cont.can_gen_contR_gen_imp
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_)
                                                       d0) pp4)) h3) acm3 g1
                                                   (Datatypes.app pp4 h3)
                                                   (Datatypes.Coq_pair
                                                   _UU0393_0 _UU0394_)
                                                   _UU0393_0 _UU0394_
                                                   _UU0394_' d0 swap}
                                         in
                                         let {
                                          _evar_0_ = Logic.eq_rect
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_')
                                                       d0)
                                                       (Datatypes.app pp4 h3))
                                                       acm4
                                                       (Datatypes.app
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_0 _UU0394_')
                                                         d0) pp4) h3)}
                                         in
                                         Logic.eq_rect
                                           (Datatypes.app g1
                                             (Datatypes.app
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_0
                                               _UU0394_') d0) pp4) h3))
                                           _evar_0_
                                           (Datatypes.app
                                             (Datatypes.app g1
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_0
                                               _UU0394_') d0) pp4)) h3)) l}})))
                               k0) pp0 drs1 acm1) g0 acm0 drs0}};
                    Datatypes.Coq_inr _ ->
                     Logic.eq_rect_r (Datatypes.app g0 pp0)
                       (Logic.eq_rect_r
                         (Datatypes.app pp0 (Datatypes.Coq_cons
                           (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                           _UU0394_) d0) k0)) (\sppc1 ->
                         (case sppc1 of {
                           EW h k1 d1 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons
                              Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons
                                (Datatypes.Coq_pair (Datatypes.Coq_pair h k1)
                                d1) Datatypes.Coq_nil)
                                (Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil)
                                  (\_ drs1 _ ->
                                  let {
                                   h2 = List_lemmasT.cons_eq_appT2
                                          Datatypes.Coq_nil pp0
                                          (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair _UU0393_0
                                          _UU0394_) d0) k0)
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair h k1) d1)}
                                  in
                                  case h2 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r h
                                        (Logic.eq_rect_r k1 (\_ ->
                                          Logic.eq_rect_r d1
                                            (Logic.eq_rect_r
                                              Datatypes.Coq_nil
                                              (Logic.eq_rect_r g0
                                                (DdT.Coq_derI
                                                (List.map (LNS.nslclext g0)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g0
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair h
                                                  _UU0394_') d1)
                                                  Datatypes.Coq_nil))
                                                (unsafeCoerce rs0
                                                  (List.map (LNS.nslclext g0)
                                                    (Datatypes.Coq_cons
                                                    Datatypes.Coq_nil
                                                    Datatypes.Coq_nil))
                                                  (Datatypes.app g0
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair h
                                                    _UU0394_') d1)
                                                    Datatypes.Coq_nil))
                                                  (LNS.NSlclctxt
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil)
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair h
                                                  _UU0394_') d1)
                                                  Datatypes.Coq_nil) g0 (EW h
                                                  _UU0394_' d1))) drs1)
                                                (Datatypes.app g0
                                                  Datatypes.Coq_nil)) k0) d0)
                                          _UU0394_ swap) _UU0393_0) pp0;
                                   Datatypes.Coq_inr h3 ->
                                    case h3 of {
                                     Specif.Coq_existT _ _ ->
                                      Logic.coq_False_rect}}) ps0 acm0 drs0
                                  sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons
                                  (Datatypes.Coq_pair (Datatypes.Coq_pair
                                  _UU0393_0 _UU0394_) d0) k0))) ps0 __)}) __
                           __) c sppc0) g1}}) s0 __) ps drs acm)) concl) ps
         __ sppc)}) __ __) __ nsr rs g k s d _UU0393_ _UU0394_1 _UU0394_2
    _UU0394_3 a __ __

gen_contL_gen_step_EW_lc :: (Datatypes.Coq_list (LNS.LNS a1)) -> (LNS.LNS 
                            a1) -> a2 -> (DdT.Coq_pfs (LNS.LNS a1) a3) ->
                            (GenT.ForallT
                            (Datatypes.Coq_list
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_list (LNS.PropF a1))
                            (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                            (Structural_defs.Coq_can_gen_contL_gen a1 a3)) ->
                            (Gen.Coq_rsub (Datatypes.Coq_list (LNS.LNS a1))
                            (LNS.LNS a1) a2 a3) -> (Datatypes.Coq_list
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
                            LNS.Coq_dir -> (Datatypes.Coq_list
                            (LNS.PropF a1)) -> (Datatypes.Coq_list
                            (LNS.PropF a1)) -> (Datatypes.Coq_list
                            (LNS.PropF a1)) -> (LNS.PropF a1) ->
                            (Datatypes.Coq_list (LNS.PropF a1)) ->
                            Datatypes.Coq_prod (DdT.Coq_pf (LNS.LNS a1) a3)
                            (DdT.Coq_pf (LNS.LNS a1) a3)
gen_contL_gen_step_EW_lc ps concl nsr drs acm rs g k s d _UU0393_1 _UU0393_2 _UU0393_3 a _UU0394_ =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LNS.NSlclctxt ps0 c g0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\_ ->
         Logic.eq_rect (LNS.nslclext g0 c) (\sppc0 ->
           let {ns = LNS.nslclext g0 c} in
           (case Structural_defs.can_gen_contL_gen_def' ns of {
             Datatypes.Coq_pair _ x -> x})
             (\g1 k0 s0 _UU0393_ _UU0394_0 _UU0393_' d0 swap _ _ ->
             Logic.eq_rect (List.map (LNS.nslclext g0) ps0) (\drs0 acm0 ->
               Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_ _UU0394_0) (\_ ->
                 let {
                  pp = List_lemmasT.app_eq_appT2 g0 c g1 (Datatypes.Coq_cons
                         (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                         _UU0394_0) d0) k0)}
                 in
                 case pp of {
                  Specif.Coq_existT pp0 pp1 ->
                   case pp1 of {
                    Datatypes.Coq_inl _ ->
                     let {
                      pp2 = List_lemmasT.cons_eq_appT2 k0 pp0 c
                              (Datatypes.Coq_pair (Datatypes.Coq_pair
                              _UU0393_ _UU0394_0) d0)}
                     in
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect_r (Datatypes.app g1 pp0) (\acm1 drs1 ->
                         Logic.eq_rect_r Datatypes.Coq_nil (\drs2 acm2 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                             _UU0394_0) d0) k0) (\sppc1 ->
                             let {
                              drs3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       drs2 g1}
                             in
                             let {
                              acm3 = Logic.eq_rect
                                       (Datatypes.app g1 Datatypes.Coq_nil)
                                       acm2 g1}
                             in
                             (case sppc1 of {
                               EW h k1 d1 -> (\_ _ ->
                                Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                                  Logic.eq_rect_r _UU0393_ (\_ ->
                                    Logic.eq_rect_r _UU0394_0 (\_ ->
                                      Logic.eq_rect_r d0 (\_ ->
                                        Logic.eq_rect Datatypes.Coq_nil
                                          (Logic.eq_rect (Datatypes.Coq_cons
                                            Datatypes.Coq_nil
                                            Datatypes.Coq_nil)
                                            (\_ drs4 sppc2 ->
                                            Logic.eq_rect Datatypes.Coq_nil
                                              (\_ -> DdT.Coq_derI
                                              (List.map (LNS.nslclext g1)
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil))
                                              (Datatypes.app g1
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_'
                                                _UU0394_0) d0)
                                                Datatypes.Coq_nil))
                                              (unsafeCoerce rs0
                                                (List.map (LNS.nslclext g1)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g1
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_' _UU0394_0) d0)
                                                  Datatypes.Coq_nil))
                                                (LNS.NSlclctxt
                                                (Datatypes.Coq_cons
                                                Datatypes.Coq_nil
                                                Datatypes.Coq_nil)
                                                (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair _UU0393_'
                                                _UU0394_0) d0)
                                                Datatypes.Coq_nil) g1 (EW
                                                _UU0393_' _UU0394_0 d0)))
                                              drs4) k0 sppc2) ps0 acm3 drs3
                                            sppc1) k0) d1) k1) h __ __ __)
                                  ps0 __)}) __ __) c sppc0) pp0 drs1 acm1) g0
                         acm0 drs0;
                      Datatypes.Coq_inr pp3 ->
                       case pp3 of {
                        Specif.Coq_existT pp4 _ ->
                         Logic.eq_rect_r (Datatypes.app g1 pp0)
                           (\acm1 drs1 ->
                           Logic.eq_rect_r (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                             _UU0394_0) d0) pp4) (\_ acm2 ->
                             Logic.eq_rect_r (Datatypes.app pp4 c)
                               (DdT.Coq_derI
                               (List.map
                                 (LNS.nslclext
                                   (Datatypes.app g1 (Datatypes.Coq_cons
                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                     _UU0393_' _UU0394_0) d0) pp4))) ps0)
                               (Datatypes.app g1 (Datatypes.Coq_cons
                                 (Datatypes.Coq_pair (Datatypes.Coq_pair
                                 _UU0393_' _UU0394_0) d0)
                                 (Datatypes.app pp4 c)))
                               (unsafeCoerce rs0
                                 (List.map
                                   (LNS.nslclext
                                     (Datatypes.app g1 (Datatypes.Coq_cons
                                       (Datatypes.Coq_pair
                                       (Datatypes.Coq_pair _UU0393_'
                                       _UU0394_0) d0) pp4))) ps0)
                                 (Datatypes.app g1 (Datatypes.Coq_cons
                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                   _UU0393_' _UU0394_0) d0)
                                   (Datatypes.app pp4 c)))
                                 (let {
                                   _evar_0_ = let {
                                               _evar_0_ = LNS.coq_NSlclctxt'
                                                            ps0 c
                                                            (Datatypes.app g1
                                                              (Datatypes.Coq_cons
                                                              (Datatypes.Coq_pair
                                                              (Datatypes.Coq_pair
                                                              _UU0393_'
                                                              _UU0394_0) d0)
                                                              pp4)) sppc0}
                                              in
                                              Logic.eq_rect_r
                                                (Datatypes.app
                                                  (Datatypes.app g1
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_' _UU0394_0) d0)
                                                    pp4)) c) _evar_0_
                                                (Datatypes.app g1
                                                  (Datatypes.app
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_' _UU0394_0) d0)
                                                    pp4) c))}
                                  in
                                  Logic.eq_rect_r
                                    (Datatypes.app (Datatypes.Coq_cons
                                      (Datatypes.Coq_pair (Datatypes.Coq_pair
                                      _UU0393_' _UU0394_0) d0) pp4) c)
                                    _evar_0_ (Datatypes.Coq_cons
                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                    _UU0393_' _UU0394_0) d0)
                                    (Datatypes.app pp4 c))))
                               (let {
                                 cs = List.map
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_'
                                            _UU0394_0) d0) pp4))) ps0}
                                in
                                (case DdT.dersrec_forall cs of {
                                  Datatypes.Coq_pair _ x -> x}) (\l h ->
                                  let {
                                   x = \_ _ f l0 y ->
                                    case GenT.coq_InT_map_iffT f l0 y of {
                                     Datatypes.Coq_pair x _ -> x}}
                                  in
                                  let {
                                   h0 = x __ __
                                          (LNS.nslclext
                                            (Datatypes.app g1
                                              (Datatypes.Coq_cons
                                              (Datatypes.Coq_pair
                                              (Datatypes.Coq_pair _UU0393_'
                                              _UU0394_0) d0) pp4))) ps0 l h}
                                  in
                                  case h0 of {
                                   Specif.Coq_existT h3 h1 ->
                                    case h1 of {
                                     Datatypes.Coq_pair _ h2 ->
                                      Logic.eq_rect
                                        (LNS.nslclext
                                          (Datatypes.app g1
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_'
                                            _UU0394_0) d0) pp4)) h3)
                                        (let {
                                          x0 = \_ _ l0 ->
                                           case GenT.coq_ForallT_forall l0 of {
                                            Datatypes.Coq_pair x0 _ -> x0}}
                                         in
                                         let {
                                          acm3 = x0 __ __
                                                   (List.map
                                                     (LNS.nslclext
                                                       (Datatypes.app g1
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_ _UU0394_0)
                                                         d0) pp4))) ps0) acm2
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_ _UU0394_0)
                                                       d0) pp4)) h3)
                                                   (GenT.coq_InT_map
                                                     (LNS.nslclext
                                                       (Datatypes.app g1
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_ _UU0394_0)
                                                         d0) pp4))) ps0 h3
                                                     h2)}
                                         in
                                         let {
                                          acm4 = Structural_cont.can_gen_contL_gen_imp
                                                   (LNS.nslclext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_ _UU0394_0)
                                                       d0) pp4)) h3) acm3 g1
                                                   (Datatypes.app pp4 h3)
                                                   (Datatypes.Coq_pair
                                                   _UU0393_ _UU0394_0)
                                                   _UU0393_ _UU0394_0
                                                   _UU0393_' d0 swap}
                                         in
                                         let {
                                          _evar_0_ = Logic.eq_rect
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_' _UU0394_0)
                                                       d0)
                                                       (Datatypes.app pp4 h3))
                                                       acm4
                                                       (Datatypes.app
                                                         (Datatypes.Coq_cons
                                                         (Datatypes.Coq_pair
                                                         (Datatypes.Coq_pair
                                                         _UU0393_' _UU0394_0)
                                                         d0) pp4) h3)}
                                         in
                                         Logic.eq_rect
                                           (Datatypes.app g1
                                             (Datatypes.app
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_'
                                               _UU0394_0) d0) pp4) h3))
                                           _evar_0_
                                           (Datatypes.app
                                             (Datatypes.app g1
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair _UU0393_'
                                               _UU0394_0) d0) pp4)) h3)) l}})))
                               k0) pp0 drs1 acm1) g0 acm0 drs0}};
                    Datatypes.Coq_inr _ ->
                     Logic.eq_rect_r (Datatypes.app g0 pp0)
                       (Logic.eq_rect_r
                         (Datatypes.app pp0 (Datatypes.Coq_cons
                           (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
                           _UU0394_0) d0) k0)) (\sppc1 ->
                         (case sppc1 of {
                           EW h k1 d1 -> (\_ _ ->
                            Logic.eq_rect (Datatypes.Coq_cons
                              Datatypes.Coq_nil Datatypes.Coq_nil) (\_ ->
                              Logic.eq_rect (Datatypes.Coq_cons
                                (Datatypes.Coq_pair (Datatypes.Coq_pair h k1)
                                d1) Datatypes.Coq_nil)
                                (Logic.eq_rect (Datatypes.Coq_cons
                                  Datatypes.Coq_nil Datatypes.Coq_nil)
                                  (\_ drs1 _ ->
                                  let {
                                   h2 = List_lemmasT.cons_eq_appT2
                                          Datatypes.Coq_nil pp0
                                          (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair _UU0393_
                                          _UU0394_0) d0) k0)
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair h k1) d1)}
                                  in
                                  case h2 of {
                                   Datatypes.Coq_inl _ ->
                                    Logic.eq_rect_r Datatypes.Coq_nil
                                      (Logic.eq_rect_r h (\_ ->
                                        Logic.eq_rect_r k1
                                          (Logic.eq_rect_r d1
                                            (Logic.eq_rect_r
                                              Datatypes.Coq_nil
                                              (Logic.eq_rect_r g0
                                                (DdT.Coq_derI
                                                (List.map (LNS.nslclext g0)
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil))
                                                (Datatypes.app g0
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_' k1) d1)
                                                  Datatypes.Coq_nil))
                                                (unsafeCoerce rs0
                                                  (List.map (LNS.nslclext g0)
                                                    (Datatypes.Coq_cons
                                                    Datatypes.Coq_nil
                                                    Datatypes.Coq_nil))
                                                  (Datatypes.app g0
                                                    (Datatypes.Coq_cons
                                                    (Datatypes.Coq_pair
                                                    (Datatypes.Coq_pair
                                                    _UU0393_' k1) d1)
                                                    Datatypes.Coq_nil))
                                                  (LNS.NSlclctxt
                                                  (Datatypes.Coq_cons
                                                  Datatypes.Coq_nil
                                                  Datatypes.Coq_nil)
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_' k1) d1)
                                                  Datatypes.Coq_nil) g0 (EW
                                                  _UU0393_' k1 d1))) drs1)
                                                (Datatypes.app g0
                                                  Datatypes.Coq_nil)) k0) d0)
                                          _UU0394_0) _UU0393_ swap) pp0;
                                   Datatypes.Coq_inr h3 ->
                                    case h3 of {
                                     Specif.Coq_existT _ _ ->
                                      Logic.coq_False_rect}}) ps0 acm0 drs0
                                  sppc1)
                                (Datatypes.app pp0 (Datatypes.Coq_cons
                                  (Datatypes.Coq_pair (Datatypes.Coq_pair
                                  _UU0393_ _UU0394_0) d0) k0))) ps0 __)}) __
                           __) c sppc0) g1}}) s0 __) ps drs acm)) concl) ps
         __ sppc)}) __ __) __ nsr rs g k s d _UU0393_1 _UU0393_2 _UU0393_3 a
    _UU0394_ __ __

