{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LntlsT where

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

gen_swapL_step_loe_lc :: (Datatypes.Coq_list
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)))
                         -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                         -> (LntT.Coq_rules_L_oeT (LntT.PropF a1) a2) -> a3
                         -> (DdT.Coq_dersrec
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                         a4 ()) -> (GenT.ForallT
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                         (LntacsT.Coq_can_gen_swapL a1 a4)) -> (Gen.Coq_rsub
                         (Datatypes.Coq_list
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)))
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                         a3 a4) -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                         -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                         -> (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LntT.PropF a1))
                         (Datatypes.Coq_list (LntT.PropF a1))) ->
                         LntT.Coq_dir -> (Datatypes.Coq_list (LntT.PropF a1))
                         -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                         (Datatypes.Coq_list (LntT.PropF a1)) ->
                         (Datatypes.Coq_list (LntT.PropF a1)) ->
                         (Datatypes.Coq_list (LntT.PropF a1)) ->
                         DdT.Coq_derrec
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                         a4 ()
gen_swapL_step_loe_lc ps concl loe nsr _ acm rs g k seq d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LntT.NSlcctxt ps0 c g0 d0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LntT.nslcext g0 d0) ps0) (\_ ->
         Logic.eq_rect (LntT.nslcext g0 d0 c) (\sppc0 ->
           let {ns = LntT.nslcext g0 d0 c} in
           (case LntacsT.can_gen_swapL_def' ns of {
             Datatypes.Coq_pair _ x -> x})
             (\g1 k0 seq0 _UU0393_ _UU0394_0 _UU0393_' d1 swap _ _ ->
             let {
              pp = List_lemmasT.partition_2_2T g0 Datatypes.Coq_nil g1 k0
                     (Datatypes.Coq_pair c d0) (Datatypes.Coq_pair seq0 d1)}
             in
             (case c of {
               Datatypes.Coq_pair l l0 -> (\sppc1 _ pp0 ->
                (case seq0 of {
                  Datatypes.Coq_pair seq1 seq2 -> (\pp1 _ ->
                   case pp1 of {
                    Datatypes.Coq_inl pp2 ->
                     case pp2 of {
                      Specif.Coq_existT pp3 _ ->
                       Logic.eq_rect (List.map (LntT.nslcext g0 d0) ps0)
                         (\acm0 ->
                         Logic.eq_rect_r
                           (Datatypes.app g1 (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair seq1
                             seq2) d1) pp3)) (\acm1 ->
                           Logic.eq_rect_r
                             (Datatypes.app pp3 (Datatypes.Coq_cons
                               (Datatypes.Coq_pair (Datatypes.Coq_pair l l0)
                               d0) Datatypes.Coq_nil))
                             (Logic.eq_rect_r _UU0393_ (\_ ->
                               Logic.eq_rect_r _UU0394_0
                                 (Logic.eq_rect_r _UU0393_ (\acm2 _ ->
                                   Logic.eq_rect_r _UU0394_0 (\acm3 _ ->
                                     DdT.Coq_derI
                                     (List.map
                                       (LntT.nslcext
                                         (Datatypes.app g1
                                           (Datatypes.Coq_cons
                                           (Datatypes.Coq_pair
                                           (Datatypes.Coq_pair _UU0393_'
                                           _UU0394_0) d1) pp3)) d0) ps0)
                                     (Datatypes.app g1 (Datatypes.Coq_cons
                                       (Datatypes.Coq_pair
                                       (Datatypes.Coq_pair _UU0393_'
                                       _UU0394_0) d1)
                                       (Datatypes.app pp3 (Datatypes.Coq_cons
                                         (Datatypes.Coq_pair
                                         (Datatypes.Coq_pair l l0) d0)
                                         Datatypes.Coq_nil))))
                                     (unsafeCoerce rs0
                                       (List.map
                                         (LntT.nslcext
                                           (Datatypes.app g1
                                             (Datatypes.Coq_cons
                                             (Datatypes.Coq_pair
                                             (Datatypes.Coq_pair _UU0393_'
                                             _UU0394_0) d1) pp3)) d0) ps0)
                                       (Datatypes.app g1 (Datatypes.Coq_cons
                                         (Datatypes.Coq_pair
                                         (Datatypes.Coq_pair _UU0393_'
                                         _UU0394_0) d1)
                                         (Datatypes.app pp3
                                           (Datatypes.Coq_cons
                                           (Datatypes.Coq_pair
                                           (Datatypes.Coq_pair l l0) d0)
                                           Datatypes.Coq_nil))))
                                       (let {
                                         _evar_0_ = let {
                                                     _evar_0_ = LntT.coq_NSlcctxt'
                                                                  ps0
                                                                  (Datatypes.Coq_pair
                                                                  l l0)
                                                                  (Datatypes.app
                                                                    g1
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    _UU0393_'
                                                                    _UU0394_0)
                                                                    d1) pp3))
                                                                  d0 sppc1}
                                                    in
                                                    Logic.eq_rect_r
                                                      (Datatypes.app
                                                        (Datatypes.app g1
                                                          (Datatypes.Coq_cons
                                                          (Datatypes.Coq_pair
                                                          (Datatypes.Coq_pair
                                                          _UU0393_'
                                                          _UU0394_0) d1)
                                                          pp3))
                                                        (Datatypes.Coq_cons
                                                        (Datatypes.Coq_pair
                                                        (Datatypes.Coq_pair l
                                                        l0) d0)
                                                        Datatypes.Coq_nil))
                                                      _evar_0_
                                                      (Datatypes.app g1
                                                        (Datatypes.app
                                                          (Datatypes.Coq_cons
                                                          (Datatypes.Coq_pair
                                                          (Datatypes.Coq_pair
                                                          _UU0393_'
                                                          _UU0394_0) d1) pp3)
                                                          (Datatypes.Coq_cons
                                                          (Datatypes.Coq_pair
                                                          (Datatypes.Coq_pair
                                                          l l0) d0)
                                                          Datatypes.Coq_nil)))}
                                        in
                                        Logic.eq_rect_r
                                          (Datatypes.app (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_'
                                            _UU0394_0) d1) pp3)
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair l l0) d0)
                                            Datatypes.Coq_nil)) _evar_0_
                                          (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair _UU0393_'
                                          _UU0394_0) d1)
                                          (Datatypes.app pp3
                                            (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair l l0) d0)
                                            Datatypes.Coq_nil)))))
                                     (let {
                                       cs = List.map
                                              (LntT.nslcext
                                                (Datatypes.app g1
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_' _UU0394_0) d1)
                                                  pp3)) d0) ps0}
                                      in
                                      (case DdT.dersrec_forall cs of {
                                        Datatypes.Coq_pair _ x -> x})
                                        (\q qin ->
                                        let {
                                         x = \_ _ f l1 y ->
                                          case GenT.coq_InT_map_iffT f l1 y of {
                                           Datatypes.Coq_pair x _ -> x}}
                                        in
                                        let {
                                         qin0 = x __ __
                                                  (LntT.nslcext
                                                    (Datatypes.app g1
                                                      (Datatypes.Coq_cons
                                                      (Datatypes.Coq_pair
                                                      (Datatypes.Coq_pair
                                                      _UU0393_' _UU0394_0)
                                                      d1) pp3)) d0) ps0 q qin}
                                        in
                                        case qin0 of {
                                         Specif.Coq_existT x0 x1 ->
                                          case x1 of {
                                           Datatypes.Coq_pair _ x2 ->
                                            Logic.eq_rect
                                              (LntT.nslcext
                                                (Datatypes.app g1
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_' _UU0394_0) d1)
                                                  pp3)) d0 x0)
                                              (let {
                                                x3 = \_ _ l1 ->
                                                 case GenT.coq_ForallT_forall
                                                        l1 of {
                                                  Datatypes.Coq_pair x3 _ ->
                                                   x3}}
                                               in
                                               let {
                                                acm4 = x3 __ __
                                                         (List.map
                                                           (LntT.nslcext
                                                             (Datatypes.app
                                                               g1
                                                               (Datatypes.Coq_cons
                                                               (Datatypes.Coq_pair
                                                               (Datatypes.Coq_pair
                                                               _UU0393_
                                                               _UU0394_0) d1)
                                                               pp3)) d0) ps0)
                                                         acm3
                                                         (LntT.nslcext
                                                           (Datatypes.app g1
                                                             (Datatypes.Coq_cons
                                                             (Datatypes.Coq_pair
                                                             (Datatypes.Coq_pair
                                                             _UU0393_
                                                             _UU0394_0) d1)
                                                             pp3)) d0 x0)
                                                         (GenT.coq_InT_map
                                                           (LntT.nslcext
                                                             (Datatypes.app
                                                               g1
                                                               (Datatypes.Coq_cons
                                                               (Datatypes.Coq_pair
                                                               (Datatypes.Coq_pair
                                                               _UU0393_
                                                               _UU0394_0) d1)
                                                               pp3)) d0) ps0
                                                           x0 x2)}
                                               in
                                               let {
                                                x4 = \_ ns0 ->
                                                 case LntacsT.can_gen_swapL_def'
                                                        ns0 of {
                                                  Datatypes.Coq_pair x4 _ ->
                                                   x4}}
                                               in
                                               let {
                                                acm5 = x4 __
                                                         (LntT.nslcext
                                                           (Datatypes.app g1
                                                             (Datatypes.Coq_cons
                                                             (Datatypes.Coq_pair
                                                             (Datatypes.Coq_pair
                                                             _UU0393_
                                                             _UU0394_0) d1)
                                                             pp3)) d0 x0)
                                                         acm4 g1
                                                         (Datatypes.app pp3
                                                           (Datatypes.Coq_cons
                                                           (Datatypes.Coq_pair
                                                           x0 d0)
                                                           Datatypes.Coq_nil))
                                                         (Datatypes.Coq_pair
                                                         _UU0393_ _UU0394_0)
                                                         _UU0393_ _UU0394_0
                                                         _UU0393_' d1 swap __
                                                         __}
                                               in
                                               let {
                                                _evar_0_ = Logic.eq_rect
                                                             (Datatypes.Coq_cons
                                                             (Datatypes.Coq_pair
                                                             (Datatypes.Coq_pair
                                                             _UU0393_'
                                                             _UU0394_0) d1)
                                                             (Datatypes.app
                                                               pp3
                                                               (Datatypes.Coq_cons
                                                               (Datatypes.Coq_pair
                                                               x0 d0)
                                                               Datatypes.Coq_nil)))
                                                             acm5
                                                             (Datatypes.app
                                                               (Datatypes.Coq_cons
                                                               (Datatypes.Coq_pair
                                                               (Datatypes.Coq_pair
                                                               _UU0393_'
                                                               _UU0394_0) d1)
                                                               pp3)
                                                               (Datatypes.Coq_cons
                                                               (Datatypes.Coq_pair
                                                               x0 d0)
                                                               Datatypes.Coq_nil))}
                                               in
                                               Logic.eq_rect
                                                 (Datatypes.app g1
                                                   (Datatypes.app
                                                     (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair
                                                     (Datatypes.Coq_pair
                                                     _UU0393_' _UU0394_0) d1)
                                                     pp3) (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair x0
                                                     d0) Datatypes.Coq_nil)))
                                                 _evar_0_
                                                 (Datatypes.app
                                                   (Datatypes.app g1
                                                     (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair
                                                     (Datatypes.Coq_pair
                                                     _UU0393_' _UU0394_0) d1)
                                                     pp3))
                                                   (Datatypes.Coq_cons
                                                   (Datatypes.Coq_pair x0 d0)
                                                   Datatypes.Coq_nil))) q}})))
                                     seq2 acm2 __) seq1 acm1 __) seq2) seq1
                               __) k0) g0 acm0) ps acm};
                    Datatypes.Coq_inr pp2 ->
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect (List.map (LntT.nslcext g0 d0) ps0)
                         (\acm0 ->
                         Logic.eq_rect_r g0
                           (Logic.eq_rect Datatypes.Coq_nil
                             (Logic.eq_rect_r seq1 (\_ ->
                               Logic.eq_rect_r seq2 (\_ ->
                                 Logic.eq_rect_r d1
                                   (Logic.eq_rect_r _UU0393_ (\_ ->
                                     Logic.eq_rect_r _UU0394_0
                                       (Logic.eq_rect_r seq1 (\sppc2 _ ->
                                         Logic.eq_rect_r seq2 (\sppc3 _ ->
                                           Logic.eq_rect_r d1 (\acm1 _ ->
                                             Logic.eq_rect_r _UU0393_
                                               (\sppc4 _ _ ->
                                               Logic.eq_rect_r _UU0394_0
                                                 (\sppc5 _ _ ->
                                                 (case sppc5 of {
                                                   Gen_seq.Sctxt ps1 c0
                                                    _UU03a6_1 _UU03a6_2
                                                    _UU03a8_1 _UU03a8_2 pr ->
                                                    (\_ _ ->
                                                    Logic.eq_rect
                                                      (List.map
                                                        (Gen_seq.seqext
                                                          _UU03a6_1 _UU03a6_2
                                                          _UU03a8_1
                                                          _UU03a8_2) ps1)
                                                      (\_ ->
                                                      Logic.eq_rect
                                                        (Gen_seq.seqext
                                                          _UU03a6_1 _UU03a6_2
                                                          _UU03a8_1 _UU03a8_2
                                                          c0) (\pr0 ->
                                                        (case c0 of {
                                                          Datatypes.Coq_pair l1
                                                           l2 -> (\pr1 _ ->
                                                           Logic.eq_rect
                                                             (List.map
                                                               (Gen_seq.seqext
                                                                 _UU03a6_1
                                                                 _UU03a6_2
                                                                 _UU03a8_1
                                                                 _UU03a8_2)
                                                               ps1)
                                                             (\acm2 _ ->
                                                             Logic.eq_rect
                                                               (Datatypes.app
                                                                 _UU03a6_1
                                                                 (Datatypes.app
                                                                   l1
                                                                   _UU03a6_2))
                                                               (\swap0 _ _ ->
                                                               Logic.eq_rect
                                                                 (Datatypes.app
                                                                   _UU03a8_1
                                                                   (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2))
                                                                 (\_ _ ->
                                                                 (case swap0 of {
                                                                   SwappedT.Coq_swapped_I x
                                                                    y a b c1
                                                                    d2 ->
                                                                    (\_ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (\_ ->
                                                                    Logic.eq_rect_r
                                                                    _UU0393_'
                                                                    (\_ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    (let {
                                                                    h = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2)
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))}
                                                                    in
                                                                    case h of {
                                                                     Specif.Coq_existT h0
                                                                    h1 ->
                                                                    case h1 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    let {
                                                                    h2 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2) h0
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2)}
                                                                    in
                                                                    case h2 of {
                                                                     Specif.Coq_existT h3
                                                                    h4 ->
                                                                    case h4 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    let {
                                                                    h5 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    l1
                                                                    _UU03a6_2
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1 d2)}
                                                                    in
                                                                    case h5 of {
                                                                     Specif.Coq_existT h6
                                                                    h7 ->
                                                                    case h7 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    let {
                                                                    h8 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    c1 d2 h6
                                                                    _UU03a6_2}
                                                                    in
                                                                    case h8 of {
                                                                     Specif.Coq_existT h9
                                                                    h10 ->
                                                                    case h10 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (\acm3 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h0 h3)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h3 h6)
                                                                    (\_ _ pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h6 h9)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    (\acm4 _ _ ->
                                                                    let {
                                                                    qpr = 
                                                                    loe ps1
                                                                    h3 h6 l2
                                                                    pr2}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 _ _ ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h6 l2
                                                                    a
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr3)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm5 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm4
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm6 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm6 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2)))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    (Datatypes.app
                                                                    h9 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h9) d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h9)
                                                                    (Datatypes.app
                                                                    h0 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h9)
                                                                    h0) d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h9)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h9)
                                                                    h0) d2
                                                                    (let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h9)
                                                                    h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 h0))
                                                                    (SwappedT.swapped_simpleL
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 h9)
                                                                    (Datatypes.app
                                                                    l3 h9))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 h0))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h9)
                                                                    h0)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 h9))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h9)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h9)
                                                                    (Datatypes.app
                                                                    h0 d2)))
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    __ __)})
                                                                    x7 acm5)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h6)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h6)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2))))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h6 h9)
                                                                    (Datatypes.app
                                                                    h0 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    h0
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    h0
                                                                    Datatypes.Coq_nil))
                                                                    h3 pr2 __
                                                                    __;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 _ _ ->
                                                                    let {
                                                                    _evar_0_ = \pr4 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    (Datatypes.app
                                                                    h3 d2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    (Datatypes.app
                                                                    h3 d2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    (Datatypes.app
                                                                    h3 d2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h3 l2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr4)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm5 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm4
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm6 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm6 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    (Datatypes.app
                                                                    l3 d2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9)
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 d2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 d2))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 d2)))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    (Datatypes.app
                                                                    h9 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h9) d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h9 h0)
                                                                    (Datatypes.app
                                                                    l3 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h9 h0)
                                                                    l3) d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h9)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h9 h0)
                                                                    l3) d2
                                                                    (let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    Gen.arg1_cong_imp
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h9)
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 h9))
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 l3))
                                                                    (SwappedT.swapped_simpleR
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    (Datatypes.app
                                                                    h0 l3))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0 l3))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h9 h0)
                                                                    l3)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 h9))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h9)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h9 h0)
                                                                    (Datatypes.app
                                                                    l3 d2)))
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9)
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    (Datatypes.app
                                                                    l3 d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    __ __)})
                                                                    x7 acm5)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    (Datatypes.app
                                                                    h3 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    h3) d2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    h3) d2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    (Datatypes.app
                                                                    h3 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9) h0)
                                                                    (Datatypes.app
                                                                    h3 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9)
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h3 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h9)
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h3 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h3 d2))))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h3 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 h3)
                                                                    d2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    h3
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    h3
                                                                    Datatypes.Coq_nil)
                                                                    pr3) h6
                                                                    pr2 __ __})
                                                                    _UU03a6_2
                                                                    acm3 __
                                                                    __) c1)
                                                                    l1 __ __
                                                                    pr1) b)
                                                                    _UU03a6_1
                                                                    acm2 __
                                                                    __;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (\acm3 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h0 h3)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h3 h6)
                                                                    (\_ _ pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    c1 h9)
                                                                    (\pr3 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2)
                                                                    (let {
                                                                    qpr = 
                                                                    loe ps1
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1 h9) l2
                                                                    pr3}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\_ _ pr4 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    qpr0 = 
                                                                    loe ps1
                                                                    c1 h9 l2
                                                                    pr4}
                                                                    in
                                                                    case qpr0 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 _ _ ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h9 l2
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr5)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm4 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm5 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0) h9)
                                                                    _UU03a6_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0) h9)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))))
                                                                    c1 pr4 __
                                                                    __;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 _ _ ->
                                                                    let {
                                                                    _evar_0_ = \pr6 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 c1 l2
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr6)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm4 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm5 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    _UU03a6_2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h0)
                                                                    _UU03a6_2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    (Datatypes.app
                                                                    l3 h0)
                                                                    _UU03a6_2
                                                                    (Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    l3 h0)
                                                                    (Datatypes.app
                                                                    l3 h0)
                                                                    (SwappedT.swapped_simpleL
                                                                    h0 l3 l3)))
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    c1
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    c1
                                                                    Datatypes.Coq_nil)
                                                                    pr5) h9
                                                                    pr4 __ __}}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    h0
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    h0
                                                                    Datatypes.Coq_nil))
                                                                    h3 __ __
                                                                    pr3;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\_ _ pr4 ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 _ _ ->
                                                                    let {
                                                                    _evar_0_ = \pr6 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h3 l2
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr6)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm4 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm5 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h3
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0) h3)
                                                                    _UU03a6_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0) h3)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h3
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h3
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h3
                                                                    _UU03a6_2)))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h3
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 h3)
                                                                    _UU03a6_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    h3
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    h3
                                                                    Datatypes.Coq_nil)
                                                                    pr5) h9
                                                                    pr4 __ __)
                                                                    c1 __ __
                                                                    pr3}) d2)
                                                                    h6 pr2 __
                                                                    __) l1 __
                                                                    __ pr1) b)
                                                                    _UU03a6_1
                                                                    acm2 __
                                                                    __}};
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (\acm3 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h0 h3)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    l1 h6)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (\acm4 _ _ ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 l1 l2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr1)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm5 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm4
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm6 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm6 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2)))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2)))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h6)
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h6) c1)
                                                                    d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h0)
                                                                    l3)
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h0)
                                                                    l3) h6)
                                                                    d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h6) c1)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h0)
                                                                    l3) h6)
                                                                    d2
                                                                    (let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    Gen.arg1_cong_imp
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h6) c1)
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 c1)))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 h6)))
                                                                    (SwappedT.swapped_simpleR
                                                                    c1
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h6)
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 h6)))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3 h6)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h0)
                                                                    (Datatypes.app
                                                                    l3 h6))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h0)
                                                                    (Datatypes.app
                                                                    l3 h6))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h0)
                                                                    l3) h6)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 c1)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    (Datatypes.app
                                                                    h6 c1))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    (Datatypes.app
                                                                    h6 c1))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h6) c1)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h0)
                                                                    l3)
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    h6)
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0 l3)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2)))))
                                                                    __ __)})
                                                                    x7 acm5)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    l1)
                                                                    (Datatypes.app
                                                                    h6 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    l1)
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h6 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) h0)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h6 d2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h6 d2)))))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l1 h6)
                                                                    d2)}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l1 h6)
                                                                    d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    l1 h6))
                                                                    d2))
                                                                    _UU03a6_2
                                                                    acm3 __
                                                                    __) h3) b)
                                                                    _UU03a6_1
                                                                    acm2 __
                                                                    __}};
                                                                     Datatypes.Coq_inr _ ->
                                                                    let {
                                                                    h5 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    c1 d2 h3
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2)}
                                                                    in
                                                                    case h5 of {
                                                                     Specif.Coq_existT h6
                                                                    h7 ->
                                                                    case h7 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    let {
                                                                    h8 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    l1
                                                                    _UU03a6_2
                                                                    h6 d2}
                                                                    in
                                                                    case h8 of {
                                                                     Specif.Coq_existT h9
                                                                    h10 ->
                                                                    case h10 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (\acm3 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (\acm4 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h3 h6)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h6 h9)
                                                                    (\_ _ pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2)
                                                                    (let {
                                                                    qpr = 
                                                                    loe ps1
                                                                    h6 h9 l2
                                                                    pr2}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 _ _ ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h9 l2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr3)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm5 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm4
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm6 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm6 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3) l3)
                                                                    _UU03a6_2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 b)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 b) l3)
                                                                    _UU03a6_2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3) l3)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 b) l3)
                                                                    _UU03a6_2
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    h3 b) l3
                                                                    (Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    h3 b)
                                                                    (Datatypes.app
                                                                    h3 b)
                                                                    (SwappedT.swapped_simpleL
                                                                    b h3 h3))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 b)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    __ __)})
                                                                    x7 acm5)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    h9)
                                                                    _UU03a6_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    h9)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) b)
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    h3
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    h3
                                                                    Datatypes.Coq_nil))
                                                                    h6 pr2 __
                                                                    __;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 _ _ ->
                                                                    let {
                                                                    _evar_0_ = \pr4 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h6 l2
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr4)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm5 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm4
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm6 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm6 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3) l3)
                                                                    _UU03a6_2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3) b)
                                                                    _UU03a6_2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3) l3)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3) b)
                                                                    _UU03a6_2
                                                                    (let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3) b)
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3 b))
                                                                    (SwappedT.swapped_simpleL
                                                                    b
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    (Datatypes.app
                                                                    h3 l3))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3 b))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3) b)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h3 l3))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3) l3)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    __ __)})
                                                                    x7 acm5)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) h6)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) h6)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 h6)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    h6
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    h6
                                                                    Datatypes.Coq_nil)
                                                                    pr3) h9
                                                                    pr2 __ __})
                                                                    d2) l1 __
                                                                    __ pr1)
                                                                    c1) h0
                                                                    acm3 __
                                                                    __)
                                                                    _UU03a6_1
                                                                    acm2 __
                                                                    __;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (\acm3 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (\acm4 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h3 h6)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    l1 h9)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    (\acm5 _ _ ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 l1 l2
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr1)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm6 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm5
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm7 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm7 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3) l3)
                                                                    (Datatypes.app
                                                                    h9 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3) l3)
                                                                    h9) d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    h9)
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    h9) b)
                                                                    d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3) l3)
                                                                    h9)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    h9) b) d2
                                                                    (let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    h9) b)
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 b)))
                                                                    (SwappedT.swapped_simpleL
                                                                    b
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3 h9))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    h9))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 b)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    (Datatypes.app
                                                                    h9 b))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    (Datatypes.app
                                                                    h9 b))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    h9) b)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3 h9)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3 h9))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3 h9))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3) l3)
                                                                    h9)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    h9)
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 l3)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3) l3)
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b h3))
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    __ __)})
                                                                    x7 acm6)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) l1)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3) l1)
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a h3)
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2)))))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l1 h9)
                                                                    (Datatypes.app
                                                                    b d2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l1 h9)
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    l1 h9))
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _UU03a6_2
                                                                    acm4 __
                                                                    __) h6)
                                                                    c1) h0
                                                                    acm3 __
                                                                    __)
                                                                    _UU03a6_1
                                                                    acm2 __
                                                                    __}};
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a h0)
                                                                    (\acm3 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    b h3)
                                                                    (\acm4 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    c1 h6)
                                                                    (\acm5 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 l1 l2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr1)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm6 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h6)))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm5
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h6)))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h6)))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h6)))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h6)))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm7 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h6)))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm7 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h6)))
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h6)))
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h6))
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h6)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1) h6)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1) h6)
                                                                    l3)
                                                                    _UU03a6_2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b) h6)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b) h6)
                                                                    l3)
                                                                    _UU03a6_2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1) h6)
                                                                    l3)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b) h6)
                                                                    l3)
                                                                    _UU03a6_2
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1) h6)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b) h6)
                                                                    l3
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    (Datatypes.app
                                                                    c1 b) h6
                                                                    (Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    (SwappedT.swapped_simpleL
                                                                    b c1 c1)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b) h6)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1) h6)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h6)
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h6))
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h6)))
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    __ __)})
                                                                    x7 acm6)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6) l1)
                                                                    _UU03a6_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6) l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    h6)
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))))))
                                                                    d2) h3
                                                                    acm4 __
                                                                    __) h0
                                                                    acm3 __
                                                                    __)
                                                                    _UU03a6_1
                                                                    acm2 __
                                                                    __}}}};
                                                                     Datatypes.Coq_inr _ ->
                                                                    let {
                                                                    h2 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    l1
                                                                    _UU03a6_2
                                                                    h0
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))}
                                                                    in
                                                                    case h2 of {
                                                                     Specif.Coq_existT h3
                                                                    h4 ->
                                                                    case h4 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    let {
                                                                    h5 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2) h3
                                                                    _UU03a6_2}
                                                                    in
                                                                    case h5 of {
                                                                     Specif.Coq_existT h6
                                                                    h7 ->
                                                                    case h7 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h0 h3)
                                                                    (\_ _ pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h3 h6)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (\acm3 _ _ ->
                                                                    let {
                                                                    qpr = 
                                                                    loe ps1
                                                                    h0 h3 l2
                                                                    pr2}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 _ _ ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h3 l2
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr3)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h6 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm4 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm5 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    _UU03a6_1
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h6)
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h6)
                                                                    c1) d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 l3)
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 l3)
                                                                    h6) d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h6)
                                                                    c1)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 l3)
                                                                    h6) d2
                                                                    (let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    Gen.arg1_cong_imp
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h6)
                                                                    c1)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 c1))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    l3 h6))
                                                                    (SwappedT.swapped_simpleR
                                                                    c1
                                                                    (Datatypes.app
                                                                    l3 h6)
                                                                    (Datatypes.app
                                                                    l3 h6))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    l3 h6))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 l3)
                                                                    h6)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 c1))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h6)
                                                                    c1)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 l3)
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h6)
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1) h3)
                                                                    (Datatypes.app
                                                                    h6 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1) h3)
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    h6 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    h6 d2))))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h3 h6)
                                                                    d2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    _UU03a6_1
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    Datatypes.Coq_nil))
                                                                    h0 pr2 __
                                                                    __;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 _ _ ->
                                                                    let {
                                                                    _evar_0_ = \pr4 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h0 l2
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr4)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm4 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm5 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    d1
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    _UU03a6_1
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))
                                                                    l3
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h6 c1)
                                                                    d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 h6)
                                                                    d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    h6 c1)
                                                                    (Datatypes.app
                                                                    c1 h6) d2
                                                                    (Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    c1 h6)
                                                                    (Datatypes.app
                                                                    c1 h6)
                                                                    (SwappedT.swapped_simpleL
                                                                    h6 c1 c1)))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    c1 d2)))))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    h6 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    h0
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    h0
                                                                    Datatypes.Coq_nil)
                                                                    pr3) h3
                                                                    pr2 __ __})
                                                                    _UU03a6_2
                                                                    acm2 __
                                                                    __) b) l1
                                                                    __ __
                                                                    pr1) a;
                                                                     Datatypes.Coq_inr _ ->
                                                                    let {
                                                                    h8 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    c1 d2 h6
                                                                    _UU03a6_2}
                                                                    in
                                                                    case h8 of {
                                                                     Specif.Coq_existT h9
                                                                    h10 ->
                                                                    case h10 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h0 h3)
                                                                    (\_ _ pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    b h6)
                                                                    (\pr3 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h6 h9)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    (\acm3 _ _ ->
                                                                    let {
                                                                    qpr = 
                                                                    loe ps1
                                                                    h0
                                                                    (Datatypes.app
                                                                    b h6) l2
                                                                    pr3}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\_ _ pr4 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    qpr0 = 
                                                                    loe ps1 b
                                                                    h6 l2 pr4}
                                                                    in
                                                                    case qpr0 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 _ _ ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h6 l2
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr5)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm4 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm5 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h6)
                                                                    (Datatypes.app
                                                                    h9 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h6)
                                                                    (Datatypes.app
                                                                    h9 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9 d2)))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    h6
                                                                    (Datatypes.app
                                                                    h9 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h6 h9)
                                                                    d2)) b
                                                                    pr4 __ __;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 _ _ ->
                                                                    let {
                                                                    _evar_0_ = \pr6 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9) d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9)
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9) d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9)
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9) d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9)
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 b l2
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9) d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr6)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9) d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9) d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9) d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9) d2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm4 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm5 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9)
                                                                    (Datatypes.app
                                                                    l3 d2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    l3 d2)))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    l3 d2))
                                                                    _UU03a6_1
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l3 h9)
                                                                    d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    h9 l3)
                                                                    d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    l3 h9)
                                                                    (Datatypes.app
                                                                    h9 l3) d2
                                                                    (Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    h9 l3)
                                                                    (Datatypes.app
                                                                    h9 l3)
                                                                    (SwappedT.swapped_simpleL
                                                                    l3 h9 h9)))
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    l3 d2)))
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9)
                                                                    (Datatypes.app
                                                                    l3 d2)))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9)
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9) b)
                                                                    d2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9) b)
                                                                    d2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9)
                                                                    (Datatypes.app
                                                                    b d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9)
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9
                                                                    (Datatypes.app
                                                                    b d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    b
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    b
                                                                    Datatypes.Coq_nil)
                                                                    pr5) h6
                                                                    pr4 __ __}}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    _UU03a6_1
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    Datatypes.Coq_nil))
                                                                    h0 __ __
                                                                    pr3;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\_ _ pr4 ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 _ _ ->
                                                                    let {
                                                                    _evar_0_ = \pr6 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h0 l2
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr6)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm4 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm5 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9 d2)
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h9 d2))))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    (Datatypes.app
                                                                    h9 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    (Datatypes.app
                                                                    h9 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h9 d2)))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    (Datatypes.app
                                                                    h9 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    (Datatypes.app
                                                                    h9 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    h0
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    h0
                                                                    Datatypes.Coq_nil)
                                                                    pr5) h6
                                                                    pr4 __ __)
                                                                    b __ __
                                                                    pr3})
                                                                    _UU03a6_2
                                                                    acm2 __
                                                                    __) c1)
                                                                    h3 pr2 __
                                                                    __) l1 __
                                                                    __ pr1) a;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h0 h3)
                                                                    (\_ _ pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    b h6)
                                                                    (\pr3 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    c1 h9)
                                                                    (\_ _ pr4 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2)
                                                                    (let {
                                                                    qpr = 
                                                                    loe ps1
                                                                    h0
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 h9))
                                                                    l2 pr4}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 _ _ ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    qpr0 = 
                                                                    loe ps1 b
                                                                    (Datatypes.app
                                                                    c1 h9) l2
                                                                    pr5}
                                                                    in
                                                                    case qpr0 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\_ _ pr6 ->
                                                                    let {
                                                                    qpr1 = 
                                                                    loe ps1
                                                                    c1 h9 l2
                                                                    pr6}
                                                                    in
                                                                    case qpr1 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr7 _ _ ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h9 l2
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr7)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm3 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm2
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm4 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm4 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    __ __)})
                                                                    x7 acm3)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9)
                                                                    _UU03a6_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h9)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h9
                                                                    _UU03a6_2)))
                                                                    c1 pr6 __
                                                                    __;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr7 _ _ ->
                                                                    let {
                                                                    _evar_0_ = \pr8 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 c1 l2
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr8)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm3 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm2
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm4 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm4 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    __ __)})
                                                                    x7 acm3)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    _UU03a6_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    c1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    c1
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    c1
                                                                    Datatypes.Coq_nil)
                                                                    pr7) h9
                                                                    pr6 __ __})
                                                                    b __ __
                                                                    pr5;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\_ _ pr6 ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr7 _ _ ->
                                                                    let {
                                                                    _evar_0_ = \pr8 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 b l2
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr8)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm3 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm2
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm4 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm4 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    __ __)})
                                                                    x7 acm3)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    b)
                                                                    _UU03a6_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    b)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    b
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    b
                                                                    Datatypes.Coq_nil)
                                                                    pr7) h9
                                                                    pr6 __ __)
                                                                    c1 __ __
                                                                    pr5}}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    _UU03a6_1
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    Datatypes.Coq_nil))
                                                                    h0 pr4 __
                                                                    __;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 _ _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\_ _ pr6 ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr7 _ _ ->
                                                                    let {
                                                                    _evar_0_ = \pr8 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 h0 l2
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr8)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm3 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm2
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm4 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm4 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2)))
                                                                    __ __)})
                                                                    x7 acm3)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    _UU03a6_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h0
                                                                    _UU03a6_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    _UU03a6_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    h0
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    h0
                                                                    Datatypes.Coq_nil)
                                                                    pr7) h9
                                                                    pr6 __ __)
                                                                    c1 __ __
                                                                    pr5) b
                                                                    pr4 __ __})
                                                                    d2) h6 __
                                                                    __ pr3)
                                                                    h3 pr2 __
                                                                    __) l1 __
                                                                    __ pr1) a}}}};
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    h0)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    l1 h3)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (\acm3 _ _ ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = DdT.Coq_derI
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (unsafeCoerce
                                                                    rs0
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e
                                                                    ps1 l1 l2
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    pr1)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)}
                                                                    in
                                                                    (case 
                                                                    DdT.dersrec_forall
                                                                    cs of {
                                                                     Datatypes.Coq_pair _
                                                                    x0 -> x0})
                                                                    (\q qin ->
                                                                    let {
                                                                    x0 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x0
                                                                    _ -> x0}}
                                                                    in
                                                                    let {
                                                                    qin0 = 
                                                                    x0 __ __
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1) q
                                                                    qin}
                                                                    in
                                                                    case qin0 of {
                                                                     Specif.Coq_existT x1
                                                                    x2 ->
                                                                    case x2 of {
                                                                     Datatypes.Coq_pair _
                                                                    x3 ->
                                                                    let {
                                                                    x4 = \_ _ f l3 y0 ->
                                                                    case 
                                                                    GenT.coq_InT_map_iffT
                                                                    f l3 y0 of {
                                                                     Datatypes.Coq_pair x4
                                                                    _ -> x4}}
                                                                    in
                                                                    let {
                                                                    inmps = 
                                                                    x4 __ __
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x1 x3}
                                                                    in
                                                                    case inmps of {
                                                                     Specif.Coq_existT x5
                                                                    x6 ->
                                                                    case x6 of {
                                                                     Datatypes.Coq_pair _
                                                                    x7 ->
                                                                    Logic.eq_rect
                                                                    (LntT.nslcext
                                                                    g0 d1 x1)
                                                                    (Logic.eq_rect
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (let {
                                                                    x8 = \_ _ l3 ->
                                                                    case 
                                                                    GenT.coq_ForallT_forall
                                                                    l3 of {
                                                                     Datatypes.Coq_pair x8
                                                                    _ -> x8}}
                                                                    in
                                                                    let {
                                                                    acm4 = 
                                                                    x8 __ __
                                                                    (List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2)
                                                                    ps1 x5
                                                                    x7))}
                                                                    in
                                                                    (case x5 of {
                                                                     Datatypes.Coq_pair l3
                                                                    l4 ->
                                                                    (\_ acm5 ->
                                                                    let {
                                                                    ns0 = 
                                                                    LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapL_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    _UU03a8_1
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    d1
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    l3
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _UU03a6_1
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    l3
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)) h3
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1) d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b) d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    (Datatypes.app
                                                                    c1 b) d2
                                                                    (Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    (SwappedT.swapped_simpleL
                                                                    b c1 c1)))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))))))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    l1
                                                                    (Datatypes.app
                                                                    h3
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l1 h3)
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l1 h3)
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1 h3))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _UU03a6_2
                                                                    acm2 __
                                                                    __) h0) a}}}})
                                                                    _UU0393_')
                                                                    y) x __
                                                                    __ __)})
                                                                   __ __)
                                                                 _UU0394_0 __
                                                                 __) _UU0393_
                                                               swap __ __)
                                                             ps0 acm1 sppc5)})
                                                          pr0 __)
                                                        (Datatypes.Coq_pair
                                                        _UU0393_ _UU0394_0))
                                                      ps0 __ pr)}) __ __)
                                                 seq2 sppc4 __ __) seq1 sppc3
                                               __ __) d0 acm0 __) l0 sppc2 __)
                                         l sppc1 __) seq2) seq1 __) d0) l0) l
                               __ __) k0) g1) ps acm;
                      Datatypes.Coq_inr pp3 ->
                       Logic.eq_rect (List.map (LntT.nslcext g0 d0) ps0)
                         (\_ ->
                         Logic.eq_rect_r
                           (Datatypes.app g0 (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair l l0)
                             d0) pp3)) Logic.coq_False_rect g1) ps acm}})})
                  pp0 __)}) sppc0 __ pp)) concl) ps __ sppc)}) __ __) __ nsr
    rs g k seq d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ __ __

gen_swapL_step_pr_lc :: (Datatypes.Coq_list
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Gen_tacs.Coq_rel
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)))
                        -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Gen_tacs.Coq_rel
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                        -> a2 -> (DdT.Coq_dersrec
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Gen_tacs.Coq_rel
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                        a3 ()) -> (GenT.ForallT
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LntT.PropF a1))
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                        (LntacsT.Coq_can_gen_swapL a1 a3)) -> (Gen.Coq_rsub
                        (Datatypes.Coq_list
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Gen_tacs.Coq_rel
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)))
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Gen_tacs.Coq_rel
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                        a2 a3) -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LntT.PropF a1))
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                        -> (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LntT.PropF a1))
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                        -> (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LntT.PropF a1))
                        (Datatypes.Coq_list (LntT.PropF a1))) -> LntT.Coq_dir
                        -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                        (Datatypes.Coq_list (LntT.PropF a1)) ->
                        (Datatypes.Coq_list (LntT.PropF a1)) ->
                        (Datatypes.Coq_list (LntT.PropF a1)) ->
                        (Datatypes.Coq_list (LntT.PropF a1)) ->
                        DdT.Coq_derrec
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Gen_tacs.Coq_rel
                        (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                        a3 ()
gen_swapL_step_pr_lc ps concl x x0 x1 x2 g k seq d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ =
  gen_swapL_step_loe_lc ps concl LntT.princrule_pfc_L_oe'T x x0 x1 x2 g k seq
    d _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_
