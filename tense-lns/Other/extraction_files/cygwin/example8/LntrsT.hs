{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module LntrsT where

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

gen_swapR_step_roe_lc :: (Datatypes.Coq_list
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)))
                         -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                         -> (LntT.Coq_rules_R_oeT (LntT.PropF a1) a2) -> a3
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
                         (LntacsT.Coq_can_gen_swapR a1 a4)) -> (Gen.Coq_rsub
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
gen_swapR_step_roe_lc ps concl roe nsr _ acm rs g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    (case unsafeCoerce nsr0 of {
      LntT.NSlcctxt ps0 c g0 d0 sppc -> (\_ _ ->
       Logic.eq_rect (List.map (LntT.nslcext g0 d0) ps0) (\_ ->
         Logic.eq_rect (LntT.nslcext g0 d0 c) (\sppc0 ->
           let {ns = LntT.nslcext g0 d0 c} in
           (case LntacsT.can_gen_swapR_def' ns of {
             Datatypes.Coq_pair _ x -> x})
             (\g1 k0 seq0 _UU0393_0 _UU0394_ _UU0394_' d1 swap _ _ ->
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
                               d0) Datatypes.Coq_nil)) (DdT.Coq_derI
                             (List.map
                               (LntT.nslcext
                                 (Datatypes.app g1 (Datatypes.Coq_cons
                                   (Datatypes.Coq_pair (Datatypes.Coq_pair
                                   _UU0393_0 _UU0394_') d1) pp3)) d0) ps0)
                             (Datatypes.app g1 (Datatypes.Coq_cons
                               (Datatypes.Coq_pair (Datatypes.Coq_pair
                               _UU0393_0 _UU0394_') d1)
                               (Datatypes.app pp3 (Datatypes.Coq_cons
                                 (Datatypes.Coq_pair (Datatypes.Coq_pair l
                                 l0) d0) Datatypes.Coq_nil))))
                             (unsafeCoerce rs0
                               (List.map
                                 (LntT.nslcext
                                   (Datatypes.app g1 (Datatypes.Coq_cons
                                     (Datatypes.Coq_pair (Datatypes.Coq_pair
                                     _UU0393_0 _UU0394_') d1) pp3)) d0) ps0)
                               (Datatypes.app g1 (Datatypes.Coq_cons
                                 (Datatypes.Coq_pair (Datatypes.Coq_pair
                                 _UU0393_0 _UU0394_') d1)
                                 (Datatypes.app pp3 (Datatypes.Coq_cons
                                   (Datatypes.Coq_pair (Datatypes.Coq_pair l
                                   l0) d0) Datatypes.Coq_nil))))
                               (let {
                                 _evar_0_ = let {
                                             _evar_0_ = LntT.coq_NSlcctxt'
                                                          ps0
                                                          (Datatypes.Coq_pair
                                                          l l0)
                                                          (Datatypes.app g1
                                                            (Datatypes.Coq_cons
                                                            (Datatypes.Coq_pair
                                                            (Datatypes.Coq_pair
                                                            _UU0393_0
                                                            _UU0394_') d1)
                                                            pp3)) d0 sppc1}
                                            in
                                            Logic.eq_rect_r
                                              (Datatypes.app
                                                (Datatypes.app g1
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_0 _UU0394_') d1)
                                                  pp3)) (Datatypes.Coq_cons
                                                (Datatypes.Coq_pair
                                                (Datatypes.Coq_pair l l0) d0)
                                                Datatypes.Coq_nil)) _evar_0_
                                              (Datatypes.app g1
                                                (Datatypes.app
                                                  (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair
                                                  _UU0393_0 _UU0394_') d1)
                                                  pp3) (Datatypes.Coq_cons
                                                  (Datatypes.Coq_pair
                                                  (Datatypes.Coq_pair l l0)
                                                  d0) Datatypes.Coq_nil)))}
                                in
                                Logic.eq_rect_r
                                  (Datatypes.app (Datatypes.Coq_cons
                                    (Datatypes.Coq_pair (Datatypes.Coq_pair
                                    _UU0393_0 _UU0394_') d1) pp3)
                                    (Datatypes.Coq_cons (Datatypes.Coq_pair
                                    (Datatypes.Coq_pair l l0) d0)
                                    Datatypes.Coq_nil)) _evar_0_
                                  (Datatypes.Coq_cons (Datatypes.Coq_pair
                                  (Datatypes.Coq_pair _UU0393_0 _UU0394_')
                                  d1)
                                  (Datatypes.app pp3 (Datatypes.Coq_cons
                                    (Datatypes.Coq_pair (Datatypes.Coq_pair l
                                    l0) d0) Datatypes.Coq_nil)))))
                             (let {
                               cs = List.map
                                      (LntT.nslcext
                                        (Datatypes.app g1 (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair _UU0393_0
                                          _UU0394_') d1) pp3)) d0) ps0}
                              in
                              (case DdT.dersrec_forall cs of {
                                Datatypes.Coq_pair _ x -> x}) (\q qin ->
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
                                              (Datatypes.Coq_pair _UU0393_0
                                              _UU0394_') d1) pp3)) d0) ps0 q
                                          qin}
                                in
                                case qin0 of {
                                 Specif.Coq_existT x0 x1 ->
                                  case x1 of {
                                   Datatypes.Coq_pair _ x2 ->
                                    Logic.eq_rect
                                      (LntT.nslcext
                                        (Datatypes.app g1 (Datatypes.Coq_cons
                                          (Datatypes.Coq_pair
                                          (Datatypes.Coq_pair _UU0393_0
                                          _UU0394_') d1) pp3)) d0 x0)
                                      (let {
                                        x3 = \_ _ l1 ->
                                         case GenT.coq_ForallT_forall l1 of {
                                          Datatypes.Coq_pair x3 _ -> x3}}
                                       in
                                       let {
                                        acm2 = x3 __ __
                                                 (List.map
                                                   (LntT.nslcext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       seq1 seq2) d1) pp3))
                                                     d0) ps0) acm1
                                                 (LntT.nslcext
                                                   (Datatypes.app g1
                                                     (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair
                                                     (Datatypes.Coq_pair seq1
                                                     seq2) d1) pp3)) d0 x0)
                                                 (GenT.coq_InT_map
                                                   (LntT.nslcext
                                                     (Datatypes.app g1
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       seq1 seq2) d1) pp3))
                                                     d0) ps0 x0 x2)}
                                       in
                                       let {
                                        x4 = \_ ns0 ->
                                         case LntacsT.can_gen_swapR_def' ns0 of {
                                          Datatypes.Coq_pair x4 _ -> x4}}
                                       in
                                       let {
                                        acm3 = x4 __
                                                 (LntT.nslcext
                                                   (Datatypes.app g1
                                                     (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair
                                                     (Datatypes.Coq_pair seq1
                                                     seq2) d1) pp3)) d0 x0)
                                                 acm2 g1
                                                 (Datatypes.app pp3
                                                   (Datatypes.Coq_cons
                                                   (Datatypes.Coq_pair x0 d0)
                                                   Datatypes.Coq_nil))
                                                 (Datatypes.Coq_pair seq1
                                                 seq2) _UU0393_0 _UU0394_
                                                 _UU0394_' d1 swap __ __}
                                       in
                                       let {
                                        _evar_0_ = Logic.eq_rect
                                                     (Datatypes.Coq_cons
                                                     (Datatypes.Coq_pair
                                                     (Datatypes.Coq_pair
                                                     _UU0393_0 _UU0394_') d1)
                                                     (Datatypes.app pp3
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair x0
                                                       d0)
                                                       Datatypes.Coq_nil)))
                                                     acm3
                                                     (Datatypes.app
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.Coq_pair
                                                       _UU0393_0 _UU0394_')
                                                       d1) pp3)
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair x0
                                                       d0)
                                                       Datatypes.Coq_nil))}
                                       in
                                       Logic.eq_rect
                                         (Datatypes.app g1
                                           (Datatypes.app (Datatypes.Coq_cons
                                             (Datatypes.Coq_pair
                                             (Datatypes.Coq_pair _UU0393_0
                                             _UU0394_') d1) pp3)
                                             (Datatypes.Coq_cons
                                             (Datatypes.Coq_pair x0 d0)
                                             Datatypes.Coq_nil))) _evar_0_
                                         (Datatypes.app
                                           (Datatypes.app g1
                                             (Datatypes.Coq_cons
                                             (Datatypes.Coq_pair
                                             (Datatypes.Coq_pair _UU0393_0
                                             _UU0394_') d1) pp3))
                                           (Datatypes.Coq_cons
                                           (Datatypes.Coq_pair x0 d0)
                                           Datatypes.Coq_nil))) q}}))) k0) g0
                           acm0) ps acm};
                    Datatypes.Coq_inr pp2 ->
                     case pp2 of {
                      Datatypes.Coq_inl _ ->
                       Logic.eq_rect (List.map (LntT.nslcext g0 d0) ps0)
                         (\acm0 ->
                         Logic.eq_rect_r g0
                           (Logic.eq_rect Datatypes.Coq_nil
                             (Logic.eq_rect_r _UU0393_0 (\_ ->
                               Logic.eq_rect_r _UU0394_ (\_ ->
                                 (case sppc1 of {
                                   Gen_seq.Sctxt ps1 c0 _UU03a6_1 _UU03a6_2
                                    _UU03a8_1 _UU03a8_2 pr -> (\_ _ ->
                                    Logic.eq_rect
                                      (List.map
                                        (Gen_seq.seqext _UU03a6_1 _UU03a6_2
                                          _UU03a8_1 _UU03a8_2) ps1) (\_ ->
                                      Logic.eq_rect
                                        (Gen_seq.seqext _UU03a6_1 _UU03a6_2
                                          _UU03a8_1 _UU03a8_2 c0) (\pr0 ->
                                        (case c0 of {
                                          Datatypes.Coq_pair l1 l2 ->
                                           (\pr1 _ ->
                                           Logic.eq_rect
                                             (List.map
                                               (Gen_seq.seqext _UU03a6_1
                                                 _UU03a6_2 _UU03a8_1
                                                 _UU03a8_2) ps1) (\acm1 _ ->
                                             Logic.eq_rect
                                               (Datatypes.app _UU03a6_1
                                                 (Datatypes.app l1 _UU03a6_2))
                                               (\_ ->
                                               Logic.eq_rect
                                                 (Datatypes.app _UU03a8_1
                                                   (Datatypes.app l2
                                                     _UU03a8_2)) (\_ ->
                                                 (case swap of {
                                                   SwappedT.Coq_swapped_I x y
                                                    a b c1 d2 -> (\_ _ ->
                                                    Logic.eq_rect_r _UU0394_
                                                      (\_ ->
                                                      Logic.eq_rect_r
                                                        _UU0394_' (\_ _ ->
                                                        Logic.eq_rect_r
                                                          (Datatypes.app a
                                                            (Datatypes.app b
                                                              (Datatypes.app
                                                                c1 d2)))
                                                          (\_ ->
                                                          Logic.eq_rect_r
                                                            (Datatypes.app a
                                                              (Datatypes.app
                                                                c1
                                                                (Datatypes.app
                                                                  b d2)))
                                                            (let {
                                                              pp3 = List_lemmasT.app_eq_appT2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))}
                                                             in
                                                             case pp3 of {
                                                              Specif.Coq_existT pp4
                                                               pp5 ->
                                                               case pp5 of {
                                                                Datatypes.Coq_inl _ ->
                                                                 let {
                                                                  pp6 = 
                                                                   List_lemmasT.app_eq_appT2
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)}
                                                                 in
                                                                 case pp6 of {
                                                                  Specif.Coq_existT pp7
                                                                   pp8 ->
                                                                   case pp8 of {
                                                                    Datatypes.Coq_inl _ ->
                                                                    let {
                                                                    pp9 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    l2
                                                                    _UU03a8_2
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1 d2)}
                                                                    in
                                                                    case pp9 of {
                                                                     Specif.Coq_existT pp10
                                                                    pp11 ->
                                                                    case pp11 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    let {
                                                                    pp12 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    c1 d2
                                                                    pp10
                                                                    _UU03a8_2}
                                                                    in
                                                                    case pp12 of {
                                                                     Specif.Coq_existT pp13
                                                                    pp14 ->
                                                                    case pp14 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (\acm2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp4 pp7)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp7 pp10)
                                                                    (\pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp10
                                                                    pp13)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (\acm3 ->
                                                                    Logic.eq_rect_r
                                                                    d1
                                                                    (\acm4 ->
                                                                    let {
                                                                    qpr = 
                                                                    roe ps1
                                                                    pp7 pp10
                                                                    l1 pr2}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 ->
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    a
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))))
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
                                                                    a
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    a
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp10
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    a
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2))
                                                                    pr3)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    a
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))
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
                                                                    a
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))
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
                                                                    a
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))
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
                                                                    a
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2))
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1))
                                                                    acm4
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm6 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2))))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp13) d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp13)
                                                                    (Datatypes.app
                                                                    pp4 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp13)
                                                                    pp4) d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp13)
                                                                    pp4) d2
                                                                    (let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp13)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 pp4))
                                                                    (SwappedT.swapped_simpleL
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 pp13)
                                                                    (Datatypes.app
                                                                    l4 pp13))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 pp4))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp13)
                                                                    pp4)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 pp13))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp13)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp13)
                                                                    (Datatypes.app
                                                                    pp4 d2)))
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    __ __)})
                                                                    x7 acm5)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp10)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp10)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp10
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    pp4 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    pp4
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    pp4
                                                                    Datatypes.Coq_nil))
                                                                    pp7 pr2;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 ->
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4) d2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp7 d2)))
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4) d2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp7 d2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4) d2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp7 d2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp7
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4) d2
                                                                    pr4)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4) d2)
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4) d2)
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4) d2)
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4) d2
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1))
                                                                    acm4
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm6 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    l4 d2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 d2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 d2))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 d2)))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp13) d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp13 pp4)
                                                                    (Datatypes.app
                                                                    l4 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp13 pp4)
                                                                    l4) d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp13 pp4)
                                                                    l4) d2
                                                                    (let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    Gen.arg1_cong_imp
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 pp13))
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 l4))
                                                                    (SwappedT.swapped_simpleR
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    (Datatypes.app
                                                                    pp4 l4))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4 l4))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp13 pp4)
                                                                    l4)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 pp13))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp13)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp13 pp4)
                                                                    (Datatypes.app
                                                                    l4 d2)))
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    l4 d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    __ __)})
                                                                    x7 acm5)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp7 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4) pp7)
                                                                    d2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4) pp7)
                                                                    d2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp7 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp7 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp7 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp13)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp7 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp7 d2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp7 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 pp7)
                                                                    d2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    pp7
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    pp7
                                                                    Datatypes.Coq_nil)
                                                                    pr3) pp10
                                                                    pr2}) d0
                                                                    acm3)
                                                                    _UU03a8_2
                                                                    acm2) c1)
                                                                    l2 pr1) b)
                                                                    _UU03a8_1
                                                                    acm1)
                                                                    _UU0393_0;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (\acm2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp4 pp7)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp7 pp10)
                                                                    (\pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    c1 pp13)
                                                                    (\pr3 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2)
                                                                    (Logic.eq_rect_r
                                                                    d1
                                                                    (\acm3 ->
                                                                    let {
                                                                    qpr = 
                                                                    roe ps1
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1 pp13)
                                                                    l1 pr3}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr4 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    qpr0 = 
                                                                    roe ps1
                                                                    c1 pp13
                                                                    l1 pr4}
                                                                    in
                                                                    case qpr0 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 ->
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
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13
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
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp13
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    pp13)
                                                                    _UU03a8_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    pp13)
                                                                    _UU03a8_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2)))
                                                                    c1 pr4;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 ->
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
                                                                    _UU03a6_2
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))))
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
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1 c1
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2)
                                                                    pr6)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))
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
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))
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
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))
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
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2)
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
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2)))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    _UU03a8_2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp4)
                                                                    _UU03a8_2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    (Datatypes.app
                                                                    l4 pp4)
                                                                    _UU03a8_2
                                                                    (Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    l4 pp4)
                                                                    (Datatypes.app
                                                                    l4 pp4)
                                                                    (SwappedT.swapped_simpleL
                                                                    pp4 l4
                                                                    l4)))
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
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
                                                                    pp4
                                                                    _UU03a8_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    c1
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    c1
                                                                    Datatypes.Coq_nil)
                                                                    pr5) pp13
                                                                    pr4}}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    pp4
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    pp4
                                                                    Datatypes.Coq_nil))
                                                                    pp7 pr3;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr4 ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 ->
                                                                    let {
                                                                    _evar_0_ = \pr6 ->
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp7
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
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp7
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
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
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    pp7)
                                                                    _UU03a8_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    pp7)
                                                                    _UU03a8_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    _UU03a8_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp7
                                                                    _UU03a8_2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp7
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 pp7)
                                                                    _UU03a8_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    pp7
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    pp7
                                                                    Datatypes.Coq_nil)
                                                                    pr5) pp13
                                                                    pr4) c1
                                                                    pr3}) d0
                                                                    acm2) d2)
                                                                    pp10 pr2)
                                                                    l2 pr1) b)
                                                                    _UU03a8_1
                                                                    acm1)
                                                                    _UU0393_0}};
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (\acm2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp4 pp7)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    l2 pp10)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (\acm3 ->
                                                                    Logic.eq_rect_r
                                                                    d1
                                                                    (\acm4 ->
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp10 d2))))
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1 l2
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp10 d2)
                                                                    pr1)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp10 d2))
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp10 d2))
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp10 d2))
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp10 d2)
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    ps1))
                                                                    acm4
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm6 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2)))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp10) c1)
                                                                    d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp4)
                                                                    l4)
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp4)
                                                                    l4) pp10)
                                                                    d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp10) c1)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp4)
                                                                    l4) pp10)
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
                                                                    pp4 l4)
                                                                    pp10) c1)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 c1)))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 pp10)))
                                                                    (SwappedT.swapped_simpleR
                                                                    c1
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 pp10)))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4 pp10)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp4)
                                                                    (Datatypes.app
                                                                    l4 pp10))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp4)
                                                                    (Datatypes.app
                                                                    l4 pp10))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp4)
                                                                    l4) pp10)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 c1)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    (Datatypes.app
                                                                    pp10 c1))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    (Datatypes.app
                                                                    pp10 c1))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp10) c1)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp4)
                                                                    l4)
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4 l4)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10
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
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4) l2)
                                                                    (Datatypes.app
                                                                    pp10 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4) l2)
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp10 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp10 d2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp10 d2)))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l2 pp10)
                                                                    d2)}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l2 pp10)
                                                                    d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    l2 pp10))
                                                                    d2)) d0
                                                                    acm3)
                                                                    _UU03a8_2
                                                                    acm2)
                                                                    pp7) b)
                                                                    _UU03a8_1
                                                                    acm1)
                                                                    _UU0393_0}};
                                                                    Datatypes.Coq_inr _ ->
                                                                    let {
                                                                    pp9 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    c1 d2 pp7
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)}
                                                                    in
                                                                    case pp9 of {
                                                                     Specif.Coq_existT pp10
                                                                    pp11 ->
                                                                    case pp11 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    let {
                                                                    pp12 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    l2
                                                                    _UU03a8_2
                                                                    pp10 d2}
                                                                    in
                                                                    case pp12 of {
                                                                     Specif.Coq_existT pp13
                                                                    pp14 ->
                                                                    case pp14 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (\acm2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (\acm3 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp7 pp10)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp10
                                                                    pp13)
                                                                    (\pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2)
                                                                    (Logic.eq_rect_r
                                                                    d1
                                                                    (\acm4 ->
                                                                    let {
                                                                    qpr = 
                                                                    roe ps1
                                                                    pp10 pp13
                                                                    l1 pr2}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 ->
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
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
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    (Datatypes.app
                                                                    pp13
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
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
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp13
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    _UU03a8_2
                                                                    pr3)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm4
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm6 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    l4)
                                                                    _UU03a8_2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 b)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 b)
                                                                    l4)
                                                                    _UU03a8_2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    l4)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 b)
                                                                    l4)
                                                                    _UU03a8_2
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    pp7 b) l4
                                                                    (Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    pp7 b)
                                                                    (Datatypes.app
                                                                    pp7 b)
                                                                    (SwappedT.swapped_simpleL
                                                                    b pp7
                                                                    pp7))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 b)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    __ __)})
                                                                    x7 acm5)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    pp13)
                                                                    _UU03a8_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    pp13)
                                                                    _UU03a8_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7) b)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    pp7
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    pp7
                                                                    Datatypes.Coq_nil))
                                                                    pp10 pr2;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 ->
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))))
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
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp10
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2)
                                                                    pr4)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))
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
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))
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
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))
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
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2)
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm4
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm6 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2)))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2)))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    l4)
                                                                    _UU03a8_2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    b)
                                                                    _UU03a8_2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    l4)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    b)
                                                                    _UU03a8_2
                                                                    (let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    b)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4 b))
                                                                    (SwappedT.swapped_simpleL
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    (Datatypes.app
                                                                    pp7 l4))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4 b))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    b)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7 l4))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    l4)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    __ __)})
                                                                    x7 acm5)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 pp10)
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    pp10
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    pp10
                                                                    Datatypes.Coq_nil)
                                                                    pr3) pp13
                                                                    pr2}) d0
                                                                    acm3) d2)
                                                                    l2 pr1)
                                                                    c1) pp4
                                                                    acm2)
                                                                    _UU03a8_1
                                                                    acm1)
                                                                    _UU0393_0;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (\acm2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (\acm3 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp7 pp10)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    l2 pp13)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (\acm4 ->
                                                                    Logic.eq_rect_r
                                                                    d1
                                                                    (\acm5 ->
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))))
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
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1 l2
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    pr1)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))
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
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))
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
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))
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
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2))
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1))
                                                                    acm5
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm7 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    l4)
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    l4) pp13)
                                                                    d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    pp13) b)
                                                                    d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    l4) pp13)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    pp13) b)
                                                                    d2
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
                                                                    pp7 l4)
                                                                    pp13) b)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 b)))
                                                                    (SwappedT.swapped_simpleL
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4 pp13))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    pp13))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 b)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    (Datatypes.app
                                                                    pp13 b))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    (Datatypes.app
                                                                    pp13 b))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    pp13) b)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4 pp13)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4 pp13))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4 pp13))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    l4) pp13)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 l4)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    l4)
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b pp7))
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    __ __)})
                                                                    x7 acm6)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    l2)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    l2)
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a pp7)
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l2 pp13)
                                                                    (Datatypes.app
                                                                    b d2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l2 pp13)
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    l2 pp13))
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    d0 acm4)
                                                                    _UU03a8_2
                                                                    acm3)
                                                                    pp10) c1)
                                                                    pp4 acm2)
                                                                    _UU03a8_1
                                                                    acm1)
                                                                    _UU0393_0}};
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    a pp4)
                                                                    (\acm2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    b pp7)
                                                                    (\acm3 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    c1 pp10)
                                                                    (\acm4 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2))
                                                                    (Logic.eq_rect_r
                                                                    d1
                                                                    (\acm5 ->
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
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
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
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
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1 l2
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
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
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
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
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp10)))
                                                                    _UU03a8_2)
                                                                    ps1))
                                                                    acm5
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp10)))
                                                                    _UU03a8_2
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp10)))
                                                                    _UU03a8_2)
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp10)))
                                                                    _UU03a8_2
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp10)))
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp10)))
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm7 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp10)))
                                                                    _UU03a8_2
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l3
                                                                    _UU03a6_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp10)))
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp10))
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp10)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    a
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    pp10) l4)
                                                                    _UU03a8_2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    pp10) l4)
                                                                    _UU03a8_2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    pp10) l4)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    pp10) l4)
                                                                    _UU03a8_2
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    pp10) l4
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    pp10
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
                                                                    c1 b)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 b)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b c1)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp10)
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp10))
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp10)))
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
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
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10) l2)
                                                                    _UU03a8_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10) l2)
                                                                    _UU03a8_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1) b)
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    a c1)
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    a
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    l2
                                                                    _UU03a8_2)))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2)))
                                                                    d0 acm4)
                                                                    d2) pp7
                                                                    acm3) pp4
                                                                    acm2)
                                                                    _UU03a8_1
                                                                    acm1)
                                                                    _UU0393_0}}}};
                                                                Datatypes.Coq_inr _ ->
                                                                 let {
                                                                  pp6 = 
                                                                   List_lemmasT.app_eq_appT2
                                                                    l2
                                                                    _UU03a8_2
                                                                    pp4
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))}
                                                                 in
                                                                 case pp6 of {
                                                                  Specif.Coq_existT pp7
                                                                   pp8 ->
                                                                   case pp8 of {
                                                                    Datatypes.Coq_inl _ ->
                                                                    let {
                                                                    pp9 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)
                                                                    pp7
                                                                    _UU03a8_2}
                                                                    in
                                                                    case pp9 of {
                                                                     Specif.Coq_existT pp10
                                                                    pp11 ->
                                                                    case pp11 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp4 pp7)
                                                                    (\pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp7 pp10)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (\acm2 ->
                                                                    Logic.eq_rect_r
                                                                    d1
                                                                    (\acm3 ->
                                                                    let {
                                                                    qpr = 
                                                                    roe ps1
                                                                    pp4 pp7
                                                                    l1 pr2}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 ->
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    pp10 d2))))
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
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp7
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp10 d2)
                                                                    pr3)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp10 d2))
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
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp10 d2))
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
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp10 d2))
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
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp10 d2)
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
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
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    _UU03a8_1
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp10)
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp10)
                                                                    c1) d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 l4)
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 l4)
                                                                    pp10) d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp10)
                                                                    c1)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 l4)
                                                                    pp10) d2
                                                                    (let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    _evar_0_ = 
                                                                    Gen.arg1_cong_imp
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp10)
                                                                    c1)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 c1))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    l4 pp10))
                                                                    (SwappedT.swapped_simpleR
                                                                    c1
                                                                    (Datatypes.app
                                                                    l4 pp10)
                                                                    (Datatypes.app
                                                                    l4 pp10))}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    l4 pp10))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 l4)
                                                                    pp10)}
                                                                    in
                                                                    Logic.eq_rec
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 c1))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp10)
                                                                    c1)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 l4)
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp10)
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1) pp7)
                                                                    (Datatypes.app
                                                                    pp10 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1) pp7)
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    pp10 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    pp10 d2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp7 pp10)
                                                                    d2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    _UU03a8_1
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    Datatypes.Coq_nil))
                                                                    pp4 pr2;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr3 ->
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))))
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
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp4
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    pr4)))
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
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))
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
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))
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
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))
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
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2))
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
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
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    d1
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    _UU03a8_1
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2))
                                                                    l4
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp10 c1)
                                                                    d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    c1 pp10)
                                                                    d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    pp10 c1)
                                                                    (Datatypes.app
                                                                    c1 pp10)
                                                                    d2
                                                                    (Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    c1 pp10)
                                                                    (Datatypes.app
                                                                    c1 pp10)
                                                                    (SwappedT.swapped_simpleL
                                                                    pp10 c1
                                                                    c1)))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    c1 d2)))))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    pp10 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    pp4
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    pp4
                                                                    Datatypes.Coq_nil)
                                                                    pr3) pp7
                                                                    pr2}) d0
                                                                    acm2)
                                                                    _UU03a8_2
                                                                    acm1) b)
                                                                    l2 pr1)
                                                                    a)
                                                                    _UU0393_0;
                                                                     Datatypes.Coq_inr _ ->
                                                                    let {
                                                                    pp12 = 
                                                                    List_lemmasT.app_eq_appT2
                                                                    c1 d2
                                                                    pp10
                                                                    _UU03a8_2}
                                                                    in
                                                                    case pp12 of {
                                                                     Specif.Coq_existT pp13
                                                                    pp14 ->
                                                                    case pp14 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp4 pp7)
                                                                    (\pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    b pp10)
                                                                    (\pr3 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp10
                                                                    pp13)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (\acm2 ->
                                                                    Logic.eq_rect_r
                                                                    d1
                                                                    (\acm3 ->
                                                                    let {
                                                                    qpr = 
                                                                    roe ps1
                                                                    pp4
                                                                    (Datatypes.app
                                                                    b pp10)
                                                                    l1 pr3}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr4 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    qpr0 = 
                                                                    roe ps1 b
                                                                    pp10 l1
                                                                    pr4}
                                                                    in
                                                                    case qpr0 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 ->
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13 d2))))
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
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp10
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    pr5)))
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
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    (Datatypes.app
                                                                    pp13 d2)
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
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
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    pp13 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp10)
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    pp10
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp10
                                                                    pp13) d2))
                                                                    b pr4;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 ->
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13) d2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    b d2)))
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
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13) d2)
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13) d2)
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1 b
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13) d2
                                                                    pr6)))
                                                                    (let {
                                                                    cs = 
                                                                    List.map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13) d2)
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
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13) d2)
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
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13) d2)
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
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13) d2
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
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
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    l4 d2))
                                                                    d1
                                                                    (Logic.eq_rec
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    l4 d2)))
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    l4 d2))
                                                                    _UU03a8_1
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l4 pp13)
                                                                    d2)
                                                                    (Logic.eq_rec_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    pp13 l4)
                                                                    d2)
                                                                    (SwappedT.swapped_R
                                                                    (Datatypes.app
                                                                    l4 pp13)
                                                                    (Datatypes.app
                                                                    pp13 l4)
                                                                    d2
                                                                    (Gen.arg_cong_imp
                                                                    (Datatypes.app
                                                                    pp13 l4)
                                                                    (Datatypes.app
                                                                    pp13 l4)
                                                                    (SwappedT.swapped_simpleL
                                                                    l4 pp13
                                                                    pp13)))
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    l4 d2)))
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    l4 d2)))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13) b)
                                                                    d2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13) b)
                                                                    d2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    b d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13)
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13
                                                                    (Datatypes.app
                                                                    b d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    b
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    b
                                                                    Datatypes.Coq_nil)
                                                                    pr5) pp10
                                                                    pr4}}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    _UU03a8_1
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    Datatypes.Coq_nil))
                                                                    pp4 pr3;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr4 ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 ->
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
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
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp4
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    pr6)))
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
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    (Datatypes.app
                                                                    pp13 d2)
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2))
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13 d2)
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
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp13 d2))))
                                                                    __ __)})
                                                                    x7 acm4)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp13 d2)))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    (Datatypes.app
                                                                    pp13 d2)))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    (Datatypes.app
                                                                    pp13 d2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    pp4
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    pp4
                                                                    Datatypes.Coq_nil)
                                                                    pr5) pp10
                                                                    pr4) b
                                                                    pr3}) d0
                                                                    acm2)
                                                                    _UU03a8_2
                                                                    acm1) c1)
                                                                    pp7 pr2)
                                                                    l2 pr1)
                                                                    a)
                                                                    _UU0393_0;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp4 pp7)
                                                                    (\pr2 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    b pp10)
                                                                    (\pr3 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    c1 pp13)
                                                                    (\pr4 ->
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2)
                                                                    (Logic.eq_rect_r
                                                                    d1
                                                                    (\acm2 ->
                                                                    let {
                                                                    qpr = 
                                                                    roe ps1
                                                                    pp4
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 pp13))
                                                                    l1 pr4}
                                                                    in
                                                                    case qpr of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 ->
                                                                    let {
                                                                    _evar_0_ = 
                                                                    let {
                                                                    qpr0 = 
                                                                    roe ps1 b
                                                                    (Datatypes.app
                                                                    c1 pp13)
                                                                    l1 pr5}
                                                                    in
                                                                    case qpr0 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr6 ->
                                                                    let {
                                                                    qpr1 = 
                                                                    roe ps1
                                                                    c1 pp13
                                                                    l1 pr6}
                                                                    in
                                                                    case qpr1 of {
                                                                     Datatypes.Coq_inl _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr7 ->
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
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13
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
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13
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
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp13
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
                                                                    LntacsT.can_gen_swapR_def'
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
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    __ __)})
                                                                    x7 acm3)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13)
                                                                    _UU03a8_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp13)
                                                                    _UU03a8_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp13
                                                                    _UU03a8_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2)))
                                                                    c1 pr6;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr7 ->
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
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    c1
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
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    c1
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
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1 c1
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
                                                                    LntacsT.can_gen_swapR_def'
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
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    __ __)})
                                                                    x7 acm3)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    _UU03a8_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    c1)
                                                                    _UU03a8_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    c1
                                                                    _UU03a8_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    c1
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    c1
                                                                    Datatypes.Coq_nil)
                                                                    pr7) pp13
                                                                    pr6}) b
                                                                    pr5;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr6 ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr7 ->
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
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    b
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
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    b
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
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1 b
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
                                                                    LntacsT.can_gen_swapR_def'
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
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    __ __)})
                                                                    x7 acm3)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    b)
                                                                    _UU03a8_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    b)
                                                                    _UU03a8_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    b
                                                                    _UU03a8_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    b
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    b
                                                                    Datatypes.Coq_nil)
                                                                    pr7) pp13
                                                                    pr6) c1
                                                                    pr5}}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    _UU03a8_1
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    Datatypes.Coq_nil))
                                                                    pp4 pr4;
                                                                     Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr5 ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr6 ->
                                                                    Logic.eq_rect_r
                                                                    Datatypes.Coq_nil
                                                                    (\pr7 ->
                                                                    let {
                                                                    _evar_0_ = \pr8 ->
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
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
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
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
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
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2)))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1
                                                                    pp4
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
                                                                    LntacsT.can_gen_swapR_def'
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
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2))
                                                                    d1
                                                                    (SwappedT.swapped_same
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    _UU03a8_2)))
                                                                    __ __)})
                                                                    x7 acm3)
                                                                    x1) q}}}}))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    _UU03a8_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    _UU03a8_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp4
                                                                    _UU03a8_2))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    _UU03a8_2)}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    pp4
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    pp4
                                                                    Datatypes.Coq_nil)
                                                                    pr7) pp13
                                                                    pr6) c1
                                                                    pr5) b
                                                                    pr4}) d0
                                                                    acm1) d2)
                                                                    pp10 pr3)
                                                                    pp7 pr2)
                                                                    l2 pr1)
                                                                    a)
                                                                    _UU0393_0}}}};
                                                                    Datatypes.Coq_inr _ ->
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    pp4)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    l2 pp7)
                                                                    (Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (\acm2 ->
                                                                    Logic.eq_rect_r
                                                                    d1
                                                                    (\acm3 ->
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
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))))
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
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    ps1))
                                                                    (Datatypes.app
                                                                    g0
                                                                    (Datatypes.Coq_cons
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))))
                                                                    d1)
                                                                    Datatypes.Coq_nil))
                                                                    (LntT.coq_NSlcctxt'
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    ps1)
                                                                    (Datatypes.Coq_pair
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))))
                                                                    g0 d1
                                                                    (Gen_seq.coq_Sctxt_e'
                                                                    ps1 l1 l2
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    pr1)))
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
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
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
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
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
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
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
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    ps1))
                                                                    acm3
                                                                    (LntT.nslcext
                                                                    g0 d1
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    x5))
                                                                    (GenT.coq_InT_map
                                                                    (LntT.nslcext
                                                                    g0 d1)
                                                                    (List.map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    ps1)
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    x5)
                                                                    (GenT.coq_InT_map
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))))
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
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Datatypes.Coq_pair
                                                                    l3 l4))}
                                                                    in
                                                                    (case 
                                                                    LntacsT.can_gen_swapR_def'
                                                                    ns0 of {
                                                                     Datatypes.Coq_pair x9
                                                                    _ -> x9})
                                                                    acm5 g0
                                                                    Datatypes.Coq_nil
                                                                    (Gen_seq.seqext
                                                                    _UU03a6_1
                                                                    _UU03a6_2
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
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
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))))
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    d1
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))))
                                                                    (Datatypes.app
                                                                    l4
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _UU03a8_1
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2)))
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))
                                                                    l4
                                                                    (SwappedT.swapped_L
                                                                    (Datatypes.app
                                                                    b
                                                                    (Datatypes.app
                                                                    c1 d2))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))
                                                                    pp7
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
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    l2)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    l2)
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))))}
                                                                    in
                                                                    Logic.eq_rect_r
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    l1)
                                                                    _UU03a6_2)
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    _UU03a6_1
                                                                    (Datatypes.app
                                                                    l1
                                                                    _UU03a6_2))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    l2
                                                                    (Datatypes.app
                                                                    pp7
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l2 pp7)
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2)))}
                                                                    in
                                                                    Logic.eq_rect
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    l2 pp7)
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    _evar_0_
                                                                    (Datatypes.app
                                                                    (Datatypes.app
                                                                    _UU03a8_1
                                                                    (Datatypes.app
                                                                    l2 pp7))
                                                                    (Datatypes.app
                                                                    c1
                                                                    (Datatypes.app
                                                                    b d2))))
                                                                    d0 acm2)
                                                                    _UU03a8_2
                                                                    acm1)
                                                                    pp4) a)
                                                                    _UU0393_0}}}})
                                                            _UU0394_')
                                                          _UU0394_ __) y) x
                                                      __ __ __)}) __ __) l0
                                                 __) l __) ps0 acm0 sppc1)})
                                          pr0 __) (Datatypes.Coq_pair l l0))
                                      ps0 __ pr)}) __ __) seq2 __) seq1 __)
                             k0) g1) ps acm;
                      Datatypes.Coq_inr pp3 ->
                       Logic.eq_rect (List.map (LntT.nslcext g0 d0) ps0)
                         (\_ ->
                         Logic.eq_rect_r
                           (Datatypes.app g0 (Datatypes.Coq_cons
                             (Datatypes.Coq_pair (Datatypes.Coq_pair l l0)
                             d0) pp3)) Logic.coq_False_rect g1) ps acm}})})
                  pp0 __)}) sppc0 __ pp)) concl) ps __ sppc)}) __ __) __ nsr
    rs g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ __ __

gen_swapR_step_pr_lc :: (Datatypes.Coq_list
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
                        (LntacsT.Coq_can_gen_swapR a1 a3)) -> (Gen.Coq_rsub
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
gen_swapR_step_pr_lc ps concl x x0 x1 x2 g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ =
  gen_swapR_step_roe_lc ps concl LntT.princrule_pfc_R_oe'T x x0 x1 x2 g k seq
    d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_

