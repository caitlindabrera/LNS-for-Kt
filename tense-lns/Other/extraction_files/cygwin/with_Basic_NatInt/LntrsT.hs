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

gen_swapR_step_roe_lc :: (([])
                         (([])
                         ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                         LntT.Coq_dir))) -> (([])
                         ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                         LntT.Coq_dir)) -> (LntT.Coq_rules_R_oeT
                         (LntT.PropF a1) a2) -> a3 -> (DdT.Coq_dersrec
                         (([])
                         ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                         LntT.Coq_dir)) a4 ()) -> (GenT.ForallT
                         (([])
                         ((,)
                         ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                         LntT.Coq_dir)) (LntacsT.Coq_can_gen_swapR a1 a4)) ->
                         (Gen.Coq_rsub
                         (([])
                         (([])
                         ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                         LntT.Coq_dir)))
                         (([])
                         ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                         LntT.Coq_dir)) a3 a4) -> (([])
                         ((,)
                         ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                         LntT.Coq_dir)) -> (([])
                         ((,)
                         ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                         LntT.Coq_dir)) -> ((,) (([]) (LntT.PropF a1))
                         (([]) (LntT.PropF a1))) -> LntT.Coq_dir -> (([])
                         (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                         (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                         (LntT.PropF a1)) -> DdT.Coq_derrec
                         (([])
                         ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                         LntT.Coq_dir)) a4 ()
gen_swapR_step_roe_lc ps concl roe nsr _ acm rs g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ =
  Logic.eq_rect_r __ (\nsr0 rs0 ->
    case unsafeCoerce nsr0 of {
     LntT.NSlcctxt ps0 c g0 d0 sppc ->
      Logic.eq_rect (List.map (LntT.nslcext g0 d0) ps0) (\_ ->
        Logic.eq_rect (LntT.nslcext g0 d0 c) (\sppc0 ->
          let {ns = LntT.nslcext g0 d0 c} in
          case LntacsT.can_gen_swapR_def' ns of {
           (,) _ x ->
            x (\g1 k0 seq0 _UU0393_0 _UU0394_ _UU0394_' d1 swap _ _ ->
              let {
               pp = List_lemmasT.partition_2_2T g0 ([]) g1 k0 ((,) c d0) ((,)
                      seq0 d1)}
              in
              case c of {
               (,) l l0 ->
                case seq0 of {
                 (,) seq1 seq2 ->
                  case pp of {
                   Prelude.Left pp0 ->
                    case pp0 of {
                     Specif.Coq_existT pp1 _ ->
                      Logic.eq_rect (List.map (LntT.nslcext g0 d0) ps0)
                        (\acm0 ->
                        Logic.eq_rect_r
                          (Datatypes.app g1 ((:) ((,) ((,) seq1 seq2) d1)
                            pp1)) (\acm1 ->
                          Logic.eq_rect_r
                            (Datatypes.app pp1 ((:) ((,) ((,) l l0) d0) ([])))
                            (DdT.Coq_derI
                            (List.map
                              (LntT.nslcext
                                (Datatypes.app g1 ((:) ((,) ((,) _UU0393_0
                                  _UU0394_') d1) pp1)) d0) ps0)
                            (Datatypes.app g1 ((:) ((,) ((,) _UU0393_0
                              _UU0394_') d1)
                              (Datatypes.app pp1 ((:) ((,) ((,) l l0) d0)
                                ([])))))
                            (unsafeCoerce rs0
                              (List.map
                                (LntT.nslcext
                                  (Datatypes.app g1 ((:) ((,) ((,) _UU0393_0
                                    _UU0394_') d1) pp1)) d0) ps0)
                              (Datatypes.app g1 ((:) ((,) ((,) _UU0393_0
                                _UU0394_') d1)
                                (Datatypes.app pp1 ((:) ((,) ((,) l l0) d0)
                                  ([])))))
                              (let {
                                _evar_0_ = let {
                                            _evar_0_ = LntT.coq_NSlcctxt' ps0
                                                         ((,) l l0)
                                                         (Datatypes.app g1
                                                           ((:) ((,) ((,)
                                                           _UU0393_0
                                                           _UU0394_') d1)
                                                           pp1)) d0 sppc0}
                                           in
                                           Logic.eq_rect_r
                                             (Datatypes.app
                                               (Datatypes.app g1 ((:) ((,)
                                                 ((,) _UU0393_0 _UU0394_') d1)
                                                 pp1)) ((:) ((,) ((,) l l0)
                                               d0) ([]))) _evar_0_
                                             (Datatypes.app g1
                                               (Datatypes.app ((:) ((,) ((,)
                                                 _UU0393_0 _UU0394_') d1) pp1)
                                                 ((:) ((,) ((,) l l0) d0)
                                                 ([]))))}
                               in
                               Logic.eq_rect_r
                                 (Datatypes.app ((:) ((,) ((,) _UU0393_0
                                   _UU0394_') d1) pp1) ((:) ((,) ((,) l l0)
                                   d0) ([]))) _evar_0_ ((:) ((,) ((,)
                                 _UU0393_0 _UU0394_') d1)
                                 (Datatypes.app pp1 ((:) ((,) ((,) l l0) d0)
                                   ([]))))))
                            (let {
                              cs = List.map
                                     (LntT.nslcext
                                       (Datatypes.app g1 ((:) ((,) ((,)
                                         _UU0393_0 _UU0394_') d1) pp1)) d0)
                                     ps0}
                             in
                             case DdT.dersrec_forall cs of {
                              (,) _ x0 ->
                               x0 (\q qin ->
                                 let {
                                  x1 = \f l1 y ->
                                   case GenT.coq_InT_map_iffT f l1 y of {
                                    (,) x1 _ -> x1}}
                                 in
                                 let {
                                  qin0 = x1
                                           (LntT.nslcext
                                             (Datatypes.app g1 ((:) ((,) ((,)
                                               _UU0393_0 _UU0394_') d1) pp1))
                                             d0) ps0 q qin}
                                 in
                                 case qin0 of {
                                  Specif.Coq_existT x2 x3 ->
                                   case x3 of {
                                    (,) _ x4 ->
                                     Logic.eq_rect
                                       (LntT.nslcext
                                         (Datatypes.app g1 ((:) ((,) ((,)
                                           _UU0393_0 _UU0394_') d1) pp1)) d0
                                         x2)
                                       (let {
                                         x5 = \l1 ->
                                          case GenT.coq_ForallT_forall l1 of {
                                           (,) x5 _ -> x5}}
                                        in
                                        let {
                                         acm2 = x5
                                                  (List.map
                                                    (LntT.nslcext
                                                      (Datatypes.app g1 ((:)
                                                        ((,) ((,) seq1 seq2)
                                                        d1) pp1)) d0) ps0)
                                                  acm1
                                                  (LntT.nslcext
                                                    (Datatypes.app g1 ((:)
                                                      ((,) ((,) seq1 seq2) d1)
                                                      pp1)) d0 x2)
                                                  (GenT.coq_InT_map
                                                    (LntT.nslcext
                                                      (Datatypes.app g1 ((:)
                                                        ((,) ((,) seq1 seq2)
                                                        d1) pp1)) d0) ps0 x2
                                                    x4)}
                                        in
                                        let {
                                         x6 = \ns0 ->
                                          case LntacsT.can_gen_swapR_def' ns0 of {
                                           (,) x6 _ -> x6}}
                                        in
                                        let {
                                         acm3 = x6
                                                  (LntT.nslcext
                                                    (Datatypes.app g1 ((:)
                                                      ((,) ((,) seq1 seq2) d1)
                                                      pp1)) d0 x2) acm2 g1
                                                  (Datatypes.app pp1 ((:) ((,)
                                                    x2 d0) ([]))) ((,) seq1
                                                  seq2) _UU0393_0 _UU0394_
                                                  _UU0394_' d1 swap __ __}
                                        in
                                        let {
                                         _evar_0_ = Logic.eq_rect ((:) ((,)
                                                      ((,) _UU0393_0
                                                      _UU0394_') d1)
                                                      (Datatypes.app pp1 ((:)
                                                        ((,) x2 d0) ([]))))
                                                      acm3
                                                      (Datatypes.app ((:) ((,)
                                                        ((,) _UU0393_0
                                                        _UU0394_') d1) pp1)
                                                        ((:) ((,) x2 d0)
                                                        ([])))}
                                        in
                                        Logic.eq_rect
                                          (Datatypes.app g1
                                            (Datatypes.app ((:) ((,) ((,)
                                              _UU0393_0 _UU0394_') d1) pp1)
                                              ((:) ((,) x2 d0) ([]))))
                                          _evar_0_
                                          (Datatypes.app
                                            (Datatypes.app g1 ((:) ((,) ((,)
                                              _UU0393_0 _UU0394_') d1) pp1))
                                            ((:) ((,) x2 d0) ([])))) q}})}))
                            k0) g0 acm0) ps acm};
                   Prelude.Right pp0 ->
                    case pp0 of {
                     Prelude.Left _ ->
                      Logic.eq_rect (List.map (LntT.nslcext g0 d0) ps0)
                        (\acm0 ->
                        Logic.eq_rect_r g0
                          (Logic.eq_rect ([])
                            (Logic.eq_rect_r _UU0393_0 (\_ ->
                              Logic.eq_rect_r _UU0394_ (\_ ->
                                case sppc0 of {
                                 Gen_seq.Sctxt ps1 c0 _UU03a6_1 _UU03a6_2
                                  _UU03a8_1 _UU03a8_2 pr ->
                                  Logic.eq_rect
                                    (List.map
                                      (Gen_seq.seqext _UU03a6_1 _UU03a6_2
                                        _UU03a8_1 _UU03a8_2) ps1) (\_ ->
                                    Logic.eq_rect
                                      (Gen_seq.seqext _UU03a6_1 _UU03a6_2
                                        _UU03a8_1 _UU03a8_2 c0) (\pr0 ->
                                      case c0 of {
                                       (,) l1 l2 ->
                                        Logic.eq_rect
                                          (List.map
                                            (Gen_seq.seqext _UU03a6_1
                                              _UU03a6_2 _UU03a8_1 _UU03a8_2)
                                            ps1) (\acm1 _ ->
                                          Logic.eq_rect
                                            (Datatypes.app _UU03a6_1
                                              (Datatypes.app l1 _UU03a6_2))
                                            (\_ ->
                                            Logic.eq_rect
                                              (Datatypes.app _UU03a8_1
                                                (Datatypes.app l2 _UU03a8_2))
                                              (\_ ->
                                              case swap of {
                                               SwappedT.Coq_swapped_I x0 y a b
                                                c1 d2 ->
                                                Logic.eq_rect_r _UU0394_
                                                  (\_ ->
                                                  Logic.eq_rect_r _UU0394_'
                                                    (\_ _ ->
                                                    Logic.eq_rect_r
                                                      (Datatypes.app a
                                                        (Datatypes.app b
                                                          (Datatypes.app c1
                                                            d2))) (\_ ->
                                                      Logic.eq_rect_r
                                                        (Datatypes.app a
                                                          (Datatypes.app c1
                                                            (Datatypes.app b
                                                              d2)))
                                                        (let {
                                                          pp1 = List_lemmasT.app_eq_appT2
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
                                                         case pp1 of {
                                                          Specif.Coq_existT pp2
                                                           pp3 ->
                                                           case pp3 of {
                                                            Prelude.Left _ ->
                                                             let {
                                                              pp4 = List_lemmasT.app_eq_appT2
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 d2)
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l2
                                                                     _UU03a8_2)}
                                                             in
                                                             case pp4 of {
                                                              Specif.Coq_existT pp5
                                                               pp6 ->
                                                               case pp6 of {
                                                                Prelude.Left _ ->
                                                                 let {
                                                                  pp7 = 
                                                                   List_lemmasT.app_eq_appT2
                                                                     l2
                                                                     _UU03a8_2
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1 d2)}
                                                                 in
                                                                 case pp7 of {
                                                                  Specif.Coq_existT pp8
                                                                   pp9 ->
                                                                   case pp9 of {
                                                                    Prelude.Left _ ->
                                                                     let {
                                                                     pp10 = 
                                                                     List_lemmasT.app_eq_appT2
                                                                     c1 d2 pp8
                                                                     _UU03a8_2}
                                                                     in
                                                                     case pp10 of {
                                                                      Specif.Coq_existT pp11
                                                                     pp12 ->
                                                                     case pp12 of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l1
                                                                     _UU03a6_2))
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (\acm2 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp2 pp5)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp5 pp8)
                                                                     (\pr1 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp8 pp11)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     (\acm3 ->
                                                                     Logic.eq_rect_r
                                                                     d1
                                                                     (\acm4 ->
                                                                     let {
                                                                     qpr = 
                                                                     roe ps1
                                                                     pp5 pp8
                                                                     l1 pr1}
                                                                     in
                                                                     case qpr of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr2 ->
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
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))))
                                                                     d1)
                                                                     ([])))
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
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     a
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp8
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     a
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2))
                                                                     pr2)))
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
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     a
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     a
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     a
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2))
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm5 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1))
                                                                     acm4
                                                                     (LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm5
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l3
                                                                     _UU03a6_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2))))
                                                                     d1
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))
                                                                     a
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp11) d2)
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp11)
                                                                     (Datatypes.app
                                                                     pp2 d2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp11)
                                                                     pp2) d2)
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp11)
                                                                     pp2) d2
                                                                     (let {
                                                                     _evar_0_ = 
                                                                     let {
                                                                     _evar_0_ = 
                                                                     Gen.arg_cong_imp
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp11)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 pp2))
                                                                     (SwappedT.swapped_simpleL
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 pp11)
                                                                     (Datatypes.app
                                                                     l4 pp11))}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 pp2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp11)
                                                                     pp2)}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 pp11))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp11)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp11)
                                                                     (Datatypes.app
                                                                     pp2 d2)))
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2)))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2))))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp8)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp8)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2))))}
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
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp8 pp11)
                                                                     (Datatypes.app
                                                                     pp2 d2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     pp2
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     pp2 ([])))
                                                                     pp5 pr1;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr2 ->
                                                                     let {
                                                                     _evar_0_ = \pr3 ->
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
                                                                     a pp11)
                                                                     pp2) d2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp5 d2)))
                                                                     d1)
                                                                     ([])))
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
                                                                     a pp11)
                                                                     pp2) d2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp5 d2)))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2) d2)
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp5 d2)))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp5
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2) d2
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
                                                                     a pp11)
                                                                     pp2) d2)
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2) d2)
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2) d2)
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2) d2
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm5 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1))
                                                                     acm4
                                                                     (LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm5
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l3
                                                                     _UU03a6_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     l4 d2))
                                                                     d1
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 d2)))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 d2))))
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 d2)))
                                                                     a
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp11) d2)
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp11 pp2)
                                                                     (Datatypes.app
                                                                     l4 d2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp11 pp2)
                                                                     l4) d2)
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp11 pp2)
                                                                     l4) d2
                                                                     (let {
                                                                     _evar_0_ = 
                                                                     let {
                                                                     _evar_0_ = 
                                                                     Gen.arg1_cong_imp
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 pp11))
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 l4))
                                                                     (SwappedT.swapped_simpleR
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     (Datatypes.app
                                                                     pp2 l4))}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2 l4))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp11 pp2)
                                                                     l4)}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 pp11))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp11)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp11 pp2)
                                                                     (Datatypes.app
                                                                     l4 d2)))
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 d2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2)))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 d2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     l4 d2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp5 d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2) pp5)
                                                                     d2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2) pp5)
                                                                     d2)
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp5 d2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp5 d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp5 d2)))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp11)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp5 d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp5 d2))))}
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
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp5 d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 pp5)
                                                                     d2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     pp5
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     pp5 ([]))
                                                                     pr2) pp8
                                                                     pr1}) d0
                                                                     acm3)
                                                                     _UU03a8_2
                                                                     acm2) c1)
                                                                     l2 pr0) b)
                                                                     _UU03a8_1
                                                                     acm1)
                                                                     _UU0393_0;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l1
                                                                     _UU03a6_2))
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (\acm2 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp2 pp5)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp5 pp8)
                                                                     (\pr1 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     c1 pp11)
                                                                     (\pr2 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)
                                                                     (Logic.eq_rect_r
                                                                     d1
                                                                     (\acm3 ->
                                                                     let {
                                                                     qpr = 
                                                                     roe ps1
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1 pp11)
                                                                     l1 pr2}
                                                                     in
                                                                     case qpr of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr3 ->
                                                                     let {
                                                                     _evar_0_ = 
                                                                     let {
                                                                     qpr0 = 
                                                                     roe ps1
                                                                     c1 pp11
                                                                     l1 pr3}
                                                                     in
                                                                     case qpr0 of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr4 ->
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
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
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
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp11
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
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
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm4 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1))
                                                                     acm3
                                                                     (LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm4
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l3
                                                                     _UU03a6_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     d1
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (SwappedT.swapped_same
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     pp11)
                                                                     _UU03a8_2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     pp11)
                                                                     _UU03a8_2)
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp11
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
                                                                     c1 pr3;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr4 ->
                                                                     let {
                                                                     _evar_0_ = \pr5 ->
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
                                                                     pp2
                                                                     _UU03a8_2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     pp2
                                                                     _UU03a8_2))))
                                                                     d1)
                                                                     ([])))
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
                                                                     pp2
                                                                     _UU03a8_2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     pp2
                                                                     _UU03a8_2))))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2))
                                                                     ps1) ((,)
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
                                                                     pp2
                                                                     _UU03a8_2))))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1 c1
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2)
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
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2))
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2))
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2))
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2)
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm4 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1))
                                                                     acm3
                                                                     (LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm4
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l3
                                                                     _UU03a6_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2)))
                                                                     d1
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2))
                                                                     a
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     _UU03a8_2)
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp2)
                                                                     _UU03a8_2)
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     (Datatypes.app
                                                                     l4 pp2)
                                                                     _UU03a8_2
                                                                     (Gen.arg_cong_imp
                                                                     (Datatypes.app
                                                                     l4 pp2)
                                                                     (Datatypes.app
                                                                     l4 pp2)
                                                                     (SwappedT.swapped_simpleL
                                                                     pp2 l4
                                                                     l4)))
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp2
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
                                                                     c1 ([]))
                                                                     pr4) pp11
                                                                     pr3}}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     pp2
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     pp2 ([])))
                                                                     pp5 pr2;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr3 ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr4 ->
                                                                     let {
                                                                     _evar_0_ = \pr5 ->
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
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp5
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
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
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp5
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp5
                                                                     _UU03a8_2)))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp5
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
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
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm4 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1))
                                                                     acm3
                                                                     (LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2)
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm4
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l3
                                                                     _UU03a6_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     d1
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (SwappedT.swapped_same
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp5
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     pp5)
                                                                     _UU03a8_2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     pp5)
                                                                     _UU03a8_2)
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp5
                                                                     _UU03a8_2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp5
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp5
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
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp5
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 pp5)
                                                                     _UU03a8_2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     pp5
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     pp5 ([]))
                                                                     pr4) pp11
                                                                     pr3) c1
                                                                     pr2}) d0
                                                                     acm2) d2)
                                                                     pp8 pr1)
                                                                     l2 pr0) b)
                                                                     _UU03a8_1
                                                                     acm1)
                                                                     _UU0393_0}};
                                                                    Prelude.Right _ ->
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l1
                                                                     _UU03a6_2))
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (\acm2 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp2 pp5)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     l2 pp8)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp8
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
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     d1)
                                                                     ([])))
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
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1 l2
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp8 d2)
                                                                     pr0)))
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
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp8 d2)
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm5 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp8
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
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm5
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     ((,) l3
                                                                     l4))
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l3
                                                                     _UU03a6_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     d1
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2)))))
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))))
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     a
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp8) c1)
                                                                     d2)
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp2)
                                                                     l4)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp2)
                                                                     l4) pp8)
                                                                     d2)
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp8) c1)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp2)
                                                                     l4) pp8)
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
                                                                     pp2 l4)
                                                                     pp8) c1)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 c1)))
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 pp8)))
                                                                     (SwappedT.swapped_simpleR
                                                                     c1
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 pp8)))}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4 pp8)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp2)
                                                                     (Datatypes.app
                                                                     l4 pp8))}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp2)
                                                                     (Datatypes.app
                                                                     l4 pp8))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp2)
                                                                     l4) pp8)}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 c1)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     (Datatypes.app
                                                                     pp8 c1))}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     (Datatypes.app
                                                                     pp8 c1))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp8) c1)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp2)
                                                                     l4)
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2)))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2 l4)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))))
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2)))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2) l2)
                                                                     (Datatypes.app
                                                                     pp8 d2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2) l2)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp8 d2)))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp8 d2))))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp8 d2)))))}
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
                                                                     pp8 d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l2 pp8)
                                                                     d2)}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l2 pp8)
                                                                     d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     l2 pp8))
                                                                     d2)) d0
                                                                     acm3)
                                                                     _UU03a8_2
                                                                     acm2)
                                                                     pp5) b)
                                                                     _UU03a8_1
                                                                     acm1)
                                                                     _UU0393_0}};
                                                                Prelude.Right _ ->
                                                                 let {
                                                                  pp7 = 
                                                                   List_lemmasT.app_eq_appT2
                                                                     c1 d2 pp5
                                                                     (Datatypes.app
                                                                     l2
                                                                     _UU03a8_2)}
                                                                 in
                                                                 case pp7 of {
                                                                  Specif.Coq_existT pp8
                                                                   pp9 ->
                                                                   case pp9 of {
                                                                    Prelude.Left _ ->
                                                                     let {
                                                                     pp10 = 
                                                                     List_lemmasT.app_eq_appT2
                                                                     l2
                                                                     _UU03a8_2
                                                                     pp8 d2}
                                                                     in
                                                                     case pp10 of {
                                                                      Specif.Coq_existT pp11
                                                                     pp12 ->
                                                                     case pp12 of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l1
                                                                     _UU03a6_2))
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (\acm2 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (\acm3 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp5 pp8)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp8 pp11)
                                                                     (\pr1 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)
                                                                     (Logic.eq_rect_r
                                                                     d1
                                                                     (\acm4 ->
                                                                     let {
                                                                     qpr = 
                                                                     roe ps1
                                                                     pp8 pp11
                                                                     l1 pr1}
                                                                     in
                                                                     case qpr of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr2 ->
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
                                                                     a pp5) b)
                                                                     _UU03a8_2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
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
                                                                     a pp5) b)
                                                                     _UU03a8_2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     _UU03a8_2)
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp11
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     _UU03a8_2
                                                                     pr2)))
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
                                                                     a pp5) b)
                                                                     _UU03a8_2)
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     _UU03a8_2)
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     _UU03a8_2)
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm5 = 
                                                                     x10
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
                                                                     b pp5))
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
                                                                     b pp5))
                                                                     _UU03a8_2
                                                                     x7))
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
                                                                     b pp5))
                                                                     _UU03a8_2)
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     _UU03a8_2)
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
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
                                                                     b pp5))
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm5
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l3
                                                                     _UU03a6_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     d1
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     a
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     l4)
                                                                     _UU03a8_2)
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 b)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 b)
                                                                     l4)
                                                                     _UU03a8_2)
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     l4)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 b)
                                                                     l4)
                                                                     _UU03a8_2
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     pp5 b) l4
                                                                     (Gen.arg_cong_imp
                                                                     (Datatypes.app
                                                                     pp5 b)
                                                                     (Datatypes.app
                                                                     pp5 b)
                                                                     (SwappedT.swapped_simpleL
                                                                     b pp5
                                                                     pp5))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 b)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     pp11)
                                                                     _UU03a8_2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     pp11)
                                                                     _UU03a8_2)
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5) b)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp11
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
                                                                     pp5
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     pp5 ([])))
                                                                     pp8 pr1;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr2 ->
                                                                     let {
                                                                     _evar_0_ = \pr3 ->
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
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))))
                                                                     d1)
                                                                     ([])))
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
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp8
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2)
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
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2)
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm5 = 
                                                                     x10
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
                                                                     b pp5))
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
                                                                     b pp5))
                                                                     _UU03a8_2
                                                                     x7))
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
                                                                     b pp5))
                                                                     _UU03a8_2)
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     _UU03a8_2)
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
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
                                                                     b pp5))
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm5
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l3
                                                                     _UU03a6_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
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
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))))
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2)))
                                                                     a
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     l4)
                                                                     _UU03a8_2)
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     b)
                                                                     _UU03a8_2)
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     l4)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     b)
                                                                     _UU03a8_2
                                                                     (let {
                                                                     _evar_0_ = 
                                                                     let {
                                                                     _evar_0_ = 
                                                                     Gen.arg_cong_imp
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     b)
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4 b))
                                                                     (SwappedT.swapped_simpleL
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     (Datatypes.app
                                                                     pp5 l4))}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4 b))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     b)}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5 l4))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     l4)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2)))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     pp8
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 pp8)
                                                                     (Datatypes.app
                                                                     b
                                                                     _UU03a8_2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     pp8
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     pp8 ([]))
                                                                     pr2) pp11
                                                                     pr1}) d0
                                                                     acm3) d2)
                                                                     l2 pr0)
                                                                     c1) pp2
                                                                     acm2)
                                                                     _UU03a8_1
                                                                     acm1)
                                                                     _UU0393_0;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l1
                                                                     _UU03a6_2))
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (\acm2 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (\acm3 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp5 pp8)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     l2 pp11)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp11 d2)
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
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))))
                                                                     d1)
                                                                     ([])))
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
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1 l2
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2))
                                                                     pr0)))
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
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2))
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm6 = 
                                                                     x10
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
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     pp11 d2))
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
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7))
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
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
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
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm6
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l3
                                                                     _UU03a6_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     d1
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))))
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     a
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     l4)
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     l4) pp11)
                                                                     d2)
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     b d2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     pp11) b)
                                                                     d2)
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     l4) pp11)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     pp11) b)
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
                                                                     pp5 l4)
                                                                     pp11) b)
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 b)))
                                                                     (SwappedT.swapped_simpleL
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4 pp11))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     pp11))}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 b)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     (Datatypes.app
                                                                     pp11 b))}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     (Datatypes.app
                                                                     pp11 b))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     pp11) b)}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4 pp11)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4 pp11))}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4 pp11))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     l4) pp11)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 l4)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     l4)
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b pp5))
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     l2)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     l2)
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2))))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a pp5)
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp11
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
                                                                     pp11
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l2 pp11)
                                                                     (Datatypes.app
                                                                     b d2))}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l2 pp11)
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     l2 pp11))
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     d0 acm4)
                                                                     _UU03a8_2
                                                                     acm3)
                                                                     pp8) c1)
                                                                     pp2 acm2)
                                                                     _UU03a8_1
                                                                     acm1)
                                                                     _UU0393_0}};
                                                                    Prelude.Right _ ->
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l1
                                                                     _UU03a6_2))
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     a pp2)
                                                                     (\acm2 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     b pp5)
                                                                     (\acm3 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     c1 pp8)
                                                                     (\acm4 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp8
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
                                                                     pp8)
                                                                     _UU03a8_2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     l2
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
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
                                                                     pp8)
                                                                     _UU03a8_2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     l2
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1) b)
                                                                     pp8)
                                                                     _UU03a8_2)
                                                                     ps1) ((,)
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
                                                                     pp8)
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
                                                                     pp8)
                                                                     _UU03a8_2
                                                                     pr0)))
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
                                                                     pp8)
                                                                     _UU03a8_2)
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
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
                                                                     pp8)
                                                                     _UU03a8_2)
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1) b)
                                                                     pp8)
                                                                     _UU03a8_2)
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1) b)
                                                                     pp8)
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm6 = 
                                                                     x10
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
                                                                     c1 pp8)))
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
                                                                     c1 pp8)))
                                                                     _UU03a8_2
                                                                     x7))
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
                                                                     c1 pp8)))
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
                                                                     c1 pp8)))
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 pp8)))
                                                                     _UU03a8_2)
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
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
                                                                     c1 pp8)))
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm6
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 pp8)))
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))
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
                                                                     c1 pp8)))
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1) b)
                                                                     pp8)
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
                                                                     c1 pp8))
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp8)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1) b)
                                                                     (Datatypes.app
                                                                     pp8
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
                                                                     pp8
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
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))))
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))
                                                                     a
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b c1)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b c1)
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b c1)
                                                                     pp8) l4)
                                                                     _UU03a8_2)
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 b)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 b)
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 b)
                                                                     pp8) l4)
                                                                     _UU03a8_2)
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b c1)
                                                                     pp8) l4)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 b)
                                                                     pp8) l4)
                                                                     _UU03a8_2
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b c1)
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 b)
                                                                     pp8) l4
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     b c1)
                                                                     (Datatypes.app
                                                                     c1 b) pp8
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
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 b)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b c1)
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b c1)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1)
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1) b)
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1) b)
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp8)
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 pp8))
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 pp8)))
                                                                     (Datatypes.app
                                                                     l4
                                                                     _UU03a8_2)))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1) b)
                                                                     pp8)
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
                                                                     pp8) l2)
                                                                     _UU03a8_2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1) b)
                                                                     pp8) l2)
                                                                     _UU03a8_2)
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1) b)
                                                                     pp8)
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
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     l2
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     a c1) b)
                                                                     (Datatypes.app
                                                                     pp8
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
                                                                     pp8
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
                                                                     pp8
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
                                                                     pp8
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
                                                                     pp8
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
                                                                     d2) pp5
                                                                     acm3) pp2
                                                                     acm2)
                                                                     _UU03a8_1
                                                                     acm1)
                                                                     _UU0393_0}}}};
                                                            Prelude.Right _ ->
                                                             let {
                                                              pp4 = List_lemmasT.app_eq_appT2
                                                                     l2
                                                                     _UU03a8_2
                                                                     pp2
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 d2))}
                                                             in
                                                             case pp4 of {
                                                              Specif.Coq_existT pp5
                                                               pp6 ->
                                                               case pp6 of {
                                                                Prelude.Left _ ->
                                                                 let {
                                                                  pp7 = 
                                                                   List_lemmasT.app_eq_appT2
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 d2)
                                                                     pp5
                                                                     _UU03a8_2}
                                                                 in
                                                                 case pp7 of {
                                                                  Specif.Coq_existT pp8
                                                                   pp9 ->
                                                                   case pp9 of {
                                                                    Prelude.Left _ ->
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l1
                                                                     _UU03a6_2))
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp2 pp5)
                                                                     (\pr1 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp5 pp8)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     (\acm2 ->
                                                                     Logic.eq_rect_r
                                                                     d1
                                                                     (\acm3 ->
                                                                     let {
                                                                     qpr = 
                                                                     roe ps1
                                                                     pp2 pp5
                                                                     l1 pr1}
                                                                     in
                                                                     case qpr of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr2 ->
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
                                                                     pp8 d2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     d1)
                                                                     ([])))
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
                                                                     pp8 d2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     c1)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     ps1) ((,)
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp5
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     c1)
                                                                     (Datatypes.app
                                                                     pp8 d2)
                                                                     pr2)))
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
                                                                     pp8 d2))
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
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
                                                                     pp8 d2))
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     c1)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     c1)
                                                                     (Datatypes.app
                                                                     pp8 d2)
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm4 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
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
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm4
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     ((,) l3
                                                                     l4))
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
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     c1)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     d1
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     _UU03a8_1
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp8)
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp8)
                                                                     c1) d2)
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 l4)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 l4)
                                                                     pp8) d2)
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp8)
                                                                     c1)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 l4)
                                                                     pp8) d2
                                                                     (let {
                                                                     _evar_0_ = 
                                                                     let {
                                                                     _evar_0_ = 
                                                                     Gen.arg1_cong_imp
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp8)
                                                                     c1)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 c1))
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     l4 pp8))
                                                                     (SwappedT.swapped_simpleR
                                                                     c1
                                                                     (Datatypes.app
                                                                     l4 pp8)
                                                                     (Datatypes.app
                                                                     l4 pp8))}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     l4 pp8))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 l4)
                                                                     pp8)}
                                                                     in
                                                                     Logic.eq_rec
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 c1))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp8)
                                                                     c1)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 l4)
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp8)
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     c1)
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     c1)
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     c1) pp5)
                                                                     (Datatypes.app
                                                                     pp8 d2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     c1) pp5)
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     c1)
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     pp8 d2)))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     c1)
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     pp8 d2))))}
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp5 pp8)
                                                                     d2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     _UU03a8_1
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     ([])))
                                                                     pp2 pr1;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr2 ->
                                                                     let {
                                                                     _evar_0_ = \pr3 ->
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
                                                                     pp8 d2)))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2)))))
                                                                     d1)
                                                                     ([])))
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
                                                                     pp8 d2)))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2)))))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2)))))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp2
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2))
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
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
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
                                                                     pp8 d2)))
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm4 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
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
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm4
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     ((,) l3
                                                                     l4))
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
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))))
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     d1
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     _UU03a8_1
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2))
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2))
                                                                     l4
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp8 c1)
                                                                     d2)
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     c1 pp8)
                                                                     d2)
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     pp8 c1)
                                                                     (Datatypes.app
                                                                     c1 pp8)
                                                                     d2
                                                                     (Gen.arg_cong_imp
                                                                     (Datatypes.app
                                                                     c1 pp8)
                                                                     (Datatypes.app
                                                                     c1 pp8)
                                                                     (SwappedT.swapped_simpleL
                                                                     pp8 c1
                                                                     c1)))
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     c1 d2)))))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2)))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2))))}
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
                                                                     pp2
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2))))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     pp8 d2)))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     pp2
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     pp2 ([]))
                                                                     pr2) pp5
                                                                     pr1}) d0
                                                                     acm2)
                                                                     _UU03a8_2
                                                                     acm1) b)
                                                                     l2 pr0)
                                                                     a)
                                                                     _UU0393_0;
                                                                    Prelude.Right _ ->
                                                                     let {
                                                                     pp10 = 
                                                                     List_lemmasT.app_eq_appT2
                                                                     c1 d2 pp8
                                                                     _UU03a8_2}
                                                                     in
                                                                     case pp10 of {
                                                                      Specif.Coq_existT pp11
                                                                     pp12 ->
                                                                     case pp12 of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l1
                                                                     _UU03a6_2))
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp2 pp5)
                                                                     (\pr1 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     b pp8)
                                                                     (\pr2 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp8 pp11)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     (\acm2 ->
                                                                     Logic.eq_rect_r
                                                                     d1
                                                                     (\acm3 ->
                                                                     let {
                                                                     qpr = 
                                                                     roe ps1
                                                                     pp2
                                                                     (Datatypes.app
                                                                     b pp8) l1
                                                                     pr2}
                                                                     in
                                                                     case qpr of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr3 ->
                                                                     let {
                                                                     _evar_0_ = 
                                                                     let {
                                                                     qpr0 = 
                                                                     roe ps1 b
                                                                     pp8 l1
                                                                     pr3}
                                                                     in
                                                                     case qpr0 of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr4 ->
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
                                                                     pp11 d2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     d1)
                                                                     ([])))
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
                                                                     pp11 d2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp8
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
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
                                                                     pp11 d2))
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm4 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1))
                                                                     acm3
                                                                     (LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm4
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))
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
                                                                     pp11 d2)))
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     d1
                                                                     (SwappedT.swapped_same
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     pp11 d2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp8)
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11 d2)))}
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
                                                                     pp8
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp8 pp11)
                                                                     d2)) b
                                                                     pr3;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr4 ->
                                                                     let {
                                                                     _evar_0_ = \pr5 ->
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
                                                                     pp11) d2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     d1)
                                                                     ([])))
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
                                                                     pp11) d2)
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11) d2)
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1 b
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11) d2
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
                                                                     _UU03a8_1
                                                                     pp11) d2)
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11) d2)
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11) d2)
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11) d2
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm4 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1))
                                                                     acm3
                                                                     (LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm4
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))
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
                                                                     pp11 d2)))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     l4 d2))
                                                                     d1
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     l4 d2)))
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     l4 d2))
                                                                     _UU03a8_1
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l4 pp11)
                                                                     d2)
                                                                     (Logic.eq_rec_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     pp11 l4)
                                                                     d2)
                                                                     (SwappedT.swapped_R
                                                                     (Datatypes.app
                                                                     l4 pp11)
                                                                     (Datatypes.app
                                                                     pp11 l4)
                                                                     d2
                                                                     (Gen.arg_cong_imp
                                                                     (Datatypes.app
                                                                     pp11 l4)
                                                                     (Datatypes.app
                                                                     pp11 l4)
                                                                     (SwappedT.swapped_simpleL
                                                                     l4 pp11
                                                                     pp11)))
                                                                     (Datatypes.app
                                                                     pp11
                                                                     (Datatypes.app
                                                                     l4 d2)))
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     l4 d2)))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     b d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11) b)
                                                                     d2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11) b)
                                                                     d2)
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     b d2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11)
                                                                     (Datatypes.app
                                                                     b d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11
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
                                                                     b ([]))
                                                                     pr4) pp8
                                                                     pr3}}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     _UU03a8_1
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     ([])))
                                                                     pp2 pr2;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr3 ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr4 ->
                                                                     let {
                                                                     _evar_0_ = \pr5 ->
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
                                                                     pp11 d2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     d1)
                                                                     ([])))
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
                                                                     pp11 d2))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp2
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
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
                                                                     pp11 d2))
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm4 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1))
                                                                     acm3
                                                                     (LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1)
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm4
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11 d2)
                                                                     ((,) l3
                                                                     l4))
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
                                                                     pp11 d2)))
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     d1
                                                                     (SwappedT.swapped_same
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp11 d2))))
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp11 d2)))}
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
                                                                     pp2
                                                                     (Datatypes.app
                                                                     pp11 d2)))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     (Datatypes.app
                                                                     pp11 d2))}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     pp2
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     pp2 ([]))
                                                                     pr4) pp8
                                                                     pr3) b
                                                                     pr2}) d0
                                                                     acm2)
                                                                     _UU03a8_2
                                                                     acm1) c1)
                                                                     pp5 pr1)
                                                                     l2 pr0)
                                                                     a)
                                                                     _UU0393_0;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l1
                                                                     _UU03a6_2))
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp2 pp5)
                                                                     (\pr1 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     b pp8)
                                                                     (\pr2 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     c1 pp11)
                                                                     (\pr3 ->
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)
                                                                     (Logic.eq_rect_r
                                                                     d1
                                                                     (\acm2 ->
                                                                     let {
                                                                     qpr = 
                                                                     roe ps1
                                                                     pp2
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 pp11))
                                                                     l1 pr3}
                                                                     in
                                                                     case qpr of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr4 ->
                                                                     let {
                                                                     _evar_0_ = 
                                                                     let {
                                                                     qpr0 = 
                                                                     roe ps1 b
                                                                     (Datatypes.app
                                                                     c1 pp11)
                                                                     l1 pr4}
                                                                     in
                                                                     case qpr0 of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr5 ->
                                                                     let {
                                                                     qpr1 = 
                                                                     roe ps1
                                                                     c1 pp11
                                                                     l1 pr5}
                                                                     in
                                                                     case qpr1 of {
                                                                      Prelude.Left _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr6 ->
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
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
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
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2)))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp11
                                                                     _UU03a6_1
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
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
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
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm3 = 
                                                                     x10
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
                                                                     x7))
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
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm3
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))
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
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11)
                                                                     _UU03a8_2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp11)
                                                                     _UU03a8_2)
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp11
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
                                                                     c1 pr5;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr6 ->
                                                                     let {
                                                                     _evar_0_ = \pr7 ->
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
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     ([])))
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
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1) ((,)
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
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
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
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm3 = 
                                                                     x10
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
                                                                     x7))
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
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm3
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))
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
                                                                     __ __}})
                                                                     x3) q}}}})})}
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
                                                                     c1 ([]))
                                                                     pr6) pp11
                                                                     pr5}) b
                                                                     pr4;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr5 ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr6 ->
                                                                     let {
                                                                     _evar_0_ = \pr7 ->
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
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     ([])))
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
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1) ((,)
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
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
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
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm3 = 
                                                                     x10
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
                                                                     x7))
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
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm3
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))
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
                                                                     __ __}})
                                                                     x3) q}}}})})}
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
                                                                     b ([]))
                                                                     pr6) pp11
                                                                     pr5) c1
                                                                     pr4}}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     _UU03a8_1
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     ([])))
                                                                     pp2 pr3;
                                                                      Prelude.Right _ ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr4 ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr5 ->
                                                                     Logic.eq_rect_r
                                                                     ([])
                                                                     (\pr6 ->
                                                                     let {
                                                                     _evar_0_ = \pr7 ->
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
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
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
                                                                     g0 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2)))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a6_1
                                                                     l1)
                                                                     _UU03a6_2)
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2)))
                                                                     g0 d1
                                                                     (Gen_seq.coq_Sctxt_e'
                                                                     ps1 l1
                                                                     pp2
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
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
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
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm3 = 
                                                                     x10
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
                                                                     x7))
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
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2)
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm3
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     _UU03a8_2
                                                                     ((,) l3
                                                                     l4))
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
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     _UU03a8_2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     _UU03a8_2)
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp2
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
                                                                     pp2
                                                                     _UU03a8_2))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     _UU03a8_2)}
                                                                     in
                                                                     Logic.eq_rect_r
                                                                     pp2
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     pp2 ([]))
                                                                     pr6) pp11
                                                                     pr5) c1
                                                                     pr4) b
                                                                     pr3}) d0
                                                                     acm1) d2)
                                                                     pp8 pr2)
                                                                     pp5 pr1)
                                                                     l2 pr0)
                                                                     a)
                                                                     _UU0393_0}}}};
                                                                Prelude.Right _ ->
                                                                 Logic.eq_rect
                                                                   (Datatypes.app
                                                                     _UU03a6_1
                                                                     (Datatypes.app
                                                                     l1
                                                                     _UU03a6_2))
                                                                   (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     pp2)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     l2 pp5)
                                                                     (Logic.eq_rect_r
                                                                     (Datatypes.app
                                                                     pp5
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))))
                                                                     d1)
                                                                     ([])))
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     ps1))
                                                                     (Datatypes.app
                                                                     g0 ((:)
                                                                     ((,) ((,)
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))))
                                                                     d1)
                                                                     ([])))
                                                                     (LntT.coq_NSlcctxt'
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     ps1) ((,)
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
                                                                     pp5
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     pr0)))
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     ps1)}
                                                                     in
                                                                     case 
                                                                     DdT.dersrec_forall
                                                                     cs of {
                                                                      (,) _
                                                                     x1 ->
                                                                     x1
                                                                     (\q qin ->
                                                                     let {
                                                                     x2 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x2
                                                                     _ -> x2}}
                                                                     in
                                                                     let {
                                                                     qin0 = 
                                                                     x2
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     ps1) q
                                                                     qin}
                                                                     in
                                                                     case qin0 of {
                                                                      Specif.Coq_existT x3
                                                                     x4 ->
                                                                     case x4 of {
                                                                      (,) _
                                                                     x5 ->
                                                                     let {
                                                                     x6 = \f l3 y0 ->
                                                                     case 
                                                                     GenT.coq_InT_map_iffT
                                                                     f l3 y0 of {
                                                                      (,) x6
                                                                     _ -> x6}}
                                                                     in
                                                                     let {
                                                                     inmps = 
                                                                     x6
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     ps1 x3 x5}
                                                                     in
                                                                     case inmps of {
                                                                      Specif.Coq_existT x7
                                                                     x8 ->
                                                                     case x8 of {
                                                                      (,) _
                                                                     x9 ->
                                                                     Logic.eq_rect
                                                                     (LntT.nslcext
                                                                     g0 d1 x3)
                                                                     (Logic.eq_rect
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2)))
                                                                     x7)
                                                                     (let {
                                                                     x10 = \l3 ->
                                                                     case 
                                                                     GenT.coq_ForallT_forall
                                                                     l3 of {
                                                                      (,) x10
                                                                     _ -> x10}}
                                                                     in
                                                                     let {
                                                                     acm4 = 
                                                                     x10
                                                                     (List.map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp5
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     x7))
                                                                     (GenT.coq_InT_map
                                                                     (LntT.nslcext
                                                                     g0 d1)
                                                                     (List.map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp5
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     x7)
                                                                     (GenT.coq_InT_map
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 d2))))
                                                                     ps1 x7
                                                                     x9))}
                                                                     in
                                                                     case x7 of {
                                                                      (,) l3
                                                                     l4 ->
                                                                     let {
                                                                     ns0 = 
                                                                     LntT.nslcext
                                                                     g0 d1
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     ((,) l3
                                                                     l4))}
                                                                     in
                                                                     case 
                                                                     LntacsT.can_gen_swapR_def'
                                                                     ns0 of {
                                                                      (,) x11
                                                                     _ ->
                                                                     x11 acm4
                                                                     g0 ([])
                                                                     (Gen_seq.seqext
                                                                     _UU03a6_1
                                                                     _UU03a6_2
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     ((,) l3
                                                                     l4))
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 d2)))))
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2)))))
                                                                     d1
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 d2))))
                                                                     (Datatypes.app
                                                                     l4
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     _UU03a8_1
                                                                     (SwappedT.swapped_L
                                                                     (Datatypes.app
                                                                     pp5
                                                                     (Datatypes.app
                                                                     b
                                                                     (Datatypes.app
                                                                     c1 d2)))
                                                                     (Datatypes.app
                                                                     pp5
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
                                                                     pp5
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
                                                                     __ __}})
                                                                     x3) q}}}})})}
                                                                     in
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     l2
                                                                     (Datatypes.app
                                                                     pp5
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
                                                                     pp5
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
                                                                     pp5
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
                                                                     pp5
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
                                                                     pp5
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     l2 pp5)
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
                                                                     l2 pp5)
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     _evar_0_
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU03a8_1
                                                                     (Datatypes.app
                                                                     l2 pp5))
                                                                     (Datatypes.app
                                                                     c1
                                                                     (Datatypes.app
                                                                     b d2))))
                                                                     d0 acm2)
                                                                     _UU03a8_2
                                                                     acm1)
                                                                     pp2) a)
                                                                   _UU0393_0}}}})
                                                        _UU0394_') _UU0394_ __)
                                                    y) x0 __ __ __}) l0 __) l
                                            __) ps0 acm0 sppc0}) ((,) l l0))
                                    ps0 __ pr}) seq2 __) seq1 __) k0) g1) ps
                        acm;
                     Prelude.Right pp1 ->
                      Logic.eq_rect (List.map (LntT.nslcext g0 d0) ps0) (\_ ->
                        Logic.eq_rect_r
                          (Datatypes.app g0 ((:) ((,) ((,) l l0) d0) pp1))
                          Logic.coq_False_rect g1) ps acm}}}})}) concl) ps __
        sppc}) __ nsr rs g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4
    _UU0393_ __ __

gen_swapR_step_pr_lc :: (([])
                        (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir))) -> (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) -> a2 -> (DdT.Coq_dersrec
                        (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) a3 ()) -> (GenT.ForallT
                        (([])
                        ((,)
                        ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) (LntacsT.Coq_can_gen_swapR a1 a3)) ->
                        (Gen.Coq_rsub
                        (([])
                        (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)))
                        (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) a2 a3) -> (([])
                        ((,)
                        ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) -> (([])
                        ((,)
                        ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) -> ((,) (([]) (LntT.PropF a1))
                        (([]) (LntT.PropF a1))) -> LntT.Coq_dir -> (([])
                        (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                        (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                        (LntT.PropF a1)) -> DdT.Coq_derrec
                        (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) a3 ()
gen_swapR_step_pr_lc ps concl x x0 x1 x2 g k seq d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ =
  gen_swapR_step_roe_lc ps concl LntT.princrule_pfc_R_oe'T x x0 x1 x2 g k seq
    d _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_

