{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Cut where

import qualified Prelude
import qualified Datatypes
import qualified Lemma_Sixteen
import qualified List
import qualified Logic
import qualified Nat
import qualified Specif
import qualified DdT
import qualified Dd_fc
import qualified Gen_tacs
import qualified Ind_lex
import qualified LntT
import qualified Lnt_contraction_mrT
import qualified Lntkt_exchT
import qualified Merge
import qualified Size
import qualified Structural_equivalence

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

coq_LNSKt_cut_admissibility :: (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) -> (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) -> (DdT.Coq_derrec
                               (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules a1) ()) ->
                               (DdT.Coq_derrec
                               (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules a1) ()) ->
                               (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                               (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                               (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                               (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                               (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) -> (Datatypes.Coq_prod
                               (Datatypes.Coq_list (LntT.PropF a1))
                               (Datatypes.Coq_list (LntT.PropF a1))) ->
                               (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1))
                               (Datatypes.Coq_list (LntT.PropF a1))) -> LntT.Coq_dir ->
                               (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                               (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                               (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                               (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                               (LntT.PropF a1) -> (Merge.Coq_merge a1) ->
                               (Structural_equivalence.Coq_struct_equiv_str a1) ->
                               DdT.Coq_derrec
                               (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules a1) ()
coq_LNSKt_cut_admissibility ns1 ns2 d1 d2 g1 g2 g3 seq1 seq2 d _UU0393_ _UU0394_1 _UU0394_2 _UU03a3_1 _UU03a3_2 _UU03a0_ a x h3 =
  let {
   p = Lemma_Sixteen.coq_Lemma_Sixteen (Datatypes.Coq_pair (Size.fsize a)
         (Nat.add (Dd_fc.dp ns1 d1) (Dd_fc.dp ns2 d2)))}
  in
  case p of {
   Datatypes.Coq_pair p0 x0 ->
    (case p0 of {
      Datatypes.Coq_pair p1 x1 ->
       (case p1 of {
         Datatypes.Coq_pair lS1 lS2 -> (\lS3 lS4 ->
          Logic.eq_rect_r
            (Datatypes.app g1 (Datatypes.Coq_cons (Datatypes.Coq_pair seq1 d)
              Datatypes.Coq_nil)) (\d3 lS5 lS6 lS7 lS8 ->
            Logic.eq_rect_r (Datatypes.Coq_pair _UU0393_
              (Datatypes.app _UU0394_1
                (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil) _UU0394_2)))
              (\d4 lS9 lS10 lS11 lS12 ->
              Logic.eq_rect_r
                (Datatypes.app g2 (Datatypes.Coq_cons (Datatypes.Coq_pair seq2 d)
                  Datatypes.Coq_nil)) (\d5 lS13 lS14 lS15 lS16 ->
                Logic.eq_rect_r (Datatypes.Coq_pair
                  (Datatypes.app _UU03a3_1
                    (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil) _UU03a3_2))
                  _UU03a0_) (\d6 lS17 _ _ _ ->
                  Logic.eq_rect
                    (Datatypes.app
                      (Datatypes.app g3 (Datatypes.Coq_cons (Datatypes.Coq_pair
                        (Datatypes.Coq_pair
                        (Datatypes.app _UU0393_ (Datatypes.app _UU03a3_1 _UU03a3_2))
                        (Datatypes.app _UU0394_1 (Datatypes.app _UU0394_2 _UU03a0_))) d)
                        Datatypes.Coq_nil)) Datatypes.Coq_nil)
                    (Logic.eq_rect
                      (Datatypes.app g3
                        (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                          (Datatypes.Coq_pair
                          (Datatypes.app _UU0393_ (Datatypes.app _UU03a3_1 _UU03a3_2))
                          (Datatypes.app _UU0394_1 (Datatypes.app _UU0394_2 _UU03a0_))) d)
                          Datatypes.Coq_nil) Datatypes.Coq_nil))
                      (unsafeCoerce lS17 __ g1 _UU0393_ _UU0394_1 _UU0394_2 g2 _UU03a3_1
                        _UU03a3_2 _UU03a0_ Datatypes.Coq_nil g3 a d d4 d6 __ __ h3 x)
                      (Datatypes.app
                        (Datatypes.app g3 (Datatypes.Coq_cons (Datatypes.Coq_pair
                          (Datatypes.Coq_pair
                          (Datatypes.app _UU0393_ (Datatypes.app _UU03a3_1 _UU03a3_2))
                          (Datatypes.app _UU0394_1 (Datatypes.app _UU0394_2 _UU03a0_))) d)
                          Datatypes.Coq_nil)) Datatypes.Coq_nil))
                    (Datatypes.app g3 (Datatypes.Coq_cons (Datatypes.Coq_pair
                      (Datatypes.Coq_pair
                      (Datatypes.app _UU0393_ (Datatypes.app _UU03a3_1 _UU03a3_2))
                      (Datatypes.app _UU0394_1 (Datatypes.app _UU0394_2 _UU03a0_))) d)
                      Datatypes.Coq_nil))) seq2 d5 lS16 lS15 lS14 lS13) ns2 d2 lS12 lS11
                lS10 lS9) seq1 d3 lS8 lS7 lS6 lS5) ns1 d1 lS1 lS2 lS3 lS4)}) x1}) x0}

data Cut_rule v =
   Cut (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                                               (LntT.PropF
                                                                               v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                                         (LntT.PropF v)) 
 LntT.Coq_dir (LntT.PropF v)

data LNSKt_cut_rules v =
   LNSKt_rules_woc (Datatypes.Coq_list
                   (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) 
 (Lntkt_exchT.LNSKt_rules v)
 | LNSKt_rules_wc (Datatypes.Coq_list
                  (Datatypes.Coq_list
                  (Datatypes.Coq_prod
                  (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) 
 (LntT.Coq_nslclrule
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)
 (Cut_rule v))

coq_LNSKt_cut_elimination :: (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                             LntT.Coq_dir)) -> (DdT.Coq_derrec
                             (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                             LntT.Coq_dir)) (LNSKt_cut_rules a1) ()) -> DdT.Coq_derrec
                             (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                             LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules a1) ()
coq_LNSKt_cut_elimination ns h =
  let {n = Dd_fc.derrec_height ns h} in
  Ind_lex.lt_wf_indT n (\n0 x ->
    (case n0 of {
      Datatypes.O -> (\_ _ h0 _ ->
       (case h0 of {
         DdT.Coq_dpI _ _ -> (\_ -> Logic.coq_False_rect);
         DdT.Coq_derI _ _ _ _ -> (\_ -> Logic.coq_False_rect)}) __);
      Datatypes.S n1 -> (\x0 _ h0 _ ->
       (case h0 of {
         DdT.Coq_dpI _ _ -> (\_ _ _ -> Logic.coq_False_rect);
         DdT.Coq_derI ps concl l d -> (\h' _ _ ->
          let {
           _evar_0_ = \_ ->
            Logic.eq_rect_r (Dd_fc.dersrec_height ps d)
              ((case l of {
                 LNSKt_rules_woc ps0 c x1 -> (\_ _ ->
                  Logic.eq_rect_r ps (\_ ->
                    Logic.eq_rect_r concl (\x2 -> DdT.Coq_derI ps concl x2
                      (DdT.dersrecI_forall ps (\p hin ->
                        let {x3 = Dd_fc.dersrecD_forall_in_dersrec ps d p hin} in
                        case x3 of {
                         Specif.Coq_existT d2 _ ->
                          x0 (Dd_fc.derrec_height p d2) __ p d2 __}))) c) ps0 __ x1);
                 LNSKt_rules_wc ps0 c x1 -> (\_ _ ->
                  Logic.eq_rect_r ps (\_ ->
                    Logic.eq_rect_r concl (\x2 ->
                      (case x2 of {
                        LntT.NSlclctxt ps1 c0 g x3 -> (\_ _ ->
                         Logic.eq_rect (List.map (LntT.nslclext g) ps1) (\_ ->
                           Logic.eq_rect (LntT.nslclext g c0) (\x4 ->
                             Logic.eq_rect (LntT.nslclext g c0) (\l0 h'0 _ _ x5 ->
                               Logic.eq_rect (List.map (LntT.nslclext g) ps1)
                                 (\l1 d0 _ _ x6 ->
                                 (case x4 of {
                                   Cut _UU0393_ _UU0394_1 _UU0394_2 _UU03a3_1 _UU03a3_2
                                    _UU03a0_ d1 a -> (\_ _ ->
                                    Logic.eq_rect
                                      (Datatypes.app (Datatypes.Coq_cons
                                        (Datatypes.Coq_cons (Datatypes.Coq_pair
                                        (Datatypes.Coq_pair _UU0393_
                                        (Datatypes.app _UU0394_1
                                          (Datatypes.app (Datatypes.Coq_cons a
                                            Datatypes.Coq_nil) _UU0394_2))) d1)
                                        Datatypes.Coq_nil) Datatypes.Coq_nil)
                                        (Datatypes.Coq_cons (Datatypes.Coq_cons
                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                        (Datatypes.app _UU03a3_1
                                          (Datatypes.app (Datatypes.Coq_cons a
                                            Datatypes.Coq_nil) _UU03a3_2)) _UU03a0_) d1)
                                        Datatypes.Coq_nil) Datatypes.Coq_nil)) (\_ ->
                                      Logic.eq_rect (Datatypes.Coq_cons
                                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                                        (Datatypes.app _UU0393_
                                          (Datatypes.app _UU03a3_1 _UU03a3_2))
                                        (Datatypes.app _UU0394_1
                                          (Datatypes.app _UU0394_2 _UU03a0_))) d1)
                                        Datatypes.Coq_nil)
                                        (Logic.eq_rect
                                          (Datatypes.app (Datatypes.Coq_cons
                                            (Datatypes.Coq_cons (Datatypes.Coq_pair
                                            (Datatypes.Coq_pair _UU0393_
                                            (Datatypes.app _UU0394_1
                                              (Datatypes.app (Datatypes.Coq_cons a
                                                Datatypes.Coq_nil) _UU0394_2))) d1)
                                            Datatypes.Coq_nil) Datatypes.Coq_nil)
                                            (Datatypes.Coq_cons (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair (Datatypes.Coq_pair
                                            (Datatypes.app _UU03a3_1
                                              (Datatypes.app (Datatypes.Coq_cons a
                                                Datatypes.Coq_nil) _UU03a3_2)) _UU03a0_)
                                            d1) Datatypes.Coq_nil) Datatypes.Coq_nil))
                                          (\d2 l2 x7 _ _ x8 ->
                                          Logic.eq_rect (Datatypes.Coq_cons
                                            (Datatypes.Coq_pair (Datatypes.Coq_pair
                                            (Datatypes.app _UU0393_
                                              (Datatypes.app _UU03a3_1 _UU03a3_2))
                                            (Datatypes.app _UU0394_1
                                              (Datatypes.app _UU0394_2 _UU03a0_))) d1)
                                            Datatypes.Coq_nil) (\_ _ _ _ _ _ ->
                                            let {
                                             x9 = Dd_fc.dersrec_double_verb
                                                    (LntT.nslclext g (Datatypes.Coq_cons
                                                      (Datatypes.Coq_pair
                                                      (Datatypes.Coq_pair _UU0393_
                                                      (Datatypes.app _UU0394_1
                                                        (Datatypes.app (Datatypes.Coq_cons
                                                          a Datatypes.Coq_nil) _UU0394_2)))
                                                      d1) Datatypes.Coq_nil))
                                                    (LntT.nslclext g (Datatypes.Coq_cons
                                                      (Datatypes.Coq_pair
                                                      (Datatypes.Coq_pair
                                                      (Datatypes.app _UU03a3_1
                                                        (Datatypes.app (Datatypes.Coq_cons
                                                          a Datatypes.Coq_nil) _UU03a3_2))
                                                      _UU03a0_) d1) Datatypes.Coq_nil)) d2}
                                            in
                                            case x9 of {
                                             Specif.Coq_existT d3 s ->
                                              case s of {
                                               Specif.Coq_existT d4 p ->
                                                case p of {
                                                 Datatypes.Coq_pair _ _ ->
                                                  let {
                                                   s0 = Merge.merge_ex g g
                                                          (Structural_equivalence.struct_equiv_weak_refl
                                                            g)}
                                                  in
                                                  case s0 of {
                                                   Specif.Coq_existT g3 hG3 ->
                                                    Lnt_contraction_mrT.derrec_mergeL g
                                                      (Datatypes.Coq_cons
                                                      (Datatypes.Coq_pair
                                                      (Datatypes.Coq_pair
                                                      (Datatypes.app _UU0393_
                                                        (Datatypes.app _UU03a3_1
                                                          _UU03a3_2))
                                                      (Datatypes.app _UU0394_1
                                                        (Datatypes.app _UU0394_2 _UU03a0_)))
                                                      d1) Datatypes.Coq_nil) g3 hG3
                                                      (coq_LNSKt_cut_admissibility
                                                        (Datatypes.app g
                                                          (Datatypes.Coq_cons
                                                          (Datatypes.Coq_pair
                                                          (Datatypes.Coq_pair _UU0393_
                                                          (Datatypes.app _UU0394_1
                                                            (Datatypes.app
                                                              (Datatypes.Coq_cons a
                                                              Datatypes.Coq_nil)
                                                              _UU0394_2))) d1)
                                                          Datatypes.Coq_nil))
                                                        (Datatypes.app g
                                                          (Datatypes.Coq_cons
                                                          (Datatypes.Coq_pair
                                                          (Datatypes.Coq_pair
                                                          (Datatypes.app _UU03a3_1
                                                            (Datatypes.app
                                                              (Datatypes.Coq_cons a
                                                              Datatypes.Coq_nil)
                                                              _UU03a3_2)) _UU03a0_) d1)
                                                          Datatypes.Coq_nil))
                                                        (x0
                                                          (Dd_fc.derrec_height
                                                            (Datatypes.app g
                                                              (Datatypes.Coq_cons
                                                              (Datatypes.Coq_pair
                                                              (Datatypes.Coq_pair _UU0393_
                                                              (Datatypes.app _UU0394_1
                                                                (Datatypes.app
                                                                  (Datatypes.Coq_cons a
                                                                  Datatypes.Coq_nil)
                                                                  _UU0394_2))) d1)
                                                              Datatypes.Coq_nil)) d3) __
                                                          (Datatypes.app g
                                                            (Datatypes.Coq_cons
                                                            (Datatypes.Coq_pair
                                                            (Datatypes.Coq_pair _UU0393_
                                                            (Datatypes.app _UU0394_1
                                                              (Datatypes.app
                                                                (Datatypes.Coq_cons a
                                                                Datatypes.Coq_nil)
                                                                _UU0394_2))) d1)
                                                            Datatypes.Coq_nil)) d3 __)
                                                        (x0
                                                          (Dd_fc.derrec_height
                                                            (Datatypes.app g
                                                              (Datatypes.Coq_cons
                                                              (Datatypes.Coq_pair
                                                              (Datatypes.Coq_pair
                                                              (Datatypes.app _UU03a3_1
                                                                (Datatypes.app
                                                                  (Datatypes.Coq_cons a
                                                                  Datatypes.Coq_nil)
                                                                  _UU03a3_2)) _UU03a0_)
                                                              d1) Datatypes.Coq_nil)) d4)
                                                          __
                                                          (Datatypes.app g
                                                            (Datatypes.Coq_cons
                                                            (Datatypes.Coq_pair
                                                            (Datatypes.Coq_pair
                                                            (Datatypes.app _UU03a3_1
                                                              (Datatypes.app
                                                                (Datatypes.Coq_cons a
                                                                Datatypes.Coq_nil)
                                                                _UU03a3_2)) _UU03a0_) d1)
                                                            Datatypes.Coq_nil)) d4 __) g g
                                                        g3 (Datatypes.Coq_pair _UU0393_
                                                        (Datatypes.app _UU0394_1
                                                          (Datatypes.app
                                                            (Datatypes.Coq_cons a
                                                            Datatypes.Coq_nil) _UU0394_2)))
                                                        (Datatypes.Coq_pair
                                                        (Datatypes.app _UU03a3_1
                                                          (Datatypes.app
                                                            (Datatypes.Coq_cons a
                                                            Datatypes.Coq_nil) _UU03a3_2))
                                                        _UU03a0_) d1 _UU0393_ _UU0394_1
                                                        _UU0394_2 _UU03a3_1 _UU03a3_2
                                                        _UU03a0_ a hG3
                                                        (Structural_equivalence.struct_equiv_str_refl
                                                          g))}}}}) c0 l2 h'0 __ x8 __ x7)
                                          ps1 d0 l1 x6 __ __ x4) c0) ps1 __)}) __ __) ps
                                 l0 d __ __ x5) concl l h' __ __ x2) concl) ps __ x3)}) __
                        __) c) ps0 __ x1)}) __ __) n1}
          in
          Logic.eq_rect_r (DdT.Coq_derI ps concl l d) _evar_0_ h' __)}) h0 __ __)}) x) ns
    h __

