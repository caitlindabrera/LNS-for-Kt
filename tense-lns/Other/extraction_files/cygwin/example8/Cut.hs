{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Cut where

import qualified Prelude
import qualified Datatypes
import qualified Lemma_Sixteen
import qualified Logic
import qualified Nat
import qualified Specif
import qualified DdT
import qualified Dd_fc
import qualified Gen_tacs
import qualified Ind_lex
import qualified LntT
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
                               (Gen_tacs.Coq_rel
                               (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) -> (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel
                               (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) -> (DdT.Coq_derrec
                               (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel
                               (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules a1)
                               ()) -> (DdT.Coq_derrec
                               (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel
                               (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules a1)
                               ()) -> (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Datatypes.Coq_prod
                               (Datatypes.Coq_list (LntT.PropF a1))
                               (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) -> (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Datatypes.Coq_prod
                               (Datatypes.Coq_list (LntT.PropF a1))
                               (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) -> (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel
                               (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) -> (Datatypes.Coq_prod
                               (Datatypes.Coq_list (LntT.PropF a1))
                               (Datatypes.Coq_list (LntT.PropF a1))) ->
                               (Datatypes.Coq_prod
                               (Datatypes.Coq_list (LntT.PropF a1))
                               (Datatypes.Coq_list (LntT.PropF a1))) ->
                               LntT.Coq_dir -> (Datatypes.Coq_list
                               (LntT.PropF a1)) -> (Datatypes.Coq_list
                               (LntT.PropF a1)) -> (Datatypes.Coq_list
                               (LntT.PropF a1)) -> (Datatypes.Coq_list
                               (LntT.PropF a1)) -> (Datatypes.Coq_list
                               (LntT.PropF a1)) -> (Datatypes.Coq_list
                               (LntT.PropF a1)) -> (LntT.PropF a1) ->
                               (Merge.Coq_merge a1) ->
                               (Structural_equivalence.Coq_struct_equiv_str
                               a1) -> DdT.Coq_derrec
                               (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel
                               (Datatypes.Coq_list (LntT.PropF a1)))
                               LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules a1) 
                               ()
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
                (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                  _UU0394_2))) (\d4 lS9 lS10 lS11 lS12 ->
              Logic.eq_rect_r
                (Datatypes.app g2 (Datatypes.Coq_cons (Datatypes.Coq_pair
                  seq2 d) Datatypes.Coq_nil)) (\d5 lS13 lS14 lS15 lS16 ->
                Logic.eq_rect_r (Datatypes.Coq_pair
                  (Datatypes.app _UU03a3_1
                    (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                      _UU03a3_2)) _UU03a0_) (\d6 lS17 _ _ _ ->
                  Logic.eq_rect
                    (Datatypes.app
                      (Datatypes.app g3 (Datatypes.Coq_cons
                        (Datatypes.Coq_pair (Datatypes.Coq_pair
                        (Datatypes.app _UU0393_
                          (Datatypes.app _UU03a3_1 _UU03a3_2))
                        (Datatypes.app _UU0394_1
                          (Datatypes.app _UU0394_2 _UU03a0_))) d)
                        Datatypes.Coq_nil)) Datatypes.Coq_nil)
                    (Logic.eq_rect
                      (Datatypes.app g3
                        (Datatypes.app (Datatypes.Coq_cons
                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                          (Datatypes.app _UU0393_
                            (Datatypes.app _UU03a3_1 _UU03a3_2))
                          (Datatypes.app _UU0394_1
                            (Datatypes.app _UU0394_2 _UU03a0_))) d)
                          Datatypes.Coq_nil) Datatypes.Coq_nil))
                      (unsafeCoerce lS17 __ g1 _UU0393_ _UU0394_1 _UU0394_2
                        g2 _UU03a3_1 _UU03a3_2 _UU03a0_ Datatypes.Coq_nil g3
                        a d d4 d6 __ __ h3 x)
                      (Datatypes.app
                        (Datatypes.app g3 (Datatypes.Coq_cons
                          (Datatypes.Coq_pair (Datatypes.Coq_pair
                          (Datatypes.app _UU0393_
                            (Datatypes.app _UU03a3_1 _UU03a3_2))
                          (Datatypes.app _UU0394_1
                            (Datatypes.app _UU0394_2 _UU03a0_))) d)
                          Datatypes.Coq_nil)) Datatypes.Coq_nil))
                    (Datatypes.app g3 (Datatypes.Coq_cons (Datatypes.Coq_pair
                      (Datatypes.Coq_pair
                      (Datatypes.app _UU0393_
                        (Datatypes.app _UU03a3_1 _UU03a3_2))
                      (Datatypes.app _UU0394_1
                        (Datatypes.app _UU0394_2 _UU03a0_))) d)
                      Datatypes.Coq_nil))) seq2 d5 lS16 lS15 lS14 lS13) ns2
                d2 lS12 lS11 lS10 lS9) seq1 d3 lS8 lS7 lS6 lS5) ns1 d1 lS1
            lS2 lS3 lS4)}) x1}) x0}

data Cut_rule v =
   Cut (Datatypes.Coq_list
       (Datatypes.Coq_prod
       (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF v))
       (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (Datatypes.Coq_list
                                                           (Datatypes.Coq_prod
                                                           (Datatypes.Coq_prod
                                                           (Datatypes.Coq_list
                                                           (LntT.PropF v))
                                                           (Datatypes.Coq_list
                                                           (LntT.PropF v)))
                                                           LntT.Coq_dir)) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod
 (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF v))
 (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (Datatypes.Coq_prod
                                                     (Datatypes.Coq_list
                                                     (LntT.PropF v))
                                                     (Datatypes.Coq_list
                                                     (LntT.PropF v))) 
 (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF v))
 (Datatypes.Coq_list (LntT.PropF v))) (Datatypes.Coq_prod
                                      (Datatypes.Coq_list (LntT.PropF v))
                                      (Datatypes.Coq_list (LntT.PropF v))) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod
 (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF v))
 (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (Datatypes.Coq_list
                                                     (Datatypes.Coq_prod
                                                     (Datatypes.Coq_prod
                                                     (Datatypes.Coq_list
                                                     (LntT.PropF v))
                                                     (Datatypes.Coq_list
                                                     (LntT.PropF v)))
                                                     LntT.Coq_dir)) (Datatypes.Coq_list
                                                                    (Datatypes.Coq_prod
                                                                    (Datatypes.Coq_prod
                                                                    (Datatypes.Coq_list
                                                                    (LntT.PropF
                                                                    v))
                                                                    (Datatypes.Coq_list
                                                                    (LntT.PropF
                                                                    v)))
                                                                    LntT.Coq_dir)) 
 LntT.Coq_dir (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                  (LntT.PropF v)) (Datatypes.Coq_list
                                                                  (LntT.PropF
                                                                  v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) 
 (Datatypes.Coq_list (LntT.PropF v)) (LntT.PropF v) (Merge.Coq_merge v) 
 (Structural_equivalence.Coq_struct_equiv_str v)

data LNSKt_cut_rules v =
   LNSKt_rules_woc (Datatypes.Coq_list
                   (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                   LntT.Coq_dir))) (Datatypes.Coq_list
                                   (Datatypes.Coq_prod
                                   (Gen_tacs.Coq_rel
                                   (Datatypes.Coq_list (LntT.PropF v)))
                                   LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules v)
 | LNSKt_rules_wc (Datatypes.Coq_list
                  (Datatypes.Coq_list
                  (Datatypes.Coq_prod
                  (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                  LntT.Coq_dir))) (Datatypes.Coq_list
                                  (Datatypes.Coq_prod
                                  (Gen_tacs.Coq_rel
                                  (Datatypes.Coq_list (LntT.PropF v)))
                                  LntT.Coq_dir)) (Cut_rule v)

coq_LNSKt_cut_elimination :: (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel
                             (Datatypes.Coq_list (LntT.PropF a1)))
                             LntT.Coq_dir)) -> (DdT.Coq_derrec
                             (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel
                             (Datatypes.Coq_list (LntT.PropF a1)))
                             LntT.Coq_dir)) (LNSKt_cut_rules a1) ()) ->
                             DdT.Coq_derrec
                             (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel
                             (Datatypes.Coq_list (LntT.PropF a1)))
                             LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules a1) 
                             ()
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
                        let {
                         x3 = Dd_fc.dersrecD_forall_in_dersrec ps d p hin}
                        in
                        case x3 of {
                         Specif.Coq_existT d2 _ ->
                          x0 (Dd_fc.derrec_height p d2) __ p d2 __}))) c) ps0
                    __ x1);
                 LNSKt_rules_wc ps0 c x1 -> (\_ _ ->
                  Logic.eq_rect_r ps (\_ ->
                    Logic.eq_rect_r concl (\x2 ->
                      (case x2 of {
                        Cut g1 g2 g3 seq1 seq2 seq3 ns1 ns2 ns3 d0 _UU0393_
                         _UU0394_1 _UU0394_2 _UU03a3_1 _UU03a3_2 _UU03a0_ a
                         x3 h5 -> (\_ _ ->
                         Logic.eq_rect (Datatypes.Coq_cons ns1
                           (Datatypes.Coq_cons ns2 Datatypes.Coq_nil)) (\_ ->
                           Logic.eq_rect_r concl (\_ _ _ _ _ _ x4 h6 ->
                             Logic.eq_rect (Datatypes.Coq_cons ns1
                               (Datatypes.Coq_cons ns2 Datatypes.Coq_nil))
                               (\l0 d1 _ _ x5 ->
                               Logic.eq_rect_r
                                 (Datatypes.app g3 (Datatypes.Coq_cons
                                   (Datatypes.Coq_pair seq3 d0)
                                   Datatypes.Coq_nil)) (\l1 h'0 _ _ _ _ ->
                                 let {
                                  x6 = Dd_fc.dersrec_double_verb ns1 ns2 d1}
                                 in
                                 case x6 of {
                                  Specif.Coq_existT d2 s ->
                                   case s of {
                                    Specif.Coq_existT d3 p ->
                                     case p of {
                                      Datatypes.Coq_pair hin1 hin2 ->
                                       Logic.eq_rect_r (Datatypes.Coq_pair
                                         (Datatypes.app _UU0393_
                                           (Datatypes.app _UU03a3_1
                                             _UU03a3_2))
                                         (Datatypes.app _UU0394_1
                                           (Datatypes.app _UU0394_2 _UU03a0_)))
                                         (\h'1 _ l2 _ _ ->
                                         coq_LNSKt_cut_admissibility
                                           (Datatypes.app g1
                                             (Datatypes.Coq_cons
                                             (Datatypes.Coq_pair
                                             (Datatypes.Coq_pair _UU0393_
                                             (Datatypes.app _UU0394_1
                                               (Datatypes.app
                                                 (Datatypes.Coq_cons a
                                                 Datatypes.Coq_nil)
                                                 _UU0394_2))) d0)
                                             Datatypes.Coq_nil))
                                           (Datatypes.app g2
                                             (Datatypes.Coq_cons
                                             (Datatypes.Coq_pair
                                             (Datatypes.Coq_pair
                                             (Datatypes.app _UU03a3_1
                                               (Datatypes.app
                                                 (Datatypes.Coq_cons a
                                                 Datatypes.Coq_nil)
                                                 _UU03a3_2)) _UU03a0_) d0)
                                             Datatypes.Coq_nil))
                                           (Logic.eq_rect_r (DdT.Coq_derI
                                             (Datatypes.Coq_cons ns1
                                             (Datatypes.Coq_cons ns2
                                             Datatypes.Coq_nil))
                                             (Datatypes.app g3
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair
                                               (Datatypes.app _UU0393_
                                                 (Datatypes.app _UU03a3_1
                                                   _UU03a3_2))
                                               (Datatypes.app _UU0394_1
                                                 (Datatypes.app _UU0394_2
                                                   _UU03a0_))) d0)
                                               Datatypes.Coq_nil)) l2 d1)
                                             (\_ ->
                                             Logic.eq_rect_r
                                               (Dd_fc.dersrec_height
                                                 (Datatypes.Coq_cons ns1
                                                 (Datatypes.Coq_cons ns2
                                                 Datatypes.Coq_nil)) d1)
                                               (\x7 _ ->
                                               Logic.eq_rect_r
                                                 (Datatypes.app g1
                                                   (Datatypes.Coq_cons
                                                   (Datatypes.Coq_pair seq1
                                                   d0) Datatypes.Coq_nil))
                                                 (\d4 x8 l3 _ d5 hin3 hin4 ->
                                                 Logic.eq_rect_r
                                                   (Datatypes.Coq_pair
                                                   _UU0393_
                                                   (Datatypes.app _UU0394_1
                                                     (Datatypes.app
                                                       (Datatypes.Coq_cons a
                                                       Datatypes.Coq_nil)
                                                       _UU0394_2)))
                                                   (\d6 x9 l4 _ d7 hin5 hin6 ->
                                                   Logic.eq_rect_r
                                                     (Datatypes.app g2
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       seq2 d0)
                                                       Datatypes.Coq_nil))
                                                     (\d8 x10 l5 _ d9 hin7 hin8 ->
                                                     Logic.eq_rect_r
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.app
                                                         _UU03a3_1
                                                         (Datatypes.app
                                                           (Datatypes.Coq_cons
                                                           a
                                                           Datatypes.Coq_nil)
                                                           _UU03a3_2))
                                                       _UU03a0_)
                                                       (\_ x11 _ _ _ _ _ ->
                                                       Logic.eq_rect_r
                                                         (Datatypes.app g3
                                                           (Datatypes.Coq_cons
                                                           (Datatypes.Coq_pair
                                                           (Datatypes.Coq_pair
                                                           (Datatypes.app
                                                             _UU0393_
                                                             (Datatypes.app
                                                               _UU03a3_1
                                                               _UU03a3_2))
                                                           (Datatypes.app
                                                             _UU0394_1
                                                             (Datatypes.app
                                                               _UU0394_2
                                                               _UU03a0_)))
                                                           d0)
                                                           Datatypes.Coq_nil))
                                                         (x11
                                                           (Dd_fc.derrec_height
                                                             (Datatypes.app
                                                               g1
                                                               (Datatypes.Coq_cons
                                                               (Datatypes.Coq_pair
                                                               (Datatypes.Coq_pair
                                                               _UU0393_
                                                               (Datatypes.app
                                                                 _UU0394_1
                                                                 (Datatypes.app
                                                                   (Datatypes.Coq_cons
                                                                   a
                                                                   Datatypes.Coq_nil)
                                                                   _UU0394_2)))
                                                               d0)
                                                               Datatypes.Coq_nil))
                                                             d7) __
                                                           (Datatypes.app g1
                                                             (Datatypes.Coq_cons
                                                             (Datatypes.Coq_pair
                                                             (Datatypes.Coq_pair
                                                             _UU0393_
                                                             (Datatypes.app
                                                               _UU0394_1
                                                               (Datatypes.app
                                                                 (Datatypes.Coq_cons
                                                                 a
                                                                 Datatypes.Coq_nil)
                                                                 _UU0394_2)))
                                                             d0)
                                                             Datatypes.Coq_nil))
                                                           d7 __) ns3) seq2
                                                       d8 x10 l5 __ d9 hin8
                                                       hin7) ns2 d6 x9 l4 __
                                                     d3 hin6 hin5) seq1 d4 x8
                                                   l3 __ d5 hin4 hin3) ns1 d1
                                                 x7 l2 __ d2 hin1 hin2) n1 x0
                                               __) h'1 __)
                                           (Logic.eq_rect_r (DdT.Coq_derI
                                             (Datatypes.Coq_cons ns1
                                             (Datatypes.Coq_cons ns2
                                             Datatypes.Coq_nil))
                                             (Datatypes.app g3
                                               (Datatypes.Coq_cons
                                               (Datatypes.Coq_pair
                                               (Datatypes.Coq_pair
                                               (Datatypes.app _UU0393_
                                                 (Datatypes.app _UU03a3_1
                                                   _UU03a3_2))
                                               (Datatypes.app _UU0394_1
                                                 (Datatypes.app _UU0394_2
                                                   _UU03a0_))) d0)
                                               Datatypes.Coq_nil)) l2 d1)
                                             (\_ ->
                                             Logic.eq_rect_r
                                               (Dd_fc.dersrec_height
                                                 (Datatypes.Coq_cons ns1
                                                 (Datatypes.Coq_cons ns2
                                                 Datatypes.Coq_nil)) d1)
                                               (\x7 _ ->
                                               Logic.eq_rect_r
                                                 (Datatypes.app g1
                                                   (Datatypes.Coq_cons
                                                   (Datatypes.Coq_pair seq1
                                                   d0) Datatypes.Coq_nil))
                                                 (\d4 x8 l3 _ d5 hin3 hin4 ->
                                                 Logic.eq_rect_r
                                                   (Datatypes.Coq_pair
                                                   _UU0393_
                                                   (Datatypes.app _UU0394_1
                                                     (Datatypes.app
                                                       (Datatypes.Coq_cons a
                                                       Datatypes.Coq_nil)
                                                       _UU0394_2)))
                                                   (\d6 x9 l4 _ _ hin5 hin6 ->
                                                   Logic.eq_rect_r
                                                     (Datatypes.app g2
                                                       (Datatypes.Coq_cons
                                                       (Datatypes.Coq_pair
                                                       seq2 d0)
                                                       Datatypes.Coq_nil))
                                                     (\d7 x10 l5 _ d8 hin7 hin8 ->
                                                     Logic.eq_rect_r
                                                       (Datatypes.Coq_pair
                                                       (Datatypes.app
                                                         _UU03a3_1
                                                         (Datatypes.app
                                                           (Datatypes.Coq_cons
                                                           a
                                                           Datatypes.Coq_nil)
                                                           _UU03a3_2))
                                                       _UU03a0_)
                                                       (\_ x11 _ _ d9 _ _ ->
                                                       x11
                                                         (Dd_fc.derrec_height
                                                           (Datatypes.app g2
                                                             (Datatypes.Coq_cons
                                                             (Datatypes.Coq_pair
                                                             (Datatypes.Coq_pair
                                                             (Datatypes.app
                                                               _UU03a3_1
                                                               (Datatypes.app
                                                                 (Datatypes.Coq_cons
                                                                 a
                                                                 Datatypes.Coq_nil)
                                                                 _UU03a3_2))
                                                             _UU03a0_) d0)
                                                             Datatypes.Coq_nil))
                                                           d9) __
                                                         (Datatypes.app g2
                                                           (Datatypes.Coq_cons
                                                           (Datatypes.Coq_pair
                                                           (Datatypes.Coq_pair
                                                           (Datatypes.app
                                                             _UU03a3_1
                                                             (Datatypes.app
                                                               (Datatypes.Coq_cons
                                                               a
                                                               Datatypes.Coq_nil)
                                                               _UU03a3_2))
                                                           _UU03a0_) d0)
                                                           Datatypes.Coq_nil))
                                                         d9 __) seq2 d7 x10
                                                       l5 __ d8 hin8 hin7)
                                                     ns2 d6 x9 l4 __ d3 hin6
                                                     hin5) seq1 d4 x8 l3 __
                                                   d5 hin4 hin3) ns1 d1 x7 l2
                                                 __ d2 hin1 hin2) n1 x0 __)
                                             h'1 __) g1 g2 g3
                                           (Datatypes.Coq_pair _UU0393_
                                           (Datatypes.app _UU0394_1
                                             (Datatypes.app
                                               (Datatypes.Coq_cons a
                                               Datatypes.Coq_nil) _UU0394_2)))
                                           (Datatypes.Coq_pair
                                           (Datatypes.app _UU03a3_1
                                             (Datatypes.app
                                               (Datatypes.Coq_cons a
                                               Datatypes.Coq_nil) _UU03a3_2))
                                           _UU03a0_) d0 _UU0393_ _UU0394_1
                                           _UU0394_2 _UU03a3_1 _UU03a3_2
                                           _UU03a0_ a x4 h6) seq3 h'0 __ l1
                                         __ __}}}) concl l0 h' __ __ x5 __)
                               ps l d __ __ x2) ns3) ps __ __ __ __ __ __ __
                           x3 h5)}) __ __) c) ps0 __ x1)}) __ __) n1}
          in
          Logic.eq_rect_r (DdT.Coq_derI ps concl l d) _evar_0_ h' __)}) h0 __
         __)}) x) ns h __

