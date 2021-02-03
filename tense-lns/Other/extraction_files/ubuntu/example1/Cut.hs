{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Cut where

import qualified Prelude
import qualified Datatypes
import qualified Lemma_Sixteen
import qualified List
import qualified Logic
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

coq_LNSKt_cut_admissibility :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                               (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                               (DdT.Coq_derrec
                               (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                               (Lntkt_exchT.LNSKt_rules a1) ()) -> (DdT.Coq_derrec
                               (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                               (Lntkt_exchT.LNSKt_rules a1) ()) -> (([])
                               ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1))) LntT.Coq_dir))
                               -> (([])
                               ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1))) LntT.Coq_dir))
                               -> (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                               -> ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1))) -> ((,)
                               (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1))) -> LntT.Coq_dir ->
                               (([]) (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                               (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([]) (LntT.PropF a1))
                               -> (([]) (LntT.PropF a1)) -> (LntT.PropF a1) -> (Merge.Coq_merge 
                               a1) -> (Structural_equivalence.Coq_struct_equiv_str a1) ->
                               DdT.Coq_derrec
                               (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                               (Lntkt_exchT.LNSKt_rules a1) ()
coq_LNSKt_cut_admissibility ns1 ns2 d1 d2 g1 g2 g3 seq1 seq2 d _UU0393_ _UU0394_1 _UU0394_2 _UU03a3_1 _UU03a3_2 _UU03a0_ a x h3 =
  let {
   p = Lemma_Sixteen.coq_Lemma_Sixteen ((,) (Size.fsize a)
         ((Prelude.+) (Dd_fc.dp ns1 d1) (Dd_fc.dp ns2 d2)))}
  in
  case p of {
   (,) p0 x0 ->
    case p0 of {
     (,) p1 x1 ->
      case p1 of {
       (,) lS1 lS2 ->
        Logic.eq_rect_r (Datatypes.app g1 ((:) ((,) seq1 d) ([]))) (\d3 lS3 lS4 lS5 lS6 ->
          Logic.eq_rect_r ((,) _UU0393_
            (Datatypes.app _UU0394_1 (Datatypes.app ((:) a ([])) _UU0394_2)))
            (\d4 lS7 lS8 lS9 lS10 ->
            Logic.eq_rect_r (Datatypes.app g2 ((:) ((,) seq2 d) ([]))) (\d5 lS11 lS12 lS13 lS14 ->
              Logic.eq_rect_r ((,) (Datatypes.app _UU03a3_1 (Datatypes.app ((:) a ([])) _UU03a3_2))
                _UU03a0_) (\d6 lS15 _ _ _ ->
                Logic.eq_rect
                  (Datatypes.app
                    (Datatypes.app g3 ((:) ((,) ((,)
                      (Datatypes.app _UU0393_ (Datatypes.app _UU03a3_1 _UU03a3_2))
                      (Datatypes.app _UU0394_1 (Datatypes.app _UU0394_2 _UU03a0_))) d) ([]))) ([]))
                  (Logic.eq_rect
                    (Datatypes.app g3
                      (Datatypes.app ((:) ((,) ((,)
                        (Datatypes.app _UU0393_ (Datatypes.app _UU03a3_1 _UU03a3_2))
                        (Datatypes.app _UU0394_1 (Datatypes.app _UU0394_2 _UU03a0_))) d) ([])) ([])))
                    (unsafeCoerce lS15 __ g1 _UU0393_ _UU0394_1 _UU0394_2 g2 _UU03a3_1 _UU03a3_2
                      _UU03a0_ ([]) g3 a d d4 d6 __ __ h3 x)
                    (Datatypes.app
                      (Datatypes.app g3 ((:) ((,) ((,)
                        (Datatypes.app _UU0393_ (Datatypes.app _UU03a3_1 _UU03a3_2))
                        (Datatypes.app _UU0394_1 (Datatypes.app _UU0394_2 _UU03a0_))) d) ([]))) ([])))
                  (Datatypes.app g3 ((:) ((,) ((,)
                    (Datatypes.app _UU0393_ (Datatypes.app _UU03a3_1 _UU03a3_2))
                    (Datatypes.app _UU0394_1 (Datatypes.app _UU0394_2 _UU03a0_))) d) ([])))) seq2 d5
                lS14 lS13 lS12 lS11) ns2 d2 lS10 lS9 lS8 lS7) seq1 d3 lS6 lS5 lS4 lS3) ns1 d1 lS1 lS2
          x1 x0}}}

data Cut_rule v =
   Cut (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) 
 (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) LntT.Coq_dir (LntT.PropF v)

data LNSKt_cut_rules v =
   LNSKt_rules_woc (([]) (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir))) 
 (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules v)
 | LNSKt_rules_wc (([]) (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir))) (([])
                                                                                            ((,)
                                                                                            (Gen_tacs.Coq_rel
                                                                                            (([])
                                                                                            (LntT.PropF
                                                                                            v)))
                                                                                            LntT.Coq_dir)) 
 (LntT.Coq_nslclrule ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir) (Cut_rule v))

coq_LNSKt_cut_elimination :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                             (DdT.Coq_derrec
                             (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                             (LNSKt_cut_rules a1) ()) -> DdT.Coq_derrec
                             (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                             (Lntkt_exchT.LNSKt_rules a1) ()
coq_LNSKt_cut_elimination ns h =
  let {n = Dd_fc.derrec_height ns h} in
  Ind_lex.lt_wf_indT n (\n0 x _ h0 _ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Logic.coq_False_rect)
      (\n1 ->
      case h0 of {
       DdT.Coq_dpI _ _ -> Logic.coq_False_rect;
       DdT.Coq_derI ps concl l d ->
        let {
         _evar_0_ = \_ ->
          Logic.eq_rect_r (Dd_fc.dersrec_height ps d)
            (case l of {
              LNSKt_rules_woc ps0 c x0 ->
               Logic.eq_rect_r ps (\_ ->
                 Logic.eq_rect_r concl (\x1 -> DdT.Coq_derI ps concl x1
                   (DdT.dersrecI_forall ps (\p hin ->
                     let {x2 = Dd_fc.dersrecD_forall_in_dersrec ps d p hin} in
                     case x2 of {
                      Specif.Coq_existT d2 _ -> x (Dd_fc.derrec_height p d2) __ p d2 __}))) c) ps0 __
                 x0;
              LNSKt_rules_wc ps0 c x0 ->
               Logic.eq_rect_r ps (\_ ->
                 Logic.eq_rect_r concl (\x1 ->
                   case x1 of {
                    LntT.NSlclctxt ps1 c0 g h1 ->
                     Logic.eq_rect (List.map (LntT.nslclext g) ps1) (\_ ->
                       Logic.eq_rect (LntT.nslclext g c0) (\h2 ->
                         Logic.eq_rect (LntT.nslclext g c0) (\l0 h' _ _ x2 ->
                           Logic.eq_rect (List.map (LntT.nslclext g) ps1) (\l1 d0 _ _ x3 ->
                             case h2 of {
                              Cut _UU0393_ _UU0394_1 _UU0394_2 _UU03a3_1 _UU03a3_2 _UU03a0_ d1 a ->
                               Logic.eq_rect
                                 (Datatypes.app ((:) ((:) ((,) ((,) _UU0393_
                                   (Datatypes.app _UU0394_1 (Datatypes.app ((:) a ([])) _UU0394_2)))
                                   d1) ([])) ([])) ((:) ((:) ((,) ((,)
                                   (Datatypes.app _UU03a3_1 (Datatypes.app ((:) a ([])) _UU03a3_2))
                                   _UU03a0_) d1) ([])) ([]))) (\_ ->
                                 Logic.eq_rect ((:) ((,) ((,)
                                   (Datatypes.app _UU0393_ (Datatypes.app _UU03a3_1 _UU03a3_2))
                                   (Datatypes.app _UU0394_1 (Datatypes.app _UU0394_2 _UU03a0_))) d1)
                                   ([]))
                                   (Logic.eq_rect
                                     (Datatypes.app ((:) ((:) ((,) ((,) _UU0393_
                                       (Datatypes.app _UU0394_1
                                         (Datatypes.app ((:) a ([])) _UU0394_2))) d1) ([])) ([]))
                                       ((:) ((:) ((,) ((,)
                                       (Datatypes.app _UU03a3_1
                                         (Datatypes.app ((:) a ([])) _UU03a3_2)) _UU03a0_) d1) ([]))
                                       ([]))) (\d2 l2 x4 _ _ h3 ->
                                     Logic.eq_rect ((:) ((,) ((,)
                                       (Datatypes.app _UU0393_ (Datatypes.app _UU03a3_1 _UU03a3_2))
                                       (Datatypes.app _UU0394_1 (Datatypes.app _UU0394_2 _UU03a0_)))
                                       d1) ([])) (\_ _ _ _ _ _ ->
                                       let {
                                        x5 = Dd_fc.dersrec_double_verb
                                               (LntT.nslclext g ((:) ((,) ((,) _UU0393_
                                                 (Datatypes.app _UU0394_1
                                                   (Datatypes.app ((:) a ([])) _UU0394_2))) d1)
                                                 ([])))
                                               (LntT.nslclext g ((:) ((,) ((,)
                                                 (Datatypes.app _UU03a3_1
                                                   (Datatypes.app ((:) a ([])) _UU03a3_2)) _UU03a0_)
                                                 d1) ([]))) d2}
                                       in
                                       case x5 of {
                                        Specif.Coq_existT d3 s ->
                                         case s of {
                                          Specif.Coq_existT d4 _ ->
                                           let {
                                            s0 = Merge.merge_ex g g
                                                   (Structural_equivalence.struct_equiv_weak_refl g)}
                                           in
                                           case s0 of {
                                            Specif.Coq_existT g3 hG3 ->
                                             Lnt_contraction_mrT.derrec_mergeL g ((:) ((,) ((,)
                                               (Datatypes.app _UU0393_
                                                 (Datatypes.app _UU03a3_1 _UU03a3_2))
                                               (Datatypes.app _UU0394_1
                                                 (Datatypes.app _UU0394_2 _UU03a0_))) d1) ([])) g3
                                               hG3
                                               (coq_LNSKt_cut_admissibility
                                                 (Datatypes.app g ((:) ((,) ((,) _UU0393_
                                                   (Datatypes.app _UU0394_1
                                                     (Datatypes.app ((:) a ([])) _UU0394_2))) d1)
                                                   ([])))
                                                 (Datatypes.app g ((:) ((,) ((,)
                                                   (Datatypes.app _UU03a3_1
                                                     (Datatypes.app ((:) a ([])) _UU03a3_2))
                                                   _UU03a0_) d1) ([])))
                                                 (x
                                                   (Dd_fc.derrec_height
                                                     (Datatypes.app g ((:) ((,) ((,) _UU0393_
                                                       (Datatypes.app _UU0394_1
                                                         (Datatypes.app ((:) a ([])) _UU0394_2))) d1)
                                                       ([]))) d3) __
                                                   (Datatypes.app g ((:) ((,) ((,) _UU0393_
                                                     (Datatypes.app _UU0394_1
                                                       (Datatypes.app ((:) a ([])) _UU0394_2))) d1)
                                                     ([]))) d3 __)
                                                 (x
                                                   (Dd_fc.derrec_height
                                                     (Datatypes.app g ((:) ((,) ((,)
                                                       (Datatypes.app _UU03a3_1
                                                         (Datatypes.app ((:) a ([])) _UU03a3_2))
                                                       _UU03a0_) d1) ([]))) d4) __
                                                   (Datatypes.app g ((:) ((,) ((,)
                                                     (Datatypes.app _UU03a3_1
                                                       (Datatypes.app ((:) a ([])) _UU03a3_2))
                                                     _UU03a0_) d1) ([]))) d4 __) g g g3 ((,) _UU0393_
                                                 (Datatypes.app _UU0394_1
                                                   (Datatypes.app ((:) a ([])) _UU0394_2))) ((,)
                                                 (Datatypes.app _UU03a3_1
                                                   (Datatypes.app ((:) a ([])) _UU03a3_2)) _UU03a0_)
                                                 d1 _UU0393_ _UU0394_1 _UU0394_2 _UU03a3_1 _UU03a3_2
                                                 _UU03a0_ a hG3
                                                 (Structural_equivalence.struct_equiv_str_refl g))}}})
                                       c0 l2 h' __ h3 __ x4) ps1 d0 l1 x3 __ __ h2) c0) ps1 __}) ps
                             l0 d __ __ x2) concl l h0 __ __ x1) concl) ps __ h1}) c) ps0 __ x0}) n1}
        in
        Logic.eq_rect_r (DdT.Coq_derI ps concl l d) _evar_0_ h0 __})
      n0) ns h __

