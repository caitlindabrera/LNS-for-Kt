{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Lemma_Sixteen where

import qualified Prelude
import qualified Datatypes
import qualified LNS
import qualified LNSKt_calculus
import qualified Lemma_Sixteen_SL
import qualified Lemma_Sixteen_SR_bb
import qualified Lemma_Sixteen_SR_p
import qualified Lemma_Sixteen_SR_wb
import qualified Lemma_Sixteen_setup
import qualified Logic
import qualified Ind_lex
import qualified Merge
import qualified Principal
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

coq_SR_wb_base :: Datatypes.Coq_nat -> (Datatypes.Coq_list
                  (Datatypes.Coq_prod
                  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                  (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                  (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                  (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                  (Datatypes.Coq_list
                  (Datatypes.Coq_prod
                  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                  (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                  (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                  (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                  (Datatypes.Coq_list
                  (Datatypes.Coq_prod
                  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                  (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                  (Datatypes.Coq_list
                  (Datatypes.Coq_prod
                  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                  (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                  (LNS.PropF a1) -> LNS.Coq_dir ->
                  (LNSKt_calculus.Coq_pf_LNSKt a1) ->
                  (LNSKt_calculus.Coq_pf_LNSKt a1) ->
                  (LNSKt_calculus.Coq_pf_LNSKt a1) ->
                  (Principal.Coq_principal_WBR a1
                  (LNSKt_calculus.LNSKt_rules a1) ()) ->
                  (Structural_equivalence.Coq_struct_equiv_str a1) ->
                  (Merge.Coq_merge a1) -> LNSKt_calculus.Coq_pf_LNSKt 
                  a1
coq_SR_wb_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Logic.coq_False_rect

coq_SR_bb_base :: Datatypes.Coq_nat -> (Datatypes.Coq_list
                  (Datatypes.Coq_prod
                  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                  (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                  (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                  (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                  (Datatypes.Coq_list
                  (Datatypes.Coq_prod
                  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                  (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                  (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                  (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                  (Datatypes.Coq_list
                  (Datatypes.Coq_prod
                  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                  (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                  (Datatypes.Coq_list
                  (Datatypes.Coq_prod
                  (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                  (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                  (LNS.PropF a1) -> LNS.Coq_dir ->
                  (LNSKt_calculus.Coq_pf_LNSKt a1) ->
                  (LNSKt_calculus.Coq_pf_LNSKt a1) ->
                  (LNSKt_calculus.Coq_pf_LNSKt a1) ->
                  (Principal.Coq_principal_BBR a1
                  (LNSKt_calculus.LNSKt_rules a1) ()) ->
                  (Structural_equivalence.Coq_struct_equiv_str a1) ->
                  (Merge.Coq_merge a1) -> LNSKt_calculus.Coq_pf_LNSKt 
                  a1
coq_SR_bb_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Logic.coq_False_rect

coq_SR_p_base :: Datatypes.Coq_nat -> (Datatypes.Coq_list
                 (Datatypes.Coq_prod
                 (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                 (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                 (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                 (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                 (Datatypes.Coq_list
                 (Datatypes.Coq_prod
                 (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                 (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                 (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                 (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                 (Datatypes.Coq_list
                 (Datatypes.Coq_prod
                 (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                 (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                 (LNS.LNS a1) -> (LNS.PropF a1) -> LNS.Coq_dir ->
                 (LNSKt_calculus.Coq_pf_LNSKt a1) ->
                 (LNSKt_calculus.Coq_pf_LNSKt a1) ->
                 (Principal.Coq_principal_not_box_R a1) -> (Size.Coq_not_box
                 a1) -> (Structural_equivalence.Coq_struct_equiv_str 
                 a1) -> (Merge.Coq_merge a1) -> LNSKt_calculus.Coq_pf_LNSKt
                 a1
coq_SR_p_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Logic.coq_False_rect

coq_SL_base :: Datatypes.Coq_nat -> (Datatypes.Coq_list
               (Datatypes.Coq_prod
               (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
               (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
               (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
               (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
               (Datatypes.Coq_list
               (Datatypes.Coq_prod
               (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
               (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
               (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
               (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
               (Datatypes.Coq_list
               (Datatypes.Coq_prod
               (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
               (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) -> (LNS.LNS
               a1) -> (LNS.PropF a1) -> LNS.Coq_dir ->
               (LNSKt_calculus.Coq_pf_LNSKt a1) ->
               (LNSKt_calculus.Coq_pf_LNSKt a1) ->
               (Structural_equivalence.Coq_struct_equiv_str a1) ->
               (Merge.Coq_merge a1) -> LNSKt_calculus.Coq_pf_LNSKt a1
coq_SL_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Logic.coq_False_rect

coq_Lemma_Sixteen_base_case :: Datatypes.Coq_nat -> Datatypes.Coq_prod
                               (Datatypes.Coq_prod
                               (Datatypes.Coq_prod
                               Lemma_Sixteen_setup.SR_wb_pre
                               Lemma_Sixteen_setup.SR_bb_pre)
                               Lemma_Sixteen_setup.SR_p_pre)
                               Lemma_Sixteen_setup.SL_pre
coq_Lemma_Sixteen_base_case m =
  Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_pair
    (\_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 _ x15 x16 _ ->
    coq_SR_wb_base m x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      x16)
    (\_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 _ x15 x16 _ ->
    coq_SR_bb_base m x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      x16)) (\_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 _ _ ->
    coq_SR_p_base m x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13))
    (\_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
    coq_SL_base m x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)

coq_Lemma_Sixteen :: (Datatypes.Coq_prod Datatypes.Coq_nat Datatypes.Coq_nat)
                     -> Datatypes.Coq_prod
                     (Datatypes.Coq_prod
                     (Datatypes.Coq_prod Lemma_Sixteen_setup.SR_wb
                     Lemma_Sixteen_setup.SR_bb) Lemma_Sixteen_setup.SR_p)
                     Lemma_Sixteen_setup.SL
coq_Lemma_Sixteen nm =
  Ind_lex.wf_lt_lex_nat_inductionT (\nm0 x ->
    (case nm0 of {
      Datatypes.Coq_pair n m -> (\x0 ->
       (case n of {
         Datatypes.O -> (\_ -> unsafeCoerce coq_Lemma_Sixteen_base_case m);
         Datatypes.S n0 -> (\x1 ->
          let {
           hSRwb = \_ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 _ x18 x19 _ ->
            Lemma_Sixteen_SR_wb.coq_Lemma_Sixteen_SR_wb n0 m x1 x2 x3 x4 x5
              x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19}
          in
          let {
           hSRbb = \_ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 _ x18 x19 _ ->
            Lemma_Sixteen_SR_bb.coq_Lemma_Sixteen_SR_bb n0 m x1 x2 x3 x4 x5
              x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19}
          in
          let {
           hSRp = \_ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 _ _ ->
            Lemma_Sixteen_SR_p.coq_Lemma_Sixteen_SR_p n0 m hSRwb hSRbb x1 x2
              x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16}
          in
          let {
           hSL = \_ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 _ _ ->
            Lemma_Sixteen_SL.coq_Lemma_Sixteen_SL n0 m hSRwb hSRbb hSRp x1 x2
              x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15}
          in
          Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_pair
          (unsafeCoerce hSRwb) (unsafeCoerce hSRbb)) (unsafeCoerce hSRp))
          (unsafeCoerce hSL))}) x0)}) x) nm

