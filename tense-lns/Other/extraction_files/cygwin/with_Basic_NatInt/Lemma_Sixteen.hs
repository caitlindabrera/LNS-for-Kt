{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Lemma_Sixteen where

import qualified Prelude
import qualified Lemma_Sixteen_SL
import qualified Lemma_Sixteen_SR_bb
import qualified Lemma_Sixteen_SR_p
import qualified Lemma_Sixteen_SR_wb
import qualified Lemma_Sixteen_setup
import qualified Logic
import qualified DdT
import qualified Gen_tacs
import qualified Ind_lex
import qualified LntT
import qualified Lntkt_exchT
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

coq_SR_wb_base :: Prelude.Int -> (([])
                  ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                  LntT.Coq_dir)) -> (([]) (LntT.PropF a1)) -> (([])
                  (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                  ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                  LntT.Coq_dir)) -> (([]) (LntT.PropF a1)) -> (([])
                  (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                  ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                  LntT.Coq_dir)) -> (([])
                  ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                  LntT.Coq_dir)) -> (LntT.PropF a1) -> LntT.Coq_dir ->
                  (DdT.Coq_derrec
                  (([])
                  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                  (Lntkt_exchT.LNSKt_rules a1) ()) -> (DdT.Coq_derrec
                  (([])
                  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                  (Lntkt_exchT.LNSKt_rules a1) ()) -> (DdT.Coq_derrec
                  (([])
                  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                  (Lntkt_exchT.LNSKt_rules a1) ()) ->
                  (Principal.Coq_principal_WBR a1 (Lntkt_exchT.LNSKt_rules a1)
                  ()) -> (Structural_equivalence.Coq_struct_equiv_str 
                  a1) -> (Merge.Coq_merge a1) -> DdT.Coq_derrec
                  (([])
                  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                  (Lntkt_exchT.LNSKt_rules a1) ()
coq_SR_wb_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Logic.coq_False_rect

coq_SR_bb_base :: Prelude.Int -> (([])
                  ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                  LntT.Coq_dir)) -> (([]) (LntT.PropF a1)) -> (([])
                  (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                  ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                  LntT.Coq_dir)) -> (([]) (LntT.PropF a1)) -> (([])
                  (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                  ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                  LntT.Coq_dir)) -> (([])
                  ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                  LntT.Coq_dir)) -> (LntT.PropF a1) -> LntT.Coq_dir ->
                  (DdT.Coq_derrec
                  (([])
                  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                  (Lntkt_exchT.LNSKt_rules a1) ()) -> (DdT.Coq_derrec
                  (([])
                  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                  (Lntkt_exchT.LNSKt_rules a1) ()) -> (DdT.Coq_derrec
                  (([])
                  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                  (Lntkt_exchT.LNSKt_rules a1) ()) ->
                  (Principal.Coq_principal_BBR a1 (Lntkt_exchT.LNSKt_rules a1)
                  ()) -> (Structural_equivalence.Coq_struct_equiv_str 
                  a1) -> (Merge.Coq_merge a1) -> DdT.Coq_derrec
                  (([])
                  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                  (Lntkt_exchT.LNSKt_rules a1) ()
coq_SR_bb_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Logic.coq_False_rect

coq_SR_p_base :: Prelude.Int -> (([])
                 ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                 LntT.Coq_dir)) -> (([]) (LntT.PropF a1)) -> (([])
                 (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                 ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                 LntT.Coq_dir)) -> (([]) (LntT.PropF a1)) -> (([])
                 (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                 ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
                 LntT.Coq_dir)) -> (([])
                 ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                 -> (LntT.PropF a1) -> LntT.Coq_dir -> (DdT.Coq_derrec
                 (([])
                 ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                 (Lntkt_exchT.LNSKt_rules a1) ()) -> (DdT.Coq_derrec
                 (([])
                 ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                 (Lntkt_exchT.LNSKt_rules a1) ()) ->
                 (Principal.Coq_principal_not_box_R a1) -> (Size.Coq_not_box
                 a1) -> (Structural_equivalence.Coq_struct_equiv_str a1) ->
                 (Merge.Coq_merge a1) -> DdT.Coq_derrec
                 (([])
                 ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                 (Lntkt_exchT.LNSKt_rules a1) ()
coq_SR_p_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Logic.coq_False_rect

coq_SL_base :: Prelude.Int -> (([])
               ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
               LntT.Coq_dir)) -> (([]) (LntT.PropF a1)) -> (([])
               (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
               ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
               LntT.Coq_dir)) -> (([]) (LntT.PropF a1)) -> (([])
               (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
               ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1)))
               LntT.Coq_dir)) -> (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               -> (LntT.PropF a1) -> LntT.Coq_dir -> (DdT.Coq_derrec
               (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               (Lntkt_exchT.LNSKt_rules a1) ()) -> (DdT.Coq_derrec
               (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               (Lntkt_exchT.LNSKt_rules a1) ()) ->
               (Structural_equivalence.Coq_struct_equiv_str a1) ->
               (Merge.Coq_merge a1) -> DdT.Coq_derrec
               (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               (Lntkt_exchT.LNSKt_rules a1) ()
coq_SL_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Logic.coq_False_rect

coq_Lemma_Sixteen_base_case :: Prelude.Int -> (,)
                               ((,)
                               ((,) Lemma_Sixteen_setup.SR_wb_pre
                               Lemma_Sixteen_setup.SR_bb_pre)
                               Lemma_Sixteen_setup.SR_p_pre)
                               Lemma_Sixteen_setup.SL_pre
coq_Lemma_Sixteen_base_case m =
  (,) ((,) ((,)
    (\_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 _ x15 x16 _ ->
    coq_SR_wb_base m x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      x16)
    (\_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 _ x15 x16 _ ->
    coq_SR_bb_base m x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      x16)) (\_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 _ _ ->
    coq_SR_p_base m x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13))
    (\_ x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
    coq_SL_base m x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)

coq_Lemma_Sixteen :: ((,) Prelude.Int Prelude.Int) -> (,)
                     ((,)
                     ((,) Lemma_Sixteen_setup.SR_wb Lemma_Sixteen_setup.SR_bb)
                     Lemma_Sixteen_setup.SR_p) Lemma_Sixteen_setup.SL
coq_Lemma_Sixteen nm =
  Ind_lex.wf_le_lex_nat_induction (\nm0 x ->
    case nm0 of {
     (,) n m ->
      (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
        (\_ -> unsafeCoerce coq_Lemma_Sixteen_base_case m)
        (\n0 ->
        let {
         hSRwb = \x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 ->
          Lemma_Sixteen_SR_wb.coq_Lemma_Sixteen_SR_wb n0 m x x0 x1 x2 x3 x4 x5
            x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17}
        in
        let {
         hSRbb = \x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 ->
          Lemma_Sixteen_SR_bb.coq_Lemma_Sixteen_SR_bb n0 m x x0 x1 x2 x3 x4 x5
            x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17}
        in
        let {
         hSRp = \x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ->
          Lemma_Sixteen_SR_p.coq_Lemma_Sixteen_SR_p n0 m
            (\_ x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 _ x31 x32 _ ->
            hSRwb x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
              x30 x31 x32)
            (\_ x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 _ x31 x32 _ ->
            hSRbb x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
              x30 x31 x32) x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14}
        in
        let {
         hSL = \x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 ->
          Lemma_Sixteen_SL.coq_Lemma_Sixteen_SL n0 m
            (\_ x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 _ x30 x31 _ ->
            hSRwb x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
              x29 x30 x31)
            (\_ x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 _ x30 x31 _ ->
            hSRbb x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
              x29 x30 x31)
            (\_ x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 _ _ ->
            hSRp x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28)
            x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13}
        in
        (,) ((,) ((,)
        (\_ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 _ x16 x17 _ ->
        unsafeCoerce hSRwb x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
          x15 x16 x17)
        (\_ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 _ x16 x17 _ ->
        unsafeCoerce hSRbb x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14
          x15 x16 x17))
        (\_ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 _ _ ->
        unsafeCoerce hSRp x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14))
        (\_ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 _ _ ->
        unsafeCoerce hSL x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13))
        n}) nm

