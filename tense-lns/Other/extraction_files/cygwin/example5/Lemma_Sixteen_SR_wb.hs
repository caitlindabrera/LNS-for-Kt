{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Lemma_Sixteen_SR_wb where

import qualified Prelude
import qualified Datatypes
import qualified Lemma_Sixteen_SR_wb_bac
import qualified Lemma_Sixteen_SR_wb_fwd
import qualified Lemma_Sixteen_setup
import qualified DdT
import qualified Gen_tacs
import qualified LntT
import qualified Lntkt_exchT
import qualified Merge
import qualified Principal
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

coq_Lemma_Sixteen_SR_wb :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> ((Datatypes.Coq_prod Datatypes.Coq_nat Datatypes.Coq_nat) -> () -> Datatypes.Coq_prod
                           (Datatypes.Coq_prod (Datatypes.Coq_prod Lemma_Sixteen_setup.SR_wb Lemma_Sixteen_setup.SR_bb) Lemma_Sixteen_setup.SR_p) Lemma_Sixteen_setup.SL) ->
                           (Datatypes.Coq_list
                           (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                           (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                           (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                           (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                           (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) ->
                           (Datatypes.Coq_list
                           (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF a1)) (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) -> (LntT.PropF
                           a1) -> LntT.Coq_dir -> (DdT.Coq_derrec
                           (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules a1) 
                           ()) -> (DdT.Coq_derrec (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                           (Lntkt_exchT.LNSKt_rules a1) ()) -> (DdT.Coq_derrec
                           (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules a1) 
                           ()) -> (Principal.Coq_principal_WBR a1 (Lntkt_exchT.LNSKt_rules a1) ()) -> (Structural_equivalence.Coq_struct_equiv_str a1) -> (Merge.Coq_merge
                           a1) -> DdT.Coq_derrec (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                           (Lntkt_exchT.LNSKt_rules a1) ()
coq_Lemma_Sixteen_SR_wb n m iH g _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a d d1 d2 d3 x x0 x1 =
  unsafeCoerce Lemma_Sixteen_setup.coq_SR_wb_fwd_bac_rev (Datatypes.Coq_pair (Datatypes.S n) m) (\_ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 _ x17 x18 _ ->
    Lemma_Sixteen_SR_wb_fwd.coq_Lemma_Sixteen_SR_wb_fwd n m iH x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18)
    (\_ x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 _ x17 x18 _ ->
    Lemma_Sixteen_SR_wb_bac.coq_Lemma_Sixteen_SR_wb_bac n m iH x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18) __ g _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_1
    _UU03a3_2 _UU03a0_ i gH a d d1 d2 d3 x __ x0 x1 __

