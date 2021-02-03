{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Lemma_Sixteen_setup where

import qualified Prelude
import qualified DdT
import qualified Gen_tacs
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

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

type SR_wb_fwd = Any

type SR_wb_bac = Any

type SR_wb_pre =
  () -> (([]) ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([])
  ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([])
  ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (LntT.PropF Any) ->
  LntT.Coq_dir -> (DdT.Coq_derrec
  (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Any)
  ()) -> (DdT.Coq_derrec (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir))
  (Lntkt_exchT.LNSKt_rules Any) ()) -> (DdT.Coq_derrec
  (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Any)
  ()) -> (Principal.Coq_principal_WBR Any (Lntkt_exchT.LNSKt_rules Any) ()) -> () ->
  (Structural_equivalence.Coq_struct_equiv_str Any) -> (Merge.Coq_merge Any) -> () -> DdT.Coq_derrec
  (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Any)
  ()

type SR_wb = Any

coq_SR_wb_fwd_bac :: ((,) Prelude.Int Prelude.Int) -> SR_wb -> (,) SR_wb_fwd SR_wb_bac
coq_SR_wb_fwd_bac _ h =
  (,)
    (unsafeCoerce (\_ g _UU0393_ _UU0394_1 _UU0394_2 h0 _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a d1 d2 ->
      unsafeCoerce h __ g _UU0393_ _UU0394_1 _UU0394_2 h0 _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a
        LntT.Coq_fwd d1 d2))
    (unsafeCoerce (\_ g _UU0393_ _UU0394_1 _UU0394_2 h0 _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a d1 d2 ->
      unsafeCoerce h __ g _UU0393_ _UU0394_1 _UU0394_2 h0 _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a
        LntT.Coq_bac d1 d2))

coq_SR_wb_fwd_bac_rev :: ((,) Prelude.Int Prelude.Int) -> SR_wb_fwd -> SR_wb_bac -> SR_wb
coq_SR_wb_fwd_bac_rev _ h1 h2 =
  unsafeCoerce (\_ g _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a d d1 d2 ->
    case d of {
     LntT.Coq_fwd ->
      unsafeCoerce h1 __ g _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a d1 d2;
     LntT.Coq_bac ->
      unsafeCoerce h2 __ g _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a d1 d2})

type SR_bb_fwd = Any

type SR_bb_bac = Any

type SR_bb_pre =
  () -> (([]) ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([])
  ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([])
  ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (LntT.PropF Any) ->
  LntT.Coq_dir -> (DdT.Coq_derrec
  (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Any)
  ()) -> (DdT.Coq_derrec (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir))
  (Lntkt_exchT.LNSKt_rules Any) ()) -> (DdT.Coq_derrec
  (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Any)
  ()) -> (Principal.Coq_principal_BBR Any (Lntkt_exchT.LNSKt_rules Any) ()) -> () ->
  (Structural_equivalence.Coq_struct_equiv_str Any) -> (Merge.Coq_merge Any) -> () -> DdT.Coq_derrec
  (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Any)
  ()

type SR_bb = Any

coq_SR_bb_fwd_bac :: ((,) Prelude.Int Prelude.Int) -> SR_bb -> (,) SR_bb_fwd SR_bb_bac
coq_SR_bb_fwd_bac _ h =
  (,)
    (unsafeCoerce (\_ g _UU0393_ _UU0394_1 _UU0394_2 h0 _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a d1 d2 ->
      unsafeCoerce h __ g _UU0393_ _UU0394_1 _UU0394_2 h0 _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a
        LntT.Coq_fwd d1 d2))
    (unsafeCoerce (\_ g _UU0393_ _UU0394_1 _UU0394_2 h0 _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a d1 d2 ->
      unsafeCoerce h __ g _UU0393_ _UU0394_1 _UU0394_2 h0 _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a
        LntT.Coq_bac d1 d2))

coq_SR_bb_fwd_bac_rev :: ((,) Prelude.Int Prelude.Int) -> SR_bb_fwd -> SR_bb_bac -> SR_bb
coq_SR_bb_fwd_bac_rev _ h1 h2 =
  unsafeCoerce (\_ g _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a d d1 d2 ->
    case d of {
     LntT.Coq_fwd ->
      unsafeCoerce h1 __ g _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a d1 d2;
     LntT.Coq_bac ->
      unsafeCoerce h2 __ g _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_1 _UU03a3_2 _UU03a0_ i gH a d1 d2})

type SR_p_pre =
  () -> (([]) ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([])
  ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([])
  ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (LntT.PropF Any) -> LntT.Coq_dir
  -> (DdT.Coq_derrec (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir))
  (Lntkt_exchT.LNSKt_rules Any) ()) -> (DdT.Coq_derrec
  (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Any)
  ()) -> (Principal.Coq_principal_not_box_R Any) -> () -> () -> (Size.Coq_not_box Any) ->
  (Structural_equivalence.Coq_struct_equiv_str Any) -> (Merge.Coq_merge Any) -> DdT.Coq_derrec
  (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Any)
  ()

type SR_p = Any

type SL_pre =
  () -> (([]) ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([])
  ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([]) (LntT.PropF Any)) -> (([])
  ((,) ((,) (([]) (LntT.PropF Any)) (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (([])
  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir)) -> (LntT.PropF Any) -> LntT.Coq_dir
  -> (DdT.Coq_derrec (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir))
  (Lntkt_exchT.LNSKt_rules Any) ()) -> (DdT.Coq_derrec
  (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Any)
  ()) -> () -> () -> (Structural_equivalence.Coq_struct_equiv_str Any) -> (Merge.Coq_merge Any) ->
  DdT.Coq_derrec (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF Any))) LntT.Coq_dir))
  (Lntkt_exchT.LNSKt_rules Any) ()

type SL = Any

