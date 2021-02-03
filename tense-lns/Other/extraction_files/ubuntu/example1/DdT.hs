{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module DdT where

import qualified Prelude
import qualified CMorphisms
import qualified CRelationClasses
import qualified Datatypes
import qualified List
import qualified Logic
import qualified GenT

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

data Coq_derrec x rules prems =
   Coq_dpI x prems
 | Coq_derI (([]) x) x rules (Coq_dersrec x rules prems)
data Coq_dersrec x rules prems =
   Coq_dlNil
 | Coq_dlCons x (([]) x) (Coq_derrec x rules prems) (Coq_dersrec x rules prems)

dersrec_rect :: a4 -> (a1 -> (([]) a1) -> (Coq_derrec a1 a2 a3) -> (Coq_dersrec a1 a2 a3) -> a4 ->
                a4) -> (([]) a1) -> (Coq_dersrec a1 a2 a3) -> a4
dersrec_rect f f0 _ d =
  case d of {
   Coq_dlNil -> f;
   Coq_dlCons seq seqs d0 d1 -> f0 seq seqs d0 d1 (dersrec_rect f f0 seqs d1)}

derrec_rect_mut :: (a1 -> a3 -> a4) -> ((([]) a1) -> a1 -> a2 -> (Coq_dersrec a1 a2 a3) -> a5 -> a4)
                   -> a5 -> (a1 -> (([]) a1) -> (Coq_derrec a1 a2 a3) -> a4 -> (Coq_dersrec a1 
                   a2 a3) -> a5 -> a5) -> a1 -> (Coq_derrec a1 a2 a3) -> a4
derrec_rect_mut f f0 f1 f2 =
  let {
   f3 _ d =
     case d of {
      Coq_dpI concl y -> f concl y;
      Coq_derI ps concl y d0 -> f0 ps concl y d0 (f4 ps d0)};
   f4 _ d =
     case d of {
      Coq_dlNil -> f1;
      Coq_dlCons seq seqs d0 d1 -> f2 seq seqs d0 (f3 seq d0) d1 (f4 seqs d1)}}
  in f3

dim_allT :: (a1 -> a3 -> a4) -> ((([]) a1) -> a1 -> a2 -> (Coq_dersrec a1 a2 a3) -> (GenT.ForallT 
            a1 a4) -> a4) -> (GenT.ForallT a1 a4) -> (a1 -> (([]) a1) -> (Coq_derrec a1 a2 a3) -> a4
            -> (Coq_dersrec a1 a2 a3) -> (GenT.ForallT a1 a4) -> GenT.ForallT a1 a4) -> a1 ->
            (Coq_derrec a1 a2 a3) -> a4
dim_allT =
  derrec_rect_mut

derrec_all_indT :: (a1 -> a3 -> a4) -> ((([]) a1) -> a1 -> a2 -> (Coq_dersrec a1 a2 a3) ->
                   (GenT.ForallT a1 a4) -> a4) -> a1 -> (Coq_derrec a1 a2 a3) -> a4
derrec_all_indT h h0 =
  dim_allT h h0 GenT.ForallT_nil (\seq seqs _ x0 _ x1 -> GenT.ForallT_cons seq seqs x0 x1)

dersrec_all :: (([]) a1) -> CRelationClasses.Coq_iffT (Coq_dersrec a1 a2 a3)
               (GenT.ForallT a1 (Coq_derrec a1 a2 a3))
dersrec_all cs =
  Datatypes.list_rect ((,) (\_ -> GenT.ForallT_nil) (\_ -> Coq_dlNil)) (\a cs0 iHcs -> (,) (\x0 ->
    case x0 of {
     Coq_dlNil -> Logic.coq_False_rect;
     Coq_dlCons seq seqs x1 x2 ->
      Logic.eq_rect_r a (\_ ->
        Logic.eq_rect_r cs0 (\x3 x4 -> GenT.ForallT_cons a cs0 x3 (case iHcs of {
                                                                    (,) f _ -> f x4})) seqs) seq __
        x1 x2}) (\x0 ->
    case x0 of {
     GenT.ForallT_nil -> Logic.coq_False_rect;
     GenT.ForallT_cons x l x1 x2 ->
      Logic.eq_rect_r a (\_ ->
        Logic.eq_rect_r cs0 (\x3 x4 -> Coq_dlCons a cs0 x3 (case iHcs of {
                                                             (,) _ d -> d x4})) l) x __ x1 x2})) cs

dersrec_forall :: (([]) a1) -> CRelationClasses.Coq_iffT (Coq_dersrec a1 a2 a3)
                  (a1 -> (GenT.InT a1) -> Coq_derrec a1 a2 a3)
dersrec_forall cs =
  let {lemma = dersrec_all cs} in
  CMorphisms.trans_co_eq_inv_arrow_morphism
    (unsafeCoerce (\_ _ _ -> CRelationClasses.iffT_Transitive)) __ __ (unsafeCoerce lemma) __ __
    (let {lemma0 = GenT.coq_ForallT_forall cs} in
     CMorphisms.trans_co_eq_inv_arrow_morphism
       (unsafeCoerce (\_ _ _ -> CRelationClasses.iffT_Transitive)) __ __ (unsafeCoerce lemma0) __ __
       (CRelationClasses.reflexivity (unsafeCoerce (\_ -> CRelationClasses.iffT_Reflexive)) __))

dersrecI_forall :: (([]) a1) -> (a1 -> (GenT.InT a1) -> Coq_derrec a1 a2 a3) -> Coq_dersrec a1 a2 a3
dersrecI_forall cs =
  GenT.iffT_D2 (dersrec_forall cs)

dersrec_nil :: Coq_dersrec a1 a2 a3
dersrec_nil =
  Coq_dlNil

dersrec_single :: a1 -> CRelationClasses.Coq_iffT (Coq_dersrec a1 a2 a3) (Coq_derrec a1 a2 a3)
dersrec_single c =
  let {lemma = dersrec_all ((:) c ([]))} in
  CMorphisms.trans_co_eq_inv_arrow_morphism
    (unsafeCoerce (\_ _ _ -> CRelationClasses.iffT_Transitive)) __ __ (unsafeCoerce lemma) __ __
    (let {lemma0 = GenT.coq_ForallT_single c} in
     CMorphisms.trans_co_eq_inv_arrow_morphism
       (unsafeCoerce (\_ _ _ -> CRelationClasses.iffT_Transitive)) __ __ (unsafeCoerce lemma0) __ __
       (CRelationClasses.reflexivity (unsafeCoerce (\_ -> CRelationClasses.iffT_Reflexive)) __))

dersrec_map_single :: (a1 -> a2) -> a1 -> CRelationClasses.Coq_iffT (Coq_dersrec a2 a3 a4)
                      (Coq_derrec a2 a3 a4)
dersrec_map_single f c =
  dersrec_single (f c)

dersrec_map_2 :: (a1 -> a2) -> a1 -> a1 -> CRelationClasses.Coq_iffT (Coq_dersrec a2 a3 a4)
                 ((,) (Coq_derrec a2 a3 a4) (Coq_derrec a2 a3 a4))
dersrec_map_2 f c d =
  let {lemma = dersrec_all (List.map f ((:) c ((:) d ([]))))} in
  CMorphisms.trans_co_eq_inv_arrow_morphism
    (unsafeCoerce (\_ _ _ -> CRelationClasses.iffT_Transitive)) __ __ (unsafeCoerce lemma) __ __
    (let {lemma0 = GenT.coq_ForallT_map_2 f c d} in
     CMorphisms.trans_co_eq_inv_arrow_morphism
       (unsafeCoerce (\_ _ _ -> CRelationClasses.iffT_Transitive)) __ __ (unsafeCoerce lemma0) __ __
       (CRelationClasses.reflexivity (unsafeCoerce (\_ -> CRelationClasses.iffT_Reflexive)) __))

