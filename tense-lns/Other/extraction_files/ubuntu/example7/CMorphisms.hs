module CMorphisms where

import qualified Prelude
import qualified CRelationClasses
import qualified Logic

trans_co_eq_inv_arrow_morphism_obligation_1 :: (CRelationClasses.Transitive a1 a2) -> a1 -> a1 -> a2
                                               -> a1 -> a1 -> CRelationClasses.Coq_arrow a2 a2
trans_co_eq_inv_arrow_morphism_obligation_1 h x y x0 x1 y0 x2 =
  Logic.eq_rect_r y0 (CRelationClasses.transitivity h x y y0 x0 x2) x1

trans_co_eq_inv_arrow_morphism :: (CRelationClasses.Transitive a1 a2) -> a1 -> a1 -> a2 -> a1 -> a1
                                  -> CRelationClasses.Coq_arrow a2 a2
trans_co_eq_inv_arrow_morphism =
  trans_co_eq_inv_arrow_morphism_obligation_1

