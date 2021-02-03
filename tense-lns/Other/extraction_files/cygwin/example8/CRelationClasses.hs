module CRelationClasses where

import qualified Prelude
import qualified Datatypes

type Coq_arrow a b = a -> b

type Coq_iffT a b = Datatypes.Coq_prod (a -> b) (b -> a)

type Reflexive a r = a -> r

reflexivity :: (Reflexive a1 a2) -> a1 -> a2
reflexivity reflexive =
  reflexive

type Transitive a r = a -> a -> a -> r -> r -> r

transitivity :: (Transitive a1 a2) -> a1 -> a1 -> a1 -> a2 -> a2 -> a2
transitivity transitive =
  transitive

iffT_Reflexive :: Coq_iffT a1 a1
iffT_Reflexive =
  Datatypes.Coq_pair (\x -> x) (\x -> x)

iffT_Transitive :: (Coq_iffT a1 a2) -> (Coq_iffT a2 a3) -> Coq_iffT a1 a3
iffT_Transitive x x0 =
  Datatypes.prod_rect (\a b ->
    Datatypes.prod_rect (\a0 b0 -> Datatypes.Coq_pair (\x1 ->
      let {x2 = a0 x1} in a x2) (\x1 -> let {x2 = b x1} in b0 x2)) x) x0

