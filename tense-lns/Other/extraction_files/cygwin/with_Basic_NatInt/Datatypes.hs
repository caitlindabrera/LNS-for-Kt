module Datatypes where

import qualified Prelude

nat_rect :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

sum_rect :: (a1 -> a3) -> (a2 -> a3) -> (Prelude.Either a1 a2) -> a3
sum_rect f f0 s =
  case s of {
   Prelude.Left x -> f x;
   Prelude.Right x -> f0 x}

sum_rec :: (a1 -> a3) -> (a2 -> a3) -> (Prelude.Either a1 a2) -> a3
sum_rec =
  sum_rect

prod_rect :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
prod_rect f p =
  case p of {
   (,) x x0 -> f x x0}

prod_rec :: (a1 -> a2 -> a3) -> ((,) a1 a2) -> a3
prod_rec =
  prod_rect

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f f0 l =
  case l of {
   ([]) -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rec =
  list_rect

length :: (([]) a1) -> Prelude.Int
length l =
  case l of {
   ([]) -> 0;
   (:) _ l' -> Prelude.succ (length l')}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

