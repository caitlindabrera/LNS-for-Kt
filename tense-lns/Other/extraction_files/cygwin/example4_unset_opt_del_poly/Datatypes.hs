module Datatypes where

import qualified Prelude

data Coq_nat =
   O
 | S Coq_nat

nat_rect :: a1 -> (Coq_nat -> a1 -> a1) -> Coq_nat -> a1
nat_rect f f0 =
  let {
   f1 n =
     case n of {
      O -> f;
      S n0 -> f0 n0 (f1 n0)}}
  in f1

data Coq_sum a b =
   Coq_inl a
 | Coq_inr b

sum_rect :: (a1 -> a3) -> (a2 -> a3) -> (Coq_sum a1 a2) -> a3
sum_rect f f0 s =
  case s of {
   Coq_inl x -> f x;
   Coq_inr x -> f0 x}

sum_rec :: (a1 -> a3) -> (a2 -> a3) -> (Coq_sum a1 a2) -> a3
sum_rec =
  sum_rect

data Coq_prod a b =
   Coq_pair a b

prod_rect :: (a1 -> a2 -> a3) -> (Coq_prod a1 a2) -> a3
prod_rect f p =
  case p of {
   Coq_pair x x0 -> f x x0}

prod_rec :: (a1 -> a2 -> a3) -> (Coq_prod a1 a2) -> a3
prod_rec =
  prod_rect

data Coq_list a =
   Coq_nil
 | Coq_cons a (Coq_list a)

list_rect :: a2 -> (a1 -> (Coq_list a1) -> a2 -> a2) -> (Coq_list a1) -> a2
list_rect f f0 =
  let {
   f1 l =
     case l of {
      Coq_nil -> f;
      Coq_cons y l0 -> f0 y l0 (f1 l0)}}
  in f1

list_rec :: a2 -> (a1 -> (Coq_list a1) -> a2 -> a2) -> (Coq_list a1) -> a2
list_rec =
  list_rect

length :: (Coq_list a1) -> Coq_nat
length l =
  case l of {
   Coq_nil -> O;
   Coq_cons _ l' -> S (length l')}

app :: (Coq_list a1) -> (Coq_list a1) -> Coq_list a1
app l m =
  case l of {
   Coq_nil -> m;
   Coq_cons a l1 -> Coq_cons a (app l1 m)}

