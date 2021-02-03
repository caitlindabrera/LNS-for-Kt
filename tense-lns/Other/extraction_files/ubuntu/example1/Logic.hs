module Logic where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

coq_False_rect :: a1
coq_False_rect =
  Prelude.error "absurd case"

coq_False_rec :: a1
coq_False_rec =
  coq_False_rect

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec =
  and_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

eq_rect_r :: a1 -> a2 -> a1 -> a2
eq_rect_r =
  eq_rect

