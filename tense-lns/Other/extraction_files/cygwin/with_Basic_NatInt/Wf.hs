module Wf where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

coq_Acc_rect :: (a1 -> () -> (a1 -> () -> a2) -> a2) -> a1 -> a2
coq_Acc_rect f x =
  f x __ (\y _ -> coq_Acc_rect f y)

well_founded_induction_type :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction_type x a =
  coq_Acc_rect (\x0 _ x1 -> x x0 x1) a

