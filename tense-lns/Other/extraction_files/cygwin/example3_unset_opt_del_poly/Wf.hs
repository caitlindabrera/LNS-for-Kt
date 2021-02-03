module Wf where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

coq_Acc_rect :: (a1 -> () -> (a1 -> () -> a2) -> a2) -> a1 -> a2
coq_Acc_rect f x =
  let {
   f0 x0 _ =
     f x0 __ (\y _ -> f0 y __)}
  in f0 x __

well_founded_induction_type :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction_type x a =
  coq_Acc_rect (\x0 _ x1 -> x x0 x1) a

