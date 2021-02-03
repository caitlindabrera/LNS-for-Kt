module PeanoNat where

import qualified Prelude
import qualified Datatypes

_Nat__add :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
_Nat__add n m =
  case n of {
   Datatypes.O -> m;
   Datatypes.S p -> Datatypes.S (_Nat__add p m)}

