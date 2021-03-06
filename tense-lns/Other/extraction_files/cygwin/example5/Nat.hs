module Nat where

import qualified Prelude
import qualified Datatypes

add :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
add n m =
  case n of {
   Datatypes.O -> m;
   Datatypes.S p -> Datatypes.S (add p m)}

sub :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
sub n m =
  case n of {
   Datatypes.O -> n;
   Datatypes.S k -> case m of {
                     Datatypes.O -> n;
                     Datatypes.S l -> sub k l}}

max :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> Datatypes.Coq_nat
max n m =
  case n of {
   Datatypes.O -> m;
   Datatypes.S n' -> case m of {
                      Datatypes.O -> n;
                      Datatypes.S m' -> Datatypes.S (max n' m')}}

