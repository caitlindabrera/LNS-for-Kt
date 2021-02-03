module Datatypes where

import qualified Prelude

data Coq_nat =
   O
 | S Coq_nat

data Coq_prod a b =
   Coq_pair a b

data Coq_list a =
   Coq_nil
 | Coq_cons a (Coq_list a)

app :: (Coq_list a1) -> (Coq_list a1) -> Coq_list a1
app l m =
  case l of {
   Coq_nil -> m;
   Coq_cons a l1 -> Coq_cons a (app l1 m)}

