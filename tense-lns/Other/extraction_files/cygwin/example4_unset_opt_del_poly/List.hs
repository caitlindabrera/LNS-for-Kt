module List where

import qualified Prelude
import qualified Datatypes

map :: (a1 -> a2) -> (Datatypes.Coq_list a1) -> Datatypes.Coq_list a2
map f =
  let {
   map0 l =
     case l of {
      Datatypes.Coq_nil -> Datatypes.Coq_nil;
      Datatypes.Coq_cons a t -> Datatypes.Coq_cons (f a) (map0 t)}}
  in map0

