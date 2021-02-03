module Size where

import qualified Prelude
import qualified LntT

fsize :: (LntT.PropF a1) -> Prelude.Int
fsize a =
  case a of {
   LntT.Imp b c -> Prelude.succ ((Prelude.+) (fsize b) (fsize c));
   LntT.WBox b -> Prelude.succ (fsize b);
   LntT.BBox b -> Prelude.succ (fsize b);
   _ -> Prelude.succ 0}

data Coq_not_box v =
   Coq_nb_Var v
 | Coq_nb_Bot
 | Coq_nb_Imp (LntT.PropF v) (LntT.PropF v)

