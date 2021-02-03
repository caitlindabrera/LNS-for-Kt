module Size where

import qualified Prelude
import qualified Datatypes
import qualified Nat
import qualified LntT

fsize :: (LntT.PropF a1) -> Datatypes.Coq_nat
fsize a =
  case a of {
   LntT.Var _ -> Datatypes.S Datatypes.O;
   LntT.Bot -> Datatypes.S Datatypes.O;
   LntT.Imp b c -> Datatypes.S (Nat.add (fsize b) (fsize c));
   LntT.WBox b -> Datatypes.S (fsize b);
   LntT.BBox b -> Datatypes.S (fsize b)}

data Coq_not_box v =
   Coq_nb_Var v
 | Coq_nb_Bot
 | Coq_nb_Imp (LntT.PropF v) (LntT.PropF v)

