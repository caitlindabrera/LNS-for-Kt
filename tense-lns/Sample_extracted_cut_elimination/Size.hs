module Size where

import qualified Prelude
import qualified Datatypes
import qualified LNS
import qualified Nat

fsize :: (LNS.PropF a1) -> Datatypes.Coq_nat
fsize a =
  case a of {
   LNS.Var _ -> Datatypes.S Datatypes.O;
   LNS.Bot -> Datatypes.S Datatypes.O;
   LNS.Imp b c -> Datatypes.S (Nat.add (fsize b) (fsize c));
   LNS.WBox b -> Datatypes.S (fsize b);
   LNS.BBox b -> Datatypes.S (fsize b)}

data Coq_not_box v =
   Coq_nb_Var v
 | Coq_nb_Bot
 | Coq_nb_Imp (LNS.PropF v) (LNS.PropF v)

