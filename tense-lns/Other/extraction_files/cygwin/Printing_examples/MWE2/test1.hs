module Top where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Logic
import qualified Gen_seq
import qualified Gen_tacs
import qualified LntT

data Coq_derrec x rules prems =
   Coq_dpI x prems
 | Coq_derI (Datatypes.Coq_list x) x rules (Coq_dersrec x rules prems)
-- deriving Prelude.Show

data Coq_dersrec x rules prems =
   Coq_dlNil
 | Coq_dlCons x (Datatypes.Coq_list x) (Coq_derrec x rules prems) (Coq_dersrec 
                                                                  x rules prems)
-- deriving Prelude.Show

derrec_same :: a1 -> a1 -> (Coq_derrec a1 a2 a3) -> Coq_derrec a1 a2 a3
derrec_same c c' x0 =
  Logic.eq_rect_r c' (\x1 -> x1) c x0

