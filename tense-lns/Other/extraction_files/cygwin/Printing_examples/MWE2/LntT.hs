module LntT where

import qualified Prelude
import qualified Datatypes

data Coq_dir =
   Coq_fwd
 | Coq_bac
 deriving Prelude.Show

data PropF v =
   Var v
 | Bot
 | Imp (PropF v) (PropF v)
 | WBox (PropF v)
 | BBox (PropF v)
 deriving Prelude.Show

data Coq_princrule_pfc v =
   Id_pfc v
 | ImpR_pfc (PropF v) (PropF v)
 | ImpL_pfc (PropF v) (PropF v)
 | BotL_pfc
 deriving Prelude.Show

nslcext :: (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)) -> Coq_dir -> a1 ->
           Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)
nslcext g d seq =
  Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair seq d) Datatypes.Coq_nil)

data Coq_nslcrule w sr =
   NSlcctxt (Datatypes.Coq_list w) w (Datatypes.Coq_list
                                     (Datatypes.Coq_prod w Coq_dir)) Coq_dir 
 sr
 deriving Prelude.Show

data Coq_nslclrule w sr =
   NSlclctxt (Datatypes.Coq_list (Datatypes.Coq_list w)) (Datatypes.Coq_list w) 
 (Datatypes.Coq_list w) sr
 deriving Prelude.Show

