module Ind_lex where

import qualified Prelude
import qualified Datatypes
import qualified Wf

wf_le_lex_nat_induction :: ((Datatypes.Coq_prod Datatypes.Coq_nat
                           Datatypes.Coq_nat) -> ((Datatypes.Coq_prod
                           Datatypes.Coq_nat Datatypes.Coq_nat) -> () -> a1)
                           -> a1) -> (Datatypes.Coq_prod Datatypes.Coq_nat
                           Datatypes.Coq_nat) -> a1
wf_le_lex_nat_induction =
  Wf.well_founded_induction_type

