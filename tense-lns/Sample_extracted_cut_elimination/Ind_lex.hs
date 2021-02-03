module Ind_lex where

import qualified Prelude
import qualified Datatypes
import qualified Wf

wf_lt_lex_nat_inductionT :: ((Datatypes.Coq_prod Datatypes.Coq_nat
                            Datatypes.Coq_nat) -> ((Datatypes.Coq_prod
                            Datatypes.Coq_nat Datatypes.Coq_nat) -> () -> a1)
                            -> a1) -> (Datatypes.Coq_prod Datatypes.Coq_nat
                            Datatypes.Coq_nat) -> a1
wf_lt_lex_nat_inductionT =
  Wf.well_founded_induction_type

wf_lt_inductionT :: (Datatypes.Coq_nat -> (Datatypes.Coq_nat -> () -> a1) ->
                    a1) -> Datatypes.Coq_nat -> a1
wf_lt_inductionT =
  Wf.well_founded_induction_type

