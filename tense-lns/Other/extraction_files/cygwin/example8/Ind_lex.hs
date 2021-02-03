module Ind_lex where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Wf

__ :: any
__ = Prelude.error "Logical or arity value used"

wf_le_lex_nat_induction :: ((Datatypes.Coq_prod Datatypes.Coq_nat
                           Datatypes.Coq_nat) -> ((Datatypes.Coq_prod
                           Datatypes.Coq_nat Datatypes.Coq_nat) -> () -> a1)
                           -> a1) -> (Datatypes.Coq_prod Datatypes.Coq_nat
                           Datatypes.Coq_nat) -> a1
wf_le_lex_nat_induction =
  Wf.well_founded_induction_type

lt_wf_indT :: Datatypes.Coq_nat -> (Datatypes.Coq_nat -> (Datatypes.Coq_nat
              -> () -> a1) -> a1) -> a1
lt_wf_indT n x =
  Datatypes.nat_rect (\_ iH -> iH Datatypes.O (\_ _ -> Logic.coq_False_rect))
    (\_ iHn _ iH ->
    iHn __ (\u hu ->
      iH (Datatypes.S u) (\v _ ->
        (case v of {
          Datatypes.O -> (\_ ->
           iH Datatypes.O (\_ _ -> Logic.coq_False_rect));
          Datatypes.S v0 -> (\_ -> hu v0 __)}) __))) n __ x

