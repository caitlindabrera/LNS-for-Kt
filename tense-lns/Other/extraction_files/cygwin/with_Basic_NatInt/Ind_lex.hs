module Ind_lex where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Wf

__ :: any
__ = Prelude.error "Logical or arity value used"

wf_le_lex_nat_induction :: (((,) Prelude.Int Prelude.Int) -> (((,) Prelude.Int
                           Prelude.Int) -> () -> a1) -> a1) -> ((,)
                           Prelude.Int Prelude.Int) -> a1
wf_le_lex_nat_induction =
  Wf.well_founded_induction_type

lt_wf_indT :: Prelude.Int -> (Prelude.Int -> (Prelude.Int -> () -> a1) -> a1)
              -> a1
lt_wf_indT n x =
  Datatypes.nat_rect (\_ iH -> iH 0 (\_ _ -> Logic.coq_False_rect))
    (\_ iHn _ iH ->
    iHn __ (\u hu ->
      iH (Prelude.succ u) (\v _ ->
        (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> iH 0 (\_ _ -> Logic.coq_False_rect))
          (\v0 -> hu v0 __)
          v))) n __ x

