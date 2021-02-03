module Top where

import qualified Prelude
import qualified Datatypes
import qualified Wf

__ :: any
__ = Prelude.error "Logical or arity value used"

wf_le_lex_nat_induction :: ((Datatypes.Coq_prod Datatypes.Coq_nat Datatypes.Coq_nat) ->
                           ((Datatypes.Coq_prod Datatypes.Coq_nat Datatypes.Coq_nat) -> ()
                           -> a1) -> a1) -> (Datatypes.Coq_prod Datatypes.Coq_nat
                           Datatypes.Coq_nat) -> a1
wf_le_lex_nat_induction =
  Wf.well_founded_induction_type

lem :: (Datatypes.Coq_prod Datatypes.Coq_nat Datatypes.Coq_nat) -> Datatypes.Coq_sum () ()
lem nm =
  wf_le_lex_nat_induction (\nm0 _ ->
    case nm0 of {
     Datatypes.Coq_pair n _ ->
      case n of {
       Datatypes.O -> Datatypes.Coq_inr __;
       Datatypes.S _ -> Datatypes.Coq_inl __}}) nm

lem2 :: (Datatypes.Coq_prod Datatypes.Coq_nat Datatypes.Coq_nat) -> Datatypes.Coq_sum 
        () ()
lem2 nm =
  let {h = lem nm} in
  case h of {
   Datatypes.Coq_inl _ -> Datatypes.Coq_inr __;
   Datatypes.Coq_inr _ -> Datatypes.Coq_inl __}

