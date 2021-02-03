module Gen_tacs where

import qualified Prelude
import qualified Datatypes
import qualified Logic

__ :: any
__ = Prelude.error "Logical or arity value used"

type Coq_rel w = Datatypes.Coq_prod w w

app_eq_unitT :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> a1 -> Datatypes.Coq_sum () ()
app_eq_unitT x y a =
  (case x of {
    Datatypes.Coq_nil -> (\_ -> Datatypes.Coq_inl __);
    Datatypes.Coq_cons a0 x0 -> (\_ ->
     Logic.eq_rec_r a (\_ ->
       Logic.eq_rec (Datatypes.app x0 y)
         (Logic.eq_rec_r a (\_ ->
           Logic.eq_rec_r Datatypes.Coq_nil (\_ ->
             Logic.eq_rec_r Datatypes.Coq_nil (\_ -> Datatypes.Coq_inr __) y __) x0 __) a0 __)
         Datatypes.Coq_nil) a0 __)}) __

unit_eq_appT :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> a1 -> Datatypes.Coq_sum () ()
unit_eq_appT =
  app_eq_unitT

