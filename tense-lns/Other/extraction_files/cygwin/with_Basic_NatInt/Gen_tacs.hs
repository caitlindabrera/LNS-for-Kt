module Gen_tacs where

import qualified Prelude
import qualified Datatypes
import qualified Logic

__ :: any
__ = Prelude.error "Logical or arity value used"

type Coq_rel w = (,) w w

app_eq_unitT :: (([]) a1) -> (([]) a1) -> a1 -> Prelude.Either () ()
app_eq_unitT x y a =
  case x of {
   ([]) -> Prelude.Left __;
   (:) a0 x0 ->
    Logic.eq_rec_r a (\_ ->
      Logic.eq_rec (Datatypes.app x0 y)
        (Logic.eq_rec_r a (\_ ->
          Logic.eq_rec_r ([]) (\_ ->
            Logic.eq_rec_r ([]) (\_ -> Prelude.Right __) y __) x0 __) a0 __)
        ([])) a0 __}

unit_eq_appT :: (([]) a1) -> (([]) a1) -> a1 -> Prelude.Either () ()
unit_eq_appT =
  app_eq_unitT

