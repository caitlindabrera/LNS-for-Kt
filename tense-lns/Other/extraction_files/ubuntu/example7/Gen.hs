module Gen where

import qualified Prelude
import qualified Logic

type Coq_rsub u v f g = u -> v -> f -> g

arg_cong_imp :: a1 -> a1 -> a2 -> a2
arg_cong_imp x y x0 =
  Logic.eq_rect_r y (\x1 -> x1) x x0

arg1_cong_imp :: a1 -> a1 -> a2 -> a3 -> a3
arg1_cong_imp x y _ x0 =
  Logic.eq_rect_r y (\x1 -> x1) x x0

