
{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

import qualified Datatypes
import qualified List
import qualified Logic
import qualified Top

{- coq naturals to haskell Ints -}
c2hn :: Datatypes.Coq_nat -> Int
c2hn Datatypes.O = 0
c2hn (Datatypes.S n) = (c2hn n) + 1

{- Haskell Ints to Coq naturals -}
h2cn :: Int -> Datatypes.Coq_nat
h2cn 0 = Datatypes.O
h2cn n = Datatypes.S (h2cn (n-1))