{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

import qualified Datatypes
import qualified List
import qualified Logic
import qualified Top

instance ((Prelude.Show a), (Prelude.Show b), (Prelude.Show c)) => Prelude.Show (Top.Coq_derrec a b c) where
  show (Top.Coq_dpI x prems) = "dpI " ++ show prems
  show (Top.Coq_derI l x rl ds) = "derI (" ++ show ds ++ ") (" ++ show x ++ ")"

{-
                                  Coq_dpI x prems -> "Working?"
    | Coq_derI l x rl ds -> "Working?"
     Coq_dpI x prems
-}
--  show derrec = case derrec
--  show _ = "Working?"

instance ((Prelude.Show a), (Prelude.Show b), (Prelude.Show c)) => Prelude.Show (Top.Coq_dersrec a b c) where
  show (Top.Coq_dlNil) = "dlNil"
  show (Top.Coq_dlCons l x d ds) = "dlCons (" ++ show ds ++ ")"

--  show _ = "Working?"

{- coq naturals to haskell Ints -}
c2hn :: Datatypes.Coq_nat -> Int
c2hn Datatypes.O = 0
c2hn (Datatypes.S n) = (c2hn n) + 1

{- Haskell Ints to Coq naturals -}
h2cn :: Int -> Datatypes.Coq_nat
h2cn 0 = Datatypes.O
h2cn n = Datatypes.S (h2cn (n-1))

{-

instance Show (Coq_derrec (Show a => a) _ _) where
  show derrec = case derrec of
    Coq_dpI x prems -> "Coq_dpi " ++ show x ++ show prems

-}
