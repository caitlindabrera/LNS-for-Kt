{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

import qualified Datatypes
import qualified List
import qualified Logic
import qualified Top
import qualified LntT
import qualified Gen_seq

instance ((Prelude.Show a), (Prelude.Show b)) => Prelude.Show (Datatypes.Coq_prod a b) where
  show (Datatypes.Coq_pair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"

instance ((Prelude.Show a)) => Prelude.Show (Datatypes.Coq_list a) where
  show (Datatypes.Coq_nil) = "[]"
  show (Datatypes.Coq_cons a l) = show a ++ " :: " ++ show l

instance Prelude.Show (Gen_seq.Coq_seqrule w pr) where
  show _ = ""

instance Prelude.Show (LntT.Coq_dir) where
  show (LntT.Coq_fwd) = "fwd"
  show (LntT.Coq_bac) = "bac"

instance (Prelude.Show v) => Prelude.Show (LntT.PropF v) where
  show (LntT.Var p) = "p " ++ show p
  show (LntT.Bot) = "Bot"
  show (LntT.Imp a b) = show a ++ " --> " ++ show b
  show (LntT.WBox a) = "[.] " ++ show a
  show (LntT.BBox a) = "[*] " ++ show a

instance (Prelude.Show v) => Prelude.Show (LntT.Coq_princrule_pfc v) where
  show (LntT.Id_pfc p) = "Id " ++ show p
  show (LntT.ImpR_pfc a b) = "ImpR " ++ show a ++ " " ++ show b
  show (LntT.ImpL_pfc a b) = "ImpL " ++ show a ++ " " ++ show b
  show (LntT.BotL_pfc) = "BotL"

instance Prelude.Show (LntT.Coq_nslcrule w sr) where
  show _ = ""

instance Prelude.Show (LntT.Coq_nslclrule w sr) where
  show _ = ""

instance Prelude.Show (Top.Coq_b2rrules v) where
  show _ = ""

instance Prelude.Show (Top.Coq_b1rrules v) where
  show _ = ""

instance Prelude.Show (Top.Coq_b1lrules v) where
  show _ = ""

instance Prelude.Show (Top.Coq_b2lrules v) where
  show _ = ""

instance Prelude.Show (Top.EW_rule v) where
  show _ = ""

instance Prelude.Show (Top.LNSKt_rules v) where
  show _ = ""

{-
instance Prelude.Show () where
  show _ = ""
-}

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


instance Prelude.Show Datatypes.Coq_nat where
  show cnat = Prelude.show (toInt cnat)
   where
    toInt Datatypes.O = 0
    toInt (Datatypes.S n) = 1 Prelude.+ toInt n


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
