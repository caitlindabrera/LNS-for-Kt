{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

import Prelude
import Datatypes
import LNS
import LNSKt_calculus
import List
import Logic
import Cut
import DdT
import Gen_seq
import Gen_tacs
import Merge
import Rules_prop
import Rules_b1l
import Rules_b1r
import Rules_b2l
import Rules_b2r
import Rules_EW
import Structural_equivalence
import Cut_extraction_example


{- PRINTING -}

instance ((Show pr)) => Show (Coq_seqrule w pr) where
  show (Sctxt l1 r l2 l3 l4 l5 pr) = show pr
      
instance Show (Coq_dir) where
  show (Coq_fwd) = "fwd"
  show (Coq_bac) = "bac"

instance (Show v) => Show (PropF v) where
  show (Var p) = "p " ++ show p
  show (Bot) = "Bot"
  show (Imp a b) = show a ++ " --> " ++ show b
  show (WBox a) = "[.] " ++ show a
  show (BBox a) = "[*] " ++ show a

instance Show (Coq_rs_prop v) where
  show (Id p) = "Id"
  show (ImpR a b) = "ImpR"
  show (ImpL a b) = "ImpL"
  show (BotL) = "BotL"

instance (Show sr) => Show (Coq_nslcrule w sr) where
  show (NSlcctxt l1 w l2 dir sr) = show sr

instance (Show sr) => Show (Coq_nslclrule w sr) where
  show (NSlclctxt l1 l2 l3 sr) = show sr

instance Show (Coq_b2rrules v) where
  show (WBox2Rs _ _ _ _) = "WBox2Rs"
  show (BBox2Rs _ _ _ _) = "BBox2Rs"

instance Show (Coq_b1rrules v) where
  show (WBox1Rs _ _ _ _ _ _ _ _) = "WBox1Rs"
  show (BBox1Rs _ _ _ _ _ _ _ _) = "BBox1Rs"

instance Show (Coq_b1lrules v) where
  show (WBox1Ls _ _ _ _ _ _ _ _) = "WBox1Ls"
  show (BBox1Ls _ _ _ _ _ _ _ _) = "BBox1Ls"

instance Show (Coq_b2lrules v) where
  show (WBox2Ls _ _ _ _ _ _ _ _) = "WBox2Ls"
  show (BBox2Ls _ _ _ _ _ _ _ _) = "BBox2Ls"

instance Show (EW_rule v) where
  show (EW _ _ _) = "EW"

instance (Show v) => Show (LNSKt_rules v) where
  show (Coq_b2r _ _ rl) = show rl
  show (Coq_b1r _ _ rl) = show rl
  show (Coq_b2l _ _ rl) = show rl
  show (Coq_b1l _ _ rl) = show rl
  show (Coq_nEW _ _ rl) = show rl
  show (Coq_prop _ _ rl) = show rl

instance Show (Cut_rule v) where
  show (Cut _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = "Cut"

instance (Show v) => Show (LNSKt_cut_rules v) where
  show (LNSKt_rules_woc _ _ rl) = show rl
  show (LNSKt_rules_wc _ _ rl) = show rl
  
instance ((Show a), (Show b), (Show c)) => Show (Coq_derrec a b c) where
  show (Coq_dpI x prems) = "dpI " ++ show prems
  show (Coq_derI l x rl ds) = "derI (" ++ show ds ++ ") (" ++ show x ++ ") (" ++ show rl ++ ")"

instance ((Show a), (Show b), (Show c)) => Show (Coq_dersrec a b c) where
  show (Coq_dlNil) = "dlNil"
  show (Coq_dlCons l x d Coq_dlNil) = show d
  show (Coq_dlCons l x d ds) = "dlCons (" ++ show d ++ ", " ++ show ds ++ ")"
