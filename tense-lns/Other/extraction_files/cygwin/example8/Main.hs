{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
{-
import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Logic
import qualified Cut
import qualified DdT
import qualified Gen_seq
import qualified Gen_tacs
import qualified LntT
import qualified Lntkt_exchT
import qualified Cut
-}

import Prelude
import Datatypes
import Lemma_Sixteen
import List
import Logic
import Nat
import Specif
import DdT
import Dd_fc
import Gen_tacs
import Ind_lex
import LntT
import Lnt_contraction_mrT
import Lntkt_exchT
import Merge
import Size
import Structural_equivalence
import Gen_seq
import Cut
import LntbRT
import Lntb1LT
import Lntb2LT
import Cut_extraction_example
{-
import qualified Extr_example1
-}


{- PRINTING -}

instance ((Show a), (Show b)) => Show (Coq_prod a b) where
  show (Coq_pair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"

instance ((Show a)) => Show (Coq_list a) where
  show ls = "[" ++ (listToString ls) ++ "]"
   where
    listToString Coq_nil = ""
    listToString (Coq_cons a Coq_nil) = show a
    listToString (Coq_cons a l) = show a ++ " :: " ++ listToString l

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

instance (Show v) => Show (Coq_princrule_pfc v) where
  show (Id_pfc p) = "Id (p " ++ show p ++ ")"
  show (ImpR_pfc a b) = "ImpR (" ++ show a ++ ") (" ++ show b ++ ")"
  show (ImpL_pfc a b) = "ImpL (" ++ show a ++ ") (" ++ show b ++ ")"
  show (BotL_pfc) = "BotL"

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


instance ((Show a), (Show b), (Show c)) => Show (Coq_derrec a b c) where
  show (Coq_dpI x prems) = "dpI " ++ show prems
  show (Coq_derI l x rl ds) = "derI (" ++ show ds ++ ") (" ++ show x ++ ") (" ++ show rl ++ ")"

instance ((Show a), (Show b), (Show c)) => Show (Coq_dersrec a b c) where
  show (Coq_dlNil) = "dlNil"
  show (Coq_dlCons l x d ds) = "dlCons (" ++ show d ++ ", " ++ show ds ++ ")"


instance Show Coq_nat where
  show cnat = show (toInt cnat)
   where
    toInt O = 0
    toInt (S n) = 1 + toInt n



{- EXAMPLES -}
{-
nslcrule_gen :: (Datatypes.Coq_list a1) -> a1 -> (Datatypes.Coq_list
                (Datatypes.Coq_prod a1 LntT.Coq_dir)) -> LntT.Coq_dir ->
                (Datatypes.Coq_list
                (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir))) ->
                (Datatypes.Coq_list (Datatypes.Coq_prod a1 LntT.Coq_dir)) ->
                a2 -> LntT.Coq_nslcrule a1 a2
nslcrule_gen ps c g d pS c0 x =
  Logic.eq_rect_r (List.map (LntT.nslcext g d) ps)
    (Logic.eq_rect_r (LntT.nslcext g d c) (LntT.NSlcctxt ps c g d x) c0) pS

pf_wc :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf_wc =
  Cut.LNSKt_rules_woc Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)
    (Lntkt_exchT.Coq_prop Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
    Datatypes.O) Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)
    (nslcrule_gen Datatypes.Coq_nil (Datatypes.Coq_pair (Datatypes.Coq_cons
      (LntT.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
      Datatypes.O) Datatypes.Coq_nil)) Datatypes.Coq_nil LntT.Coq_fwd
      Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair
      (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O)
      Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
      Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)
      (Logic.eq_rect
        (Gen_seq.seqext Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil
          Datatypes.Coq_nil (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
          Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
          Datatypes.O) Datatypes.Coq_nil)))
        (Gen_seq.Sctxt Datatypes.Coq_nil (Datatypes.Coq_pair (Datatypes.Coq_cons
          (LntT.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons
          (LntT.Var Datatypes.O) Datatypes.Coq_nil)) Datatypes.Coq_nil
          Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil (LntT.Id_pfc
          Datatypes.O)) (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var
        Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var
        Datatypes.O) Datatypes.Coq_nil)))))

seq :: Datatypes.Coq_list
       (Datatypes.Coq_prod
       (Datatypes.Coq_prod
       (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))
       (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir)
seq =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
    (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil))
    LntT.Coq_fwd) Datatypes.Coq_nil

example2 :: DdT.Coq_derrec
            (Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Gen_tacs.Coq_rel
            (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
            LntT.Coq_dir)) (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
example2 =
  DdT.Coq_derI Datatypes.Coq_nil seq pf_wc DdT.Coq_dlNil

cut_example2 :: DdT.Coq_derrec
                (Datatypes.Coq_list
                (Datatypes.Coq_prod
                (Gen_tacs.Coq_rel
                (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)))
                LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Datatypes.Coq_nat) 
                ()
cut_example2 =
  Cut.coq_LNSKt_cut_elimination seq example2


{- 3rd EXAMPLE -}

seqrule_id :: (Datatypes.Coq_list (Gen_tacs.Coq_rel (Datatypes.Coq_list a1))) -> (Gen_tacs.Coq_rel (Datatypes.Coq_list a1)) -> a2 -> Gen_seq.Coq_seqrule a1 a2
seqrule_id ps c x =
  (case c of {
    Datatypes.Coq_pair ca cs -> (\x0 -> Gen_seq.coq_Sctxt_eq ps ps ca cs ca cs Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil x0)}) x
  
concl3b :: Datatypes.Coq_list (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)) (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir)
concl3b =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.app (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil))) LntT.Coq_fwd) Datatypes.Coq_nil

pf3b_wc :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf3b_wc =
  Cut.LNSKt_rules_woc Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.app (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil))) LntT.Coq_fwd) Datatypes.Coq_nil) (Lntkt_exchT.Coq_prop Datatypes.Coq_nil (Datatypes.Coq_cons
    (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
    (Datatypes.app (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil))) LntT.Coq_fwd) Datatypes.Coq_nil)
    (nslcrule_gen (List.map (Gen_seq.seqext Datatypes.Coq_nil Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) Datatypes.Coq_nil) Datatypes.Coq_nil) Datatypes.Coq_nil) (Datatypes.Coq_pair
      (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.app (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil))) Datatypes.Coq_nil
      LntT.Coq_fwd Datatypes.Coq_nil (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)
      (Datatypes.app (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil))) LntT.Coq_fwd) Datatypes.Coq_nil) (Gen_seq.Sctxt Datatypes.Coq_nil
      (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil)) Datatypes.Coq_nil Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O))
      Datatypes.Coq_nil) Datatypes.Coq_nil (LntT.Id_pfc Datatypes.O))))


concl3' :: Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir)
concl3' =
  Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil

ps3 :: Datatypes.Coq_list (Datatypes.Coq_list (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat)) (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir))
ps3 =
  Datatypes.Coq_cons concl3b Datatypes.Coq_nil

ds_nil :: DdT.Coq_dersrec (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir)) (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
ds_nil =
  DdT.Coq_dlNil

example3b :: DdT.Coq_derrec (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir)) (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
example3b =
  DdT.Coq_derI Datatypes.Coq_nil concl3b pf3b_wc ds_nil

pf3a_wc :: Cut.LNSKt_cut_rules Datatypes.Coq_nat
pf3a_wc =
  Cut.LNSKt_rules_woc (Datatypes.Coq_cons concl3b Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O))
    Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil) (Lntkt_exchT.Coq_prop (Datatypes.Coq_cons concl3b Datatypes.Coq_nil) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var
    Datatypes.O)) Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)
    (nslcrule_gen (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
      Datatypes.Coq_nil))) Datatypes.Coq_nil) (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) Datatypes.Coq_nil)) Datatypes.Coq_nil LntT.Coq_fwd (Datatypes.Coq_cons concl3b Datatypes.Coq_nil)
      (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) Datatypes.Coq_nil)) LntT.Coq_fwd) Datatypes.Coq_nil)
      (seqrule_id (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_cons (LntT.Var Datatypes.O) Datatypes.Coq_nil) (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) (Datatypes.Coq_cons (LntT.Var Datatypes.O)
        Datatypes.Coq_nil))) Datatypes.Coq_nil) (Datatypes.Coq_pair Datatypes.Coq_nil (Datatypes.Coq_cons (LntT.Imp (LntT.Var Datatypes.O) (LntT.Var Datatypes.O)) Datatypes.Coq_nil)) (LntT.ImpR_pfc (LntT.Var Datatypes.O) (LntT.Var
        Datatypes.O)))))

example3 :: DdT.Coq_derrec (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir)) (Cut.LNSKt_cut_rules Datatypes.Coq_nat) ()
example3 =
  DdT.Coq_derI ps3 concl3' pf3a_wc (DdT.Coq_dlCons concl3b Datatypes.Coq_nil example3b ds_nil)

cut_example3 :: DdT.Coq_derrec (Datatypes.Coq_list (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF Datatypes.Coq_nat))) LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Datatypes.Coq_nat) ()
cut_example3 =
  Cut.coq_LNSKt_cut_elimination concl3' example3
    -}




{- coq naturals to haskell Ints
c2hn :: Datatypes.Coq_nat -> Int
c2hn Datatypes.O = 0
c2hn (Datatypes.S n) = (c2hn n) + 1
-}

{- Haskell Ints to Coq naturals
h2cn :: Int -> Datatypes.Coq_nat
h2cn 0 = Datatypes.O
h2cn n = Datatypes.S (h2cn (n-1))
-}


{-
                                  Coq_dpI x prems -> "Working?"
    | Coq_derI l x rl ds -> "Working?"
     Coq_dpI x prems
-}
--  Prelude.show derrec = case derrec
--  Prelude.show _ = "Working?"
{-
instance Prelude.Show () where
  Prelude.show _ = ""
-}

--  Prelude.show _ = "Working?"

{-

instance Show (Coq_derrec (Show a => a) _ _) where
  Prelude.show derrec = case derrec of
    Coq_dpI x prems -> "Coq_dpi " ++ show x ++ show prems

-}
