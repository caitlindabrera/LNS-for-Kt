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

import qualified Prelude
import qualified Datatypes
import qualified Lemma_Sixteen
import qualified List
import qualified Logic
import qualified Nat
import qualified Specif
import qualified DdT
import qualified Dd_fc
import qualified Gen_tacs
import qualified Ind_lex
import qualified LntT
import qualified Lnt_contraction_mrT
import qualified Lntkt_exchT
import qualified Merge
import qualified Size
import qualified Structural_equivalence
import qualified Gen_seq
import qualified Cut
import qualified LntbRT
import qualified Lntb1LT
import qualified Lntb2LT
import qualified Cut_extraction_example
{-
import qualified Extr_example1
-}


{- PRINTING -}

instance ((Prelude.Show a), (Prelude.Show b)) => Prelude.Show (Datatypes.Coq_prod a b) where
  show (Datatypes.Coq_pair a b) = "(" Prelude.++ Prelude.show a Prelude.++ ", " Prelude.++ Prelude.show b Prelude.++ ")"

instance ((Prelude.Show a)) => Prelude.Show (Datatypes.Coq_list a) where
  show (Datatypes.Coq_nil) = "[]"
  show (Datatypes.Coq_cons a (Datatypes.Coq_nil)) = "[" Prelude.++ Prelude.show a Prelude.++ "]"
  show (Datatypes.Coq_cons a l) = Prelude.show a Prelude.++ " :: " Prelude.++ Prelude.show l

instance ((Prelude.Show pr)) => Prelude.Show (Gen_seq.Coq_seqrule w pr) where
  show (Gen_seq.Sctxt l1 r l2 l3 l4 l5 pr) = Prelude.show pr
      
instance Prelude.Show (LntT.Coq_dir) where
  show (LntT.Coq_fwd) = "fwd"
  show (LntT.Coq_bac) = "bac"

instance (Prelude.Show v) => Prelude.Show (LntT.PropF v) where
  show (LntT.Var p) = "p " Prelude.++ Prelude.show p
  show (LntT.Bot) = "Bot"
  show (LntT.Imp a b) = Prelude.show a Prelude.++ " --> " Prelude.++ Prelude.show b
  show (LntT.WBox a) = "[.] " Prelude.++ Prelude.show a
  show (LntT.BBox a) = "[*] " Prelude.++ Prelude.show a

instance (Prelude.Show v) => Prelude.Show (LntT.Coq_princrule_pfc v) where
  show (LntT.Id_pfc p) = "Id " Prelude.++ Prelude.show p
  show (LntT.ImpR_pfc a b) = "ImpR " Prelude.++ Prelude.show a Prelude.++ " " Prelude.++ Prelude.show b
  show (LntT.ImpL_pfc a b) = "ImpL " Prelude.++ Prelude.show a Prelude.++ " " Prelude.++ Prelude.show b
  show (LntT.BotL_pfc) = "BotL"

instance (Prelude.Show sr) => Prelude.Show (LntT.Coq_nslcrule w sr) where
  show (LntT.NSlcctxt l1 w l2 dir sr) = Prelude.show sr

instance (Prelude.Show sr) => Prelude.Show (LntT.Coq_nslclrule w sr) where
  show (LntT.NSlclctxt l1 l2 l3 sr) = Prelude.show sr

instance Prelude.Show (LntbRT.Coq_b2rrules v) where
  show (LntbRT.WBox2Rs _ _ _ _) = "WBox2Rs"
  show (LntbRT.BBox2Rs _ _ _ _) = "BBox2Rs"

instance Prelude.Show (LntbRT.Coq_b1rrules v) where
  show (LntbRT.WBox1Rs _ _ _ _ _ _ _ _) = "WBox1Rs"
  show (LntbRT.BBox1Rs _ _ _ _ _ _ _ _) = "BBox1Rs"

instance Prelude.Show (Lntb1LT.Coq_b1lrules v) where
  show (Lntb1LT.WBox1Ls _ _ _ _ _ _ _ _) = "WBox1Ls"
  show (Lntb1LT.BBox1Ls _ _ _ _ _ _ _ _) = "BBox1Ls"

instance Prelude.Show (Lntb2LT.Coq_b2lrules v) where
  show (Lntb2LT.WBox2Ls _ _ _ _ _ _ _ _) = "WBox2Ls"
  show (Lntb2LT.BBox2Ls _ _ _ _ _ _ _ _) = "BBox2Ls"

instance Prelude.Show (Lntkt_exchT.EW_rule v) where
  show (Lntkt_exchT.EW _ _ _) = "EW"

instance (Prelude.Show v) => Prelude.Show (Lntkt_exchT.LNSKt_rules v) where
  show (Lntkt_exchT.Coq_b2r _ _ rl) = Prelude.show rl
  show (Lntkt_exchT.Coq_b1r _ _ rl) = Prelude.show rl
  show (Lntkt_exchT.Coq_b2l _ _ rl) = Prelude.show rl
  show (Lntkt_exchT.Coq_b1l _ _ rl) = Prelude.show rl
  show (Lntkt_exchT.Coq_nEW _ _ rl) = Prelude.show rl
  show (Lntkt_exchT.Coq_prop _ _ rl) = Prelude.show rl


instance ((Prelude.Show a), (Prelude.Show b), (Prelude.Show c)) => Prelude.Show (DdT.Coq_derrec a b c) where
  show (DdT.Coq_dpI x prems) = "dpI " Prelude.++ Prelude.show prems
  show (DdT.Coq_derI l x rl ds) = "derI (" Prelude.++ Prelude.show ds Prelude.++ ") (" Prelude.++ Prelude.show x Prelude.++ ") (" Prelude.++ Prelude.show rl Prelude.++ ")"

instance ((Prelude.Show a), (Prelude.Show b), (Prelude.Show c)) => Prelude.Show (DdT.Coq_dersrec a b c) where
  show (DdT.Coq_dlNil) = "dlNil"
  show (DdT.Coq_dlCons l x d ds) = "dlCons (" Prelude.++ Prelude.show d Prelude.++ ", " Prelude.++ Prelude.show ds Prelude.++ ")"


instance Prelude.Show Datatypes.Coq_nat where
  show cnat = Prelude.show (toInt cnat)
   where
    toInt Datatypes.O = 0
    toInt (Datatypes.S n) = 1 Prelude.+ toInt n


{-
{- EXAMPLES -}

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
        (Gen_seq.coq_Sctxt_nil (Datatypes.Coq_pair (Datatypes.Coq_cons
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
