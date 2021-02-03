{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}


main = writeFile "foo.tex" doc

doc = beginning ++ middle ++ end

beginning = "\\documentclass{article}\\title{Cut-elimination output}\\date{}\\author{}\\begin{document}\\maketitle{}"

middle = output

end = "\\end{document}"










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










