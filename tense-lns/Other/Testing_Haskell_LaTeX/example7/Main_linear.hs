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



main = writeFile "foo.tex" doc

doc = beginning ++ middle ++ end

beginning = "\\documentclass{article}\\title{Cut-elimination output}\\date{}\\author{}\\begin{document}\\maketitle{}"

middle = "$ " ++ (convert_der_to_string (output)) ++ " $"

end = "\\end{document}"

output = Cut_extraction_example.cut_example2


type Vars = Datatypes.Coq_nat


convert_der_to_string :: (DdT.Coq_derrec
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF Vars)))
                         LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Vars) 
                         ()) ->
                         String
convert_der_to_string d =
  case d of {
    DdT.Coq_dpI x prems -> "dpI";
    DdT.Coq_derI l x rl ds -> "derI " ++ (convert_lns_to_string x) ++ (convert_ders_to_string ds)}


convert_ders_to_string :: (DdT.Coq_dersrec
                          (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Gen_tacs.Coq_rel
                          (Datatypes.Coq_list (LntT.PropF Vars)))
                          LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules Vars) 
                          ()) ->
                          String
convert_ders_to_string ds = 
  case ds of {
    DdT.Coq_dlNil -> "dlNil";
    DdT.Coq_dlCons x l d ds -> "dlCons " ++ (convert_lns_to_string x) ++ (convert_der_to_string d) ++ " " ++ (convert_ders_to_string ds)}


convert_lns_to_string :: (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF Vars)))
                         LntT.Coq_dir)) ->
                         String
convert_lns_to_string lns =
  "[" ++
    case lns of {
      Datatypes.Coq_nil -> "";
      Datatypes.Coq_cons x Datatypes.Coq_nil -> (convert_seq_dir_to_string x);
      Datatypes.Coq_cons x (Datatypes.Coq_cons y l) -> (convert_seq_dir_to_string x) ++ " :: " ++ (convert_lns_to_string (Datatypes.Coq_cons y l))}
  ++ "]"


convert_seq_dir_to_string :: (Datatypes.Coq_prod
                         (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF Vars)))
                         LntT.Coq_dir) ->
                         String
convert_seq_dir_to_string seq =
  case seq of {
    Datatypes.Coq_pair a b -> "(" ++ (convert_seq_to_string a) ++ ", " ++ (convert_dir_to_string b) ++ ")"}


convert_dir_to_string :: LntT.Coq_dir -> String
convert_dir_to_string dir =
  case dir of {
    LntT.Coq_fwd -> "fwd";
    LntT.Coq_bac -> "bac"}


convert_seq_to_string :: (Gen_tacs.Coq_rel
                         (Datatypes.Coq_list (LntT.PropF Vars))) ->
                         String
convert_seq_to_string seq =
  case seq of {
    Datatypes.Coq_pair a b -> (convert_flist_to_string a) ++ ", " ++ (convert_flist_to_string b)}


convert_flist_to_string :: (Datatypes.Coq_list (LntT.PropF Vars)) ->
                           String
convert_flist_to_string l =
  "[" ++
  case l of {
    Datatypes.Coq_nil -> "";
    Datatypes.Coq_cons x Datatypes.Coq_nil -> convert_fml_to_string x;
    Datatypes.Coq_cons x (Datatypes.Coq_cons y l') -> convert_fml_to_string x ++ ", " ++ convert_flist_to_string (Datatypes.Coq_cons y l')}
  ++ "]"


convert_fml_to_string :: (LntT.PropF Vars) -> String
convert_fml_to_string a =
  case a of {
    LntT.Var n -> "p_{" ++ (convert_vars_to_string n) ++ "}";
    LntT.Bot -> "\\bot_L";
    LntT.Imp b c -> (convert_fml_to_string b) ++ "-->" ++ (convert_fml_to_string c);
    LntT.WBox b -> "\\wbx" ++ (convert_fml_to_string b);
    LntT.BBox b -> "\\bbx" ++ (convert_fml_to_string b)}



convert_vars_to_string :: Vars -> String
convert_vars_to_string n = convert_Int_to_string (convert_coq_nat_toInt n)


convert_coq_nat_toInt :: Datatypes.Coq_nat -> Int
convert_coq_nat_toInt coqnat =
  case coqnat of {
    Datatypes.O -> 0;
    Datatypes.S n -> 1 + convert_coq_nat_toInt n}


convert_Int_to_string :: Int -> String
convert_Int_to_string n = show n



{-

convert_nat_to_string :: 


    show cnat = show (toInt cnat)
   where
    toInt Datatypes.O = 0
    toInt (Datatypes.S n) = 1 + toInt n
  -}
      

{-
Datatypes.Coq_cons x (Datatypes.Coq_nil) -> (convert_seq_to_string_no_dir x)
      Datatypes.Coq_cons x (Datatypes.Coq_cons y l) ->
        case y of {
          Datatypes.Coq_pair a b -> convert_seq_to_string}


case lns of {
      Datatypes.Coq_nil -> ""
      Datatypes.Coq_cons x (Datatypes.Coq_nil) -> (convert_seq_to_string_no_dir x)
      Datatypes.Coq_cons x (Datatypes.Coq_cons y l) ->
        case y of {
          Datatypes.Coq_pair a b -> convert_seq_to_string

    show (Datatypes.Coq_nil) = "[]"
  show (Datatypes.Coq_cons a (Datatypes.Coq_nil)) = "[" ++ show a ++ "]"
  show (Datatypes.Coq_cons a l) = show a ++ " :: " ++ show l
-}
  
{-

  instance ((Show a), (Show b), (Show c)) => Show (DdT.Coq_derrec a b c) where
  show (DdT.Coq_dpI x prems) = "dpI " ++ show prems
  show (DdT.Coq_derI l x rl ds) = "derI (" ++ show ds ++ ") (" ++ show x ++ ") (" ++ show rl ++ ")"

instance ((Show a), (Show b), (Show c)) => Show (DdT.Coq_dersrec a b c) where
  show (DdT.Coq_dlNil) = "dlNil"
  show (DdT.Coq_dlCons l x d ds) = "dlCons (" ++ show d ++ ", " ++ show ds ++ ")"

coq_LNSKt_cut_elimination :: (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel
                             (Datatypes.Coq_list (LntT.PropF a1)))
                             LntT.Coq_dir)) -> (DdT.Coq_derrec
                             (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel
                             (Datatypes.Coq_list (LntT.PropF a1)))
                             LntT.Coq_dir)) (LNSKt_cut_rules a1) ()) ->
                             DdT.Coq_derrec
                             (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel
                             (Datatypes.Coq_list (LntT.PropF a1)))
                             LntT.Coq_dir)) (Lntkt_exchT.LNSKt_rules a1) 
                             ()
coq_LNSKt_cut_elimination ns h =





instance ((Show a), (Show b)) => Show (Datatypes.Coq_prod a b) where
  show (Datatypes.Coq_pair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"

instance ((Show a)) => Show (Datatypes.Coq_list a) where
  show (Datatypes.Coq_nil) = "[]"
  show (Datatypes.Coq_cons a (Datatypes.Coq_nil)) = "[" ++ show a ++ "]"
  show (Datatypes.Coq_cons a l) = show a ++ " :: " ++ show l

instance ((Show pr)) => Show (Gen_seq.Coq_seqrule w pr) where
  show (Gen_seq.Sctxt l1 r l2 l3 l4 l5 pr) = show pr
      
instance Show (LntT.Coq_dir) where
  show (LntT.Coq_fwd) = "fwd"
  show (LntT.Coq_bac) = "bac"

instance (Show v) => Show (LntT.PropF v) where
  show (LntT.Var p) = "p " ++ show p
  show (LntT.Bot) = "Bot"
  show (LntT.Imp a b) = show a ++ " --> " ++ show b
  show (LntT.WBox a) = "[.] " ++ show a
  show (LntT.BBox a) = "[*] " ++ show a

instance (Show v) => Show (LntT.Coq_princrule_pfc v) where
  show (LntT.Id_pfc p) = "Id " ++ show p
  show (LntT.ImpR_pfc a b) = "ImpR " ++ show a ++ " " ++ show b
  show (LntT.ImpL_pfc a b) = "ImpL " ++ show a ++ " " ++ show b
  show (LntT.BotL_pfc) = "BotL"

instance (Show sr) => Show (LntT.Coq_nslcrule w sr) where
  show (LntT.NSlcctxt l1 w l2 dir sr) = show sr

instance (Show sr) => Show (LntT.Coq_nslclrule w sr) where
  show (LntT.NSlclctxt l1 l2 l3 sr) = show sr

instance Show (LntbRT.Coq_b2rrules v) where
  show (LntbRT.WBox2Rs _ _ _ _) = "WBox2Rs"
  show (LntbRT.BBox2Rs _ _ _ _) = "BBox2Rs"

instance Show (LntbRT.Coq_b1rrules v) where
  show (LntbRT.WBox1Rs _ _ _ _ _ _ _ _) = "WBox1Rs"
  show (LntbRT.BBox1Rs _ _ _ _ _ _ _ _) = "BBox1Rs"

instance Show (Lntb1LT.Coq_b1lrules v) where
  show (Lntb1LT.WBox1Ls _ _ _ _ _ _ _ _) = "WBox1Ls"
  show (Lntb1LT.BBox1Ls _ _ _ _ _ _ _ _) = "BBox1Ls"

instance Show (Lntb2LT.Coq_b2lrules v) where
  show (Lntb2LT.WBox2Ls _ _ _ _ _ _ _ _) = "WBox2Ls"
  show (Lntb2LT.BBox2Ls _ _ _ _ _ _ _ _) = "BBox2Ls"

instance Show (Lntkt_exchT.EW_rule v) where
  show (Lntkt_exchT.EW _ _ _) = "EW"

instance (Show v) => Show (Lntkt_exchT.LNSKt_rules v) where
  show (Lntkt_exchT.Coq_b2r _ _ rl) = show rl
  show (Lntkt_exchT.Coq_b1r _ _ rl) = show rl
  show (Lntkt_exchT.Coq_b2l _ _ rl) = show rl
  show (Lntkt_exchT.Coq_b1l _ _ rl) = show rl
  show (Lntkt_exchT.Coq_nEW _ _ rl) = show rl
  show (Lntkt_exchT.Coq_prop _ _ rl) = show rl


instance ((Show a), (Show b), (Show c)) => Show (DdT.Coq_derrec a b c) where
  show (DdT.Coq_dpI x prems) = "dpI " ++ show prems
  show (DdT.Coq_derI l x rl ds) = "derI (" ++ show ds ++ ") (" ++ show x ++ ") (" ++ show rl ++ ")"

instance ((Show a), (Show b), (Show c)) => Show (DdT.Coq_dersrec a b c) where
  show (DdT.Coq_dlNil) = "dlNil"
  show (DdT.Coq_dlCons l x d ds) = "dlCons (" ++ show d ++ ", " ++ show ds ++ ")"


instance Show Datatypes.Coq_nat where
  show cnat = show (toInt cnat)
   where
    toInt Datatypes.O = 0
    toInt (Datatypes.S n) = 1 + toInt n
-}






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
--  show derrec = case derrec
--  show _ = "Working?"
{-
instance Show () where
  show _ = ""
-}

--  show _ = "Working?"

{-

instance Show (Coq_derrec (Show a => a) _ _) where
  show derrec = case derrec of
    Coq_dpI x prems -> "Coq_dpi " ++ show x ++ show prems

-}
