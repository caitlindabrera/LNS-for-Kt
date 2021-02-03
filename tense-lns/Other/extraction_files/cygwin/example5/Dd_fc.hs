module Dd_fc where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Nat
import qualified Specif
import qualified DdT
import qualified GenT

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_in_dersrec x rules prems =
   Coq_in_dersrec_hd (Datatypes.Coq_list x) (DdT.Coq_dersrec x rules prems)
 | Coq_in_dersrec_tl x (DdT.Coq_derrec x rules prems) (Datatypes.Coq_list x) (DdT.Coq_dersrec x rules prems) (Coq_in_dersrec x rules prems)

derrec_height :: a1 -> (DdT.Coq_derrec a1 a2 a3) -> Datatypes.Coq_nat
derrec_height _ der =
  case der of {
   DdT.Coq_dpI _ _ -> Datatypes.O;
   DdT.Coq_derI ps _ _ ds -> Datatypes.S (dersrec_height ps ds)}

dersrec_height :: (Datatypes.Coq_list a1) -> (DdT.Coq_dersrec a1 a2 a3) -> Datatypes.Coq_nat
dersrec_height _ ders =
  case ders of {
   DdT.Coq_dlNil -> Datatypes.O;
   DdT.Coq_dlCons seq seqs d ds -> Nat.max (derrec_height seq d) (dersrec_height seqs ds)}

dersrecD_forall_in_dersrec :: (Datatypes.Coq_list a1) -> (DdT.Coq_dersrec a1 a2 a3) -> a1 -> (GenT.InT a1) -> Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3)
                              (Coq_in_dersrec a1 a2 a3)
dersrecD_forall_in_dersrec cs ds =
  DdT.dersrec_rect (\_ hin -> (case hin of {
                                GenT.InT_eq' _ _ -> (\_ -> Logic.coq_False_rect __);
                                GenT.InT_cons _ _ x0 -> (\_ -> Logic.coq_False_rect x0)}) __) (\seq seqs d ds0 iHds c hin ->
    (case hin of {
      GenT.InT_eq' b l -> (\_ ->
       Logic.eq_rect_r seq (\_ -> Logic.eq_rect_r seqs (\_ -> Logic.eq_rect_r c (\d0 _ _ -> Specif.Coq_existT d0 (Coq_in_dersrec_hd seqs ds0)) seq d hin __) l) b __ __);
      GenT.InT_cons b l x0 -> (\_ ->
       Logic.eq_rect_r seq (\_ ->
         Logic.eq_rect_r seqs (\x1 -> let {x2 = iHds c x1} in case x2 of {
                                                               Specif.Coq_existT d2 hin2 -> Specif.Coq_existT d2 (Coq_in_dersrec_tl seq d seqs ds0 hin2)}) l) b __ x0)}) __)
    cs ds

dersrec_double_verb :: a1 -> a1 -> (DdT.Coq_dersrec a1 a2 a3) -> Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3)
                       (Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3) (Datatypes.Coq_prod (Coq_in_dersrec a1 a2 a3) (Coq_in_dersrec a1 a2 a3)))
dersrec_double_verb c1 c2 d =
  let {hin1 = GenT.InT_eq' c1 (Datatypes.Coq_cons c2 Datatypes.Coq_nil)} in
  let {hin2 = GenT.InT_cons c1 (Datatypes.Coq_cons c2 Datatypes.Coq_nil) (GenT.InT_eq' c2 Datatypes.Coq_nil)} in
  let {hin3 = dersrecD_forall_in_dersrec (Datatypes.Coq_cons c1 (Datatypes.Coq_cons c2 Datatypes.Coq_nil)) d c1 hin1} in
  case hin3 of {
   Specif.Coq_existT d1 hin4 -> Specif.Coq_existT d1
    (let {hin5 = dersrecD_forall_in_dersrec (Datatypes.Coq_cons c1 (Datatypes.Coq_cons c2 Datatypes.Coq_nil)) d c2 hin2} in
     case hin5 of {
      Specif.Coq_existT d2 hin6 -> Specif.Coq_existT d2 (Datatypes.Coq_pair hin4 hin6)})}

dp :: a1 -> (DdT.Coq_derrec a1 a2 a3) -> Datatypes.Coq_nat
dp =
  derrec_height

dersrec_derrec_height :: Datatypes.Coq_nat -> a1 -> (DdT.Coq_dersrec a1 a2 a3) -> Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3) ()
dersrec_derrec_height n g d2 =
  (case d2 of {
    DdT.Coq_dlNil -> (\_ _ _ _ -> Logic.coq_False_rect);
    DdT.Coq_dlCons seq seqs d d3 -> (\_ d2' _ _ ->
     Logic.eq_rect_r (DdT.Coq_dlCons seq seqs d d3) (\_ ->
       Logic.eq_rect (dersrec_height (Datatypes.Coq_cons seq seqs) (DdT.Coq_dlCons seq seqs d d3))
         (Logic.eq_rect_r g (\_ d0 -> Logic.eq_rect_r Datatypes.Coq_nil (\_ _ -> Specif.Coq_existT d0 __) seqs __ d3) seq __ d) n) d2' __)}) __ d2 __ __

dersrec_derrec2_height :: Datatypes.Coq_nat -> a1 -> a1 -> (DdT.Coq_dersrec a1 a2 a3) -> Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3)
                          (Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3) ())
dersrec_derrec2_height n g1 g2 d2 =
  (case d2 of {
    DdT.Coq_dlNil -> (\_ _ _ _ -> Logic.coq_False_rect);
    DdT.Coq_dlCons seq seqs d d3 -> (\_ d2' _ _ ->
     (case seqs of {
       Datatypes.Coq_nil -> (\_ _ _ _ _ -> Logic.coq_False_rect);
       Datatypes.Coq_cons x seqs0 -> (\_ d4 d2'0 _ _ ->
        (case seqs0 of {
          Datatypes.Coq_nil -> (\_ d5 d2'1 _ _ ->
           let {s = dersrec_derrec_height (dersrec_height (Datatypes.Coq_cons x Datatypes.Coq_nil) d5) x d5} in
           case s of {
            Specif.Coq_existT x0 _ ->
             Logic.eq_rect_r (DdT.Coq_dlCons seq (Datatypes.Coq_cons x Datatypes.Coq_nil) d d5) (\_ ->
               Logic.eq_rect
                 (dersrec_height (Datatypes.Coq_cons seq (Datatypes.Coq_cons x Datatypes.Coq_nil)) (DdT.Coq_dlCons seq (Datatypes.Coq_cons x Datatypes.Coq_nil) d d5))
                 (Logic.eq_rect_r g1 (\_ d0 -> Logic.eq_rect_r g2 (\_ _ x1 _ -> Specif.Coq_existT d0 (Specif.Coq_existT x1 __)) x __ d5 x0 __) seq __ d) n) d2'1 __});
          Datatypes.Coq_cons _ _ -> (\_ _ _ _ _ -> Logic.coq_False_rect)}) __ d4 d2'0 __ __)}) __ d3 d2' __ __)}) __ d2 __ __

dersrec_derrec_dp :: Datatypes.Coq_nat -> a1 -> (DdT.Coq_dersrec a1 a2 a3) -> Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3) ()
dersrec_derrec_dp =
  dersrec_derrec_height

dersrec_derrec2_dp :: Datatypes.Coq_nat -> a1 -> a1 -> (DdT.Coq_dersrec a1 a2 a3) -> Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3) (Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3) ())
dersrec_derrec2_dp =
  dersrec_derrec2_height

derrec_dp_same2 :: a1 -> (DdT.Coq_derrec a1 a2 a3) -> a1 -> Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3) ()
derrec_dp_same2 g d1 h =
  Logic.eq_rect_r h (\d2 -> Specif.Coq_existT d2 __) g d1

get_D :: a1 -> a1 -> (DdT.Coq_derrec a1 a2 a3) -> DdT.Coq_derrec a1 a2 a3
get_D g h d =
  case Logic.eq_rect_r h (\d2 -> Specif.Coq_existT d2 __) g d of {
   Specif.Coq_existT d' _ -> d'}

