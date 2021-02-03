module Dd_fc where

import qualified Prelude
import qualified Logic
import qualified Specif
import qualified DdT
import qualified GenT

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_in_dersrec x rules prems =
   Coq_in_dersrec_hd (([]) x) (DdT.Coq_dersrec x rules prems)
 | Coq_in_dersrec_tl x (DdT.Coq_derrec x rules prems) (([]) x) (DdT.Coq_dersrec
                                                               x rules 
                                                               prems) 
 (Coq_in_dersrec x rules prems)

derrec_height :: a1 -> (DdT.Coq_derrec a1 a2 a3) -> Prelude.Int
derrec_height _ der =
  case der of {
   DdT.Coq_dpI _ _ -> 0;
   DdT.Coq_derI ps _ _ ds -> Prelude.succ (dersrec_height ps ds)}

dersrec_height :: (([]) a1) -> (DdT.Coq_dersrec a1 a2 a3) -> Prelude.Int
dersrec_height _ ders =
  case ders of {
   DdT.Coq_dlNil -> 0;
   DdT.Coq_dlCons seq seqs d ds ->
    Prelude.max (derrec_height seq d) (dersrec_height seqs ds)}

dersrecD_forall_in_dersrec :: (([]) a1) -> (DdT.Coq_dersrec a1 a2 a3) -> a1 ->
                              (GenT.InT a1) -> Specif.Coq_sigT
                              (DdT.Coq_derrec a1 a2 a3)
                              (Coq_in_dersrec a1 a2 a3)
dersrecD_forall_in_dersrec cs ds =
  DdT.dersrec_rect (\_ hin ->
    case hin of {
     GenT.InT_eq' _ _ -> Logic.coq_False_rect __;
     GenT.InT_cons _ _ x0 -> Logic.coq_False_rect x0})
    (\seq seqs d ds0 iHds c hin ->
    case hin of {
     GenT.InT_eq' b l ->
      Logic.eq_rect_r seq (\_ ->
        Logic.eq_rect_r seqs (\_ ->
          Logic.eq_rect_r c (\d0 _ _ -> Specif.Coq_existT d0
            (Coq_in_dersrec_hd seqs ds0)) seq d hin __) l) b __ __;
     GenT.InT_cons b l x0 ->
      Logic.eq_rect_r seq (\_ ->
        Logic.eq_rect_r seqs (\x1 ->
          let {x2 = iHds c x1} in
          case x2 of {
           Specif.Coq_existT d2 hin2 -> Specif.Coq_existT d2
            (Coq_in_dersrec_tl seq d seqs ds0 hin2)}) l) b __ x0}) cs ds

dersrec_double_verb :: a1 -> a1 -> (DdT.Coq_dersrec a1 a2 a3) ->
                       Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3)
                       (Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3)
                       ((,) (Coq_in_dersrec a1 a2 a3)
                       (Coq_in_dersrec a1 a2 a3)))
dersrec_double_verb c1 c2 d =
  let {hin1 = GenT.InT_eq' c1 ((:) c2 ([]))} in
  let {hin2 = GenT.InT_cons c1 ((:) c2 ([])) (GenT.InT_eq' c2 ([]))} in
  let {hin3 = dersrecD_forall_in_dersrec ((:) c1 ((:) c2 ([]))) d c1 hin1} in
  case hin3 of {
   Specif.Coq_existT d1 hin4 -> Specif.Coq_existT d1
    (let {hin5 = dersrecD_forall_in_dersrec ((:) c1 ((:) c2 ([]))) d c2 hin2}
     in
     case hin5 of {
      Specif.Coq_existT d2 hin6 -> Specif.Coq_existT d2 ((,) hin4 hin6)})}

dp :: a1 -> (DdT.Coq_derrec a1 a2 a3) -> Prelude.Int
dp =
  derrec_height

dersrec_derrec_height :: Prelude.Int -> a1 -> (DdT.Coq_dersrec a1 a2 a3) ->
                         Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3) ()
dersrec_derrec_height n g d2 =
  case d2 of {
   DdT.Coq_dlNil -> Logic.coq_False_rect;
   DdT.Coq_dlCons seq seqs d d3 ->
    Logic.eq_rect_r (DdT.Coq_dlCons seq seqs d d3) (\_ ->
      Logic.eq_rect
        (dersrec_height ((:) seq seqs) (DdT.Coq_dlCons seq seqs d d3))
        (Logic.eq_rect_r g (\_ d0 ->
          Logic.eq_rect_r ([]) (\_ _ -> Specif.Coq_existT d0 __) seqs __ d3)
          seq __ d) n) d2 __}

dersrec_derrec2_height :: Prelude.Int -> a1 -> a1 -> (DdT.Coq_dersrec 
                          a1 a2 a3) -> Specif.Coq_sigT
                          (DdT.Coq_derrec a1 a2 a3)
                          (Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3) ())
dersrec_derrec2_height n g1 g2 d2 =
  case d2 of {
   DdT.Coq_dlNil -> Logic.coq_False_rect;
   DdT.Coq_dlCons seq seqs d d3 ->
    case seqs of {
     ([]) -> Logic.coq_False_rect;
     (:) x seqs0 ->
      case seqs0 of {
       ([]) ->
        let {s = dersrec_derrec_height (dersrec_height ((:) x ([])) d3) x d3}
        in
        case s of {
         Specif.Coq_existT x0 _ ->
          Logic.eq_rect_r (DdT.Coq_dlCons seq ((:) x ([])) d d3) (\_ ->
            Logic.eq_rect
              (dersrec_height ((:) seq ((:) x ([]))) (DdT.Coq_dlCons seq ((:)
                x ([])) d d3))
              (Logic.eq_rect_r g1 (\_ d0 ->
                Logic.eq_rect_r g2 (\_ _ x1 _ -> Specif.Coq_existT d0
                  (Specif.Coq_existT x1 __)) x __ d3 x0 __) seq __ d) n) d2 __};
       (:) _ _ -> Logic.coq_False_rect}}}

dersrec_derrec_dp :: Prelude.Int -> a1 -> (DdT.Coq_dersrec a1 a2 a3) ->
                     Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3) ()
dersrec_derrec_dp =
  dersrec_derrec_height

dersrec_derrec2_dp :: Prelude.Int -> a1 -> a1 -> (DdT.Coq_dersrec a1 a2 
                      a3) -> Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3)
                      (Specif.Coq_sigT (DdT.Coq_derrec a1 a2 a3) ())
dersrec_derrec2_dp =
  dersrec_derrec2_height

derrec_dp_same2 :: a1 -> (DdT.Coq_derrec a1 a2 a3) -> a1 -> Specif.Coq_sigT
                   (DdT.Coq_derrec a1 a2 a3) ()
derrec_dp_same2 g d1 h =
  Logic.eq_rect_r h (\d2 -> Specif.Coq_existT d2 __) g d1

get_D :: a1 -> a1 -> (DdT.Coq_derrec a1 a2 a3) -> DdT.Coq_derrec a1 a2 a3
get_D g h d =
  case Logic.eq_rect_r h (\d2 -> Specif.Coq_existT d2 __) g d of {
   Specif.Coq_existT d' _ -> d'}

