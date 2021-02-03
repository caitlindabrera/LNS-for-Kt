module List_lemmasT where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Specif
import qualified GenT

__ :: any
__ = Prelude.error "Logical or arity value used"

partition_2_2T :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                  (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> a1 ->
                  a1 -> Datatypes.Coq_sum
                  (Specif.Coq_sigT (Datatypes.Coq_list a1) ())
                  (Datatypes.Coq_sum () (Datatypes.Coq_list a1))
partition_2_2T l1 l2 l3 l4 a b =
  Datatypes.list_rect (\l5 l6 l7 b0 c _ ->
    (case l6 of {
      Datatypes.Coq_nil -> (\_ -> Datatypes.Coq_inr (Datatypes.Coq_inl __));
      Datatypes.Coq_cons a0 l8 -> (\_ ->
       Logic.eq_rect_r a0 (\_ ->
         Logic.eq_rect_r (Datatypes.app l8 (Datatypes.Coq_cons c l7))
           (Logic.eq_rect_r a0 (\_ ->
             Logic.eq_rect_r (Datatypes.app l8 (Datatypes.Coq_cons c l7))
               (\_ -> Datatypes.Coq_inr (Datatypes.Coq_inr l8)) l5 __) b0 __)
           l5) b0 __)}) __) (\a0 l5 iHl1 l6 l7 l8 b0 c _ ->
    (case l7 of {
      Datatypes.Coq_nil -> (\_ ->
       Logic.eq_rect_r c (\_ ->
         Logic.eq_rect (Datatypes.app l5 (Datatypes.Coq_cons b0 l6))
           (Logic.eq_rect_r c (\_ ->
             Logic.eq_rect (Datatypes.app l5 (Datatypes.Coq_cons b0 l6))
               (\_ -> Datatypes.Coq_inl (Specif.Coq_existT l5 __)) l8 __) a0
             __) l8) a0 __);
      Datatypes.Coq_cons a1 l9 -> (\_ ->
       Logic.eq_rect_r a1 (\_ ->
         Logic.eq_rect (Datatypes.app l5 (Datatypes.Coq_cons b0 l6))
           (Logic.eq_rect_r a1 (\_ ->
             let {h3 = iHl1 l6 l9 l8 b0 c __} in
             case h3 of {
              Datatypes.Coq_inl s ->
               case s of {
                Specif.Coq_existT l10 _ ->
                 Logic.eq_rect_r (Datatypes.app l9 (Datatypes.Coq_cons c l10))
                   (\_ _ ->
                   Logic.eq_rect_r
                     (Datatypes.app l10 (Datatypes.Coq_cons b0 l6)) (\_ ->
                     Datatypes.Coq_inl (Specif.Coq_existT l10 __)) l8 __) l5
                   iHl1 __};
              Datatypes.Coq_inr s ->
               case s of {
                Datatypes.Coq_inl _ ->
                 Logic.eq_rect_r l5 (\_ ->
                   Logic.eq_rect_r c (\_ ->
                     Logic.eq_rect_r l8 (\_ -> Datatypes.Coq_inr
                       (Datatypes.Coq_inl __)) l6 __) b0 __) l9 __;
                Datatypes.Coq_inr s0 ->
                 Logic.eq_rect_r (Datatypes.app l5 (Datatypes.Coq_cons b0 s0))
                   (\_ ->
                   Logic.eq_rect_r
                     (Datatypes.app s0 (Datatypes.Coq_cons c l8)) (\_ ->
                     Datatypes.Coq_inr (Datatypes.Coq_inr s0)) l6 __) l9 __}})
             a0 __) (Datatypes.app l9 (Datatypes.Coq_cons c l8))) a0 __)}) __)
    l1 l2 l3 l4 a b __

cons_eq_appT2 :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                 (Datatypes.Coq_list a1) -> a1 -> Datatypes.Coq_sum ()
                 (Specif.Coq_sigT (Datatypes.Coq_list a1) ())
cons_eq_appT2 x y z a =
  (case y of {
    Datatypes.Coq_nil -> (\_ ->
     Logic.eq_rect (Datatypes.Coq_cons a x) (Datatypes.Coq_inl __) z);
    Datatypes.Coq_cons a0 y0 -> (\_ -> Datatypes.Coq_inr
     (Logic.eq_rect_r (Datatypes.app y0 z) (\_ ->
       Logic.eq_rect_r a0 (\_ -> Specif.Coq_existT y0 __) a __) x __))}) __

app_eq_consT2 :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                 (Datatypes.Coq_list a1) -> a1 -> Datatypes.Coq_sum ()
                 (Specif.Coq_sigT (Datatypes.Coq_list a1) ())
app_eq_consT2 =
  cons_eq_appT2

app_eq_appT2 :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                Specif.Coq_sigT (Datatypes.Coq_list a1)
                (Datatypes.Coq_sum () ())
app_eq_appT2 w x y z =
  Datatypes.list_rect (\x0 y0 z0 _ ->
    Logic.eq_rect_r (Datatypes.app y0 z0) (Specif.Coq_existT y0
      (Datatypes.Coq_inr __)) x0) (\a w0 iHw x0 y0 z0 _ ->
    let {h = cons_eq_appT2 (Datatypes.app w0 x0) y0 z0 a} in
    case h of {
     Datatypes.Coq_inl _ ->
      Logic.eq_rect_r Datatypes.Coq_nil
        (Logic.eq_rect_r (Datatypes.Coq_cons a (Datatypes.app w0 x0))
          (Specif.Coq_existT (Datatypes.Coq_cons a w0) (Datatypes.Coq_inl __))
          z0) y0;
     Datatypes.Coq_inr s ->
      case s of {
       Specif.Coq_existT l _ ->
        Logic.eq_rect_r (Datatypes.Coq_cons a l)
          (let {h3 = iHw x0 l z0 __} in
           case h3 of {
            Specif.Coq_existT l2 s0 ->
             case s0 of {
              Datatypes.Coq_inl _ ->
               Logic.eq_rect_r (Datatypes.app l l2) (\_ ->
                 Logic.eq_rect_r (Datatypes.app l2 x0) (Specif.Coq_existT l2
                   (Datatypes.Coq_inl __)) z0) w0 iHw;
              Datatypes.Coq_inr _ ->
               Logic.eq_rect_r (Datatypes.app w0 l2)
                 (Logic.eq_rect_r (Datatypes.app l2 z0) (Specif.Coq_existT l2
                   (Datatypes.Coq_inr __)) x0) l}}) y0}}) w x y z __

app_eq_unitT2 :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> a1 ->
                 Datatypes.Coq_sum () ()
app_eq_unitT2 x y a =
  (case x of {
    Datatypes.Coq_nil -> (\_ -> Datatypes.Coq_inl __);
    Datatypes.Coq_cons a0 x0 -> (\_ ->
     Logic.eq_rec_r a (\_ ->
       Logic.eq_rec (Datatypes.app x0 y)
         (Logic.eq_rec_r a (\_ -> Datatypes.Coq_inr __) a0 __)
         Datatypes.Coq_nil) a0 __)}) __

unit_eq_appT2 :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> a1 ->
                 Datatypes.Coq_sum () ()
unit_eq_appT2 =
  app_eq_unitT2

partition_singleton_app :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list 
                           a1) -> (Datatypes.Coq_list a1) -> a1 -> a1 ->
                           Datatypes.Coq_sum ()
                           (Specif.Coq_sigT (Datatypes.Coq_list a1) ())
partition_singleton_app l1 l2 l3 a b =
  Datatypes.list_rect (\l4 l5 a0 b0 _ ->
    (case l4 of {
      Datatypes.Coq_nil -> (\_ ->
       Logic.eq_rect_r b0 (\_ ->
         Logic.eq_rect Datatypes.Coq_nil (Datatypes.Coq_inl __) l5) a0 __);
      Datatypes.Coq_cons _ l6 -> (\_ ->
       (case l6 of {
         Datatypes.Coq_nil -> (\_ -> Logic.coq_False_rect);
         Datatypes.Coq_cons _ _ -> (\_ -> Logic.coq_False_rect)}) __)}) __)
    (\a0 l4 iHL1 l5 l6 a1 b0 _ ->
    (case l5 of {
      Datatypes.Coq_nil -> (\_ ->
       Logic.eq_rect_r b0 (\_ ->
         Logic.eq_rect
           (Datatypes.app l4 (Datatypes.Coq_cons a1 Datatypes.Coq_nil))
           (Logic.eq_rect_r b0 (\_ ->
             Logic.eq_rect
               (Datatypes.app l4 (Datatypes.Coq_cons a1 Datatypes.Coq_nil))
               (\_ -> Datatypes.Coq_inr (Specif.Coq_existT l4 __)) l6 __) a0
             __) l6) a0 __);
      Datatypes.Coq_cons t l7 -> (\_ ->
       Logic.eq_rect_r t (\_ ->
         Logic.eq_rect
           (Datatypes.app l4 (Datatypes.Coq_cons a1 Datatypes.Coq_nil))
           (Logic.eq_rect_r t (\_ ->
             let {h2 = iHL1 l7 l6 a1 b0 __} in
             case h2 of {
              Datatypes.Coq_inl _ ->
               Logic.eq_rect_r Datatypes.Coq_nil (\_ ->
                 Logic.eq_rect_r l7 (\_ _ ->
                   Logic.eq_rect_r b0 (\_ -> Datatypes.Coq_inl __) a1 __) l4
                   iHL1 __) l6 __;
              Datatypes.Coq_inr h3 ->
               case h3 of {
                Specif.Coq_existT h4 _ ->
                 Logic.eq_rect_r
                   (Datatypes.app h4 (Datatypes.Coq_cons a1
                     Datatypes.Coq_nil)) (\_ ->
                   Logic.eq_rect_r
                     (Datatypes.app l7
                       (Datatypes.app (Datatypes.Coq_cons b0
                         Datatypes.Coq_nil) h4)) (\_ _ -> Datatypes.Coq_inr
                     (Specif.Coq_existT h4 __)) l4 iHL1 __) l6 __}}) a0 __)
           (Datatypes.app l7 (Datatypes.Coq_cons b0 l6))) a0 __)}) __) l1 l2
    l3 a b __

coq_InT_mid :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> a1 ->
               GenT.InT a1
coq_InT_mid l1 l2 a =
  GenT.coq_InT_appR a l1
    (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil) l2)
    (GenT.coq_InT_appL a (Datatypes.Coq_cons a Datatypes.Coq_nil) l2
      (GenT.InT_eq' a Datatypes.Coq_nil))

coq_InT_singleton_mid :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list 
                         a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list
                         a1) -> a1 -> a1 -> Datatypes.Coq_sum (GenT.InT a1)
                         (GenT.InT a1)
coq_InT_singleton_mid l1 l2 l3 l4 a b =
  let {hin = coq_InT_mid l1 l2 a} in
  let {
   hin0 = Logic.eq_rect
            (Datatypes.app l1
              (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil) l2)) hin
            (Datatypes.app l3
              (Datatypes.app (Datatypes.Coq_cons b Datatypes.Coq_nil) l4))}
  in
  let {
   hin1 = GenT.coq_InT_appE a l3
            (Datatypes.app (Datatypes.Coq_cons b Datatypes.Coq_nil) l4) hin0}
  in
  case hin1 of {
   Datatypes.Coq_inl i -> Datatypes.Coq_inl i;
   Datatypes.Coq_inr i ->
    (case i of {
      GenT.InT_eq' b0 l -> (\_ ->
       Logic.eq_rect_r b (\_ ->
         Logic.eq_rect_r l4 (\_ ->
           Logic.eq_rect_r a (\_ _ _ _ -> Logic.coq_False_rect) b __ __ i __)
           l) b0 __ __);
      GenT.InT_cons b0 l x -> (\_ ->
       Logic.eq_rect_r b (\_ ->
         Logic.eq_rect_r l4 (\x0 -> Datatypes.Coq_inr x0) l) b0 __ x)}) __}

list_nil_or_tail_singleton :: (Datatypes.Coq_list a1) -> Datatypes.Coq_sum 
                              ()
                              (Specif.Coq_sigT (Datatypes.Coq_list a1)
                              (Specif.Coq_sigT a1 ()))
list_nil_or_tail_singleton l =
  Datatypes.list_rect (Datatypes.Coq_inl __) (\a l0 iHl -> Datatypes.Coq_inr
    (case iHl of {
      Datatypes.Coq_inl _ ->
       Logic.eq_rect_r Datatypes.Coq_nil (Specif.Coq_existT Datatypes.Coq_nil
         (Specif.Coq_existT a __)) l0;
      Datatypes.Coq_inr s ->
       case s of {
        Specif.Coq_existT l2' s0 ->
         case s0 of {
          Specif.Coq_existT a' _ ->
           Logic.eq_rect_r
             (Datatypes.app l2' (Datatypes.Coq_cons a' Datatypes.Coq_nil))
             (Specif.Coq_existT (Datatypes.Coq_cons a l2') (Specif.Coq_existT
             a' __)) l0}}})) l

app_eq_appT2_nn :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                   (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                   Specif.Coq_sigT (Datatypes.Coq_list a1)
                   (Datatypes.Coq_sum () ())
app_eq_appT2_nn w x y z =
  Datatypes.list_rect (\x0 y0 z0 _ ->
    Logic.eq_rect_r (Datatypes.app y0 z0) (Specif.Coq_existT y0
      (Datatypes.Coq_inr __)) x0) (\a w0 iHw x0 y0 z0 _ ->
    let {h = cons_eq_appT2 (Datatypes.app w0 x0) y0 z0 a} in
    case h of {
     Datatypes.Coq_inl _ ->
      Logic.eq_rect_r Datatypes.Coq_nil
        (Logic.eq_rect_r (Datatypes.Coq_cons a (Datatypes.app w0 x0))
          (Specif.Coq_existT (Datatypes.Coq_cons a w0) (Datatypes.Coq_inl __))
          z0) y0;
     Datatypes.Coq_inr s ->
      case s of {
       Specif.Coq_existT l _ ->
        Logic.eq_rect_r (Datatypes.Coq_cons a l)
          (let {h3 = iHw x0 l z0 __} in
           case h3 of {
            Specif.Coq_existT l2 s0 ->
             case s0 of {
              Datatypes.Coq_inl _ -> Specif.Coq_existT l2
               (Logic.eq_rect_r (Datatypes.app l l2) (\_ ->
                 Logic.eq_rec_r (Datatypes.app l2 x0) (Datatypes.Coq_inl __)
                   z0) w0 iHw);
              Datatypes.Coq_inr _ ->
               Logic.eq_rect_r (Datatypes.app w0 l2)
                 (Logic.eq_rect_r (Datatypes.app l2 z0) (Specif.Coq_existT l2
                   (Datatypes.Coq_inr __)) x0) l}}) y0}}) w x y z __

app_eq_appT2_single_hdL :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list 
                           a1) -> (Datatypes.Coq_list a1) -> a1 ->
                           Datatypes.Coq_sum
                           (Specif.Coq_sigT (Datatypes.Coq_list a1) ()) 
                           ()
app_eq_appT2_single_hdL x y z w =
  (case y of {
    Datatypes.Coq_nil -> (\_ ->
     Logic.eq_rect (Datatypes.Coq_cons w x) (Datatypes.Coq_inr __) z);
    Datatypes.Coq_cons a y0 -> (\_ -> Datatypes.Coq_inl
     (Logic.eq_rect_r a (\_ ->
       Logic.eq_rect_r (Datatypes.app y0 z)
         (Logic.eq_rect_r a (\_ ->
           Logic.eq_rect_r (Datatypes.app y0 z) (\_ -> Specif.Coq_existT y0
             __) x __) w __) x) w __))}) __

app_eq_appT2_single_tlL :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list 
                           a1) -> (Datatypes.Coq_list a1) -> a1 ->
                           Datatypes.Coq_sum
                           (Specif.Coq_sigT (Datatypes.Coq_list a1) ()) 
                           ()
app_eq_appT2_single_tlL x y z w =
  let {s = list_nil_or_tail_singleton z} in
  case s of {
   Datatypes.Coq_inl _ ->
    Logic.eq_rect_r Datatypes.Coq_nil (\_ ->
      Logic.eq_rect (Datatypes.app x (Datatypes.Coq_cons w Datatypes.Coq_nil))
        (Datatypes.Coq_inr __) y) z __;
   Datatypes.Coq_inr s0 ->
    case s0 of {
     Specif.Coq_existT s1 s2 ->
      case s2 of {
       Specif.Coq_existT s3 _ ->
        Logic.eq_rect_r
          (Datatypes.app s1 (Datatypes.Coq_cons s3 Datatypes.Coq_nil)) (\_ ->
          Datatypes.Coq_inl
          (Logic.eq_rect_r (Datatypes.app y s1)
            (Logic.eq_rect_r s3 (Specif.Coq_existT s1 __) w) x)) z __}}}

