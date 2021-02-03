module List_lemmasT where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Specif
import qualified GenT

__ :: any
__ = Prelude.error "Logical or arity value used"

partition_2_2T :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> a1 -> a1
                  -> Prelude.Either (Specif.Coq_sigT (([]) a1) ())
                  (Prelude.Either () (([]) a1))
partition_2_2T l1 l2 l3 l4 a b =
  Datatypes.list_rect (\l5 l6 l7 b0 c _ ->
    case l6 of {
     ([]) -> Prelude.Right (Prelude.Left __);
     (:) a0 l8 ->
      Logic.eq_rect_r a0 (\_ ->
        Logic.eq_rect_r (Datatypes.app l8 ((:) c l7))
          (Logic.eq_rect_r a0 (\_ ->
            Logic.eq_rect_r (Datatypes.app l8 ((:) c l7)) (\_ -> Prelude.Right
              (Prelude.Right l8)) l5 __) b0 __) l5) b0 __})
    (\a0 l5 iHl1 l6 l7 l8 b0 c _ ->
    case l7 of {
     ([]) ->
      Logic.eq_rect_r c (\_ ->
        Logic.eq_rect (Datatypes.app l5 ((:) b0 l6))
          (Logic.eq_rect_r c (\_ ->
            Logic.eq_rect (Datatypes.app l5 ((:) b0 l6)) (\_ -> Prelude.Left
              (Specif.Coq_existT l5 __)) l8 __) a0 __) l8) a0 __;
     (:) a1 l9 ->
      Logic.eq_rect_r a1 (\_ ->
        Logic.eq_rect (Datatypes.app l5 ((:) b0 l6))
          (Logic.eq_rect_r a1 (\_ ->
            let {h3 = iHl1 l6 l9 l8 b0 c __} in
            case h3 of {
             Prelude.Left s ->
              case s of {
               Specif.Coq_existT l10 _ ->
                Logic.eq_rect_r (Datatypes.app l9 ((:) c l10)) (\_ _ ->
                  Logic.eq_rect_r (Datatypes.app l10 ((:) b0 l6)) (\_ ->
                    Prelude.Left (Specif.Coq_existT l10 __)) l8 __) l5 iHl1 __};
             Prelude.Right s ->
              case s of {
               Prelude.Left _ ->
                Logic.eq_rect_r l5 (\_ ->
                  Logic.eq_rect_r c (\_ ->
                    Logic.eq_rect_r l8 (\_ -> Prelude.Right (Prelude.Left __))
                      l6 __) b0 __) l9 __;
               Prelude.Right s0 ->
                Logic.eq_rect_r (Datatypes.app l5 ((:) b0 s0)) (\_ ->
                  Logic.eq_rect_r (Datatypes.app s0 ((:) c l8)) (\_ ->
                    Prelude.Right (Prelude.Right s0)) l6 __) l9 __}}) a0 __)
          (Datatypes.app l9 ((:) c l8))) a0 __}) l1 l2 l3 l4 a b __

cons_eq_appT2 :: (([]) a1) -> (([]) a1) -> (([]) a1) -> a1 -> Prelude.Either
                 () (Specif.Coq_sigT (([]) a1) ())
cons_eq_appT2 x y z a =
  case y of {
   ([]) -> Logic.eq_rect ((:) a x) (Prelude.Left __) z;
   (:) a0 y0 -> Prelude.Right
    (Logic.eq_rect_r (Datatypes.app y0 z) (\_ ->
      Logic.eq_rect_r a0 (\_ -> Specif.Coq_existT y0 __) a __) x __)}

app_eq_consT2 :: (([]) a1) -> (([]) a1) -> (([]) a1) -> a1 -> Prelude.Either
                 () (Specif.Coq_sigT (([]) a1) ())
app_eq_consT2 =
  cons_eq_appT2

app_eq_appT2 :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) ->
                Specif.Coq_sigT (([]) a1) (Prelude.Either () ())
app_eq_appT2 w x y z =
  Datatypes.list_rect (\x0 y0 z0 _ ->
    Logic.eq_rect_r (Datatypes.app y0 z0) (Specif.Coq_existT y0 (Prelude.Right
      __)) x0) (\a w0 iHw x0 y0 z0 _ ->
    let {h = cons_eq_appT2 (Datatypes.app w0 x0) y0 z0 a} in
    case h of {
     Prelude.Left _ ->
      Logic.eq_rect_r ([])
        (Logic.eq_rect_r ((:) a (Datatypes.app w0 x0)) (Specif.Coq_existT ((:)
          a w0) (Prelude.Left __)) z0) y0;
     Prelude.Right s ->
      case s of {
       Specif.Coq_existT l _ ->
        Logic.eq_rect_r ((:) a l)
          (let {h3 = iHw x0 l z0 __} in
           case h3 of {
            Specif.Coq_existT l2 s0 ->
             case s0 of {
              Prelude.Left _ ->
               Logic.eq_rect_r (Datatypes.app l l2) (\_ ->
                 Logic.eq_rect_r (Datatypes.app l2 x0) (Specif.Coq_existT l2
                   (Prelude.Left __)) z0) w0 iHw;
              Prelude.Right _ ->
               Logic.eq_rect_r (Datatypes.app w0 l2)
                 (Logic.eq_rect_r (Datatypes.app l2 z0) (Specif.Coq_existT l2
                   (Prelude.Right __)) x0) l}}) y0}}) w x y z __

app_eq_unitT2 :: (([]) a1) -> (([]) a1) -> a1 -> Prelude.Either () ()
app_eq_unitT2 x y a =
  case x of {
   ([]) -> Prelude.Left __;
   (:) a0 x0 ->
    Logic.eq_rec_r a (\_ ->
      Logic.eq_rec (Datatypes.app x0 y)
        (Logic.eq_rec_r a (\_ -> Prelude.Right __) a0 __) ([])) a0 __}

unit_eq_appT2 :: (([]) a1) -> (([]) a1) -> a1 -> Prelude.Either () ()
unit_eq_appT2 =
  app_eq_unitT2

partition_singleton_app :: (([]) a1) -> (([]) a1) -> (([]) a1) -> a1 -> a1 ->
                           Prelude.Either () (Specif.Coq_sigT (([]) a1) ())
partition_singleton_app l1 l2 l3 a b =
  Datatypes.list_rect (\l4 l5 a0 b0 _ ->
    case l4 of {
     ([]) ->
      Logic.eq_rect_r b0 (\_ -> Logic.eq_rect ([]) (Prelude.Left __) l5) a0 __;
     (:) _ _ -> Logic.coq_False_rect}) (\a0 l4 iHL1 l5 l6 a1 b0 _ ->
    case l5 of {
     ([]) ->
      Logic.eq_rect_r b0 (\_ ->
        Logic.eq_rect (Datatypes.app l4 ((:) a1 ([])))
          (Logic.eq_rect_r b0 (\_ ->
            Logic.eq_rect (Datatypes.app l4 ((:) a1 ([]))) (\_ ->
              Prelude.Right (Specif.Coq_existT l4 __)) l6 __) a0 __) l6) a0 __;
     (:) t l7 ->
      Logic.eq_rect_r t (\_ ->
        Logic.eq_rect (Datatypes.app l4 ((:) a1 ([])))
          (Logic.eq_rect_r t (\_ ->
            let {h2 = iHL1 l7 l6 a1 b0 __} in
            case h2 of {
             Prelude.Left _ ->
              Logic.eq_rect_r ([]) (\_ ->
                Logic.eq_rect_r l7 (\_ _ ->
                  Logic.eq_rect_r b0 (\_ -> Prelude.Left __) a1 __) l4 iHL1 __)
                l6 __;
             Prelude.Right h3 ->
              case h3 of {
               Specif.Coq_existT h4 _ ->
                Logic.eq_rect_r (Datatypes.app h4 ((:) a1 ([]))) (\_ ->
                  Logic.eq_rect_r
                    (Datatypes.app l7 (Datatypes.app ((:) b0 ([])) h4))
                    (\_ _ -> Prelude.Right (Specif.Coq_existT h4 __)) l4 iHL1
                    __) l6 __}}) a0 __) (Datatypes.app l7 ((:) b0 l6))) a0 __})
    l1 l2 l3 a b __

coq_InT_mid :: (([]) a1) -> (([]) a1) -> a1 -> GenT.InT a1
coq_InT_mid l1 l2 a =
  GenT.coq_InT_appR a l1 (Datatypes.app ((:) a ([])) l2)
    (GenT.coq_InT_appL a ((:) a ([])) l2 (GenT.InT_eq' a ([])))

coq_InT_singleton_mid :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) 
                         a1) -> a1 -> a1 -> Prelude.Either (GenT.InT a1)
                         (GenT.InT a1)
coq_InT_singleton_mid l1 l2 l3 l4 a b =
  let {hin = coq_InT_mid l1 l2 a} in
  let {
   hin0 = Logic.eq_rect (Datatypes.app l1 (Datatypes.app ((:) a ([])) l2)) hin
            (Datatypes.app l3 (Datatypes.app ((:) b ([])) l4))}
  in
  let {hin1 = GenT.coq_InT_appE a l3 (Datatypes.app ((:) b ([])) l4) hin0} in
  case hin1 of {
   Prelude.Left i -> Prelude.Left i;
   Prelude.Right i ->
    case i of {
     GenT.InT_eq' b0 l ->
      Logic.eq_rect_r b (\_ ->
        Logic.eq_rect_r l4 (\_ ->
          Logic.eq_rect_r a (\_ _ _ _ -> Logic.coq_False_rect) b __ __ i __) l)
        b0 __ __;
     GenT.InT_cons b0 l x ->
      Logic.eq_rect_r b (\_ -> Logic.eq_rect_r l4 (\x0 -> Prelude.Right x0) l)
        b0 __ x}}

list_nil_or_tail_singleton :: (([]) a1) -> Prelude.Either ()
                              (Specif.Coq_sigT (([]) a1)
                              (Specif.Coq_sigT a1 ()))
list_nil_or_tail_singleton l =
  Datatypes.list_rect (Prelude.Left __) (\a l0 iHl -> Prelude.Right
    (case iHl of {
      Prelude.Left _ ->
       Logic.eq_rect_r ([]) (Specif.Coq_existT ([]) (Specif.Coq_existT a __))
         l0;
      Prelude.Right s ->
       case s of {
        Specif.Coq_existT l2' s0 ->
         case s0 of {
          Specif.Coq_existT a' _ ->
           Logic.eq_rect_r (Datatypes.app l2' ((:) a' ([])))
             (Specif.Coq_existT ((:) a l2') (Specif.Coq_existT a' __)) l0}}}))
    l

app_eq_appT2_nn :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) ->
                   Specif.Coq_sigT (([]) a1) (Prelude.Either () ())
app_eq_appT2_nn w x y z =
  Datatypes.list_rect (\x0 y0 z0 _ ->
    Logic.eq_rect_r (Datatypes.app y0 z0) (Specif.Coq_existT y0 (Prelude.Right
      __)) x0) (\a w0 iHw x0 y0 z0 _ ->
    let {h = cons_eq_appT2 (Datatypes.app w0 x0) y0 z0 a} in
    case h of {
     Prelude.Left _ ->
      Logic.eq_rect_r ([])
        (Logic.eq_rect_r ((:) a (Datatypes.app w0 x0)) (Specif.Coq_existT ((:)
          a w0) (Prelude.Left __)) z0) y0;
     Prelude.Right s ->
      case s of {
       Specif.Coq_existT l _ ->
        Logic.eq_rect_r ((:) a l)
          (let {h3 = iHw x0 l z0 __} in
           case h3 of {
            Specif.Coq_existT l2 s0 ->
             case s0 of {
              Prelude.Left _ -> Specif.Coq_existT l2
               (Logic.eq_rect_r (Datatypes.app l l2) (\_ ->
                 Logic.eq_rec_r (Datatypes.app l2 x0) (Prelude.Left __) z0) w0
                 iHw);
              Prelude.Right _ ->
               Logic.eq_rect_r (Datatypes.app w0 l2)
                 (Logic.eq_rect_r (Datatypes.app l2 z0) (Specif.Coq_existT l2
                   (Prelude.Right __)) x0) l}}) y0}}) w x y z __

app_eq_appT2_single_hdL :: (([]) a1) -> (([]) a1) -> (([]) a1) -> a1 ->
                           Prelude.Either (Specif.Coq_sigT (([]) a1) ()) 
                           ()
app_eq_appT2_single_hdL x y z w =
  case y of {
   ([]) -> Logic.eq_rect ((:) w x) (Prelude.Right __) z;
   (:) a y0 -> Prelude.Left
    (Logic.eq_rect_r a (\_ ->
      Logic.eq_rect_r (Datatypes.app y0 z)
        (Logic.eq_rect_r a (\_ ->
          Logic.eq_rect_r (Datatypes.app y0 z) (\_ -> Specif.Coq_existT y0 __)
            x __) w __) x) w __)}

app_eq_appT2_single_tlL :: (([]) a1) -> (([]) a1) -> (([]) a1) -> a1 ->
                           Prelude.Either (Specif.Coq_sigT (([]) a1) ()) 
                           ()
app_eq_appT2_single_tlL x y z w =
  let {s = list_nil_or_tail_singleton z} in
  case s of {
   Prelude.Left _ ->
    Logic.eq_rect_r ([]) (\_ ->
      Logic.eq_rect (Datatypes.app x ((:) w ([]))) (Prelude.Right __) y) z __;
   Prelude.Right s0 ->
    case s0 of {
     Specif.Coq_existT s1 s2 ->
      case s2 of {
       Specif.Coq_existT s3 _ ->
        Logic.eq_rect_r (Datatypes.app s1 ((:) s3 ([]))) (\_ -> Prelude.Left
          (Logic.eq_rect_r (Datatypes.app y s1)
            (Logic.eq_rect_r s3 (Specif.Coq_existT s1 __) w) x)) z __}}}

