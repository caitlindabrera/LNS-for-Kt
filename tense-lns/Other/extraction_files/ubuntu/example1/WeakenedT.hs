module WeakenedT where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified LntT

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_weakened t =
   Coq_weakened_I (([]) t) (([]) t) (([]) t) (([]) t) (([]) t)

weakened_I' :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> Coq_weakened a1
weakened_I' a b c _ =
  Coq_weakened_I (Datatypes.app a c) (Datatypes.app a (Datatypes.app b c)) a b c

data Coq_weakened_multi t =
   Coq_weak_multi_refl (([]) t)
 | Coq_weak_multi_step (([]) t) (([]) t) (([]) t) (Coq_weakened t) (Coq_weakened_multi t)

weakened_multi_rect :: ((([]) a1) -> a2) -> ((([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_weakened 
                       a1) -> (Coq_weakened_multi a1) -> a2 -> a2) -> (([]) a1) -> (([]) a1) ->
                       (Coq_weakened_multi a1) -> a2
weakened_multi_rect f f0 _ _ w =
  case w of {
   Coq_weak_multi_refl x -> f x;
   Coq_weak_multi_step x y z w0 w1 -> f0 x y z w0 w1 (weakened_multi_rect f f0 y z w1)}

data Coq_weakened_seqL t =
   Coq_weak_seqL (([]) t) (([]) t) (([]) t) LntT.Coq_dir (Coq_weakened_multi t)

data Coq_weakened_seqR t =
   Coq_weak_seqR (([]) t) (([]) t) (([]) t) LntT.Coq_dir (Coq_weakened_multi t)

data Coq_weakened_seq t =
   Coq_weak_seq_baseL ((,) ((,) (([]) t) (([]) t)) LntT.Coq_dir) ((,) ((,) (([]) t) (([]) t))
                                                                 LntT.Coq_dir) (Coq_weakened_seqL t)
 | Coq_weak_seq_baseR ((,) ((,) (([]) t) (([]) t)) LntT.Coq_dir) ((,) ((,) (([]) t) (([]) t))
                                                                 LntT.Coq_dir) (Coq_weakened_seqR t)
 | Coq_weak_seq_baseLR ((,) ((,) (([]) t) (([]) t)) LntT.Coq_dir) ((,) ((,) (([]) t) (([]) t))
                                                                  LntT.Coq_dir) ((,)
                                                                                ((,) (([]) t)
                                                                                (([]) t))
                                                                                LntT.Coq_dir) 
 (Coq_weakened_seqL t) (Coq_weakened_seqR t)

data Coq_weakened_nseq t =
   Coq_weak_nseq_nil
 | Coq_weak_nseq_cons ((,) ((,) (([]) t) (([]) t)) LntT.Coq_dir) ((,) ((,) (([]) t) (([]) t))
                                                                 LntT.Coq_dir) (([])
                                                                               ((,)
                                                                               ((,) (([]) t)
                                                                               (([]) t))
                                                                               LntT.Coq_dir)) 
 (([]) ((,) ((,) (([]) t) (([]) t)) LntT.Coq_dir)) (Coq_weakened_seq t) (Coq_weakened_nseq t)

weakened_nseq_rect :: a2 -> (((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,)
                      ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> (([])
                      ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                      ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (Coq_weakened_seq a1) ->
                      (Coq_weakened_nseq a1) -> a2 -> a2) -> (([])
                      ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                      ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (Coq_weakened_nseq a1) -> a2
weakened_nseq_rect f f0 _ _ w =
  case w of {
   Coq_weak_nseq_nil -> f;
   Coq_weak_nseq_cons s1 s2 ns1 ns2 w0 w1 ->
    f0 s1 s2 ns1 ns2 w0 w1 (weakened_nseq_rect f f0 ns1 ns2 w1)}

weakened_cons :: (([]) a1) -> (([]) a1) -> a1 -> (Coq_weakened a1) -> Coq_weakened a1
weakened_cons y z a hc =
  case hc of {
   Coq_weakened_I x y0 a0 b c ->
    Logic.eq_rect_r y (\_ ->
      Logic.eq_rect_r z (\_ _ ->
        Logic.eq_rect_r (Datatypes.app a0 c) (\hc0 _ ->
          Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app b c)) (\_ _ ->
            Logic.eq_rect_r (Datatypes.app ((:) a a0) c)
              (Logic.eq_rect_r (Datatypes.app ((:) a a0) (Datatypes.app b c)) (Coq_weakened_I
                (Datatypes.app ((:) a a0) c) (Datatypes.app ((:) a a0) (Datatypes.app b c)) ((:) a
                a0) b c) ((:) a (Datatypes.app a0 (Datatypes.app b c)))) ((:) a (Datatypes.app a0 c)))
            z hc0 __) y hc __) y0) x __ __ __}

weakened_multi_cons :: (([]) a1) -> (([]) a1) -> a1 -> (Coq_weakened_multi a1) -> Coq_weakened_multi
                       a1
weakened_multi_cons y z a hc =
  weakened_multi_rect (\x -> Coq_weak_multi_refl ((:) a x)) (\x y0 z0 w _ iHHc -> Coq_weak_multi_step
    ((:) a x) ((:) a y0) ((:) a z0) (weakened_cons x y0 a w) iHHc) y z hc

weakened_multi_L :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_weakened_multi a1) ->
                    Coq_weakened_multi a1
weakened_multi_L x =
  Datatypes.list_rect (\_ _ hc -> hc) (\a x0 iHX y z hc ->
    weakened_multi_cons (Datatypes.app x0 y) (Datatypes.app x0 z) a (iHX y z hc)) x

weakened_multi_same :: (([]) a1) -> (([]) a1) -> Coq_weakened_multi a1
weakened_multi_same x y =
  Logic.eq_rect_r y (Coq_weak_multi_refl y) x

weakened_seq_refl :: ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> Coq_weakened_seq a1
weakened_seq_refl s =
  case s of {
   (,) p x ->
    case p of {
     (,) _UU0393_ _UU0394_ -> Coq_weak_seq_baseL ((,) ((,) _UU0393_ _UU0394_) x) ((,) ((,) _UU0393_
      _UU0394_) x) (Coq_weak_seqL _UU0393_ _UU0393_ _UU0394_ x (Coq_weak_multi_refl _UU0393_))}}

weakened_nseq_refl :: (([]) ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> Coq_weakened_nseq a1
weakened_nseq_refl ns =
  Datatypes.list_rect Coq_weak_nseq_nil (\a ns0 iHns -> Coq_weak_nseq_cons a a ns0 ns0
    (weakened_seq_refl a) iHns) ns

weak_appL :: (([]) a1) -> (([]) a1) -> Coq_weakened a1
weak_appL x y =
  Logic.eq_rect (Datatypes.app y ([]))
    (Logic.eq_rect (Datatypes.app x ([])) (Coq_weakened_I (Datatypes.app x ([]))
      (Datatypes.app (Datatypes.app x ([])) (Datatypes.app y ([]))) x y ([])) x) y

weak_appR :: (([]) a1) -> (([]) a1) -> Coq_weakened a1
weak_appR x y =
  Logic.eq_rect (Datatypes.app ([]) x)
    (Logic.eq_rect (Datatypes.app ([]) y) (Coq_weakened_I (Datatypes.app ([]) y)
      (Datatypes.app (Datatypes.app ([]) x) (Datatypes.app ([]) y)) ([]) x y) y) x

weakened_nseq_app :: (([]) ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                     ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                     ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                     ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (Coq_weakened_nseq a1) ->
                     (Coq_weakened_nseq a1) -> Coq_weakened_nseq a1
weakened_nseq_app l1 =
  Datatypes.list_rect (\_ l3 _ h1 h2 ->
    case h1 of {
     Coq_weak_nseq_nil -> Logic.eq_rect ([]) h2 l3;
     Coq_weak_nseq_cons _ _ _ _ x x0 -> Logic.coq_False_rect __ x x0}) (\a l2 iHl1 l3 l4 l5 h1 h2 ->
    case h1 of {
     Coq_weak_nseq_nil -> Logic.coq_False_rect __;
     Coq_weak_nseq_cons s1 s2 ns1 ns2 x x0 ->
      Logic.eq_rect_r a (\_ ->
        Logic.eq_rect_r l2 (\_ ->
          Logic.eq_rect ((:) s2 ns2) (\x1 x2 ->
            Logic.eq_rect ((:) s2 ns2) (\_ -> Coq_weak_nseq_cons a s2 (Datatypes.app l2 l3)
              (Datatypes.app ns2 l5) x1 (iHl1 l3 ns2 l5 x2 h2)) l4 h1) l4) ns1) s1 __ __ x x0}) l1

weakened_consL :: (([]) a1) -> a1 -> Coq_weakened a1
weakened_consL a b =
  Logic.eq_rect_r (Datatypes.app ((:) b ([])) a) (Coq_weakened_I a (Datatypes.app ((:) b ([])) a)
    ([]) ((:) b ([])) a) ((:) b a)

weakened_multi_appL :: (([]) a1) -> (([]) a1) -> Coq_weakened_multi a1
weakened_multi_appL a b =
  Datatypes.list_rect (Coq_weak_multi_refl (Datatypes.app ([]) a)) (\a0 b0 iHB -> Coq_weak_multi_step
    a ((:) a0 a) ((:) a0 (Datatypes.app b0 a)) (weakened_consL a a0)
    (weakened_multi_cons a (Datatypes.app b0 a) a0 iHB)) b

weak_L :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_weakened a1) -> Coq_weakened a1
weak_L _ _ z x0 =
  case x0 of {
   Coq_weakened_I x y a b c ->
    Logic.eq_rect_r (Datatypes.app a c)
      (Logic.eq_rect_r (Datatypes.app a (Datatypes.app b c))
        (Logic.eq_rect_r (Datatypes.app (Datatypes.app z a) c)
          (Logic.eq_rect_r (Datatypes.app (Datatypes.app z a) (Datatypes.app b c))
            (weakened_I' (Datatypes.app z a) b c c)
            (Datatypes.app z (Datatypes.app a (Datatypes.app b c))))
          (Datatypes.app z (Datatypes.app a c))) y) x}

weak_R :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_weakened a1) -> Coq_weakened a1
weak_R _ _ z x0 =
  case x0 of {
   Coq_weakened_I x y a b c ->
    Logic.eq_rect_r (Datatypes.app a c)
      (Logic.eq_rect_r (Datatypes.app a (Datatypes.app b c))
        (Logic.eq_rect (Datatypes.app a (Datatypes.app c z))
          (Logic.eq_rect (Datatypes.app a (Datatypes.app (Datatypes.app b c) z))
            (Logic.eq_rect (Datatypes.app b (Datatypes.app c z))
              (weakened_I' a b (Datatypes.app c z) c) (Datatypes.app (Datatypes.app b c) z))
            (Datatypes.app (Datatypes.app a (Datatypes.app b c)) z))
          (Datatypes.app (Datatypes.app a c) z)) y) x}

weak_cons :: a1 -> (([]) a1) -> (([]) a1) -> (Coq_weakened a1) -> Coq_weakened a1
weak_cons x _ _ x0 =
  case x0 of {
   Coq_weakened_I x1 y a b c ->
    Logic.eq_rect_r (Datatypes.app a c)
      (Logic.eq_rect_r (Datatypes.app a (Datatypes.app b c))
        (Logic.eq_rect_r (Datatypes.app (Datatypes.app a b) c)
          (Logic.eq_rect_r (Datatypes.app ((:) x a) c)
            (Logic.eq_rect_r (Datatypes.app ((:) x (Datatypes.app a b)) c)
              (Logic.eq_rect_r (Datatypes.app ((:) x a) b)
                (Logic.eq_rect (Datatypes.app ((:) x a) (Datatypes.app b c))
                  (weakened_I' ((:) x a) b c c) (Datatypes.app (Datatypes.app ((:) x a) b) c)) ((:) x
                (Datatypes.app a b))) ((:) x (Datatypes.app (Datatypes.app a b) c))) ((:) x
            (Datatypes.app a c))) (Datatypes.app a (Datatypes.app b c))) y) x1}

weak_simpleRX :: (([]) a1) -> (([]) a1) -> Coq_weakened a1
weak_simpleRX a b =
  Coq_weakened_I a (Datatypes.app a b) a b ([])

weak_simpleLX :: (([]) a1) -> (([]) a1) -> Coq_weakened a1
weak_simpleLX a b =
  Coq_weakened_I a (Datatypes.app b a) ([]) b a

weakened_seq_appL :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> LntT.Coq_dir ->
                     Coq_weakened_seq a1
weakened_seq_appL a b l1 l2 d =
  Coq_weak_seq_baseLR ((,) ((,) a b) d) ((,) ((,) (Datatypes.app l1 a) b) d) ((,) ((,)
    (Datatypes.app l1 a) (Datatypes.app l2 b)) d) (Coq_weak_seqL a (Datatypes.app l1 a) b d
    (weakened_multi_appL a l1)) (Coq_weak_seqR b (Datatypes.app l2 b) (Datatypes.app l1 a) d
    (weakened_multi_appL b l2))

weakened_nseq_app_sameL :: (([]) ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                           ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                           ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (Coq_weakened_nseq 
                           a1) -> Coq_weakened_nseq a1
weakened_nseq_app_sameL l1 l2 l3 x =
  weakened_nseq_app l1 l2 l1 l3 (weakened_nseq_refl l1) x

weakened_nseq_app_sameR :: (([]) ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                           ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                           ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (Coq_weakened_nseq 
                           a1) -> Coq_weakened_nseq a1
weakened_nseq_app_sameR l1 l2 l3 x =
  weakened_nseq_app l2 l1 l3 l1 x (weakened_nseq_refl l1)

