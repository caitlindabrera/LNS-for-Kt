module WeakenedT where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified LntT

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_weakened t =
   Coq_weakened_I (Datatypes.Coq_list t) (Datatypes.Coq_list t) (Datatypes.Coq_list t) (Datatypes.Coq_list t) (Datatypes.Coq_list t)

weakened_I' :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> Coq_weakened a1
weakened_I' a b c _ =
  Coq_weakened_I (Datatypes.app a c) (Datatypes.app a (Datatypes.app b c)) a b c

data Coq_weakened_multi t =
   Coq_weak_multi_refl (Datatypes.Coq_list t)
 | Coq_weak_multi_step (Datatypes.Coq_list t) (Datatypes.Coq_list t) (Datatypes.Coq_list t) (Coq_weakened t) (Coq_weakened_multi t)

weakened_multi_rect :: ((Datatypes.Coq_list a1) -> a2) -> ((Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Coq_weakened a1) ->
                       (Coq_weakened_multi a1) -> a2 -> a2) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Coq_weakened_multi a1) -> a2
weakened_multi_rect f f0 =
  let {
   f1 _ _ w =
     case w of {
      Coq_weak_multi_refl x -> f x;
      Coq_weak_multi_step x y z w0 w1 -> f0 x y z w0 w1 (f1 y z w1)}}
  in f1

data Coq_weakened_seqL t =
   Coq_weak_seqL (Datatypes.Coq_list t) (Datatypes.Coq_list t) (Datatypes.Coq_list t) LntT.Coq_dir (Coq_weakened_multi t)

data Coq_weakened_seqR t =
   Coq_weak_seqR (Datatypes.Coq_list t) (Datatypes.Coq_list t) (Datatypes.Coq_list t) LntT.Coq_dir (Coq_weakened_multi t)

data Coq_weakened_seq t =
   Coq_weak_seq_baseL (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list t) (Datatypes.Coq_list t)) LntT.Coq_dir) (Datatypes.Coq_prod
                                                                                                                           (Datatypes.Coq_prod (Datatypes.Coq_list t)
                                                                                                                           (Datatypes.Coq_list t)) LntT.Coq_dir) (Coq_weakened_seqL
                                                                                                                                                                 t)
 | Coq_weak_seq_baseR (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list t) (Datatypes.Coq_list t)) LntT.Coq_dir) (Datatypes.Coq_prod
                                                                                                                           (Datatypes.Coq_prod (Datatypes.Coq_list t)
                                                                                                                           (Datatypes.Coq_list t)) LntT.Coq_dir) (Coq_weakened_seqR
                                                                                                                                                                 t)
 | Coq_weak_seq_baseLR (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list t) (Datatypes.Coq_list t)) LntT.Coq_dir) (Datatypes.Coq_prod
                                                                                                                            (Datatypes.Coq_prod (Datatypes.Coq_list t)
                                                                                                                            (Datatypes.Coq_list t)) LntT.Coq_dir) (Datatypes.Coq_prod
                                                                                                                                                                  (Datatypes.Coq_prod
                                                                                                                                                                  (Datatypes.Coq_list
                                                                                                                                                                  t)
                                                                                                                                                                  (Datatypes.Coq_list
                                                                                                                                                                  t))
                                                                                                                                                                  LntT.Coq_dir) 
 (Coq_weakened_seqL t) (Coq_weakened_seqR t)

data Coq_weakened_nseq t =
   Coq_weak_nseq_nil
 | Coq_weak_nseq_cons (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list t) (Datatypes.Coq_list t)) LntT.Coq_dir) (Datatypes.Coq_prod
                                                                                                                           (Datatypes.Coq_prod (Datatypes.Coq_list t)
                                                                                                                           (Datatypes.Coq_list t)) LntT.Coq_dir) (Datatypes.Coq_list
                                                                                                                                                                 (Datatypes.Coq_prod
                                                                                                                                                                 (Datatypes.Coq_prod
                                                                                                                                                                 (Datatypes.Coq_list
                                                                                                                                                                 t)
                                                                                                                                                                 (Datatypes.Coq_list
                                                                                                                                                                 t))
                                                                                                                                                                 LntT.Coq_dir)) 
 (Datatypes.Coq_list (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list t) (Datatypes.Coq_list t)) LntT.Coq_dir)) (Coq_weakened_seq t) (Coq_weakened_nseq t)

weakened_nseq_rect :: a2 -> ((Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir) -> (Datatypes.Coq_prod
                      (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir) -> (Datatypes.Coq_list
                      (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Datatypes.Coq_list
                      (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Coq_weakened_seq a1) -> (Coq_weakened_nseq
                      a1) -> a2 -> a2) -> (Datatypes.Coq_list (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) ->
                      (Datatypes.Coq_list (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Coq_weakened_nseq 
                      a1) -> a2
weakened_nseq_rect f f0 =
  let {
   f1 _ _ w =
     case w of {
      Coq_weak_nseq_nil -> f;
      Coq_weak_nseq_cons s1 s2 ns1 ns2 w0 w1 -> f0 s1 s2 ns1 ns2 w0 w1 (f1 ns1 ns2 w1)}}
  in f1

weakened_cons :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> a1 -> (Coq_weakened a1) -> Coq_weakened a1
weakened_cons y z a hc =
  (case hc of {
    Coq_weakened_I x y0 a0 b c -> (\_ _ ->
     Logic.eq_rect_r y (\_ ->
       Logic.eq_rect_r z (\_ _ ->
         Logic.eq_rect_r (Datatypes.app a0 c) (\hc0 _ ->
           Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app b c)) (\_ _ ->
             Logic.eq_rect_r (Datatypes.app (Datatypes.Coq_cons a a0) c)
               (Logic.eq_rect_r (Datatypes.app (Datatypes.Coq_cons a a0) (Datatypes.app b c)) (Coq_weakened_I (Datatypes.app (Datatypes.Coq_cons a a0) c)
                 (Datatypes.app (Datatypes.Coq_cons a a0) (Datatypes.app b c)) (Datatypes.Coq_cons a a0) b c) (Datatypes.Coq_cons a (Datatypes.app a0 (Datatypes.app b c))))
               (Datatypes.Coq_cons a (Datatypes.app a0 c))) z hc0 __) y hc __) y0) x __ __ __)}) __ __

weakened_multi_cons :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> a1 -> (Coq_weakened_multi a1) -> Coq_weakened_multi a1
weakened_multi_cons y z a hc =
  weakened_multi_rect (\x -> Coq_weak_multi_refl (Datatypes.Coq_cons a x)) (\x y0 z0 w _ iHHc -> Coq_weak_multi_step (Datatypes.Coq_cons a x) (Datatypes.Coq_cons a y0)
    (Datatypes.Coq_cons a z0) (weakened_cons x y0 a w) iHHc) y z hc

weakened_multi_L :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Coq_weakened_multi a1) -> Coq_weakened_multi a1
weakened_multi_L x =
  Datatypes.list_rect (\_ _ hc -> hc) (\a x0 iHX y z hc -> weakened_multi_cons (Datatypes.app x0 y) (Datatypes.app x0 z) a (iHX y z hc)) x

weakened_multi_same :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> Coq_weakened_multi a1
weakened_multi_same x y =
  Logic.eq_rect_r y (Coq_weak_multi_refl y) x

weakened_seq_refl :: (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir) -> Coq_weakened_seq a1
weakened_seq_refl s =
  case s of {
   Datatypes.Coq_pair p x ->
    (case p of {
      Datatypes.Coq_pair _UU0393_ _UU0394_ -> (\d -> Coq_weak_seq_baseL (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ _UU0394_) d) (Datatypes.Coq_pair (Datatypes.Coq_pair
       _UU0393_ _UU0394_) d) (Coq_weak_seqL _UU0393_ _UU0393_ _UU0394_ d (Coq_weak_multi_refl _UU0393_)))}) x}

weakened_nseq_refl :: (Datatypes.Coq_list (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> Coq_weakened_nseq a1
weakened_nseq_refl ns =
  Datatypes.list_rect Coq_weak_nseq_nil (\a ns0 iHns -> Coq_weak_nseq_cons a a ns0 ns0 (weakened_seq_refl a) iHns) ns

weak_appL :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> Coq_weakened a1
weak_appL x y =
  Logic.eq_rect (Datatypes.app y Datatypes.Coq_nil)
    (Logic.eq_rect (Datatypes.app x Datatypes.Coq_nil) (Coq_weakened_I (Datatypes.app x Datatypes.Coq_nil)
      (Datatypes.app (Datatypes.app x Datatypes.Coq_nil) (Datatypes.app y Datatypes.Coq_nil)) x y Datatypes.Coq_nil) x) y

weak_appR :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> Coq_weakened a1
weak_appR x y =
  Logic.eq_rect (Datatypes.app Datatypes.Coq_nil x)
    (Logic.eq_rect (Datatypes.app Datatypes.Coq_nil y) (Coq_weakened_I (Datatypes.app Datatypes.Coq_nil y)
      (Datatypes.app (Datatypes.app Datatypes.Coq_nil x) (Datatypes.app Datatypes.Coq_nil y)) Datatypes.Coq_nil x y) y) x

weakened_nseq_app :: (Datatypes.Coq_list (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Datatypes.Coq_list
                     (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Datatypes.Coq_list
                     (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Datatypes.Coq_list
                     (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Coq_weakened_nseq a1) -> (Coq_weakened_nseq
                     a1) -> Coq_weakened_nseq a1
weakened_nseq_app l1 =
  Datatypes.list_rect (\_ l3 _ h1 h2 ->
    (case h1 of {
      Coq_weak_nseq_nil -> (\_ _ -> Logic.eq_rect Datatypes.Coq_nil h2 l3);
      Coq_weak_nseq_cons _ _ _ _ x x0 -> (\_ _ -> Logic.coq_False_rect __ x x0)}) __ __) (\a l2 iHl1 l3 l4 l5 h1 h2 ->
    (case h1 of {
      Coq_weak_nseq_nil -> (\_ _ -> Logic.coq_False_rect __);
      Coq_weak_nseq_cons s1 s2 ns1 ns2 x x0 -> (\_ _ ->
       Logic.eq_rect_r a (\_ ->
         Logic.eq_rect_r l2 (\_ ->
           Logic.eq_rect (Datatypes.Coq_cons s2 ns2) (\x1 x2 ->
             Logic.eq_rect (Datatypes.Coq_cons s2 ns2) (\_ -> Coq_weak_nseq_cons a s2 (Datatypes.app l2 l3) (Datatypes.app ns2 l5) x1 (iHl1 l3 ns2 l5 x2 h2)) l4 h1) l4) ns1)
         s1 __ __ x x0)}) __ __) l1

weakened_consL :: (Datatypes.Coq_list a1) -> a1 -> Coq_weakened a1
weakened_consL a b =
  Logic.eq_rect_r (Datatypes.app (Datatypes.Coq_cons b Datatypes.Coq_nil) a) (Coq_weakened_I a (Datatypes.app (Datatypes.Coq_cons b Datatypes.Coq_nil) a) Datatypes.Coq_nil
    (Datatypes.Coq_cons b Datatypes.Coq_nil) a) (Datatypes.Coq_cons b a)

weakened_multi_appL :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> Coq_weakened_multi a1
weakened_multi_appL a b =
  Datatypes.list_rect (Coq_weak_multi_refl (Datatypes.app Datatypes.Coq_nil a)) (\a0 b0 iHB -> Coq_weak_multi_step a (Datatypes.Coq_cons a0 a) (Datatypes.Coq_cons a0
    (Datatypes.app b0 a)) (weakened_consL a a0) (weakened_multi_cons a (Datatypes.app b0 a) a0 iHB)) b

weak_L :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Coq_weakened a1) -> Coq_weakened a1
weak_L _ _ z x0 =
  case x0 of {
   Coq_weakened_I x y a b c ->
    Logic.eq_rect_r (Datatypes.app a c)
      (Logic.eq_rect_r (Datatypes.app a (Datatypes.app b c))
        (Logic.eq_rect_r (Datatypes.app (Datatypes.app z a) c)
          (Logic.eq_rect_r (Datatypes.app (Datatypes.app z a) (Datatypes.app b c)) (weakened_I' (Datatypes.app z a) b c c)
            (Datatypes.app z (Datatypes.app a (Datatypes.app b c)))) (Datatypes.app z (Datatypes.app a c))) y) x}

weak_R :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Coq_weakened a1) -> Coq_weakened a1
weak_R _ _ z x0 =
  case x0 of {
   Coq_weakened_I x y a b c ->
    Logic.eq_rect_r (Datatypes.app a c)
      (Logic.eq_rect_r (Datatypes.app a (Datatypes.app b c))
        (Logic.eq_rect (Datatypes.app a (Datatypes.app c z))
          (Logic.eq_rect (Datatypes.app a (Datatypes.app (Datatypes.app b c) z))
            (Logic.eq_rect (Datatypes.app b (Datatypes.app c z)) (weakened_I' a b (Datatypes.app c z) c) (Datatypes.app (Datatypes.app b c) z))
            (Datatypes.app (Datatypes.app a (Datatypes.app b c)) z)) (Datatypes.app (Datatypes.app a c) z)) y) x}

weak_cons :: a1 -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Coq_weakened a1) -> Coq_weakened a1
weak_cons x _ _ x0 =
  case x0 of {
   Coq_weakened_I x1 y a b c ->
    Logic.eq_rect_r (Datatypes.app a c)
      (Logic.eq_rect_r (Datatypes.app a (Datatypes.app b c))
        (Logic.eq_rect_r (Datatypes.app (Datatypes.app a b) c)
          (Logic.eq_rect_r (Datatypes.app (Datatypes.Coq_cons x a) c)
            (Logic.eq_rect_r (Datatypes.app (Datatypes.Coq_cons x (Datatypes.app a b)) c)
              (Logic.eq_rect_r (Datatypes.app (Datatypes.Coq_cons x a) b)
                (Logic.eq_rect (Datatypes.app (Datatypes.Coq_cons x a) (Datatypes.app b c)) (weakened_I' (Datatypes.Coq_cons x a) b c c)
                  (Datatypes.app (Datatypes.app (Datatypes.Coq_cons x a) b) c)) (Datatypes.Coq_cons x (Datatypes.app a b))) (Datatypes.Coq_cons x
              (Datatypes.app (Datatypes.app a b) c))) (Datatypes.Coq_cons x (Datatypes.app a c))) (Datatypes.app a (Datatypes.app b c))) y) x1}

weak_simpleRX :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> Coq_weakened a1
weak_simpleRX a b =
  Coq_weakened_I a (Datatypes.app a b) a b Datatypes.Coq_nil

weak_simpleLX :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> Coq_weakened a1
weak_simpleLX a b =
  Coq_weakened_I a (Datatypes.app b a) Datatypes.Coq_nil b a

weakened_seq_appL :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> LntT.Coq_dir -> Coq_weakened_seq a1
weakened_seq_appL a b l1 l2 d =
  Coq_weak_seq_baseLR (Datatypes.Coq_pair (Datatypes.Coq_pair a b) d) (Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.app l1 a) b) d) (Datatypes.Coq_pair
    (Datatypes.Coq_pair (Datatypes.app l1 a) (Datatypes.app l2 b)) d) (Coq_weak_seqL a (Datatypes.app l1 a) b d (weakened_multi_appL a l1)) (Coq_weak_seqR b
    (Datatypes.app l2 b) (Datatypes.app l1 a) d (weakened_multi_appL b l2))

weakened_nseq_app_sameL :: (Datatypes.Coq_list (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Datatypes.Coq_list
                           (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Datatypes.Coq_list
                           (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Coq_weakened_nseq a1) ->
                           Coq_weakened_nseq a1
weakened_nseq_app_sameL l1 l2 l3 x =
  weakened_nseq_app l1 l2 l1 l3 (weakened_nseq_refl l1) x

weakened_nseq_app_sameR :: (Datatypes.Coq_list (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Datatypes.Coq_list
                           (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Datatypes.Coq_list
                           (Datatypes.Coq_prod (Datatypes.Coq_prod (Datatypes.Coq_list a1) (Datatypes.Coq_list a1)) LntT.Coq_dir)) -> (Coq_weakened_nseq a1) ->
                           Coq_weakened_nseq a1
weakened_nseq_app_sameR l1 l2 l3 x =
  weakened_nseq_app l2 l1 l3 l1 x (weakened_nseq_refl l1)

