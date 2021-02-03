module SwappedT where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Nat
import qualified PeanoNat
import qualified Specif

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_swapped t =
   Coq_swapped_I (Datatypes.Coq_list t) (Datatypes.Coq_list t) (Datatypes.Coq_list t) 
 (Datatypes.Coq_list t) (Datatypes.Coq_list t) (Datatypes.Coq_list t)

swapped_I' :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list
              a1) -> (Datatypes.Coq_list a1) -> Coq_swapped a1
swapped_I' a b c d =
  Coq_swapped_I (Datatypes.app a (Datatypes.app b (Datatypes.app c d)))
    (Datatypes.app a (Datatypes.app c (Datatypes.app b d))) a b c d

swapped_same :: (Datatypes.Coq_list a1) -> Coq_swapped a1
swapped_same x =
  Coq_swapped_I x x Datatypes.Coq_nil Datatypes.Coq_nil Datatypes.Coq_nil x

swapped_L :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list 
             a1) -> (Coq_swapped a1) -> Coq_swapped a1
swapped_L x y z x0 =
  (case x0 of {
    Coq_swapped_I x1 y0 a b c d -> (\_ _ ->
     Logic.eq_rect_r x (\_ ->
       Logic.eq_rect_r y (\_ _ ->
         Logic.eq_rect_r (Datatypes.app a (Datatypes.app b (Datatypes.app c d))) (\x2 _ ->
           Logic.eq_rect_r (Datatypes.app a (Datatypes.app c (Datatypes.app b d)))
             (\_ _ ->
             Logic.eq_rect_r
               (Datatypes.app (Datatypes.app z a) (Datatypes.app b (Datatypes.app c d)))
               (Logic.eq_rect_r
                 (Datatypes.app (Datatypes.app z a) (Datatypes.app c (Datatypes.app b d)))
                 (swapped_I' (Datatypes.app z a) b c d)
                 (Datatypes.app z (Datatypes.app a (Datatypes.app c (Datatypes.app b d)))))
               (Datatypes.app z (Datatypes.app a (Datatypes.app b (Datatypes.app c d)))))
             y x2 __) x x0 __) y0) x1 __ __ __)}) __ __

swapped_R :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list 
             a1) -> (Coq_swapped a1) -> Coq_swapped a1
swapped_R _ _ z x0 =
  case x0 of {
   Coq_swapped_I x y a b c d ->
    Logic.eq_rect_r (Datatypes.app a (Datatypes.app b (Datatypes.app c d)))
      (Logic.eq_rect_r (Datatypes.app a (Datatypes.app c (Datatypes.app b d)))
        (Logic.eq_rect
          (Datatypes.app a (Datatypes.app (Datatypes.app b (Datatypes.app c d)) z))
          (Logic.eq_rect (Datatypes.app b (Datatypes.app (Datatypes.app c d) z))
            (Logic.eq_rect (Datatypes.app c (Datatypes.app d z))
              (Logic.eq_rect
                (Datatypes.app a (Datatypes.app (Datatypes.app c (Datatypes.app b d)) z))
                (Logic.eq_rect (Datatypes.app c (Datatypes.app (Datatypes.app b d) z))
                  (Logic.eq_rect (Datatypes.app b (Datatypes.app d z))
                    (swapped_I' a b c (Datatypes.app d z))
                    (Datatypes.app (Datatypes.app b d) z))
                  (Datatypes.app (Datatypes.app c (Datatypes.app b d)) z))
                (Datatypes.app (Datatypes.app a (Datatypes.app c (Datatypes.app b d))) z))
              (Datatypes.app (Datatypes.app c d) z))
            (Datatypes.app (Datatypes.app b (Datatypes.app c d)) z))
          (Datatypes.app (Datatypes.app a (Datatypes.app b (Datatypes.app c d))) z)) y) x}

swapped_cons :: a1 -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Coq_swapped
                a1) -> Coq_swapped a1
swapped_cons x _ _ h =
  case h of {
   Coq_swapped_I x0 y a b c d ->
    Logic.eq_rect_r (Datatypes.app a (Datatypes.app b (Datatypes.app c d)))
      (Logic.eq_rect_r (Datatypes.app a (Datatypes.app c (Datatypes.app b d)))
        (Logic.eq_rect_r
          (Datatypes.app (Datatypes.Coq_cons x a) (Datatypes.app b (Datatypes.app c d)))
          (Logic.eq_rect_r
            (Datatypes.app (Datatypes.Coq_cons x a) (Datatypes.app c (Datatypes.app b d)))
            (swapped_I' (Datatypes.Coq_cons x a) b c d) (Datatypes.Coq_cons x
            (Datatypes.app a (Datatypes.app c (Datatypes.app b d))))) (Datatypes.Coq_cons
          x (Datatypes.app a (Datatypes.app b (Datatypes.app c d))))) y) x0}

swapped_simple :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                  (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> Coq_swapped 
                  a1
swapped_simple u v x y =
  Logic.eq_rect_r (Datatypes.app x y)
    (Logic.eq_rect_r (Datatypes.app y x) (Coq_swapped_I (Datatypes.app x y)
      (Datatypes.app y x) Datatypes.Coq_nil x y Datatypes.Coq_nil) v) u

swapped_simple' :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> Coq_swapped a1
swapped_simple' x y =
  swapped_simple (Datatypes.app x y) (Datatypes.app y x) x y

swapped_simpleL :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                   (Datatypes.Coq_list a1) -> Coq_swapped a1
swapped_simpleL x y z =
  Logic.eq_rect_r z (swapped_simple' x z) y

swapped_simpleR :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                   (Datatypes.Coq_list a1) -> Coq_swapped a1
swapped_simpleR x y z =
  Logic.eq_rect_r z (swapped_simple' z x) y

swapped_comm :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Coq_swapped 
                a1) -> Coq_swapped a1
swapped_comm a b h =
  (case h of {
    Coq_swapped_I x y a0 b0 c d -> (\_ _ ->
     Logic.eq_rect_r a (\_ ->
       Logic.eq_rect_r b (\_ _ ->
         Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app b0 (Datatypes.app c d)))
           (\h0 _ ->
           Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app c (Datatypes.app b0 d)))
             (\_ _ -> swapped_I' a0 c b0 d) b h0 __) a h __) y) x __ __ __)}) __ __

data Coq_swapped_spec t =
   Coq_swapped_spec_I (Datatypes.Coq_list t) (Datatypes.Coq_list t) (Coq_swapped t)
 | Coq_swapped_spec_step Datatypes.Coq_nat (Datatypes.Coq_list t) (Datatypes.Coq_list t) 
 (Datatypes.Coq_list t) (Coq_swapped_spec t) (Coq_swapped t)

swapped_spec_refl :: Datatypes.Coq_nat -> (Datatypes.Coq_list a1) -> Coq_swapped_spec a1
swapped_spec_refl n =
  Datatypes.nat_rect (\a -> Coq_swapped_spec_I a a (swapped_same a)) (\n0 iHn a ->
    Coq_swapped_spec_step n0 a a a (iHn a) (swapped_same a)) n

swapped_app_L :: Datatypes.Coq_nat -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list 
                 a1) -> (Datatypes.Coq_list a1) -> (Coq_swapped_spec a1) ->
                 Coq_swapped_spec a1
swapped_app_L n =
  Datatypes.nat_rect (\l a b hswap -> Coq_swapped_spec_I (Datatypes.app l a)
    (Datatypes.app l b)
    (swapped_L a b l
      ((case hswap of {
         Coq_swapped_spec_I x y x0 -> (\_ _ _ ->
          Logic.eq_rect_r a (\_ -> Logic.eq_rect_r b (\x1 -> x1) y) x __ x0);
         Coq_swapped_spec_step _ _ _ _ x x0 -> (\_ _ _ -> Logic.coq_False_rect __ __ x x0)})
        __ __ __))) (\n0 iHn l a b hswap ->
    (case hswap of {
      Coq_swapped_spec_I _ _ x0 -> (\_ _ _ -> Logic.coq_False_rect __ __ x0);
      Coq_swapped_spec_step n1 a0 b0 c x x0 -> (\_ _ _ ->
       Logic.eq_rect_r n0 (\_ ->
         Logic.eq_rect_r a (\_ ->
           Logic.eq_rect_r b (\x1 x2 -> Coq_swapped_spec_step n0 (Datatypes.app l a)
             (Datatypes.app l b0) (Datatypes.app l b) (iHn l a b0 x1)
             (swapped_L b0 b l x2)) c) a0) n1 __ __ x x0)}) __ __ __) n

swapped_spec_trans :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> (Datatypes.Coq_list 
                      a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                      (Coq_swapped_spec a1) -> (Coq_swapped_spec a1) -> Specif.Coq_sigT
                      Datatypes.Coq_nat (Coq_swapped_spec a1)
swapped_spec_trans n1 n2 =
  Datatypes.nat_rect (\l1 l2 l3 h1 h2 ->
    (case h2 of {
      Coq_swapped_spec_I x y x0 -> (\_ _ _ ->
       Logic.eq_rect_r l2 (\_ ->
         Logic.eq_rect_r l3 (\x1 -> Specif.Coq_existT (Datatypes.S n1)
           (Coq_swapped_spec_step n1 l1 l2 l3 h1 x1)) y) x __ x0);
      Coq_swapped_spec_step _ _ _ _ x x0 -> (\_ _ _ -> Logic.coq_False_rect __ __ x x0)})
      __ __ __) (\n3 iHn2 l1 l2 l3 h1 h2 ->
    (case h2 of {
      Coq_swapped_spec_I _ _ x0 -> (\_ _ _ -> Logic.coq_False_rect __ __ x0);
      Coq_swapped_spec_step n a b c x x0 -> (\_ _ _ ->
       Logic.eq_rect_r n3 (\_ ->
         Logic.eq_rect_r l2 (\_ ->
           Logic.eq_rect_r l3 (\x1 x2 ->
             let {h3 = iHn2 l1 l2 b h1 x1} in
             case h3 of {
              Specif.Coq_existT m h4 -> Specif.Coq_existT (Datatypes.S m)
               (Coq_swapped_spec_step m l1 b l3 h4 x2)}) c) a) n __ __ x x0)}) __ __ __)
    n2

swapped_spec_trans_exact :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> (Datatypes.Coq_list
                            a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list 
                            a1) -> (Coq_swapped_spec a1) -> (Coq_swapped_spec a1) ->
                            Coq_swapped_spec a1
swapped_spec_trans_exact n1 n2 =
  Datatypes.nat_rect (\l1 l2 l3 h1 h2 ->
    (case h2 of {
      Coq_swapped_spec_I x0 y x -> (\_ _ _ ->
       Logic.eq_rect_r l2 (\_ ->
         Logic.eq_rect_r l3 (\x1 ->
           Logic.eq_rect_r n1 (Coq_swapped_spec_step n1 l1 l2 l3 h1 x1)
             (PeanoNat._Nat__add n1 Datatypes.O)) y) x0 __ x);
      Coq_swapped_spec_step _ _ _ _ x x0 -> (\_ _ _ -> Logic.coq_False_rect __ __ x x0)})
      __ __ __) (\n3 iHn2 l1 l2 l3 h1 h2 ->
    (case h2 of {
      Coq_swapped_spec_I _ _ x0 -> (\_ _ _ -> Logic.coq_False_rect __ __ x0);
      Coq_swapped_spec_step n a b c x x0 -> (\_ _ _ ->
       Logic.eq_rect_r n3 (\_ ->
         Logic.eq_rect_r l2 (\_ ->
           Logic.eq_rect_r l3 (\x1 x2 ->
             let {h3 = iHn2 l1 l2 b h1 x1} in
             Coq_swapped_spec_step (Nat.add n1 (Datatypes.S n3)) l1 b l3
             (Logic.eq_rect (PeanoNat._Nat__add (Datatypes.S n1) n3) h3
               (PeanoNat._Nat__add n1 (Datatypes.S n3))) x2) c) a) n __ __ x x0)}) __ __
      __) n2

swapped_spec_comm :: Datatypes.Coq_nat -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list
                     a1) -> (Coq_swapped_spec a1) -> Coq_swapped_spec a1
swapped_spec_comm n =
  Datatypes.nat_rect (\a b h -> Coq_swapped_spec_I b a
    ((case h of {
       Coq_swapped_spec_I x0 y x -> (\_ _ _ ->
        Logic.eq_rect_r a (\_ -> Logic.eq_rect_r b (\x1 -> swapped_comm a b x1) y) x0 __ x);
       Coq_swapped_spec_step _ _ _ _ x x0 -> (\_ _ _ -> Logic.coq_False_rect __ __ x x0)})
      __ __ __)) (\n0 iHn a b h ->
    (case h of {
      Coq_swapped_spec_I _ _ x0 -> (\_ _ _ -> Logic.coq_False_rect __ __ x0);
      Coq_swapped_spec_step n1 a0 b0 c x x0 -> (\_ _ _ ->
       Logic.eq_rect_r n0 (\_ ->
         Logic.eq_rect_r a (\_ ->
           Logic.eq_rect_r b (\x1 x2 ->
             let {x3 = swapped_comm b0 b x2} in
             let {x4 = Coq_swapped_spec_I b b0 x3} in
             let {x5 = iHn a b0 x1} in
             swapped_spec_trans_exact Datatypes.O n0 b b0 a x4 x5) c) a0) n1 __ __ x x0)})
      __ __ __) n

swapped_spec_conv :: Datatypes.Coq_nat -> Datatypes.Coq_nat -> (Datatypes.Coq_list 
                     a1) -> (Datatypes.Coq_list a1) -> (Coq_swapped_spec a1) ->
                     Coq_swapped_spec a1
swapped_spec_conv n m _ _ x =
  Logic.eq_rect_r m (\x0 -> x0) n x

swapped_app_mid_L :: Datatypes.Coq_nat -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list
                     a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                     (Datatypes.Coq_list a1) -> (Coq_swapped_spec a1) -> Coq_swapped_spec
                     a1
swapped_app_mid_L n a b c d e hswap =
  swapped_spec_conv (Datatypes.S (Nat.add Datatypes.O n)) (Datatypes.S n)
    (Datatypes.app a (Datatypes.app c (Datatypes.app b d))) e
    (swapped_spec_trans_exact Datatypes.O n
      (Datatypes.app a (Datatypes.app c (Datatypes.app b d)))
      (Datatypes.app a (Datatypes.app b (Datatypes.app c d))) e (Coq_swapped_spec_I
      (Datatypes.app a (Datatypes.app c (Datatypes.app b d)))
      (Datatypes.app a (Datatypes.app b (Datatypes.app c d))) (swapped_I' a c b d)) hswap)

swapped_app_mid_R :: Datatypes.Coq_nat -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list
                     a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                     (Datatypes.Coq_list a1) -> (Coq_swapped_spec a1) -> Coq_swapped_spec
                     a1
swapped_app_mid_R n a b c d e h =
  let {
   h0 = swapped_spec_comm n e (Datatypes.app a (Datatypes.app b (Datatypes.app c d))) h}
  in
  swapped_spec_comm (Datatypes.S n)
    (Datatypes.app a (Datatypes.app c (Datatypes.app b d))) e
    (swapped_app_mid_L n a b c d e h0)

swapped_spec_front_mid :: Datatypes.Coq_nat -> (Datatypes.Coq_list a1) ->
                          (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                          (Datatypes.Coq_list a1) -> (Coq_swapped_spec a1) ->
                          Specif.Coq_sigT Datatypes.Coq_nat (Coq_swapped_spec a1)
swapped_spec_front_mid n a b c d hswap =
  let {hswap0 = swapped_app_L n a b (Datatypes.app c d) hswap} in
  swapped_spec_trans n (Datatypes.S Datatypes.O) (Datatypes.app a b)
    (Datatypes.app a (Datatypes.app c d)) (Datatypes.app c (Datatypes.app a d)) hswap0
    (Logic.eq_rect (Datatypes.app Datatypes.Coq_nil (Datatypes.app c (Datatypes.app a d)))
      (swapped_app_mid_R Datatypes.O Datatypes.Coq_nil a c d
        (Datatypes.app a (Datatypes.app c d))
        (swapped_spec_refl Datatypes.O
          (Datatypes.app Datatypes.Coq_nil (Datatypes.app a (Datatypes.app c d)))))
      (Datatypes.app c (Datatypes.app a d)))

swapped__n_mid :: Datatypes.Coq_nat -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list 
                  a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                  (Datatypes.Coq_list a1) -> (Coq_swapped_spec a1) -> Specif.Coq_sigT
                  Datatypes.Coq_nat (Coq_swapped_spec a1)
swapped__n_mid m l _UU0393_1 _UU0393_2 _UU0393_1' _UU0393_2' h =
  let {
   h0 = swapped_app_L m l (Datatypes.app _UU0393_1 _UU0393_2)
          (Datatypes.app _UU0393_1' _UU0393_2') h}
  in
  let {
   h1 = Logic.eq_rect_r (Datatypes.app l (Datatypes.app _UU0393_1' _UU0393_2')) h0
          (Datatypes.app Datatypes.Coq_nil
            (Datatypes.app l (Datatypes.app _UU0393_1' _UU0393_2')))}
  in
  Specif.Coq_existT (Datatypes.S (Datatypes.S m))
  (Logic.eq_rect
    (Datatypes.app Datatypes.Coq_nil
      (Datatypes.app _UU0393_1 (Datatypes.app l _UU0393_2)))
    (Logic.eq_rect
      (Datatypes.app Datatypes.Coq_nil
        (Datatypes.app _UU0393_1' (Datatypes.app l _UU0393_2')))
      (swapped_app_mid_R (Datatypes.S m) Datatypes.Coq_nil l _UU0393_1' _UU0393_2'
        (Datatypes.app Datatypes.Coq_nil
          (Datatypes.app _UU0393_1 (Datatypes.app l _UU0393_2)))
        (swapped_app_mid_L m Datatypes.Coq_nil l _UU0393_1 _UU0393_2
          (Datatypes.app Datatypes.Coq_nil
            (Datatypes.app l (Datatypes.app _UU0393_1' _UU0393_2'))) h1))
      (Datatypes.app _UU0393_1' (Datatypes.app l _UU0393_2')))
    (Datatypes.app _UU0393_1 (Datatypes.app l _UU0393_2)))

type Coq_swapped_gen t =
  Specif.Coq_sigT Datatypes.Coq_nat (Coq_swapped_spec t)
  -- singleton inductive, whose constructor was swapped_gen_I
  
swapped_gen_front_mid :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                         (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                         (Coq_swapped_gen a1) -> Coq_swapped_gen a1
swapped_gen_front_mid a b c d hswap =
  case hswap of {
   Specif.Coq_existT n hs -> swapped_spec_front_mid n a b c d hs}

swapped_gen_app_L :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                     (Datatypes.Coq_list a1) -> (Coq_swapped_gen a1) -> Coq_swapped_gen 
                     a1
swapped_gen_app_L l a b h =
  case h of {
   Specif.Coq_existT n h2 -> let {h3 = swapped_app_L n l a b h2} in Specif.Coq_existT n h3}

swapped_gen_refl :: (Datatypes.Coq_list a1) -> Coq_swapped_gen a1
swapped_gen_refl a =
  Specif.Coq_existT Datatypes.O (swapped_spec_refl Datatypes.O a)

