module GenT where

import qualified Prelude
import qualified CRelationClasses
import qualified Datatypes
import qualified List
import qualified Logic
import qualified Specif

__ :: any
__ = Prelude.error "Logical or arity value used"

iffT_D1 :: (CRelationClasses.Coq_iffT a1 a2) -> a1 -> a2
iffT_D1 x a =
  case x of {
   Datatypes.Coq_pair f _ -> f a}

iffT_D2 :: (CRelationClasses.Coq_iffT a1 a2) -> a2 -> a1
iffT_D2 x b =
  case x of {
   Datatypes.Coq_pair _ g -> g b}

data ForallT a p =
   ForallT_nil
 | ForallT_cons a (Datatypes.Coq_list a) p (ForallT a p)

coq_ForallT_single :: a1 -> CRelationClasses.Coq_iffT (ForallT a1 a2) a2
coq_ForallT_single x =
  Datatypes.Coq_pair (\x0 ->
    (case x0 of {
      ForallT_nil -> (\_ -> Logic.coq_False_rect);
      ForallT_cons x1 l x2 x3 -> (\_ ->
       Logic.eq_rect_r x (\_ -> Logic.eq_rect_r Datatypes.Coq_nil (\x4 _ -> x4) l) x1 __
         x2 x3)}) __) (\x0 -> ForallT_cons x Datatypes.Coq_nil x0 ForallT_nil)

coq_ForallT_2 :: a1 -> a1 -> CRelationClasses.Coq_iffT (ForallT a1 a2)
                 (Datatypes.Coq_prod a2 a2)
coq_ForallT_2 x y =
  Datatypes.Coq_pair (\x0 ->
    (case x0 of {
      ForallT_nil -> (\_ -> Logic.coq_False_rect);
      ForallT_cons x1 l x2 x3 -> (\_ ->
       Logic.eq_rect_r x (\_ ->
         Logic.eq_rect_r (Datatypes.Coq_cons y Datatypes.Coq_nil) (\x4 x5 ->
           (case x5 of {
             ForallT_nil -> (\_ -> Logic.coq_False_rect);
             ForallT_cons x6 l0 x7 x8 -> (\_ ->
              Logic.eq_rect_r y (\_ ->
                Logic.eq_rect_r Datatypes.Coq_nil (\x9 _ -> Datatypes.Coq_pair x4 x9) l0)
                x6 __ x7 x8)}) __) l) x1 __ x2 x3)}) __) (\x0 ->
    case x0 of {
     Datatypes.Coq_pair p p0 -> ForallT_cons x (Datatypes.Coq_cons y Datatypes.Coq_nil) p
      (ForallT_cons y Datatypes.Coq_nil p0 ForallT_nil)})

coq_ForallT_map_2 :: (a1 -> a2) -> a1 -> a1 -> CRelationClasses.Coq_iffT (ForallT a2 a3)
                     (Datatypes.Coq_prod a3 a3)
coq_ForallT_map_2 f x y =
  coq_ForallT_2 (f x) (f y)

coq_ForallT_map_rev :: (a1 -> a2) -> a1 -> CRelationClasses.Coq_iffT a3 (ForallT a2 a3)
coq_ForallT_map_rev f x =
  Datatypes.Coq_pair (\hH ->
    let {x0 = f x} in (case coq_ForallT_single x0 of {
                        Datatypes.Coq_pair _ x1 -> x1}) hH) (\hH ->
    let {x0 = f x} in (case coq_ForallT_single x0 of {
                        Datatypes.Coq_pair x1 _ -> x1}) hH)

data InT a =
   InT_eq' a (Datatypes.Coq_list a)
 | InT_cons a (Datatypes.Coq_list a) (InT a)

coq_InT_rect :: a1 -> (a1 -> (Datatypes.Coq_list a1) -> () -> a2) -> (a1 ->
                (Datatypes.Coq_list a1) -> (InT a1) -> a2 -> a2) -> (Datatypes.Coq_list
                a1) -> (InT a1) -> a2
coq_InT_rect _ f f0 =
  let {
   f1 _ i =
     case i of {
      InT_eq' b l -> f b l __;
      InT_cons b l i0 -> f0 b l i0 (f1 l i0)}}
  in f1

coq_InT_eq :: a1 -> (Datatypes.Coq_list a1) -> InT a1
coq_InT_eq a l =
  InT_eq' a l

coq_InT_appL :: a1 -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (InT a1) ->
                InT a1
coq_InT_appL a x y x0 =
  coq_InT_rect a (\b l _ -> Logic.eq_rect_r a (coq_InT_eq a (Datatypes.app l y)) b)
    (\b l _ iHX0 -> InT_cons b (Datatypes.app l y) iHX0) x x0

coq_InT_appR :: a1 -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (InT a1) ->
                InT a1
coq_InT_appR _ x y x0 =
  Datatypes.list_rect x0 (\a0 x1 iHX -> InT_cons a0 (Datatypes.app x1 y) iHX) x

coq_InT_appE' :: a1 -> (Datatypes.Coq_list a1) -> (InT a1) -> (Datatypes.Coq_list 
                 a1) -> (Datatypes.Coq_list a1) -> Datatypes.Coq_sum (InT a1) (InT a1)
coq_InT_appE' a z x x0 y =
  coq_InT_rect a (\b l _ x1 y0 _ ->
    (case x1 of {
      Datatypes.Coq_nil -> (\_ ->
       Logic.eq_rect_r a (\_ ->
         Logic.eq_rect (Datatypes.Coq_cons a l) (Datatypes.Coq_inr (coq_InT_eq a l)) y0) b
         __);
      Datatypes.Coq_cons a0 x2 -> (\_ ->
       Logic.eq_rect_r a (\_ _ ->
         Logic.eq_rect_r (Datatypes.app x2 y0) (\_ ->
           Logic.eq_rect_r a0 (\_ -> Datatypes.Coq_inl (coq_InT_eq a0 x2)) a __) l __) b
         __ __)}) __) (\b l x1 iHX x2 y0 _ ->
    (case x2 of {
      Datatypes.Coq_nil -> (\_ ->
       Logic.eq_rect (Datatypes.Coq_cons b l) (Datatypes.Coq_inr (InT_cons b l x1)) y0);
      Datatypes.Coq_cons a0 x3 -> (\_ ->
       Logic.eq_rect_r (Datatypes.app x3 y0) (\_ iHX0 _ ->
         Logic.eq_rect_r a0 (\_ ->
           let {e = iHX0 x3 y0 __} in
           case e of {
            Datatypes.Coq_inl i -> Datatypes.Coq_inl (InT_cons a0 x3 i);
            Datatypes.Coq_inr i -> Datatypes.Coq_inr i}) b __) l x1 iHX __)}) __) z x x0 y
    __

coq_InT_appE :: a1 -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (InT a1) ->
                Datatypes.Coq_sum (InT a1) (InT a1)
coq_InT_appE a x y x0 =
  coq_InT_appE' a (Datatypes.app x y) x0 x y

coq_InT_nilE' :: a1 -> (Datatypes.Coq_list a1) -> (InT a1) -> a2
coq_InT_nilE' a z x =
  coq_InT_rect a (\_ _ _ _ -> Logic.coq_False_rect) (\_ _ _ _ _ -> Logic.coq_False_rect) z
    x __

coq_InT_nilE :: a1 -> (InT a1) -> a2
coq_InT_nilE a x =
  coq_InT_nilE' a Datatypes.Coq_nil x

coq_InT_split :: a1 -> (Datatypes.Coq_list a1) -> (InT a1) -> Specif.Coq_sigT
                 (Datatypes.Coq_list a1) (Specif.Coq_sigT (Datatypes.Coq_list a1) ())
coq_InT_split x l x0 =
  coq_InT_rect x (\_ l0 _ -> Specif.Coq_existT Datatypes.Coq_nil (Specif.Coq_existT l0
    __)) (\b l0 x1 iHX ->
    case iHX of {
     Specif.Coq_existT x2 s ->
      case s of {
       Specif.Coq_existT x3 _ ->
        Logic.eq_rect_r (Datatypes.app x2 (Datatypes.Coq_cons x x3)) (\_ ->
          Specif.Coq_existT (Datatypes.Coq_cons b x2) (Specif.Coq_existT x3 __)) l0 x1}})
    l x0

coq_InT_map :: (a1 -> a2) -> (Datatypes.Coq_list a1) -> a1 -> (InT a1) -> InT a2
coq_InT_map f l x x0 =
  coq_InT_rect x (\b l0 _ -> Logic.eq_rect_r x (coq_InT_eq (f x) (List.map f l0)) b)
    (\b l0 _ iHX -> InT_cons (f b) (List.map f l0) iHX) l x0

coq_InT_mapE :: (a1 -> a2) -> (Datatypes.Coq_list a1) -> a2 -> (InT a2) -> Specif.Coq_sigT
                a1 (Datatypes.Coq_prod () (InT a1))
coq_InT_mapE f l y x =
  Datatypes.list_rect (\x0 -> coq_InT_nilE y x0) (\a l0 iHl x0 ->
    (case x0 of {
      InT_eq' b l1 -> (\_ ->
       Logic.eq_rect_r (f a) (\_ ->
         Logic.eq_rect_r (List.map f l0) (\_ ->
           Logic.eq_rect (f a) (\_ _ -> Specif.Coq_existT a (Datatypes.Coq_pair __
             (coq_InT_eq a l0))) y x0 iHl) l1) b __ __);
      InT_cons b l1 x1 -> (\_ ->
       Logic.eq_rect_r (f a) (\_ ->
         Logic.eq_rect_r (List.map f l0) (\x2 ->
           let {x3 = iHl x2} in
           case x3 of {
            Specif.Coq_existT x4 x5 ->
             case x5 of {
              Datatypes.Coq_pair _ x6 -> Specif.Coq_existT x4
               (Logic.eq_rect (f x4) (\_ _ -> Datatypes.Coq_pair __ (InT_cons a l0 x6)) y
                 x0 iHl)}}) l1) b __ x1)}) __) l x

coq_InT_map_iffT :: (a1 -> a2) -> (Datatypes.Coq_list a1) -> a2 ->
                    CRelationClasses.Coq_iffT (InT a2)
                    (Specif.Coq_sigT a1 (Datatypes.Coq_prod () (InT a1)))
coq_InT_map_iffT f l y =
  Datatypes.Coq_pair (coq_InT_mapE f l y) (\x ->
    case x of {
     Specif.Coq_existT x0 x1 ->
      case x1 of {
       Datatypes.Coq_pair _ x2 -> Logic.eq_rect (f x0) (coq_InT_map f l x0 x2) y}})

coq_ForallT_forall :: (Datatypes.Coq_list a1) -> CRelationClasses.Coq_iffT (ForallT a1 a2)
                      (a1 -> (InT a1) -> a2)
coq_ForallT_forall l =
  Datatypes.list_rect (Datatypes.Coq_pair (\_ -> coq_InT_nilE) (\_ -> ForallT_nil))
    (\a l0 iHl -> Datatypes.Coq_pair (\x x0 x1 ->
    case iHl of {
     Datatypes.Coq_pair p _ ->
      (case x of {
        ForallT_nil -> (\_ -> Logic.coq_False_rect);
        ForallT_cons x2 l1 x3 x4 -> (\_ ->
         Logic.eq_rect_r a (\_ ->
           Logic.eq_rect_r l0 (\x5 x6 ->
             (case x1 of {
               InT_eq' b l2 -> (\_ ->
                Logic.eq_rect_r a (\_ ->
                  Logic.eq_rect_r l0 (\_ ->
                    Logic.eq_rect_r x0 (\_ _ x7 _ -> x7) a x x1 x5 __) l2) b __ __);
               InT_cons b l2 x7 -> (\_ ->
                Logic.eq_rect_r a (\_ -> Logic.eq_rect_r l0 (\x8 -> p x6 x0 x8) l2) b __
                  x7)}) __) l1) x2 __ x3 x4)}) __}) (\x ->
    case iHl of {
     Datatypes.Coq_pair _ f -> ForallT_cons a l0 (x a (coq_InT_eq a l0))
      (f (\x0 x1 -> x x0 (InT_cons a l0 x1)))})) l

coq_ForallTD_forall :: (Datatypes.Coq_list a1) -> (ForallT a1 a2) -> a1 -> (InT a1) -> a2
coq_ForallTD_forall x =
  iffT_D1 (coq_ForallT_forall x)

want_prod_under_universal4 :: (a1 -> a2 -> Datatypes.Coq_prod
                              (Datatypes.Coq_prod (Datatypes.Coq_prod a3 a4) a5) a6) ->
                              Datatypes.Coq_prod
                              (Datatypes.Coq_prod
                              (Datatypes.Coq_prod (a1 -> a2 -> a3) (a1 -> a2 -> a4))
                              (a1 -> a2 -> a5)) (a1 -> a2 -> a6)
want_prod_under_universal4 x =
  Datatypes.Coq_pair (Datatypes.Coq_pair (Datatypes.Coq_pair (\y x0 ->
    let {x1 = x y} in
    let {x2 = x1 x0} in
    Datatypes.prod_rect (\a _ ->
      Datatypes.prod_rect (\a0 _ -> Datatypes.prod_rect (\a1 _ -> a1) a0) a) x2) (\y x0 ->
    let {x1 = x y} in
    let {x2 = x1 x0} in
    Datatypes.prod_rect (\a _ ->
      Datatypes.prod_rect (\a0 _ -> Datatypes.prod_rect (\_ b1 -> b1) a0) a) x2))
    (\y x0 ->
    let {x1 = x y} in
    let {x2 = x1 x0} in
    Datatypes.prod_rect (\a _ -> Datatypes.prod_rect (\_ b0 -> b0) a) x2)) (\y x0 ->
    let {x1 = x y} in let {x2 = x1 x0} in Datatypes.prod_rect (\_ b -> b) x2)

prod_nat_split :: ((Datatypes.Coq_prod Datatypes.Coq_nat Datatypes.Coq_nat) -> a1) ->
                  Datatypes.Coq_nat -> Datatypes.Coq_nat -> a1
prod_nat_split x n m =
  x (Datatypes.Coq_pair n m)

