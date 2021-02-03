module Structural_equivalence where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Gen_tacs
import qualified LntT

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_struct_equiv_str v =
   Coq_se_nil2
 | Coq_se_step2 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) LntT.Coq_dir 
 (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list
                                                                         (Datatypes.Coq_prod
                                                                         (Datatypes.Coq_prod
                                                                         (Datatypes.Coq_list
                                                                         (LntT.PropF v))
                                                                         (Datatypes.Coq_list
                                                                         (LntT.PropF v)))
                                                                         LntT.Coq_dir)) (Datatypes.Coq_list
                                                                                        (Datatypes.Coq_prod
                                                                                        (Datatypes.Coq_prod
                                                                                        (Datatypes.Coq_list
                                                                                        (LntT.PropF
                                                                                        v))
                                                                                        (Datatypes.Coq_list
                                                                                        (LntT.PropF
                                                                                        v)))
                                                                                        LntT.Coq_dir)) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod
 (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF v)) (Datatypes.Coq_list (LntT.PropF v)))
 LntT.Coq_dir)) (Datatypes.Coq_list
                (Datatypes.Coq_prod
                (Datatypes.Coq_prod (Datatypes.Coq_list (LntT.PropF v))
                (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (Coq_struct_equiv_str v)

data Coq_struct_equiv_weak v =
   Coq_se_wk2_extL (Datatypes.Coq_list
                   (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                   LntT.Coq_dir)) (Datatypes.Coq_list
                                  (Datatypes.Coq_prod
                                  (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                                  LntT.Coq_dir)) (Datatypes.Coq_list
                                                 (Datatypes.Coq_prod
                                                 (Gen_tacs.Coq_rel
                                                 (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (Coq_struct_equiv_str
                                                                                           v)
 | Coq_se_wk2_extR (Datatypes.Coq_list
                   (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                   LntT.Coq_dir)) (Datatypes.Coq_list
                                  (Datatypes.Coq_prod
                                  (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v)))
                                  LntT.Coq_dir)) (Datatypes.Coq_list
                                                 (Datatypes.Coq_prod
                                                 (Gen_tacs.Coq_rel
                                                 (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) 
 (Datatypes.Coq_list
 (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF v))) LntT.Coq_dir)) (Coq_struct_equiv_str
                                                                                           v)

struct_equiv_str_weak :: (Datatypes.Coq_list
                         (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                         LntT.Coq_dir)) -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                         LntT.Coq_dir)) -> (Coq_struct_equiv_str a1) -> Coq_struct_equiv_weak 
                         a1
struct_equiv_str_weak g1 g2 h =
  let {h0 = Coq_se_wk2_extL g1 g2 Datatypes.Coq_nil (Datatypes.app g1 Datatypes.Coq_nil) h} in
  Logic.eq_rect (Datatypes.app g1 Datatypes.Coq_nil) h0 g1

struct_equiv_str_refl :: (Datatypes.Coq_list
                         (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                         LntT.Coq_dir)) -> Coq_struct_equiv_str a1
struct_equiv_str_refl g =
  Datatypes.list_rec Coq_se_nil2 (\a g0 iHG ->
    case a of {
     Datatypes.Coq_pair r x ->
      (case r of {
        Datatypes.Coq_pair _UU0393_ _UU0394_ -> (\d -> Coq_se_step2 _UU0393_ _UU0394_ d _UU0393_
         _UU0394_ g0 g0 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
         _UU0394_) d) g0) (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_
         _UU0394_) d) g0) iHG)}) x}) g

struct_equiv_str_comm :: (Datatypes.Coq_list
                         (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                         LntT.Coq_dir)) -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                         LntT.Coq_dir)) -> (Coq_struct_equiv_str a1) -> Coq_struct_equiv_str 
                         a1
struct_equiv_str_comm a =
  Datatypes.list_rect (\b hs ->
    (case hs of {
      Coq_se_nil2 -> (\_ _ -> Logic.eq_rec Datatypes.Coq_nil Coq_se_nil2 b);
      Coq_se_step2 _ _ _ _ _ _ _ ns3 ns4 h1 -> (\_ _ ->
       Logic.eq_rec_r Datatypes.Coq_nil (\_ -> Logic.eq_rec_r b (\_ _ _ -> Logic.coq_False_rec) ns4)
         ns3 __ __ __ h1)}) __ __) (\a0 a1 iHA b hs ->
    (case hs of {
      Coq_se_nil2 -> (\_ _ -> Logic.coq_False_rec __);
      Coq_se_step2 _UU0393_1 _UU0394_1 d _UU0393_2 _UU0394_2 ns1 ns2 ns3 ns4 h1 -> (\_ _ ->
       Logic.eq_rec_r (Datatypes.Coq_cons a0 a1) (\_ ->
         Logic.eq_rec_r b (\_ _ h2 ->
           Logic.eq_rec_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_2
             _UU0394_2) d) ns2) (\hs0 _ ->
             Logic.eq_rec_r (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_1 _UU0394_1) d) (\_ ->
               Logic.eq_rec_r ns1
                 (Logic.eq_rec_r (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_1 _UU0394_1) d)
                   (\hs1 _ ->
                   Logic.eq_rect_r ns1 (\iHA0 _ _ -> Coq_se_step2 _UU0393_2 _UU0394_2 d _UU0393_1
                     _UU0394_1 ns2 ns1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                     _UU0393_2 _UU0394_2) d) ns2) (Datatypes.Coq_cons (Datatypes.Coq_pair
                     (Datatypes.Coq_pair _UU0393_1 _UU0394_1) d) ns1) (iHA0 ns2 h2)) a1 iHA hs1 __)
                   a0 hs0 __) a1) a0 __) b hs __) ns4) ns3 __ __ __ h1)}) __ __) a

struct_equiv_weak_refl :: (Datatypes.Coq_list
                          (Datatypes.Coq_prod (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1)))
                          LntT.Coq_dir)) -> Coq_struct_equiv_weak a1
struct_equiv_weak_refl g =
  Coq_se_wk2_extL g g Datatypes.Coq_nil g (struct_equiv_str_refl g)

struct_equiv_str_app_revR :: (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                             -> (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                             -> (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                             -> (Datatypes.Coq_list
                             (Datatypes.Coq_prod
                             (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                             -> (Coq_struct_equiv_str a1) -> Datatypes.Coq_prod
                             (Coq_struct_equiv_str a1) (Coq_struct_equiv_str a1)
struct_equiv_str_app_revR a1 a2 b1 b2 x =
  Datatypes.list_rect (\_ b3 _ _ hs ->
    (case b3 of {
      Datatypes.Coq_nil -> (\_ hs0 -> Datatypes.Coq_pair Coq_se_nil2 hs0);
      Datatypes.Coq_cons _ _ -> (\_ _ -> Logic.coq_False_rec)}) __ hs) (\a a3 iHA1 a4 b3 b4 _ hs ->
    (case b3 of {
      Datatypes.Coq_nil -> (\_ _ -> Logic.coq_False_rec);
      Datatypes.Coq_cons p b5 -> (\_ hs0 ->
       Logic.eq_rec (Datatypes.length a3)
         ((case hs0 of {
            Coq_se_nil2 -> (\_ _ -> Logic.coq_False_rec __);
            Coq_se_step2 _UU0393_1 _UU0394_1 d _UU0393_2 _UU0394_2 ns1 ns2 ns3 ns4 h2 -> (\_ _ ->
             Logic.eq_rec_r (Datatypes.Coq_cons a (Datatypes.app a3 a4)) (\_ ->
               Logic.eq_rec_r (Datatypes.Coq_cons p (Datatypes.app b5 b4)) (\_ _ h3 ->
                 Logic.eq_rec_r (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_2 _UU0394_2) d)
                   (\_ ->
                   Logic.eq_rec (Datatypes.app b5 b4)
                     (Logic.eq_rec_r (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_2 _UU0394_2) d)
                       (\hs1 _ ->
                       Logic.eq_rec (Datatypes.app b5 b4) (\_ h4 ->
                         Logic.eq_rec_r (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_1 _UU0394_1)
                           d) (\_ ->
                           Logic.eq_rec (Datatypes.app a3 a4)
                             (Logic.eq_rec_r (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_1
                               _UU0394_1) d) (\_ _ ->
                               Logic.eq_rec (Datatypes.app a3 a4) (\_ h5 ->
                                 let {p0 = iHA1 a4 b5 b4 __ h5} in
                                 case p0 of {
                                  Datatypes.Coq_pair s s0 -> Datatypes.Coq_pair (Coq_se_step2
                                   _UU0393_1 _UU0394_1 d _UU0393_2 _UU0394_2 a3 b5
                                   (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                                   _UU0393_1 _UU0394_1) d) a3) (Datatypes.Coq_cons
                                   (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_2 _UU0394_2) d)
                                   b5) s) s0}) ns1 __ h4) a hs1 __) ns1) a __) ns2 __ h3) p hs0 __)
                     ns2) p __) ns4) ns3 __ __ __ h2)}) __ __) (Datatypes.length b5))}) __ hs) a1 a2
    b1 b2 __ x

struct_equiv_str_app_single :: (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                               -> (Datatypes.Coq_list
                               (Datatypes.Coq_prod
                               (Gen_tacs.Coq_rel (Datatypes.Coq_list (LntT.PropF a1))) LntT.Coq_dir))
                               -> (Datatypes.Coq_list (LntT.PropF a1)) -> (Datatypes.Coq_list
                               (LntT.PropF a1)) -> (Datatypes.Coq_list (LntT.PropF a1)) ->
                               (Datatypes.Coq_list (LntT.PropF a1)) -> LntT.Coq_dir ->
                               (Coq_struct_equiv_str a1) -> Coq_struct_equiv_str a1
struct_equiv_str_app_single h1 =
  Datatypes.list_rect (\h2 a1 a2 b1 b2 d hstr ->
    (case hstr of {
      Coq_se_nil2 -> (\_ _ ->
       Logic.eq_rec Datatypes.Coq_nil (Coq_se_step2 a1 a2 d b1 b2 Datatypes.Coq_nil Datatypes.Coq_nil
         (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair a1 a2) d) Datatypes.Coq_nil)
         (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair b1 b2) d) Datatypes.Coq_nil)
         Coq_se_nil2) h2);
      Coq_se_step2 _ _ _ _ _ _ _ ns3 ns4 h3 -> (\_ _ ->
       Logic.eq_rec_r Datatypes.Coq_nil (\_ -> Logic.eq_rec_r h2 (\_ _ _ -> Logic.coq_False_rec) ns4)
         ns3 __ __ __ h3)}) __ __) (\a h2 iHlist h3 a1 a2 b1 b2 d hstr ->
    (case hstr of {
      Coq_se_nil2 -> (\_ _ -> Logic.coq_False_rec __);
      Coq_se_step2 _UU0393_1 _UU0394_1 d0 _UU0393_2 _UU0394_2 ns1 ns2 ns3 ns4 h4 -> (\_ _ ->
       Logic.eq_rec_r (Datatypes.Coq_cons a h2) (\_ ->
         Logic.eq_rec_r h3 (\_ _ h5 ->
           Logic.eq_rec_r (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_1 _UU0394_1) d0) (\_ ->
             Logic.eq_rec_r ns1
               (Logic.eq_rec_r (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_2
                 _UU0394_2) d0) ns2) (\hstr0 _ ->
                 Logic.eq_rec_r (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_1 _UU0394_1) d0)
                   (\hstr1 _ ->
                   Logic.eq_rect_r ns1 (\iHlist0 _ _ -> Coq_se_step2 _UU0393_1 _UU0394_1 d0 _UU0393_2
                     _UU0394_2
                     (Datatypes.app ns1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                       a1 a2) d) Datatypes.Coq_nil))
                     (Datatypes.app ns2 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                       b1 b2) d) Datatypes.Coq_nil)) (Datatypes.Coq_cons (Datatypes.Coq_pair
                     (Datatypes.Coq_pair _UU0393_1 _UU0394_1) d0)
                     (Datatypes.app ns1 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                       a1 a2) d) Datatypes.Coq_nil))) (Datatypes.Coq_cons (Datatypes.Coq_pair
                     (Datatypes.Coq_pair _UU0393_2 _UU0394_2) d0)
                     (Datatypes.app ns2 (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_pair
                       b1 b2) d) Datatypes.Coq_nil))) (iHlist0 ns2 a1 a2 b1 b2 d h5)) h2 iHlist hstr1
                     __) a hstr0 __) h3 hstr __) h2) a __) ns4) ns3 __ __ __ h4)}) __ __) h1

