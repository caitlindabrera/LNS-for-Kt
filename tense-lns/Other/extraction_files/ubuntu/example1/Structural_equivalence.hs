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
 | Coq_se_step2 (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) LntT.Coq_dir (([]) (LntT.PropF v)) 
 (([]) (LntT.PropF v)) (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) (([])
                                                                             ((,)
                                                                             ((,)
                                                                             (([]) (LntT.PropF v))
                                                                             (([]) (LntT.PropF v)))
                                                                             LntT.Coq_dir)) (([])
                                                                                            ((,)
                                                                                            ((,)
                                                                                            (([])
                                                                                            (LntT.PropF
                                                                                            v))
                                                                                            (([])
                                                                                            (LntT.PropF
                                                                                            v)))
                                                                                            LntT.Coq_dir)) 
 (Coq_struct_equiv_str v)

data Coq_struct_equiv_weak v =
   Coq_se_wk2_extL (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir)) (([])
                                                                                      ((,)
                                                                                      (Gen_tacs.Coq_rel
                                                                                      (([])
                                                                                      (LntT.PropF v)))
                                                                                      LntT.Coq_dir)) 
 (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir)) (([])
                                                                    ((,)
                                                                    (Gen_tacs.Coq_rel
                                                                    (([]) (LntT.PropF v)))
                                                                    LntT.Coq_dir)) (Coq_struct_equiv_str
                                                                                   v)
 | Coq_se_wk2_extR (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir)) (([])
                                                                                      ((,)
                                                                                      (Gen_tacs.Coq_rel
                                                                                      (([])
                                                                                      (LntT.PropF v)))
                                                                                      LntT.Coq_dir)) 
 (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir)) (([])
                                                                    ((,)
                                                                    (Gen_tacs.Coq_rel
                                                                    (([]) (LntT.PropF v)))
                                                                    LntT.Coq_dir)) (Coq_struct_equiv_str
                                                                                   v)

struct_equiv_str_weak :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) -> (([])
                         ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Coq_struct_equiv_str a1) -> Coq_struct_equiv_weak a1
struct_equiv_str_weak g1 g2 h =
  let {h0 = Coq_se_wk2_extL g1 g2 ([]) (Datatypes.app g1 ([])) h} in
  Logic.eq_rect (Datatypes.app g1 ([])) h0 g1

struct_equiv_str_refl :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                         Coq_struct_equiv_str a1
struct_equiv_str_refl g =
  Datatypes.list_rec Coq_se_nil2 (\a g0 iHG ->
    case a of {
     (,) r x ->
      case r of {
       (,) _UU0393_ _UU0394_ -> Coq_se_step2 _UU0393_ _UU0394_ x _UU0393_ _UU0394_ g0 g0 ((:) ((,)
        ((,) _UU0393_ _UU0394_) x) g0) ((:) ((,) ((,) _UU0393_ _UU0394_) x) g0) iHG}}) g

struct_equiv_str_comm :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) -> (([])
                         ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                         (Coq_struct_equiv_str a1) -> Coq_struct_equiv_str a1
struct_equiv_str_comm a =
  Datatypes.list_rect (\b hs ->
    case hs of {
     Coq_se_nil2 -> Logic.eq_rec ([]) Coq_se_nil2 b;
     Coq_se_step2 _ _ _ _ _ _ _ ns3 ns4 h1 ->
      Logic.eq_rec_r ([]) (\_ -> Logic.eq_rec_r b (\_ _ _ -> Logic.coq_False_rec) ns4) ns3 __ __ __
        h1}) (\a0 a1 iHA b hs ->
    case hs of {
     Coq_se_nil2 -> Logic.coq_False_rec __;
     Coq_se_step2 _UU0393_1 _UU0394_1 d _UU0393_2 _UU0394_2 ns1 ns2 ns3 ns4 h1 ->
      Logic.eq_rec_r ((:) a0 a1) (\_ ->
        Logic.eq_rec_r b (\_ _ h2 ->
          Logic.eq_rec_r ((:) ((,) ((,) _UU0393_2 _UU0394_2) d) ns2) (\hs0 _ ->
            Logic.eq_rec_r ((,) ((,) _UU0393_1 _UU0394_1) d) (\_ ->
              Logic.eq_rec_r ns1
                (Logic.eq_rec_r ((,) ((,) _UU0393_1 _UU0394_1) d) (\hs1 _ ->
                  Logic.eq_rect_r ns1 (\iHA0 _ _ -> Coq_se_step2 _UU0393_2 _UU0394_2 d _UU0393_1
                    _UU0394_1 ns2 ns1 ((:) ((,) ((,) _UU0393_2 _UU0394_2) d) ns2) ((:) ((,) ((,)
                    _UU0393_1 _UU0394_1) d) ns1) (iHA0 ns2 h2)) a1 iHA hs1 __) a0 hs0 __) a1) a0 __)
            b hs __) ns4) ns3 __ __ __ h1}) a

struct_equiv_weak_refl :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                          Coq_struct_equiv_weak a1
struct_equiv_weak_refl g =
  Coq_se_wk2_extL g g ([]) g (struct_equiv_str_refl g)

struct_equiv_str_app_revR :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                             (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                             (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                             (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                             (Coq_struct_equiv_str a1) -> (,) (Coq_struct_equiv_str a1)
                             (Coq_struct_equiv_str a1)
struct_equiv_str_app_revR a1 a2 b1 b2 x =
  Datatypes.list_rect (\_ b3 _ _ hs ->
    case b3 of {
     ([]) -> (,) Coq_se_nil2 hs;
     (:) _ _ -> Logic.coq_False_rec}) (\a a3 iHA1 a4 b3 b4 _ hs ->
    case b3 of {
     ([]) -> Logic.coq_False_rec;
     (:) p b5 ->
      Logic.eq_rec (Datatypes.length a3)
        (case hs of {
          Coq_se_nil2 -> Logic.coq_False_rec __;
          Coq_se_step2 _UU0393_1 _UU0394_1 d _UU0393_2 _UU0394_2 ns1 ns2 ns3 ns4 h2 ->
           Logic.eq_rec_r ((:) a (Datatypes.app a3 a4)) (\_ ->
             Logic.eq_rec_r ((:) p (Datatypes.app b5 b4)) (\_ _ h3 ->
               Logic.eq_rec_r ((,) ((,) _UU0393_2 _UU0394_2) d) (\_ ->
                 Logic.eq_rec (Datatypes.app b5 b4)
                   (Logic.eq_rec_r ((,) ((,) _UU0393_2 _UU0394_2) d) (\hs0 _ ->
                     Logic.eq_rec (Datatypes.app b5 b4) (\_ h4 ->
                       Logic.eq_rec_r ((,) ((,) _UU0393_1 _UU0394_1) d) (\_ ->
                         Logic.eq_rec (Datatypes.app a3 a4)
                           (Logic.eq_rec_r ((,) ((,) _UU0393_1 _UU0394_1) d) (\_ _ ->
                             Logic.eq_rec (Datatypes.app a3 a4) (\_ h5 ->
                               let {p0 = iHA1 a4 b5 b4 __ h5} in
                               case p0 of {
                                (,) s s0 -> (,) (Coq_se_step2 _UU0393_1 _UU0394_1 d _UU0393_2
                                 _UU0394_2 a3 b5 ((:) ((,) ((,) _UU0393_1 _UU0394_1) d) a3) ((:) ((,)
                                 ((,) _UU0393_2 _UU0394_2) d) b5) s) s0}) ns1 __ h4) a hs0 __) ns1) a
                         __) ns2 __ h3) p hs __) ns2) p __) ns4) ns3 __ __ __ h2})
        (Datatypes.length b5)}) a1 a2 b1 b2 __ x

struct_equiv_str_app_single :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                               (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                               (([]) (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                               (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> LntT.Coq_dir ->
                               (Coq_struct_equiv_str a1) -> Coq_struct_equiv_str a1
struct_equiv_str_app_single h1 =
  Datatypes.list_rect (\h2 a1 a2 b1 b2 d hstr ->
    case hstr of {
     Coq_se_nil2 ->
      Logic.eq_rec ([]) (Coq_se_step2 a1 a2 d b1 b2 ([]) ([]) ((:) ((,) ((,) a1 a2) d) ([])) ((:)
        ((,) ((,) b1 b2) d) ([])) Coq_se_nil2) h2;
     Coq_se_step2 _ _ _ _ _ _ _ ns3 ns4 h3 ->
      Logic.eq_rec_r ([]) (\_ -> Logic.eq_rec_r h2 (\_ _ _ -> Logic.coq_False_rec) ns4) ns3 __ __ __
        h3}) (\a h2 iHlist h3 a1 a2 b1 b2 d hstr ->
    case hstr of {
     Coq_se_nil2 -> Logic.coq_False_rec __;
     Coq_se_step2 _UU0393_1 _UU0394_1 d0 _UU0393_2 _UU0394_2 ns1 ns2 ns3 ns4 h4 ->
      Logic.eq_rec_r ((:) a h2) (\_ ->
        Logic.eq_rec_r h3 (\_ _ h5 ->
          Logic.eq_rec_r ((,) ((,) _UU0393_1 _UU0394_1) d0) (\_ ->
            Logic.eq_rec_r ns1
              (Logic.eq_rec_r ((:) ((,) ((,) _UU0393_2 _UU0394_2) d0) ns2) (\hstr0 _ ->
                Logic.eq_rec_r ((,) ((,) _UU0393_1 _UU0394_1) d0) (\hstr1 _ ->
                  Logic.eq_rect_r ns1 (\iHlist0 _ _ -> Coq_se_step2 _UU0393_1 _UU0394_1 d0 _UU0393_2
                    _UU0394_2 (Datatypes.app ns1 ((:) ((,) ((,) a1 a2) d) ([])))
                    (Datatypes.app ns2 ((:) ((,) ((,) b1 b2) d) ([]))) ((:) ((,) ((,) _UU0393_1
                    _UU0394_1) d0) (Datatypes.app ns1 ((:) ((,) ((,) a1 a2) d) ([])))) ((:) ((,) ((,)
                    _UU0393_2 _UU0394_2) d0) (Datatypes.app ns2 ((:) ((,) ((,) b1 b2) d) ([]))))
                    (iHlist0 ns2 a1 a2 b1 b2 d h5)) h2 iHlist hstr1 __) a hstr0 __) h3 hstr __) h2) a
            __) ns4) ns3 __ __ __ h4}) h1

