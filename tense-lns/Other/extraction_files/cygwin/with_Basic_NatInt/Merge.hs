module Merge where

import qualified Prelude
import qualified Datatypes
import qualified List_lemmasT
import qualified Logic
import qualified Specif
import qualified ContractedT
import qualified Gen_tacs
import qualified LntT
import qualified Structural_equivalence
import qualified WeakenedT

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_merge v =
   Coq_merge_nilL (([])
                  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir)) (([])
                                                                    ((,)
                                                                    (Gen_tacs.Coq_rel
                                                                    (([])
                                                                    (LntT.PropF
                                                                    v)))
                                                                    LntT.Coq_dir))
 | Coq_merge_nilR (([])
                  ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF v))) LntT.Coq_dir)) (([])
                                                                    ((,)
                                                                    (Gen_tacs.Coq_rel
                                                                    (([])
                                                                    (LntT.PropF
                                                                    v)))
                                                                    LntT.Coq_dir))
 | Coq_merge_step (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) (([])
                                                              (LntT.PropF v)) 
 (([]) (LntT.PropF v)) LntT.Coq_dir (([])
                                    ((,)
                                    (Gen_tacs.Coq_rel (([]) (LntT.PropF v)))
                                    LntT.Coq_dir)) (([])
                                                   ((,)
                                                   (Gen_tacs.Coq_rel
                                                   (([]) (LntT.PropF v)))
                                                   LntT.Coq_dir)) (([])
                                                                  ((,)
                                                                  (Gen_tacs.Coq_rel
                                                                  (([])
                                                                  (LntT.PropF
                                                                  v)))
                                                                  LntT.Coq_dir)) 
 (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir) 
 ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir) 
 ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir) 
 (Coq_merge v)

merge_ex_str :: (([])
                ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                -> (([])
                ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                -> (Structural_equivalence.Coq_struct_equiv_str a1) ->
                Specif.Coq_sigT
                (([])
                ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                (Coq_merge a1)
merge_ex_str g1 =
  Datatypes.list_rect (\g2 hs ->
    case hs of {
     Structural_equivalence.Coq_se_nil2 ->
      Logic.eq_rect ([]) (Specif.Coq_existT ([]) (Coq_merge_nilL ([]) ([])
        ([]))) g2;
     Structural_equivalence.Coq_se_step2 _ _ _ _ _ _ _ ns3 ns4 h1 ->
      Logic.eq_rect_r ([]) (\_ ->
        Logic.eq_rect_r g2 (\_ _ _ -> Logic.coq_False_rect) ns4) ns3 __ __ __
        h1}) (\a g2 iHG1 g3 hs ->
    case hs of {
     Structural_equivalence.Coq_se_nil2 -> Logic.coq_False_rect __;
     Structural_equivalence.Coq_se_step2 _UU0393_1 _UU0394_1 d _UU0393_2
      _UU0394_2 ns1 ns2 ns3 ns4 h1 ->
      Logic.eq_rect_r ((:) a g2) (\_ ->
        Logic.eq_rect_r g3 (\_ _ h2 ->
          Logic.eq_rect_r ((,) ((,) _UU0393_1 _UU0394_1) d) (\_ ->
            Logic.eq_rect_r ns1
              (Logic.eq_rect_r ((:) ((,) ((,) _UU0393_2 _UU0394_2) d) ns2)
                (\hs0 _ ->
                Logic.eq_rect_r ((,) ((,) _UU0393_1 _UU0394_1) d) (\hs1 _ ->
                  Logic.eq_rect_r ns1 (\iHG2 _ _ ->
                    let {h3 = iHG2 ns2 h2} in
                    case h3 of {
                     Specif.Coq_existT g4 h4 -> Specif.Coq_existT ((:) ((,)
                      ((,) (Datatypes.app _UU0393_1 _UU0393_2)
                      (Datatypes.app _UU0394_1 _UU0394_2)) d) g4)
                      (Coq_merge_step _UU0393_1 _UU0394_1 _UU0393_2 _UU0394_2
                      d ns1 ns2 g4 ((:) ((,) ((,) _UU0393_1 _UU0394_1) d) ns1)
                      ((:) ((,) ((,) _UU0393_2 _UU0394_2) d) ns2) ((:) ((,)
                      ((,) (Datatypes.app _UU0393_1 _UU0393_2)
                      (Datatypes.app _UU0394_1 _UU0394_2)) d) g4) ((,) ((,)
                      _UU0393_1 _UU0394_1) d) ((,) ((,) _UU0393_2 _UU0394_2)
                      d) ((,) ((,) (Datatypes.app _UU0393_1 _UU0393_2)
                      (Datatypes.app _UU0394_1 _UU0394_2)) d) h4)}) g2 iHG1
                    hs1 __) a hs0 __) g3 hs __) g2) a __) ns4) ns3 __ __ __ h1})
    g1

merge_appLR :: (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               -> (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               -> (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               -> (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               -> (Coq_merge a1) -> Coq_merge a1
merge_appLR g1 g2 g3 g x =
  Datatypes.list_rect (\g4 g5 g0 hm _ ->
    case g4 of {
     ([]) ->
      case hm of {
       Coq_merge_nilL ns1 ns2 ns3 ->
        Logic.eq_rect_r ([]) (\_ ->
          Logic.eq_rect_r ([]) (\_ ->
            Logic.eq_rect_r g5 (\_ _ ->
              Logic.eq_rect_r ([]) (\_ _ -> Coq_merge_nilR g0 ([]) g0) g5 hm
                __) ns3) ns2) ns1 __ __ __ __;
       Coq_merge_nilR ns1 ns2 ns3 ->
        Logic.eq_rect_r ([]) (\_ ->
          Logic.eq_rect_r ([]) (\_ ->
            Logic.eq_rect_r g5 (\_ _ ->
              Logic.eq_rect_r ([]) (\_ _ -> Coq_merge_nilR g0 ([]) g0) g5 hm
                __) ns3) ns2) ns1 __ __ __ __;
       Coq_merge_step _ _ _ _ _ _ _ _ ns4 ns5 ns6 _ _ _ x0 ->
        Logic.eq_rect_r ([]) (\_ ->
          Logic.eq_rect_r ([]) (\_ ->
            Logic.eq_rect_r g5 (\_ _ _ _ _ _ _ -> Logic.coq_False_rect) ns6)
            ns5) ns4 __ __ __ __ __ x0 __ __ __};
     (:) _ _ -> Logic.coq_False_rect}) (\a g4 iHG1 g5 g6 g0 hm _ ->
    case g5 of {
     ([]) -> Logic.coq_False_rect;
     (:) p g7 ->
      Logic.eq_rect (Datatypes.length g4)
        (case g6 of {
          ([]) ->
           case hm of {
            Coq_merge_nilL ns1 ns2 ns3 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ([]) (\_ _ -> Logic.coq_False_rect) ns3) ns2)
               ns1 __ __ __ __;
            Coq_merge_nilR ns1 ns2 ns3 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ([]) (\_ _ -> Logic.coq_False_rect) ns3) ns2)
               ns1 __ __ __ __;
            Coq_merge_step _ _ _ _ _ _ _ _ ns4 ns5 ns6 _ _ _ x0 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ([]) (\_ _ _ _ _ _ _ -> Logic.coq_False_rect)
                   ns6) ns5) ns4 __ __ __ __ __ x0 __ __ __};
          (:) p0 g8 ->
           case hm of {
            Coq_merge_nilL ns1 ns2 ns3 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ((:) p0 g8) (\_ _ -> Logic.coq_False_rect)
                   ns3) ns2) ns1 __ __ __ __;
            Coq_merge_nilR ns1 ns2 ns3 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ((:) p0 g8) (\_ _ -> Logic.coq_False_rect)
                   ns3) ns2) ns1 __ __ __ __;
            Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns1 ns2 ns3
             ns4 ns5 ns6 seq1 seq2 seq3 x0 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ((:) p0 g8) (\_ _ _ x1 _ _ _ ->
                   Logic.eq_rect_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                     Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                       Logic.eq_rect_r ((,) ((,)
                         (Datatypes.app _UU0393_ _UU03a3_)
                         (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                         Logic.eq_rect_r ((,) ((,)
                           (Datatypes.app _UU0393_ _UU03a3_)
                           (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                           Logic.eq_rect_r ns3
                             (Logic.eq_rect_r ((,) ((,)
                               (Datatypes.app _UU0393_ _UU03a3_)
                               (Datatypes.app _UU0394_ _UU03a0_)) d)
                               (\hm0 _ ->
                               Logic.eq_rect_r ns3 (\hm1 _ ->
                                 Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_)
                                   d) (\_ ->
                                   Logic.eq_rect_r ns2
                                     (Logic.eq_rect_r ((,) ((,) _UU03a3_
                                       _UU03a0_) d) (\hm2 _ ->
                                       Logic.eq_rect_r ns2 (\hm3 _ _ _ ->
                                         Logic.eq_rect_r ((,) ((,) _UU0393_
                                           _UU0394_) d) (\_ ->
                                           Logic.eq_rect_r ns1
                                             (Logic.eq_rect_r ((,) ((,)
                                               _UU0393_ _UU0394_) d)
                                               (\hm4 _ ->
                                               Logic.eq_rect_r ns1
                                                 (\iHG2 _ _ _ _ ->
                                                 let {
                                                  x2 = iHG2 ns2 ns3 g0 x1 __}
                                                 in
                                                 Coq_merge_step _UU0393_
                                                 _UU0394_ _UU03a3_ _UU03a0_ d
                                                 (Datatypes.app ns1 g0) ns2
                                                 (Datatypes.app ns3 g0) ((:)
                                                 ((,) ((,) _UU0393_ _UU0394_)
                                                 d) (Datatypes.app ns1 g0))
                                                 ((:) ((,) ((,) _UU03a3_
                                                 _UU03a0_) d) ns2) ((:) ((,)
                                                 ((,)
                                                 (Datatypes.app _UU0393_
                                                   _UU03a3_)
                                                 (Datatypes.app _UU0394_
                                                   _UU03a0_)) d)
                                                 (Datatypes.app ns3 g0)) ((,)
                                                 ((,) _UU0393_ _UU0394_) d)
                                                 ((,) ((,) _UU03a3_ _UU03a0_)
                                                 d) ((,) ((,)
                                                 (Datatypes.app _UU0393_
                                                   _UU03a3_)
                                                 (Datatypes.app _UU0394_
                                                   _UU03a0_)) d) x2) g4 iHG1
                                                 __ __ hm4 __) a hm3 __) g4) a
                                           __) g7 hm2 __ __ __) p hm1 __) g7)
                                   p __) g8 hm0 __) p0 hm __) g8) p0 __) seq3
                         __) seq2 __) seq1 __) ns6) ns5) ns4 __ __ __ __ __ x0
               __ __ __}}) (Datatypes.length g7)}) g1 g2 g3 g x __

merge_appRR :: (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               -> (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               -> (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               -> (([])
               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
               -> (Coq_merge a1) -> Coq_merge a1
merge_appRR g1 g2 g3 g x =
  Datatypes.list_rect (\g4 g5 g0 hm _ ->
    case g4 of {
     ([]) ->
      case hm of {
       Coq_merge_nilL ns1 ns2 ns3 ->
        Logic.eq_rect_r ([]) (\_ ->
          Logic.eq_rect_r ([]) (\_ ->
            Logic.eq_rect_r g5 (\_ _ ->
              Logic.eq_rect_r ([]) (\_ _ -> Coq_merge_nilL ([]) g0 g0) g5 hm
                __) ns3) ns2) ns1 __ __ __ __;
       Coq_merge_nilR ns1 ns2 ns3 ->
        Logic.eq_rect_r ([]) (\_ ->
          Logic.eq_rect_r ([]) (\_ ->
            Logic.eq_rect_r g5 (\_ _ ->
              Logic.eq_rect_r ([]) (\_ _ -> Coq_merge_nilL ([]) g0 g0) g5 hm
                __) ns3) ns2) ns1 __ __ __ __;
       Coq_merge_step _ _ _ _ _ _ _ _ ns4 ns5 ns6 _ _ _ x0 ->
        Logic.eq_rect_r ([]) (\_ ->
          Logic.eq_rect_r ([]) (\_ ->
            Logic.eq_rect_r g5 (\_ _ _ _ _ _ _ -> Logic.coq_False_rect) ns6)
            ns5) ns4 __ __ __ __ __ x0 __ __ __};
     (:) _ _ -> Logic.coq_False_rect}) (\a g4 iHG1 g5 g6 g0 hm _ ->
    case g5 of {
     ([]) -> Logic.coq_False_rect;
     (:) p g7 ->
      Logic.eq_rect (Datatypes.length g4)
        (case g6 of {
          ([]) ->
           case hm of {
            Coq_merge_nilL ns1 ns2 ns3 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ([]) (\_ _ -> Logic.coq_False_rect) ns3) ns2)
               ns1 __ __ __ __;
            Coq_merge_nilR ns1 ns2 ns3 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ([]) (\_ _ -> Logic.coq_False_rect) ns3) ns2)
               ns1 __ __ __ __;
            Coq_merge_step _ _ _ _ _ _ _ _ ns4 ns5 ns6 _ _ _ x0 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ([]) (\_ _ _ _ _ _ _ -> Logic.coq_False_rect)
                   ns6) ns5) ns4 __ __ __ __ __ x0 __ __ __};
          (:) p0 g8 ->
           case hm of {
            Coq_merge_nilL ns1 ns2 ns3 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ((:) p0 g8) (\_ _ -> Logic.coq_False_rect)
                   ns3) ns2) ns1 __ __ __ __;
            Coq_merge_nilR ns1 ns2 ns3 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ((:) p0 g8) (\_ _ -> Logic.coq_False_rect)
                   ns3) ns2) ns1 __ __ __ __;
            Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns1 ns2 ns3
             ns4 ns5 ns6 seq1 seq2 seq3 x0 ->
             Logic.eq_rect_r ((:) a g4) (\_ ->
               Logic.eq_rect_r ((:) p g7) (\_ ->
                 Logic.eq_rect_r ((:) p0 g8) (\_ _ _ x1 _ _ _ ->
                   Logic.eq_rect_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                     Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                       Logic.eq_rect_r ((,) ((,)
                         (Datatypes.app _UU0393_ _UU03a3_)
                         (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                         Logic.eq_rect_r ((,) ((,)
                           (Datatypes.app _UU0393_ _UU03a3_)
                           (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                           Logic.eq_rect_r ns3
                             (Logic.eq_rect_r ((,) ((,)
                               (Datatypes.app _UU0393_ _UU03a3_)
                               (Datatypes.app _UU0394_ _UU03a0_)) d)
                               (\hm0 _ ->
                               Logic.eq_rect_r ns3 (\hm1 _ ->
                                 Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_)
                                   d) (\_ ->
                                   Logic.eq_rect_r ns2
                                     (Logic.eq_rect_r ((,) ((,) _UU03a3_
                                       _UU03a0_) d) (\hm2 _ ->
                                       Logic.eq_rect_r ns2 (\hm3 _ _ _ ->
                                         Logic.eq_rect_r ((,) ((,) _UU0393_
                                           _UU0394_) d) (\_ ->
                                           Logic.eq_rect_r ns1
                                             (Logic.eq_rect_r ((,) ((,)
                                               _UU0393_ _UU0394_) d)
                                               (\hm4 _ ->
                                               Logic.eq_rect_r ns1
                                                 (\iHG2 _ _ _ _ ->
                                                 let {
                                                  x2 = iHG2 ns2 ns3 g0 x1 __}
                                                 in
                                                 Coq_merge_step _UU0393_
                                                 _UU0394_ _UU03a3_ _UU03a0_ d
                                                 ns1 (Datatypes.app ns2 g0)
                                                 (Datatypes.app ns3 g0) ((:)
                                                 ((,) ((,) _UU0393_ _UU0394_)
                                                 d) ns1) ((:) ((,) ((,)
                                                 _UU03a3_ _UU03a0_) d)
                                                 (Datatypes.app ns2 g0)) ((:)
                                                 ((,) ((,)
                                                 (Datatypes.app _UU0393_
                                                   _UU03a3_)
                                                 (Datatypes.app _UU0394_
                                                   _UU03a0_)) d)
                                                 (Datatypes.app ns3 g0)) ((,)
                                                 ((,) _UU0393_ _UU0394_) d)
                                                 ((,) ((,) _UU03a3_ _UU03a0_)
                                                 d) ((,) ((,)
                                                 (Datatypes.app _UU0393_
                                                   _UU03a3_)
                                                 (Datatypes.app _UU0394_
                                                   _UU03a0_)) d) x2) g4 iHG1
                                                 __ __ hm4 __) a hm3 __) g4) a
                                           __) g7 hm2 __ __ __) p hm1 __) g7)
                                   p __) g8 hm0 __) p0 hm __) g8) p0 __) seq3
                         __) seq2 __) seq1 __) ns6) ns5) ns4 __ __ __ __ __ x0
               __ __ __}}) (Datatypes.length g7)}) g1 g2 g3 g x __

merge_ex :: (([])
            ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
            (([])
            ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
            (Structural_equivalence.Coq_struct_equiv_weak a1) ->
            Specif.Coq_sigT
            (([])
            ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
            (Coq_merge a1)
merge_ex g1 g2 hs =
  case hs of {
   Structural_equivalence.Coq_se_wk2_extL ns1 ns2 ns3 ns4 h0 ->
    Logic.eq_rect_r g1 (\_ ->
      Logic.eq_rect_r g2 (\_ h1 ->
        Logic.eq_rect_r (Datatypes.app ns1 ns3) (\_ _ ->
          let {h2 = merge_ex_str ns1 g2 h1} in
          case h2 of {
           Specif.Coq_existT g3 h3 -> Specif.Coq_existT (Datatypes.app g3 ns3)
            (merge_appLR ns1 g2 g3 ns3 h3)}) g1 hs __) ns2) ns4 __ __ h0;
   Structural_equivalence.Coq_se_wk2_extR ns1 ns2 ns3 ns4 h0 ->
    Logic.eq_rect_r g1 (\_ ->
      Logic.eq_rect_r g2 (\_ h1 ->
        Logic.eq_rect_r (Datatypes.app ns2 ns3) (\_ _ ->
          let {h2 = merge_ex_str g1 ns2 h1} in
          case h2 of {
           Specif.Coq_existT g3 h3 -> Specif.Coq_existT (Datatypes.app g3 ns3)
            (merge_appRR g1 ns2 g3 ns3 h3)}) g2 hs __) ns4) ns1 __ __ h0}

merge_contracted_nseq :: (([])
                         ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                         LntT.Coq_dir)) -> (([])
                         ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                         LntT.Coq_dir)) -> (Coq_merge a1) ->
                         ContractedT.Coq_contracted_nseq (LntT.PropF a1)
merge_contracted_nseq g =
  Datatypes.list_rect (\h _ ->
    Logic.eq_rec_r ([]) ContractedT.Coq_cont_nseq_nil h) (\a g0 iHG h hm ->
    case hm of {
     Coq_merge_nilL ns1 ns2 ns3 ->
      Logic.eq_rec_r ((:) a g0) (\_ ->
        Logic.eq_rec_r ((:) a g0) (\_ ->
          Logic.eq_rec_r h (\_ _ -> Logic.coq_False_rec) ns3) ns2) ns1 __ __
        __ __;
     Coq_merge_nilR ns1 ns2 ns3 ->
      Logic.eq_rec_r ((:) a g0) (\_ ->
        Logic.eq_rec_r ((:) a g0) (\_ ->
          Logic.eq_rec_r h (\_ _ -> Logic.coq_False_rec) ns3) ns2) ns1 __ __
        __ __;
     Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns1 ns2 ns3 ns4 ns5
      ns6 seq1 seq2 seq3 x ->
      Logic.eq_rect_r ((:) a g0) (\_ ->
        Logic.eq_rect_r ((:) a g0) (\_ ->
          Logic.eq_rect_r h (\_ _ _ x0 _ _ _ ->
            Logic.eq_rec_r seq2 (\_ ->
              Logic.eq_rec_r ns2
                (Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                  Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ _ ->
                    Logic.eq_rec_r ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                      Logic.eq_rect_r ((:) ((,) ((,)
                        (Datatypes.app _UU0393_ _UU03a3_)
                        (Datatypes.app _UU0394_ _UU03a0_)) d) ns3) (\hm0 _ ->
                        Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_) d)
                          (\hm1 _ _ ->
                          Logic.eq_rect_r ns2 (\iHG0 hm2 _ _ ->
                            Logic.eq_rec_r _UU0393_ (\_ ->
                              Logic.eq_rec_r _UU0394_ (\_ ->
                                Logic.eq_rec_r ns1
                                  (Logic.eq_rect_r _UU0393_ (\hm3 _ ->
                                    Logic.eq_rect_r _UU0394_ (\hm4 _ ->
                                      Logic.eq_rect_r ns1 (\iHG1 _ x1 _ ->
                                        ContractedT.Coq_cont_nseq_cons ((,)
                                        ((,) (Datatypes.app _UU0393_ _UU0393_)
                                        (Datatypes.app _UU0394_ _UU0394_)) d)
                                        ((,) ((,) _UU0393_ _UU0394_) d) ns3
                                        ns1
                                        (ContractedT.contracted_seq_double
                                          _UU0393_ _UU0394_ d) (iHG1 ns3 x1))
                                        ns2 iHG0 hm4 x0 __) _UU03a0_ hm3 __)
                                    _UU03a3_ hm2 __) ns2) _UU03a0_) _UU03a3_
                              __ __) g0 iHG hm1 __ __) a hm0 __ __) h hm __)
                      seq3 __) seq2 __ __) seq1 __) g0) a __) ns6) ns5) ns4 __
        __ __ __ __ x __ __ __}) g

merge_merge_contractedR :: (([])
                           ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                           LntT.Coq_dir)) -> (([])
                           ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                           LntT.Coq_dir)) -> (([])
                           ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                           LntT.Coq_dir)) -> (([])
                           ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                           LntT.Coq_dir)) -> (Coq_merge a1) -> (Coq_merge 
                           a1) -> ContractedT.Coq_contracted_nseq
                           (LntT.PropF a1)
merge_merge_contractedR g1 =
  Datatypes.list_rect (\g2 g3 g4 hm1 hm2 ->
    case hm1 of {
     Coq_merge_nilL ns1 ns2 ns3 ->
      Logic.eq_rec_r ([]) (\_ ->
        Logic.eq_rec_r g2 (\_ ->
          Logic.eq_rec_r g3 (\_ _ ->
            Logic.eq_rect_r g2 (\hm3 hm4 _ ->
              case hm4 of {
               Coq_merge_nilL ns4 ns5 ns6 ->
                Logic.eq_rec_r g2 (\_ ->
                  Logic.eq_rec_r g2 (\_ ->
                    Logic.eq_rec_r g4 (\_ _ ->
                      Logic.eq_rect_r ([]) (\hm5 _ _ _ _ ->
                        Logic.eq_rect_r ([]) (\_ _ ->
                          ContractedT.Coq_cont_nseq_nil) g4 hm5 __) g2 hm4 hm3
                        __ __ __) ns6) ns5) ns4 __ __ __ __;
               Coq_merge_nilR ns4 ns5 ns6 ->
                Logic.eq_rec_r g2 (\_ ->
                  Logic.eq_rec_r g2 (\_ ->
                    Logic.eq_rec_r g4 (\_ _ ->
                      Logic.eq_rect_r ([]) (\hm5 _ _ _ _ ->
                        Logic.eq_rect_r ([]) (\_ _ ->
                          ContractedT.Coq_cont_nseq_nil) g4 hm5 __) g2 hm4 hm3
                        __ __ __) ns6) ns5) ns4 __ __ __ __;
               Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns4 ns5
                ns6 ns7 ns8 ns9 seq1 seq2 seq3 x ->
                Logic.eq_rect_r g2 (\_ ->
                  Logic.eq_rect_r g2 (\_ ->
                    Logic.eq_rect_r g4 (\_ _ _ x0 _ _ _ ->
                      Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                        Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                          Logic.eq_rec_r ((,) ((,)
                            (Datatypes.app _UU0393_ _UU03a3_)
                            (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                            Logic.eq_rect_r ((:) ((,) ((,) _UU0393_ _UU0394_)
                              d) ns4) (\hm5 hm6 _ _ _ ->
                              Logic.eq_rect_r ((:) ((,) ((,)
                                (Datatypes.app _UU0393_ _UU03a3_)
                                (Datatypes.app _UU0394_ _UU03a0_)) d) ns6)
                                (\hm7 _ ->
                                Logic.eq_rec_r _UU03a3_ (\_ ->
                                  Logic.eq_rec_r _UU03a0_ (\_ ->
                                    Logic.eq_rec_r ns5
                                      (Logic.eq_rect_r _UU03a3_ (\hm8 hm9 _ ->
                                        Logic.eq_rect_r _UU03a0_
                                          (\hm10 hm11 _ ->
                                          Logic.eq_rect_r ns5
                                            (\hm12 hm13 x1 _ ->
                                            case hm13 of {
                                             Coq_merge_nilL ns10 ns0 ns11 ->
                                              Logic.eq_rec_r ((:) ((,) ((,)
                                                _UU03a3_ _UU03a0_) d) ns5)
                                                (\_ ->
                                                Logic.eq_rec_r ((:) ((,) ((,)
                                                  _UU03a3_ _UU03a0_) d) ns5)
                                                  (\_ ->
                                                  Logic.eq_rec_r ((:) ((,)
                                                    ((,)
                                                    (Datatypes.app _UU03a3_
                                                      _UU03a3_)
                                                    (Datatypes.app _UU03a0_
                                                      _UU03a0_)) d) ns6)
                                                    (\_ _ ->
                                                    Logic.coq_False_rec) ns11)
                                                  ns0) ns10 __ __ __ __;
                                             Coq_merge_nilR ns10 ns0 ns11 ->
                                              Logic.eq_rec_r ((:) ((,) ((,)
                                                _UU03a3_ _UU03a0_) d) ns5)
                                                (\_ ->
                                                Logic.eq_rec_r ((:) ((,) ((,)
                                                  _UU03a3_ _UU03a0_) d) ns5)
                                                  (\_ ->
                                                  Logic.eq_rec_r ((:) ((,)
                                                    ((,)
                                                    (Datatypes.app _UU03a3_
                                                      _UU03a3_)
                                                    (Datatypes.app _UU03a0_
                                                      _UU03a0_)) d) ns6)
                                                    (\_ _ ->
                                                    Logic.coq_False_rec) ns11)
                                                  ns0) ns10 __ __ __ __;
                                             Coq_merge_step _UU0393_0
                                              _UU0394_0 _UU03a3_0 _UU03a0_0 d0
                                              ns10 ns0 ns11 ns12 ns13 ns14
                                              seq4 seq5 seq6 x2 ->
                                              Logic.eq_rect_r ((:) ((,) ((,)
                                                _UU03a3_ _UU03a0_) d) ns5)
                                                (\_ ->
                                                Logic.eq_rect_r ((:) ((,) ((,)
                                                  _UU03a3_ _UU03a0_) d) ns5)
                                                  (\_ ->
                                                  Logic.eq_rect_r ((:) ((,)
                                                    ((,)
                                                    (Datatypes.app _UU03a3_
                                                      _UU03a3_)
                                                    (Datatypes.app _UU03a0_
                                                      _UU03a0_)) d) ns6)
                                                    (\_ _ _ x3 _ _ _ ->
                                                    Logic.eq_rec ((,) ((,)
                                                      (Datatypes.app _UU03a3_
                                                        _UU03a3_)
                                                      (Datatypes.app _UU03a0_
                                                        _UU03a0_)) d) (\_ ->
                                                      Logic.eq_rec_r ns11
                                                        (Logic.eq_rec_r ((,)
                                                          ((,) _UU0393_0
                                                          _UU0394_0) d0)
                                                          (\_ ->
                                                          Logic.eq_rec_r ((,)
                                                            ((,) _UU03a3_0
                                                            _UU03a0_0) d0)
                                                            (\_ ->
                                                            Logic.eq_rec_r
                                                              ((,) ((,)
                                                              (Datatypes.app
                                                                _UU0393_0
                                                                _UU03a3_0)
                                                              (Datatypes.app
                                                                _UU0394_0
                                                                _UU03a0_0))
                                                              d0) (\_ _ ->
                                                              Logic.eq_rect_r
                                                                ns11
                                                                (\x4 hm14 _ ->
                                                                Logic.eq_rec
                                                                  (Datatypes.app
                                                                    _UU03a3_
                                                                    _UU03a3_)
                                                                  (\_ ->
                                                                  Logic.eq_rec
                                                                    (Datatypes.app
                                                                     _UU03a0_
                                                                     _UU03a0_)
                                                                    (\_ ->
                                                                    Logic.eq_rec_r
                                                                     d0
                                                                     (Logic.eq_rect_r
                                                                     d0
                                                                     (\hm15 hm16 _ _ _ _ ->
                                                                     Logic.eq_rec_r
                                                                     _UU0393_0
                                                                     (\_ ->
                                                                     Logic.eq_rec_r
                                                                     _UU0394_0
                                                                     (\_ ->
                                                                     Logic.eq_rec_r
                                                                     ns10
                                                                     (Logic.eq_rect_r
                                                                     _UU0393_0
                                                                     (\hm17 hm18 _ _ _ _ _ ->
                                                                     Logic.eq_rect_r
                                                                     _UU0394_0
                                                                     (\hm19 hm20 _ _ _ _ _ ->
                                                                     Logic.eq_rect_r
                                                                     ns10
                                                                     (\x5 hm21 hm22 _ _ ->
                                                                     Logic.eq_rec_r
                                                                     _UU03a3_0
                                                                     (\_ ->
                                                                     Logic.eq_rec_r
                                                                     _UU03a0_0
                                                                     (\_ ->
                                                                     Logic.eq_rec_r
                                                                     ns0
                                                                     (Logic.eq_rect_r
                                                                     _UU03a3_0
                                                                     (\hm23 hm24 _ _ _ _ ->
                                                                     Logic.eq_rect_r
                                                                     _UU03a0_0
                                                                     (\hm25 hm26 _ _ _ _ ->
                                                                     Logic.eq_rect_r
                                                                     ns0
                                                                     (\_ _ _ x6 _ ->
                                                                     ContractedT.Coq_cont_nseq_cons
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     _UU03a3_0
                                                                     _UU03a3_0)
                                                                     (Datatypes.app
                                                                     _UU03a0_0
                                                                     _UU03a0_0))
                                                                     d0) ((,)
                                                                     ((,)
                                                                     _UU03a3_0
                                                                     _UU03a0_0)
                                                                     d0) ns11
                                                                     ns0
                                                                     (ContractedT.contracted_seq_double
                                                                     _UU03a3_0
                                                                     _UU03a0_0
                                                                     d0)
                                                                     (merge_contracted_nseq
                                                                     ns0 ns11
                                                                     x6)) ns10
                                                                     x5 hm26
                                                                     hm25 x3
                                                                     __)
                                                                     _UU0394_0
                                                                     hm24 hm23
                                                                     __ __ __
                                                                     __)
                                                                     _UU0393_0
                                                                     hm22 hm21
                                                                     __ __ __
                                                                     __) ns10)
                                                                     _UU0394_0)
                                                                     _UU0393_0
                                                                     __ __)
                                                                     ns5 x4
                                                                     hm20 hm19
                                                                     __ __)
                                                                     _UU03a0_
                                                                     hm18 hm17
                                                                     __ __ __
                                                                     __ __)
                                                                     _UU03a3_
                                                                     hm16 hm15
                                                                     __ __ __
                                                                     __ __)
                                                                     ns5)
                                                                     _UU03a0_)
                                                                     _UU03a3_
                                                                     __ __) d
                                                                     hm12 hm14
                                                                     __ __ __
                                                                     __) d)
                                                                    (Datatypes.app
                                                                     _UU0394_0
                                                                     _UU03a0_0))
                                                                  (Datatypes.app
                                                                    _UU0393_0
                                                                    _UU03a3_0)
                                                                  __ __) ns6
                                                                x1 hm13 __)
                                                              seq6 __ __) seq5
                                                            __) seq4 __) ns6)
                                                      seq6 __) ns14) ns13)
                                                ns12 __ __ __ __ __ x2 __ __
                                                __}) ns4 hm10 hm11 x0 __)
                                          _UU0394_ hm8 hm9 __) _UU0393_ hm6
                                        hm7 __) ns4) _UU0394_) _UU0393_ __ __)
                                g4 hm5 __) g2 hm4 hm3 __ __ __) seq3 __) seq2
                          __) seq1 __) ns9) ns8) ns7 __ __ __ __ __ x __ __ __})
              g3 hm1 hm2 __) ns3) ns2) ns1 __ __ __ __;
     Coq_merge_nilR ns1 ns2 ns3 ->
      Logic.eq_rec_r ([]) (\_ ->
        Logic.eq_rec_r g2 (\_ ->
          Logic.eq_rec_r g3 (\_ _ ->
            Logic.eq_rect_r ([]) (\hm3 hm4 _ ->
              Logic.eq_rect_r ([]) (\hm5 _ _ ->
                case hm5 of {
                 Coq_merge_nilL ns4 ns5 ns6 ->
                  Logic.eq_rec_r ([]) (\_ ->
                    Logic.eq_rec_r ([]) (\_ ->
                      Logic.eq_rec_r g4 (\_ _ ->
                        Logic.eq_rect_r ([]) (\_ _ ->
                          ContractedT.Coq_cont_nseq_nil) g4 hm5 __) ns6) ns5)
                    ns4 __ __ __ __;
                 Coq_merge_nilR ns4 ns5 ns6 ->
                  Logic.eq_rec_r ([]) (\_ ->
                    Logic.eq_rec_r ([]) (\_ ->
                      Logic.eq_rec_r g4 (\_ _ ->
                        Logic.eq_rect_r ([]) (\_ _ ->
                          ContractedT.Coq_cont_nseq_nil) g4 hm5 __) ns6) ns5)
                    ns4 __ __ __ __;
                 Coq_merge_step _ _ _ _ _ _ _ _ ns4 ns5 ns6 _ _ _ x ->
                  Logic.eq_rect_r ([]) (\_ ->
                    Logic.eq_rect_r ([]) (\_ ->
                      Logic.eq_rect_r g4 (\_ _ _ _ _ _ _ ->
                        Logic.coq_False_rec) ns6) ns5) ns4 __ __ __ __ __ x __
                    __ __}) g3 hm4 hm3 __) g2 hm1 hm2 __) ns3) ns2) ns1 __ __
        __ __;
     Coq_merge_step _ _ _ _ _ _ _ _ ns4 ns5 ns6 _ _ _ x ->
      Logic.eq_rect_r ([]) (\_ ->
        Logic.eq_rect_r g2 (\_ ->
          Logic.eq_rect_r g3 (\_ _ _ _ _ _ _ -> Logic.coq_False_rec) ns6) ns5)
        ns4 __ __ __ __ __ x __ __ __}) (\a g2 iHG1 g3 g4 g5 hm1 hm2 ->
    case hm1 of {
     Coq_merge_nilL ns1 ns2 ns3 ->
      Logic.eq_rec_r ((:) a g2) (\_ ->
        Logic.eq_rec_r g3 (\_ ->
          Logic.eq_rec_r g4 (\_ _ -> Logic.coq_False_rec) ns3) ns2) ns1 __ __
        __ __;
     Coq_merge_nilR ns1 ns2 ns3 ->
      Logic.eq_rec_r ((:) a g2) (\_ ->
        Logic.eq_rec_r g3 (\_ ->
          Logic.eq_rec_r g4 (\_ _ ->
            Logic.eq_rect_r ([]) (\hm3 hm4 _ ->
              Logic.eq_rect_r ((:) a g2) (\hm5 _ _ ->
                case hm5 of {
                 Coq_merge_nilL ns4 ns5 ns6 ->
                  Logic.eq_rec_r ((:) a g2) (\_ ->
                    Logic.eq_rec_r ([]) (\_ ->
                      Logic.eq_rec_r g5 (\_ _ -> Logic.coq_False_rec) ns6) ns5)
                    ns4 __ __ __ __;
                 Coq_merge_nilR ns4 ns5 ns6 ->
                  Logic.eq_rec_r ((:) a g2) (\_ ->
                    Logic.eq_rec_r ([]) (\_ ->
                      Logic.eq_rec_r g5 (\_ _ ->
                        Logic.eq_rect_r ((:) a g2) (\_ _ ->
                          ContractedT.contracted_nseq_refl ((:) a g2)) g5 hm5
                          __) ns6) ns5) ns4 __ __ __ __;
                 Coq_merge_step _ _ _ _ _ _ _ _ ns4 ns5 ns6 _ _ _ x ->
                  Logic.eq_rect_r ((:) a g2) (\_ ->
                    Logic.eq_rect_r ([]) (\_ ->
                      Logic.eq_rect_r g5 (\_ _ _ _ _ _ _ ->
                        Logic.coq_False_rec) ns6) ns5) ns4 __ __ __ __ __ x __
                    __ __}) g4 hm4 hm3 __) g3 hm1 hm2 __) ns3) ns2) ns1 __ __
        __ __;
     Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns1 ns2 ns3 ns4 ns5
      ns6 seq1 seq2 seq3 x ->
      Logic.eq_rect_r ((:) a g2) (\_ ->
        Logic.eq_rect_r g3 (\_ ->
          Logic.eq_rect_r g4 (\_ _ _ x0 _ _ _ ->
            Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
              Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                Logic.eq_rec_r ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                  (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                  Logic.eq_rect_r ((:) ((,) ((,) _UU03a3_ _UU03a0_) d) ns2)
                    (\hm3 hm4 _ ->
                    Logic.eq_rect_r ((:) ((,) ((,)
                      (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) ns3)
                      (\hm5 hm6 _ ->
                      Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                        Logic.eq_rec_r ns1
                          (Logic.eq_rect_r ((,) ((,) _UU0393_ _UU0394_) d)
                            (\hm7 _ ->
                            Logic.eq_rect_r ns1 (\iHG2 hm8 _ ->
                              case hm5 of {
                               Coq_merge_nilL ns0 ns7 ns8 ->
                                Logic.eq_rec_r ((:) ((,) ((,)
                                  (Datatypes.app _UU0393_ _UU03a3_)
                                  (Datatypes.app _UU0394_ _UU03a0_)) d) ns3)
                                  (\_ ->
                                  Logic.eq_rec_r ((:) ((,) ((,) _UU03a3_
                                    _UU03a0_) d) ns2) (\_ ->
                                    Logic.eq_rec_r g5 (\_ _ ->
                                      Logic.coq_False_rec) ns8) ns7) ns0 __ __
                                  __ __;
                               Coq_merge_nilR ns0 ns7 ns8 ->
                                Logic.eq_rec_r ((:) ((,) ((,)
                                  (Datatypes.app _UU0393_ _UU03a3_)
                                  (Datatypes.app _UU0394_ _UU03a0_)) d) ns3)
                                  (\_ ->
                                  Logic.eq_rec_r ((:) ((,) ((,) _UU03a3_
                                    _UU03a0_) d) ns2) (\_ ->
                                    Logic.eq_rec_r g5 (\_ _ ->
                                      Logic.coq_False_rec) ns8) ns7) ns0 __ __
                                  __ __;
                               Coq_merge_step _UU0393_0 _UU0394_0 _UU03a3_0
                                _UU03a0_0 d0 ns0 ns7 ns8 ns9 ns10 ns11 seq4
                                seq5 seq6 x1 ->
                                Logic.eq_rect_r ((:) ((,) ((,)
                                  (Datatypes.app _UU0393_ _UU03a3_)
                                  (Datatypes.app _UU0394_ _UU03a0_)) d) ns3)
                                  (\_ ->
                                  Logic.eq_rect_r ((:) ((,) ((,) _UU03a3_
                                    _UU03a0_) d) ns2) (\_ ->
                                    Logic.eq_rect_r g5 (\_ _ _ x2 _ _ _ ->
                                      Logic.eq_rec_r ((,) ((,) _UU0393_0
                                        _UU0394_0) d0) (\_ ->
                                        Logic.eq_rec_r ((,) ((,) _UU03a3_0
                                          _UU03a0_0) d0) (\_ ->
                                          Logic.eq_rec_r ((,) ((,)
                                            (Datatypes.app _UU0393_0
                                              _UU03a3_0)
                                            (Datatypes.app _UU0394_0
                                              _UU03a0_0)) d0) (\_ ->
                                            Logic.eq_rect_r ((:) ((,) ((,)
                                              (Datatypes.app _UU0393_0
                                                _UU03a3_0)
                                              (Datatypes.app _UU0394_0
                                                _UU03a0_0)) d0) ns8)
                                              (\hm9 _ ->
                                              Logic.eq_rec_r _UU03a3_0 (\_ ->
                                                Logic.eq_rec_r _UU03a0_0
                                                  (\_ ->
                                                  Logic.eq_rec_r d0 (\_ ->
                                                    Logic.eq_rec_r ns7
                                                      (Logic.eq_rect_r
                                                        _UU03a3_0
                                                        (\hm10 hm11 _ _ ->
                                                        Logic.eq_rect_r
                                                          _UU03a0_0
                                                          (\hm12 hm13 _ _ ->
                                                          Logic.eq_rect_r d0
                                                            (\hm14 hm15 _ _ ->
                                                            Logic.eq_rect_r
                                                              ns7
                                                              (\hm16 hm17 x3 _ ->
                                                              Logic.eq_rec
                                                                (Datatypes.app
                                                                  _UU0393_
                                                                  _UU03a3_0)
                                                                (\_ ->
                                                                Logic.eq_rec
                                                                  (Datatypes.app
                                                                    _UU0394_
                                                                    _UU03a0_0)
                                                                  (\_ ->
                                                                  Logic.eq_rec_r
                                                                    ns0
                                                                    (Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     (\hm18 _ ->
                                                                     Logic.eq_rect
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0)
                                                                     (\hm19 _ ->
                                                                     Logic.eq_rect_r
                                                                     ns0
                                                                     (\_ x4 _ _ ->
                                                                     ContractedT.Coq_cont_nseq_cons
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     _UU03a3_0)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0)
                                                                     _UU03a0_0))
                                                                     d0) ((,)
                                                                     ((,)
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0))
                                                                     d0) ns8
                                                                     ns0
                                                                     (ContractedT.Coq_cont_seq_stepL
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     _UU03a3_0)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0)
                                                                     _UU03a0_0))
                                                                     d0) ((,)
                                                                     ((,)
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0)
                                                                     _UU03a0_0))
                                                                     d0) ((,)
                                                                     ((,)
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0))
                                                                     d0)
                                                                     (ContractedT.Coq_cont_seqL
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     _UU03a3_0)
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0)
                                                                     _UU03a0_0)
                                                                     d0
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     (Datatypes.app
                                                                     _UU03a3_0
                                                                     _UU03a3_0))
                                                                     (ContractedT.contracted_multi_L
                                                                     _UU0393_
                                                                     (Datatypes.app
                                                                     _UU03a3_0
                                                                     _UU03a3_0)
                                                                     _UU03a3_0
                                                                     (ContractedT.contracted_multi_double
                                                                     _UU03a3_0))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     _UU03a3_0)))
                                                                     (ContractedT.Coq_cont_seq_baseR
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0)
                                                                     _UU03a0_0))
                                                                     d0) ((,)
                                                                     ((,)
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0))
                                                                     d0)
                                                                     (ContractedT.Coq_cont_seqR
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0)
                                                                     _UU03a0_0)
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0)
                                                                     (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_0)
                                                                     d0
                                                                     (Logic.eq_rec
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     (Datatypes.app
                                                                     _UU03a0_0
                                                                     _UU03a0_0))
                                                                     (ContractedT.contracted_multi_L
                                                                     _UU0394_
                                                                     (Datatypes.app
                                                                     _UU03a0_0
                                                                     _UU03a0_0)
                                                                     _UU03a0_0
                                                                     (ContractedT.contracted_multi_double
                                                                     _UU03a0_0))
                                                                     (Datatypes.app
                                                                     (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_0)
                                                                     _UU03a0_0)))))
                                                                     (iHG2 ns7
                                                                     ns0 ns8
                                                                     x4 x2))
                                                                     ns3 hm16
                                                                     x3 hm19
                                                                     __)
                                                                     _UU0394_0
                                                                     hm18 __)
                                                                     _UU0393_0
                                                                     hm17 __)
                                                                    ns3)
                                                                  _UU0394_0)
                                                                _UU0393_0 __
                                                                __) ns2 hm14
                                                              hm15 x0 __) d
                                                            hm12 hm13 __ __)
                                                          _UU03a0_ hm10 hm11
                                                          __ __) _UU03a3_ hm8
                                                        hm9 __ __) ns2) d)
                                                  _UU03a0_) _UU03a3_ __ __ __)
                                              g5 hm5 __) seq6 __) seq5 __)
                                        seq4 __) ns11) ns10) ns9 __ __ __ __
                                  __ x1 __ __ __}) g2 iHG1 hm7 __) a hm6 __)
                          g2) a __) g4 hm4 hm3 __) g3 hm1 hm2 __) seq3 __)
                seq2 __) seq1 __) ns6) ns5) ns4 __ __ __ __ __ x __ __ __}) g1

merge_weakened_nseqL :: (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) -> (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) -> (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) ->
                        (Structural_equivalence.Coq_struct_equiv_str a1) ->
                        (Coq_merge a1) -> WeakenedT.Coq_weakened_nseq
                        (LntT.PropF a1)
merge_weakened_nseqL g =
  Datatypes.list_rect (\h gH hs hm ->
    case hm of {
     Coq_merge_nilL ns1 ns2 ns3 ->
      Logic.eq_rec_r ([]) (\_ ->
        Logic.eq_rec_r h (\_ ->
          Logic.eq_rec_r gH (\_ _ ->
            Logic.eq_rect_r h (\hm0 _ ->
              case hs of {
               Structural_equivalence.Coq_se_nil2 ->
                Logic.eq_rec ([])
                  (Logic.eq_rect ([]) (\_ _ -> WeakenedT.Coq_weak_nseq_nil) h
                    hs hm0) h;
               Structural_equivalence.Coq_se_step2 _ _ d _UU0393_2 _UU0394_2 _
                ns4 ns5 ns6 h3 ->
                Logic.eq_rec_r ([]) (\_ ->
                  Logic.eq_rec_r h (\_ _ _ ->
                    Logic.eq_rect_r ((:) ((,) ((,) _UU0393_2 _UU0394_2) d)
                      ns4) (\_ _ _ -> Logic.coq_False_rec) h hs hm0 __) ns6)
                  ns5 __ __ __ h3}) gH hm __) ns3) ns2) ns1 __ __ __ __;
     Coq_merge_nilR ns1 ns2 ns3 ->
      Logic.eq_rec_r ([]) (\_ ->
        Logic.eq_rec_r h (\_ ->
          Logic.eq_rec_r gH (\_ _ ->
            Logic.eq_rect_r ([]) (\_ hm0 _ ->
              Logic.eq_rect_r ([]) (\_ _ -> WeakenedT.Coq_weak_nseq_nil) gH
                hm0 __) h hs hm __) ns3) ns2) ns1 __ __ __ __;
     Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d _ ns2 ns3 ns4 ns5
      ns6 seq1 seq2 seq3 x ->
      Logic.eq_rect_r ([]) (\_ ->
        Logic.eq_rect_r h (\_ ->
          Logic.eq_rect_r gH (\_ _ _ _ _ _ _ ->
            Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
              Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                Logic.eq_rec_r ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                  (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                  Logic.eq_rect_r ((:) ((,) ((,) _UU03a3_ _UU03a0_) d) ns2)
                    (\_ hm0 _ ->
                    Logic.eq_rect_r ((:) ((,) ((,)
                      (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) ns3) (\_ _ ->
                      Logic.coq_False_rec) gH hm0 __) h hs hm __) seq3 __)
                seq2 __) seq1 __) ns6) ns5) ns4 __ __ __ __ __ x __ __ __})
    (\a g0 iHG h gH hs hm ->
    case hm of {
     Coq_merge_nilL ns1 ns2 ns3 ->
      Logic.eq_rec_r ((:) a g0) (\_ ->
        Logic.eq_rec_r h (\_ ->
          Logic.eq_rec_r gH (\_ _ -> Logic.coq_False_rec) ns3) ns2) ns1 __ __
        __ __;
     Coq_merge_nilR ns1 ns2 ns3 ->
      Logic.eq_rec_r ((:) a g0) (\_ ->
        Logic.eq_rec_r h (\_ ->
          Logic.eq_rec_r gH (\_ _ ->
            Logic.eq_rect_r ([]) (\hs0 hm0 _ ->
              Logic.eq_rect_r ((:) a g0) (\_ _ ->
                case hs0 of {
                 Structural_equivalence.Coq_se_nil2 -> Logic.coq_False_rec __;
                 Structural_equivalence.Coq_se_step2 _ _ _ _ _ _ _ ns4 ns5
                  h1 ->
                  Logic.eq_rec_r ((:) a g0) (\_ ->
                    Logic.eq_rec_r ([]) (\_ _ _ -> Logic.coq_False_rec) ns5)
                    ns4 __ __ __ h1}) gH hm0 __) h hs hm __) ns3) ns2) ns1 __
        __ __ __;
     Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns1 ns2 ns3 ns4 ns5
      ns6 seq1 seq2 seq3 x ->
      Logic.eq_rect_r ((:) a g0) (\_ ->
        Logic.eq_rect_r h (\_ ->
          Logic.eq_rect_r gH (\_ _ _ x0 _ _ _ ->
            Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
              Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                Logic.eq_rec_r ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                  (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                  Logic.eq_rect_r ((:) ((,) ((,) _UU03a3_ _UU03a0_) d) ns2)
                    (\hs0 hm0 _ ->
                    Logic.eq_rect_r ((:) ((,) ((,)
                      (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) ns3) (\hm1 _ ->
                      Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                        Logic.eq_rec_r ns1
                          (Logic.eq_rect_r ((,) ((,) _UU0393_ _UU0394_) d)
                            (\hm2 hs1 _ ->
                            Logic.eq_rect_r ns1 (\iHG0 hs2 hm3 _ ->
                              case hs2 of {
                               Structural_equivalence.Coq_se_nil2 ->
                                Logic.coq_False_rec __;
                               Structural_equivalence.Coq_se_step2 _UU0393_1
                                _UU0394_1 d0 _UU0393_2 _UU0394_2 ns0 ns7 ns8
                                ns9 h1 ->
                                Logic.eq_rec_r ((:) ((,) ((,) _UU0393_
                                  _UU0394_) d) ns1) (\_ ->
                                  Logic.eq_rec_r ((:) ((,) ((,) _UU03a3_
                                    _UU03a0_) d) ns2) (\_ _ h2 ->
                                    Logic.eq_rec_r _UU0393_1 (\_ ->
                                      Logic.eq_rec_r _UU0394_1 (\_ ->
                                        Logic.eq_rec_r d0 (\_ ->
                                          Logic.eq_rec_r ns0
                                            (Logic.eq_rec_r _UU0393_2 (\_ ->
                                              Logic.eq_rec_r _UU0394_2 (\_ ->
                                                Logic.eq_rec_r d0 (\_ ->
                                                  Logic.eq_rec_r ns7
                                                    (Logic.eq_rect_r _UU0393_1
                                                      (\hm4 hs3 _ ->
                                                      Logic.eq_rect_r
                                                        _UU0394_1
                                                        (\hs4 hm5 _ ->
                                                        Logic.eq_rect_r d0
                                                          (\hm6 hs5 _ _ _ ->
                                                          Logic.eq_rect_r ns0
                                                            (\iHG1 hs6 hm7 x1 _ ->
                                                            Logic.eq_rect_r
                                                              _UU0393_2
                                                              (\hm8 hs7 _ ->
                                                              Logic.eq_rect_r
                                                                _UU0394_2
                                                                (\hs8 hm9 _ ->
                                                                Logic.eq_rect_r
                                                                  ns7
                                                                  (\x2 _ _ _ ->
                                                                  WeakenedT.Coq_weak_nseq_cons
                                                                  ((,) ((,)
                                                                  _UU0393_1
                                                                  _UU0394_1)
                                                                  d0) ((,)
                                                                  ((,)
                                                                  (Datatypes.app
                                                                    _UU0393_1
                                                                    _UU0393_2)
                                                                  (Datatypes.app
                                                                    _UU0394_1
                                                                    _UU0394_2))
                                                                  d0) ns0 ns3
                                                                  (WeakenedT.Coq_weak_seq_baseLR
                                                                  ((,) ((,)
                                                                  _UU0393_1
                                                                  _UU0394_1)
                                                                  d0) ((,)
                                                                  ((,)
                                                                  (Datatypes.app
                                                                    _UU0393_1
                                                                    _UU0393_2)
                                                                  _UU0394_1)
                                                                  d0) ((,)
                                                                  ((,)
                                                                  (Datatypes.app
                                                                    _UU0393_1
                                                                    _UU0393_2)
                                                                  (Datatypes.app
                                                                    _UU0394_1
                                                                    _UU0394_2))
                                                                  d0)
                                                                  (WeakenedT.Coq_weak_seqL
                                                                  _UU0393_1
                                                                  (Datatypes.app
                                                                    _UU0393_1
                                                                    _UU0393_2)
                                                                  _UU0394_1 d0
                                                                  (WeakenedT.Coq_weak_multi_step
                                                                  _UU0393_1
                                                                  (Datatypes.app
                                                                    _UU0393_1
                                                                    _UU0393_2)
                                                                  (Datatypes.app
                                                                    _UU0393_1
                                                                    _UU0393_2)
                                                                  (WeakenedT.weak_appL
                                                                    _UU0393_1
                                                                    _UU0393_2)
                                                                  (WeakenedT.Coq_weak_multi_refl
                                                                  (Datatypes.app
                                                                    _UU0393_1
                                                                    _UU0393_2))))
                                                                  (WeakenedT.Coq_weak_seqR
                                                                  _UU0394_1
                                                                  (Datatypes.app
                                                                    _UU0394_1
                                                                    _UU0394_2)
                                                                  (Datatypes.app
                                                                    _UU0393_1
                                                                    _UU0393_2)
                                                                  d0
                                                                  (WeakenedT.Coq_weak_multi_step
                                                                  _UU0394_1
                                                                  (Datatypes.app
                                                                    _UU0394_1
                                                                    _UU0394_2)
                                                                  (Datatypes.app
                                                                    _UU0394_1
                                                                    _UU0394_2)
                                                                  (WeakenedT.weak_appL
                                                                    _UU0394_1
                                                                    _UU0394_2)
                                                                  (WeakenedT.Coq_weak_multi_refl
                                                                  (Datatypes.app
                                                                    _UU0394_1
                                                                    _UU0394_2)))))
                                                                  (iHG1 ns7
                                                                    ns3 h2 x2))
                                                                  ns2 x1 hm9
                                                                  hs8 __)
                                                                _UU03a0_ hs7
                                                                hm8 __)
                                                              _UU03a3_ hm7 hs6
                                                              __) ns1 iHG0 hs5
                                                            hm6 x0 __) d hm5
                                                          hs4 __ __ __)
                                                        _UU0394_ hs3 hm4 __)
                                                      _UU0393_ hm3 hs2 __) ns2)
                                                  d) _UU03a0_) _UU03a3_ __ __
                                              __) ns1) d) _UU0394_) _UU0393_
                                      __ __ __) ns9) ns8 __ __ __ h1}) g0 iHG
                              hs1 hm2 __) a hm1 hs0 __) g0) a __) gH hm0 __) h
                    hs hm __) seq3 __) seq2 __) seq1 __) ns6) ns5) ns4 __ __
        __ __ __ x __ __ __}) g

merge_weakened_nseqR :: (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) -> (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) -> (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) ->
                        (Structural_equivalence.Coq_struct_equiv_str a1) ->
                        (Coq_merge a1) -> WeakenedT.Coq_weakened_nseq
                        (LntT.PropF a1)
merge_weakened_nseqR g h =
  Datatypes.list_rect (\g0 gH hs hm ->
    case hm of {
     Coq_merge_nilL ns1 ns2 ns3 ->
      Logic.eq_rec_r g0 (\_ ->
        Logic.eq_rec_r ([]) (\_ ->
          Logic.eq_rec_r gH (\_ _ ->
            Logic.eq_rect_r ([]) (\hs0 hm0 _ ->
              Logic.eq_rect_r ([]) (\_ _ ->
                case hs0 of {
                 Structural_equivalence.Coq_se_nil2 ->
                  WeakenedT.Coq_weak_nseq_nil;
                 Structural_equivalence.Coq_se_step2 _ _ _ _ _ _ _ ns4 ns5
                  h1 ->
                  Logic.eq_rec_r ([]) (\_ ->
                    Logic.eq_rec_r ([]) (\_ _ _ -> Logic.coq_False_rec) ns5)
                    ns4 __ __ __ h1}) gH hm0 __) g0 hs hm __) ns3) ns2) ns1 __
        __ __ __;
     Coq_merge_nilR ns1 ns2 ns3 ->
      Logic.eq_rec_r g0 (\_ ->
        Logic.eq_rec_r ([]) (\_ ->
          Logic.eq_rec_r gH (\_ _ ->
            Logic.eq_rect_r g0 (\_ _ ->
              case hs of {
               Structural_equivalence.Coq_se_nil2 ->
                Logic.eq_rec ([]) (\_ -> WeakenedT.Coq_weak_nseq_nil) g0 __;
               Structural_equivalence.Coq_se_step2 _ _ _ _ _ _ _ ns4 ns5 h2 ->
                Logic.eq_rec_r g0 (\_ ->
                  Logic.eq_rec_r ([]) (\_ _ _ -> Logic.coq_False_rec) ns5) ns4
                  __ __ __ h2}) gH hm __) ns3) ns2) ns1 __ __ __ __;
     Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns1 _ ns3 ns4 ns5
      ns6 seq1 seq2 seq3 x ->
      Logic.eq_rect_r g0 (\_ ->
        Logic.eq_rect_r ([]) (\_ ->
          Logic.eq_rect_r gH (\_ _ _ _ _ _ _ ->
            Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
              Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                Logic.eq_rec_r ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                  (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                  Logic.eq_rect_r ((:) ((,) ((,) _UU0393_ _UU0394_) d) ns1)
                    (\_ hm0 _ ->
                    Logic.eq_rect_r ((:) ((,) ((,)
                      (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) ns3) (\_ _ ->
                      Logic.coq_False_rec) gH hm0 __) g0 hs hm __) seq3 __)
                seq2 __) seq1 __) ns6) ns5) ns4 __ __ __ __ __ x __ __ __})
    (\a h0 iHlist g0 gH hs hm ->
    case hm of {
     Coq_merge_nilL ns1 ns2 ns3 ->
      Logic.eq_rec_r g0 (\_ ->
        Logic.eq_rec_r ((:) a h0) (\_ ->
          Logic.eq_rec_r gH (\_ _ ->
            Logic.eq_rect_r ([]) (\hs0 hm0 _ ->
              Logic.eq_rect_r ((:) a h0) (\_ _ ->
                case hs0 of {
                 Structural_equivalence.Coq_se_nil2 -> Logic.coq_False_rec;
                 Structural_equivalence.Coq_se_step2 _ _ _ _ _ _ _ ns4 ns5
                  h2 ->
                  Logic.eq_rec_r ([]) (\_ ->
                    Logic.eq_rec_r ((:) a h0) (\_ _ _ -> Logic.coq_False_rec)
                      ns5) ns4 __ __ __ h2}) gH hm0 __) g0 hs hm __) ns3) ns2)
        ns1 __ __ __ __;
     Coq_merge_nilR ns1 ns2 ns3 ->
      Logic.eq_rec_r g0 (\_ ->
        Logic.eq_rec_r ((:) a h0) (\_ ->
          Logic.eq_rec_r gH (\_ _ -> Logic.coq_False_rec) ns3) ns2) ns1 __ __
        __ __;
     Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns1 ns2 ns3 ns4 ns5
      ns6 seq1 seq2 seq3 x ->
      Logic.eq_rect_r g0 (\_ ->
        Logic.eq_rect_r ((:) a h0) (\_ ->
          Logic.eq_rect_r gH (\_ _ _ x0 _ _ _ ->
            Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
              Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                Logic.eq_rec_r ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                  (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                  Logic.eq_rect_r ((:) ((,) ((,) _UU0393_ _UU0394_) d) ns1)
                    (\hs0 hm0 _ ->
                    Logic.eq_rect_r ((:) ((,) ((,)
                      (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) ns3) (\hm1 _ ->
                      Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                        Logic.eq_rec_r ns2
                          (Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_) d)
                            (\hm2 hs1 _ ->
                            Logic.eq_rect_r ns2 (\iHlist0 hs2 hm3 _ ->
                              WeakenedT.Coq_weak_nseq_cons ((,) ((,) _UU03a3_
                              _UU03a0_) d) ((,) ((,)
                              (Datatypes.app _UU0393_ _UU03a3_)
                              (Datatypes.app _UU0394_ _UU03a0_)) d) ns2 ns3
                              (WeakenedT.Coq_weak_seq_baseLR ((,) ((,)
                              _UU03a3_ _UU03a0_) d) ((,) ((,)
                              (Datatypes.app _UU0393_ _UU03a3_) _UU03a0_) d)
                              ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                              (Datatypes.app _UU0394_ _UU03a0_)) d)
                              (WeakenedT.Coq_weak_seqL _UU03a3_
                              (Datatypes.app _UU0393_ _UU03a3_) _UU03a0_ d
                              (WeakenedT.Coq_weak_multi_step _UU03a3_
                              (Datatypes.app _UU0393_ _UU03a3_)
                              (Datatypes.app _UU0393_ _UU03a3_)
                              (WeakenedT.weak_appR _UU0393_ _UU03a3_)
                              (WeakenedT.Coq_weak_multi_refl
                              (Datatypes.app _UU0393_ _UU03a3_))))
                              (WeakenedT.Coq_weak_seqR _UU03a0_
                              (Datatypes.app _UU0394_ _UU03a0_)
                              (Datatypes.app _UU0393_ _UU03a3_) d
                              (WeakenedT.Coq_weak_multi_step _UU03a0_
                              (Datatypes.app _UU0394_ _UU03a0_)
                              (Datatypes.app _UU0394_ _UU03a0_)
                              (WeakenedT.weak_appR _UU0394_ _UU03a0_)
                              (WeakenedT.Coq_weak_multi_refl
                              (Datatypes.app _UU0394_ _UU03a0_)))))
                              (iHlist0 ns1 ns3
                                (case hs2 of {
                                  Structural_equivalence.Coq_se_nil2 ->
                                   Logic.coq_False_rec __;
                                  Structural_equivalence.Coq_se_step2 _UU0393_1
                                   _UU0394_1 d0 _UU0393_2 _UU0394_2 ns0 ns7
                                   ns8 ns9 h1 ->
                                   Logic.eq_rec_r ((:) ((,) ((,) _UU0393_
                                     _UU0394_) d) ns1) (\_ ->
                                     Logic.eq_rec_r ((:) ((,) ((,) _UU03a3_
                                       _UU03a0_) d) ns2) (\_ _ h2 ->
                                       Logic.eq_rec_r _UU0393_1 (\_ ->
                                         Logic.eq_rec_r _UU0394_1 (\_ ->
                                           Logic.eq_rec_r d0 (\_ ->
                                             Logic.eq_rec_r ns0
                                               (Logic.eq_rec_r _UU0393_2
                                                 (\_ ->
                                                 Logic.eq_rec_r _UU0394_2
                                                   (\_ ->
                                                   Logic.eq_rec_r d0 (\_ ->
                                                     Logic.eq_rec_r ns7
                                                       (Logic.eq_rect_r
                                                         _UU0393_1
                                                         (\hm4 hs3 _ ->
                                                         Logic.eq_rect_r
                                                           _UU0394_1
                                                           (\hs4 hm5 _ ->
                                                           Logic.eq_rect_r d0
                                                             (\hm6 hs5 _ _ _ ->
                                                             Logic.eq_rect_r
                                                               ns0
                                                               (\hs6 hm7 x1 _ ->
                                                               Logic.eq_rect_r
                                                                 _UU0393_2
                                                                 (\hm8 hs7 _ ->
                                                                 Logic.eq_rect_r
                                                                   _UU0394_2
                                                                   (\hs8 hm9 _ ->
                                                                   Logic.eq_rect_r
                                                                     ns7
                                                                     (\_ _ _ _ _ ->
                                                                     h2) ns2
                                                                     iHlist0
                                                                     x1 hm9
                                                                     hs8 __)
                                                                   _UU03a0_
                                                                   hs7 hm8 __)
                                                                 _UU03a3_ hm7
                                                                 hs6 __) ns1
                                                               hs5 hm6 x0 __)
                                                             d hm5 hs4 __ __
                                                             __) _UU0394_ hs3
                                                           hm4 __) _UU0393_
                                                         hm3 hs2 __) ns2) d)
                                                   _UU03a0_) _UU03a3_ __ __
                                                 __) ns1) d) _UU0394_)
                                         _UU0393_ __ __ __) ns9) ns8 __ __ __
                                     h1}) x0)) h0 iHlist hs1 hm2 __) a hm1 hs0
                            __) h0) a __) gH hm0 __) g0 hs hm __) seq3 __)
                seq2 __) seq1 __) ns6) ns5) ns4 __ __ __ __ __ x __ __ __}) h
    g

merge_app :: (([])
             ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
             (([])
             ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
             (([])
             ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
             (([])
             ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
             (([])
             ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
             (([])
             ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
             (Coq_merge a1) -> (Coq_merge a1) -> Coq_merge a1
merge_app l1 l2 l3 l4 l5 l6 x x0 =
  Datatypes.list_rect (\_ l7 _ l8 _ _ hm1 hm2 ->
    case l7 of {
     ([]) ->
      case hm1 of {
       Coq_merge_nilL ns1 ns2 ns3 ->
        Logic.eq_rect_r ([]) (\_ ->
          Logic.eq_rect_r ([]) (\_ ->
            Logic.eq_rect_r l8 (\_ _ ->
              Logic.eq_rect_r ([]) (\_ _ -> hm2) l8 hm1 __) ns3) ns2) ns1 __
          __ __ __;
       Coq_merge_nilR ns1 ns2 ns3 ->
        Logic.eq_rect_r ([]) (\_ ->
          Logic.eq_rect_r ([]) (\_ ->
            Logic.eq_rect_r l8 (\_ _ ->
              Logic.eq_rect_r ([]) (\_ _ -> hm2) l8 hm1 __) ns3) ns2) ns1 __
          __ __ __;
       Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d _ _ ns3 ns4 ns5
        ns6 seq1 seq2 seq3 x1 ->
        Logic.eq_rect_r ([]) (\_ ->
          Logic.eq_rect_r ([]) (\_ ->
            Logic.eq_rect_r l8 (\_ _ _ _ _ _ _ ->
              Logic.eq_rect_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                  Logic.eq_rect_r ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                    (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                    Logic.eq_rect_r ((:) ((,) ((,)
                      (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) ns3) (\_ _ ->
                      Logic.coq_False_rect) l8 hm1 __) seq3 __) seq2 __) seq1
                __) ns6) ns5) ns4 __ __ __ __ __ x1 __ __ __};
     (:) _ _ -> Logic.coq_False_rect})
    (\a l7 iHl1 l8 l9 l10 l11 l12 _ hm1 hm2 ->
    case l9 of {
     ([]) -> Logic.coq_False_rect;
     (:) p l13 ->
      case hm1 of {
       Coq_merge_nilL ns1 ns2 ns3 ->
        Logic.eq_rect_r ((:) a l7) (\_ ->
          Logic.eq_rect_r ((:) p l13) (\_ ->
            Logic.eq_rect_r l11 (\_ _ -> Logic.coq_False_rect) ns3) ns2) ns1
          __ __ __ __;
       Coq_merge_nilR ns1 ns2 ns3 ->
        Logic.eq_rect_r ((:) a l7) (\_ ->
          Logic.eq_rect_r ((:) p l13) (\_ ->
            Logic.eq_rect_r l11 (\_ _ -> Logic.coq_False_rect) ns3) ns2) ns1
          __ __ __ __;
       Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns1 ns2 ns3 ns4
        ns5 ns6 seq1 seq2 seq3 x1 ->
        Logic.eq_rect_r ((:) a l7) (\_ ->
          Logic.eq_rect_r ((:) p l13) (\_ ->
            Logic.eq_rect_r l11 (\_ _ _ x2 _ _ _ ->
              Logic.eq_rect_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                  Logic.eq_rect_r ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                    (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                    Logic.eq_rect_r ((:) ((,) ((,)
                      (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) ns3) (\hm3 _ ->
                      Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                        Logic.eq_rect_r ns2
                          (Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_) d)
                            (\_ hm4 _ ->
                            Logic.eq_rect_r ns2 (\_ hm5 _ ->
                              Logic.eq_rect_r ((,) ((,) _UU0393_ _UU0394_) d)
                                (\_ ->
                                Logic.eq_rect_r ns1
                                  (Logic.eq_rect_r ((,) ((,) _UU0393_
                                    _UU0394_) d) (\_ hm6 _ ->
                                    Logic.eq_rect_r ns1 (\iHl2 _ _ _ ->
                                      Coq_merge_step _UU0393_ _UU0394_
                                      _UU03a3_ _UU03a0_ d
                                      (Datatypes.app ns1 l8)
                                      (Datatypes.app ns2 l10)
                                      (Datatypes.app ns3 l12) ((:) ((,) ((,)
                                      _UU0393_ _UU0394_) d)
                                      (Datatypes.app ns1 l8)) ((:) ((,) ((,)
                                      _UU03a3_ _UU03a0_) d)
                                      (Datatypes.app ns2 l10)) ((:) ((,) ((,)
                                      (Datatypes.app _UU0393_ _UU03a3_)
                                      (Datatypes.app _UU0394_ _UU03a0_)) d)
                                      (Datatypes.app ns3 l12)) ((,) ((,)
                                      _UU0393_ _UU0394_) d) ((,) ((,) _UU03a3_
                                      _UU03a0_) d) ((,) ((,)
                                      (Datatypes.app _UU0393_ _UU03a3_)
                                      (Datatypes.app _UU0394_ _UU03a0_)) d)
                                      (iHl2 l8 ns2 l10 ns3 l12 __ x2 hm2)) l7
                                      iHl1 __ hm6 __) a __ hm5 __) l7) a __)
                              l13 __ hm4 __) p __ hm3 __) l13) p __) l11 hm1
                      __) seq3 __) seq2 __) seq1 __) ns6) ns5) ns4 __ __ __ __
          __ x1 __ __ __}}) l1 l2 l3 l4 l5 l6 __ x x0

merge_app_rev :: (([])
                 ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                 -> (([])
                 ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                 -> (([])
                 ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                 -> (([])
                 ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                 -> (([])
                 ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                 -> (([])
                 ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                 -> (Coq_merge a1) -> (,) (Coq_merge a1) (Coq_merge a1)
merge_app_rev l1 l2 l3 l4 l5 l6 x =
  Datatypes.list_rect (\_ l7 _ l8 _ _ _ hm ->
    case l7 of {
     ([]) ->
      case l8 of {
       ([]) -> (,) (Coq_merge_nilL ([]) ([]) ([])) hm;
       (:) _ _ -> Logic.coq_False_rect};
     (:) _ _ -> Logic.coq_False_rect}) (\a l7 iHl1 l8 l9 l10 l11 l12 _ _ hm ->
    case l9 of {
     ([]) -> Logic.coq_False_rect;
     (:) p l13 ->
      case l11 of {
       ([]) -> Logic.coq_False_rect;
       (:) p0 l14 ->
        case hm of {
         Coq_merge_nilL ns1 ns2 ns3 ->
          Logic.eq_rect_r ((:) a (Datatypes.app l7 l8)) (\_ ->
            Logic.eq_rect_r ((:) p (Datatypes.app l13 l10)) (\_ ->
              Logic.eq_rect_r ((:) p0 (Datatypes.app l14 l12)) (\_ _ ->
                Logic.coq_False_rect) ns3) ns2) ns1 __ __ __ __;
         Coq_merge_nilR ns1 ns2 ns3 ->
          Logic.eq_rect_r ((:) a (Datatypes.app l7 l8)) (\_ ->
            Logic.eq_rect_r ((:) p (Datatypes.app l13 l10)) (\_ ->
              Logic.eq_rect_r ((:) p0 (Datatypes.app l14 l12)) (\_ _ ->
                Logic.coq_False_rect) ns3) ns2) ns1 __ __ __ __;
         Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns1 ns2 ns3 ns4
          ns5 ns6 seq1 seq2 seq3 x0 ->
          Logic.eq_rect_r ((:) a (Datatypes.app l7 l8)) (\_ ->
            Logic.eq_rect_r ((:) p (Datatypes.app l13 l10)) (\_ ->
              Logic.eq_rect_r ((:) p0 (Datatypes.app l14 l12))
                (\_ _ _ x1 _ _ _ ->
                Logic.eq_rect_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                  Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                    Logic.eq_rect_r ((,) ((,)
                      (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                      Logic.eq_rect_r ((,) ((,)
                        (Datatypes.app _UU0393_ _UU03a3_)
                        (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                        Logic.eq_rect (Datatypes.app l14 l12)
                          (Logic.eq_rect_r ((,) ((,)
                            (Datatypes.app _UU0393_ _UU03a3_)
                            (Datatypes.app _UU0394_ _UU03a0_)) d) (\hm0 _ ->
                            Logic.eq_rect (Datatypes.app l14 l12) (\x2 _ ->
                              Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_) d)
                                (\_ ->
                                Logic.eq_rect (Datatypes.app l13 l10)
                                  (Logic.eq_rect_r ((,) ((,) _UU03a3_
                                    _UU03a0_) d) (\hm1 _ ->
                                    Logic.eq_rect (Datatypes.app l13 l10)
                                      (\x3 _ ->
                                      Logic.eq_rect_r ((,) ((,) _UU0393_
                                        _UU0394_) d) (\_ ->
                                        Logic.eq_rect (Datatypes.app l7 l8)
                                          (Logic.eq_rect_r ((,) ((,) _UU0393_
                                            _UU0394_) d) (\_ _ ->
                                            Logic.eq_rect
                                              (Datatypes.app l7 l8) (\x4 _ ->
                                              Logic.eq_rect
                                                (Datatypes.length l7)
                                                (let {
                                                  p1 = iHl1 l8 l13 l10 l14 l12
                                                         __ __ x4}
                                                 in
                                                 case p1 of {
                                                  (,) m m0 -> (,)
                                                   (Coq_merge_step _UU0393_
                                                   _UU0394_ _UU03a3_ _UU03a0_
                                                   d l7 l13 l14 ((:) ((,) ((,)
                                                   _UU0393_ _UU0394_) d) l7)
                                                   ((:) ((,) ((,) _UU03a3_
                                                   _UU03a0_) d) l13) ((:) ((,)
                                                   ((,)
                                                   (Datatypes.app _UU0393_
                                                     _UU03a3_)
                                                   (Datatypes.app _UU0394_
                                                     _UU03a0_)) d) l14) ((,)
                                                   ((,) _UU0393_ _UU0394_) d)
                                                   ((,) ((,) _UU03a3_
                                                   _UU03a0_) d) ((,) ((,)
                                                   (Datatypes.app _UU0393_
                                                     _UU03a3_)
                                                   (Datatypes.app _UU0394_
                                                     _UU03a0_)) d) m) m0})
                                                (Datatypes.length l14)) ns1 x3
                                              __) a hm1 __) ns1) a __) ns2 x2
                                      __) p hm0 __) ns2) p __) ns3 x1 __) p0
                            hm __) ns3) p0 __) seq3 __) seq2 __) seq1 __) ns6)
              ns5) ns4 __ __ __ __ __ x0 __ __ __}}}) l1 l2 l3 l4 l5 l6 __ __
    x

merge_app_struct_equiv_strR :: (([])
                               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                               LntT.Coq_dir)) -> (([])
                               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                               LntT.Coq_dir)) -> ((,)
                               (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                               LntT.Coq_dir) -> (([])
                               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                               LntT.Coq_dir)) -> (Coq_merge a1) ->
                               (Structural_equivalence.Coq_struct_equiv_str
                               a1) -> Specif.Coq_sigT
                               (([])
                               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                               LntT.Coq_dir))
                               (Specif.Coq_sigT
                               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                               LntT.Coq_dir)
                               (Specif.Coq_sigT
                               (([])
                               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                               LntT.Coq_dir))
                               (Specif.Coq_sigT
                               ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                               LntT.Coq_dir)
                               ((,) ((,) () (Coq_merge a1))
                               (Structural_equivalence.Coq_struct_equiv_str
                               a1)))))
merge_app_struct_equiv_strR g h1 seq gHseq hm hs =
  let {s = List_lemmasT.list_nil_or_tail_singleton g} in
  case s of {
   Prelude.Left _ ->
    Logic.eq_rect_r ([]) (\_ hs0 ->
      case hs0 of {
       Structural_equivalence.Coq_se_nil2 ->
        Logic.eq_rect ([]) Logic.coq_False_rect
          (Datatypes.app h1 ((:) seq ([])));
       Structural_equivalence.Coq_se_step2 _ _ _ _ _ _ _ ns3 ns4 h2 ->
        Logic.eq_rect_r ([]) (\_ ->
          Logic.eq_rect_r (Datatypes.app h1 ((:) seq ([]))) (\_ _ _ ->
            Logic.coq_False_rect) ns4) ns3 __ __ __ h2}) g hm hs;
   Prelude.Right s0 ->
    case s0 of {
     Specif.Coq_existT s1 s2 ->
      case s2 of {
       Specif.Coq_existT s3 _ ->
        Logic.eq_rect_r (Datatypes.app s1 ((:) s3 ([]))) (\hm0 hs0 ->
          let {s4 = List_lemmasT.list_nil_or_tail_singleton gHseq} in
          case s4 of {
           Prelude.Left _ ->
            Logic.eq_rect_r ([]) (\hm1 ->
              case hm1 of {
               Coq_merge_nilL ns1 ns2 ns3 ->
                Logic.eq_rect_r (Datatypes.app s1 ((:) s3 ([]))) (\_ ->
                  Logic.eq_rect_r (Datatypes.app h1 ((:) seq ([]))) (\_ ->
                    Logic.eq_rect_r ([]) (\_ _ -> Logic.coq_False_rect) ns3)
                    ns2) ns1 __ __ __ __;
               Coq_merge_nilR ns1 ns2 ns3 ->
                Logic.eq_rect_r (Datatypes.app s1 ((:) s3 ([]))) (\_ ->
                  Logic.eq_rect_r (Datatypes.app h1 ((:) seq ([]))) (\_ ->
                    Logic.eq_rect_r ([]) (\_ _ -> Logic.coq_False_rect) ns3)
                    ns2) ns1 __ __ __ __;
               Coq_merge_step _ _ _ _ _ _ _ _ ns4 ns5 ns6 _ _ _ x ->
                Logic.eq_rect_r (Datatypes.app s1 ((:) s3 ([]))) (\_ ->
                  Logic.eq_rect_r (Datatypes.app h1 ((:) seq ([]))) (\_ ->
                    Logic.eq_rect_r ([]) (\_ _ _ _ _ _ _ ->
                      Logic.coq_False_rect) ns6) ns5) ns4 __ __ __ __ __ x __
                  __ __}) gHseq hm0;
           Prelude.Right s5 ->
            case s5 of {
             Specif.Coq_existT s6 s7 ->
              case s7 of {
               Specif.Coq_existT s8 _ ->
                Logic.eq_rect_r (Datatypes.app s6 ((:) s8 ([]))) (\hm1 ->
                  Logic.eq_rect (Datatypes.length s1)
                    (let {
                      hm2 = merge_app_rev s1 ((:) s3 ([])) h1 ((:) seq ([]))
                              s6 ((:) s8 ([])) hm1}
                     in
                     case hm2 of {
                      (,) hm3 _ -> Specif.Coq_existT s1 (Specif.Coq_existT s3
                       (Specif.Coq_existT s6 (Specif.Coq_existT s8 ((,) ((,)
                       __ hm3)
                       (let {
                         hs1 = Structural_equivalence.struct_equiv_str_app_revR
                                 s1 ((:) s3 ([])) h1 ((:) seq ([])) hs0}
                        in
                        case hs1 of {
                         (,) x _ -> x})))))}) (Datatypes.length h1)) gHseq hm0}}})
          g hm hs}}}

merge_single :: (([]) (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> LntT.Coq_dir ->
                Coq_merge a1
merge_single a1 a2 b1 b2 d =
  Coq_merge_step a1 a2 b1 b2 d ([]) ([]) ([]) ((:) ((,) ((,) a1 a2) d) ([]))
    ((:) ((,) ((,) b1 b2) d) ([])) ((:) ((,) ((,) (Datatypes.app a1 b1)
    (Datatypes.app a2 b2)) d) ([])) ((,) ((,) a1 a2) d) ((,) ((,) b1 b2) d)
    ((,) ((,) (Datatypes.app a1 b1) (Datatypes.app a2 b2)) d) (Coq_merge_nilL
    ([]) ([]) ([]))

merge_app_single_rev :: (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) -> (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) -> (([])
                        ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                        LntT.Coq_dir)) -> (([]) (LntT.PropF a1)) -> (([])
                        (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                        (LntT.PropF a1)) -> LntT.Coq_dir ->
                        (Structural_equivalence.Coq_struct_equiv_str a1) ->
                        (Coq_merge a1) -> Coq_merge a1
merge_app_single_rev g =
  Datatypes.list_rect (\h gH a1 a2 b1 b2 d hstr hm ->
    case hstr of {
     Structural_equivalence.Coq_se_nil2 ->
      Logic.eq_rect ([])
        (Logic.eq_rect ([]) (\_ hm0 ->
          case hm0 of {
           Coq_merge_nilL ns1 ns2 ns3 ->
            Logic.eq_rect_r ([]) (\_ ->
              Logic.eq_rect_r ([]) (\_ ->
                Logic.eq_rect_r gH (\_ _ ->
                  Logic.eq_rect_r ([]) (\_ _ -> merge_single a1 a2 b1 b2 d) gH
                    hm0 __) ns3) ns2) ns1 __ __ __ __;
           Coq_merge_nilR ns1 ns2 ns3 ->
            Logic.eq_rect_r ([]) (\_ ->
              Logic.eq_rect_r ([]) (\_ ->
                Logic.eq_rect_r gH (\_ _ ->
                  Logic.eq_rect_r ([]) (\_ _ -> merge_single a1 a2 b1 b2 d) gH
                    hm0 __) ns3) ns2) ns1 __ __ __ __;
           Coq_merge_step _ _ _ _ _ _ _ _ ns4 ns5 ns6 _ _ _ x ->
            Logic.eq_rect_r ([]) (\_ ->
              Logic.eq_rect_r ([]) (\_ ->
                Logic.eq_rect_r gH (\_ _ _ _ _ _ _ -> Logic.coq_False_rect)
                  ns6) ns5) ns4 __ __ __ __ __ x __ __ __}) h hstr hm) h;
     Structural_equivalence.Coq_se_step2 _ _ _ _ _ _ _ ns3 ns4 h2 ->
      Logic.eq_rect_r ([]) (\_ ->
        Logic.eq_rect_r h (\_ _ _ -> Logic.coq_False_rect) ns4) ns3 __ __ __
        h2}) (\a g0 iHG h gH a1 a2 b1 b2 d hstr hm ->
    case hstr of {
     Structural_equivalence.Coq_se_nil2 -> Logic.coq_False_rect __;
     Structural_equivalence.Coq_se_step2 _UU0393_1 _UU0394_1 d0 _UU0393_2
      _UU0394_2 ns1 ns2 ns3 ns4 h2 ->
      Logic.eq_rect_r ((:) a g0) (\_ ->
        Logic.eq_rect_r h (\_ _ h3 ->
          Logic.eq_rect_r ((:) ((,) ((,) _UU0393_2 _UU0394_2) d0) ns2)
            (\hstr0 hm0 _ ->
            let {
             hstr1 = Logic.eq_rec ((:) a g0) hstr0
                       (Datatypes.app ((:) a ([])) g0)}
            in
            let {
             hstr2 = Logic.eq_rec ((:) ((,) ((,) _UU0393_2 _UU0394_2) d0) ns2)
                       hstr1
                       (Datatypes.app ((:) ((,) ((,) _UU0393_2 _UU0394_2) d0)
                         ([])) ns2)}
            in
            let {
             hm1 = Logic.eq_rect ((:) a g0) hm0
                     (Datatypes.app ((:) a ([])) g0)}
            in
            let {
             hm2 = Logic.eq_rect ((:) ((,) ((,) _UU0393_2 _UU0394_2) d0) ns2)
                     hm1
                     (Datatypes.app ((:) ((,) ((,) _UU0393_2 _UU0394_2) d0)
                       ([])) ns2)}
            in
            Logic.eq_rect_r ((,) ((,) _UU0393_1 _UU0394_1) d0)
              (let {
                hstr3 = Logic.eq_rec a hstr2 ((,) ((,) _UU0393_1 _UU0394_1)
                          d0)}
               in
               let {
                hm3 = Logic.eq_rect a hm2 ((,) ((,) _UU0393_1 _UU0394_1) d0)}
               in
               Logic.eq_rect a
                 (let {
                   hstr4 = Logic.eq_rec_r ((,) ((,) _UU0393_1 _UU0394_1) d0)
                             hstr3 a}
                  in
                  let {
                   hm4 = Logic.eq_rect_r ((,) ((,) _UU0393_1 _UU0394_1) d0)
                           hm3 a}
                  in
                  Logic.eq_rect_r ((,) ((,) _UU0393_1 _UU0394_1) d0)
                    (\hm5 hstr5 ->
                    Logic.eq_rect_r ns1 (\iHG0 hstr6 hm6 ->
                      case hm6 of {
                       Coq_merge_nilL ns0 ns5 ns6 ->
                        Logic.eq_rect_r ((:) ((,) ((,) _UU0393_1 _UU0394_1)
                          d0) ns1) (\_ ->
                          Logic.eq_rect_r ((:) ((,) ((,) _UU0393_2 _UU0394_2)
                            d0) ns2) (\_ ->
                            Logic.eq_rect_r gH (\_ _ -> Logic.coq_False_rect)
                              ns6) ns5) ns0 __ __ __ __;
                       Coq_merge_nilR ns0 ns5 ns6 ->
                        Logic.eq_rect_r ((:) ((,) ((,) _UU0393_1 _UU0394_1)
                          d0) ns1) (\_ ->
                          Logic.eq_rect_r ((:) ((,) ((,) _UU0393_2 _UU0394_2)
                            d0) ns2) (\_ ->
                            Logic.eq_rect_r gH (\_ _ -> Logic.coq_False_rect)
                              ns6) ns5) ns0 __ __ __ __;
                       Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d1
                        ns0 ns5 ns6 ns7 ns8 ns9 seq1 seq2 seq3 x ->
                        Logic.eq_rect_r ((:) ((,) ((,) _UU0393_1 _UU0394_1)
                          d0) ns1) (\_ ->
                          Logic.eq_rect_r ((:) ((,) ((,) _UU0393_2 _UU0394_2)
                            d0) ns2) (\_ ->
                            Logic.eq_rect_r gH (\_ _ _ x0 _ _ _ ->
                              Logic.eq_rect_r ((,) ((,) _UU0393_ _UU0394_) d1)
                                (\_ ->
                                Logic.eq_rect_r ((,) ((,) _UU03a3_ _UU03a0_)
                                  d1) (\_ ->
                                  Logic.eq_rect_r ((,) ((,)
                                    (Datatypes.app _UU0393_ _UU03a3_)
                                    (Datatypes.app _UU0394_ _UU03a0_)) d1)
                                    (\_ ->
                                    Logic.eq_rect_r ((:) ((,) ((,)
                                      (Datatypes.app _UU0393_ _UU03a3_)
                                      (Datatypes.app _UU0394_ _UU03a0_)) d1)
                                      ns6) (\hm7 _ ->
                                      Logic.eq_rect_r _UU0393_ (\_ ->
                                        Logic.eq_rect_r _UU0394_ (\_ ->
                                          Logic.eq_rect_r d1 (\_ ->
                                            Logic.eq_rect_r ns0
                                              (Logic.eq_rect_r _UU03a3_ (\_ ->
                                                Logic.eq_rect_r _UU03a0_
                                                  (\_ ->
                                                  Logic.eq_rect_r d1 (\_ ->
                                                    Logic.eq_rect_r ns5
                                                      (Logic.eq_rect_r
                                                        _UU0393_
                                                        (\hm8 hstr7 _ ->
                                                        Logic.eq_rect_r
                                                          _UU0394_
                                                          (\hstr8 hm9 _ ->
                                                          Logic.eq_rect_r d1
                                                            (\hm10 hstr9 _ _ _ ->
                                                            Logic.eq_rect_r
                                                              ns0
                                                              (\iHG1 hstr10 hm11 h4 _ ->
                                                              Logic.eq_rect_r
                                                                _UU03a3_
                                                                (\hm12 hstr11 _ ->
                                                                Logic.eq_rect_r
                                                                  _UU03a0_
                                                                  (\hstr12 hm13 _ ->
                                                                  Logic.eq_rect_r
                                                                    ns5
                                                                    (\h5 _ _ _ ->
                                                                    Coq_merge_step
                                                                    _UU0393_
                                                                    _UU0394_
                                                                    _UU03a3_
                                                                    _UU03a0_
                                                                    d1
                                                                    (Datatypes.app
                                                                     ns0 ((:)
                                                                     ((,) ((,)
                                                                     a1 a2) d)
                                                                     ([])))
                                                                    (Datatypes.app
                                                                     ns5 ((:)
                                                                     ((,) ((,)
                                                                     b1 b2) d)
                                                                     ([])))
                                                                    (Datatypes.app
                                                                     ns6 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     a1 b1)
                                                                     (Datatypes.app
                                                                     a2 b2))
                                                                     d) ([])))
                                                                    ((:) ((,)
                                                                    ((,)
                                                                    _UU0393_
                                                                    _UU0394_)
                                                                    d1)
                                                                    (Datatypes.app
                                                                     ns0 ((:)
                                                                     ((,) ((,)
                                                                     a1 a2) d)
                                                                     ([]))))
                                                                    ((:) ((,)
                                                                    ((,)
                                                                    _UU03a3_
                                                                    _UU03a0_)
                                                                    d1)
                                                                    (Datatypes.app
                                                                     ns5 ((:)
                                                                     ((,) ((,)
                                                                     b1 b2) d)
                                                                     ([]))))
                                                                    ((:) ((,)
                                                                    ((,)
                                                                    (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_)
                                                                    (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_))
                                                                    d1)
                                                                    (Datatypes.app
                                                                     ns6 ((:)
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     a1 b1)
                                                                     (Datatypes.app
                                                                     a2 b2))
                                                                     d) ([]))))
                                                                    ((,) ((,)
                                                                    _UU0393_
                                                                    _UU0394_)
                                                                    d1) ((,)
                                                                    ((,)
                                                                    _UU03a3_
                                                                    _UU03a0_)
                                                                    d1) ((,)
                                                                    ((,)
                                                                    (Datatypes.app
                                                                     _UU0393_
                                                                     _UU03a3_)
                                                                    (Datatypes.app
                                                                     _UU0394_
                                                                     _UU03a0_))
                                                                    d1)
                                                                    (iHG1 ns5
                                                                     ns6 a1 a2
                                                                     b1 b2 d
                                                                     h5 x0))
                                                                    ns2 h4
                                                                    hm13
                                                                    hstr12 __)
                                                                  _UU0394_2
                                                                  hstr11 hm12
                                                                  __)
                                                                _UU0393_2 hm11
                                                                hstr10 __) ns1
                                                              iHG0 hstr9 hm10
                                                              h3 __) d0 hm9
                                                            hstr8 __ __ __)
                                                          _UU0394_1 hstr7 hm8
                                                          __) _UU0393_1 hm7
                                                        hstr6 __) ns2) d0)
                                                  _UU0394_2) _UU0393_2 __ __
                                                __) ns1) d0) _UU0394_1)
                                        _UU0393_1 __ __ __) gH hm6 __) seq3 __)
                                  seq2 __) seq1 __) ns9) ns8) ns7 __ __ __ __
                          __ x __ __ __}) g0 iHG hstr5 hm5) a hm4 hstr4) ((,)
                 ((,) _UU0393_1 _UU0394_1) d0)) a) h hstr hm __) ns4) ns3 __
        __ __ h2}) g

merge_app_struct_equiv_strR_explicit :: (([])
                                        ((,)
                                        (Gen_tacs.Coq_rel
                                        (([]) (LntT.PropF a1))) LntT.Coq_dir))
                                        -> (([])
                                        ((,)
                                        ((,) (([]) (LntT.PropF a1))
                                        (([]) (LntT.PropF a1))) LntT.Coq_dir))
                                        -> (([])
                                        ((,)
                                        (Gen_tacs.Coq_rel
                                        (([]) (LntT.PropF a1))) LntT.Coq_dir))
                                        -> (([]) (LntT.PropF a1)) -> (([])
                                        (LntT.PropF a1)) -> LntT.Coq_dir ->
                                        (Coq_merge a1) ->
                                        (Structural_equivalence.Coq_struct_equiv_str
                                        a1) -> Specif.Coq_sigT
                                        (([])
                                        ((,)
                                        ((,) (([]) (LntT.PropF a1))
                                        (([]) (LntT.PropF a1))) LntT.Coq_dir))
                                        (Specif.Coq_sigT
                                        (([]) (LntT.PropF a1))
                                        (Specif.Coq_sigT
                                        (([]) (LntT.PropF a1))
                                        (Specif.Coq_sigT
                                        (([])
                                        ((,)
                                        ((,) (([]) (LntT.PropF a1))
                                        (([]) (LntT.PropF a1))) LntT.Coq_dir))
                                        ((,) ((,) () (Coq_merge a1))
                                        (Structural_equivalence.Coq_struct_equiv_str
                                        a1)))))
merge_app_struct_equiv_strR_explicit g h gHseq _UU0393_ _UU0394_ d hm hstr =
  let {
   hstr0 = merge_app_struct_equiv_strR g h ((,) ((,) _UU0393_ _UU0394_) d)
             gHseq hm hstr}
  in
  case hstr0 of {
   Specif.Coq_existT hstr1 hstr2 ->
    case hstr2 of {
     Specif.Coq_existT hstr3 hstr4 ->
      case hstr3 of {
       (,) hstr5 hstr6 ->
        case hstr4 of {
         Specif.Coq_existT hstr7 hstr8 ->
          case hstr8 of {
           Specif.Coq_existT hstr9 hstr10 ->
            case hstr10 of {
             (,) _ hstr11 ->
              case hstr9 of {
               (,) hstr12 hstr13 ->
                Logic.eq_rect_r
                  (Datatypes.app hstr1 ((:) ((,) hstr5 hstr6) ([]))) (\hm0 ->
                  Logic.eq_rect_r
                    (Datatypes.app hstr7 ((:) ((,) hstr12 hstr13) ([])))
                    (\hm1 ->
                    case hstr12 of {
                     (,) l l0 ->
                      case hstr5 of {
                       (,) l1 l2 ->
                        let {
                         hm2 = merge_app_rev hstr1 ((:) ((,) ((,) l1 l2)
                                 hstr6) ([])) h ((:) ((,) ((,) _UU0393_
                                 _UU0394_) d) ([])) hstr7 ((:) ((,) ((,) l l0)
                                 hstr13) ([])) hm1}
                        in
                        case hm2 of {
                         (,) hm3 hm4 ->
                          case hm4 of {
                           Coq_merge_nilL ns1 ns2 ns3 ->
                            Logic.eq_rect_r ((:) ((,) ((,) l1 l2) hstr6) ([]))
                              (\_ ->
                              Logic.eq_rect_r ((:) ((,) ((,) _UU0393_
                                _UU0394_) d) ([])) (\_ ->
                                Logic.eq_rect_r ((:) ((,) ((,) l l0) hstr13)
                                  ([])) (\_ _ -> Logic.coq_False_rect) ns3)
                                ns2) ns1 __ __ __ __;
                           Coq_merge_nilR ns1 ns2 ns3 ->
                            Logic.eq_rect_r ((:) ((,) ((,) l1 l2) hstr6) ([]))
                              (\_ ->
                              Logic.eq_rect_r ((:) ((,) ((,) _UU0393_
                                _UU0394_) d) ([])) (\_ ->
                                Logic.eq_rect_r ((:) ((,) ((,) l l0) hstr13)
                                  ([])) (\_ _ -> Logic.coq_False_rect) ns3)
                                ns2) ns1 __ __ __ __;
                           Coq_merge_step _UU0393_0 _UU0394_0 _UU03a3_
                            _UU03a0_ d0 ns1 ns2 ns3 ns4 ns5 ns6 seq1 seq2 seq3
                            x ->
                            Logic.eq_rect_r ((:) ((,) ((,) l1 l2) hstr6) ([]))
                              (\_ ->
                              Logic.eq_rect_r ((:) ((,) ((,) _UU0393_
                                _UU0394_) d) ([])) (\_ ->
                                Logic.eq_rect_r ((:) ((,) ((,) l l0) hstr13)
                                  ([])) (\_ _ _ x0 _ _ _ ->
                                  Logic.eq_rect ((,) ((,) l l0) hstr13) (\_ ->
                                    Logic.eq_rect ([])
                                      (Logic.eq_rect_r ((,) ((,) _UU0393_0
                                        _UU0394_0) d0) (\_ ->
                                        Logic.eq_rect_r ((,) ((,) _UU03a3_
                                          _UU03a0_) d0) (\_ ->
                                          Logic.eq_rect_r ((,) ((,)
                                            (Datatypes.app _UU0393_0 _UU03a3_)
                                            (Datatypes.app _UU0394_0 _UU03a0_))
                                            d0) (\_ _ ->
                                            Logic.eq_rect ([]) (\x1 _ ->
                                              Logic.eq_rect_r
                                                (Datatypes.app _UU0393_0
                                                  _UU03a3_) (\_ ->
                                                Logic.eq_rect_r
                                                  (Datatypes.app _UU0394_0
                                                    _UU03a0_) (\_ ->
                                                  Logic.eq_rect_r d0
                                                    (Logic.eq_rect_r
                                                      (Datatypes.app _UU0393_0
                                                        _UU03a3_) (\hm5 _ _ ->
                                                      Logic.eq_rect_r
                                                        (Datatypes.app
                                                          _UU0394_0 _UU03a0_)
                                                        (\hm6 _ _ ->
                                                        Logic.eq_rect_r d0
                                                          (\hm7 _ _ ->
                                                          Logic.eq_rect_r
                                                            _UU0393_0 (\_ ->
                                                            Logic.eq_rect_r
                                                              _UU0394_0 (\_ ->
                                                              Logic.eq_rect_r
                                                                d0 (\_ ->
                                                                Logic.eq_rect
                                                                  ([])
                                                                  (Logic.eq_rect_r
                                                                    _UU03a3_
                                                                    (\_ ->
                                                                    Logic.eq_rect_r
                                                                     _UU03a0_
                                                                     (\_ ->
                                                                     Logic.eq_rect_r
                                                                     d0 (\_ ->
                                                                     Logic.eq_rect
                                                                     ([])
                                                                     (Logic.eq_rect_r
                                                                     _UU0393_0
                                                                     (\hm8 _ ->
                                                                     Logic.eq_rect_r
                                                                     _UU0394_0
                                                                     (\hm9 _ ->
                                                                     Logic.eq_rect_r
                                                                     d0
                                                                     (\hm10 _ ->
                                                                     Logic.eq_rect
                                                                     ([])
                                                                     (\x2 _ ->
                                                                     Logic.eq_rect_r
                                                                     _UU03a3_
                                                                     (\hm11 _ ->
                                                                     Logic.eq_rect_r
                                                                     _UU03a0_
                                                                     (\hm12 _ ->
                                                                     Logic.eq_rect_r
                                                                     d0
                                                                     (\_ _ ->
                                                                     Logic.eq_rect
                                                                     ([])
                                                                     (\_ _ ->
                                                                     Specif.Coq_existT
                                                                     hstr1
                                                                     (Specif.Coq_existT
                                                                     _UU0393_0
                                                                     (Specif.Coq_existT
                                                                     _UU0394_0
                                                                     (Specif.Coq_existT
                                                                     hstr7
                                                                     ((,) ((,)
                                                                     __ hm3)
                                                                     hstr11)))))
                                                                     ns2 x2 __)
                                                                     d hm12 __)
                                                                     _UU0394_
                                                                     hm11 __)
                                                                     _UU0393_
                                                                     hm10 __)
                                                                     ns1 x1 __)
                                                                     hstr6 hm9
                                                                     __) l2
                                                                     hm8 __)
                                                                     l1 hm7
                                                                     __) ns2)
                                                                     d)
                                                                     _UU0394_)
                                                                    _UU0393_
                                                                    __ __ __)
                                                                  ns1) hstr6)
                                                              l2) l1 __ __ __)
                                                          hstr13 hm6 __ __) l0
                                                        hm5 __ __) l hm4 __
                                                      __) hstr13) l0) l __ __)
                                              ns3 x0 __) seq3 __ __) seq2 __)
                                        seq1 __) ns3) seq3 __) ns6) ns5) ns4
                              __ __ __ __ __ x __ __ __}}}}) gHseq hm0) g hm}}}}}}}

struct_equiv_str_mergeR :: (([])
                           ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                           LntT.Coq_dir)) -> (([])
                           ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                           LntT.Coq_dir)) -> (([])
                           ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                           LntT.Coq_dir)) ->
                           (Structural_equivalence.Coq_struct_equiv_str 
                           a1) -> (Coq_merge a1) ->
                           Structural_equivalence.Coq_struct_equiv_str 
                           a1
struct_equiv_str_mergeR g1 =
  Datatypes.list_rect (\g2 g3 hs hm ->
    case hs of {
     Structural_equivalence.Coq_se_nil2 ->
      Logic.eq_rec ([])
        (Logic.eq_rect ([]) (\_ hm0 ->
          case hm0 of {
           Coq_merge_nilL ns1 ns2 ns3 ->
            Logic.eq_rec_r ([]) (\_ ->
              Logic.eq_rec_r ([]) (\_ ->
                Logic.eq_rec_r g3 (\_ _ ->
                  Logic.eq_rect_r ([]) (\_ _ ->
                    Structural_equivalence.Coq_se_nil2) g3 hm0 __) ns3) ns2)
              ns1 __ __ __ __;
           Coq_merge_nilR ns1 ns2 ns3 ->
            Logic.eq_rec_r ([]) (\_ ->
              Logic.eq_rec_r ([]) (\_ ->
                Logic.eq_rec_r g3 (\_ _ ->
                  Logic.eq_rect_r ([]) (\_ _ ->
                    Structural_equivalence.Coq_se_nil2) g3 hm0 __) ns3) ns2)
              ns1 __ __ __ __;
           Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d _ _ ns3 ns4
            ns5 ns6 seq1 seq2 seq3 x ->
            Logic.eq_rect_r ([]) (\_ ->
              Logic.eq_rect_r ([]) (\_ ->
                Logic.eq_rect_r g3 (\_ _ _ _ _ _ _ ->
                  Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                    Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                      Logic.eq_rec_r ((,) ((,)
                        (Datatypes.app _UU0393_ _UU03a3_)
                        (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                        Logic.eq_rect_r ((:) ((,) ((,)
                          (Datatypes.app _UU0393_ _UU03a3_)
                          (Datatypes.app _UU0394_ _UU03a0_)) d) ns3) (\_ _ ->
                          Logic.coq_False_rec) g3 hm0 __) seq3 __) seq2 __)
                    seq1 __) ns6) ns5) ns4 __ __ __ __ __ x __ __ __}) g2 hs
          hm) g2;
     Structural_equivalence.Coq_se_step2 _ _ d _UU0393_2 _UU0394_2 _ ns2 ns3
      ns4 h1 ->
      Logic.eq_rec_r ([]) (\_ ->
        Logic.eq_rec_r g2 (\_ _ _ ->
          Logic.eq_rect_r ((:) ((,) ((,) _UU0393_2 _UU0394_2) d) ns2)
            (\_ hm0 _ ->
            case hm0 of {
             Coq_merge_nilL ns0 ns5 ns6 ->
              Logic.eq_rec_r ([]) (\_ ->
                Logic.eq_rec_r ((:) ((,) ((,) _UU0393_2 _UU0394_2) d) ns2)
                  (\_ ->
                  Logic.eq_rec_r g3 (\_ _ ->
                    Logic.eq_rect_r ((:) ((,) ((,) _UU0393_2 _UU0394_2) d)
                      ns2) (\_ _ -> Logic.coq_False_rec) g3 hm0 __) ns6) ns5)
                ns0 __ __ __ __;
             Coq_merge_nilR ns0 ns5 ns6 ->
              Logic.eq_rec_r ([]) (\_ ->
                Logic.eq_rec_r ((:) ((,) ((,) _UU0393_2 _UU0394_2) d) ns2)
                  (\_ ->
                  Logic.eq_rec_r g3 (\_ _ ->
                    Logic.eq_rect_r ([]) (\_ _ -> Logic.coq_False_rec) g3 hm0
                      __) ns6) ns5) ns0 __ __ __ __;
             Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d0 _ _ ns5 ns6
              ns7 ns8 seq1 seq2 seq3 x ->
              Logic.eq_rect_r ([]) (\_ ->
                Logic.eq_rect_r ((:) ((,) ((,) _UU0393_2 _UU0394_2) d) ns2)
                  (\_ ->
                  Logic.eq_rect_r g3 (\_ _ _ _ _ _ _ ->
                    Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d0) (\_ ->
                      Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d0) (\_ ->
                        Logic.eq_rec_r ((,) ((,)
                          (Datatypes.app _UU0393_ _UU03a3_)
                          (Datatypes.app _UU0394_ _UU03a0_)) d0) (\_ ->
                          Logic.eq_rect_r ((:) ((,) ((,)
                            (Datatypes.app _UU0393_ _UU03a3_)
                            (Datatypes.app _UU0394_ _UU03a0_)) d0) ns5)
                            (\_ _ -> Logic.coq_False_rec) g3 hm0 __) seq3 __)
                        seq2 __) seq1 __) ns8) ns7) ns6 __ __ __ __ __ x __ __
                __}) g2 hs hm __) ns4) ns3 __ __ __ h1})
    (\a g2 iHG1 g3 g4 hs hm ->
    case hm of {
     Coq_merge_nilL ns1 ns2 ns3 ->
      Logic.eq_rec_r ((:) a g2) (\_ ->
        Logic.eq_rec_r g3 (\_ ->
          Logic.eq_rec_r g4 (\_ _ ->
            Logic.eq_rect_r g3 (\_ _ -> Logic.coq_False_rec) g4 hm __) ns3)
          ns2) ns1 __ __ __ __;
     Coq_merge_nilR ns1 ns2 ns3 ->
      Logic.eq_rec_r ((:) a g2) (\_ ->
        Logic.eq_rec_r g3 (\_ ->
          Logic.eq_rec_r g4 (\_ _ ->
            Logic.eq_rect_r ([]) (\hs0 hm0 _ ->
              Logic.eq_rect_r ((:) a g2) (\_ _ ->
                case hs0 of {
                 Structural_equivalence.Coq_se_nil2 -> Logic.coq_False_rec __;
                 Structural_equivalence.Coq_se_step2 _ _ _ _ _ _ _ ns4 ns5
                  h1 ->
                  Logic.eq_rec_r ((:) a g2) (\_ ->
                    Logic.eq_rec_r ([]) (\_ _ _ -> Logic.coq_False_rec) ns5)
                    ns4 __ __ __ h1}) g4 hm0 __) g3 hs hm __) ns3) ns2) ns1 __
        __ __ __;
     Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns1 ns2 ns3 ns4 ns5
      ns6 seq1 seq2 seq3 x ->
      Logic.eq_rect_r ((:) a g2) (\_ ->
        Logic.eq_rect_r g3 (\_ ->
          Logic.eq_rect_r g4 (\_ _ _ x0 _ _ _ ->
            Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
              Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                Logic.eq_rec_r ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                  (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                  Logic.eq_rect_r ((:) ((,) ((,) _UU03a3_ _UU03a0_) d) ns2)
                    (\hs0 hm0 _ ->
                    Logic.eq_rect_r ((:) ((,) ((,)
                      (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) ns3) (\hm1 _ ->
                      Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                        Logic.eq_rec_r ns1
                          (Logic.eq_rect_r ((,) ((,) _UU0393_ _UU0394_) d)
                            (\hm2 hs1 _ ->
                            Logic.eq_rect_r ns1 (\iHG2 hs2 hm3 _ ->
                              Structural_equivalence.Coq_se_step2 _UU03a3_
                              _UU03a0_ d (Datatypes.app _UU0393_ _UU03a3_)
                              (Datatypes.app _UU0394_ _UU03a0_) ns2 ns3 ((:)
                              ((,) ((,) _UU03a3_ _UU03a0_) d) ns2) ((:) ((,)
                              ((,) (Datatypes.app _UU0393_ _UU03a3_)
                              (Datatypes.app _UU0394_ _UU03a0_)) d) ns3)
                              (iHG2 ns2 ns3
                                (case hs2 of {
                                  Structural_equivalence.Coq_se_nil2 ->
                                   Logic.coq_False_rec __;
                                  Structural_equivalence.Coq_se_step2 _UU0393_1
                                   _UU0394_1 d0 _UU0393_2 _UU0394_2 ns0 ns7
                                   ns8 ns9 h1 ->
                                   Logic.eq_rec_r ((:) ((,) ((,) _UU0393_
                                     _UU0394_) d) ns1) (\_ ->
                                     Logic.eq_rec_r ((:) ((,) ((,) _UU03a3_
                                       _UU03a0_) d) ns2) (\_ _ h2 ->
                                       Logic.eq_rec_r _UU0393_2 (\_ ->
                                         Logic.eq_rec_r _UU0394_2 (\_ ->
                                           Logic.eq_rec_r d0 (\_ ->
                                             Logic.eq_rec_r ns7
                                               (Logic.eq_rect_r _UU0393_2
                                                 (\hm4 hs3 _ ->
                                                 Logic.eq_rect_r _UU0394_2
                                                   (\hs4 hm5 _ ->
                                                   Logic.eq_rect_r d0
                                                     (\hm6 hs5 _ _ ->
                                                     Logic.eq_rect_r ns7
                                                       (\hs6 hm7 x1 _ ->
                                                       Logic.eq_rec_r
                                                         _UU0393_1 (\_ ->
                                                         Logic.eq_rec_r
                                                           _UU0394_1 (\_ ->
                                                           Logic.eq_rec_r ns0
                                                             (Logic.eq_rect_r
                                                               _UU0393_1
                                                               (\hm8 hs7 _ ->
                                                               Logic.eq_rect_r
                                                                 _UU0394_1
                                                                 (\hs8 hm9 _ ->
                                                                 Logic.eq_rect_r
                                                                   ns0
                                                                   (\_ _ _ _ _ ->
                                                                   h2) ns1
                                                                   iHG2 x1 hm9
                                                                   hs8 __)
                                                                 _UU0394_ hs7
                                                                 hm8 __)
                                                               _UU0393_ hm7
                                                               hs6 __) ns1)
                                                           _UU0394_) _UU0393_
                                                         __ __) ns2 hs5 hm6 x0
                                                       __) d hm5 hs4 __ __)
                                                   _UU03a0_ hs3 hm4 __)
                                                 _UU03a3_ hm3 hs2 __) ns2) d)
                                           _UU03a0_) _UU03a3_ __ __ __) ns9)
                                     ns8 __ __ __ h1}) x0)) g2 iHG1 hs1 hm2 __)
                            a hm1 hs0 __) g2) a __) g4 hm0 __) g3 hs hm __)
                  seq3 __) seq2 __) seq1 __) ns6) ns5) ns4 __ __ __ __ __ x __
        __ __}) g1

contracted_nseq_merge_fwdR :: (([])
                              ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                              LntT.Coq_dir)) -> (([])
                              ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                              LntT.Coq_dir)) -> (([])
                              ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1)))
                              LntT.Coq_dir)) -> (Coq_merge a1) ->
                              (ContractedT.Coq_contracted_nseq
                              (LntT.PropF a1)) ->
                              ContractedT.Coq_contracted_nseq (LntT.PropF a1)
contracted_nseq_merge_fwdR g1 =
  Datatypes.list_rect (\g2 g3 hm hc ->
    case hm of {
     Coq_merge_nilL ns1 ns2 ns3 ->
      Logic.eq_rec_r ([]) (\_ ->
        Logic.eq_rec_r g2 (\_ ->
          Logic.eq_rec_r g3 (\_ _ ->
            Logic.eq_rect_r g2 (\hm0 _ ->
              case hc of {
               ContractedT.Coq_cont_nseq_nil ->
                Logic.eq_rec ([])
                  (Logic.eq_rect ([]) (\_ _ -> ContractedT.Coq_cont_nseq_nil)
                    g2 hm0 hc) g2;
               ContractedT.Coq_cont_nseq_cons _ _ _ _ h0 h1 ->
                Logic.coq_False_rec __ h0 h1}) g3 hm __) ns3) ns2) ns1 __ __
        __ __;
     Coq_merge_nilR ns1 ns2 ns3 ->
      Logic.eq_rec_r ([]) (\_ ->
        Logic.eq_rec_r g2 (\_ ->
          Logic.eq_rec_r g3 (\_ _ ->
            Logic.eq_rect_r ([]) (\hm0 hc0 _ ->
              Logic.eq_rect_r ([]) (\_ _ ->
                case hc0 of {
                 ContractedT.Coq_cont_nseq_nil ->
                  ContractedT.Coq_cont_nseq_nil;
                 ContractedT.Coq_cont_nseq_cons _ _ _ _ h h0 ->
                  Logic.coq_False_rec __ h h0}) g3 hm0 __) g2 hm hc __) ns3)
          ns2) ns1 __ __ __ __;
     Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d _ ns2 ns3 ns4 ns5
      ns6 seq1 seq2 seq3 x ->
      Logic.eq_rect_r ([]) (\_ ->
        Logic.eq_rect_r g2 (\_ ->
          Logic.eq_rect_r g3 (\_ _ _ _ _ _ _ ->
            Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
              Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                Logic.eq_rec_r ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                  (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                  Logic.eq_rect_r ((:) ((,) ((,) _UU03a3_ _UU03a0_) d) ns2)
                    (\hm0 hc0 _ ->
                    Logic.eq_rect_r ((:) ((,) ((,)
                      (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) ns3) (\_ _ ->
                      case hc0 of {
                       ContractedT.Coq_cont_nseq_nil -> Logic.coq_False_rec;
                       ContractedT.Coq_cont_nseq_cons _ _ _ _ h h0 ->
                        Logic.coq_False_rec __ h h0}) g3 hm0 __) g2 hm hc __)
                  seq3 __) seq2 __) seq1 __) ns6) ns5) ns4 __ __ __ __ __ x __
        __ __}) (\a g2 iHG1 g3 g4 hm hc ->
    case hm of {
     Coq_merge_nilL ns1 ns2 ns3 ->
      Logic.eq_rec_r ((:) a g2) (\_ ->
        Logic.eq_rec_r g3 (\_ ->
          Logic.eq_rec_r g4 (\_ _ ->
            Logic.eq_rect_r g3 (\_ _ -> Logic.coq_False_rec) g4 hm __) ns3)
          ns2) ns1 __ __ __ __;
     Coq_merge_nilR ns1 ns2 ns3 ->
      Logic.eq_rec_r ((:) a g2) (\_ ->
        Logic.eq_rec_r g3 (\_ ->
          Logic.eq_rec_r g4 (\_ _ ->
            Logic.eq_rect_r ([]) (\hm0 hc0 _ ->
              Logic.eq_rect_r ((:) a g2) (\_ _ ->
                case hc0 of {
                 ContractedT.Coq_cont_nseq_nil -> Logic.coq_False_rec __;
                 ContractedT.Coq_cont_nseq_cons s1 _ ns4 _ h h0 ->
                  Logic.eq_rec_r a (\_ ->
                    Logic.eq_rec_r g2 (\_ -> Logic.coq_False_rec) ns4) s1 __
                    __ h h0}) g4 hm0 __) g3 hm hc __) ns3) ns2) ns1 __ __ __
        __;
     Coq_merge_step _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d ns1 ns2 ns3 ns4 ns5
      ns6 seq1 seq2 seq3 x ->
      Logic.eq_rect_r ((:) a g2) (\_ ->
        Logic.eq_rect_r g3 (\_ ->
          Logic.eq_rect_r g4 (\_ _ _ x0 _ _ _ ->
            Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
              Logic.eq_rec_r ((,) ((,) _UU03a3_ _UU03a0_) d) (\_ ->
                Logic.eq_rec_r ((,) ((,) (Datatypes.app _UU0393_ _UU03a3_)
                  (Datatypes.app _UU0394_ _UU03a0_)) d) (\_ ->
                  Logic.eq_rect_r ((:) ((,) ((,) _UU03a3_ _UU03a0_) d) ns2)
                    (\hm0 hc0 _ ->
                    Logic.eq_rect_r ((:) ((,) ((,)
                      (Datatypes.app _UU0393_ _UU03a3_)
                      (Datatypes.app _UU0394_ _UU03a0_)) d) ns3) (\hm1 _ ->
                      Logic.eq_rec_r ((,) ((,) _UU0393_ _UU0394_) d) (\_ ->
                        Logic.eq_rec_r ns1
                          (Logic.eq_rect_r ((,) ((,) _UU0393_ _UU0394_) d)
                            (\hc1 hm2 _ ->
                            Logic.eq_rect_r ns1 (\iHG2 hc2 hm3 _ ->
                              case hm3 of {
                               Coq_merge_nilL ns0 ns7 ns8 ->
                                Logic.eq_rec_r ((:) ((,) ((,) _UU0393_
                                  _UU0394_) d) ns1) (\_ ->
                                  Logic.eq_rec_r ((:) ((,) ((,) _UU03a3_
                                    _UU03a0_) d) ns2) (\_ ->
                                    Logic.eq_rec_r ((:) ((,) ((,)
                                      (Datatypes.app _UU0393_ _UU03a3_)
                                      (Datatypes.app _UU0394_ _UU03a0_)) d)
                                      ns3) (\_ _ -> Logic.coq_False_rec) ns8)
                                    ns7) ns0 __ __ __ __;
                               Coq_merge_nilR ns0 ns7 ns8 ->
                                Logic.eq_rec_r ((:) ((,) ((,) _UU0393_
                                  _UU0394_) d) ns1) (\_ ->
                                  Logic.eq_rec_r ((:) ((,) ((,) _UU03a3_
                                    _UU03a0_) d) ns2) (\_ ->
                                    Logic.eq_rec_r ((:) ((,) ((,)
                                      (Datatypes.app _UU0393_ _UU03a3_)
                                      (Datatypes.app _UU0394_ _UU03a0_)) d)
                                      ns3) (\_ _ -> Logic.coq_False_rec) ns8)
                                    ns7) ns0 __ __ __ __;
                               Coq_merge_step _UU0393_0 _UU0394_0 _UU03a3_0
                                _UU03a0_0 d0 ns0 ns7 ns8 ns9 ns10 ns11 seq4
                                seq5 seq6 x1 ->
                                Logic.eq_rect_r ((:) ((,) ((,) _UU0393_
                                  _UU0394_) d) ns1) (\_ ->
                                  Logic.eq_rect_r ((:) ((,) ((,) _UU03a3_
                                    _UU03a0_) d) ns2) (\_ ->
                                    Logic.eq_rect_r ((:) ((,) ((,)
                                      (Datatypes.app _UU0393_ _UU03a3_)
                                      (Datatypes.app _UU0394_ _UU03a0_)) d)
                                      ns3) (\_ _ _ _ _ _ _ ->
                                      Logic.eq_rec ((,) ((,)
                                        (Datatypes.app _UU0393_ _UU03a3_)
                                        (Datatypes.app _UU0394_ _UU03a0_)) d)
                                        (\_ ->
                                        Logic.eq_rec_r ns8
                                          (Logic.eq_rec_r ((,) ((,) _UU0393_0
                                            _UU0394_0) d0) (\_ ->
                                            Logic.eq_rec_r ((,) ((,) _UU03a3_0
                                              _UU03a0_0) d0) (\_ ->
                                              Logic.eq_rec_r ((,) ((,)
                                                (Datatypes.app _UU0393_0
                                                  _UU03a3_0)
                                                (Datatypes.app _UU0394_0
                                                  _UU03a0_0)) d0) (\_ _ ->
                                                Logic.eq_rect_r ns8
                                                  (\hm4 x2 _ ->
                                                  Logic.eq_rec
                                                    (Datatypes.app _UU0393_
                                                      _UU03a3_) (\_ ->
                                                    Logic.eq_rec
                                                      (Datatypes.app _UU0394_
                                                        _UU03a0_) (\_ ->
                                                      Logic.eq_rec_r d0
                                                        (Logic.eq_rect_r d0
                                                          (\hc3 hm5 _ _ _ _ ->
                                                          Logic.eq_rec_r
                                                            _UU0393_0 (\_ ->
                                                            Logic.eq_rec_r
                                                              _UU0394_0 (\_ ->
                                                              Logic.eq_rec_r
                                                                ns0
                                                                (Logic.eq_rect_r
                                                                  _UU0393_0
                                                                  (\hc4 hm6 _ _ _ _ ->
                                                                  Logic.eq_rect_r
                                                                    _UU0394_0
                                                                    (\hc5 hm7 _ _ _ _ ->
                                                                    Logic.eq_rect_r
                                                                     ns0
                                                                     (\iHG3 hc6 x3 hm8 _ ->
                                                                     Logic.eq_rec_r
                                                                     _UU03a3_0
                                                                     (\_ ->
                                                                     Logic.eq_rec_r
                                                                     _UU03a0_0
                                                                     (\_ ->
                                                                     Logic.eq_rec_r
                                                                     ns7
                                                                     (Logic.eq_rect_r
                                                                     _UU03a3_0
                                                                     (\hc7 hm9 _ _ _ _ ->
                                                                     Logic.eq_rect_r
                                                                     _UU03a0_0
                                                                     (\hc8 hm10 _ _ _ _ ->
                                                                     Logic.eq_rect_r
                                                                     ns7
                                                                     (\hc9 _ x4 _ ->
                                                                     case hc9 of {
                                                                      ContractedT.Coq_cont_nseq_nil ->
                                                                     Logic.coq_False_rec
                                                                     __;
                                                                      ContractedT.Coq_cont_nseq_cons s1
                                                                     s2 ns12
                                                                     ns13 h
                                                                     h0 ->
                                                                     Logic.eq_rec_r
                                                                     ((,) ((,)
                                                                     _UU0393_0
                                                                     _UU0394_0)
                                                                     d0)
                                                                     (\_ ->
                                                                     Logic.eq_rec_r
                                                                     ns0
                                                                     (\_ ->
                                                                     Logic.eq_rec_r
                                                                     ((,) ((,)
                                                                     _UU03a3_0
                                                                     _UU03a0_0)
                                                                     d0)
                                                                     (\_ ->
                                                                     Logic.eq_rec_r
                                                                     ns7
                                                                     (\h2 h4 ->
                                                                     ContractedT.Coq_cont_nseq_cons
                                                                     ((,) ((,)
                                                                     (Datatypes.app
                                                                     _UU0393_0
                                                                     _UU03a3_0)
                                                                     (Datatypes.app
                                                                     _UU0394_0
                                                                     _UU03a0_0))
                                                                     d0) ((,)
                                                                     ((,)
                                                                     _UU03a3_0
                                                                     _UU03a0_0)
                                                                     d0) ns8
                                                                     ns7
                                                                     (ContractedT.contracted_seq_merge_app2R_rev
                                                                     _UU03a3_0
                                                                     _UU03a0_0
                                                                     _UU0393_0
                                                                     _UU0394_0
                                                                     d0 h2)
                                                                     (iHG3 ns7
                                                                     ns8 x4
                                                                     h4)) ns13)
                                                                     s2 __)
                                                                     ns12) s1
                                                                     __ __ h
                                                                     h0}) ns2
                                                                     hc8 hm10
                                                                     x3 __)
                                                                     _UU03a0_
                                                                     hc7 hm9
                                                                     __ __ __
                                                                     __)
                                                                     _UU03a3_
                                                                     hc6 hm8
                                                                     __ __ __
                                                                     __) ns2)
                                                                     _UU03a0_)
                                                                     _UU03a3_
                                                                     __ __)
                                                                     ns1 iHG2
                                                                     hc5 x2
                                                                     hm7 __)
                                                                    _UU0394_
                                                                    hc4 hm6 __
                                                                    __ __ __)
                                                                  _UU0393_ hc3
                                                                  hm5 __ __ __
                                                                  __) ns1)
                                                              _UU0394_)
                                                            _UU0393_ __ __) d
                                                          hc2 hm4 __ __ __ __)
                                                        d)
                                                      (Datatypes.app _UU0394_0
                                                        _UU03a0_0))
                                                    (Datatypes.app _UU0393_0
                                                      _UU03a3_0) __ __) ns3
                                                  hm3 x0 __) seq6 __ __) seq5
                                              __) seq4 __) ns3) seq6 __) ns11)
                                    ns10) ns9 __ __ __ __ __ x1 __ __ __}) g2
                              iHG1 hc1 hm2 __) a hc0 hm1 __) g2) a __) g4 hm0
                      __) g3 hm hc __) seq3 __) seq2 __) seq1 __) ns6) ns5)
        ns4 __ __ __ __ __ x __ __ __}) g1

