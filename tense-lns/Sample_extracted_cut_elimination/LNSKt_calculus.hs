module LNSKt_calculus where

import qualified Prelude
import qualified Datatypes
import qualified LNS
import qualified List
import qualified Logic
import qualified Specif
import qualified ContractedT
import qualified DdT
import qualified GenT
import qualified Gen_seq
import qualified Gen_tacs
import qualified Merge
import qualified Rules_EW
import qualified Rules_b1l
import qualified Rules_b1r
import qualified Rules_b2l
import qualified Rules_b2r
import qualified Rules_prop
import qualified Structural_equivalence
import qualified WeakenedT

__ :: any
__ = Prelude.error "Logical or arity value used"

data LNSKt_rules v =
   Coq_b2r (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod (LNS.Coq_seq v) LNS.Coq_dir))) (Datatypes.Coq_list
                                                              (Datatypes.Coq_prod
                                                              (LNS.Coq_seq v)
                                                              LNS.Coq_dir)) 
 (LNS.Coq_nslclrule (Datatypes.Coq_prod (LNS.Coq_seq v) LNS.Coq_dir)
 (Rules_b2r.Coq_b2rrules v))
 | Coq_b1r (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod (LNS.Coq_seq v) LNS.Coq_dir))) (Datatypes.Coq_list
                                                              (Datatypes.Coq_prod
                                                              (LNS.Coq_seq v)
                                                              LNS.Coq_dir)) 
 (LNS.Coq_nslclrule (Datatypes.Coq_prod (LNS.Coq_seq v) LNS.Coq_dir)
 (Rules_b1r.Coq_b1rrules v))
 | Coq_b2l (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod (LNS.Coq_seq v) LNS.Coq_dir))) (Datatypes.Coq_list
                                                              (Datatypes.Coq_prod
                                                              (LNS.Coq_seq v)
                                                              LNS.Coq_dir)) 
 (LNS.Coq_nslclrule (Datatypes.Coq_prod (LNS.Coq_seq v) LNS.Coq_dir)
 (Rules_b2l.Coq_b2lrules v))
 | Coq_b1l (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod (LNS.Coq_seq v) LNS.Coq_dir))) (Datatypes.Coq_list
                                                              (Datatypes.Coq_prod
                                                              (LNS.Coq_seq v)
                                                              LNS.Coq_dir)) 
 (LNS.Coq_nslclrule (Datatypes.Coq_prod (LNS.Coq_seq v) LNS.Coq_dir)
 (Rules_b1l.Coq_b1lrules v))
 | Coq_nEW (Datatypes.Coq_list
           (Datatypes.Coq_list
           (Datatypes.Coq_prod (LNS.Coq_seq v) LNS.Coq_dir))) (Datatypes.Coq_list
                                                              (Datatypes.Coq_prod
                                                              (LNS.Coq_seq v)
                                                              LNS.Coq_dir)) 
 (LNS.Coq_nslclrule (Datatypes.Coq_prod (LNS.Coq_seq v) LNS.Coq_dir)
 (Rules_EW.EW_rule v))
 | Coq_prop (Datatypes.Coq_list
            (Datatypes.Coq_list
            (Datatypes.Coq_prod
            (Gen_tacs.Coq_rel (Datatypes.Coq_list (LNS.PropF v)))
            LNS.Coq_dir))) (Datatypes.Coq_list
                           (Datatypes.Coq_prod
                           (Gen_tacs.Coq_rel
                           (Datatypes.Coq_list (LNS.PropF v))) LNS.Coq_dir)) 
 (LNS.Coq_nslcrule (Gen_tacs.Coq_rel (Datatypes.Coq_list (LNS.PropF v)))
 (Gen_seq.Coq_seqrule (LNS.PropF v) (Rules_prop.Coq_rs_prop v)))

type Coq_pf_LNSKt v = DdT.Coq_derrec (LNS.LNS v) (LNSKt_rules v) ()

type Coq_pfs_LNSKt v = DdT.Coq_dersrec (LNS.LNS v) (LNSKt_rules v) ()

coq_Id_InT :: (Datatypes.Coq_list
              (Datatypes.Coq_prod
              (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
              (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
              (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
              (LNS.PropF a1)) -> LNS.Coq_dir -> a1 -> (GenT.InT
              (LNS.PropF a1)) -> (GenT.InT (LNS.PropF a1)) -> Coq_pf_LNSKt 
              a1
coq_Id_InT gH _UU0393_ _UU0394_ d p hin1 hin2 =
  let {
   s = Gen_seq.coq_InT_seqext _UU0393_ _UU0394_ (LNS.Var p) (LNS.Var p) hin1
         hin2}
  in
  case s of {
   Specif.Coq_existT h1 s0 ->
    case s0 of {
     Specif.Coq_existT h2 s1 ->
      case s1 of {
       Specif.Coq_existT h3 s2 ->
        case s2 of {
         Specif.Coq_existT h4 _ -> DdT.Coq_derI
          (List.map (LNS.nslcext gH d)
            (List.map (Gen_seq.seqext h1 h2 h3 h4) Datatypes.Coq_nil))
          (Datatypes.app gH (Datatypes.Coq_cons (Datatypes.Coq_pair
            (Datatypes.Coq_pair _UU0393_ _UU0394_) d) Datatypes.Coq_nil))
          (Coq_prop
          (List.map (LNS.nslcext gH d)
            (List.map (Gen_seq.seqext h1 h2 h3 h4) Datatypes.Coq_nil))
          (Datatypes.app gH (Datatypes.Coq_cons (Datatypes.Coq_pair
            (Datatypes.Coq_pair _UU0393_ _UU0394_) d) Datatypes.Coq_nil))
          (LNS.NSlcctxt
          (List.map (Gen_seq.seqext h1 h2 h3 h4) Datatypes.Coq_nil)
          (Datatypes.Coq_pair _UU0393_ _UU0394_) gH d
          (Gen_seq.seqrule_same
            (List.map (Gen_seq.seqext h1 h2 h3 h4) Datatypes.Coq_nil)
            (Gen_seq.seqext h1 h2 h3 h4 (Datatypes.Coq_pair
              (Datatypes.Coq_cons (LNS.Var p) Datatypes.Coq_nil)
              (Datatypes.Coq_cons (LNS.Var p) Datatypes.Coq_nil)))
            (Datatypes.Coq_pair _UU0393_ _UU0394_) (Gen_seq.Sctxt
            Datatypes.Coq_nil (Datatypes.Coq_pair (Datatypes.Coq_cons
            (LNS.Var p) Datatypes.Coq_nil) (Datatypes.Coq_cons (LNS.Var p)
            Datatypes.Coq_nil)) h1 h2 h3 h4 (Rules_prop.Id p)))))
          DdT.Coq_dlNil}}}}

coq_BotL_InT :: (Datatypes.Coq_list
                (Datatypes.Coq_prod
                (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                (LNS.PropF a1)) -> LNS.Coq_dir -> (GenT.InT (LNS.PropF a1))
                -> Coq_pf_LNSKt a1
coq_BotL_InT gH _UU0393_ _UU0394_ d hin =
  let {s = Gen_seq.coq_InT_seqextL _UU0393_ _UU0394_ LNS.Bot hin} in
  case s of {
   Specif.Coq_existT h1 s0 ->
    case s0 of {
     Specif.Coq_existT h2 _ -> DdT.Coq_derI
      (List.map (LNS.nslcext gH d)
        (List.map (Gen_seq.seqext h1 h2 _UU0394_ Datatypes.Coq_nil)
          Datatypes.Coq_nil))
      (Datatypes.app gH (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair _UU0393_ _UU0394_) d) Datatypes.Coq_nil))
      (Coq_prop
      (List.map (LNS.nslcext gH d)
        (List.map (Gen_seq.seqext h1 h2 _UU0394_ Datatypes.Coq_nil)
          Datatypes.Coq_nil))
      (Datatypes.app gH (Datatypes.Coq_cons (Datatypes.Coq_pair
        (Datatypes.Coq_pair _UU0393_ _UU0394_) d) Datatypes.Coq_nil))
      (LNS.NSlcctxt
      (List.map (Gen_seq.seqext h1 h2 _UU0394_ Datatypes.Coq_nil)
        Datatypes.Coq_nil) (Datatypes.Coq_pair _UU0393_ _UU0394_) gH d
      (Gen_seq.seqrule_same
        (List.map (Gen_seq.seqext h1 h2 _UU0394_ Datatypes.Coq_nil)
          Datatypes.Coq_nil)
        (Gen_seq.seqext h1 h2 _UU0394_ Datatypes.Coq_nil (Datatypes.Coq_pair
          (Datatypes.Coq_cons LNS.Bot Datatypes.Coq_nil) Datatypes.Coq_nil))
        (Datatypes.Coq_pair _UU0393_ _UU0394_) (Gen_seq.Sctxt
        Datatypes.Coq_nil (Datatypes.Coq_pair (Datatypes.Coq_cons LNS.Bot
        Datatypes.Coq_nil) Datatypes.Coq_nil) h1 h2 _UU0394_
        Datatypes.Coq_nil Rules_prop.BotL)))) DdT.Coq_dlNil}}

coq_LNSKt_exchL :: (LNS.LNS a1) -> (Coq_pf_LNSKt a1) -> (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                   (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir ->
                   (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                   (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                   (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                   (LNS.PropF a1)) -> DdT.Coq_pf (LNS.LNS a1)
                   (LNSKt_rules a1)
coq_LNSKt_exchL ns d g k s d0 _UU0393_1 _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ =
  DdT.derrec_all_indT (\_ _ -> Logic.coq_False_rect) (\h1 h2 h3 h4 h5 ->
    (case h3 of {
      Coq_b2r ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b2r u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b2r.gen_swapL_step_b2R_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6
             x7 x8 x9 x10)) c) ps __ x);
      Coq_b1r ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b1r u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b1r.gen_swapL_step_b1R_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6
             x7 x8 x9 x10)) c) ps __ x);
      Coq_b2l ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b2l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b2l.gen_swapL_step_b2L_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6
             x7 x8 x9 x10)) c) ps __ x);
      Coq_b1l ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b1l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b1l.gen_swapL_step_b1L_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6
             x7 x8 x9 x10)) c) ps __ x);
      Coq_nEW ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_nEW u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_EW.gen_swapL_step_EW_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7
             x8 x9 x10)) c) ps __ x);
      Coq_prop ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_prop u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_prop.gen_swapL_step_pr_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6
             x7 x8 x9 x10)) c) ps __ x)}) __ __) ns d g k s d0 _UU0393_1
    _UU0393_2 _UU0393_3 _UU0393_4 _UU0394_ __ __

coq_LNSKt_exchR :: (LNS.LNS a1) -> (Coq_pf_LNSKt a1) -> (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                   (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir ->
                   (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                   (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                   (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                   (LNS.PropF a1)) -> DdT.Coq_pf (LNS.LNS a1)
                   (LNSKt_rules a1)
coq_LNSKt_exchR ns d g k s d0 _UU0394_1 _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ =
  DdT.derrec_all_indT (\_ _ -> Logic.coq_False_rect) (\h1 h2 h3 h4 h5 ->
    (case h3 of {
      Coq_b2r ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b2r u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b2r.gen_swapR_step_b2R_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6
             x7 x8 x9 x10)) c) ps __ x);
      Coq_b1r ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b1r u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b1r.gen_swapR_step_b1R_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6
             x7 x8 x9 x10)) c) ps __ x);
      Coq_b2l ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b2l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b2l.gen_swapR_step_b2L_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6
             x7 x8 x9 x10)) c) ps __ x);
      Coq_b1l ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_b1l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b1l.gen_swapR_step_b1L_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6
             x7 x8 x9 x10)) c) ps __ x);
      Coq_nEW ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_nEW u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_EW.gen_swapR_step_EW_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6 x7
             x8 x9 x10)) c) ps __ x);
      Coq_prop ps c x -> (\_ _ ->
       Logic.eq_rect_r h1 (\_ ->
         Logic.eq_rect_r h2 (\x0 ->
           let {x1 = \u v x1 -> Coq_prop u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_prop.gen_swapR_step_pr_lc h1 h2 x0 h4 h5 x1 x2 x3 x4 x5 x6
             x7 x8 x9 x10)) c) ps __ x)}) __ __) ns d g k s d0 _UU0394_1
    _UU0394_2 _UU0394_3 _UU0394_4 _UU0393_ __ __

coq_LNSKt_weakR :: (LNS.LNS a1) -> (Coq_pf_LNSKt a1) -> (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                   (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir ->
                   (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                   (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                   (Datatypes.Coq_list (LNS.PropF a1)) -> DdT.Coq_pf
                   (LNS.LNS a1) (LNSKt_rules a1)
coq_LNSKt_weakR ns d g k s d0 _UU0393_ _UU0394_1 _UU0394_2 _UU0394_3 =
  DdT.derrec_all_indT (\_ _ -> Logic.coq_False_rect) (\ps concl x x0 x1 ->
    (case x of {
      Coq_b2r ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {x4 = \u v x4 -> Coq_b2r u v x4} in
           (\x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
           Rules_b2r.gen_weakR_step_b2R_lc ps concl x3 x0 x1 x4 x5 x6 x7 x8
             x9 x10 x11 x12)) c) ps0 __ x2);
      Coq_b1r ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {
            x4 = \_ ns0 d1 x4 x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
             coq_LNSKt_exchR ns0 d1 x4 x5 x6 x7 x8 x9 x10 x11 x12}
           in
           let {x5 = \u v x5 -> Coq_b1r u v x5} in
           (\x6 x7 x8 x9 x10 x11 x12 x13 _ _ ->
           Rules_b1r.gen_weakR_step_b1R_lc ps concl x4 x3 x0 x1 x5 x6 x7 x8
             x9 x10 x11 x12 x13)) c) ps0 __ x2);
      Coq_b2l ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {x4 = \u v x4 -> Coq_b2l u v x4} in
           (\x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
           Rules_b2l.gen_weakR_step_b2L_lc ps concl x3 x0 x1 x4 x5 x6 x7 x8
             x9 x10 x11 x12)) c) ps0 __ x2);
      Coq_b1l ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {x4 = \u v x4 -> Coq_b1l u v x4} in
           (\x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
           Rules_b1l.gen_weakR_step_b1L_lc ps concl x3 x0 x1 x4 x5 x6 x7 x8
             x9 x10 x11 x12)) c) ps0 __ x2);
      Coq_nEW ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {x4 = \u v x4 -> Coq_nEW u v x4} in
           (\x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
           Rules_EW.gen_weakR_step_EW_lc ps concl x3 x0 x1 x4 x5 x6 x7 x8 x9
             x10 x11 x12)) c) ps0 __ x2);
      Coq_prop ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {x4 = \u v x4 -> Coq_prop u v x4} in
           (\x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
           Rules_prop.gen_weakR_step_pr_lc ps concl x3 x0 x1 x4 x5 x6 x7 x8
             x9 x10 x11 x12)) c) ps0 __ x2)}) __ __) ns d g k s d0 _UU0393_
    _UU0394_1 _UU0394_2 _UU0394_3 __ __

coq_LNSKt_weakL :: (LNS.LNS a1) -> (Coq_pf_LNSKt a1) -> (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                   (Datatypes.Coq_list
                   (Datatypes.Coq_prod
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                   (Datatypes.Coq_prod (Datatypes.Coq_list (LNS.PropF a1))
                   (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir ->
                   (Datatypes.Coq_list (LNS.PropF a1)) -> (Datatypes.Coq_list
                   (LNS.PropF a1)) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                   (Datatypes.Coq_list (LNS.PropF a1)) -> DdT.Coq_pf
                   (LNS.LNS a1) (LNSKt_rules a1)
coq_LNSKt_weakL ns d g k s d0 _UU0393_1 _UU0393_2 _UU0393_3 _UU0394_ =
  DdT.derrec_all_indT (\_ _ -> Logic.coq_False_rect) (\ps concl x x0 x1 ->
    (case x of {
      Coq_b2r ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {x4 = \u v x4 -> Coq_b2r u v x4} in
           (\x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
           Rules_b2r.gen_weakL_step_b2R_lc ps concl x3 x0 x1 x4 x5 x6 x7 x8
             x9 x10 x11 x12)) c) ps0 __ x2);
      Coq_b1r ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {x4 = \u v x4 -> Coq_b1r u v x4} in
           (\x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
           Rules_b1r.gen_weakL_step_b1R_lc ps concl x3 x0 x1 x4 x5 x6 x7 x8
             x9 x10 x11 x12)) c) ps0 __ x2);
      Coq_b2l ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {x4 = \u v x4 -> Coq_b2l u v x4} in
           (\x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
           Rules_b2l.gen_weakL_step_b2L_lc ps concl x3 x0 x1 x4 x5 x6 x7 x8
             x9 x10 x11 x12)) c) ps0 __ x2);
      Coq_b1l ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {x4 = \u v x4 -> Coq_b1l u v x4} in
           (\x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
           Rules_b1l.gen_weakL_step_b1L_lc ps concl x3 x0 x1 x4 x5 x6 x7 x8
             x9 x10 x11 x12)) c) ps0 __ x2);
      Coq_nEW ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {x4 = \u v x4 -> Coq_nEW u v x4} in
           (\x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
           Rules_EW.gen_weakL_step_EW_lc ps concl x3 x0 x1 x4 x5 x6 x7 x8 x9
             x10 x11 x12)) c) ps0 __ x2);
      Coq_prop ps0 c x2 -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x3 ->
           let {x4 = \u v x4 -> Coq_prop u v x4} in
           (\x5 x6 x7 x8 x9 x10 x11 x12 _ _ ->
           Rules_prop.gen_weakL_step_pr_lc ps concl x3 x0 x1 x4 x5 x6 x7 x8
             x9 x10 x11 x12)) c) ps0 __ x2)}) __ __) ns d g k s d0 _UU0393_1
    _UU0393_2 _UU0393_3 _UU0394_ __ __

external_weakeningR :: (LNS.LNS a1) -> (Datatypes.Coq_list
                       (Datatypes.Coq_prod (LNS.Coq_seq a1) LNS.Coq_dir)) ->
                       (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt a1
external_weakeningR ns1 ns2 =
  Datatypes.list_rect (\ns3 hder ->
    Logic.eq_rect_r ns3 hder (Datatypes.app ns3 Datatypes.Coq_nil))
    (\a ns3 iHns2 ns4 hder ->
    Logic.eq_rect_r
      (Datatypes.app
        (Datatypes.app ns4 (Datatypes.Coq_cons a Datatypes.Coq_nil)) ns3)
      (iHns2 (Datatypes.app ns4 (Datatypes.Coq_cons a Datatypes.Coq_nil))
        (DdT.Coq_derI
        (List.map (LNS.nslclext ns4) (Datatypes.Coq_cons Datatypes.Coq_nil
          Datatypes.Coq_nil))
        (Datatypes.app ns4 (Datatypes.Coq_cons a Datatypes.Coq_nil)) (Coq_nEW
        (List.map (LNS.nslclext ns4) (Datatypes.Coq_cons Datatypes.Coq_nil
          Datatypes.Coq_nil))
        (Datatypes.app ns4 (Datatypes.Coq_cons a Datatypes.Coq_nil))
        (LNS.NSlclctxt (Datatypes.Coq_cons Datatypes.Coq_nil
        Datatypes.Coq_nil) (Datatypes.Coq_cons a Datatypes.Coq_nil) ns4
        (case a of {
          Datatypes.Coq_pair r d ->
           case r of {
            Datatypes.Coq_pair l l0 -> Rules_EW.EW l l0 d}})))
        (Logic.eq_rect_r ns4 (DdT.Coq_dlCons ns4 Datatypes.Coq_nil hder
          DdT.Coq_dlNil) (Datatypes.app ns4 Datatypes.Coq_nil))))
      (Datatypes.app ns4 (Datatypes.Coq_cons a ns3))) ns2 ns1

derrec_weakened_multiL :: (Datatypes.Coq_list (LNS.PropF a1)) ->
                          (Datatypes.Coq_list (LNS.PropF a1)) ->
                          (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir
                          -> (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (WeakenedT.Coq_weakened_multi (LNS.PropF a1)) ->
                          (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt a1
derrec_weakened_multiL _UU0393_1 _UU0393_2 _UU0394_ d x y hc hd =
  WeakenedT.weakened_multi_rect (\_ _ _ _ _ hd0 -> hd0)
    (\x0 y0 _ w hc0 iHHc xX yY _UU0394_0 d0 hd0 ->
    iHHc xX yY _UU0394_0 d0
      ((case w of {
         WeakenedT.Coq_weakened_I x1 y1 a b c -> (\_ _ ->
          Logic.eq_rect_r x0 (\_ ->
            Logic.eq_rect_r y0 (\_ _ ->
              Logic.eq_rect_r (Datatypes.app a c) (\w0 hd1 _ ->
                Logic.eq_rect_r (Datatypes.app a (Datatypes.app b c))
                  (\_ _ _ _ ->
                  coq_LNSKt_weakL
                    (Datatypes.app xX
                      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                        (Datatypes.Coq_pair (Datatypes.app a c) _UU0394_0)
                        d0) Datatypes.Coq_nil) yY)) hd1 xX yY
                    (Datatypes.Coq_pair (Datatypes.app a c) _UU0394_0) d0 a b
                    c _UU0394_0) y0 w0 hc0 iHHc __) x0 w hd0 __) y1) x1 __ __
            __)}) __ __)) _UU0393_1 _UU0393_2 hc x y _UU0394_ d hd

derrec_weakened_multiR :: (Datatypes.Coq_list (LNS.PropF a1)) ->
                          (Datatypes.Coq_list (LNS.PropF a1)) ->
                          (Datatypes.Coq_list (LNS.PropF a1)) -> LNS.Coq_dir
                          -> (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (WeakenedT.Coq_weakened_multi (LNS.PropF a1)) ->
                          (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt a1
derrec_weakened_multiR _UU0393_ _UU0394_1 _UU0394_2 d x y hc hd =
  WeakenedT.weakened_multi_rect (\_ _ _ _ _ hd0 -> hd0)
    (\x0 y0 _ w hc0 iHHc xX yY _UU0393_0 d0 hd0 ->
    iHHc xX yY _UU0393_0 d0
      ((case w of {
         WeakenedT.Coq_weakened_I x1 y1 a b c -> (\_ _ ->
          Logic.eq_rect_r x0 (\_ ->
            Logic.eq_rect_r y0 (\_ _ ->
              Logic.eq_rect_r (Datatypes.app a c) (\w0 hd1 _ ->
                Logic.eq_rect_r (Datatypes.app a (Datatypes.app b c))
                  (\_ _ _ _ ->
                  coq_LNSKt_weakR
                    (Datatypes.app xX
                      (Datatypes.app (Datatypes.Coq_cons (Datatypes.Coq_pair
                        (Datatypes.Coq_pair _UU0393_0 (Datatypes.app a c))
                        d0) Datatypes.Coq_nil) yY)) hd1 xX yY
                    (Datatypes.Coq_pair _UU0393_0 (Datatypes.app a c)) d0
                    _UU0393_0 a b c) y0 w0 hc0 iHHc __) x0 w hd0 __) y1) x1
            __ __ __)}) __ __)) _UU0394_1 _UU0394_2 hc x y _UU0393_ d hd

derrec_weakened_seqL :: (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir) ->
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir) ->
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (WeakenedT.Coq_weakened_seqL (LNS.PropF a1)
                        LNS.Coq_dir) -> (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt 
                        a1
derrec_weakened_seqL s1 s3 x y hc hd =
  (case hc of {
    WeakenedT.Coq_weak_seqL x0 y0 _UU0394_ d h -> (\_ _ ->
     Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair x0 _UU0394_) d)
       (\_ ->
       Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair y0 _UU0394_) d)
         (\h0 ->
         Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair x0 _UU0394_)
           d) (\hc0 hd0 ->
           Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair y0 _UU0394_)
             d) (\_ -> derrec_weakened_multiL x0 y0 _UU0394_ d x y h0 hd0) s3
             hc0) s1 hc hd) s3) s1 __ h)}) __ __

derrec_weakened_seqR :: (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir) ->
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir) ->
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (WeakenedT.Coq_weakened_seqR (LNS.PropF a1)
                        LNS.Coq_dir) -> (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt 
                        a1
derrec_weakened_seqR s1 s3 x y hc hd =
  (case hc of {
    WeakenedT.Coq_weak_seqR x0 y0 _UU0393_ d h -> (\_ _ ->
     Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ x0) d)
       (\_ ->
       Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ y0) d)
         (\h0 ->
         Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ x0)
           d) (\hc0 hd0 ->
           Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ y0)
             d) (\_ -> derrec_weakened_multiR _UU0393_ x0 y0 d x y h0 hd0) s3
             hc0) s1 hc hd) s3) s1 __ h)}) __ __

derrec_weakened_seq :: (Datatypes.Coq_prod
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_list (LNS.PropF a1))
                       (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir) ->
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_list (LNS.PropF a1))
                       (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir) ->
                       (Datatypes.Coq_list
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_list (LNS.PropF a1))
                       (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                       (Datatypes.Coq_list
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_list (LNS.PropF a1))
                       (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                       (WeakenedT.Coq_weakened_seq (LNS.PropF a1)
                       LNS.Coq_dir) -> (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt 
                       a1
derrec_weakened_seq s1 s2 x y hc hd =
  (case hc of {
    WeakenedT.Coq_weak_seq_baseL s0 s3 h -> (\_ _ ->
     Logic.eq_rect_r s1 (\_ ->
       Logic.eq_rect_r s2 (\h0 -> derrec_weakened_seqL s1 s2 x y h0 hd) s3)
       s0 __ h);
    WeakenedT.Coq_weak_seq_baseR s0 s3 h -> (\_ _ ->
     Logic.eq_rect_r s1 (\_ ->
       Logic.eq_rect_r s2 (\h0 -> derrec_weakened_seqR s1 s2 x y h0 hd) s3)
       s0 __ h);
    WeakenedT.Coq_weak_seq_baseLR s0 s3 s4 h h0 -> (\_ _ ->
     Logic.eq_rect_r s1 (\_ ->
       Logic.eq_rect_r s2 (\h1 h2 ->
         derrec_weakened_seqR s3 s2 x y h2
           (derrec_weakened_seqL s1 s3 x y h1 hd)) s4) s0 __ h h0)}) __ __

derrec_weakened_nseq_gen :: (Datatypes.Coq_list
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_list (LNS.PropF a1))
                            (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                            -> (Datatypes.Coq_list
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_list (LNS.PropF a1))
                            (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                            -> (Datatypes.Coq_list
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_list (LNS.PropF a1))
                            (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                            -> (Datatypes.Coq_list
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_list (LNS.PropF a1))
                            (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                            -> (WeakenedT.Coq_weakened_nseq (LNS.PropF a1)
                            LNS.Coq_dir) -> (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt
                            a1
derrec_weakened_nseq_gen s1 s2 x y hc =
  WeakenedT.weakened_nseq_rect (\_ _ hd -> hd)
    (\s3 s4 ns1 ns2 w _ iHHc x0 y0 hd ->
    let {
     hd0 = Logic.eq_rect (Datatypes.Coq_cons s3 (Datatypes.app ns1 y0)) hd
             (Datatypes.app (Datatypes.Coq_cons s3 Datatypes.Coq_nil)
               (Datatypes.app ns1 y0))}
    in
    let {hd1 = derrec_weakened_seq s3 s4 x0 (Datatypes.app ns1 y0) w hd0} in
    Logic.eq_rect_r
      (Datatypes.app
        (Datatypes.app x0 (Datatypes.Coq_cons s4 Datatypes.Coq_nil))
        (Datatypes.app ns2 y0))
      (iHHc (Datatypes.app x0 (Datatypes.Coq_cons s4 Datatypes.Coq_nil)) y0
        (Logic.eq_rect
          (Datatypes.app x0 (Datatypes.Coq_cons s4 (Datatypes.app ns1 y0)))
          hd1
          (Datatypes.app
            (Datatypes.app x0 (Datatypes.Coq_cons s4 Datatypes.Coq_nil))
            (Datatypes.app ns1 y0))))
      (Datatypes.app x0 (Datatypes.Coq_cons s4 (Datatypes.app ns2 y0)))) s1
    s2 hc x y

derrec_weakened_nseq :: (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (Datatypes.Coq_list
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_prod
                        (Datatypes.Coq_list (LNS.PropF a1))
                        (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                        (WeakenedT.Coq_weakened_nseq (LNS.PropF a1)
                        LNS.Coq_dir) -> (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt 
                        a1
derrec_weakened_nseq g h hc hd =
  Logic.eq_rect_r
    (Datatypes.app Datatypes.Coq_nil (Datatypes.app g Datatypes.Coq_nil))
    (derrec_weakened_nseq_gen h g Datatypes.Coq_nil Datatypes.Coq_nil hc
      (Logic.eq_rect_r h hd (Datatypes.app h Datatypes.Coq_nil))) g

derrec_struct_equiv_mergeR :: (LNS.LNS a1) -> (LNS.LNS a1) -> (LNS.LNS 
                              a1) ->
                              (Structural_equivalence.Coq_struct_equiv_str
                              a1) -> (Merge.Coq_merge a1) -> (Coq_pf_LNSKt
                              a1) -> Coq_pf_LNSKt a1
derrec_struct_equiv_mergeR g h gH hs hm hd =
  derrec_weakened_nseq gH h (Merge.merge_weakened_nseqR g h gH hs hm) hd

derrec_weakened_nseq_nslclext :: (Datatypes.Coq_list
                                 (Datatypes.Coq_prod
                                 (Datatypes.Coq_prod
                                 (Datatypes.Coq_list (LNS.PropF a1))
                                 (Datatypes.Coq_list (LNS.PropF a1)))
                                 LNS.Coq_dir)) -> (Datatypes.Coq_list
                                 (Datatypes.Coq_prod
                                 (Datatypes.Coq_prod
                                 (Datatypes.Coq_list (LNS.PropF a1))
                                 (Datatypes.Coq_list (LNS.PropF a1)))
                                 LNS.Coq_dir)) -> (Datatypes.Coq_list
                                 (Datatypes.Coq_prod
                                 (Datatypes.Coq_prod
                                 (Datatypes.Coq_list (LNS.PropF a1))
                                 (Datatypes.Coq_list (LNS.PropF a1)))
                                 LNS.Coq_dir)) ->
                                 (WeakenedT.Coq_weakened_nseq (LNS.PropF a1)
                                 LNS.Coq_dir) -> (Coq_pf_LNSKt a1) ->
                                 Coq_pf_LNSKt a1
derrec_weakened_nseq_nslclext x y ns hw hd =
  let {hd0 = Logic.eq_rect_r x hd (Datatypes.app Datatypes.Coq_nil x)} in
  Logic.eq_rect (Datatypes.app Datatypes.Coq_nil y)
    (Logic.eq_rect (Datatypes.app Datatypes.Coq_nil (Datatypes.app y ns))
      (let {
        hd1 = Logic.eq_rect_r
                (Datatypes.app (Datatypes.app Datatypes.Coq_nil x) ns) hd0
                (Datatypes.app Datatypes.Coq_nil (Datatypes.app x ns))}
       in
       derrec_weakened_nseq_gen x y Datatypes.Coq_nil ns hw hd1)
      (Datatypes.app (Datatypes.app Datatypes.Coq_nil y) ns)) y

coq_LNSKt_contR_gen :: (LNS.LNS a1) -> (Coq_pf_LNSKt a1) ->
                       (Datatypes.Coq_list
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_list (LNS.PropF a1))
                       (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                       (Datatypes.Coq_list
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_list (LNS.PropF a1))
                       (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_list (LNS.PropF a1))
                       (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir ->
                       (Datatypes.Coq_list (LNS.PropF a1)) ->
                       (Datatypes.Coq_list (LNS.PropF a1)) ->
                       (Datatypes.Coq_list (LNS.PropF a1)) ->
                       (Datatypes.Coq_list (LNS.PropF a1)) -> (LNS.PropF 
                       a1) -> Datatypes.Coq_prod
                       (DdT.Coq_pf (LNS.LNS a1) (LNSKt_rules a1))
                       (DdT.Coq_pf (LNS.LNS a1) (LNSKt_rules a1))
coq_LNSKt_contR_gen ns d g k s d0 _UU0393_ _UU0394_1 _UU0394_2 _UU0394_3 a =
  DdT.derrec_all_indT (\_ _ -> Logic.coq_False_rect) (\ps concl h h1 h2 ->
    (case h of {
      Coq_b2r ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {x1 = \u v x1 -> Coq_b2r u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b2r.gen_contR_gen_step_b2R_lc ps concl x0 h1 h2 x1 x2 x3 x4
             x5 x6 x7 x8 x9 x10)) c) ps0 __ x);
      Coq_b1r ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {
            x1 = \_ ns0 d1 x1 x2 x3 x4 x5 x6 x7 x8 x9 _ _ ->
             coq_LNSKt_exchR ns0 d1 x1 x2 x3 x4 x5 x6 x7 x8 x9}
           in
           let {x2 = \u v x2 -> Coq_b1r u v x2} in
           (\x3 x4 x5 x6 x7 x8 x9 x10 x11 _ _ ->
           Rules_b1r.gen_contR_gen_step_b1R_lc ps concl x1 x0 h1 h2 x2 x3 x4
             x5 x6 x7 x8 x9 x10 x11)) c) ps0 __ x);
      Coq_b2l ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {x1 = \u v x1 -> Coq_b2l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b2l.gen_contR_gen_step_b2L_lc ps concl x0 h1 h2 x1 x2 x3 x4
             x5 x6 x7 x8 x9 x10)) c) ps0 __ x);
      Coq_b1l ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {x1 = \u v x1 -> Coq_b1l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b1l.gen_contR_gen_step_b1L_lc ps concl x0 h1 h2 x1 x2 x3 x4
             x5 x6 x7 x8 x9 x10)) c) ps0 __ x);
      Coq_nEW ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {x1 = \u v x1 -> Coq_nEW u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_EW.gen_contR_gen_step_EW_lc ps concl x0 h1 h2 x1 x2 x3 x4 x5
             x6 x7 x8 x9 x10)) c) ps0 __ x);
      Coq_prop ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {
            x1 = \ns0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
             coq_LNSKt_exchR ns0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10}
           in
           let {x2 = \u v x2 -> Coq_prop u v x2} in
           (\x3 x4 x5 x6 x7 x8 x9 x10 x11 _ _ ->
           Rules_prop.gen_contR_gen_step_pr_lc ps concl x1 x0 h1 h2 x2 x3 x4
             x5 x6 x7 x8 x9 x10 x11)) c) ps0 __ x)}) __ __) ns d g k s d0
    _UU0393_ _UU0394_1 _UU0394_2 _UU0394_3 a __ __

coq_LNSKt_contL_gen :: (LNS.LNS a1) -> (Coq_pf_LNSKt a1) ->
                       (Datatypes.Coq_list
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_list (LNS.PropF a1))
                       (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                       (Datatypes.Coq_list
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_list (LNS.PropF a1))
                       (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)) ->
                       (Datatypes.Coq_prod
                       (Datatypes.Coq_list (LNS.PropF a1))
                       (Datatypes.Coq_list (LNS.PropF a1))) -> LNS.Coq_dir ->
                       (Datatypes.Coq_list (LNS.PropF a1)) ->
                       (Datatypes.Coq_list (LNS.PropF a1)) ->
                       (Datatypes.Coq_list (LNS.PropF a1)) -> (LNS.PropF 
                       a1) -> (Datatypes.Coq_list (LNS.PropF a1)) ->
                       Datatypes.Coq_prod
                       (DdT.Coq_pf (LNS.LNS a1) (LNSKt_rules a1))
                       (DdT.Coq_pf (LNS.LNS a1) (LNSKt_rules a1))
coq_LNSKt_contL_gen ns d g k s d0 _UU0393_1 _UU0393_2 _UU0393_3 a _UU0394_ =
  DdT.derrec_all_indT (\_ _ -> Logic.coq_False_rect) (\ps concl h h1 h2 ->
    (case h of {
      Coq_b2r ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {x1 = \u v x1 -> Coq_b2r u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b2r.gen_contL_gen_step_b2R_lc ps concl x0 h1 h2 x1 x2 x3 x4
             x5 x6 x7 x8 x9 x10)) c) ps0 __ x);
      Coq_b1r ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {x1 = \u v x1 -> Coq_b1r u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b1r.gen_contL_gen_step_b1R_lc ps concl x0 h1 h2 x1 x2 x3 x4
             x5 x6 x7 x8 x9 x10)) c) ps0 __ x);
      Coq_b2l ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {x1 = \u v x1 -> Coq_b2l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b2l.gen_contL_gen_step_b2L_lc ps concl x0 h1 h2 x1 x2 x3 x4
             x5 x6 x7 x8 x9 x10)) c) ps0 __ x);
      Coq_b1l ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {x1 = \u v x1 -> Coq_b1l u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_b1l.gen_contL_gen_step_b1L_lc ps concl x0 h1 h2 x1 x2 x3 x4
             x5 x6 x7 x8 x9 x10)) c) ps0 __ x);
      Coq_nEW ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {x1 = \u v x1 -> Coq_nEW u v x1} in
           (\x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
           Rules_EW.gen_contL_gen_step_EW_lc ps concl x0 h1 h2 x1 x2 x3 x4 x5
             x6 x7 x8 x9 x10)) c) ps0 __ x);
      Coq_prop ps0 c x -> (\_ _ ->
       Logic.eq_rect_r ps (\_ ->
         Logic.eq_rect_r concl (\x0 ->
           let {
            x1 = \ns0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 _ _ ->
             coq_LNSKt_exchL ns0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10}
           in
           let {x2 = \u v x2 -> Coq_prop u v x2} in
           (\x3 x4 x5 x6 x7 x8 x9 x10 x11 _ _ ->
           Rules_prop.gen_contL_gen_step_pr_lc ps concl x1 x0 h1 h2 x2 x3 x4
             x5 x6 x7 x8 x9 x10 x11)) c) ps0 __ x)}) __ __) ns d g k s d0
    _UU0393_1 _UU0393_2 _UU0393_3 a _UU0394_ __ __

derrec_contracted_multiL :: (Datatypes.Coq_list (LNS.PropF a1)) ->
                            (Datatypes.Coq_list (LNS.PropF a1)) ->
                            (Datatypes.Coq_list (LNS.PropF a1)) ->
                            LNS.Coq_dir -> (Datatypes.Coq_list
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_list (LNS.PropF a1))
                            (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                            -> (Datatypes.Coq_list
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_list (LNS.PropF a1))
                            (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                            -> (ContractedT.Coq_contracted_multi
                            (LNS.PropF a1)) -> (Coq_pf_LNSKt a1) ->
                            Coq_pf_LNSKt a1
derrec_contracted_multiL _UU0393_1 _UU0393_2 _UU0394_ d x y hc hd =
  ContractedT.contracted_multi_rect (\_ _ _ _ _ hd0 -> hd0)
    (\x0 y0 _ c hc0 iHHc xX yY _UU0394_0 d0 hd0 ->
    iHHc xX yY _UU0394_0 d0
      ((case c of {
         ContractedT.Coq_contracted_genL_I a x1 y1 a0 b c0 -> (\_ _ ->
          Logic.eq_rect_r x0 (\_ ->
            Logic.eq_rect_r y0 (\_ _ ->
              Logic.eq_rect_r
                (Datatypes.app a0
                  (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                    (Datatypes.app b
                      (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                        c0)))) (\c1 hd1 _ ->
                Logic.eq_rect_r
                  (Datatypes.app a0
                    (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                      (Datatypes.app b c0))) (\_ _ _ _ ->
                  let {
                   ns = Datatypes.app xX
                          (Datatypes.app (Datatypes.Coq_cons
                            (Datatypes.Coq_pair (Datatypes.Coq_pair
                            (Datatypes.app a0
                              (Datatypes.app (Datatypes.Coq_cons a
                                Datatypes.Coq_nil)
                                (Datatypes.app b
                                  (Datatypes.app (Datatypes.Coq_cons a
                                    Datatypes.Coq_nil) c0)))) _UU0394_0) d0)
                            Datatypes.Coq_nil) yY)}
                  in
                  let {
                   s = Datatypes.Coq_pair
                    (Datatypes.app a0
                      (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                        (Datatypes.app b
                          (Datatypes.app (Datatypes.Coq_cons a
                            Datatypes.Coq_nil) c0)))) _UU0394_0}
                  in
                  case coq_LNSKt_contL_gen ns hd1 xX yY s d0 a0 b c0 a
                         _UU0394_0 of {
                   Datatypes.Coq_pair x2 _ -> x2}) y0 c1 hc0 iHHc __) x0 c
                hd0 __) y1) x1 __ __ __);
         ContractedT.Coq_contracted_genR_I a x1 y1 a0 b c0 -> (\_ _ ->
          Logic.eq_rect_r x0 (\_ ->
            Logic.eq_rect_r y0 (\_ _ ->
              Logic.eq_rect_r
                (Datatypes.app a0
                  (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                    (Datatypes.app b
                      (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                        c0)))) (\c1 hd1 _ ->
                Logic.eq_rect_r
                  (Datatypes.app a0
                    (Datatypes.app b
                      (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                        c0))) (\_ _ _ _ ->
                  let {
                   ns = Datatypes.app xX
                          (Datatypes.app (Datatypes.Coq_cons
                            (Datatypes.Coq_pair (Datatypes.Coq_pair
                            (Datatypes.app a0
                              (Datatypes.app (Datatypes.Coq_cons a
                                Datatypes.Coq_nil)
                                (Datatypes.app b
                                  (Datatypes.app (Datatypes.Coq_cons a
                                    Datatypes.Coq_nil) c0)))) _UU0394_0) d0)
                            Datatypes.Coq_nil) yY)}
                  in
                  let {
                   s = Datatypes.Coq_pair
                    (Datatypes.app a0
                      (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                        (Datatypes.app b
                          (Datatypes.app (Datatypes.Coq_cons a
                            Datatypes.Coq_nil) c0)))) _UU0394_0}
                  in
                  case coq_LNSKt_contL_gen ns hd1 xX yY s d0 a0 b c0 a
                         _UU0394_0 of {
                   Datatypes.Coq_pair _ x2 -> x2}) y0 c1 hc0 iHHc __) x0 c
                hd0 __) y1) x1 __ __ __)}) __ __)) _UU0393_1 _UU0393_2 hc x y
    _UU0394_ d hd

derrec_contracted_multiR :: (Datatypes.Coq_list (LNS.PropF a1)) ->
                            (Datatypes.Coq_list (LNS.PropF a1)) ->
                            (Datatypes.Coq_list (LNS.PropF a1)) ->
                            LNS.Coq_dir -> (Datatypes.Coq_list
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_list (LNS.PropF a1))
                            (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                            -> (Datatypes.Coq_list
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_prod
                            (Datatypes.Coq_list (LNS.PropF a1))
                            (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                            -> (ContractedT.Coq_contracted_multi
                            (LNS.PropF a1)) -> (Coq_pf_LNSKt a1) ->
                            Coq_pf_LNSKt a1
derrec_contracted_multiR _UU0393_ _UU0394_1 _UU0394_2 d x y hc hd =
  ContractedT.contracted_multi_rect (\_ _ _ _ _ hd0 -> hd0)
    (\x0 y0 _ c hc0 iHHc xX yY _UU0393_0 d0 hd0 ->
    iHHc xX yY _UU0393_0 d0
      ((case c of {
         ContractedT.Coq_contracted_genL_I a x1 y1 a0 b c0 -> (\_ _ ->
          Logic.eq_rect_r x0 (\_ ->
            Logic.eq_rect_r y0 (\_ _ ->
              Logic.eq_rect_r
                (Datatypes.app a0
                  (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                    (Datatypes.app b
                      (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                        c0)))) (\c1 hd1 _ ->
                Logic.eq_rect_r
                  (Datatypes.app a0
                    (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                      (Datatypes.app b c0))) (\_ _ _ _ ->
                  let {
                   ns = Datatypes.app xX
                          (Datatypes.app (Datatypes.Coq_cons
                            (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                            (Datatypes.app a0
                              (Datatypes.app (Datatypes.Coq_cons a
                                Datatypes.Coq_nil)
                                (Datatypes.app b
                                  (Datatypes.app (Datatypes.Coq_cons a
                                    Datatypes.Coq_nil) c0))))) d0)
                            Datatypes.Coq_nil) yY)}
                  in
                  let {
                   s = Datatypes.Coq_pair _UU0393_0
                    (Datatypes.app a0
                      (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                        (Datatypes.app b
                          (Datatypes.app (Datatypes.Coq_cons a
                            Datatypes.Coq_nil) c0))))}
                  in
                  case coq_LNSKt_contR_gen ns hd1 xX yY s d0 _UU0393_0 a0 b
                         c0 a of {
                   Datatypes.Coq_pair x2 _ -> x2}) y0 c1 hc0 iHHc __) x0 c
                hd0 __) y1) x1 __ __ __);
         ContractedT.Coq_contracted_genR_I a x1 y1 a0 b c0 -> (\_ _ ->
          Logic.eq_rect_r x0 (\_ ->
            Logic.eq_rect_r y0 (\_ _ ->
              Logic.eq_rect_r
                (Datatypes.app a0
                  (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                    (Datatypes.app b
                      (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                        c0)))) (\c1 hd1 _ ->
                Logic.eq_rect_r
                  (Datatypes.app a0
                    (Datatypes.app b
                      (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                        c0))) (\_ _ _ _ ->
                  let {
                   ns = Datatypes.app xX
                          (Datatypes.app (Datatypes.Coq_cons
                            (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_0
                            (Datatypes.app a0
                              (Datatypes.app (Datatypes.Coq_cons a
                                Datatypes.Coq_nil)
                                (Datatypes.app b
                                  (Datatypes.app (Datatypes.Coq_cons a
                                    Datatypes.Coq_nil) c0))))) d0)
                            Datatypes.Coq_nil) yY)}
                  in
                  let {
                   s = Datatypes.Coq_pair _UU0393_0
                    (Datatypes.app a0
                      (Datatypes.app (Datatypes.Coq_cons a Datatypes.Coq_nil)
                        (Datatypes.app b
                          (Datatypes.app (Datatypes.Coq_cons a
                            Datatypes.Coq_nil) c0))))}
                  in
                  case coq_LNSKt_contR_gen ns hd1 xX yY s d0 _UU0393_0 a0 b
                         c0 a of {
                   Datatypes.Coq_pair _ x2 -> x2}) y0 c1 hc0 iHHc __) x0 c
                hd0 __) y1) x1 __ __ __)}) __ __)) _UU0394_1 _UU0394_2 hc x y
    _UU0393_ d hd

derrec_contracted_seqL :: (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)
                          -> (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)
                          -> (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (ContractedT.Coq_contracted_seqL (LNS.PropF a1)
                          LNS.Coq_dir) -> (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt
                          a1
derrec_contracted_seqL s1 s3 x y hc hd =
  (case hc of {
    ContractedT.Coq_cont_seqL x0 y0 _UU0394_ d h -> (\_ _ ->
     Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair x0 _UU0394_) d)
       (\_ ->
       Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair y0 _UU0394_) d)
         (\h0 ->
         Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair x0 _UU0394_)
           d) (\hc0 hd0 ->
           Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair y0 _UU0394_)
             d) (\_ -> derrec_contracted_multiL x0 y0 _UU0394_ d x y h0 hd0)
             s3 hc0) s1 hc hd) s3) s1 __ h)}) __ __

derrec_contracted_seqR :: (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)
                          -> (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir)
                          -> (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (ContractedT.Coq_contracted_seqR (LNS.PropF a1)
                          LNS.Coq_dir) -> (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt
                          a1
derrec_contracted_seqR s1 s3 x y hc hd =
  (case hc of {
    ContractedT.Coq_cont_seqR x0 y0 _UU0393_ d h -> (\_ _ ->
     Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ x0) d)
       (\_ ->
       Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ y0) d)
         (\h0 ->
         Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ x0)
           d) (\hc0 hd0 ->
           Logic.eq_rect (Datatypes.Coq_pair (Datatypes.Coq_pair _UU0393_ y0)
             d) (\_ -> derrec_contracted_multiR _UU0393_ x0 y0 d x y h0 hd0)
             s3 hc0) s1 hc hd) s3) s1 __ h)}) __ __

derrec_contracted_seq :: (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir) ->
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir) ->
                         (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> (Datatypes.Coq_list
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_prod
                         (Datatypes.Coq_list (LNS.PropF a1))
                         (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                         -> (ContractedT.Coq_contracted_seq (LNS.PropF a1)
                         LNS.Coq_dir) -> (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt 
                         a1
derrec_contracted_seq s1 s2 x y hc =
  ContractedT.contracted_seq_rect (\s3 s4 hc0 x0 y0 hd ->
    derrec_contracted_seqL s3 s4 x0 y0 hc0 hd) (\s3 s4 hc0 x0 y0 hd ->
    derrec_contracted_seqR s3 s4 x0 y0 hc0 hd)
    (\s3 s4 _ hc0 _ iHHc2 x0 y0 hd ->
    iHHc2 x0 y0 (derrec_contracted_seqL s3 s4 x0 y0 hc0 hd))
    (\s3 s4 _ hc0 _ iHHc2 x0 y0 hd ->
    iHHc2 x0 y0 (derrec_contracted_seqR s3 s4 x0 y0 hc0 hd)) s1 s2 hc x y

derrec_contracted_nseq_gen :: (Datatypes.Coq_list
                              (Datatypes.Coq_prod
                              (Datatypes.Coq_prod
                              (Datatypes.Coq_list (LNS.PropF a1))
                              (Datatypes.Coq_list (LNS.PropF a1)))
                              LNS.Coq_dir)) -> (Datatypes.Coq_list
                              (Datatypes.Coq_prod
                              (Datatypes.Coq_prod
                              (Datatypes.Coq_list (LNS.PropF a1))
                              (Datatypes.Coq_list (LNS.PropF a1)))
                              LNS.Coq_dir)) -> (Datatypes.Coq_list
                              (Datatypes.Coq_prod
                              (Datatypes.Coq_prod
                              (Datatypes.Coq_list (LNS.PropF a1))
                              (Datatypes.Coq_list (LNS.PropF a1)))
                              LNS.Coq_dir)) -> (Datatypes.Coq_list
                              (Datatypes.Coq_prod
                              (Datatypes.Coq_prod
                              (Datatypes.Coq_list (LNS.PropF a1))
                              (Datatypes.Coq_list (LNS.PropF a1)))
                              LNS.Coq_dir)) ->
                              (ContractedT.Coq_contracted_nseq (LNS.PropF a1)
                              LNS.Coq_dir) -> (Coq_pf_LNSKt a1) ->
                              Coq_pf_LNSKt a1
derrec_contracted_nseq_gen s1 s2 x y hc =
  ContractedT.contracted_nseq_rect (\_ _ hd -> hd)
    (\s3 s4 ns1 ns2 c _ iHHc x0 y0 hd ->
    let {
     hd0 = Logic.eq_rect (Datatypes.Coq_cons s3 (Datatypes.app ns1 y0)) hd
             (Datatypes.app (Datatypes.Coq_cons s3 Datatypes.Coq_nil)
               (Datatypes.app ns1 y0))}
    in
    let {hd1 = derrec_contracted_seq s3 s4 x0 (Datatypes.app ns1 y0) c hd0}
    in
    Logic.eq_rect_r
      (Datatypes.app
        (Datatypes.app x0 (Datatypes.Coq_cons s4 Datatypes.Coq_nil))
        (Datatypes.app ns2 y0))
      (iHHc (Datatypes.app x0 (Datatypes.Coq_cons s4 Datatypes.Coq_nil)) y0
        (Logic.eq_rect
          (Datatypes.app x0 (Datatypes.Coq_cons s4 (Datatypes.app ns1 y0)))
          hd1
          (Datatypes.app
            (Datatypes.app x0 (Datatypes.Coq_cons s4 Datatypes.Coq_nil))
            (Datatypes.app ns1 y0))))
      (Datatypes.app x0 (Datatypes.Coq_cons s4 (Datatypes.app ns2 y0)))) s1
    s2 hc x y

derrec_contracted_nseq :: (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (Datatypes.Coq_list
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_prod
                          (Datatypes.Coq_list (LNS.PropF a1))
                          (Datatypes.Coq_list (LNS.PropF a1))) LNS.Coq_dir))
                          -> (ContractedT.Coq_contracted_nseq (LNS.PropF a1)
                          LNS.Coq_dir) -> (Coq_pf_LNSKt a1) -> Coq_pf_LNSKt
                          a1
derrec_contracted_nseq g h hc hd =
  Logic.eq_rect_r
    (Datatypes.app Datatypes.Coq_nil (Datatypes.app g Datatypes.Coq_nil))
    (derrec_contracted_nseq_gen h g Datatypes.Coq_nil Datatypes.Coq_nil hc
      (Logic.eq_rect_r h hd (Datatypes.app h Datatypes.Coq_nil))) g

