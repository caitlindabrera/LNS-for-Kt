module LntT where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Gen_tacs

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_dir =
   Coq_fwd
 | Coq_bac

data PropF v =
   Var v
 | Bot
 | Imp (PropF v) (PropF v)
 | WBox (PropF v)
 | BBox (PropF v)

data Coq_princrule_pfc v =
   Id_pfc v
 | ImpR_pfc (PropF v) (PropF v)
 | ImpL_pfc (PropF v) (PropF v)
 | BotL_pfc

nslcext :: (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)) -> Coq_dir -> a1 ->
           Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)
nslcext g d seq =
  Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair seq d) Datatypes.Coq_nil)

data Coq_nslcrule w sr =
   NSlcctxt (Datatypes.Coq_list w) w (Datatypes.Coq_list (Datatypes.Coq_prod w Coq_dir)) 
 Coq_dir sr

coq_NSlcctxt_nil :: (Datatypes.Coq_list (Datatypes.Coq_prod a1 Coq_dir)) -> Coq_dir -> a1
                    -> a2 -> Coq_nslcrule a1 a2
coq_NSlcctxt_nil g d c h =
  NSlcctxt Datatypes.Coq_nil c g d h

coq_NSlcctxt' :: (Datatypes.Coq_list a1) -> a1 -> (Datatypes.Coq_list
                 (Datatypes.Coq_prod a1 Coq_dir)) -> Coq_dir -> a2 -> Coq_nslcrule 
                 a1 a2
coq_NSlcctxt' ps c g d x =
  Logic.eq_rect (nslcext g d c) (NSlcctxt ps c g d x)
    (Datatypes.app g (Datatypes.Coq_cons (Datatypes.Coq_pair c d) Datatypes.Coq_nil))

nslclext :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> Datatypes.Coq_list a1
nslclext =
  Datatypes.app

data Coq_nslclrule w sr =
   NSlclctxt (Datatypes.Coq_list (Datatypes.Coq_list w)) (Datatypes.Coq_list w) (Datatypes.Coq_list
                                                                                w) 
 sr

coq_NSlclctxt' :: (Datatypes.Coq_list (Datatypes.Coq_list a1)) -> (Datatypes.Coq_list 
                  a1) -> (Datatypes.Coq_list a1) -> a2 -> Coq_nslclrule a1 a2
coq_NSlclctxt' ps c g x =
  Logic.eq_rect (nslclext g c) (NSlclctxt ps c g x) (Datatypes.app g c)

princrule_pfc_LT :: (Datatypes.Coq_list
                    (Gen_tacs.Coq_rel (Datatypes.Coq_list (PropF a1)))) ->
                    (Datatypes.Coq_list (PropF a1)) -> (Datatypes.Coq_list (PropF a1)) ->
                    (Coq_princrule_pfc a1) -> Datatypes.Coq_sum () (PropF a1)
princrule_pfc_LT ps _UU0393_ _UU0394_ p =
  (case p of {
    Id_pfc p0 -> (\_ _ ->
     Logic.eq_rec Datatypes.Coq_nil (\_ ->
       Logic.eq_rec (Datatypes.Coq_cons (Var p0) Datatypes.Coq_nil) (\_ ->
         Logic.eq_rec (Datatypes.Coq_cons (Var p0) Datatypes.Coq_nil) (Datatypes.Coq_inr
           (Var p0)) _UU0394_) _UU0393_ __) ps __);
    ImpR_pfc p2 b -> (\_ _ ->
     Logic.eq_rec (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_cons p2
       Datatypes.Coq_nil) (Datatypes.Coq_cons (Imp p2 b) (Datatypes.Coq_cons b
       Datatypes.Coq_nil))) Datatypes.Coq_nil) (\_ ->
       Logic.eq_rec Datatypes.Coq_nil (\_ ->
         Logic.eq_rec (Datatypes.Coq_cons (Imp p2 b) Datatypes.Coq_nil) (Datatypes.Coq_inl
           __) _UU0394_) _UU0393_ __) ps __);
    ImpL_pfc a b -> (\_ _ ->
     Logic.eq_rec (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_cons (Imp a b)
       (Datatypes.Coq_cons b Datatypes.Coq_nil)) Datatypes.Coq_nil) (Datatypes.Coq_cons
       (Datatypes.Coq_pair (Datatypes.Coq_cons (Imp a b) Datatypes.Coq_nil)
       (Datatypes.Coq_cons a Datatypes.Coq_nil)) Datatypes.Coq_nil)) (\_ ->
       Logic.eq_rec (Datatypes.Coq_cons (Imp a b) Datatypes.Coq_nil) (\_ ->
         Logic.eq_rec Datatypes.Coq_nil (Datatypes.Coq_inr (Imp a b)) _UU0394_) _UU0393_
         __) ps __);
    BotL_pfc -> (\_ _ ->
     Logic.eq_rec Datatypes.Coq_nil (\_ ->
       Logic.eq_rec (Datatypes.Coq_cons Bot Datatypes.Coq_nil) (\_ ->
         Logic.eq_rec Datatypes.Coq_nil (Datatypes.Coq_inr Bot) _UU0394_) _UU0393_ __) ps
       __)}) __ __

princrule_pfc_RT :: (Datatypes.Coq_list
                    (Gen_tacs.Coq_rel (Datatypes.Coq_list (PropF a1)))) ->
                    (Datatypes.Coq_list (PropF a1)) -> (Datatypes.Coq_list (PropF a1)) ->
                    (Coq_princrule_pfc a1) -> Datatypes.Coq_sum () (PropF a1)
princrule_pfc_RT ps _UU0393_ _UU0394_ p =
  (case p of {
    Id_pfc p0 -> (\_ _ ->
     Logic.eq_rec Datatypes.Coq_nil (\_ ->
       Logic.eq_rec (Datatypes.Coq_cons (Var p0) Datatypes.Coq_nil) (\_ ->
         Logic.eq_rec (Datatypes.Coq_cons (Var p0) Datatypes.Coq_nil) (Datatypes.Coq_inr
           (Var p0)) _UU0394_) _UU0393_ __) ps __);
    ImpR_pfc a b -> (\_ _ ->
     Logic.eq_rec (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_cons a
       Datatypes.Coq_nil) (Datatypes.Coq_cons (Imp a b) (Datatypes.Coq_cons b
       Datatypes.Coq_nil))) Datatypes.Coq_nil) (\_ ->
       Logic.eq_rec Datatypes.Coq_nil (\_ ->
         Logic.eq_rec (Datatypes.Coq_cons (Imp a b) Datatypes.Coq_nil) (Datatypes.Coq_inr
           (Imp a b)) _UU0394_) _UU0393_ __) ps __);
    ImpL_pfc p2 b -> (\_ _ ->
     Logic.eq_rec (Datatypes.Coq_cons (Datatypes.Coq_pair (Datatypes.Coq_cons (Imp p2 b)
       (Datatypes.Coq_cons b Datatypes.Coq_nil)) Datatypes.Coq_nil) (Datatypes.Coq_cons
       (Datatypes.Coq_pair (Datatypes.Coq_cons (Imp p2 b) Datatypes.Coq_nil)
       (Datatypes.Coq_cons p2 Datatypes.Coq_nil)) Datatypes.Coq_nil)) (\_ ->
       Logic.eq_rec (Datatypes.Coq_cons (Imp p2 b) Datatypes.Coq_nil) (\_ ->
         Logic.eq_rec Datatypes.Coq_nil (Datatypes.Coq_inl __) _UU0394_) _UU0393_ __) ps
       __);
    BotL_pfc -> (\_ _ ->
     Logic.eq_rec Datatypes.Coq_nil (\_ ->
       Logic.eq_rec (Datatypes.Coq_cons Bot Datatypes.Coq_nil) (\_ ->
         Logic.eq_rec Datatypes.Coq_nil (Datatypes.Coq_inl __) _UU0394_) _UU0393_ __) ps
       __)}) __ __

type Coq_rules_L_oeT w rules =
  (Datatypes.Coq_list (Gen_tacs.Coq_rel (Datatypes.Coq_list w))) -> (Datatypes.Coq_list 
  w) -> (Datatypes.Coq_list w) -> (Datatypes.Coq_list w) -> rules -> Datatypes.Coq_sum 
  () ()

type Coq_rules_R_oeT w rules =
  (Datatypes.Coq_list (Gen_tacs.Coq_rel (Datatypes.Coq_list w))) -> (Datatypes.Coq_list 
  w) -> (Datatypes.Coq_list w) -> (Datatypes.Coq_list w) -> rules -> Datatypes.Coq_sum 
  () ()

princrule_pfc_L_oeT :: (Datatypes.Coq_list
                       (Gen_tacs.Coq_rel (Datatypes.Coq_list (PropF a1)))) ->
                       (Datatypes.Coq_list (PropF a1)) -> (Datatypes.Coq_list (PropF a1))
                       -> (Datatypes.Coq_list (PropF a1)) -> (Coq_princrule_pfc a1) ->
                       Datatypes.Coq_sum () ()
princrule_pfc_L_oeT ps x y _UU0394_ h =
  let {h0 = princrule_pfc_LT ps (Datatypes.app x y) _UU0394_ h} in
  case h0 of {
   Datatypes.Coq_inl _ -> Datatypes.Coq_inl __;
   Datatypes.Coq_inr h1 ->
    let {h2 = Gen_tacs.app_eq_unitT x y h1} in
    case h2 of {
     Datatypes.Coq_inl _ -> Datatypes.Coq_inl __;
     Datatypes.Coq_inr _ -> Datatypes.Coq_inr __}}

princrule_pfc_R_oeT :: (Datatypes.Coq_list
                       (Gen_tacs.Coq_rel (Datatypes.Coq_list (PropF a1)))) ->
                       (Datatypes.Coq_list (PropF a1)) -> (Datatypes.Coq_list (PropF a1))
                       -> (Datatypes.Coq_list (PropF a1)) -> (Coq_princrule_pfc a1) ->
                       Datatypes.Coq_sum () ()
princrule_pfc_R_oeT ps x y _UU0393_ h =
  let {h0 = princrule_pfc_RT ps _UU0393_ (Datatypes.app x y) h} in
  case h0 of {
   Datatypes.Coq_inl _ -> Datatypes.prod_rec (\_ _ -> Datatypes.Coq_inl __) __;
   Datatypes.Coq_inr h1 ->
    let {h2 = Gen_tacs.app_eq_unitT x y h1} in
    Datatypes.sum_rec (\_ -> Logic.and_rec (\_ _ -> Datatypes.Coq_inl __)) (\_ ->
      Logic.and_rec (\_ _ -> Datatypes.Coq_inr __)) h2}

princrule_pfc_L_oe'T :: Coq_rules_L_oeT (PropF a1) (Coq_princrule_pfc a1)
princrule_pfc_L_oe'T =
  princrule_pfc_L_oeT

princrule_pfc_R_oe'T :: Coq_rules_R_oeT (PropF a1) (Coq_princrule_pfc a1)
princrule_pfc_R_oe'T =
  princrule_pfc_R_oeT

