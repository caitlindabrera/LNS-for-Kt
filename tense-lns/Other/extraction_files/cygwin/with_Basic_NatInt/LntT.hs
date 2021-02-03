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

nslcext :: (([]) ((,) a1 Coq_dir)) -> Coq_dir -> a1 -> ([]) ((,) a1 Coq_dir)
nslcext g d seq =
  Datatypes.app g ((:) ((,) seq d) ([]))

data Coq_nslcrule w sr =
   NSlcctxt (([]) w) w (([]) ((,) w Coq_dir)) Coq_dir sr

coq_NSlcctxt_nil :: (([]) ((,) a1 Coq_dir)) -> Coq_dir -> a1 -> a2 ->
                    Coq_nslcrule a1 a2
coq_NSlcctxt_nil g d c h =
  NSlcctxt ([]) c g d h

coq_NSlcctxt' :: (([]) a1) -> a1 -> (([]) ((,) a1 Coq_dir)) -> Coq_dir -> a2
                 -> Coq_nslcrule a1 a2
coq_NSlcctxt' ps c g d x =
  Logic.eq_rect (nslcext g d c) (NSlcctxt ps c g d x)
    (Datatypes.app g ((:) ((,) c d) ([])))

nslclext :: (([]) a1) -> (([]) a1) -> ([]) a1
nslclext =
  Datatypes.app

data Coq_nslclrule w sr =
   NSlclctxt (([]) (([]) w)) (([]) w) (([]) w) sr

coq_NSlclctxt' :: (([]) (([]) a1)) -> (([]) a1) -> (([]) a1) -> a2 ->
                  Coq_nslclrule a1 a2
coq_NSlclctxt' ps c g x =
  Logic.eq_rect (nslclext g c) (NSlclctxt ps c g x) (Datatypes.app g c)

princrule_pfc_LT :: (([]) (Gen_tacs.Coq_rel (([]) (PropF a1)))) -> (([])
                    (PropF a1)) -> (([]) (PropF a1)) -> (Coq_princrule_pfc 
                    a1) -> Prelude.Either () (PropF a1)
princrule_pfc_LT ps _UU0393_ _UU0394_ p =
  case p of {
   Id_pfc p0 ->
    Logic.eq_rec ([]) (\_ ->
      Logic.eq_rec ((:) (Var p0) ([])) (\_ ->
        Logic.eq_rec ((:) (Var p0) ([])) (Prelude.Right (Var p0)) _UU0394_)
        _UU0393_ __) ps __;
   ImpR_pfc p2 b ->
    Logic.eq_rec ((:) ((,) ((:) p2 ([])) ((:) (Imp p2 b) ((:) b ([])))) ([]))
      (\_ ->
      Logic.eq_rec ([]) (\_ ->
        Logic.eq_rec ((:) (Imp p2 b) ([])) (Prelude.Left __) _UU0394_)
        _UU0393_ __) ps __;
   ImpL_pfc a b ->
    Logic.eq_rec ((:) ((,) ((:) (Imp a b) ((:) b ([]))) ([])) ((:) ((,) ((:)
      (Imp a b) ([])) ((:) a ([]))) ([]))) (\_ ->
      Logic.eq_rec ((:) (Imp a b) ([])) (\_ ->
        Logic.eq_rec ([]) (Prelude.Right (Imp a b)) _UU0394_) _UU0393_ __) ps
      __;
   BotL_pfc ->
    Logic.eq_rec ([]) (\_ ->
      Logic.eq_rec ((:) Bot ([])) (\_ ->
        Logic.eq_rec ([]) (Prelude.Right Bot) _UU0394_) _UU0393_ __) ps __}

princrule_pfc_RT :: (([]) (Gen_tacs.Coq_rel (([]) (PropF a1)))) -> (([])
                    (PropF a1)) -> (([]) (PropF a1)) -> (Coq_princrule_pfc 
                    a1) -> Prelude.Either () (PropF a1)
princrule_pfc_RT ps _UU0393_ _UU0394_ p =
  case p of {
   Id_pfc p0 ->
    Logic.eq_rec ([]) (\_ ->
      Logic.eq_rec ((:) (Var p0) ([])) (\_ ->
        Logic.eq_rec ((:) (Var p0) ([])) (Prelude.Right (Var p0)) _UU0394_)
        _UU0393_ __) ps __;
   ImpR_pfc a b ->
    Logic.eq_rec ((:) ((,) ((:) a ([])) ((:) (Imp a b) ((:) b ([])))) ([]))
      (\_ ->
      Logic.eq_rec ([]) (\_ ->
        Logic.eq_rec ((:) (Imp a b) ([])) (Prelude.Right (Imp a b)) _UU0394_)
        _UU0393_ __) ps __;
   ImpL_pfc p2 b ->
    Logic.eq_rec ((:) ((,) ((:) (Imp p2 b) ((:) b ([]))) ([])) ((:) ((,) ((:)
      (Imp p2 b) ([])) ((:) p2 ([]))) ([]))) (\_ ->
      Logic.eq_rec ((:) (Imp p2 b) ([])) (\_ ->
        Logic.eq_rec ([]) (Prelude.Left __) _UU0394_) _UU0393_ __) ps __;
   BotL_pfc ->
    Logic.eq_rec ([]) (\_ ->
      Logic.eq_rec ((:) Bot ([])) (\_ ->
        Logic.eq_rec ([]) (Prelude.Left __) _UU0394_) _UU0393_ __) ps __}

type Coq_rules_L_oeT w rules =
  (([]) (Gen_tacs.Coq_rel (([]) w))) -> (([]) w) -> (([]) w) -> (([]) 
  w) -> rules -> Prelude.Either () ()

type Coq_rules_R_oeT w rules =
  (([]) (Gen_tacs.Coq_rel (([]) w))) -> (([]) w) -> (([]) w) -> (([]) 
  w) -> rules -> Prelude.Either () ()

princrule_pfc_L_oeT :: (([]) (Gen_tacs.Coq_rel (([]) (PropF a1)))) -> (([])
                       (PropF a1)) -> (([]) (PropF a1)) -> (([]) (PropF a1))
                       -> (Coq_princrule_pfc a1) -> Prelude.Either () 
                       ()
princrule_pfc_L_oeT ps x y _UU0394_ h =
  let {h0 = princrule_pfc_LT ps (Datatypes.app x y) _UU0394_ h} in
  case h0 of {
   Prelude.Left _ -> Prelude.Left __;
   Prelude.Right h1 ->
    let {h2 = Gen_tacs.app_eq_unitT x y h1} in
    case h2 of {
     Prelude.Left _ -> Prelude.Left __;
     Prelude.Right _ -> Prelude.Right __}}

princrule_pfc_R_oeT :: (([]) (Gen_tacs.Coq_rel (([]) (PropF a1)))) -> (([])
                       (PropF a1)) -> (([]) (PropF a1)) -> (([]) (PropF a1))
                       -> (Coq_princrule_pfc a1) -> Prelude.Either () 
                       ()
princrule_pfc_R_oeT ps x y _UU0393_ h =
  let {h0 = princrule_pfc_RT ps _UU0393_ (Datatypes.app x y) h} in
  case h0 of {
   Prelude.Left _ -> Datatypes.prod_rec (\_ _ -> Prelude.Left __) __;
   Prelude.Right h1 ->
    let {h2 = Gen_tacs.app_eq_unitT x y h1} in
    Datatypes.sum_rec (\_ -> Logic.and_rec (\_ _ -> Prelude.Left __)) (\_ ->
      Logic.and_rec (\_ _ -> Prelude.Right __)) h2}

princrule_pfc_L_oe'T :: Coq_rules_L_oeT (PropF a1) (Coq_princrule_pfc a1)
princrule_pfc_L_oe'T =
  princrule_pfc_L_oeT

princrule_pfc_R_oe'T :: Coq_rules_R_oeT (PropF a1) (Coq_princrule_pfc a1)
princrule_pfc_R_oe'T =
  princrule_pfc_R_oeT

