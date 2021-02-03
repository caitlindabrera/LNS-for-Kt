module Lnt_gen_initT where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Specif
import qualified DdT
import qualified GenT
import qualified Gen_seq
import qualified Gen_tacs
import qualified LntT
import qualified Lntkt_exchT

coq_Id_InT :: (([]) ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1))) LntT.Coq_dir)) -> (([])
              (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> LntT.Coq_dir -> a1 -> (GenT.InT
              (LntT.PropF a1)) -> (GenT.InT (LntT.PropF a1)) -> DdT.Coq_derrec
              (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
              (Lntkt_exchT.LNSKt_rules a1) ()
coq_Id_InT gH _UU0393_ _UU0394_ d p hin1 hin2 =
  let {s = Gen_seq.coq_InT_seqext _UU0393_ _UU0394_ (LntT.Var p) (LntT.Var p) hin1 hin2} in
  case s of {
   Specif.Coq_existT h1 s0 ->
    case s0 of {
     Specif.Coq_existT h2 s1 ->
      case s1 of {
       Specif.Coq_existT h3 s2 ->
        case s2 of {
         Specif.Coq_existT h4 _ -> DdT.Coq_derI
          (List.map (LntT.nslcext gH d) (List.map (Gen_seq.seqext h1 h2 h3 h4) ([])))
          (Datatypes.app gH ((:) ((,) ((,) _UU0393_ _UU0394_) d) ([]))) (Lntkt_exchT.Coq_prop
          (List.map (LntT.nslcext gH d) (List.map (Gen_seq.seqext h1 h2 h3 h4) ([])))
          (Datatypes.app gH ((:) ((,) ((,) _UU0393_ _UU0394_) d) ([]))) (LntT.NSlcctxt
          (List.map (Gen_seq.seqext h1 h2 h3 h4) ([])) ((,) _UU0393_ _UU0394_) gH d
          (Gen_seq.seqrule_same (List.map (Gen_seq.seqext h1 h2 h3 h4) ([]))
            (Gen_seq.seqext h1 h2 h3 h4 ((,) ((:) (LntT.Var p) ([])) ((:) (LntT.Var p) ([])))) ((,)
            _UU0393_ _UU0394_) (Gen_seq.Sctxt ([]) ((,) ((:) (LntT.Var p) ([])) ((:) (LntT.Var p)
            ([]))) h1 h2 h3 h4 (LntT.Id_pfc p))))) DdT.Coq_dlNil}}}}

coq_BotL_InT :: (([]) ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                (([]) (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> LntT.Coq_dir -> (GenT.InT
                (LntT.PropF a1)) -> DdT.Coq_derrec
                (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                (Lntkt_exchT.LNSKt_rules a1) ()
coq_BotL_InT gH _UU0393_ _UU0394_ d hin =
  let {s = Gen_seq.coq_InT_seqextL _UU0393_ _UU0394_ LntT.Bot hin} in
  case s of {
   Specif.Coq_existT h1 s0 ->
    case s0 of {
     Specif.Coq_existT h2 _ -> DdT.Coq_derI
      (List.map (LntT.nslcext gH d) (List.map (Gen_seq.seqext h1 h2 _UU0394_ ([])) ([])))
      (Datatypes.app gH ((:) ((,) ((,) _UU0393_ _UU0394_) d) ([]))) (Lntkt_exchT.Coq_prop
      (List.map (LntT.nslcext gH d) (List.map (Gen_seq.seqext h1 h2 _UU0394_ ([])) ([])))
      (Datatypes.app gH ((:) ((,) ((,) _UU0393_ _UU0394_) d) ([]))) (LntT.NSlcctxt
      (List.map (Gen_seq.seqext h1 h2 _UU0394_ ([])) ([])) ((,) _UU0393_ _UU0394_) gH d
      (Gen_seq.seqrule_same (List.map (Gen_seq.seqext h1 h2 _UU0394_ ([])) ([]))
        (Gen_seq.seqext h1 h2 _UU0394_ ([]) ((,) ((:) LntT.Bot ([])) ([]))) ((,) _UU0393_ _UU0394_)
        (Gen_seq.Sctxt ([]) ((,) ((:) LntT.Bot ([])) ([])) h1 h2 _UU0394_ ([]) LntT.BotL_pfc))))
      DdT.Coq_dlNil}}

