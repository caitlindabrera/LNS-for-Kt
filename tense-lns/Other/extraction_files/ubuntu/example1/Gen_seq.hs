module Gen_seq where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Logic
import qualified Specif
import qualified GenT
import qualified Gen_tacs

__ :: any
__ = Prelude.error "Logical or arity value used"

seqext :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (Gen_tacs.Coq_rel (([]) a1)) -> (,)
          (([]) a1) (([]) a1)
seqext _UU0393_1 _UU0393_2 _UU0394_1 _UU0394_2 seq =
  case seq of {
   (,) u v -> (,) (Datatypes.app _UU0393_1 (Datatypes.app u _UU0393_2))
    (Datatypes.app _UU0394_1 (Datatypes.app v _UU0394_2))}

data Coq_seqrule w pr =
   Sctxt (([]) (Gen_tacs.Coq_rel (([]) w))) (Gen_tacs.Coq_rel (([]) w)) (([]) w) (([]) w) (([]) w) 
 (([]) w) pr

coq_Sctxt_e :: (([]) (Gen_tacs.Coq_rel (([]) a1))) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (([])
               a1) -> (([]) a1) -> (([]) a1) -> a2 -> Coq_seqrule a1 a2
coq_Sctxt_e ps u v _UU03a6_1 _UU03a6_2 _UU03a8_1 _UU03a8_2 h =
  Logic.eq_rect (seqext _UU03a6_1 _UU03a6_2 _UU03a8_1 _UU03a8_2 ((,) u v)) (Sctxt ps ((,) u v)
    _UU03a6_1 _UU03a6_2 _UU03a8_1 _UU03a8_2 h) ((,)
    (Datatypes.app _UU03a6_1 (Datatypes.app u _UU03a6_2))
    (Datatypes.app _UU03a8_1 (Datatypes.app v _UU03a8_2)))

coq_Sctxt_eq :: (([]) (Gen_tacs.Coq_rel (([]) a1))) -> (([]) ((,) (([]) a1) (([]) a1))) -> (([]) 
                a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) 
                a1) -> (([]) a1) -> a2 -> Coq_seqrule a1 a2
coq_Sctxt_eq ps mps ca cs u v _UU03a6_1 _UU03a6_2 _UU03a8_1 _UU03a8_2 x =
  Logic.eq_rect_r (Datatypes.app _UU03a6_1 (Datatypes.app u _UU03a6_2))
    (Logic.eq_rect_r (Datatypes.app _UU03a8_1 (Datatypes.app v _UU03a8_2))
      (Logic.eq_rect_r (List.map (seqext _UU03a6_1 _UU03a6_2 _UU03a8_1 _UU03a8_2) ps)
        (coq_Sctxt_e ps u v _UU03a6_1 _UU03a6_2 _UU03a8_1 _UU03a8_2 x) mps) cs) ca

coq_Sctxt_e' :: (([]) (Gen_tacs.Coq_rel (([]) a1))) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (([])
                a1) -> (([]) a1) -> (([]) a1) -> a2 -> Coq_seqrule a1 a2
coq_Sctxt_e' ps u v _UU03a6_1 _UU03a6_2 _UU03a8_1 _UU03a8_2 h =
  Logic.eq_rect (Datatypes.app _UU03a6_1 (Datatypes.app u _UU03a6_2))
    (coq_Sctxt_e ps u v _UU03a6_1 _UU03a6_2 _UU03a8_1 _UU03a8_2 h)
    (Datatypes.app (Datatypes.app _UU03a6_1 u) _UU03a6_2)

seqrule_same :: (([]) (Gen_tacs.Coq_rel (([]) a1))) -> (Gen_tacs.Coq_rel (([]) a1)) ->
                (Gen_tacs.Coq_rel (([]) a1)) -> (Coq_seqrule a1 a2) -> Coq_seqrule a1 a2
seqrule_same _ c c' x =
  Logic.eq_rect_r c' (\x0 -> x0) c x

coq_InT_seqextL :: (([]) a1) -> (([]) a1) -> a1 -> (GenT.InT a1) -> Specif.Coq_sigT (([]) a1)
                   (Specif.Coq_sigT (([]) a1) ())
coq_InT_seqextL _UU0393_ =
  Datatypes.list_rect (\_ _ hin ->
    case hin of {
     GenT.InT_eq' _ _ -> Logic.coq_False_rect __;
     GenT.InT_cons _ _ x -> Logic.coq_False_rect x}) (\a _UU0393_0 iH_UU0393_ _UU0394_ a0 hin ->
    case hin of {
     GenT.InT_eq' b l ->
      Logic.eq_rect_r a (\_ ->
        Logic.eq_rect_r _UU0393_0 (\_ ->
          Logic.eq_rect_r a0 (\_ _ -> Specif.Coq_existT ([]) (Specif.Coq_existT _UU0393_0 __)) a hin
            __) l) b __ __;
     GenT.InT_cons b l x ->
      Logic.eq_rect_r a (\_ ->
        Logic.eq_rect_r _UU0393_0 (\x0 ->
          let {s = iH_UU0393_ _UU0394_ a0 x0} in
          case s of {
           Specif.Coq_existT h1 s0 ->
            case s0 of {
             Specif.Coq_existT h2 _ ->
              Logic.eq_rect (Datatypes.app h1 ((:) a0 h2)) (\_ ->
                Logic.eq_rect (Datatypes.app _UU0394_ ([]))
                  (let {
                    _evar_0_ = let {
                                _evar_0_ = let {
                                            _evar_0_ = Specif.Coq_existT ((:) a h1)
                                             (Specif.Coq_existT h2 __)}
                                           in
                                           Logic.eq_rect_r _UU0394_ _evar_0_
                                             (Datatypes.app _UU0394_ ([]))}
                               in
                               Logic.eq_rect_r ([]) _evar_0_ (Datatypes.app ([]) ([]))}
                   in
                   Logic.eq_rect_r _UU0394_ _evar_0_ (Datatypes.app _UU0394_ ([]))) _UU0394_)
                _UU0393_0 __}}) l) b __ x}) _UU0393_

coq_InT_seqextR :: (([]) a1) -> (([]) a1) -> a1 -> (GenT.InT a1) -> Specif.Coq_sigT (([]) a1)
                   (Specif.Coq_sigT (([]) a1) ())
coq_InT_seqextR _UU0393_ _UU0394_ =
  Datatypes.list_rect (\_ hin ->
    case hin of {
     GenT.InT_eq' _ _ -> Logic.coq_False_rect __;
     GenT.InT_cons _ _ x -> Logic.coq_False_rect x}) (\a _UU0394_0 iH_UU0394_ a0 hin ->
    case hin of {
     GenT.InT_eq' b l ->
      Logic.eq_rect_r a (\_ ->
        Logic.eq_rect_r _UU0394_0 (\_ ->
          Logic.eq_rect_r a0 (\_ _ -> Specif.Coq_existT ([]) (Specif.Coq_existT _UU0394_0 __)) a hin
            __) l) b __ __;
     GenT.InT_cons b l x ->
      Logic.eq_rect_r a (\_ ->
        Logic.eq_rect_r _UU0394_0 (\x0 ->
          let {s = iH_UU0394_ a0 x0} in
          case s of {
           Specif.Coq_existT h1 s0 ->
            case s0 of {
             Specif.Coq_existT h2 _ ->
              Logic.eq_rect (Datatypes.app _UU0393_ ([])) (\_ ->
                Logic.eq_rect (Datatypes.app h1 ((:) a0 h2))
                  (let {
                    _evar_0_ = let {
                                _evar_0_ = let {
                                            _evar_0_ = Specif.Coq_existT ((:) a h1)
                                             (Specif.Coq_existT h2 __)}
                                           in
                                           Logic.eq_rect_r _UU0393_ _evar_0_
                                             (Datatypes.app _UU0393_ ([]))}
                               in
                               Logic.eq_rect_r ([]) _evar_0_ (Datatypes.app ([]) ([]))}
                   in
                   Logic.eq_rect_r _UU0393_ _evar_0_ (Datatypes.app _UU0393_ ([]))) _UU0394_0)
                _UU0393_ __}}) l) b __ x}) _UU0394_

coq_InT_seqext :: (([]) a1) -> (([]) a1) -> a1 -> a1 -> (GenT.InT a1) -> (GenT.InT a1) ->
                  Specif.Coq_sigT (([]) a1)
                  (Specif.Coq_sigT (([]) a1)
                  (Specif.Coq_sigT (([]) a1) (Specif.Coq_sigT (([]) a1) ())))
coq_InT_seqext _UU0393_ _UU0394_ a b hin1 hin2 =
  let {s = coq_InT_seqextL _UU0393_ _UU0394_ a hin1} in
  case s of {
   Specif.Coq_existT h1 s0 ->
    case s0 of {
     Specif.Coq_existT h2 _ ->
      let {s1 = coq_InT_seqextR _UU0393_ _UU0394_ b hin2} in
      case s1 of {
       Specif.Coq_existT j1 s2 ->
        case s2 of {
         Specif.Coq_existT j2 _ ->
          let {
           _evar_0_ = \_ ->
            let {
             _evar_0_ = \_ ->
              let {
               _evar_0_ = \_ ->
                let {
                 _evar_0_ = \_ ->
                  Logic.eq_rect (Datatypes.app h1 ((:) a h2))
                    (Logic.eq_rect (Datatypes.app j1 ((:) b j2))
                      (Logic.eq_rect (Datatypes.app h1 ((:) a h2)) (\_ _ _ ->
                        Logic.eq_rect (Datatypes.app j1 ((:) b j2)) (\_ _ _ -> Specif.Coq_existT h1
                          (Specif.Coq_existT h2 (Specif.Coq_existT j1 (Specif.Coq_existT j2 __))))
                          _UU0394_ hin2 __ __) _UU0393_ hin1 __ __) _UU0394_) _UU0393_}
                in
                Logic.eq_rect_r _UU0393_ _evar_0_ (Datatypes.app _UU0393_ ([])) __}
              in
              Logic.eq_rect_r ([]) _evar_0_ (Datatypes.app ([]) ([])) __}
            in
            Logic.eq_rect_r _UU0394_ _evar_0_ (Datatypes.app _UU0394_ ([])) __}
          in
          Logic.eq_rect_r ([]) _evar_0_ (Datatypes.app ([]) ([])) __}}}}

