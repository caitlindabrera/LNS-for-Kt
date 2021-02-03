module ContractedT where

import qualified Prelude
import qualified Datatypes
import qualified Logic
import qualified Specif
import qualified GenT
import qualified InclT
import qualified LntT

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_contracted_gen t =
   Coq_contracted_genL_I t (([]) t) (([]) t) (([]) t) (([]) t) (([]) t)
 | Coq_contracted_genR_I t (([]) t) (([]) t) (([]) t) (([]) t) (([]) t)

data Coq_contracted_gen_spec t =
   Coq_contracted_genL_spec_I (([]) t) (([]) t) (([]) t) (([]) t) (([]) t)
 | Coq_contracted_genR_spec_I (([]) t) (([]) t) (([]) t) (([]) t) (([]) t)

contracted_genL_I' :: a1 -> (([]) a1) -> (([]) a1) -> (([]) a1) -> Coq_contracted_gen a1
contracted_genL_I' a a0 b c =
  Coq_contracted_genL_I a
    (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
    (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c))) a0 b c

contracted_genR_I' :: a1 -> (([]) a1) -> (([]) a1) -> (([]) a1) -> Coq_contracted_gen a1
contracted_genR_I' a a0 b c =
  Coq_contracted_genR_I a
    (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
    (Datatypes.app a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c))) a0 b c

contracted_genR_spec_I' :: a1 -> (([]) a1) -> (([]) a1) -> (([]) a1) -> Coq_contracted_gen_spec a1
contracted_genR_spec_I' a a0 b c =
  Coq_contracted_genR_spec_I
    (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
    (Datatypes.app a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c))) a0 b c

contracted_genL_spec_I' :: a1 -> (([]) a1) -> (([]) a1) -> (([]) a1) -> Coq_contracted_gen_spec a1
contracted_genL_spec_I' a a0 b c =
  Coq_contracted_genL_spec_I
    (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
    (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c))) a0 b c

contracted_gen__spec :: a1 -> (([]) a1) -> (([]) a1) -> (Coq_contracted_gen_spec a1) ->
                        Coq_contracted_gen a1
contracted_gen__spec a l1 l2 h =
  case h of {
   Coq_contracted_genL_spec_I x y a0 b c ->
    Logic.eq_rect_r l1 (\_ -> Logic.eq_rect_r l2 (\_ _ -> Coq_contracted_genL_I a l1 l2 a0 b c) y) x
      __ __ __;
   Coq_contracted_genR_spec_I x y a0 b c ->
    Logic.eq_rect_r l1 (\_ -> Logic.eq_rect_r l2 (\_ _ -> Coq_contracted_genR_I a l1 l2 a0 b c) y) x
      __ __ __}

cont_gen_L :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_contracted_gen a1) -> Coq_contracted_gen a1
cont_gen_L _ _ z h =
  case h of {
   Coq_contracted_genL_I a x y a0 b c ->
    Logic.eq_rect_r
      (Datatypes.app a0
        (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
      (Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c)))
        (Logic.eq_rect_r
          (Datatypes.app (Datatypes.app z a0)
            (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
          (Logic.eq_rect_r
            (Datatypes.app (Datatypes.app z a0) (Datatypes.app ((:) a ([])) (Datatypes.app b c)))
            (contracted_genL_I' a (Datatypes.app z a0) b c)
            (Datatypes.app z (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c)))))
          (Datatypes.app z
            (Datatypes.app a0
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))))) y) x;
   Coq_contracted_genR_I a x y a0 b c ->
    Logic.eq_rect_r
      (Datatypes.app a0
        (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
      (Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c)))
        (Logic.eq_rect_r
          (Datatypes.app (Datatypes.app z a0)
            (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
          (Logic.eq_rect_r
            (Datatypes.app (Datatypes.app z a0) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))
            (contracted_genR_I' a (Datatypes.app z a0) b c)
            (Datatypes.app z (Datatypes.app a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c)))))
          (Datatypes.app z
            (Datatypes.app a0
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))))) y) x}

cont_gen_R :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_contracted_gen a1) -> Coq_contracted_gen a1
cont_gen_R _ _ z h =
  case h of {
   Coq_contracted_genL_I a x y a0 b c ->
    Logic.eq_rect_r
      (Datatypes.app a0
        (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
      (Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c)))
        (Logic.eq_rect
          (Datatypes.app a0
            (Datatypes.app
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))) z))
          (Logic.eq_rect
            (Datatypes.app ((:) a ([]))
              (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
            (Logic.eq_rect (Datatypes.app b (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
              (Logic.eq_rect (Datatypes.app ((:) a ([])) (Datatypes.app c z))
                (Logic.eq_rect
                  (Datatypes.app a0
                    (Datatypes.app (Datatypes.app ((:) a ([])) (Datatypes.app b c)) z))
                  (Logic.eq_rect (Datatypes.app ((:) a ([])) (Datatypes.app (Datatypes.app b c) z))
                    (Logic.eq_rect (Datatypes.app b (Datatypes.app c z))
                      (contracted_genL_I' a a0 b (Datatypes.app c z))
                      (Datatypes.app (Datatypes.app b c) z))
                    (Datatypes.app (Datatypes.app ((:) a ([])) (Datatypes.app b c)) z))
                  (Datatypes.app (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c)))
                    z)) (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
              (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
            (Datatypes.app
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))) z))
          (Datatypes.app
            (Datatypes.app a0
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))) z)) y) x;
   Coq_contracted_genR_I a x y a0 b c ->
    Logic.eq_rect_r
      (Datatypes.app a0
        (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
      (Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c)))
        (Logic.eq_rect
          (Datatypes.app a0
            (Datatypes.app
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))) z))
          (Logic.eq_rect
            (Datatypes.app ((:) a ([]))
              (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
            (Logic.eq_rect (Datatypes.app b (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
              (Logic.eq_rect (Datatypes.app ((:) a ([])) (Datatypes.app c z))
                (Logic.eq_rect
                  (Datatypes.app a0
                    (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
                  (Logic.eq_rect (Datatypes.app b (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
                    (Logic.eq_rect (Datatypes.app ((:) a ([])) (Datatypes.app c z))
                      (contracted_genR_I' a a0 b (Datatypes.app c z))
                      (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
                    (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
                  (Datatypes.app (Datatypes.app a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c)))
                    z)) (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
              (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
            (Datatypes.app
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))) z))
          (Datatypes.app
            (Datatypes.app a0
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))) z)) y) x}

cont_gen_spec_basic :: a1 -> Coq_contracted_gen_spec a1
cont_gen_spec_basic a =
  contracted_genL_spec_I' a ([]) ([]) ([])

cont_gen_spec_L :: a1 -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_contracted_gen_spec a1) ->
                   Coq_contracted_gen_spec a1
cont_gen_spec_L a _ _ z h =
  case h of {
   Coq_contracted_genL_spec_I x y a0 b c ->
    Logic.eq_rect_r
      (Datatypes.app a0
        (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
      (Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c)))
        (Logic.eq_rect_r
          (Datatypes.app (Datatypes.app z a0)
            (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
          (Logic.eq_rect_r
            (Datatypes.app (Datatypes.app z a0) (Datatypes.app ((:) a ([])) (Datatypes.app b c)))
            (contracted_genL_spec_I' a (Datatypes.app z a0) b c)
            (Datatypes.app z (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c)))))
          (Datatypes.app z
            (Datatypes.app a0
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))))) y) x;
   Coq_contracted_genR_spec_I x y a0 b c ->
    Logic.eq_rect_r
      (Datatypes.app a0
        (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
      (Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c)))
        (Logic.eq_rect_r
          (Datatypes.app (Datatypes.app z a0)
            (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
          (Logic.eq_rect_r
            (Datatypes.app (Datatypes.app z a0) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))
            (contracted_genR_spec_I' a (Datatypes.app z a0) b c)
            (Datatypes.app z (Datatypes.app a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c)))))
          (Datatypes.app z
            (Datatypes.app a0
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))))) y) x}

cont_gen_spec_R :: a1 -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_contracted_gen_spec a1) ->
                   Coq_contracted_gen_spec a1
cont_gen_spec_R a _ _ z h =
  case h of {
   Coq_contracted_genL_spec_I x y a0 b c ->
    Logic.eq_rect_r
      (Datatypes.app a0
        (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
      (Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c)))
        (Logic.eq_rect
          (Datatypes.app a0
            (Datatypes.app
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))) z))
          (Logic.eq_rect
            (Datatypes.app ((:) a ([]))
              (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
            (Logic.eq_rect (Datatypes.app b (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
              (Logic.eq_rect (Datatypes.app ((:) a ([])) (Datatypes.app c z))
                (Logic.eq_rect
                  (Datatypes.app a0
                    (Datatypes.app (Datatypes.app ((:) a ([])) (Datatypes.app b c)) z))
                  (Logic.eq_rect (Datatypes.app ((:) a ([])) (Datatypes.app (Datatypes.app b c) z))
                    (Logic.eq_rect (Datatypes.app b (Datatypes.app c z))
                      (contracted_genL_spec_I' a a0 b (Datatypes.app c z))
                      (Datatypes.app (Datatypes.app b c) z))
                    (Datatypes.app (Datatypes.app ((:) a ([])) (Datatypes.app b c)) z))
                  (Datatypes.app (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c)))
                    z)) (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
              (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
            (Datatypes.app
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))) z))
          (Datatypes.app
            (Datatypes.app a0
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))) z)) y) x;
   Coq_contracted_genR_spec_I x y a0 b c ->
    Logic.eq_rect_r
      (Datatypes.app a0
        (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
      (Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c)))
        (Logic.eq_rect
          (Datatypes.app a0
            (Datatypes.app
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))) z))
          (Logic.eq_rect
            (Datatypes.app ((:) a ([]))
              (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
            (Logic.eq_rect (Datatypes.app b (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
              (Logic.eq_rect (Datatypes.app ((:) a ([])) (Datatypes.app c z))
                (Logic.eq_rect
                  (Datatypes.app a0
                    (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
                  (Logic.eq_rect (Datatypes.app b (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
                    (Logic.eq_rect (Datatypes.app ((:) a ([])) (Datatypes.app c z))
                      (contracted_genR_spec_I' a a0 b (Datatypes.app c z))
                      (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
                    (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
                  (Datatypes.app (Datatypes.app a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c)))
                    z)) (Datatypes.app (Datatypes.app ((:) a ([])) c) z))
              (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a ([])) c)) z))
            (Datatypes.app
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))) z))
          (Datatypes.app
            (Datatypes.app a0
              (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))) z)) y) x}

cont_gen_spec_rem_sml_L :: a1 -> (([]) a1) -> Coq_contracted_gen_spec a1
cont_gen_spec_rem_sml_L a z =
  Logic.eq_rect (Datatypes.app ([]) (Datatypes.app ((:) a ([])) (Datatypes.app z ([]))))
    (contracted_genL_spec_I' a ([]) z ([])) (Datatypes.app ((:) a ([])) z)

cont_gen_spec_rem_sml_R :: a1 -> (([]) a1) -> Coq_contracted_gen_spec a1
cont_gen_spec_rem_sml_R a z =
  contracted_genR_spec_I' a ([]) z ([])

contracted_gen_in1 :: a1 -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (GenT.InT a1) ->
                      Coq_contracted_gen a1
contracted_gen_in1 a a0 _UU0393_1 c h5 h =
  let {h0 = GenT.coq_InT_split a c h} in
  case h0 of {
   Specif.Coq_existT l1 s ->
    case s of {
     Specif.Coq_existT l2 _ ->
      Logic.eq_rect_r (Datatypes.app l1 ((:) a l2))
        (let {
          _evar_0_ = let {
                      _evar_0_ = let {
                                  _evar_0_ = Coq_contracted_genR_I a
                                   (Datatypes.app a0
                                     (Datatypes.app ((:) a ([]))
                                       (Datatypes.app _UU0393_1
                                         (Datatypes.app l1
                                           (Datatypes.app ((:) a ([])) (Datatypes.app l2 h5))))))
                                   (Datatypes.app a0
                                     (Datatypes.app _UU0393_1
                                       (Datatypes.app l1
                                         (Datatypes.app ((:) a ([])) (Datatypes.app l2 h5))))) a0
                                   (Datatypes.app _UU0393_1 l1) (Datatypes.app l2 h5)}
                                 in
                                 Logic.eq_rect ((:) a (Datatypes.app l2 h5)) _evar_0_
                                   (Datatypes.app ((:) a l2) h5)}
                     in
                     Logic.eq_rect ((:) a
                       (Datatypes.app ([])
                         (Datatypes.app _UU0393_1 (Datatypes.app l1 (Datatypes.app ((:) a l2) h5)))))
                       _evar_0_
                       (Datatypes.app ((:) a ([]))
                         (Datatypes.app _UU0393_1 (Datatypes.app l1 (Datatypes.app ((:) a l2) h5))))}
         in
         Logic.eq_rect (Datatypes.app l1 (Datatypes.app ((:) a l2) h5)) _evar_0_
           (Datatypes.app (Datatypes.app l1 ((:) a l2)) h5)) c}}

contracted_gen_in3 :: a1 -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (GenT.InT a1) ->
                      Coq_contracted_gen a1
contracted_gen_in3 a a0 _UU0393_1 c h =
  let {h0 = GenT.coq_InT_split a _UU0393_1 h} in
  case h0 of {
   Specif.Coq_existT l1 s ->
    case s of {
     Specif.Coq_existT l2 _ ->
      Logic.eq_rect_r (Datatypes.app l1 ((:) a l2))
        (let {
          _evar_0_ = let {
                      _evar_0_ = let {
                                  _evar_0_ = let {
                                              _evar_0_ = let {
                                                          _evar_0_ = Coq_contracted_genL_I a
                                                           (Datatypes.app a0
                                                             (Datatypes.app l1
                                                               (Datatypes.app ((:) a ([]))
                                                                 (Datatypes.app l2 ((:) a c)))))
                                                           (Datatypes.app a0
                                                             (Datatypes.app l1
                                                               (Datatypes.app ((:) a ([]))
                                                                 (Datatypes.app l2 c))))
                                                           (Datatypes.app a0 l1) l2 c}
                                                         in
                                                         Logic.eq_rect ((:) a (Datatypes.app l2 c))
                                                           _evar_0_ (Datatypes.app ((:) a l2) c)}
                                             in
                                             Logic.eq_rect ((:) a (Datatypes.app ([]) c)) _evar_0_
                                               (Datatypes.app ((:) a ([])) c)}
                                 in
                                 Logic.eq_rect ((:) a
                                   (Datatypes.app l2 (Datatypes.app ((:) a ([])) c))) _evar_0_
                                   (Datatypes.app ((:) a l2) (Datatypes.app ((:) a ([])) c))}
                     in
                     Logic.eq_rect (Datatypes.app l1 (Datatypes.app ((:) a l2) c)) _evar_0_
                       (Datatypes.app (Datatypes.app l1 ((:) a l2)) c)}
         in
         Logic.eq_rect (Datatypes.app l1 (Datatypes.app ((:) a l2) (Datatypes.app ((:) a ([])) c)))
           _evar_0_ (Datatypes.app (Datatypes.app l1 ((:) a l2)) (Datatypes.app ((:) a ([])) c)))
        _UU0393_1}}

contracted_gen_in4 :: a1 -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> (GenT.InT a1) ->
                      Coq_contracted_gen a1
contracted_gen_in4 a a0 _UU0393_1 h5 c h =
  let {h0 = GenT.coq_InT_split a _UU0393_1 h} in
  case h0 of {
   Specif.Coq_existT l1 s ->
    case s of {
     Specif.Coq_existT l2 _ ->
      Logic.eq_rect_r (Datatypes.app l1 ((:) a l2))
        (let {
          _evar_0_ = let {
                      _evar_0_ = let {
                                  _evar_0_ = let {
                                              _evar_0_ = let {
                                                          _evar_0_ = let {
                                                                      _evar_0_ = let {
                                                                                  _evar_0_ = 
                                                                                   let {
                                                                                    _evar_0_ = 
                                                                                     let {
                                                                                      _evar_0_ = 
                                                                                       let {
                                                                                        _evar_0_ = 
                                                                                         let {
                                                                                          _evar_0_ = 
                                                                                           let {
                                                                                            _evar_0_ = 
                                                                                            let {
                                                                                            _evar_0_ = 
                                                                                            let {
                                                                                            _evar_0_ = Coq_contracted_genL_I
                                                                                            a
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            a0 l1)
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            l2
                                                                                            (Datatypes.app
                                                                                            h5
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            ([]) c))))))
                                                                                            (Datatypes.app
                                                                                            a0
                                                                                            (Datatypes.app
                                                                                            l1
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            l2
                                                                                            (Datatypes.app
                                                                                            h5 c)))))
                                                                                            (Datatypes.app
                                                                                            a0 l1)
                                                                                            (Datatypes.app
                                                                                            l2 h5)
                                                                                            (Datatypes.app
                                                                                            ([]) c)}
                                                                                            in
                                                                                            Logic.eq_rect
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            a0 l1)
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            l2
                                                                                            (Datatypes.app
                                                                                            h5
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            ([]) c))))))
                                                                                            _evar_0_
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            a0 l1)
                                                                                            ((:) a
                                                                                            ([])))
                                                                                            (Datatypes.app
                                                                                            l2
                                                                                            (Datatypes.app
                                                                                            h5
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            ([]) c)))))}
                                                                                            in
                                                                                            Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            a0 l1)
                                                                                            ((:) a
                                                                                            ([])))
                                                                                            (Datatypes.app
                                                                                            l2
                                                                                            (Datatypes.app
                                                                                            h5
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            ([]) c)))))
                                                                                            _evar_0_
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            a0 l1)
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            l2
                                                                                            (Datatypes.app
                                                                                            h5
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            ([]) c))))))}
                                                                                           in
                                                                                           Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            a0 l1)
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            l2
                                                                                            (Datatypes.app
                                                                                            h5
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            ([]) c))))))
                                                                                            _evar_0_
                                                                                            (Datatypes.app
                                                                                            a0
                                                                                            (Datatypes.app
                                                                                            l1
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            l2
                                                                                            (Datatypes.app
                                                                                            h5
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            ([]) c)))))))}
                                                                                         in
                                                                                         Logic.eq_rect_r
                                                                                           (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            l2
                                                                                            (Datatypes.app
                                                                                            h5 c)))
                                                                                           _evar_0_
                                                                                           ((:) a
                                                                                           (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            l2
                                                                                            (Datatypes.app
                                                                                            h5 c))))}
                                                                                       in
                                                                                       Logic.eq_rect_r
                                                                                         (Datatypes.app
                                                                                           ((:) a
                                                                                           ([]))
                                                                                           (Datatypes.app
                                                                                            ([]) c))
                                                                                         _evar_0_
                                                                                         ((:) a
                                                                                         (Datatypes.app
                                                                                           ([])
                                                                                           (Datatypes.app
                                                                                            ([]) c)))}
                                                                                     in
                                                                                     Logic.eq_rect_r
                                                                                       (Datatypes.app
                                                                                         ((:) a ([]))
                                                                                         (Datatypes.app
                                                                                           l2
                                                                                           (Datatypes.app
                                                                                            h5 ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            ([]) c))))))
                                                                                       _evar_0_ ((:)
                                                                                       a
                                                                                       (Datatypes.app
                                                                                         ([])
                                                                                         (Datatypes.app
                                                                                           l2
                                                                                           (Datatypes.app
                                                                                            h5 ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            ([]) c)))))))}
                                                                                   in
                                                                                   Logic.eq_rect ((:)
                                                                                     a
                                                                                     (Datatypes.app
                                                                                       ([])
                                                                                       (Datatypes.app
                                                                                         l2
                                                                                         (Datatypes.app
                                                                                           h5 c))))
                                                                                     _evar_0_
                                                                                     (Datatypes.app
                                                                                       ((:) a ([]))
                                                                                       (Datatypes.app
                                                                                         l2
                                                                                         (Datatypes.app
                                                                                           h5 c)))}
                                                                                 in
                                                                                 Logic.eq_rect ((:) a
                                                                                   (Datatypes.app
                                                                                     ([])
                                                                                     (Datatypes.app
                                                                                       ([]) c)))
                                                                                   _evar_0_
                                                                                   (Datatypes.app
                                                                                     ((:) a ([]))
                                                                                     (Datatypes.app
                                                                                       ([]) c))}
                                                                     in
                                                                     Logic.eq_rect ((:) a
                                                                       (Datatypes.app ([])
                                                                         (Datatypes.app l2
                                                                           (Datatypes.app h5
                                                                             (Datatypes.app ((:) a
                                                                               ([]))
                                                                               (Datatypes.app ([]) c))))))
                                                                       _evar_0_
                                                                       (Datatypes.app ((:) a ([]))
                                                                         (Datatypes.app l2
                                                                           (Datatypes.app h5
                                                                             (Datatypes.app ((:) a
                                                                               ([]))
                                                                               (Datatypes.app ([]) c)))))}
                                                         in
                                                         Logic.eq_rect
                                                           (Datatypes.app ((:) a ([]))
                                                             (Datatypes.app l2 (Datatypes.app h5 c)))
                                                           _evar_0_
                                                           (Datatypes.app
                                                             (Datatypes.app ((:) a ([])) l2)
                                                             (Datatypes.app h5 c))}
                                             in
                                             Logic.eq_rect
                                               (Datatypes.app l1
                                                 (Datatypes.app (Datatypes.app ((:) a ([])) l2)
                                                   (Datatypes.app h5 c))) _evar_0_
                                               (Datatypes.app
                                                 (Datatypes.app l1 (Datatypes.app ((:) a ([])) l2))
                                                 (Datatypes.app h5 c))}
                                 in
                                 Logic.eq_rect (Datatypes.app ((:) a ([])) (Datatypes.app ([]) c))
                                   _evar_0_ (Datatypes.app (Datatypes.app ((:) a ([])) ([])) c)}
                     in
                     Logic.eq_rect
                       (Datatypes.app ((:) a ([]))
                         (Datatypes.app l2
                           (Datatypes.app h5 (Datatypes.app (Datatypes.app ((:) a ([])) ([])) c))))
                       _evar_0_
                       (Datatypes.app (Datatypes.app ((:) a ([])) l2)
                         (Datatypes.app h5 (Datatypes.app (Datatypes.app ((:) a ([])) ([])) c)))}
         in
         Logic.eq_rect
           (Datatypes.app l1
             (Datatypes.app (Datatypes.app ((:) a ([])) l2)
               (Datatypes.app h5 (Datatypes.app (Datatypes.app ((:) a ([])) ([])) c)))) _evar_0_
           (Datatypes.app (Datatypes.app l1 (Datatypes.app ((:) a ([])) l2))
             (Datatypes.app h5 (Datatypes.app (Datatypes.app ((:) a ([])) ([])) c)))) _UU0393_1}}

data Coq_contracted_multi t =
   Coq_cont_multi_refl (([]) t)
 | Coq_cont_multi_step (([]) t) (([]) t) (([]) t) (Coq_contracted_gen t) (Coq_contracted_multi t)

contracted_multi_rect :: ((([]) a1) -> a2) -> ((([]) a1) -> (([]) a1) -> (([]) a1) ->
                         (Coq_contracted_gen a1) -> (Coq_contracted_multi a1) -> a2 -> a2) -> (([])
                         a1) -> (([]) a1) -> (Coq_contracted_multi a1) -> a2
contracted_multi_rect f f0 _ _ c =
  case c of {
   Coq_cont_multi_refl x -> f x;
   Coq_cont_multi_step x y z c0 c1 -> f0 x y z c0 c1 (contracted_multi_rect f f0 y z c1)}

contracted_multi_rec :: ((([]) a1) -> a2) -> ((([]) a1) -> (([]) a1) -> (([]) a1) ->
                        (Coq_contracted_gen a1) -> (Coq_contracted_multi a1) -> a2 -> a2) -> (([])
                        a1) -> (([]) a1) -> (Coq_contracted_multi a1) -> a2
contracted_multi_rec =
  contracted_multi_rect

data Coq_contracted_seqL t =
   Coq_cont_seqL (([]) t) (([]) t) (([]) t) LntT.Coq_dir (Coq_contracted_multi t)

data Coq_contracted_seqR t =
   Coq_cont_seqR (([]) t) (([]) t) (([]) t) LntT.Coq_dir (Coq_contracted_multi t)

data Coq_contracted_seq t =
   Coq_cont_seq_baseL ((,) ((,) (([]) t) (([]) t)) LntT.Coq_dir) ((,) ((,) (([]) t) (([]) t))
                                                                 LntT.Coq_dir) (Coq_contracted_seqL
                                                                               t)
 | Coq_cont_seq_baseR ((,) ((,) (([]) t) (([]) t)) LntT.Coq_dir) ((,) ((,) (([]) t) (([]) t))
                                                                 LntT.Coq_dir) (Coq_contracted_seqR
                                                                               t)
 | Coq_cont_seq_stepL ((,) ((,) (([]) t) (([]) t)) LntT.Coq_dir) ((,) ((,) (([]) t) (([]) t))
                                                                 LntT.Coq_dir) ((,)
                                                                               ((,) (([]) t)
                                                                               (([]) t))
                                                                               LntT.Coq_dir) 
 (Coq_contracted_seqL t) (Coq_contracted_seq t)
 | Coq_cont_seq_stepR ((,) ((,) (([]) t) (([]) t)) LntT.Coq_dir) ((,) ((,) (([]) t) (([]) t))
                                                                 LntT.Coq_dir) ((,)
                                                                               ((,) (([]) t)
                                                                               (([]) t))
                                                                               LntT.Coq_dir) 
 (Coq_contracted_seqR t) (Coq_contracted_seq t)

contracted_seq_rect :: (((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,)
                       ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> (Coq_contracted_seqL a1) -> a2) ->
                       (((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,)
                       ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> (Coq_contracted_seqR a1) -> a2) ->
                       (((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,)
                       ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,) ((,) (([]) a1) (([]) a1))
                       LntT.Coq_dir) -> (Coq_contracted_seqL a1) -> (Coq_contracted_seq a1) -> a2 ->
                       a2) -> (((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,)
                       ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,) ((,) (([]) a1) (([]) a1))
                       LntT.Coq_dir) -> (Coq_contracted_seqR a1) -> (Coq_contracted_seq a1) -> a2 ->
                       a2) -> ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,)
                       ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> (Coq_contracted_seq a1) -> a2
contracted_seq_rect f f0 f1 f2 _ _ c =
  case c of {
   Coq_cont_seq_baseL s1 s2 c0 -> f s1 s2 c0;
   Coq_cont_seq_baseR s1 s2 c0 -> f0 s1 s2 c0;
   Coq_cont_seq_stepL s1 s2 s3 c0 c1 -> f1 s1 s2 s3 c0 c1 (contracted_seq_rect f f0 f1 f2 s2 s3 c1);
   Coq_cont_seq_stepR s1 s2 s3 c0 c1 -> f2 s1 s2 s3 c0 c1 (contracted_seq_rect f f0 f1 f2 s2 s3 c1)}

contracted_seq_rec :: (((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,) ((,) (([]) a1) (([]) a1))
                      LntT.Coq_dir) -> (Coq_contracted_seqL a1) -> a2) -> (((,)
                      ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,) ((,) (([]) a1) (([]) a1))
                      LntT.Coq_dir) -> (Coq_contracted_seqR a1) -> a2) -> (((,)
                      ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,) ((,) (([]) a1) (([]) a1))
                      LntT.Coq_dir) -> ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) ->
                      (Coq_contracted_seqL a1) -> (Coq_contracted_seq a1) -> a2 -> a2) -> (((,)
                      ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,) ((,) (([]) a1) (([]) a1))
                      LntT.Coq_dir) -> ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) ->
                      (Coq_contracted_seqR a1) -> (Coq_contracted_seq a1) -> a2 -> a2) -> ((,)
                      ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,) ((,) (([]) a1) (([]) a1))
                      LntT.Coq_dir) -> (Coq_contracted_seq a1) -> a2
contracted_seq_rec =
  contracted_seq_rect

data Coq_contracted_nseq t =
   Coq_cont_nseq_nil
 | Coq_cont_nseq_cons ((,) ((,) (([]) t) (([]) t)) LntT.Coq_dir) ((,) ((,) (([]) t) (([]) t))
                                                                 LntT.Coq_dir) (([])
                                                                               ((,)
                                                                               ((,) (([]) t)
                                                                               (([]) t))
                                                                               LntT.Coq_dir)) 
 (([]) ((,) ((,) (([]) t) (([]) t)) LntT.Coq_dir)) (Coq_contracted_seq t) (Coq_contracted_nseq t)

contracted_nseq_rect :: a2 -> (((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> ((,)
                        ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> (([])
                        ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                        ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (Coq_contracted_seq 
                        a1) -> (Coq_contracted_nseq a1) -> a2 -> a2) -> (([])
                        ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                        ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (Coq_contracted_nseq 
                        a1) -> a2
contracted_nseq_rect f f0 _ _ c =
  case c of {
   Coq_cont_nseq_nil -> f;
   Coq_cont_nseq_cons s1 s2 ns1 ns2 c0 c1 ->
    f0 s1 s2 ns1 ns2 c0 c1 (contracted_nseq_rect f f0 ns1 ns2 c1)}

contracted_gen_cons :: (([]) a1) -> (([]) a1) -> a1 -> (Coq_contracted_gen a1) -> Coq_contracted_gen
                       a1
contracted_gen_cons y z a hc =
  case hc of {
   Coq_contracted_genL_I a0 x y0 a1 b c ->
    Logic.eq_rect_r y (\_ ->
      Logic.eq_rect_r z (\_ _ ->
        Logic.eq_rect_r
          (Datatypes.app a1
            (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c))))
          (\hc0 _ ->
          Logic.eq_rect_r (Datatypes.app a1 (Datatypes.app ((:) a0 ([])) (Datatypes.app b c)))
            (\_ _ ->
            Logic.eq_rect_r
              (Datatypes.app ((:) a a1)
                (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c))))
              (Logic.eq_rect_r
                (Datatypes.app ((:) a a1) (Datatypes.app ((:) a0 ([])) (Datatypes.app b c)))
                (Coq_contracted_genL_I a0
                (Datatypes.app ((:) a a1)
                  (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c))))
                (Datatypes.app ((:) a a1) (Datatypes.app ((:) a0 ([])) (Datatypes.app b c))) ((:) a
                a1) b c) ((:) a
                (Datatypes.app a1 (Datatypes.app ((:) a0 ([])) (Datatypes.app b c))))) ((:) a
              (Datatypes.app a1
                (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c)))))) z
            hc0 __) y hc __) y0) x __ __ __;
   Coq_contracted_genR_I a0 x y0 a1 b c ->
    Logic.eq_rect_r y (\_ ->
      Logic.eq_rect_r z (\_ _ ->
        Logic.eq_rect_r
          (Datatypes.app a1
            (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c))))
          (\hc0 _ ->
          Logic.eq_rect_r (Datatypes.app a1 (Datatypes.app b (Datatypes.app ((:) a0 ([])) c)))
            (\_ _ ->
            Logic.eq_rect_r
              (Datatypes.app ((:) a a1)
                (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c))))
              (Logic.eq_rect_r
                (Datatypes.app ((:) a a1) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c)))
                (Coq_contracted_genR_I a0
                (Datatypes.app ((:) a a1)
                  (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c))))
                (Datatypes.app ((:) a a1) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c))) ((:) a
                a1) b c) ((:) a
                (Datatypes.app a1 (Datatypes.app b (Datatypes.app ((:) a0 ([])) c))))) ((:) a
              (Datatypes.app a1
                (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c)))))) z
            hc0 __) y hc __) y0) x __ __ __}

contracted_multi_cons :: (([]) a1) -> (([]) a1) -> a1 -> (Coq_contracted_multi a1) ->
                         Coq_contracted_multi a1
contracted_multi_cons y z a hc =
  contracted_multi_rect (\x -> Coq_cont_multi_refl ((:) a x)) (\x y0 z0 c _ iHHc ->
    Coq_cont_multi_step ((:) a x) ((:) a y0) ((:) a z0) (contracted_gen_cons x y0 a c) iHHc) y z hc

contracted_multi_cons_tl :: (([]) a1) -> (([]) a1) -> a1 -> (Coq_contracted_multi a1) ->
                            Coq_contracted_multi a1
contracted_multi_cons_tl y z a hc =
  contracted_multi_rect (\x -> Coq_cont_multi_refl (Datatypes.app x ((:) a ([]))))
    (\x y0 z0 c hc0 iHHc ->
    case c of {
     Coq_contracted_genL_I a0 x0 y1 a1 b c0 ->
      Logic.eq_rect_r x (\_ ->
        Logic.eq_rect_r y0 (\_ _ ->
          Logic.eq_rect_r
            (Datatypes.app a1
              (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0))))
            (\c1 _ ->
            Logic.eq_rect_r (Datatypes.app a1 (Datatypes.app ((:) a0 ([])) (Datatypes.app b c0)))
              (\_ _ iHHc0 _ -> Coq_cont_multi_step
              (Datatypes.app
                (Datatypes.app a1
                  (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0))))
                ((:) a ([])))
              (Datatypes.app a1
                (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app c0 ((:) a ([]))))))
              (Datatypes.app z0 ((:) a ([])))
              (let {
                _evar_0_ = let {
                            _evar_0_ = let {
                                        _evar_0_ = let {
                                                    _evar_0_ = let {
                                                                _evar_0_ = let {
                                                                            _evar_0_ = Coq_contracted_genL_I
                                                                             a0
                                                                             (Datatypes.app a1 ((:)
                                                                               a0
                                                                               (Datatypes.app b ((:)
                                                                                 a0
                                                                                 (Datatypes.app c0
                                                                                   ((:) a ([])))))))
                                                                             (Datatypes.app a1
                                                                               (Datatypes.app ((:) a0
                                                                                 ([]))
                                                                                 (Datatypes.app b
                                                                                   (Datatypes.app c0
                                                                                     ((:) a ([]))))))
                                                                             a1 b
                                                                             (Datatypes.app c0 ((:) a
                                                                               ([])))}
                                                                           in
                                                                           Logic.eq_rect ((:) a0
                                                                             (Datatypes.app ([])
                                                                               (Datatypes.app c0 ((:)
                                                                                 a ([]))))) _evar_0_
                                                                             (Datatypes.app ((:) a0
                                                                               ([]))
                                                                               (Datatypes.app c0 ((:)
                                                                                 a ([]))))}
                                                               in
                                                               Logic.eq_rect ((:) a0
                                                                 (Datatypes.app ([])
                                                                   (Datatypes.app b
                                                                     (Datatypes.app ((:) a0 ([]))
                                                                       (Datatypes.app c0 ((:) a
                                                                         ([]))))))) _evar_0_
                                                                 (Datatypes.app ((:) a0 ([]))
                                                                   (Datatypes.app b
                                                                     (Datatypes.app ((:) a0 ([]))
                                                                       (Datatypes.app c0 ((:) a
                                                                         ([]))))))}
                                                   in
                                                   Logic.eq_rect
                                                     (Datatypes.app ((:) a0 ([]))
                                                       (Datatypes.app c0 ((:) a ([])))) _evar_0_
                                                     (Datatypes.app (Datatypes.app ((:) a0 ([])) c0)
                                                       ((:) a ([])))}
                                       in
                                       Logic.eq_rect
                                         (Datatypes.app b
                                           (Datatypes.app (Datatypes.app ((:) a0 ([])) c0) ((:) a
                                             ([])))) _evar_0_
                                         (Datatypes.app
                                           (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0)) ((:) a
                                           ([])))}
                           in
                           Logic.eq_rect
                             (Datatypes.app ((:) a0 ([]))
                               (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0)) ((:)
                                 a ([])))) _evar_0_
                             (Datatypes.app
                               (Datatypes.app ((:) a0 ([]))
                                 (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0))) ((:) a ([])))}
               in
               Logic.eq_rect
                 (Datatypes.app a1
                   (Datatypes.app
                     (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0)))
                     ((:) a ([])))) _evar_0_
                 (Datatypes.app
                   (Datatypes.app a1
                     (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0))))
                   ((:) a ([]))))
              (let {
                iHHc1 = Logic.eq_rect_r
                          (Datatypes.app
                            (Datatypes.app a1 (Datatypes.app ((:) a0 ([])) (Datatypes.app b c0)))
                            ((:) a ([]))) iHHc0
                          (Datatypes.app a1
                            (Datatypes.app (Datatypes.app ((:) a0 ([])) (Datatypes.app b c0)) ((:) a
                              ([]))))}
               in
               let {
                iHHc2 = Logic.eq_rect_r
                          (Datatypes.app (Datatypes.app ((:) a0 ([])) (Datatypes.app b c0)) ((:) a
                            ([]))) iHHc1
                          (Datatypes.app ((:) a0 ([]))
                            (Datatypes.app (Datatypes.app b c0) ((:) a ([]))))}
               in
               Logic.eq_rect_r (Datatypes.app (Datatypes.app b c0) ((:) a ([]))) iHHc2
                 (Datatypes.app b (Datatypes.app c0 ((:) a ([])))))) y0 c1 hc0 iHHc __) x c __) y1)
        x0 __ __ __;
     Coq_contracted_genR_I a0 x0 y1 a1 b c0 ->
      Logic.eq_rect_r x (\_ ->
        Logic.eq_rect_r y0 (\_ _ ->
          Logic.eq_rect_r
            (Datatypes.app a1
              (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0))))
            (\c1 _ ->
            Logic.eq_rect_r (Datatypes.app a1 (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0)))
              (\_ _ iHHc0 _ -> Coq_cont_multi_step
              (Datatypes.app
                (Datatypes.app a1
                  (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0))))
                ((:) a ([])))
              (Datatypes.app a1
                (Datatypes.app b (Datatypes.app ((:) a0 ([])) (Datatypes.app c0 ((:) a ([]))))))
              (Datatypes.app z0 ((:) a ([])))
              (let {
                _evar_0_ = let {
                            _evar_0_ = let {
                                        _evar_0_ = let {
                                                    _evar_0_ = let {
                                                                _evar_0_ = let {
                                                                            _evar_0_ = Coq_contracted_genR_I
                                                                             a0
                                                                             (Datatypes.app a1 ((:)
                                                                               a0
                                                                               (Datatypes.app b ((:)
                                                                                 a0
                                                                                 (Datatypes.app c0
                                                                                   ((:) a ([])))))))
                                                                             (Datatypes.app a1
                                                                               (Datatypes.app b
                                                                                 (Datatypes.app ((:)
                                                                                   a0 ([]))
                                                                                   (Datatypes.app c0
                                                                                     ((:) a ([]))))))
                                                                             a1 b
                                                                             (Datatypes.app c0 ((:) a
                                                                               ([])))}
                                                                           in
                                                                           Logic.eq_rect ((:) a0
                                                                             (Datatypes.app ([])
                                                                               (Datatypes.app c0 ((:)
                                                                                 a ([]))))) _evar_0_
                                                                             (Datatypes.app ((:) a0
                                                                               ([]))
                                                                               (Datatypes.app c0 ((:)
                                                                                 a ([]))))}
                                                               in
                                                               Logic.eq_rect ((:) a0
                                                                 (Datatypes.app ([])
                                                                   (Datatypes.app b
                                                                     (Datatypes.app ((:) a0 ([]))
                                                                       (Datatypes.app c0 ((:) a
                                                                         ([]))))))) _evar_0_
                                                                 (Datatypes.app ((:) a0 ([]))
                                                                   (Datatypes.app b
                                                                     (Datatypes.app ((:) a0 ([]))
                                                                       (Datatypes.app c0 ((:) a
                                                                         ([]))))))}
                                                   in
                                                   Logic.eq_rect
                                                     (Datatypes.app ((:) a0 ([]))
                                                       (Datatypes.app c0 ((:) a ([])))) _evar_0_
                                                     (Datatypes.app (Datatypes.app ((:) a0 ([])) c0)
                                                       ((:) a ([])))}
                                       in
                                       Logic.eq_rect
                                         (Datatypes.app b
                                           (Datatypes.app (Datatypes.app ((:) a0 ([])) c0) ((:) a
                                             ([])))) _evar_0_
                                         (Datatypes.app
                                           (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0)) ((:) a
                                           ([])))}
                           in
                           Logic.eq_rect
                             (Datatypes.app ((:) a0 ([]))
                               (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0)) ((:)
                                 a ([])))) _evar_0_
                             (Datatypes.app
                               (Datatypes.app ((:) a0 ([]))
                                 (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0))) ((:) a ([])))}
               in
               Logic.eq_rect
                 (Datatypes.app a1
                   (Datatypes.app
                     (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0)))
                     ((:) a ([])))) _evar_0_
                 (Datatypes.app
                   (Datatypes.app a1
                     (Datatypes.app ((:) a0 ([])) (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0))))
                   ((:) a ([]))))
              (let {
                iHHc1 = Logic.eq_rect_r
                          (Datatypes.app
                            (Datatypes.app a1 (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0)))
                            ((:) a ([]))) iHHc0
                          (Datatypes.app a1
                            (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0)) ((:) a
                              ([]))))}
               in
               let {
                iHHc2 = Logic.eq_rect_r
                          (Datatypes.app (Datatypes.app b (Datatypes.app ((:) a0 ([])) c0)) ((:) a
                            ([]))) iHHc1
                          (Datatypes.app b
                            (Datatypes.app (Datatypes.app ((:) a0 ([])) c0) ((:) a ([]))))}
               in
               Logic.eq_rect_r (Datatypes.app (Datatypes.app ((:) a0 ([])) c0) ((:) a ([]))) iHHc2
                 (Datatypes.app ((:) a0 ([])) (Datatypes.app c0 ((:) a ([])))))) y0 c1 hc0 iHHc __) x
            c __) y1) x0 __ __ __}) y z hc

contracted_multi_L :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_contracted_multi a1) ->
                      Coq_contracted_multi a1
contracted_multi_L x =
  Datatypes.list_rect (\_ _ hc -> hc) (\a x0 iHX y z hc ->
    contracted_multi_cons (Datatypes.app x0 y) (Datatypes.app x0 z) a (iHX y z hc)) x

contracted_multi_R :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_contracted_multi a1) ->
                      Coq_contracted_multi a1
contracted_multi_R x =
  Datatypes.list_rect (\y z hc ->
    Logic.eq_rect_r y (Logic.eq_rect_r z hc (Datatypes.app z ([]))) (Datatypes.app y ([])))
    (\a x0 iHX y z hc ->
    Logic.eq_rect_r (Datatypes.app ((:) a ([])) x0)
      (Logic.eq_rect_r (Datatypes.app (Datatypes.app y ((:) a ([]))) x0)
        (Logic.eq_rect_r (Datatypes.app (Datatypes.app z ((:) a ([]))) x0)
          (iHX (Datatypes.app y ((:) a ([]))) (Datatypes.app z ((:) a ([])))
            (contracted_multi_cons_tl y z a hc)) (Datatypes.app z (Datatypes.app ((:) a ([])) x0)))
        (Datatypes.app y (Datatypes.app ((:) a ([])) x0))) ((:) a x0)) x

contracted_multi_multi :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> Coq_contracted_multi a1
contracted_multi_multi _UU0393_ x =
  Datatypes.list_rect (\y z ->
    let {
     _evar_0_ = let {
                 _evar_0_ = let {
                             _evar_0_ = contracted_multi_R z
                                          (Datatypes.app (Datatypes.app _UU0393_ y) _UU0393_)
                                          (Datatypes.app _UU0393_ y)
                                          (let {
                                            _evar_0_ = Datatypes.list_rect (\y0 _ ->
                                                         Logic.eq_rect_r y0 (Coq_cont_multi_refl y0)
                                                           (Datatypes.app y0 ([])))
                                                         (\a _UU0393_0 iH_UU0393_ y0 z0 ->
                                                         Coq_cont_multi_step ((:) a
                                                         (Datatypes.app _UU0393_0
                                                           (Datatypes.app y0 ((:) a _UU0393_0))))
                                                         ((:) a
                                                         (Datatypes.app _UU0393_0
                                                           (Datatypes.app y0 _UU0393_0))) ((:) a
                                                         (Datatypes.app _UU0393_0 y0))
                                                         (contracted_gen__spec a ((:) a
                                                           (Datatypes.app _UU0393_0
                                                             (Datatypes.app y0 ((:) a _UU0393_0))))
                                                           ((:) a
                                                           (Datatypes.app _UU0393_0
                                                             (Datatypes.app y0 _UU0393_0)))
                                                           (Logic.eq_rect_r
                                                             (Datatypes.app ((:) a ([])) _UU0393_0)
                                                             (Logic.eq_rect_r
                                                               (Datatypes.app ((:) a ([]))
                                                                 (Datatypes.app _UU0393_0
                                                                   (Datatypes.app y0
                                                                     (Datatypes.app ((:) a ([]))
                                                                       _UU0393_0))))
                                                               (Logic.eq_rect_r
                                                                 (Datatypes.app ((:) a ([]))
                                                                   (Datatypes.app _UU0393_0
                                                                     (Datatypes.app y0 _UU0393_0)))
                                                                 (let {
                                                                   _evar_0_ = let {
                                                                               _evar_0_ = let {
                                                                                           _evar_0_ = 
                                                                                            Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            _UU0393_0)))))
                                                                                            (Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            (Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0
                                                                                            _UU0393_0)))
                                                                                            (let {
                                                                                            _evar_0_ = 
                                                                                            let {
                                                                                            _evar_0_ = 
                                                                                            let {
                                                                                            _evar_0_ = 
                                                                                            let {
                                                                                            _evar_0_ = 
                                                                                            let {
                                                                                            _evar_0_ = 
                                                                                            cont_gen_spec_R
                                                                                            a
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            y0) ((:)
                                                                                            a ([])))
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            y0)
                                                                                            _UU0393_0
                                                                                            (Logic.eq_rect
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            ([]))))
                                                                                            (Logic.eq_rect
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            ([])))))
                                                                                            (Logic.eq_rect
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            y0))
                                                                                            (Logic.eq_rect
                                                                                            ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            ([]))))))
                                                                                            (Logic.eq_rect
                                                                                            ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            y0)))
                                                                                            (Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            ([]))))))
                                                                                            (Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            y0)))
                                                                                            (Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            ([]))))
                                                                                            (Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            y0)
                                                                                            (Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            y0) ((:)
                                                                                            a ([])))
                                                                                            (cont_gen_spec_rem_sml_L
                                                                                            a
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            y0))
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            ([])))))
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            y0)))
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            ([]))))))
                                                                                            ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            y0))))
                                                                                            ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            ([])))))))
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            y0)))
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            ([]))))))
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            y0))
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            ([])))))
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            y0) ((:)
                                                                                            a ([]))))}
                                                                                            in
                                                                                            Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            y0)
                                                                                            _UU0393_0)
                                                                                            _evar_0_
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            (Datatypes.app
                                                                                            y0
                                                                                            _UU0393_0))}
                                                                                            in
                                                                                            Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            (Datatypes.app
                                                                                            y0
                                                                                            _UU0393_0))
                                                                                            _evar_0_
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0
                                                                                            _UU0393_0)))}
                                                                                            in
                                                                                            Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            y0) ((:)
                                                                                            a ([])))
                                                                                            _UU0393_0)
                                                                                            _evar_0_
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            y0)
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0))}
                                                                                            in
                                                                                            Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            y0)
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0))
                                                                                            _evar_0_
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            (Datatypes.app
                                                                                            y0
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)))}
                                                                                            in
                                                                                            Logic.eq_rect_r
                                                                                            (Datatypes.app
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)
                                                                                            (Datatypes.app
                                                                                            y0
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)))
                                                                                            _evar_0_
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            _UU0393_0)))))
                                                                                            ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0
                                                                                            _UU0393_0)))))
                                                                                            ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            _UU0393_0)))
                                                                                            ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0 ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            _UU0393_0))))))}
                                                                                          in
                                                                                          Logic.eq_rect
                                                                                            ((:) a
                                                                                            (Datatypes.app
                                                                                            ([])
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0
                                                                                            _UU0393_0))))
                                                                                            _evar_0_
                                                                                            (Datatypes.app
                                                                                            ((:) a
                                                                                            ([]))
                                                                                            (Datatypes.app
                                                                                            _UU0393_0
                                                                                            (Datatypes.app
                                                                                            y0
                                                                                            _UU0393_0)))}
                                                                              in
                                                                              Logic.eq_rect ((:) a
                                                                                (Datatypes.app ([])
                                                                                  _UU0393_0))
                                                                                _evar_0_
                                                                                (Datatypes.app ((:) a
                                                                                  ([])) _UU0393_0)}
                                                                  in
                                                                  Logic.eq_rect ((:) a
                                                                    (Datatypes.app ([])
                                                                      (Datatypes.app _UU0393_0
                                                                        (Datatypes.app y0
                                                                          (Datatypes.app ((:) a ([]))
                                                                            _UU0393_0))))) _evar_0_
                                                                    (Datatypes.app ((:) a ([]))
                                                                      (Datatypes.app _UU0393_0
                                                                        (Datatypes.app y0
                                                                          (Datatypes.app ((:) a ([]))
                                                                            _UU0393_0))))) ((:) a
                                                                 (Datatypes.app _UU0393_0
                                                                   (Datatypes.app y0 _UU0393_0))))
                                                               ((:) a
                                                               (Datatypes.app _UU0393_0
                                                                 (Datatypes.app y0
                                                                   (Datatypes.app ((:) a ([]))
                                                                     _UU0393_0))))) ((:) a
                                                             _UU0393_0)))
                                                         (contracted_multi_cons
                                                           (Datatypes.app _UU0393_0
                                                             (Datatypes.app y0 _UU0393_0))
                                                           (Datatypes.app _UU0393_0 y0) a
                                                           (iH_UU0393_ y0 z0))) _UU0393_ y z}
                                           in
                                           Logic.eq_rect
                                             (Datatypes.app _UU0393_ (Datatypes.app y _UU0393_))
                                             _evar_0_
                                             (Datatypes.app (Datatypes.app _UU0393_ y) _UU0393_))}
                            in
                            Logic.eq_rect_r (Datatypes.app (Datatypes.app _UU0393_ y) z) _evar_0_
                              (Datatypes.app _UU0393_ (Datatypes.app y z))}
                in
                Logic.eq_rect_r (Datatypes.app (Datatypes.app (Datatypes.app _UU0393_ y) _UU0393_) z)
                  _evar_0_ (Datatypes.app (Datatypes.app _UU0393_ y) (Datatypes.app _UU0393_ z))}
    in
    Logic.eq_rect_r (Datatypes.app (Datatypes.app _UU0393_ y) (Datatypes.app _UU0393_ z)) _evar_0_
      (Datatypes.app _UU0393_ (Datatypes.app y (Datatypes.app _UU0393_ z)))) (\a x0 iHX y z ->
    contracted_multi_cons
      (Datatypes.app x0 (Datatypes.app _UU0393_ (Datatypes.app y (Datatypes.app _UU0393_ z))))
      (Datatypes.app x0 (Datatypes.app _UU0393_ (Datatypes.app y z))) a (iHX y z)) x

contracted_multi_double :: (([]) a1) -> Coq_contracted_multi a1
contracted_multi_double _UU0393_ =
  let {hass = contracted_multi_multi _UU0393_ ([]) ([]) ([])} in
  let {hass0 = Logic.eq_rect (Datatypes.app _UU0393_ ([])) hass _UU0393_} in
  Logic.eq_rect (Datatypes.app _UU0393_ ([])) hass0 _UU0393_

contracted_seq_double :: (([]) a1) -> (([]) a1) -> LntT.Coq_dir -> Coq_contracted_seq a1
contracted_seq_double _UU0393_ _UU0394_ d =
  Coq_cont_seq_stepL ((,) ((,) (Datatypes.app _UU0393_ _UU0393_) (Datatypes.app _UU0394_ _UU0394_))
    d) ((,) ((,) _UU0393_ (Datatypes.app _UU0394_ _UU0394_)) d) ((,) ((,) _UU0393_ _UU0394_) d)
    (Coq_cont_seqL (Datatypes.app _UU0393_ _UU0393_) _UU0393_ (Datatypes.app _UU0394_ _UU0394_) d
    (contracted_multi_double _UU0393_)) (Coq_cont_seq_baseR ((,) ((,) _UU0393_
    (Datatypes.app _UU0394_ _UU0394_)) d) ((,) ((,) _UU0393_ _UU0394_) d) (Coq_cont_seqR
    (Datatypes.app _UU0394_ _UU0394_) _UU0394_ _UU0393_ d (contracted_multi_double _UU0394_)))

contracted_seq_refl :: ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir) -> Coq_contracted_seq a1
contracted_seq_refl s =
  case s of {
   (,) p x ->
    case p of {
     (,) _UU0393_ _UU0394_ -> Coq_cont_seq_baseL ((,) ((,) _UU0393_ _UU0394_) x) ((,) ((,) _UU0393_
      _UU0394_) x) (Coq_cont_seqL _UU0393_ _UU0393_ _UU0394_ x (Coq_cont_multi_refl _UU0393_))}}

contracted_multi_seq :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> LntT.Coq_dir ->
                        (Coq_contracted_multi a1) -> (Coq_contracted_multi a1) -> Coq_contracted_seq
                        a1
contracted_multi_seq g1 g2 h1 h2 d x x0 =
  Coq_cont_seq_stepL ((,) ((,) g1 h1) d) ((,) ((,) g2 h1) d) ((,) ((,) g2 h2) d) (Coq_cont_seqL g1 g2
    h1 d x) (Coq_cont_seq_baseR ((,) ((,) g2 h1) d) ((,) ((,) g2 h2) d) (Coq_cont_seqR h1 h2 g2 d
    x0))

contracted_nseq_refl :: (([]) ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> Coq_contracted_nseq a1
contracted_nseq_refl ns =
  Datatypes.list_rect Coq_cont_nseq_nil (\a ns0 iHns -> Coq_cont_nseq_cons a a ns0 ns0
    (contracted_seq_refl a) iHns) ns

contracted_nseq_app :: (([]) ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                       ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                       ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (([])
                       ((,) ((,) (([]) a1) (([]) a1)) LntT.Coq_dir)) -> (Coq_contracted_nseq 
                       a1) -> (Coq_contracted_nseq a1) -> Coq_contracted_nseq a1
contracted_nseq_app l1 =
  Datatypes.list_rect (\_ l3 _ h1 h2 ->
    case h1 of {
     Coq_cont_nseq_nil -> Logic.eq_rect ([]) h2 l3;
     Coq_cont_nseq_cons _ _ _ _ x x0 -> Logic.coq_False_rect __ x x0}) (\a l2 iHl1 l3 l4 l5 h1 h2 ->
    case h1 of {
     Coq_cont_nseq_nil -> Logic.coq_False_rect __;
     Coq_cont_nseq_cons s1 s2 ns1 ns2 x x0 ->
      Logic.eq_rect_r a (\_ ->
        Logic.eq_rect_r l2 (\_ ->
          Logic.eq_rect ((:) s2 ns2) (\x1 x2 ->
            Logic.eq_rect ((:) s2 ns2) (\_ -> Coq_cont_nseq_cons a s2 (Datatypes.app l2 l3)
              (Datatypes.app ns2 l5) x1 (iHl1 l3 ns2 l5 x2 h2)) l4 h1) l4) ns1) s1 __ __ x x0}) l1

contracted_nseq_single :: (([]) a1) -> (([]) a1) -> LntT.Coq_dir -> Coq_contracted_nseq a1
contracted_nseq_single l1 l2 d =
  Coq_cont_nseq_cons ((,) ((,) (Datatypes.app l1 l1) (Datatypes.app l2 l2)) d) ((,) ((,) l1 l2) d)
    ([]) ([]) (contracted_seq_double l1 l2 d) Coq_cont_nseq_nil

contracted_multi_trans :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_contracted_multi a1) ->
                          (Coq_contracted_multi a1) -> Coq_contracted_multi a1
contracted_multi_trans x y z x0 x1 =
  contracted_multi_rect (\_ x2 -> x2) (\x2 y0 _ c _ iHX0 x3 -> Coq_cont_multi_step x2 y0 z c
    (iHX0 x3)) x y x0 x1

contracted_gen_InT_rev :: (([]) a1) -> (([]) a1) -> (Coq_contracted_gen a1) -> a1 -> (GenT.InT 
                          a1) -> GenT.InT a1
contracted_gen_InT_rev _UU0393_ _UU03a3_ hc =
  case hc of {
   Coq_contracted_genL_I a x y a0 b c ->
    Logic.eq_rect_r _UU0393_ (\_ ->
      Logic.eq_rect_r _UU03a3_ (\_ _ b0 hin ->
        Logic.eq_rect_r
          (Datatypes.app a0
            (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
          (\hc0 _ hin0 ->
          Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c)))
            (\_ _ ->
            let {
             hin1 = GenT.coq_InT_appE b0 a0
                      (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))
                      hin0}
            in
            case hin1 of {
             Prelude.Left hin2 ->
              GenT.coq_InT_appL b0 a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c)) hin2;
             Prelude.Right hin2 ->
              let {
               hin3 = GenT.coq_InT_appE b0 ((:) a ([]))
                        (Datatypes.app b (Datatypes.app ((:) a ([])) c)) hin2}
              in
              case hin3 of {
               Prelude.Left hin4 ->
                GenT.coq_InT_appR b0 a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c))
                  (GenT.coq_InT_appL b0 ((:) a ([])) (Datatypes.app b c) hin4);
               Prelude.Right hin4 ->
                let {hin5 = GenT.coq_InT_appE b0 b (Datatypes.app ((:) a ([])) c) hin4} in
                case hin5 of {
                 Prelude.Left hin6 ->
                  GenT.coq_InT_appR b0 a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c))
                    (GenT.coq_InT_appR b0 ((:) a ([])) (Datatypes.app b c)
                      (GenT.coq_InT_appL b0 b c hin6));
                 Prelude.Right hin6 ->
                  let {hin7 = GenT.coq_InT_appE b0 ((:) a ([])) c hin6} in
                  case hin7 of {
                   Prelude.Left hin8 ->
                    GenT.coq_InT_appR b0 a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c))
                      (GenT.coq_InT_appL b0 ((:) a ([])) (Datatypes.app b c) hin8);
                   Prelude.Right hin8 ->
                    GenT.coq_InT_appR b0 a0 (Datatypes.app ((:) a ([])) (Datatypes.app b c))
                      (GenT.coq_InT_appR b0 ((:) a ([])) (Datatypes.app b c)
                        (GenT.coq_InT_appR b0 b c hin8))}}}}) _UU03a3_ hc0 __) _UU0393_ hc __ hin) y)
      x __ __ __;
   Coq_contracted_genR_I a x y a0 b c ->
    Logic.eq_rect_r _UU0393_ (\_ ->
      Logic.eq_rect_r _UU03a3_ (\_ _ b0 hin ->
        Logic.eq_rect_r
          (Datatypes.app a0
            (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c))))
          (\hc0 _ hin0 ->
          Logic.eq_rect_r (Datatypes.app a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c)))
            (\_ _ ->
            let {
             hin1 = GenT.coq_InT_appE b0 a0
                      (Datatypes.app ((:) a ([])) (Datatypes.app b (Datatypes.app ((:) a ([])) c)))
                      hin0}
            in
            case hin1 of {
             Prelude.Left hin2 ->
              GenT.coq_InT_appL b0 a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c)) hin2;
             Prelude.Right hin2 ->
              let {
               hin3 = GenT.coq_InT_appE b0 ((:) a ([]))
                        (Datatypes.app b (Datatypes.app ((:) a ([])) c)) hin2}
              in
              case hin3 of {
               Prelude.Left hin4 ->
                GenT.coq_InT_appR b0 a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c))
                  (GenT.coq_InT_appR b0 b (Datatypes.app ((:) a ([])) c)
                    (GenT.coq_InT_appL b0 ((:) a ([])) c hin4));
               Prelude.Right hin4 ->
                let {hin5 = GenT.coq_InT_appE b0 b (Datatypes.app ((:) a ([])) c) hin4} in
                case hin5 of {
                 Prelude.Left hin6 ->
                  GenT.coq_InT_appR b0 a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c))
                    (GenT.coq_InT_appL b0 b (Datatypes.app ((:) a ([])) c) hin6);
                 Prelude.Right hin6 ->
                  let {hin7 = GenT.coq_InT_appE b0 ((:) a ([])) c hin6} in
                  case hin7 of {
                   Prelude.Left hin8 ->
                    GenT.coq_InT_appR b0 a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c))
                      (GenT.coq_InT_appR b0 b (Datatypes.app ((:) a ([])) c)
                        (GenT.coq_InT_appL b0 ((:) a ([])) c hin8));
                   Prelude.Right hin8 ->
                    GenT.coq_InT_appR b0 a0 (Datatypes.app b (Datatypes.app ((:) a ([])) c))
                      (GenT.coq_InT_appR b0 b (Datatypes.app ((:) a ([])) c)
                        (GenT.coq_InT_appR b0 ((:) a ([])) c hin8))}}}}) _UU03a3_ hc0 __) _UU0393_ hc
          __ hin) y) x __ __ __}

contracted_multi_InT_rev :: (([]) a1) -> (([]) a1) -> (Coq_contracted_multi a1) -> a1 -> (GenT.InT
                            a1) -> GenT.InT a1
contracted_multi_InT_rev _UU0393_ _UU03a3_ hc =
  contracted_multi_rec (\_ _ hin -> hin) (\x y _ c _ iHHc b hin ->
    iHHc b (contracted_gen_InT_rev x y c b hin)) _UU0393_ _UU03a3_ hc

contracted_multi_insertL_pre :: (([]) a1) -> (([]) a1) -> a1 -> (GenT.InT a1) ->
                                (Coq_contracted_multi a1) -> Coq_contracted_multi a1
contracted_multi_insertL_pre l1 l3 a hin hc =
  contracted_multi_rect (\x hin0 -> Coq_cont_multi_step (Datatypes.app ((:) a ([])) x) x x
    (let {hin1 = GenT.coq_InT_split a x hin0} in
     case hin1 of {
      Specif.Coq_existT l2 s ->
       case s of {
        Specif.Coq_existT l4 _ ->
         Logic.eq_rect_r (Datatypes.app l2 ((:) a l4))
           (Logic.eq_rect ((:) a (Datatypes.app ([]) (Datatypes.app l2 ((:) a l4))))
             (Logic.eq_rect_r
               (Datatypes.app ((:) a ([])) (Datatypes.app ([]) (Datatypes.app l2 ((:) a l4))))
               (Logic.eq_rect_r (Datatypes.app ((:) a ([])) l4)
                 (Logic.eq_rect_r (Datatypes.app l2 (Datatypes.app ((:) a ([])) l4))
                   (Logic.eq_rect
                     (Datatypes.app ([])
                       (Datatypes.app ((:) a ([]))
                         (Datatypes.app l2 (Datatypes.app ((:) a ([])) l4)))) (Coq_contracted_genR_I
                     a
                     (Datatypes.app ([])
                       (Datatypes.app ((:) a ([]))
                         (Datatypes.app l2 (Datatypes.app ((:) a ([])) l4))))
                     (Datatypes.app l2 (Datatypes.app ((:) a ([])) l4)) ([]) l2 l4)
                     (Datatypes.app ((:) a ([])) (Datatypes.app l2 (Datatypes.app ((:) a ([])) l4))))
                   (Datatypes.app ([]) (Datatypes.app l2 (Datatypes.app ((:) a ([])) l4)))) ((:) a
                 l4)) ((:) a (Datatypes.app ([]) (Datatypes.app l2 ((:) a l4)))))
             (Datatypes.app ((:) a ([])) (Datatypes.app l2 ((:) a l4)))) x}}) (Coq_cont_multi_refl
    x)) (\x y z c _ iHHc hin0 ->
    contracted_multi_trans (Datatypes.app ((:) a ([])) x) (Datatypes.app ((:) a ([])) y) z
      (contracted_multi_cons x y a (Coq_cont_multi_step x y y c (Coq_cont_multi_refl y)))
      (iHHc (contracted_gen_InT_rev x y c a hin0))) l1 l3 hc hin

contracted_multi_insertL :: (([]) a1) -> (([]) a1) -> (([]) a1) -> a1 -> (Prelude.Either
                            (GenT.InT a1) (GenT.InT a1)) -> (Coq_contracted_multi a1) ->
                            Coq_contracted_multi a1
contracted_multi_insertL l1 l2 l3 a hin hc =
  Coq_cont_multi_step (Datatypes.app l1 (Datatypes.app ((:) a ([])) l2)) (Datatypes.app l1 l2) l3
    (case hin of {
      Prelude.Left hin0 ->
       Logic.eq_rect_r (Datatypes.app (Datatypes.app l1 ((:) a ([]))) l2)
         (cont_gen_R (Datatypes.app l1 ((:) a ([]))) l1 l2
           (let {hin1 = GenT.coq_InT_split a l1 hin0} in
            case hin1 of {
             Specif.Coq_existT l1' s ->
              case s of {
               Specif.Coq_existT l2' _ ->
                Logic.eq_rect_r (Datatypes.app l1' ((:) a l2')) (\_ ->
                  Logic.eq_rect (Datatypes.app l1' (Datatypes.app ((:) a l2') ((:) a ([]))))
                    (Logic.eq_rect ((:) a (Datatypes.app l2' ((:) a ([]))))
                      (Logic.eq_rect_r (Datatypes.app ((:) a ([])) (Datatypes.app l2' ((:) a ([]))))
                        (Logic.eq_rect_r (Datatypes.app ((:) a ([])) l2')
                          (Logic.eq_rect (Datatypes.app ((:) a ([])) ([])) (Coq_contracted_genL_I a
                            (Datatypes.app l1'
                              (Datatypes.app (Datatypes.app ((:) a ([])) ([]))
                                (Datatypes.app l2' (Datatypes.app ((:) a ([])) ([])))))
                            (Datatypes.app l1' (Datatypes.app (Datatypes.app ((:) a ([])) ([])) l2'))
                            l1' l2' ([])) ((:) a ([]))) ((:) a l2')) ((:) a
                        (Datatypes.app l2' ((:) a ([]))))) (Datatypes.app ((:) a l2') ((:) a ([]))))
                    (Datatypes.app (Datatypes.app l1' ((:) a l2')) ((:) a ([])))) l1 hc}}))
         (Datatypes.app l1 (Datatypes.app ((:) a ([])) l2));
      Prelude.Right hin0 ->
       cont_gen_L (Datatypes.app ((:) a ([])) l2) l2 l1
         (let {hin1 = GenT.coq_InT_split a l2 hin0} in
          case hin1 of {
           Specif.Coq_existT l1' s ->
            case s of {
             Specif.Coq_existT l2' _ ->
              Logic.eq_rect_r (Datatypes.app l1' ((:) a l2')) (\_ ->
                Logic.eq_rect ((:) a (Datatypes.app ([]) (Datatypes.app l1' ((:) a l2'))))
                  (Logic.eq_rect_r
                    (Datatypes.app ((:) a ([])) (Datatypes.app ([]) (Datatypes.app l1' ((:) a l2'))))
                    (Logic.eq_rect_r (Datatypes.app ((:) a ([])) l2')
                      (Logic.eq_rect_r (Datatypes.app l1' (Datatypes.app ((:) a ([])) l2'))
                        (Logic.eq_rect (Datatypes.app ([]) ((:) a ([])))
                          (Logic.eq_rect
                            (Datatypes.app ([])
                              (Datatypes.app ((:) a ([]))
                                (Datatypes.app l1'
                                  (Datatypes.app (Datatypes.app ([]) ((:) a ([]))) l2'))))
                            (Logic.eq_rect (Datatypes.app ([]) (Datatypes.app ((:) a ([])) l2'))
                              (Coq_contracted_genR_I a
                              (Datatypes.app ([])
                                (Datatypes.app ((:) a ([]))
                                  (Datatypes.app l1'
                                    (Datatypes.app ([]) (Datatypes.app ((:) a ([])) l2')))))
                              (Datatypes.app l1'
                                (Datatypes.app ([]) (Datatypes.app ((:) a ([])) l2'))) ([]) l1' l2')
                              (Datatypes.app (Datatypes.app ([]) ((:) a ([]))) l2'))
                            (Datatypes.app (Datatypes.app ([]) ((:) a ([])))
                              (Datatypes.app l1'
                                (Datatypes.app (Datatypes.app ([]) ((:) a ([]))) l2')))) ((:) a
                          ([])))
                        (Datatypes.app ([]) (Datatypes.app l1' (Datatypes.app ((:) a ([])) l2'))))
                      ((:) a l2')) ((:) a (Datatypes.app ([]) (Datatypes.app l1' ((:) a l2')))))
                  (Datatypes.app ((:) a ([])) (Datatypes.app l1' ((:) a l2')))) l2 hc}})}) hc

contracted_multi_appR_InT :: (([]) a1) -> (([]) a1) -> (a1 -> (GenT.InT a1) -> GenT.InT a1) ->
                             Coq_contracted_multi a1
contracted_multi_appR_InT _UU0393_ _UU03a3_ =
  Datatypes.list_rec (\_UU0393_0 _ -> Coq_cont_multi_refl _UU0393_0)
    (\a _UU03a3_0 iH_UU03a3_ _UU0393_0 h ->
    let {h2 = h a (GenT.InT_eq' a _UU03a3_0)} in
    contracted_multi_insertL_pre (Datatypes.app _UU03a3_0 _UU0393_0) _UU0393_0 a
      (GenT.coq_InT_appR a _UU03a3_0 _UU0393_0 h2)
      (iH_UU03a3_ _UU0393_0 (\b hb -> h b (GenT.InT_cons a _UU03a3_0 hb)))) _UU03a3_ _UU0393_

contracted_multi_appR_rev :: (([]) a1) -> (([]) a1) -> (Coq_contracted_multi a1) ->
                             Coq_contracted_multi a1
contracted_multi_appR_rev _UU0393_ _UU03a3_ h =
  contracted_multi_appR_InT _UU0393_ _UU03a3_ (contracted_multi_InT_rev _UU03a3_ _UU0393_ h)

contracted_seq_multiR :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> LntT.Coq_dir ->
                         LntT.Coq_dir -> (Coq_contracted_seq a1) -> Coq_contracted_multi a1
contracted_seq_multiR _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d1 d2 h =
  let {s1 = (,) ((,) _UU0393_ _UU0394_) d1} in
  let {s2 = (,) ((,) _UU03a3_ _UU03a0_) d2} in
  contracted_seq_rec (\s3 s4 c _UU0393_0 _UU0394_0 _UU03a3_0 _UU03a0_0 d3 d4 _ _ ->
    Logic.eq_rec_r ((,) ((,) _UU0393_0 _UU0394_0) d3) (\c0 ->
      Logic.eq_rec_r ((,) ((,) _UU03a3_0 _UU03a0_0) d4) (\c1 ->
        case c1 of {
         Coq_cont_seqL x y _UU0394_1 d h0 ->
          Logic.eq_rec_r _UU0393_0 (\_ ->
            Logic.eq_rec_r _UU0394_0 (\_ ->
              Logic.eq_rec_r d3 (\_ ->
                Logic.eq_rec_r _UU03a3_0 (\_ ->
                  Logic.eq_rec_r _UU03a0_0 (\_ ->
                    Logic.eq_rec_r d4 (\_ ->
                      Logic.eq_rec_r _UU03a0_0 (\c2 ->
                        Logic.eq_rec_r d4 (\_ -> Coq_cont_multi_refl _UU03a0_0) d3 c2) _UU0394_0 c1)
                      d3) _UU0394_0) y __ __) d) _UU0394_1) x __ __ __ h0}) s4 c0) s3 c)
    (\s3 s4 c _UU0393_0 _UU0394_0 _UU03a3_0 _UU03a0_0 d3 d4 _ _ ->
    Logic.eq_rec_r ((,) ((,) _UU0393_0 _UU0394_0) d3) (\c0 ->
      Logic.eq_rec_r ((,) ((,) _UU03a3_0 _UU03a0_0) d4) (\c1 ->
        case c1 of {
         Coq_cont_seqR x y _UU0393_1 d h0 ->
          Logic.eq_rec_r _UU0393_0 (\_ ->
            Logic.eq_rec_r _UU0394_0 (\_ ->
              Logic.eq_rec_r d3 (\_ ->
                Logic.eq_rec_r _UU03a3_0 (\_ ->
                  Logic.eq_rec_r _UU03a0_0 (\_ ->
                    Logic.eq_rec_r d4 (\h1 ->
                      Logic.eq_rec_r _UU03a3_0 (\c2 -> Logic.eq_rec_r d4 (\_ -> h1) d3 c2) _UU0393_0
                        c1) d3) y) _UU0393_0 __ __) d) x) _UU0393_1 __ __ __ h0}) s4 c0) s3 c)
    (\s3 s4 s5 c h0 iHcontracted_seq _UU0393_0 _UU0394_0 _UU03a3_0 _UU03a0_0 d3 d4 _ _ ->
    Logic.eq_rec_r ((,) ((,) _UU0393_0 _UU0394_0) d3) (\c0 ->
      Logic.eq_rec_r ((,) ((,) _UU03a3_0 _UU03a0_0) d4) (\h1 iHcontracted_seq0 ->
        case c0 of {
         Coq_cont_seqL x y _UU0394_1 d h2 ->
          Logic.eq_rec_r _UU0393_0 (\_ ->
            Logic.eq_rec_r _UU0394_0 (\_ ->
              Logic.eq_rec_r d3 (\_ ->
                Logic.eq_rec ((,) ((,) y _UU0394_0) d3) (\_ ->
                  Logic.eq_rec ((,) ((,) y _UU0394_0) d3) (\_ iHcontracted_seq1 _ ->
                    iHcontracted_seq1 y _UU0394_0 _UU03a3_0 _UU03a0_0 d3 d4 __ __) s4 c0
                    iHcontracted_seq0 h1) s4) d) _UU0394_1) x __ __ __ h2}) s5 h0 iHcontracted_seq)
      s3 c) (\s3 s4 s5 c h0 iHcontracted_seq _UU0393_0 _UU0394_0 _UU03a3_0 _UU03a0_0 d3 d4 _ _ ->
    Logic.eq_rec_r ((,) ((,) _UU0393_0 _UU0394_0) d3) (\c0 ->
      Logic.eq_rec_r ((,) ((,) _UU03a3_0 _UU03a0_0) d4) (\h1 iHcontracted_seq0 ->
        case c0 of {
         Coq_cont_seqR x y _UU0393_1 d h2 ->
          Logic.eq_rec_r _UU0393_0 (\_ ->
            Logic.eq_rec_r _UU0394_0 (\_ ->
              Logic.eq_rec_r d3 (\_ ->
                Logic.eq_rec ((,) ((,) _UU0393_0 y) d3) (\h4 ->
                  Logic.eq_rec ((,) ((,) _UU0393_0 y) d3) (\_ iHcontracted_seq1 _ ->
                    let {h3 = iHcontracted_seq1 _UU0393_0 y _UU03a3_0 _UU03a0_0 d3 d4 __ __} in
                    contracted_multi_trans _UU0394_0 y _UU03a0_0 h4 h3) s4 c0 iHcontracted_seq0 h1)
                  s4) d) x) _UU0393_1 __ __ __ h2}) s5 h0 iHcontracted_seq) s3 c) s1 s2 h _UU0393_
    _UU0394_ _UU03a3_ _UU03a0_ d1 d2 __ __

contracted_seq_multiL :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> LntT.Coq_dir ->
                         LntT.Coq_dir -> (Coq_contracted_seq a1) -> Coq_contracted_multi a1
contracted_seq_multiL _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d1 d2 h =
  let {s1 = (,) ((,) _UU0393_ _UU0394_) d1} in
  let {s2 = (,) ((,) _UU03a3_ _UU03a0_) d2} in
  contracted_seq_rec (\s3 s4 c _UU0393_0 _UU0394_0 _UU03a3_0 _UU03a0_0 d3 d4 _ _ ->
    Logic.eq_rec_r ((,) ((,) _UU0393_0 _UU0394_0) d3) (\c0 ->
      Logic.eq_rec_r ((,) ((,) _UU03a3_0 _UU03a0_0) d4) (\c1 ->
        case c1 of {
         Coq_cont_seqL x y _UU0394_1 d h0 ->
          Logic.eq_rec_r _UU0393_0 (\_ ->
            Logic.eq_rec_r _UU0394_0 (\_ ->
              Logic.eq_rec_r d3 (\_ ->
                Logic.eq_rec_r _UU03a3_0 (\_ ->
                  Logic.eq_rec_r _UU03a0_0 (\_ ->
                    Logic.eq_rec_r d4 (\h1 ->
                      Logic.eq_rec_r _UU03a0_0 (\c2 -> Logic.eq_rec_r d4 (\_ -> h1) d3 c2) _UU0394_0
                        c1) d3) _UU0394_0) y __ __) d) _UU0394_1) x __ __ __ h0}) s4 c0) s3 c)
    (\s3 s4 c _UU0393_0 _UU0394_0 _UU03a3_0 _UU03a0_0 d3 d4 _ _ ->
    Logic.eq_rec_r ((,) ((,) _UU0393_0 _UU0394_0) d3) (\c0 ->
      Logic.eq_rec_r ((,) ((,) _UU03a3_0 _UU03a0_0) d4) (\c1 ->
        case c1 of {
         Coq_cont_seqR x y _UU0393_1 d h0 ->
          Logic.eq_rec_r _UU0393_0 (\_ ->
            Logic.eq_rec_r _UU0394_0 (\_ ->
              Logic.eq_rec_r d3 (\_ ->
                Logic.eq_rec_r _UU03a3_0 (\_ ->
                  Logic.eq_rec_r _UU03a0_0 (\_ ->
                    Logic.eq_rec_r d4 (\_ ->
                      Logic.eq_rec_r _UU03a3_0 (\c2 ->
                        Logic.eq_rec_r d4 (\_ -> Coq_cont_multi_refl _UU03a3_0) d3 c2) _UU0393_0 c1)
                      d3) y) _UU0393_0 __ __) d) x) _UU0393_1 __ __ __ h0}) s4 c0) s3 c)
    (\s3 s4 s5 c h0 iHcontracted_seq _UU0393_0 _UU0394_0 _UU03a3_0 _UU03a0_0 d3 d4 _ _ ->
    Logic.eq_rec_r ((,) ((,) _UU0393_0 _UU0394_0) d3) (\c0 ->
      Logic.eq_rec_r ((,) ((,) _UU03a3_0 _UU03a0_0) d4) (\h1 iHcontracted_seq0 ->
        case c0 of {
         Coq_cont_seqL x y _UU0394_1 d h2 ->
          Logic.eq_rec_r _UU0393_0 (\_ ->
            Logic.eq_rec_r _UU0394_0 (\_ ->
              Logic.eq_rec_r d3 (\_ ->
                Logic.eq_rec ((,) ((,) y _UU0394_0) d3) (\h4 ->
                  Logic.eq_rec ((,) ((,) y _UU0394_0) d3) (\_ iHcontracted_seq1 _ ->
                    let {h3 = iHcontracted_seq1 y _UU0394_0 _UU03a3_0 _UU03a0_0 d3 d4 __ __} in
                    contracted_multi_trans _UU0393_0 y _UU03a3_0 h4 h3) s4 c0 iHcontracted_seq0 h1)
                  s4) d) _UU0394_1) x __ __ __ h2}) s5 h0 iHcontracted_seq) s3 c)
    (\s3 s4 s5 c h0 iHcontracted_seq _UU0393_0 _UU0394_0 _UU03a3_0 _UU03a0_0 d3 d4 _ _ ->
    Logic.eq_rec_r ((,) ((,) _UU0393_0 _UU0394_0) d3) (\c0 ->
      Logic.eq_rec_r ((,) ((,) _UU03a3_0 _UU03a0_0) d4) (\h1 iHcontracted_seq0 ->
        case c0 of {
         Coq_cont_seqR x y _UU0393_1 d h2 ->
          Logic.eq_rec_r _UU0393_0 (\_ ->
            Logic.eq_rec_r _UU0394_0 (\_ ->
              Logic.eq_rec_r d3 (\_ ->
                Logic.eq_rec ((,) ((,) _UU0393_0 y) d3) (\_ ->
                  Logic.eq_rec ((,) ((,) _UU0393_0 y) d3) (\_ iHcontracted_seq1 _ ->
                    iHcontracted_seq1 _UU0393_0 y _UU03a3_0 _UU03a0_0 d3 d4 __ __) s4 c0
                    iHcontracted_seq0 h1) s4) d) x) _UU0393_1 __ __ __ h2}) s5 h0 iHcontracted_seq)
      s3 c) s1 s2 h _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d1 d2 __ __

contracted_seq_merge_app2R_rev :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (([]) a1) -> LntT.Coq_dir ->
                                  (Coq_contracted_seq a1) -> Coq_contracted_seq a1
contracted_seq_merge_app2R_rev _UU0393_ _UU0394_ _UU03a3_ _UU03a0_ d h =
  Coq_cont_seq_stepR ((,) ((,) (Datatypes.app _UU03a3_ _UU0393_) (Datatypes.app _UU03a0_ _UU0394_))
    d) ((,) ((,) (Datatypes.app _UU03a3_ _UU0393_) _UU0394_) d) ((,) ((,) _UU0393_ _UU0394_) d)
    (Coq_cont_seqR (Datatypes.app _UU03a0_ _UU0394_) _UU0394_ (Datatypes.app _UU03a3_ _UU0393_) d
    (contracted_multi_appR_rev _UU0394_ _UU03a0_
      (contracted_seq_multiR _UU03a3_ _UU03a0_ _UU0393_ _UU0394_ d d h))) (Coq_cont_seq_baseL ((,)
    ((,) (Datatypes.app _UU03a3_ _UU0393_) _UU0394_) d) ((,) ((,) _UU0393_ _UU0394_) d)
    (Coq_cont_seqL (Datatypes.app _UU03a3_ _UU0393_) _UU0393_ _UU0394_ d
    (contracted_multi_appR_rev _UU0393_ _UU03a3_
      (contracted_seq_multiL _UU03a3_ _UU03a0_ _UU0393_ _UU0394_ d d h))))

contracted_multi_appR_inclT :: (([]) a1) -> (([]) a1) -> (InclT.Coq_inclT a1) -> Coq_contracted_multi
                               a1
contracted_multi_appR_inclT l1 l2 =
  Datatypes.list_rect (\_ -> Logic.eq_rect_r l1 (Coq_cont_multi_refl l1) (Datatypes.app l1 ([])))
    (\a l3 iHL2 hincl ->
    let {hin = InclT.inclT_consL_InT l3 l1 a hincl} in
    let {hincl2 = InclT.inclT_consL_inclT l3 l1 a hincl} in
    Logic.eq_rect_r (Datatypes.app ((:) a ([])) l3)
      (contracted_multi_insertL l1 l3 l1 a (Prelude.Left hin) (iHL2 hincl2)) ((:) a l3)) l2

