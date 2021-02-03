module Principal where

import qualified Prelude
import qualified Datatypes
import qualified List
import qualified Logic
import qualified Specif
import qualified DdT
import qualified Gen_tacs
import qualified LntT
import qualified Lntkt_exchT

__ :: any
__ = Prelude.error "Logical or arity value used"

data Coq_principal_ImpR v rules prems =
   Coq_princ_ImpR_I (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 (([]) (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir))) (LntT.PropF v) 
 (LntT.PropF v) LntT.Coq_dir (DdT.Coq_dersrec
                             (([])
                             ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir))
                             rules prems) rules

data Coq_principal_Id_pfc v rules prems =
   Coq_princ_Id_pfc_I (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 (([]) (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir))) v LntT.Coq_dir 
 (DdT.Coq_dersrec (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 rules prems) rules

data Coq_principal_WBox2Rs v rules prems =
   Coq_princ_WB2Rs_I (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 (([]) (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir))) (LntT.PropF v) 
 (DdT.Coq_dersrec (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 rules prems) rules

data Coq_principal_BBox2Rs v rules prems =
   Coq_princ_BB2Rs_I (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 (([]) (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir))) (LntT.PropF v) 
 (DdT.Coq_dersrec (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 rules prems) rules

data Coq_principal_WBox1Rs v rules prems =
   Coq_princ_WB1Rs_I (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 (([]) (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir))) (LntT.PropF v) 
 LntT.Coq_dir (DdT.Coq_dersrec
              (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) rules
              prems) rules

data Coq_principal_BBox1Rs v rules prems =
   Coq_princ_BB1Rs_I (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) 
 (([]) (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir))) (LntT.PropF v) 
 LntT.Coq_dir (DdT.Coq_dersrec
              (([]) ((,) ((,) (([]) (LntT.PropF v)) (([]) (LntT.PropF v))) LntT.Coq_dir)) rules
              prems) rules

data Coq_principal_WBR v rules prems =
   Coq_princ_WB1Rs (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) (Coq_principal_WBox1Rs
                                                                                     v rules 
                                                                                     prems)
 | Coq_princ_WB2Rs (Coq_principal_WBox2Rs v rules prems)

data Coq_principal_BBR v rules prems =
   Coq_princ_BB1Rs (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) (Coq_principal_BBox1Rs
                                                                                     v rules 
                                                                                     prems)
 | Coq_princ_BB2Rs (Coq_principal_BBox2Rs v rules prems)

data Coq_principal_not_box_R v =
   Coq_princ_nb_Id (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) (Coq_principal_Id_pfc v
                                                               (Lntkt_exchT.LNSKt_rules v) ())
 | Coq_princ_nb_ImpR (([]) (LntT.PropF v)) (([]) (LntT.PropF v)) (Coq_principal_ImpR v
                                                                 (Lntkt_exchT.LNSKt_rules v) 
                                                                 ())

principal_WBR_fwd :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                     (DdT.Coq_derrec
                     (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                     (Lntkt_exchT.LNSKt_rules a1) ()) -> (LntT.PropF a1) -> (([]) (LntT.PropF a1)) ->
                     (([]) (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                     ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1))) LntT.Coq_dir)) -> (([])
                     (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (Coq_principal_WBR a1
                     (Lntkt_exchT.LNSKt_rules a1) ()) -> Coq_principal_WBox2Rs a1
                     (Lntkt_exchT.LNSKt_rules a1) ()
principal_WBR_fwd g d a _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_ _UU03a0_ hprinc =
  case hprinc of {
   Coq_princ_WB1Rs _UU03a3_0 _UU03a0_1 _UU03a0_2 x ->
    case x of {
     Coq_princ_WB1Rs_I g' h0 b d0 d2 rl ->
      Logic.eq_rect_r (Datatypes.app h ((:) ((,) ((,) _UU03a3_ _UU03a0_) LntT.Coq_fwd) ([])))
        (\d1 hprinc0 x0 rl0 _ _ ->
        Logic.eq_rect_r (LntT.WBox b) (\hprinc1 x1 _ ->
          Logic.eq_rect_r
            (List.map (LntT.nslclext g') ((:) ((:) ((,) ((,) _UU03a3_0
              (Datatypes.app _UU03a0_1 (Datatypes.app ((:) b ([])) _UU03a0_2))) d0) ((:) ((,) ((,)
              _UU0393_ (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.WBox b) ([])) _UU0394_2)))
              LntT.Coq_bac) ([]))) ((:) ((:) ((,) ((,) _UU03a3_0 (Datatypes.app _UU03a0_1 _UU03a0_2))
              d0) ((:) ((,) ((,) _UU0393_
              (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.WBox b) ([])) _UU0394_2)))
              LntT.Coq_bac) ((:) ((,) ((,) ([]) ((:) b ([]))) LntT.Coq_fwd) ([])))) ([]))))
            (\d3 rl1 _ ->
            Logic.eq_rect_r (DdT.Coq_derI
              (List.map (LntT.nslclext g') ((:) ((:) ((,) ((,) _UU03a3_0
                (Datatypes.app _UU03a0_1 (Datatypes.app ((:) b ([])) _UU03a0_2))) d0) ((:) ((,) ((,)
                _UU0393_
                (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.WBox b) ([])) _UU0394_2)))
                LntT.Coq_bac) ([]))) ((:) ((:) ((,) ((,) _UU03a3_0
                (Datatypes.app _UU03a0_1 _UU03a0_2)) d0) ((:) ((,) ((,) _UU0393_
                (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.WBox b) ([])) _UU0394_2)))
                LntT.Coq_bac) ((:) ((,) ((,) ([]) ((:) b ([]))) LntT.Coq_fwd) ([])))) ([]))))
              (Datatypes.app h ((:) ((,) ((,) _UU03a3_ _UU03a0_) LntT.Coq_fwd) ([]))) rl1 d3)
              (\_ _ ->
              let {_evar_0_ = \_ -> Logic.coq_False_rect} in
              Logic.eq_rect_r
                (Datatypes.app
                  (Datatypes.app g' ((:) ((,) ((,) _UU03a3_0 (Datatypes.app _UU03a0_1 _UU03a0_2)) d0)
                    ([]))) ((:) ((,) ((,) _UU0393_
                  (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.WBox b) ([])) _UU0394_2)))
                  LntT.Coq_bac) ([]))) _evar_0_
                (Datatypes.app g'
                  (Datatypes.app ((:) ((,) ((,) _UU03a3_0 (Datatypes.app _UU03a0_1 _UU03a0_2)) d0)
                    ([])) ((:) ((,) ((,) _UU0393_
                    (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.WBox b) ([])) _UU0394_2)))
                    LntT.Coq_bac) ([])))) __) d1 hprinc1 x1) h0 d2 rl0 __) a hprinc0 x0 __) g d
        hprinc x rl __ __};
   Coq_princ_WB2Rs x -> x}

principal_WBR_bac :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                     (DdT.Coq_derrec
                     (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                     (Lntkt_exchT.LNSKt_rules a1) ()) -> (LntT.PropF a1) -> (([]) (LntT.PropF a1)) ->
                     (([]) (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                     ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1))) LntT.Coq_dir)) -> (([])
                     (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (Coq_principal_WBR a1
                     (Lntkt_exchT.LNSKt_rules a1) ()) -> Specif.Coq_sigT (([]) (LntT.PropF a1))
                     (Specif.Coq_sigT (([]) (LntT.PropF a1))
                     (Specif.Coq_sigT (([]) (LntT.PropF a1))
                     (Coq_principal_WBox1Rs a1 (Lntkt_exchT.LNSKt_rules a1) ())))
principal_WBR_bac g d a _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_ _UU03a0_ hprinc =
  case hprinc of {
   Coq_princ_WB1Rs _UU03a3_0 _UU03a0_1 _UU03a0_2 x -> Specif.Coq_existT _UU03a3_0 (Specif.Coq_existT
    _UU03a0_1 (Specif.Coq_existT _UU03a0_2 x));
   Coq_princ_WB2Rs x ->
    case x of {
     Coq_princ_WB2Rs_I g' h0 b d2 rl ->
      Logic.eq_rect_r (Datatypes.app h ((:) ((,) ((,) _UU03a3_ _UU03a0_) LntT.Coq_bac) ([])))
        (\d0 hprinc0 x0 rl0 _ _ ->
        Logic.eq_rect_r (LntT.WBox b) (\hprinc1 x1 _ ->
          Logic.eq_rect_r
            (List.map (LntT.nslclext g') ((:) ((:) ((,) ((,) _UU0393_
              (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.WBox b) ([])) _UU0394_2)))
              LntT.Coq_fwd) ((:) ((,) ((,) ([]) ((:) b ([]))) LntT.Coq_fwd) ([]))) ([])))
            (\d3 rl1 _ ->
            Logic.eq_rect_r (DdT.Coq_derI
              (List.map (LntT.nslclext g') ((:) ((:) ((,) ((,) _UU0393_
                (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.WBox b) ([])) _UU0394_2)))
                LntT.Coq_fwd) ((:) ((,) ((,) ([]) ((:) b ([]))) LntT.Coq_fwd) ([]))) ([])))
              (Datatypes.app h ((:) ((,) ((,) _UU03a3_ _UU03a0_) LntT.Coq_bac) ([]))) rl1 d3)
              (\_ _ ->
              let {_evar_0_ = \_ -> Logic.coq_False_rect} in
              Logic.eq_rect_r
                (Datatypes.app (Datatypes.app _UU0394_1 ((:) (LntT.WBox b) ([]))) _UU0394_2) _evar_0_
                (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.WBox b) ([])) _UU0394_2)) __) d0
              x1 hprinc1) h0 d2 rl0 __) a hprinc0 x0 __) g d hprinc x rl __ __}}

principal_BBR_fwd :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                     (DdT.Coq_derrec
                     (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                     (Lntkt_exchT.LNSKt_rules a1) ()) -> (LntT.PropF a1) -> (([]) (LntT.PropF a1)) ->
                     (([]) (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                     ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1))) LntT.Coq_dir)) -> (([])
                     (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (Coq_principal_BBR a1
                     (Lntkt_exchT.LNSKt_rules a1) ()) -> Specif.Coq_sigT (([]) (LntT.PropF a1))
                     (Specif.Coq_sigT (([]) (LntT.PropF a1))
                     (Specif.Coq_sigT (([]) (LntT.PropF a1))
                     (Coq_principal_BBox1Rs a1 (Lntkt_exchT.LNSKt_rules a1) ())))
principal_BBR_fwd g d a _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_ _UU03a0_ hprinc =
  case hprinc of {
   Coq_princ_BB1Rs _UU03a3_0 _UU03a0_1 _UU03a0_2 x -> Specif.Coq_existT _UU03a3_0 (Specif.Coq_existT
    _UU03a0_1 (Specif.Coq_existT _UU03a0_2 x));
   Coq_princ_BB2Rs x ->
    case x of {
     Coq_princ_BB2Rs_I g' h0 b d2 rl ->
      Logic.eq_rect_r (Datatypes.app h ((:) ((,) ((,) _UU03a3_ _UU03a0_) LntT.Coq_fwd) ([])))
        (\d0 hprinc0 x0 rl0 _ _ ->
        Logic.eq_rect_r (LntT.BBox b) (\hprinc1 x1 _ ->
          Logic.eq_rect_r
            (List.map (LntT.nslclext g') ((:) ((:) ((,) ((,) _UU0393_
              (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.BBox b) ([])) _UU0394_2)))
              LntT.Coq_bac) ((:) ((,) ((,) ([]) ((:) b ([]))) LntT.Coq_bac) ([]))) ([])))
            (\d3 rl1 _ ->
            Logic.eq_rect_r (DdT.Coq_derI
              (List.map (LntT.nslclext g') ((:) ((:) ((,) ((,) _UU0393_
                (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.BBox b) ([])) _UU0394_2)))
                LntT.Coq_bac) ((:) ((,) ((,) ([]) ((:) b ([]))) LntT.Coq_bac) ([]))) ([])))
              (Datatypes.app h ((:) ((,) ((,) _UU03a3_ _UU03a0_) LntT.Coq_fwd) ([]))) rl1 d3)
              (\_ _ ->
              let {_evar_0_ = \_ -> Logic.coq_False_rect} in
              Logic.eq_rect_r
                (Datatypes.app (Datatypes.app _UU0394_1 ((:) (LntT.BBox b) ([]))) _UU0394_2) _evar_0_
                (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.BBox b) ([])) _UU0394_2)) __) d0
              x1 hprinc1) h0 d2 rl0 __) a hprinc0 x0 __) g d hprinc x rl __ __}}

principal_BBR_bac :: (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir)) ->
                     (DdT.Coq_derrec
                     (([]) ((,) (Gen_tacs.Coq_rel (([]) (LntT.PropF a1))) LntT.Coq_dir))
                     (Lntkt_exchT.LNSKt_rules a1) ()) -> (LntT.PropF a1) -> (([]) (LntT.PropF a1)) ->
                     (([]) (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (([])
                     ((,) ((,) (([]) (LntT.PropF a1)) (([]) (LntT.PropF a1))) LntT.Coq_dir)) -> (([])
                     (LntT.PropF a1)) -> (([]) (LntT.PropF a1)) -> (Coq_principal_BBR a1
                     (Lntkt_exchT.LNSKt_rules a1) ()) -> Coq_principal_BBox2Rs a1
                     (Lntkt_exchT.LNSKt_rules a1) ()
principal_BBR_bac g d a _UU0393_ _UU0394_1 _UU0394_2 h _UU03a3_ _UU03a0_ hprinc =
  case hprinc of {
   Coq_princ_BB1Rs _UU03a3_0 _UU03a0_1 _UU03a0_2 x ->
    case x of {
     Coq_princ_BB1Rs_I g' h0 b d0 d2 rl ->
      Logic.eq_rect_r (Datatypes.app h ((:) ((,) ((,) _UU03a3_ _UU03a0_) LntT.Coq_bac) ([])))
        (\d1 hprinc0 x0 rl0 _ _ ->
        Logic.eq_rect_r (LntT.BBox b) (\hprinc1 x1 _ ->
          Logic.eq_rect_r
            (List.map (LntT.nslclext g') ((:) ((:) ((,) ((,) _UU03a3_0
              (Datatypes.app _UU03a0_1 (Datatypes.app ((:) b ([])) _UU03a0_2))) d0) ((:) ((,) ((,)
              _UU0393_ (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.BBox b) ([])) _UU0394_2)))
              LntT.Coq_fwd) ([]))) ((:) ((:) ((,) ((,) _UU03a3_0 (Datatypes.app _UU03a0_1 _UU03a0_2))
              d0) ((:) ((,) ((,) _UU0393_
              (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.BBox b) ([])) _UU0394_2)))
              LntT.Coq_fwd) ((:) ((,) ((,) ([]) ((:) b ([]))) LntT.Coq_bac) ([])))) ([]))))
            (\d3 rl1 _ ->
            Logic.eq_rect_r (DdT.Coq_derI
              (List.map (LntT.nslclext g') ((:) ((:) ((,) ((,) _UU03a3_0
                (Datatypes.app _UU03a0_1 (Datatypes.app ((:) b ([])) _UU03a0_2))) d0) ((:) ((,) ((,)
                _UU0393_
                (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.BBox b) ([])) _UU0394_2)))
                LntT.Coq_fwd) ([]))) ((:) ((:) ((,) ((,) _UU03a3_0
                (Datatypes.app _UU03a0_1 _UU03a0_2)) d0) ((:) ((,) ((,) _UU0393_
                (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.BBox b) ([])) _UU0394_2)))
                LntT.Coq_fwd) ((:) ((,) ((,) ([]) ((:) b ([]))) LntT.Coq_bac) ([])))) ([]))))
              (Datatypes.app h ((:) ((,) ((,) _UU03a3_ _UU03a0_) LntT.Coq_bac) ([]))) rl1 d3)
              (\_ _ ->
              let {_evar_0_ = \_ -> Logic.coq_False_rect} in
              Logic.eq_rect_r
                (Datatypes.app
                  (Datatypes.app g' ((:) ((,) ((,) _UU03a3_0 (Datatypes.app _UU03a0_1 _UU03a0_2)) d0)
                    ([]))) ((:) ((,) ((,) _UU0393_
                  (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.BBox b) ([])) _UU0394_2)))
                  LntT.Coq_fwd) ([]))) _evar_0_
                (Datatypes.app g'
                  (Datatypes.app ((:) ((,) ((,) _UU03a3_0 (Datatypes.app _UU03a0_1 _UU03a0_2)) d0)
                    ([])) ((:) ((,) ((,) _UU0393_
                    (Datatypes.app _UU0394_1 (Datatypes.app ((:) (LntT.BBox b) ([])) _UU0394_2)))
                    LntT.Coq_fwd) ([])))) __) d1 hprinc1 x1) h0 d2 rl0 __) a hprinc0 x0 __) g d
        hprinc x rl __ __};
   Coq_princ_BB2Rs x -> x}

