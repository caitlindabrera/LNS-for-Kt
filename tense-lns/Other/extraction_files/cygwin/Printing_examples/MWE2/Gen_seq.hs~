module Gen_seq where

import qualified Prelude
import qualified Datatypes
import qualified Gen_tacs

seqext :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list
          a1) -> (Datatypes.Coq_list a1) -> (Gen_tacs.Coq_rel
          (Datatypes.Coq_list a1)) -> Datatypes.Coq_prod (Datatypes.Coq_list a1)
          (Datatypes.Coq_list a1)
seqext _UU0393_1 _UU0393_2 _UU0394_1 _UU0394_2 seq =
  case seq of {
   Datatypes.Coq_pair u v -> Datatypes.Coq_pair
    (Datatypes.app _UU0393_1 (Datatypes.app u _UU0393_2))
    (Datatypes.app _UU0394_1 (Datatypes.app v _UU0394_2))}

data Coq_seqrule w pr =
   Sctxt (Datatypes.Coq_list (Gen_tacs.Coq_rel (Datatypes.Coq_list w))) (Gen_tacs.Coq_rel
                                                                        (Datatypes.Coq_list
                                                                        w)) 
 (Datatypes.Coq_list w) (Datatypes.Coq_list w) (Datatypes.Coq_list w) (Datatypes.Coq_list
                                                                      w) pr

coq_Sctxt_nil :: (Gen_tacs.Coq_rel (Datatypes.Coq_list a1)) -> (Datatypes.Coq_list
                 a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) ->
                 (Datatypes.Coq_list a1) -> a2 -> Coq_seqrule a1 a2
coq_Sctxt_nil c _UU0393_1 _UU0393_2 _UU0394_1 _UU0394_2 h =
  Sctxt Datatypes.Coq_nil c _UU0393_1 _UU0393_2 _UU0394_1 _UU0394_2 h

