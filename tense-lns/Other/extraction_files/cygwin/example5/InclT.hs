module InclT where

import qualified Prelude
import qualified Datatypes
import qualified GenT

type Coq_inclT a = a -> (GenT.InT a) -> GenT.InT a

inclT_consL_InT :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> a1 -> (Coq_inclT a1) -> GenT.InT a1
inclT_consL_InT l1 _ a hincl =
  hincl a (GenT.InT_eq' a l1)

inclT_consL_inclT :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> a1 -> (Coq_inclT a1) -> Coq_inclT a1
inclT_consL_inclT l1 _ a hincl b hin =
  hincl b (GenT.InT_cons a l1 hin)

inclT_appL :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Coq_inclT a1) -> (Coq_inclT a1) -> Coq_inclT a1
inclT_appL l1 l2 _ hincl1 hincl2 a hin =
  let {hin0 = GenT.coq_InT_appE a l1 l2 hin} in case hin0 of {
                                                 Datatypes.Coq_inl hin1 -> hincl1 a hin1;
                                                 Datatypes.Coq_inr hin1 -> hincl2 a hin1}

inclT_refl :: (Datatypes.Coq_list a1) -> Coq_inclT a1
inclT_refl _ _ ha =
  ha

inclT_appL_refl :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> Coq_inclT a1
inclT_appL_refl l1 l2 a ha =
  GenT.coq_InT_appL a l1 l2 ha

inclT_appRL :: (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Datatypes.Coq_list a1) -> (Coq_inclT a1) -> Coq_inclT a1
inclT_appRL _ l2 l3 hincl a ha =
  GenT.coq_InT_appR a l2 l3 (hincl a ha)

