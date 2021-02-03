module InclT where

import qualified Prelude
import qualified GenT

type Coq_inclT a = a -> (GenT.InT a) -> GenT.InT a

inclT_consL_InT :: (([]) a1) -> (([]) a1) -> a1 -> (Coq_inclT a1) -> GenT.InT
                   a1
inclT_consL_InT l1 _ a hincl =
  hincl a (GenT.InT_eq' a l1)

inclT_consL_inclT :: (([]) a1) -> (([]) a1) -> a1 -> (Coq_inclT a1) ->
                     Coq_inclT a1
inclT_consL_inclT l1 _ a hincl b hin =
  hincl b (GenT.InT_cons a l1 hin)

inclT_appL :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_inclT a1) ->
              (Coq_inclT a1) -> Coq_inclT a1
inclT_appL l1 l2 _ hincl1 hincl2 a hin =
  let {hin0 = GenT.coq_InT_appE a l1 l2 hin} in
  case hin0 of {
   Prelude.Left hin1 -> hincl1 a hin1;
   Prelude.Right hin1 -> hincl2 a hin1}

inclT_refl :: (([]) a1) -> Coq_inclT a1
inclT_refl _ _ ha =
  ha

inclT_appL_refl :: (([]) a1) -> (([]) a1) -> Coq_inclT a1
inclT_appL_refl l1 l2 a ha =
  GenT.coq_InT_appL a l1 l2 ha

inclT_appRL :: (([]) a1) -> (([]) a1) -> (([]) a1) -> (Coq_inclT a1) ->
               Coq_inclT a1
inclT_appRL _ l2 l3 hincl a ha =
  GenT.coq_InT_appR a l2 l3 (hincl a ha)

