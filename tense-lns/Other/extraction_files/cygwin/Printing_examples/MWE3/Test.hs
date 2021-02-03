module Test where

myShow :: (Show a, Show b) => a -> b -> String
myShow a b = "Here is my thing: " ++ show a


data MyType a = One a | Two a a
  deriving Show

data MyOtherType = NoShow Int 


type Coord a = (a, a)
