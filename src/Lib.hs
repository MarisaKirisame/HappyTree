{-# LANGUAGE 
  DataKinds,
  TypeFamilies,
  TemplateHaskell,
  PolyKinds,
  ExistentialQuantification,
  ScopedTypeVariables,
  UndecidableInstances,
  TypeOperators,
  UndecidableSuperClasses
#-}

module Lib where

import Data.Singletons.Prelude
import Data.Void
import Data.Singletons.TH
import qualified Generics.SOP as SOP

someFunc :: IO ()
someFunc = putStrLn "someFunc"

$(singletons [d|
  takeElem :: [a] -> [(a, [a])]
  takeElem [] = []
  takeElem (x:xs) = (x, xs) : map (\(l, r) -> (l, x:r)) (takeElem xs)
 |])

class SOP.Generic a => SplitGeneric a where
  type SplitCode a :: [[*]]
  type SplitCode a = SOP.Code a

type SplitRep a = SOP.SOP SOP.I (SplitCode a)

type family SplitStructureOn (a :: (*, [*])) :: *
type instance SplitStructureOn '(l, r) = (SplitRep l, SOP.NP SOP.I r)

$(genDefunSymbols [''SplitStructureOn])

data DecisionTree (a :: [*]) (b :: *) =
  Leaf (SOP.NP SOP.I a -> b) |
  SplitOnStructure (SOP.NS SOP.I (Map SplitStructureOnSym0 (TakeElem a)))
