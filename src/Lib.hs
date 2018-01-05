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
import Data.Constraint

someFunc :: IO ()
someFunc = putStrLn "someFunc"

$(singletons [d|
  takeElem :: [a] -> [(a, [a])]
  takeElem [] = []
  takeElem (x:xs) = (x, xs) : map (\(l, r) -> (l, x:r)) (takeElem xs)
 |])

class SOP.Generic a => SplitStructure a where
  type SplitCode a :: [[*]]
  type SplitCode a = SOP.Code a

class Ord a => SplitOrd a

type family SplitStructureOnAux (dt :: [*] -> * -> *) (b :: *) (r :: [*]) (a :: [*]) :: *
type instance SplitStructureOnAux dt b r a = dt (r :++ a) b

$(genDefunSymbols [''SplitStructureOnAux])

type family SplitStructureOn (dt :: [*] -> * -> *) (b :: *) (a :: (*, [*])) :: *
type instance SplitStructureOn dt b '(l, r) = SOP.NP SOP.I (Map (SplitStructureOnAuxSym3 dt b r) (SplitCode l))

type family SplitOrderOn (dt :: [*] -> * -> *) (b :: *) (a :: (*, [*])) :: *
type instance SplitOrderOn dt b '(l, r) = (Dict (SplitOrd l), l, dt (l:r) b, dt r b, dt (l:r) b)

$(genDefunSymbols [''SplitStructureOn, ''SplitOrderOn])

data DecisionTree (a :: [*]) (b :: *) =
  Leaf (SOP.NP SOP.I a -> b) |
  SplitOnStructure (SOP.NS SOP.I (Map (SplitStructureOnSym2 DecisionTree b) (TakeElem a))) |
  SplitOnOrd (SOP.NS SOP.I (Map (SplitOrderOnSym2 DecisionTree b) (TakeElem a)))
