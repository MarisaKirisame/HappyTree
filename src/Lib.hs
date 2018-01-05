{-# LANGUAGE 
  DataKinds,
  TypeFamilies,
  TemplateHaskell,
  PolyKinds,
  ExistentialQuantification,
  ScopedTypeVariables,
  UndecidableInstances,
  TypeOperators,
  UndecidableSuperClasses,
  GADTs
#-}

module Lib where

import Data.Singletons.Prelude
import Data.Void
import Data.Singletons.TH
import qualified Generics.SOP as SOP
import Data.Constraint
import Data.Proxy

someFunc :: IO ()
someFunc = putStrLn "someFunc"

$(singletons [d|
  revAppend :: [a] -> [a] -> [a]
  revAppend [] x = x
  revAppend (x:xs) n = revAppend xs (x:n) 
  takeElemAux :: [a] -> [a] -> [(a, [a])]
  takeElemAux l [] = []
  takeElemAux l (r:rs) = (r, revAppend l rs) : takeElemAux (r:l) rs 
  takeElem :: [a] -> [(a, [a])]
  takeElem = takeElemAux []
 |])

class SOP.Generic a => SplitStructure a where
  type SplitCode a :: [[*]]
  type SplitCode a = SOP.Code a

class Ord a => SplitOrd a

type family SplitStructureOnAux (dt :: [*] -> * -> *) (b :: *) (r :: [*]) (a :: [*]) :: *
type instance SplitStructureOnAux dt b r a = dt (r :++ a) b

$(genDefunSymbols [''SplitStructureOnAux])

type family SplitStructureOn (dt :: [*] -> * -> *) (b :: *) (a :: (*, [*])) :: *
type instance SplitStructureOn dt b '(l, r) = (Dict (SOP.Generic l), SOP.NP SOP.I (Map (SplitStructureOnAuxSym3 dt b r) (SplitCode l)))

type family SplitOrderOn (dt :: [*] -> * -> *) (b :: *) (a :: (*, [*])) :: *
type instance SplitOrderOn dt b '(l, r) = (Dict (SplitOrd l), l, dt (l:r) b, dt r b, dt (l:r) b)

$(genDefunSymbols [''SplitStructureOn, ''SplitOrderOn])

data DecisionTree (a :: [*]) (b :: *) =
  Leaf (SOP.NP SOP.I a -> b) |
  SplitOnStructure (SOP.NS SOP.I (Map (SplitStructureOnSym2 DecisionTree b) (TakeElem a))) |
  SplitOnOrd (SOP.NS SOP.I (Map (SplitOrderOnSym2 DecisionTree b) (TakeElem a)))

type family TakeElemTypeAux (a :: (*, [*])) :: *
type instance TakeElemTypeAux '(l, r) = (l, SOP.NP SOP.I r)

$(genDefunSymbols [''TakeElemTypeAux])

type family TakeElemAuxType (a :: [*]) (b :: [*]) :: *
type instance TakeElemAuxType a b = SOP.NP SOP.I (Map TakeElemTypeAuxSym0 (TakeElemAux a b))

type family TakeElemType (a :: [*]) :: *
type instance TakeElemType a = TakeElemAuxType '[] a

revAppendDT :: SOP.NP SOP.I a -> SOP.NP SOP.I b -> SOP.NP SOP.I (RevAppend a b)
revAppendDT SOP.Nil x = x
revAppendDT (x SOP.:* y) z = revAppendDT y (x SOP.:* z)

takeElemAuxDT :: SOP.NP SOP.I a -> SOP.NP SOP.I b -> TakeElemAuxType a b
takeElemAuxDT _ SOP.Nil = SOP.Nil
takeElemAuxDT x (SOP.I y SOP.:* z) = SOP.I (y, revAppendDT x z) SOP.:* takeElemAuxDT (SOP.I y SOP.:* x) z

takeElemDT :: SOP.NP SOP.I a -> TakeElemType a
takeElemDT = takeElemAuxDT SOP.Nil

evalStructure = undefined

eval :: DecisionTree a b -> SOP.NP SOP.I a -> b
eval (Leaf f) x = f x
eval (SplitOnStructure f) x = _ f $ takeElemDT x
eval (SplitOnOrd f) x = undefined
