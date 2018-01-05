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
  secondCons :: a -> (a, [a]) -> (a, [a])
  secondCons x (l, r) = (l, x:r)
  takeElem :: [a] -> [(a, [a])]
  takeElem [] = []
  takeElem (x:xs) = (x, xs) : map (secondCons x) (takeElem xs)
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

type family TakeElemType (a :: [*]) :: *
type instance TakeElemType a = SOP.NP SOP.I (Map TakeElemTypeAuxSym0 (TakeElem a))

data TakeElemDTAuxSing (a :: [(*, [*])]) where
  STENil :: TakeElemDTAuxSing '[]
  STECons :: Proxy l -> Proxy r -> TakeElemDTAuxSing s -> TakeElemDTAuxSing ('(l, r):s)

takeElemDTAux :: x -> TakeElemDTAuxSing a -> SOP.NP SOP.I (Map TakeElemTypeAuxSym0 a) -> SOP.NP SOP.I (Map TakeElemTypeAuxSym0 (Map (SecondConsSym1 x) a))
takeElemDTAux _ STENil SOP.Nil = SOP.Nil
takeElemDTAux x (STECons _ _ stes) (SOP.I (ll, lr) SOP.:* r) = SOP.I (ll, SOP.I x SOP.:* lr) SOP.:* takeElemDTAux x stes r

evalStructure = undefined

takeElemDT :: SOP.NP SOP.I a -> TakeElemType a
takeElemDT SOP.Nil = SOP.Nil
takeElemDT (SOP.I (x :: x) SOP.:* (xs :: SOP.NP SOP.I xs)) = SOP.I (x, xs) SOP.:* takeElemDTAux x (undefined :: TakeElemDTAuxSing (TakeElem xs)) (takeElemDT xs)

unSCons :: SOP.SList (l:r) -> SOP.SList r
unSCons SOP.SCons = SOP.sList

sListToSTE :: SOP.SList a -> TakeElemDTAuxSing (TakeElem a)
sListToSTE SOP.SNil = STENil
sListToSTE sl@SOP.SCons = STECons Proxy Proxy (sListToSTE (unSCons sl))

takeElemDTSing :: SOP.SList a -> SOP.NP SOP.I a -> TakeElemType a
takeElemDTSing _ SOP.Nil = SOP.Nil
takeElemDTSing sl@SOP.SCons (SOP.I x SOP.:* (xs :: SOP.NP SOP.I xs)) =
  SOP.I (x, xs) SOP.:* takeElemDTAux x (sListToSTE (unSCons sl)) (takeElemDTSing SOP.sList xs)

eval :: DecisionTree a b -> SOP.NP SOP.I a -> b
eval (Leaf f) x = f x
eval (SplitOnStructure f) x = evalStructure f $ takeElemDT x
eval (SplitOnOrd f) x = undefined
