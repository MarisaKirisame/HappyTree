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
  GADTs,
  PartialTypeSignatures
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

class (SplitCode a ~ SOP.Code a, SOP.Generic a) => SplitStructure a where
  type SplitCode a :: [[*]]
  type SplitCode a = SOP.Code a
  splitStructureFrom :: a -> SOP.SOP SOP.I (SplitCode a)
  splitStructureFrom = SOP.from
  splitStructureTo :: SOP.SOP SOP.I (SplitCode a) -> a

class Ord a => SplitOrd a

type family SplitStructureOnAux (dt :: [*] -> * -> *) (b :: *) (r :: [*]) (a :: [*]) :: *
type instance SplitStructureOnAux dt b r a = dt (r :++ a) b
newtype SplitStructureOnAuxT dt b r a = SplitStructureOnAuxT { runSplitStructureOnAuxT :: dt (r :++ a) b }
$(genDefunSymbols [''SplitStructureOnAux])

type family SplitStructureOn (dt :: [*] -> * -> *) (b :: *) (a :: (*, [*])) :: *
type instance SplitStructureOn dt b '(l, r) = (Dict (SplitStructure l), SOP.NP SOP.I (Map (SplitStructureOnAuxSym3 dt b r) (SplitCode l)))
newtype SplitStructureOnT dt b a =
  SplitStructureOnT { runSplitStructureOnT :: (Dict (SplitStructure (Fst a)), SOP.NP (SplitStructureOnAuxT dt b (Snd a)) (SplitCode (Fst a))) }

type family SplitOrderOn (dt :: [*] -> * -> *) (b :: *) (a :: (*, [*])) :: *
type instance SplitOrderOn dt b '(l, r) = (Dict (SplitOrd l), l, dt (l:r) b, dt r b, dt (l:r) b)
newtype SplitOrderOnT dt b a = SplitOrderOnT { runSplitOrderOnT :: SplitOrderOn dt b a }

data DecisionTree (a :: [*]) (b :: *) =
  Leaf (SOP.NP SOP.I a -> b) |
  SplitOnStructure (SOP.NS (SplitStructureOnT DecisionTree b) (TakeElem a)) |
  SplitOnOrd (SOP.NS (SplitOrderOnT DecisionTree b) (TakeElem a))

type family TakeElemTypeAux (a :: (*, [*])) :: *
type instance TakeElemTypeAux '(l, r) = (l, SOP.NP SOP.I r)
newtype TakeElemTypeAuxT a = TakeElemTypeAuxT { runTakeElemTypeAuxT :: (Fst a, SOP.NP SOP.I (Snd a)) }

type family TakeElemAuxType (a :: [*]) (b :: [*]) :: *
type instance TakeElemAuxType a b = SOP.NP TakeElemTypeAuxT (TakeElemAux a b)

type family TakeElemType (a :: [*]) :: *
type instance TakeElemType a = TakeElemAuxType '[] a

revAppendDT :: SOP.NP f a -> SOP.NP f b -> SOP.NP f (RevAppend a b)
revAppendDT SOP.Nil x = x
revAppendDT (x SOP.:* y) z = revAppendDT y (x SOP.:* z)

takeElemAuxDT :: SOP.NP SOP.I a -> SOP.NP SOP.I b -> TakeElemAuxType a b
takeElemAuxDT _ SOP.Nil = SOP.Nil
takeElemAuxDT x (SOP.I y SOP.:* z) = TakeElemTypeAuxT (y, revAppendDT x z) SOP.:* takeElemAuxDT (SOP.I y SOP.:* x) z

dictSList :: SOP.SList a -> Dict (SOP.SListI a)
dictSList SOP.SNil = Dict
dictSList SOP.SCons = Dict

sListCons :: Proxy a -> SOP.SList b -> SOP.SList (a:b)
sListCons _ x = dictSList x `withDict` SOP.SCons

unSListCons :: forall (a :: [k]) . SOP.SList (_:a) -> SOP.SList a
unSListCons SOP.SCons = SOP.sList

takeElemAuxDTSingAux :: SOP.SList (a:as) -> Proxy a
takeElemAuxDTSingAux _ = Proxy

takeElemAuxDTSing :: SOP.SList a -> SOP.SList b -> SOP.SList (TakeElemAux a b)
takeElemAuxDTSing _ SOP.SNil = SOP.SNil
takeElemAuxDTSing x y@SOP.SCons =
  dictSList (takeElemAuxDTSing (sListCons (takeElemAuxDTSingAux y) x) (unSListCons y)) `withDict` SOP.SCons

takeElemDT :: SOP.NP SOP.I a -> TakeElemType a
takeElemDT = takeElemAuxDT SOP.Nil

sopAppend :: SOP.NP f a -> SOP.NP f b -> SOP.NP f (a :++ b)
sopAppend SOP.Nil x = x
sopAppend (x SOP.:* y) z = x SOP.:* sopAppend y z

npToSList :: SOP.NP f a -> SOP.SList a
npToSList SOP.Nil = SOP.SNil
npToSList (_ SOP.:* x) = sListCons Proxy (npToSList x)

eval :: DecisionTree a b -> SOP.NP SOP.I a -> b
eval (Leaf f) x = f x
eval (SplitOnStructure f) x =
  dictSList (takeElemAuxDTSing SOP.SNil (npToSList x)) `withDict`
  (SOP.hcollapse $ SOP.hzipWith
    (\(TakeElemTypeAuxT (a, b)) (SplitStructureOnT (Dict, d)) ->
      let SOP.SOP e = splitStructureFrom a in
      SOP.K (SOP.hcollapse $ SOP.hzipWith (\(SplitStructureOnAuxT f) g -> SOP.K (eval f (sopAppend b g))) d e)) (takeElemDT x) f)
eval (SplitOnOrd f) x = undefined
