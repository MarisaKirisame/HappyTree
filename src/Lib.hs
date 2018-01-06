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
  PartialTypeSignatures,
  RankNTypes
#-}

module Lib where

import Data.Singletons.Prelude
import Data.Singletons.TH
import qualified Generics.SOP as SOP
import Data.Constraint
import Data.List

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

newtype TakeElemTypeAux a = TakeElemTypeAux { runTakeElemTypeAux :: (Fst a, SOP.NP SOP.I (Snd a)) }
type TakeElemAuxType a b = SOP.NP TakeElemTypeAux (TakeElemAux a b)
type TakeElemType a = TakeElemAuxType '[] a

npRevAppend :: SOP.NP f a -> SOP.NP f b -> SOP.NP f (RevAppend a b)
npRevAppend SOP.Nil x = x
npRevAppend (x SOP.:* y) z = npRevAppend y (x SOP.:* z)

npTakeElemAux :: SOP.NP SOP.I a -> SOP.NP SOP.I b -> TakeElemAuxType a b
npTakeElemAux _ SOP.Nil = SOP.Nil
npTakeElemAux x (SOP.I y SOP.:* z) = TakeElemTypeAux (y, npRevAppend x z) SOP.:* npTakeElemAux (SOP.I y SOP.:* x) z
npTakeElem :: SOP.NP SOP.I a -> TakeElemAuxType '[] a
npTakeElem = npTakeElemAux SOP.Nil

dictSList :: SOP.SList a -> Dict (SOP.SListI a)
dictSList SOP.SNil = Dict
dictSList SOP.SCons = Dict

sListCons :: Proxy a -> SOP.SList b -> SOP.SList (a:b)
sListCons _ x = dictSList x `withDict` SOP.SCons

npAppend :: SOP.NP f a -> SOP.NP f b -> SOP.NP f (a :++ b)
npAppend SOP.Nil x = x
npAppend (x SOP.:* y) z = x SOP.:* npAppend y z

npToSList :: SOP.NP f a -> SOP.SList a
npToSList SOP.Nil = SOP.SNil
npToSList (_ SOP.:* x) = sListCons Proxy (npToSList x)

newtype SplitOnAux a b c = SplitOnAux { runSplitOnAux :: DecisionTree (c :++ a) b }

data SplitOn (b :: *) (x :: (*, [*])) =
  forall (c :: [[*]]) . SOP.SListI c => SplitOn (Fst x -> SOP.SOP SOP.I c) (SOP.NP (SplitOnAux (Snd x) b) c)

data DecisionTree (a :: [*]) (b :: *) = Leaf (SOP.NP SOP.I a -> b) | Split (SOP.NS (SplitOn b) (TakeElem a))

eval :: DecisionTree a b -> SOP.NP SOP.I a -> b
eval (Leaf f) x = f x
eval (Split f) x = dictSList (npToSList tex) `withDict` SOP.hcollapse (SOP.hzipWith onTree tex f)
  where
    tex = npTakeElem x
    onTree :: TakeElemTypeAux c -> SplitOn b c -> SOP.K b _
    onTree (TakeElemTypeAux (a, b)) (SplitOn c d) = 
      let SOP.SOP e = c a in SOP.K $
        SOP.hcollapse $ SOP.hzipWith (\(SplitOnAux f) g -> SOP.K $ eval f (npAppend g b)) d e

entropy :: Ord a => [a] -> Double
entropy x = sum $ map (\y -> let py = fromIntegral (length y) / lenx in -py * log py) $ group $ sort x
  where
    lenx = fromIntegral $ length x :: Double

data IndexAux (l :: k) (r :: k) = l ~ r => IndexAux
newtype Index (l :: [k]) (x :: k) = Index { runIndex :: SOP.NS (IndexAux x) l }

data SplitFunAux b d = SplitFunAux (SOP.NP SOP.I d) b
data SplitFun a (env :: [*]) =
  forall (c :: [[[*]]]) . SplitFun (SOP.POP (SOP.NP (Index env)) c) (a -> SOP.NP (SOP.SOP SOP.I) c) (forall b . [(a, b)] -> SOP.POP (SplitFunAux b) c)
--data SplitFun a (env :: [*]) =
--  forall (c :: [[*]]) . SplitFun (SOP.POP (Index env) c) (a -> SOP.SOP SOP.I c) (forall b . [(a, b)] -> SOP.NP (SplitFunAux b) c)

build :: DecisionTree a b
build = undefined
