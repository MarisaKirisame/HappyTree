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
  RankNTypes,
  FlexibleInstances,
  MultiParamTypeClasses,
  FlexibleContexts
#-}

module Lib where

import Data.Singletons.Prelude
import Data.Singletons.TH
import qualified Generics.SOP as SOP
import Data.Constraint
import Data.List
import Data.Ord

$(singletons [d|
  revAppend :: [a] -> [a] -> [a]
  revAppend [] x = x
  revAppend (x:xs) n = revAppend xs (x:n) 
  selElemAux :: [a] -> [a] -> [(a, [a])]
  selElemAux l [] = []
  selElemAux l (r:rs) = (r, revAppend l rs) : selElemAux (r:l) rs 
  selElem :: [a] -> [(a, [a])]
  selElem = selElemAux []
 |])

takeElemAux :: [a] -> [a] -> [([a], a, [a])]
takeElemAux l [] = []
takeElemAux l (r:rs) = (reverse l, r, rs) : takeElemAux (r:l) rs

takeElem :: [a] -> [([a], a, [a])]
takeElem = takeElemAux []

data SelElemTypeAux a = SelElemTypeAux (Fst a) (SOP.NP SOP.I (Snd a))
type SelElemAuxType a b = SOP.NP SelElemTypeAux (SelElemAux a b)
type SelElemType a = SelElemAuxType '[] a

npRevAppend :: SOP.NP f a -> SOP.NP f b -> SOP.NP f (RevAppend a b)
npRevAppend SOP.Nil x = x
npRevAppend (x SOP.:* y) z = npRevAppend y (x SOP.:* z)

npSelElemAux :: SOP.NP SOP.I a -> SOP.NP SOP.I b -> SelElemAuxType a b
npSelElemAux _ SOP.Nil = SOP.Nil
npSelElemAux x (SOP.I y SOP.:* z) = SelElemTypeAux y (npRevAppend x z) SOP.:* npSelElemAux (SOP.I y SOP.:* x) z
npSelElem :: SOP.NP SOP.I a -> SelElemAuxType '[] a
npSelElem = npSelElemAux SOP.Nil

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

data DecisionTree (a :: [*]) (b :: *) = Leaf (SOP.NP SOP.I a -> b) | Split (SOP.NS (SplitOn b) (SelElem a))

eval :: DecisionTree a b -> SOP.NP SOP.I a -> b
eval (Leaf f) x = f x
eval (Split f) x = dictSList (npToSList sex) `withDict` SOP.hcollapse (SOP.hzipWith onTree sex f)
  where
    sex = npSelElem x
    onTree :: SelElemTypeAux c -> SplitOn b c -> SOP.K b _
    onTree (SelElemTypeAux a b) (SplitOn c d) = 
      let SOP.SOP e = c a in SOP.K $
        SOP.hcollapse $ SOP.hzipWith (\(SplitOnAux f) g -> SOP.K $ eval f (npAppend g b)) d e

entropy :: Ord a => [a] -> Double
entropy x = sum $ map (\y -> let py = fromIntegral (length y) / lenx in -py * log py) $ group $ sort x
  where
    lenx = fromIntegral $ length x :: Double

data IndexAux (l :: k) (r :: k) = l ~ r => IndexAux
newtype Index (l :: [k]) (x :: k) = Index { runIndex :: SOP.NS (IndexAux x) l }

fromIndex :: SOP.SListI l => SOP.NP f l -> Index l x -> f x
fromIndex l (Index r) = SOP.hcollapse $ SOP.hzipWith (\x IndexAux -> SOP.K x) l r

class GetIndex l x where
  getIndex :: Proxy l -> Proxy x -> Index l x

instance {-# OVERLAPPABLE #-} GetIndex r x => GetIndex (l:r) x where
  getIndex _ _ = Index $ SOP.S $ runIndex $ getIndex Proxy Proxy

instance {-# OVERLAPPING #-} GetIndex (l:r) l where
  getIndex _ _ = Index $ SOP.Z IndexAux

newtype SplitFunAuxAux b d = SplitFunAuxAux { runSplitFunAuxAux :: [(SOP.NP SOP.I d, b)] }
data SplitFunAux env a b = forall (c :: [[*]]) . SOP.SListI2 c => SplitFunAux (SOP.POP (Index env) c) (a -> SOP.SOP SOP.I c) (SOP.NP (SplitFunAuxAux b) c)
splitFunAuxP :: SOP.SListI2 c => Proxy c -> SOP.POP (Index env) c -> (a -> SOP.SOP SOP.I c) -> SOP.NP (SplitFunAuxAux b) c -> SplitFunAux env a b
splitFunAuxP _ = SplitFunAux

data SplitFun (env :: [*]) a = SplitFun (forall b . [(a, b)] -> [SplitFunAux env a b])
type SplitFuns cur env = SOP.NP (SplitFun env) cur

instance Monoid (SplitFun env a) where
  mempty = SplitFun (const [])
  SplitFun l `mappend` SplitFun r = SplitFun (\b -> l b ++ r b)

splitStaticAux :: SplitFun env a -> Proxy (GetIndex env)
splitStaticAux _ = Proxy

splitStatic :: (SOP.SListI2 c, SOP.All2 (GetIndex env) c) => (a -> SOP.SOP SOP.I c) -> SplitFun env a
splitStatic split = res where
  res = SplitFun $ \x ->
    [SplitFunAux
      (SOP.hcpure (splitStaticAux res) (getIndex Proxy Proxy))
      split
      (foldl join def $ map (\(a, b) -> SOP.hexpand (SplitFunAuxAux []) $ SOP.hmap (\c -> SplitFunAuxAux [(c, b)]) $ SOP.unSOP $ split a) x)]
  join :: SOP.SListI2 c => SOP.NP (SplitFunAuxAux b) c -> SOP.NP (SplitFunAuxAux b) c -> SOP.NP (SplitFunAuxAux b) c
  join = SOP.hzipWith (\(SplitFunAuxAux l) (SplitFunAuxAux r) -> SplitFunAuxAux $ l ++ r)
  def :: SOP.SListI2 c => SOP.NP (SplitFunAuxAux b) c
  def = SOP.hpure $ SplitFunAuxAux []

splitOrd :: (Ord a, GetIndex env a) => SplitFun env a
splitOrd = SplitFun $
  map (\(x, y, z) -> splitFunAuxP (Proxy :: Proxy ['[a], '[], '[a]])
    (SOP.POP (i SOP.:* SOP.Nil SOP.:* i SOP.:* SOP.Nil))
    (\a -> SOP.SOP $ case a `compare` fst (head y) of
      LT -> SOP.Z $ SOP.I a SOP.:* SOP.Nil
      EQ -> SOP.S $ SOP.Z SOP.Nil
      GT -> SOP.S $ SOP.S $ SOP.Z $ SOP.I a SOP.:* SOP.Nil)
    (SplitFunAuxAux (map func $ concat x) SOP.:* SplitFunAuxAux (map (\(_, a) -> (SOP.Nil, a)) y) SOP.:* SplitFunAuxAux (map func $ concat z) SOP.:* SOP.Nil)) .
  takeElem . groupBy (\(l, _) (r, _) -> l == r) . sortBy (comparing fst)
  where
    func (a, b) = (SOP.I a SOP.:* SOP.Nil, b)
    i = getIndex Proxy Proxy SOP.:* SOP.Nil

splitStructure :: (SOP.Generic a, SOP.SListI2 (SOP.Code a), SOP.All2 (GetIndex env) (SOP.Code a)) => SplitFun env a
splitStructure = splitStatic SOP.from

getIndex2 :: SOP.All (GetIndex l) r => SOP.SList r -> SOP.NP (Index l) r
getIndex2 SOP.SNil = SOP.Nil
getIndex2 SOP.SCons = getIndex Proxy Proxy SOP.:* getIndex2 SOP.sList

newtype BuildAuxAux a b = BuildAuxAux { runBuildAuxAux :: [(a, Fst b, SOP.NP SOP.I (Snd b))] }
buildAuxAux :: SOP.All (GetIndex env) a => SplitFuns env env -> [(SOP.NP SOP.I a, b)] -> SOP.NP (Index env) a
buildAuxAux _ _ = getIndex2 SOP.sList

data WithScore b x = WithScore Double (SplitOn b x)

mode :: Ord a => [a] -> a
mode = head . maximumBy (comparing length) . group . sort

nSelect :: SOP.NP f a -> SOP.NS f a
nSelect = undefined

data SelElemTypeAuxIndex env a = SelElemTypeAuxIndex (Index env (Fst a)) (SOP.NP (Index env) (Snd a))
selElemTypeAuxIndex :: SOP.NP (Index env) a -> SOP.NP (Index env) b -> SOP.NP (SelElemTypeAuxIndex env) (SelElemAux a b)
selElemTypeAuxIndex _ SOP.Nil = SOP.Nil
selElemTypeAuxIndex x (y SOP.:* z) = SelElemTypeAuxIndex y (npRevAppend x z) SOP.:* selElemTypeAuxIndex (y SOP.:* x) z

buildAux :: (SOP.All (GetIndex env) a, Ord b) => SplitFuns env env -> [(SOP.NP SOP.I a, b)] -> b -> DecisionTree a b
buildAux sf [] def = Leaf $ const def
buildAux sf x@(xh:_) def = undefined
{-  case dictSList $ npToSList $ npSelElem $ fst $ xh of
    Dict -> if length (group (map snd x)) == 1 then
      Leaf $ const $ snd $ head x else
      let i = buildAuxAux sf x
          a = map (\(l, r) -> SOP.hmap (\(SelElemTypeAux a b) -> BuildAuxAux [(r, a, b)]) $ npSelElem l) x
          b = foldl (SOP.hzipWith (\(BuildAuxAux l) (BuildAuxAux r) -> BuildAuxAux (l ++ r))) (SOP.hpure (BuildAuxAux [])) a in
        Split $ SOP.hmap (\(WithScore _ s) -> s) $ nSelect $
          SOP.hzipWith (\(SelElemTypeAuxIndex (Index c) d) (BuildAuxAux e) -> WithScore undefined (_ $ map (\(f, g, h) -> (f, SOP.hzipWith (\x IndexAux -> SOP.K x) sf c, h)) e)) (selElemTypeAuxIndex SOP.Nil i) b-}

build :: (SOP.All (GetIndex env) a, Ord b) => SplitFuns env env -> [(SOP.NP SOP.I a, b)] -> b -> DecisionTree a b
build sf = buildAux sf . sortBy (comparing snd)
