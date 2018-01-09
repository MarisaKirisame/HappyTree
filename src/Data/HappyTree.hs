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

module Data.HappyTree where

import Data.Singletons.Prelude
import Data.Singletons.TH
import qualified Generics.SOP as SOP
import Generics.SOP (NP(..), K(..), I(..), POP(..), SOP(..), NS(..), SListI, SListI2, All2, unSOP, unPOP, hzipWith, hpure, Generic, Code, hexpand, hcollapse, hmap, to, from, hcmap)
import Data.Constraint
import Data.List
import Data.Ord
import Data.Maybe
import Safe

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

data SelElemTypeAux a = SelElemTypeAux (Fst a) (NP I (Snd a))
type SelElemAuxType a b = NP SelElemTypeAux (SelElemAux a b)
type SelElemType a = SelElemAuxType '[] a

npRevAppend :: NP f a -> NP f b -> NP f (RevAppend a b)
npRevAppend Nil x = x
npRevAppend (x :* y) z = npRevAppend y (x :* z)

npSelElemAux :: NP I a -> NP I b -> SelElemAuxType a b
npSelElemAux _ Nil = Nil
npSelElemAux x (I y :* z) = SelElemTypeAux y (npRevAppend x z) :* npSelElemAux (I y :* x) z
npSelElem :: NP I a -> SelElemAuxType '[] a
npSelElem = npSelElemAux Nil

dictSList :: SOP.SList a -> Dict (SListI a)
dictSList SOP.SNil = Dict
dictSList SOP.SCons = Dict

sListCons :: Proxy a -> SOP.SList b -> SOP.SList (a:b)
sListCons _ x = dictSList x `withDict` SOP.SCons

npAppend :: NP f a -> NP f b -> NP f (a :++ b)
npAppend Nil x = x
npAppend (x :* y) z = x :* npAppend y z

npToSList :: NP f a -> SOP.SList a
npToSList Nil = SOP.SNil
npToSList (_ :* x) = sListCons Proxy (npToSList x)

newtype SplitOnAux a b c = SplitOnAux { runSplitOnAux :: DecisionTree (c :++ a) b }

data SplitOn (b :: *) (x :: (*, [*])) =
  forall (c :: [[*]]) . SListI c => SplitOn (Fst x -> SOP I c) (NP (SplitOnAux (Snd x) b) c)

data DecisionTree (a :: [*]) (b :: *) = Leaf (NP I a -> b) | Split (NS (SplitOn b) (SelElem a))

eval :: DecisionTree a b -> NP I a -> b
eval (Leaf f) x = f x
eval (Split f) x = dictSList (npToSList sex) `withDict` hcollapse (hzipWith onTree sex f)
  where
    sex = npSelElem x
    onTree :: SelElemTypeAux c -> SplitOn b c -> K b _
    onTree (SelElemTypeAux a b) (SplitOn c d) = 
      let SOP e = c a in K $
        hcollapse $ hzipWith (\(SplitOnAux f) g -> K $ eval f (npAppend g b)) d e

entropy :: Ord a => [a] -> Double
entropy x = sum $ map (\y -> let py = fromIntegral (length y) / lenx in -py * log py) $ group $ sort x
  where
    lenx = fromIntegral $ length x :: Double

data IndexAux (l :: k) (r :: k) = l ~ r => IndexAux
newtype Index (l :: [k]) (x :: k) = Index { runIndex :: NS (IndexAux x) l }

fromIndex :: SListI l => NP f l -> Index l x -> f x
fromIndex l (Index r) = hcollapse $ hzipWith (\x IndexAux -> K x) l r

class GetIndex l x where
  getIndex :: Proxy l -> Proxy x -> Index l x

instance {-# OVERLAPPABLE #-} GetIndex r x => GetIndex (l:r) x where
  getIndex _ _ = Index $ S $ runIndex $ getIndex Proxy Proxy

instance {-# OVERLAPPING #-} GetIndex (l:r) l where
  getIndex _ _ = Index $ Z IndexAux

newtype SplitFunAux b d = SplitFunAux { runSplitFunAux :: [(NP I d, b)] }
data SplitFun env a b = forall (c :: [[*]]) . (SListI2 c, All2 (GetIndex env) c) =>
  SplitFun (a -> SOP I c) (NP (SplitFunAux b) c)

unitSplitFun :: [b] -> SplitFun env a b
unitSplitFun b = SplitFun (const $ SOP (Z Nil)) (SplitFunAux (map (\x -> (Nil, x)) b) :* Nil)

splitFunP :: (SListI2 c, All2 (GetIndex env) c) => Proxy c -> (a -> SOP I c) -> NP (SplitFunAux b) c -> SplitFun env a b
splitFunP _ = SplitFun

data SplitStrat (env :: [*]) a = SplitStrat (forall b . [(a, b)] -> [SplitFun env a b])
runSplitFun (SplitStrat f) x = f x

type SplitStrats cur env = NP (SplitStrat env) cur

instance Monoid (SplitStrat env a) where
  mempty = SplitStrat (const [])
  SplitStrat l `mappend` SplitStrat r = SplitStrat (\b -> l b ++ r b)

splitStaticAux :: SplitStrat env a -> Proxy (GetIndex env)
splitStaticAux _ = Proxy

splitStatic :: (SListI2 c, All2 (GetIndex env) c) => (a -> SOP I c) -> SplitStrat env a
splitStatic split = res where
  res = SplitStrat $ \x ->
    [SplitFun
      split
      (foldl join def $ map (\(a, b) -> hexpand (SplitFunAux []) $ hmap (\c -> SplitFunAux [(c, b)]) $ unSOP $ split a) x)]
  join :: SListI2 c => NP (SplitFunAux b) c -> NP (SplitFunAux b) c -> NP (SplitFunAux b) c
  join = hzipWith (\(SplitFunAux l) (SplitFunAux r) -> SplitFunAux $ l ++ r)
  def :: SListI2 c => NP (SplitFunAux b) c
  def = hpure $ SplitFunAux []

splitOrd :: (Ord a, GetIndex env a) => SplitStrat env a
splitOrd = SplitStrat $
  map (\(x, y, z) -> splitFunP (Proxy :: Proxy ['[a], '[], '[a]])
    (\a -> SOP $ case a `compare` fst (head y) of
      LT -> Z $ I a :* Nil
      EQ -> S $ Z Nil
      GT -> S $ S $ Z $ I a :* Nil)
    (SplitFunAux (map func $ concat x) :* SplitFunAux (map (\(_, a) -> (Nil, a)) y) :* SplitFunAux (map func $ concat z) :* Nil)) .
  takeElem . groupBy (\(l, _) (r, _) -> l == r) . sortBy (comparing fst)
  where
    func (a, b) = (I a :* Nil, b)

splitStructure :: (Generic a, SListI2 (Code a), All2 (GetIndex env) (Code a)) => SplitStrat env a
splitStructure = splitStatic from

splitStructureP :: (Generic a, SListI2 (Code a), All2 (GetIndex env) (Code a)) => Proxy a -> SplitStrat env a
splitStructureP _ = splitStatic from

getIndex2 :: SOP.All (GetIndex l) r => SOP.SList r -> NP (Index l) r
getIndex2 SOP.SNil = Nil
getIndex2 SOP.SCons = getIndex Proxy Proxy :* getIndex2 SOP.sList

mode :: Ord a => [a] -> a
mode = head . maximumBy (comparing length) . group . sort

nMinOnAux :: Ord b => (forall x . f x -> b) -> NP f a -> Maybe (b, NS f a)
nMinOnAux fb Nil = Nothing
nMinOnAux fb (l :* r) =
  let lb = fb l in
    case nMinOnAux fb r of
      Nothing -> Just (lb, Z l)
      Just (rb, rs) ->
        case lb `compare` rb of
          GT -> Just (rb, S rs)
          _ -> Just (lb, Z l)

nMinOn :: Ord b => (forall x . f x -> b) -> NP f a -> Maybe (NS f a)
nMinOn f = fmap snd . nMinOnAux f

data SelElemTypeAuxIndex env a = SelElemTypeAuxIndex (Index env (Fst a)) (NP (Index env) (Snd a))
selElemTypeAuxIndex :: NP (Index env) a -> NP (Index env) b -> NP (SelElemTypeAuxIndex env) (SelElemAux a b)
selElemTypeAuxIndex _ Nil = Nil
selElemTypeAuxIndex x (y :* z) = SelElemTypeAuxIndex y (npRevAppend x z) :* selElemTypeAuxIndex (y :* x) z

fromSF :: SplitFun (env :: [*]) a b -> Proxy (SOP.All (GetIndex env))
fromSF _ = Proxy

newtype BuildAuxAux a b = BuildAuxAux { runBuildAuxAux :: [(a, Fst b, NP I (Snd b))] }

data Score = Destructing | Deciding Double deriving Eq
instance Ord Score where
  Destructing `compare` Destructing = EQ
  Destructing `compare` _ = LT
  _ `compare` Destructing = GT
  Deciding l `compare` Deciding r = l `compare` r

newtype WithScore b x = WithScore { runWithScore :: (Score, (SplitOn b x)) }

buildTree :: (SListI env, Ord b) =>
  SplitStrats env env -> NP (Index env) (Snd a1) -> b -> SplitFun env (Fst a1) (b, NP I (Snd a1)) -> (Score, SplitOn b a1)
buildTree sf i def sfa@(SplitFun x y) =
  (if (<=1) $ length $ filter not $ hcollapse $ hmap (\(SplitFunAux z) -> K $ null z) y then
     Destructing else
     Deciding $ sum $ hcollapse $ hmap (\(SplitFunAux z) -> K $ (fromIntegral (length z)*) $ entropy $ map (fst . snd) z) y,
  SplitOn x (hcmap (fromSF sfa) (\(SplitFunAux z) -> if length z == 0 then SplitOnAux $ Leaf $ const def else
    let j = fst $ head z in
      SplitOnAux $ buildAux
        (getIndex2 (npToSList j) `npAppend` i) sf (map (\(c, (d, e)) -> (c `npAppend` e, d)) z) (mode $ map (fst . snd) z)) y))

buildAux :: (SListI env, Ord b) => NP (Index env) a -> SplitStrats env env -> [(NP I a, b)] -> b -> DecisionTree a b
buildAux _ sf [] def = Leaf $ const def
buildAux i sf x@((l, r):_) def =
  case dictSList $ npToSList $ npSelElem $ l of
    Dict -> if length (group (map snd x)) == 1 then
      Leaf $ const $ r else
      let a = map (\(l, r) -> hmap (\(SelElemTypeAux a b) -> BuildAuxAux [(r, a, b)]) $ npSelElem l) x
          b = foldl (hzipWith (\(BuildAuxAux l) (BuildAuxAux r) -> BuildAuxAux (l ++ r))) (hpure (BuildAuxAux [])) a
      in
        fromMaybe (Leaf $ const def) $ fmap (Split . hmap (\(WithScore (_, t)) -> t)) $ nMinOn (\(WithScore (s, _)) -> s) $
          hzipWith
            (\(SelElemTypeAuxIndex c d) (BuildAuxAux e) ->
              WithScore $ minimumByDef (buildTree sf d def $ unitSplitFun $ map (\(f, g, h) -> (f, h)) e) (comparing fst) $
                map (buildTree sf d def) $
                  runSplitFun (fromIndex sf c) $
                    map (\(f, g, h) -> (g, (f, h))) e)
            (selElemTypeAuxIndex Nil i)
            b

build :: (SOP.All (GetIndex env) a, SListI env, Ord b) => SplitStrats env env -> [(NP I a, b)] -> b -> DecisionTree a b
build sf [] def = Leaf $ const def
build sf x@((np, _):_) _ = buildAux (getIndex2 $ npToSList $ np) sf (sortBy (comparing snd) x) (mode $ map snd x)
