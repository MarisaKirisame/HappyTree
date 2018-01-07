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
import Data.Constraint
import Data.List
import Data.Ord
import Data.Maybe

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
data SplitFunAux env a b = forall (c :: [[*]]) . (SOP.SListI2 c, SOP.All2 (GetIndex env) c) =>
  SplitFunAux (a -> SOP.SOP SOP.I c) (SOP.NP (SplitFunAuxAux b) c)
splitFunAuxP :: (SOP.SListI2 c, SOP.All2 (GetIndex env) c) => Proxy c -> (a -> SOP.SOP SOP.I c) -> SOP.NP (SplitFunAuxAux b) c -> SplitFunAux env a b
splitFunAuxP _ = SplitFunAux

data SplitFun (env :: [*]) a = SplitFun (forall b . [(a, b)] -> [SplitFunAux env a b])
runSplitFun (SplitFun f) x = f x

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
      split
      (foldl join def $ map (\(a, b) -> SOP.hexpand (SplitFunAuxAux []) $ SOP.hmap (\c -> SplitFunAuxAux [(c, b)]) $ SOP.unSOP $ split a) x)]
  join :: SOP.SListI2 c => SOP.NP (SplitFunAuxAux b) c -> SOP.NP (SplitFunAuxAux b) c -> SOP.NP (SplitFunAuxAux b) c
  join = SOP.hzipWith (\(SplitFunAuxAux l) (SplitFunAuxAux r) -> SplitFunAuxAux $ l ++ r)
  def :: SOP.SListI2 c => SOP.NP (SplitFunAuxAux b) c
  def = SOP.hpure $ SplitFunAuxAux []

splitOrd :: (Ord a, GetIndex env a) => SplitFun env a
splitOrd = SplitFun $
  map (\(x, y, z) -> splitFunAuxP (Proxy :: Proxy ['[a], '[], '[a]])
    (\a -> SOP.SOP $ case a `compare` fst (head y) of
      LT -> SOP.Z $ SOP.I a SOP.:* SOP.Nil
      EQ -> SOP.S $ SOP.Z SOP.Nil
      GT -> SOP.S $ SOP.S $ SOP.Z $ SOP.I a SOP.:* SOP.Nil)
    (SplitFunAuxAux (map func $ concat x) SOP.:* SplitFunAuxAux (map (\(_, a) -> (SOP.Nil, a)) y) SOP.:* SplitFunAuxAux (map func $ concat z) SOP.:* SOP.Nil)) .
  takeElem . groupBy (\(l, _) (r, _) -> l == r) . sortBy (comparing fst)
  where
    func (a, b) = (SOP.I a SOP.:* SOP.Nil, b)

splitStructure :: (SOP.Generic a, SOP.SListI2 (SOP.Code a), SOP.All2 (GetIndex env) (SOP.Code a)) => SplitFun env a
splitStructure = splitStatic SOP.from

getIndex2 :: SOP.All (GetIndex l) r => SOP.SList r -> SOP.NP (Index l) r
getIndex2 SOP.SNil = SOP.Nil
getIndex2 SOP.SCons = getIndex Proxy Proxy SOP.:* getIndex2 SOP.sList

mode :: Ord a => [a] -> a
mode = head . maximumBy (comparing length) . group . sort

nMinOnAux :: Ord b => (forall x . f x -> b) -> SOP.NP f a -> Maybe (b, SOP.NS f a)
nMinOnAux fb SOP.Nil = Nothing
nMinOnAux fb (l SOP.:* r) =
  let lb = fb l in
    case nMinOnAux fb r of
      Nothing -> Just (lb, SOP.Z l)
      Just (rb, rs) ->
        case lb `compare` rb of
          GT -> Just (rb, SOP.S rs)
          _ -> Just (lb, SOP.Z l)

nMinOn :: Ord b => (forall x . f x -> b) -> SOP.NP f a -> Maybe (SOP.NS f a)
nMinOn f = fmap snd . nMinOnAux f

data SelElemTypeAuxIndex env a = SelElemTypeAuxIndex (Index env (Fst a)) (SOP.NP (Index env) (Snd a))
selElemTypeAuxIndex :: SOP.NP (Index env) a -> SOP.NP (Index env) b -> SOP.NP (SelElemTypeAuxIndex env) (SelElemAux a b)
selElemTypeAuxIndex _ SOP.Nil = SOP.Nil
selElemTypeAuxIndex x (y SOP.:* z) = SelElemTypeAuxIndex y (npRevAppend x z) SOP.:* selElemTypeAuxIndex (y SOP.:* x) z

fromSFA :: SplitFunAux (env :: [*]) a b -> Proxy (SOP.All (GetIndex env))
fromSFA _ = Proxy

newtype BuildAuxAux a b = BuildAuxAux { runBuildAuxAux :: [(a, Fst b, SOP.NP SOP.I (Snd b))] }

data Score = Destructing | Deciding Double deriving Eq
instance Ord Score where
  Destructing `compare` Destructing = EQ
  Destructing `compare` _ = LT
  _ `compare` Destructing = GT
  Deciding l `compare` Deciding r = l `compare` r

newtype WithScore b x = WithScore { runWithScore :: (Score, (SplitOn b x)) }

buildTree :: (SOP.SListI env, Ord b) =>
  SplitFuns env env -> SOP.NP (Index env) (Snd a1) -> b -> SplitFunAux env (Fst a1) (b, SOP.NP SOP.I (Snd a1)) -> (Score, SplitOn b a1)
buildTree sf i def sfa@(SplitFunAux x y) =
  (if (==1) $ length $ filter not $ SOP.hcollapse $ SOP.hmap (\(SplitFunAuxAux z) -> SOP.K $ null z) y then
     Destructing else
     Deciding $ sum $ SOP.hcollapse $ SOP.hmap (\(SplitFunAuxAux z) -> SOP.K $ (fromIntegral (length z)*) $ entropy $ map (fst . snd) z) y,
  SplitOn x (SOP.hcmap (fromSFA sfa) (\(SplitFunAuxAux z) -> if length z == 0 then SplitOnAux $ Leaf $ const def else
    let j = fst $ head z in
      SplitOnAux $ buildAux
        (getIndex2 (npToSList j) `npAppend` i) sf (map (\(c, (d, e)) -> (c `npAppend` e, d)) z) (mode $ map (fst . snd) z)) y))

buildAux :: (SOP.SListI env, Ord b) => SOP.NP (Index env) a -> SplitFuns env env -> [(SOP.NP SOP.I a, b)] -> b -> DecisionTree a b
buildAux _ sf [] def = Leaf $ const def
buildAux i sf x@(xh:_) def =
  case dictSList $ npToSList $ npSelElem $ fst $ xh of
    Dict -> if length (group (map snd x)) == 1 then
      Leaf $ const $ snd $ head x else
      let a = map (\(l, r) -> SOP.hmap (\(SelElemTypeAux a b) -> BuildAuxAux [(r, a, b)]) $ npSelElem l) x
          b = foldl (SOP.hzipWith (\(BuildAuxAux l) (BuildAuxAux r) -> BuildAuxAux (l ++ r))) (SOP.hpure (BuildAuxAux [])) a
      in
        fromMaybe (Leaf $ const def) $ fmap (Split . SOP.hmap (\(WithScore (_, t)) -> t)) $ nMinOn (\(WithScore (s, _)) -> s) $
          SOP.hzipWith
            (\(SelElemTypeAuxIndex c d) (BuildAuxAux e) ->
              WithScore $ minimumBy (comparing fst) $
                map (buildTree sf d def) $
                  runSplitFun (fromIndex sf c) $
                    map (\(f, g, h) -> (g, (f, h))) e)
            (selElemTypeAuxIndex SOP.Nil i)
            b

build :: (SOP.All (GetIndex env) a, SOP.SListI env, Ord b) => SplitFuns env env -> [(SOP.NP SOP.I a, b)] -> b -> DecisionTree a b
build sf [] def = Leaf $ const def
build sf x@((np, _):_) def = buildAux (getIndex2 $ npToSList $ np) sf (sortBy (comparing snd) x) def
