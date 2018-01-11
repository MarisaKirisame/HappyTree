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
import Generics.SOP (
  NP(..), K(..), I(..), POP(..), SOP(..), NS(..), (:.:)(..),
  SListI, SListI2, All2, unSOP, unPOP, hzipWith, hpure, Generic, Code, hexpand, hcollapse, hmap, to, from, hcmap, hsequence, hsequence', unComp)
import Data.Constraint
import Data.List
import Data.Ord
import Data.Maybe
import Safe
import Control.Get
import Control.Monad

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

evalAux :: DecisionTree a b -> NP I a -> b
evalAux (Leaf f) x = f x
evalAux (Split f) x = dictSList (npToSList sex) `withDict` hcollapse (hzipWith onTree sex f)
  where
    sex = npSelElem x
    onTree :: SelElemTypeAux c -> SplitOn b c -> K b _
    onTree (SelElemTypeAux a b) (SplitOn c d) = 
      let SOP e = c a in K $
        hcollapse $ hzipWith (\(SplitOnAux f) g -> K $ evalAux f (npAppend g b)) d e

eval :: DecisionTree '[a] b -> a -> b
eval dt x = evalAux dt (I x :* Nil)

entropy :: Ord a => [a] -> Double
entropy x = sum $ map (\y -> let py = fromIntegral (length y) / lenx in -py * log py) $ group $ sort x
  where
    lenx = fromIntegral $ length x :: Double

class Get (SplitStrat a) env => GetSplitStrat env a
instance Get (SplitStrat a) env => GetSplitStrat env a

data SplitFun a b = forall (c :: [[*]]) . SListI2 c =>
  SplitFun (a -> SOP I c) (NP ([] :.: (,) b :.: NP I) c) (POP SplitStrat c)

unitSplitFun :: [b] -> SplitFun a b
unitSplitFun b = SplitFun (const $ SOP (Z Nil)) (Comp (map (\b -> Comp $ (,) b Nil) b) :* Nil) (POP $ Nil :* Nil)

data SplitStrat a = SplitStrat (forall b . [(a, b)] -> [SplitFun a b])
runSplitStrat (SplitStrat f) x = f x

instance Monoid (SplitStrat a) where
  mempty = SplitStrat (const [])
  SplitStrat l `mappend` SplitStrat r = SplitStrat (\b -> l b ++ r b)

splitFunP :: SListI2 c => Proxy c -> (a -> SOP I c) -> NP ([] :.: (,) b :.: NP I) c -> POP SplitStrat c -> SplitFun a b
splitFunP _ = SplitFun

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

data Score = Destructing | Deciding Double deriving Eq
instance Ord Score where
  Destructing `compare` Destructing = EQ
  Destructing `compare` _ = LT
  _ `compare` Destructing = GT
  Deciding l `compare` Deciding r = l `compare` r

npSplitStratAux :: SOP.All (GetSplitStrat env) x => SOP.SList x -> env -> NP SplitStrat x
npSplitStratAux SOP.SNil env = Nil
npSplitStratAux SOP.SCons env = get env :* npSplitStratAux SOP.sList env

npSplitStrat :: SOP.All (GetSplitStrat env) x => env -> NP SplitStrat x
npSplitStrat = npSplitStratAux SOP.sList

popSplitStratAux :: All2 (GetSplitStrat env) c => SOP.SList c -> env -> NP (NP SplitStrat) c
popSplitStratAux SOP.SNil env = Nil
popSplitStratAux SOP.SCons env = npSplitStrat env :* popSplitStratAux SOP.sList env

popSplitStrat :: All2 (GetSplitStrat env) c => env -> POP SplitStrat c
popSplitStrat = POP . popSplitStratAux SOP.sList

splitStatic :: SListI2 c => POP SplitStrat c -> (a -> SOP I c) -> SplitStrat a
splitStatic strat split = res where
  res = SplitStrat $ \x ->
    [SplitFun
      split
      (foldl join def $ map (\(a, b) -> hexpand (Comp []) $ hmap (\c -> Comp [Comp $ (b, c)]) $ unSOP $ split a) x)
      strat]
  join :: SListI2 c => NP ([] :.: (,) b :.: NP I) c -> NP ([] :.: (,) b :.: NP I) c -> NP ([] :.: (,) b :.: NP I) c
  join = hzipWith (\(Comp l) (Comp r) -> Comp (l ++ r))
  def :: SListI2 c => NP ([] :.: (,) b :.: NP I) c
  def = hpure $ Comp []

splitStructure :: (Generic a, SListI2 (Code a)) => POP SplitStrat (Code a) -> SplitStrat a
splitStructure strat = splitStatic strat from

splitStructureP :: (Generic a, SListI2 (Code a)) => POP SplitStrat (Code a) -> Proxy a -> SplitStrat a
splitStructureP strat _ = splitStructure strat

splitOrd :: Ord a => POP SplitStrat ['[a], '[], '[a]] -> SplitStrat a
splitOrd strat = SplitStrat $
  map (\(x, y, z) -> SplitFun
    (\a -> SOP $ case a `compare` fst (head y) of
      LT -> Z $ I a :* Nil
      EQ -> S $ Z Nil
      GT -> S $ S $ Z $ I a :* Nil)
    (Comp (map func $ concat x) :* Comp (map (\(_, b) -> Comp $ (b, Nil)) y) :* Comp (map func $ concat z) :* Nil)
    strat) .
  takeElem . groupBy (\(l, _) (r, _) -> l == r) . sortBy (comparing fst)
  where
    func (a, b) = Comp $ (b, (I a :* Nil))

buildTree :: Ord b => NP SplitStrat (Snd a1) -> b -> SplitFun (Fst a1) (b, NP I (Snd a1)) -> (Score, SplitOn b a1)
buildTree strat def sfa@(SplitFun a b (POP c)) =
  (if (<=1) $ length $ filter not $ hcollapse $ hmap (\(Comp z) -> K $ null z) b then
     Destructing else
     Deciding $ sum $ hcollapse $ hmap (\(Comp z) -> K $ (fromIntegral (length z) *) $ entropy $ map (\(Comp ((x, _), _)) -> x) z) b,
  SplitOn a (hzipWith (\(Comp z) aStrat -> case sortBy (comparing $ fst . fst) $ map unComp z of
    [] -> SplitOnAux $ Leaf $ const def
    z -> SplitOnAux $ buildAux (aStrat `npAppend` strat) (map (\((c, d), e) -> (e `npAppend` d, c)) z) (mode $ map (fst . fst) z)) b c))

newtype BuildAuxAux a b = BuildAuxAux { runBuildAuxAux :: [(a, Fst b, NP I (Snd b))] }

data SelElemTypeAuxStrat env a = SelElemTypeAuxStrat (SplitStrat (Fst a)) (NP SplitStrat (Snd a))
selElemTypeAuxStrat :: NP SplitStrat a -> NP SplitStrat b -> NP (SelElemTypeAuxStrat env) (SelElemAux a b)
selElemTypeAuxStrat _ Nil = Nil
selElemTypeAuxStrat x (y :* z) = SelElemTypeAuxStrat y (npRevAppend x z) :* selElemTypeAuxStrat (y :* x) z

newtype WithScore b x = WithScore { runWithScore :: (Score, (SplitOn b x)) }

buildAux :: Ord b => NP SplitStrat a -> [(NP I a, b)] -> b -> DecisionTree a b
buildAux strat [] def = Leaf $ const def
buildAux strat x@((l, r):_) def =
  case dictSList $ npToSList $ npSelElem $ l of
    Dict -> if length (group (map snd x)) == 1 then
      Leaf $ const $ r else
      let a = map (\(l, r) -> hmap (\(SelElemTypeAux a b) -> BuildAuxAux [(r, a, b)]) $ npSelElem l) x
          b = foldl (hzipWith (\(BuildAuxAux l) (BuildAuxAux r) -> BuildAuxAux (l ++ r))) (hpure (BuildAuxAux [])) a
      in
        fromMaybe (Leaf $ const def) $ join $ fmap (fmap (Split . hmap (\(WithScore (_, t)) -> t)) . nMinOn (\(WithScore (s, _)) -> s)) $ hsequence' $
          hzipWith
            (\(SelElemTypeAuxStrat c d) (BuildAuxAux e) ->
              Comp $ fmap WithScore $ minimumByMay (comparing fst) $
                map (buildTree d def) $
                  runSplitStrat c $
                    map (\(f, g, h) -> (g, (f, h))) e)
            (selElemTypeAuxStrat Nil strat)
            b

splitStratP :: Proxy a -> Proxy (SplitStrat a)
splitStratP _ = Proxy
unSplitStratP :: Proxy (SplitStrat a) -> Proxy a
unSplitStratP _ = Proxy
unListP :: Proxy [a] -> Proxy a
unListP _ = Proxy

instance TryGet (SplitStrat a) self self ok => TryGet (SplitStrat [a]) DefSplitStrat self ok where
  tryGetVal self _ p = let (v, s) = tryGet self self (splitStratP $ unListP $ unSplitStratP p) in
    case s of
      STrue -> let res = splitStatic (POP (Nil :* (v :* res :* Nil) :* Nil)) from in res
      SFalse -> ()
  tryGetSing self _ p = tryGetSing self self (splitStratP $ unListP $ unSplitStratP p)

instance TryGet (SplitStrat Bool) DefSplitStrat self True where
  tryGetVal self _ _ = splitStructure (popSplitStrat self)
  tryGetSing _ _ _ = STrue

data DefSplitStrat = DefSplitStrat

build :: (GetSplitStrat env a, Ord b) => env -> [(a, b)] -> b -> DecisionTree '[a] b
build env [] def = Leaf $ const def
build env x@((np, _):_) _ = buildAux (get env :* Nil) (map (\(l, r) -> (I l :* Nil, r)) $ sortBy (comparing snd) x) (mode $ map snd x)
