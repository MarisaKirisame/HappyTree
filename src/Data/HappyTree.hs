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

newtype SplitFunAux b d = SplitFunAux { runSplitFunAux :: [(NP I d, b)] }

class Get (SplitStrat env a) env => GetSplitStrat env a
instance Get (SplitStrat env a) env => GetSplitStrat env a

data SplitFun env a b = forall (c :: [[*]]) . (SListI2 c, All2 (GetSplitStrat env) c) =>
  SplitFun (a -> SOP I c) (NP (SplitFunAux b) c)

unitSplitFun :: [b] -> SplitFun env a b
unitSplitFun b = SplitFun (const $ SOP (Z Nil)) (SplitFunAux (map (\x -> (Nil, x)) b) :* Nil)

data SplitStrat env a = SplitStrat (forall b . [(a, b)] -> [SplitFun env a b])
runSplitStrat (SplitStrat f) x = f x

instance Monoid (SplitStrat env a) where
  mempty = SplitStrat (const [])
  SplitStrat l `mappend` SplitStrat r = SplitStrat (\b -> l b ++ r b)

splitFunP :: (SListI2 c, All2 (GetSplitStrat env) c) => Proxy c -> (a -> SOP I c) -> NP (SplitFunAux b) c -> SplitFun env a b
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

splitStatic :: (SListI2 c, All2 (GetSplitStrat env) c) => (a -> SOP I c) -> SplitStrat env a
splitStatic split = res where
  res = SplitStrat $ \x ->
    [SplitFun
      split
      (foldl join def $ map (\(a, b) -> hexpand (SplitFunAux []) $ hmap (\c -> SplitFunAux [(c, b)]) $ unSOP $ split a) x)]
  join :: SListI2 c => NP (SplitFunAux b) c -> NP (SplitFunAux b) c -> NP (SplitFunAux b) c
  join = hzipWith (\(SplitFunAux l) (SplitFunAux r) -> SplitFunAux $ l ++ r)
  def :: SListI2 c => NP (SplitFunAux b) c
  def = hpure $ SplitFunAux []

splitOrd :: (Ord a, GetSplitStrat env a) => SplitStrat env a
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

splitStructure :: (Generic a, SListI2 (Code a), All2 (GetSplitStrat env) (Code a)) => SplitStrat env a
splitStructure = splitStatic from

splitStructureP :: (Generic a, SListI2 (Code a), All2 (GetSplitStrat env) (Code a)) => Proxy a -> SplitStrat env a
splitStructureP _ = splitStructure

newtype BuildAuxAux a b = BuildAuxAux { runBuildAuxAux :: [(a, Fst b, NP I (Snd b))] }

newtype WithScore b x = WithScore { runWithScore :: (Score, (SplitOn b x)) }

fromSF :: SplitFun env a b -> Proxy (SOP.All (GetSplitStrat env))
fromSF _ = Proxy

type Getter env = ((->) env) :.: SplitStrat env

getGetter :: SOP.All (GetSplitStrat env) x => SOP.SList x -> NP (((->) env) :.: SplitStrat env) x
getGetter SOP.SNil = Nil
getGetter SOP.SCons = Comp get :* getGetter SOP.sList

data SelElemTypeAuxGetter env a = SelElemTypeAuxGetter (Getter env (Fst a)) (NP (Getter env) (Snd a))
selElemTypeAuxGetter :: NP (Getter env) a -> NP (Getter env) b -> NP (SelElemTypeAuxGetter env) (SelElemAux a b)
selElemTypeAuxGetter _ Nil = Nil
selElemTypeAuxGetter x (y :* z) = SelElemTypeAuxGetter y (npRevAppend x z) :* selElemTypeAuxGetter (y :* x) z

buildTree :: Ord b =>
  env -> NP (Getter env) (Snd a1) -> b -> SplitFun env (Fst a1) (b, NP I (Snd a1)) -> (Score, SplitOn b a1)
buildTree env getter def sfa@(SplitFun x y) =
  (if (<=1) $ length $ filter not $ hcollapse $ hmap (\(SplitFunAux z) -> K $ null z) y then
     Destructing else
     Deciding $ sum $ hcollapse $ hmap (\(SplitFunAux z) -> K $ (fromIntegral (length z)*) $ entropy $ map (fst . snd) z) y,
  SplitOn x (hcmap (fromSF sfa) (\(SplitFunAux z) -> if length z == 0 then SplitOnAux $ Leaf $ const def else
    let j = fst $ head z in
      SplitOnAux $ buildAux env
        (getGetter (npToSList j) `npAppend` getter) (map (\(c, (d, e)) -> (c `npAppend` e, d)) z) (mode $ map (fst . snd) z)) y))

buildAux :: Ord b => env -> NP (Getter env) a -> [(NP I a, b)] -> b -> DecisionTree a b
buildAux env getter [] def = Leaf $ const def
buildAux env getter x@((l, r):_) def =
  case dictSList $ npToSList $ npSelElem $ l of
    Dict -> if length (group (map snd x)) == 1 then
      Leaf $ const $ r else
      let a = map (\(l, r) -> hmap (\(SelElemTypeAux a b) -> BuildAuxAux [(r, a, b)]) $ npSelElem l) x
          b = foldl (hzipWith (\(BuildAuxAux l) (BuildAuxAux r) -> BuildAuxAux (l ++ r))) (hpure (BuildAuxAux [])) a
      in
        fromMaybe (Leaf $ const def) $ fmap (Split . hmap (\(WithScore (_, t)) -> t)) $ nMinOn (\(WithScore (s, _)) -> s) $
          hzipWith
            (\(SelElemTypeAuxGetter c d) (BuildAuxAux e) ->
              WithScore $ minimumByDef (buildTree env d def $ unitSplitFun $ map (\(f, g, h) -> (f, h)) e) (comparing fst) $
                map (buildTree env d def) $
                  runSplitStrat (unComp c env) $
                    map (\(f, g, h) -> (g, (f, h))) e)
            (selElemTypeAuxGetter Nil getter)
            b

build :: (SOP.All (GetSplitStrat env) a, Ord b) => env -> [(NP I a, b)] -> b -> DecisionTree a b
build env [] def = Leaf $ const def
build env x@((np, _):_) _ = buildAux env (getGetter $ npToSList np) (sortBy (comparing snd) x) (mode $ map snd x)

{-buildTree :: (Ord b, SOP.All (GetSplitStrat env) (Snd a1), SListI (Snd a1)) =>
  env -> b -> SplitFun env (Fst a1) (b, NP I (Snd a1)) -> (Score, SplitOn b a1)
buildTree env def sf@(SplitFun x y) =
  (if (<=1) $ length $ filter not $ hcollapse $ hmap (\(SplitFunAux z) -> K $ null z) y then
     Destructing else
     Deciding $ sum $ hcollapse $ hmap (\(SplitFunAux z) -> K $ (fromIntegral (length z)*) $ entropy $ map (fst . snd) z) y,
  SplitOn x $
    hmap (\(SplitFunAux z) ->
      case z of
        [] -> SplitOnAux $ Leaf $ const def
        ((j, _):_) -> SplitOnAux $ build env (map (\(c, (d, e)) -> (c `npAppend` e, d)) z) (mode $ map (fst . snd) z))
    y)

build :: (SOP.All (GetSplitStrat env) a, Ord b) => env -> [(NP I a, b)] -> b -> DecisionTree a b
build env [] def = Leaf $ const def
build env x@((l, r):_) _ = let sorted = sortBy (comparing snd) x in
  case dictSList $ npToSList $ npSelElem l of
    Dict -> if length (group (map snd sorted)) == 1 then Leaf $ const r else
      let a = map (\(l, r) -> hmap (\(SelElemTypeAux a b) -> BuildAux [(r, a, b)]) $ npSelElem l) sorted
          b = foldl (hzipWith (\(BuildAux l) (BuildAux r) -> BuildAux (l ++ r))) (hpure $ BuildAux []) a
          def = mode $ map snd x
      in fromMaybe (Leaf $ const def) $ join $
         fmap (fmap (Split . hmap (\(WithScore (_, t)) -> t)) . nMinOn (\(WithScore (s, _)) -> s)) $ hsequence' $
         hmap
           (\(BuildAux x) ->
             Comp $ fmap WithScore $
             minimumByMay (comparing fst) $
             map (buildTree env def) $
             runSplitStrat (get env) $
             map (\(f, g, h) -> (g, (f, h))) x)
         b-}
