import Data.HappyTree
import Generics.SOP
import Criterion.Main

comb :: [a] -> Int -> [[a]]
comb xs n = mapM (const xs) [1..n]

combUpTo :: [a] -> Int -> [[a]]
combUpTo xs n = [0..n] >>= comb xs

genSample :: Int -> [([Bool], Bool)]
genSample = map (\x -> (x, 2 * length (filter id x) >= length x)) . combUpTo [True, False]

sampleData :: [([Bool], Bool)]
sampleData = genSample 12

main = do
  let tree = build DefSplitStrat sampleData True
  print $ eval tree (repeat True)
