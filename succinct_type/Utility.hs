module Utility where

import Data.List
import Data.Tuple

findPair :: (Eq a) => [(a, b)] -> a -> Maybe Int
findPair [] key = Nothing
findPair lst key = find lst key 0
  where 
    find ((x,y):xs) key n = 
      if x == key 
        then Just n 
        else findPair xs key

removeDups :: (Eq a) => [a] -> [a] -> [a]
removeDups []     _     = []
removeDups (x:xs) sofar = case elemIndex x sofar of
    Just i  -> removeDups xs sofar
    Nothing -> x:(removeDups xs (x:sofar))

lengthOf :: Int -> [[a]] -> [[a]]
lengthOf 0 _      = []
lengthOf _ []     = []
lengthOf n (x:xs)
    | length x == n = x:(lengthOf n xs)
    | otherwise     = lengthOf n xs

fromOne :: Int -> [Int]
fromOne 0 = []
fromOne n = (fromOne (n-1))++[n]

fromZero :: Int -> [Int]
fromZero 0 = [0]
fromZero n = 0:(fromOne n)

divide :: Int -> [a] -> [[[a]]]
divide 1 x  = [[x]]
divide n x  = foldl f [] (fromZero (length x))
  where
    f acc elm = let (p1, p2) = splitAt elm x in (map (\x->p1:x) (divide (n-1) p2))++acc

-- divideDup :: (Eq a) => Int -> [a] -> [[[a]]]
-- divideDup 1 x = foldl (\acc x->acc++[[x]]) [] (subsequences x)
-- divideDup n x = [i:j | i <- (subsequences x),
--                       j <- (divideDup (n-1) x)]

divideDup :: Int -> [a] -> [[[a]]]
divideDup 1 x = [[x]]
divideDup n x = [i:j | i <- drop 1 (subsequences x),
                       j <- (divideDup (n-1) x)]

divideOpt :: Int -> [a] -> [[[a]]]
divideOpt 1 x = [subsequences x]
divideOpt n x = [i:j | i <- subsequences x,
                       j <- (divideOpt (n-1) x)]