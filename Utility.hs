module Utility where

import Data.List

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