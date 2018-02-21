module Main where

import Data.Tuple
import Graph
import Succinct
import Utility


main = do
  let
    testCont = [("f",(Fun (BType Int) (Fun (BType Bool) (Fun (BType Int) (BType Int))))) -- Int -> Bool -> Int -> Int
               , ("name", BType Char) -- Char
               , ("g", Fun (BType String) (BType Bool)) -- String -> Bool
               , ("lst", BType (DT "List" (BType Int))) -- List Int
               , ("h", Fun (BType (DT "List" (BType Int))) (BType Bool)) -- List Int -> Bool
               , ("s", Fun (BType (DT "List" (BType (TVar "a")))) (BType Bool)) -- List a -> Bool
               , ("t", Fun (BType (DT "List" (BType (TVar "a")))) (BType (TVar "a"))) -- List a -> a
               , ("r", Fun (BType (DT "List" (BType (TVar "a")))) (BType (DT "List" (BType (TVar "b"))))) -- List a -> List b
               ]
    -- renamedTyLst = let (_, tys) = foldl (\(n, acc) ty -> (n+1, ((renameVars ty n):acc))) (0,[]) testTyLst in tys
    baseTyLst    = removeDups (getBaseTypes (snd (unzip testCont))) []
    appliedTyLst = foldl (\acc t -> acc ++ (applyVars t baseTyLst)) [] (testCont)
    testTypes = snd (unzip appliedTyLst)
    testNames = fst (unzip appliedTyLst)
    succinctTyLst = zip testNames (map toSuccinctType testTypes)
    compoundTys = foldl (\acc x -> acc ++ (addCompoundTypes x)) [] succinctTyLst
    allTyLst = appliedTyLst ++ (map (\x -> ("", x)) (snd (unzip compoundTys)))
    allSuccTyLst = succinctTyLst ++ (map (\x -> ("", x)) (fst (unzip compoundTys)))
    typeIndices = toTypeIdx (removeDups (foldl (\acc t -> (getTypes t) ++ acc) [] (snd (unzip allSuccTyLst))) [])
    edges = foldl (\acc x -> (generateEdges x typeIndices)++acc) [] allSuccTyLst
    gr = transposeG (buildG (0,(length typeIndices)-1) edges)
    --e = edges gr
    lgr = LabGraph gr (\x->getTypeName typeIndices x)
  putStrLn $ showGraphViz lgr typeIndices
  -- putStrLn $ foldl (\acc (v, n, u) -> acc ++ (show v) ++ "->" ++ n ++ "->" ++ (show u) ++ "\n") "" e
  -- putStrLn $ foldl (\acc t -> acc ++ (typeToStr (fst t)) ++ ":" ++ (show (snd t)) ++ "\n") "" typeIndices
  -- putStrLn $ foldl (\acc t -> acc ++ (fst t) ++ " " ++ (typeToStr (snd t)) ++ "\n") "" appliedTyLst
