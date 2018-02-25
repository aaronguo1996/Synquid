module Main where

import Data.Tuple
import Graph
import Succinct
import Utility


main = do
  let
    sampleTest = [("f",(Fun (BType Int) (Fun (BType Bool) (Fun (BType Int) (BType Int))))) -- Int -> Bool -> Int -> Int
                 , ("name", BType Char) -- Char
                 , ("g", Fun (BType String) (BType Bool)) -- String -> Bool
                 , ("lst", BType (DT "List" (BType Int))) -- List Int
                 , ("h", Fun (BType (DT "List" (BType Int))) (BType Bool)) -- List Int -> Bool
                 , ("s", Fun (BType (DT "List" (BType (TVar "a")))) (BType Bool)) -- List a -> Bool
                 , ("t", Fun (BType (DT "List" (BType (TVar "a")))) (BType (TVar "a"))) -- List a -> a
                 , ("r", Fun (BType (DT "List" (BType (TVar "a")))) (BType (DT "List" (BType (TVar "b"))))) -- List a -> List b
                 ]
    addressBookMerge = [("Nil", BType (DT "List" (BType (TVar "a"))))
                       ,("Cons", (Fun (BType (TVar "a")) (Fun (BType (DT "List" (BType (TVar "a")))) (BType (DT "List" (BType (TVar "a")))))))
                       ,("append", (Fun (BType (DT "List" (BType (TVar "a")))) (Fun (BType (DT "List" (BType (TVar "a")))) (BType (DT "List" (BType (TVar "a")))))))
                       ,("Info", (Fun (BType Int) (Fun (BType Int) (Fun (BType Bool) (BType (DT "Info" (BType Nil)))))))
                       ,("Address", (Fun (BType (DT "Info" (BType Nil))) (Fun (BType Bool) (BType (DT "Address" (BType Nil))))))
                       ,("getPriv", (Fun (BType (DT "Address" (BType Nil))) (BType Bool)))
                       ,("AddressBook", (Fun (BType (DT "List" (BType (DT "Address" (BType Nil))))) (Fun (BType (DT "List" (BType (DT "Address" (BType Nil))))) (BType (DT "AddressBook" (BType Nil))))))
                       ,("AddressBook_match", (Fun (BType (DT "AddressBook" (BType Nil))) (BType (DT "List" (BType (DT "Address" (BType Nil))))) ))
                       ,("a", (BType (DT "AddressBook" (BType Nil))))
                       ,("b", (BType (DT "AddressBook" (BType Nil))))
                       ,("mergeAddressBooks", (Fun (BType (DT "AddressBook" (BType Nil))) (Fun (BType (DT "AddressBook" (BType Nil))) (BType (DT "AddressBook" (BType Nil))))))
                       ]
    listConcat = [("Nil", BType (DT "List" (BType (TVar "a"))))
                 ,("Cons", (Fun (BType (TVar "a")) (Fun (BType (DT "List" (BType (TVar "a")))) (BType (DT "List" (BType (TVar "a")))))))
                 ,("Nil2", BType (DT "ListOfLists" (BType (TVar "a"))))
                 ,("Cons2", (Fun (BType (DT "List" (BType (TVar "a")))) (Fun (BType (DT "ListOfLists" (BType (TVar "a")))) (BType (DT "ListOfLists" (BType (TVar "a")))))))
                 ,("append", (Fun (BType (DT "List" (BType (TVar "a")))) (Fun (BType (DT "List" (BType (TVar "a")))) (BType (DT "List" (BType (TVar "a")))))))
                 ,("xss", BType (DT "ListOfLists" (BType (TVar "a"))))
                 ,("concat", (Fun (BType (DT "ListOfLists" (BType (TVar "a")))) (BType (DT "List" (BType (TVar "a"))))))
                 ]
    replicateExmp = [("zero", BType Int)
                    ,("inc", Fun (BType Int) (BType Int))
                    ,("dec", Fun (BType Int) (BType Int))
                    ,("Nil", BType (DT "List" (BType (TVar "a"))))
                    ,("Cons", (Fun (BType (TVar "a")) (Fun (BType (DT "List" (BType (TVar "a")))) (BType (DT "List" (BType (TVar "a")))))))
                    ,("Cons_match", (Fun (BType (DT "List" (BType (TVar "a")))) (BType (TVar "a"))))
                    --,("n", BType (DT "Nat" (BType Nil)))
                    --,("", Fun (BType (DT "Nat" (BType Nil))) (BType Int))
                    ,("replicate", Fun (BType Int) (Fun (BType (TVar "a")) (BType (DT "List" (BType (TVar "a"))))))
                    ]
    testCont = replicateExmp
    -- renamedTyLst = let (_, tys) = foldl (\(n, acc) ty -> (n+1, ((renameVars ty n):acc))) (0,[]) testTyLst in tys
    baseTyLst    = removeDups (getBaseTypes (snd (unzip testCont))) []
    -- baseTyLst = snd (unzip testCont)
    appliedTyLst = removeDups ((foldl (\acc t -> acc ++ (applyVars t baseTyLst)) [] (testCont)) ++ (testCont)) []
    testTypes = snd (unzip appliedTyLst)
    testNames = fst (unzip appliedTyLst)
    succinctTyLst = zip testNames (map toSuccinctType testTypes)
    compoundTys = foldl (\acc x -> acc ++ (addCompoundTypes x)) [] succinctTyLst
    --allTyLst = appliedTyLst ++ (map (\x -> ("", x)) (snd (unzip compoundTys)))
    allSuccTyLst = succinctTyLst ++ (map (\x -> ("", x)) compoundTys)
    typeIndices = toTypeIdx (removeDups (foldl (\acc t -> (getTypes t) ++ acc) [] (snd (unzip allSuccTyLst))) [])
    edges = foldl (\acc x -> (generateEdges x typeIndices)++acc) [] allSuccTyLst
    gr = transposeG (buildG (0,(length typeIndices)-1) edges)
    --e = edges gr
    lgr = LabGraph gr (\x->getTypeName typeIndices x)
  putStrLn $ showGraphViz lgr typeIndices
  --putStrLn $ foldl (\acc t -> acc ++ (fst t) ++ ": " ++ (succinctToStr (snd t)) ++ "\n") "" allSuccTyLst
  --putStrLn $ foldl (\acc (v, n, u) -> acc ++ (show v) ++ "->" ++ n ++ "->" ++ (show u) ++ "\n") "" edges
  --putStrLn $ foldl (\acc t -> acc ++ (succinctToStr (fst t)) ++ ":" ++ (show (snd t)) ++ "\n") "" typeIndices
  --putStrLn $ foldl (\acc t -> acc ++ (fst t) ++ " " ++ (typeToStr (snd t)) ++ "\n") "" appliedTyLst
