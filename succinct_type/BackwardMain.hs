module Main where

import System.IO
import System.Environment
import Data.Tuple
import GraphBackward
import SuccinctBackward
import Utility


main = do
  let
    addressBookMerge = [("Nil",  TyAll "a" (TyDt "List_nil" [TyId "a"]))
                       ,("Cons", TyAll "a" (TyArr (TyId "a") (TyArr (TyDt "List" [TyId "a"]) (TyDt "List" [TyId "a"]))))
                       ,("ConsToList", TyAll "a" (TyArr (TyDt "List_cons" [TyId "a"]) (TyDt "List" [TyId "a"])))
                       ,("NilToList", TyAll "a" (TyArr (TyDt "List_nil" [TyId "a"]) (TyDt "List" [TyId "a"])))
                       ,("Cons_head", TyAll "a" (TyArr (TyDt "List_cons" [TyId "a"]) (TyId "a")))
                       ,("Cons_tail", TyAll "a" (TyArr (TyDt "List_cons" [TyId "a"]) (TyDt "List" [TyId "a"])))
                       ,("append", TyAll "a" (TyArr (TyDt "List" [TyId "a"]) (TyArr (TyDt "List" [TyId "a"]) (TyDt "List" [TyId "a"]))))
                       ,("Info", (TyArr TyInt (TyArr TyInt (TyArr TyBool (TyDt "Info" [])))))
                       ,("Address", (TyArr (TyDt "Info" []) (TyArr TyBool (TyDt "Address" []))))
                       ,("getPriv", (TyArr (TyDt "Address" []) TyBool))
                       ,("AddressBook", (TyArr (TyDt "List" [TyDt "Address" []]) (TyArr (TyDt "List" [TyDt "Address" []]) (TyDt "AddressBook" []))))
                       ,("AddressBook_match", (TyArr (TyDt "AddressBook" []) (TyDt "List" [TyDt "Address" []])))
                       ,("a", (TyDt "AddressBook" []))
                       ,("b", (TyDt "AddressBook" []))
                       ,("mergeAddressBooks", (TyArr (TyDt "AddressBook" []) (TyArr (TyDt "AddressBook" []) (TyDt "AddressBook" []))))
                       ]
    makeEdge = [("Node", TyAll "a" (TyArr (TyId "a") (TyDt "Node" [TyId "a"])))
               ,("Edge", TyAll "a" ((TyArr (TyDt "Node" [TyId "a"]) (TyArr TyString (TyArr (TyDt "Node" [TyId "a"]) (TyDt "Edge" [TyId "a"]))))))
               ,("Pair", TyAll "a" (TyAll "b" (TyArr (TyId "a") (TyArr (TyId "b") (TyDt "Pair" [TyId "a", TyId "b"])))))
               ,("Pair_fst", TyAll "a" (TyAll "b" (TyArr (TyDt "Pair" [TyId "a", TyId "b"]) (TyId "a"))))
               ,("Pair_snd", TyAll "a" (TyAll "b" (TyArr (TyDt "Pair" [TyId "a", TyId "b"]) (TyId "b"))))
               ,("makeEdge", TyAll "a" (TyArr (TyDt "Pair" [TyDt "Node" [TyId "a"], TyDt "Node" [TyId "a"]]) (TyDt "Edge" [TyId "a"])))
               ,("nodes", (TyDt "Pair" [TyDt "Node" [TyId "a"], TyDt "Node" [TyId "a"]]))
               ,("label", (TyString))
               ]
    replicateTest = [("Nil",  TyAll "a" (TyDt "List" [TyId "a"]))
                    ,("Cons", TyAll "a" (TyArr (TyId "a") (TyArr (TyDt "List" [TyId "a"]) (TyDt "List" [TyId "a"]))))
                    ,("Cons_head", TyAll "a" (TyArr (TyDt "List" [TyId "a"]) (TyId "a")))
                    ,("Cons_tail", TyAll "a" (TyArr (TyDt "List" [TyId "a"]) (TyDt "List" [TyId "a"])))
                    ,("inc", TyArr TyInt TyInt)
                    ,("dec", TyArr TyInt TyInt)
                    ,("leq", TyArr TyInt (TyArr TyInt TyBool))
                    ,("neq", TyArr TyInt (TyArr TyInt TyBool))
                    ,("n", TyInt)
                    ,("x", (TyId "a"))
                    ,("replicate", TyAll "a" (TyArr TyInt (TyArr (TyId "a") (TyDt "List" [TyId "a"]))))]
    listConcat = [("Nil",  TyAll "a" (TyDt "List_nil" [TyId "a"]))
                 ,("ConsToList", TyAll "a" (TyArr (TyDt "List_cons" [TyId "a"]) (TyDt "List" [TyId "a"])))
                 ,("NilToList", TyAll "a" (TyArr (TyDt "List_nil" [TyId "a"]) (TyDt "List" [TyId "a"])))
                 ,("Cons", TyAll "a" (TyArr (TyId "a") (TyArr (TyDt "List" [TyId "a"]) (TyDt "List" [TyId "a"]))))
                 ,("Cons_head", TyAll "a" (TyArr (TyDt "List_cons" [TyId "a"]) (TyId "a")))
                 ,("Cons_tail", TyAll "a" (TyArr (TyDt "List_cons" [TyId "a"]) (TyDt "List" [TyId "a"])))
                 ,("Nil2",  TyAll "a" (TyDt "ListOfLists_nil" [TyId "a"]))
                 ,("Cons2ToList", TyAll "a" (TyArr (TyDt "ListOfLists_cons" [TyId "a"]) (TyDt "ListOfLists" [TyId "a"])))
                 ,("Nil2ToList", TyAll "a" (TyArr (TyDt "ListOfLists_nil" [TyId "a"]) (TyDt "ListOfLists" [TyId "a"])))
                 ,("Cons2", TyAll "a" (TyArr (TyDt "List" [TyId "a"]) (TyArr (TyDt "ListOfLists" [TyId "a"]) (TyDt "ListOfLists" [TyId "a"]))))
                 ,("Cons2_head", TyAll "a" (TyArr (TyDt "ListOfLists_cons" [TyId "a"]) (TyDt "List" [TyId "a"])))
                 ,("Cons2_tail", TyAll "a" (TyArr (TyDt "ListOfLists_cons" [TyId "a"]) (TyDt "ListOfLists" [TyId "a"])))
                 ,("append", TyAll "a" (TyArr (TyDt "List" [TyId "a"]) (TyArr (TyDt "List" [TyId "a"]) (TyDt "List" [TyId "a"]))))
                 ,("xss", TyDt "ListOfLists" [TyId "a"])
                 ,("xss", TyDt "ListOfLists_nill" [TyId "a"])
                 ,("xss", TyDt "ListOfLists_cons" [TyId "a"])
                 ,("concat", TyAll "a" (TyArr (TyDt "ListOfLists" [TyId "a"]) (TyDt "List" [TyId "a"])))
                 ]
    sampleTest = [("f",(TyArr (TyInt) (TyArr (TyBool) (TyArr (TyInt) (TyInt))))) -- Int -> Bool -> Int -> Int
                 , ("name", TyChar) -- Char
                 , ("g", TyArr (TyString) (TyBool)) -- String -> Bool
                 , ("lst", TyDt "List" [TyInt]) -- List Int
                 , ("h", TyArr (TyDt "List" [TyInt]) TyBool) -- List Int -> Bool
                 ,("s", TyAll "X" (TyArr (TyDt "List" [TyId "X"]) TyBool)) -- List a -> Bool
                 ,("t", TyAll "X" (TyArr (TyDt "List" [TyId "X"]) (TyDt "List" [TyId "X"]))) -- List a -> List a
                 , ("r", TyAll "X" (TyAll "Y" (TyArr (TyDt "List" [TyId "X"]) (TyDt "List" [TyId "Y"])))) -- List a -> List b
                 ]
    bvadd  = [("Bit", (TyArr TyBool (TyDt "BitVec" [])))
             ,("Cons", (TyArr TyBool (TyArr (TyDt "BitVec" []) (TyDt "BitVec" []))))
             ,("Bit_v", (TyArr (TyDt "BitVec" []) TyBool))
             ,("Cons_head", (TyArr (TyDt "BitVec" []) TyBool))
             ,("Cons_tail", (TyArr (TyDt "BitVec" []) (TyDt "BitVec" [])))
             ,("true", TyBool)
             ,("false", TyBool)
             ,("plus1", (TyArr (TyDt "BitVec" []) (TyArr (TyDt "BitVec" []) (TyArr TyBool (TyDt "BitVec" [])))))
             ,("plus", TyArr (TyDt "BitVec" []) (TyArr (TyDt "BitVec" []) (TyDt "BitVec" [])))
             ,("x", (TyDt "BitVec" []))
             ,("y", (TyDt "BitVec" []))
             ]
    bstExtractMin = [("Empty", TyAll "a" (TyDt "BST_empty" [TyId "a"]))
                    ,("Node", TyAll "a" (TyArr (TyId "a") (TyArr (TyDt "BST" [TyId "a"]) (TyDt "BST" [TyId "a"]))))
                    ,("Node_v", TyAll "a" (TyArr (TyDt "BST_node" [TyId "a"]) (TyId "a")))
                    ,("Node_tree", TyAll "a" (TyArr (TyDt "BST_node" [TyId "a"]) (TyDt "BST" [TyId "a"])))
                    ,("NodeToBST", TyAll "a" (TyArr (TyDt "BST_node" [TyId "a"]) (TyDt "BST" [TyId "a"])))
                    ,("EmptyToBST", TyAll "a" (TyArr (TyDt "BST_empty" [TyId "a"]) (TyDt "BST" [TyId "a"])))
                    ,("MinPair", TyAll "a" (TyArr (TyId "a") (TyArr (TyDt "BST" [TyId "a"]) (TyDt "MinPair" [TyId "a"]))))
                    ,("extractMin", TyAll "a" (TyArr (TyDt "BST" [TyId "a"]) (TyDt "MinPair" [TyId "a"])))
                    ,("t", TyDt "BST" [TyId "a"])
                    ]
    nnf = [("Var", TyArr (TyDt "Id" []) (TyDt "Expr" []))
          ,("Var_id", TyArr (TyDt "Expr" []) (TyDt "Id" []))
          ,("Not", TyArr (TyDt "Expr" []) (TyDt "Expr" []))
          ,("Not_expr", TyArr (TyDt "Expr" []) (TyDt "Expr" []))
          ,("And", TyArr (TyDt "Expr" []) (TyArr (TyDt "Expr" []) (TyDt "Expr" [])))
          ,("And_lhs", TyArr (TyDt "Expr" []) (TyDt "Expr" []))
          ,("And_rhs", TyArr (TyDt "Expr" []) (TyDt "Expr" []))
          ,("Or", TyArr (TyDt "Expr" []) (TyArr (TyDt "Expr" []) (TyDt "Expr" [])))
          ,("Or_lhs", TyArr (TyDt "Expr" []) (TyDt "Expr" []))
          ,("Or_rhs", TyArr (TyDt "Expr" []) (TyDt "Expr" []))
          ,("Implies", TyArr (TyDt "Expr" []) (TyArr (TyDt "Expr" []) (TyDt "Expr" [])))
          ,("Implies_lhs", TyArr (TyDt "Expr" []) (TyDt "Expr" []))
          ,("Implies_rhs", TyArr (TyDt "Expr" []) (TyDt "Expr" []))
          ,("NAtom", TyArr (TyDt "Id" []) (TyArr TyBool (TyDt "NExpr" [])))
          ,("NAtom_id", TyArr (TyDt "NExpr" []) (TyDt "Id" []))
          ,("NAtom_neg", TyArr (TyDt "NExpr" []) (TyBool))
          ,("NAnd", TyArr (TyDt "NExpr" []) (TyArr (TyDt "NExpr" []) (TyDt "NExpr" [])))
          ,("NAnd_lhs", TyArr (TyDt "NExpr" []) (TyDt "NExpr" []))
          ,("NAnd_rhs", TyArr (TyDt "NExpr" []) (TyDt "NExpr" []))
          ,("NOr", TyArr (TyDt "NExpr" []) (TyArr (TyDt "NExpr" []) (TyDt "NExpr" [])))
          ,("NOr_lhs", TyArr (TyDt "NExpr" []) (TyDt "NExpr" []))
          ,("NOr_rhs", TyArr (TyDt "NExpr" []) (TyDt "NExpr" []))
          ,("true", TyBool)
          ,("false", TyBool)
          ,("toNNF", TyArr (TyDt "Expr" []) (TyDt "NExpr" []))
          ,("e", TyDt "Expr" [])
          ,("stringToExpr", TyArr TyString (TyDt "Expr" []))
          ,("stringToNExpr", TyArr TyString (TyDt "NExpr" []))
          ]
    target = TyDt "Edge" [TyId "a"]--TyDt "Edge" [TyId "a"] --TyDt "NExpr" [] --TyDt "MinPair" [TyId "a"] --TyDt "List" [TyId "a"]  --TyDt "AddressBook" [] -- TyDt "BitVec" [] --TyDt "AddressBook" [] --TyDt "List" [TyId "a"] --TyAll "a" (TyDt "List" [TyId "a"]) --TyDt "AddressBook" []--TyAll "X" (TyDt "List" [TyId "X"])
    sctx = map (\(n,t)->(n,VarBind (toSuccinctType t))) makeEdge
    -- tyCtx = []
    starget = toSuccinctType target
    result = removeDups (traversal sctx [] starget) []
    types = getUniqueSet result
    prunedRes = prune sctx result (filter (\x-> not (isReachable sctx result [] x)) types)
    prunedTys = getUniqueSet prunedRes
    tyIndices = toTypeIndices types 
    prunedIdx = toTypeIndices prunedTys
    edges = generateEdges result tyIndices
    prunedEdges = generateEdges prunedRes prunedIdx
    gr = buildG (0,(length tyIndices)-1) edges
    prunedGr = buildG (0,(length prunedIdx)-1) prunedEdges
    labeling ti x  = let t = getTypeByIndex ti x in 
                       if t == starget
                         then "\""++(succinct2str t)++"\",fillcolor=\"#ffffff\", style=filled"
                         else case t of
                                SCmp _ -> "\""++(succinct2str t)++"\",fillcolor=\"#1f78b4\", fontcolor=\"#ffffff\",style=filled"
                                SRaw _ -> "\""++(succinct2str t)++"\",fillcolor=\"#a6cee3\", style=filled"
                                _      -> "\""++(succinct2str t)++"\",fillcolor=\"#b2df8a\", style=filled"
    lgr = LabGraph gr (labeling tyIndices)
    prunedLgr = LabGraph prunedGr (labeling prunedIdx)
    --tmp = rootTypeOf sctx starget
  [f] <- getArgs
  writeFile f $ showGraphViz lgr tyIndices
  writeFile (f++"_pruned") $ showGraphViz prunedLgr prunedIdx
  --putStrLn $ foldl (\acc (t1,n,t2) -> acc ++ (succinct2str t1) ++ "="++n++"=>" ++ (succinct2str t2) ++ "\n") "" result
  --putStrLn $ foldl (\acc (n,t2) -> acc ++n++"=>" ++ (succinct2str t2) ++ "\n") "" tmp