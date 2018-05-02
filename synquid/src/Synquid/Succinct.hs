module Synquid.Succinct where

import Synquid.Type hiding (set)
import Synquid.Util
import Synquid.Logic

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List as List
import Data.Maybe
import Control.Lens as Lens

data SuccinctType r = 
  SuccinctScalar (BaseType r) |
  SuccinctFunction (Set (SuccinctType r)) (SuccinctType r) |
  SuccinctDatatype (Set (Id, Int)) (Set (SuccinctType r)) (Map Id (Set Id)) | -- Datatype names, included types and datatype constructors
  SuccinctAll (Set Id) (SuccinctType r) |
  SuccinctComposite (Set (SuccinctType r)) |
  SuccinctLet Id (SuccinctType r) (SuccinctType r) |
  SuccinctAny |
  SuccinctInhabited (SuccinctType r)
  deriving (Show, Eq, Ord)

-- instance Eq (SuccinctType r) where
--   SuccinctDatatype ids1 tys1 cons1 == SuccinctDatatype ids2 tys2 cons2 = ids1 == ids2 && tys1 == tys2 && (Map.null cons1 || Map.null cons2 || cons1 == cons2)
--   sty1 == sty2 = sty1 == sty2

-- instance Ord (SuccinctType r)  where
--   SuccinctDatatype ids1 tys1 cons1 <= SuccinctDatatype ids2 tys2 cons2 = ids1 <= ids2 && tys1 <= tys2
--   sty1 <= sty2 = sty1 <= sty2

type RSuccinctType = SuccinctType Formula

extractBaseTyVars :: BaseType Formula -> Set Id
extractBaseTyVars (TypeVarT _ id) = Set.singleton id
extractBaseTyVars (DatatypeT id ts _) = foldl (\acc t -> acc `Set.union` (extractRTyVars t)) Set.empty ts
extractBaseTyVars _ = Set.empty

extractRTyVars :: RType -> Set Id
extractRTyVars (ScalarT bt _) = extractBaseTyVars bt
extractRTyVars (FunctionT _ param ret) = (extractRTyVars param) `Set.union` (extractRTyVars ret)
extractRTyVars _ = Set.empty

extractSuccinctTyVars :: RSuccinctType -> Set Id
extractSuccinctTyVars (SuccinctScalar t) = extractBaseTyVars t
extractSuccinctTyVars (SuccinctFunction args ret) = foldl (\acc t -> (extractSuccinctTyVars t) `Set.union` acc) (extractSuccinctTyVars ret) args
extractSuccinctTyVars (SuccinctDatatype _ tys _) = foldl (\acc t -> (extractSuccinctTyVars t) `Set.union` acc) Set.empty tys
extractSuccinctTyVars (SuccinctAll ids _) = ids
extractSuccinctTyVars (SuccinctComposite tys) = foldl (\acc t -> (extractSuccinctTyVars t) `Set.union` acc) Set.empty tys
extractSuccinctTyVars _ = Set.empty

baseToSuccinctType :: BaseType Formula -> RSuccinctType
baseToSuccinctType (DatatypeT id ts _) = if "_" == id 
  then SuccinctAll (Set.singleton "_") (SuccinctScalar (TypeVarT Map.empty "_"))
  else SuccinctDatatype resIds resTys Map.empty
  where
    mergeDt (accIds, accTys) t = case outOfSuccinctAll (rtypeToSuccinctType t) of
      SuccinctDatatype ids tys _ -> (ids `Set.union` accIds, tys `Set.union` accTys)
      ty                         -> (accIds, Set.singleton ty `Set.union` accTys)
    (resIds, resTys) = foldl mergeDt (Set.singleton (id, length ts), Set.empty) ts
baseToSuccinctType t = SuccinctScalar t

rtypeToSuccinctType :: RType -> RSuccinctType
rtypeToSuccinctType t@(ScalarT bt _) = let 
  vars = extractRTyVars t 
  ty = baseToSuccinctType bt
  in if Set.size vars == 0 then ty else simplifySuccinctType $ SuccinctAll vars ty
rtypeToSuccinctType t@(FunctionT _ param ret) = let
  vars = extractRTyVars t
  ty = case outOfSuccinctAll (rtypeToSuccinctType ret) of
    SuccinctFunction paramSet retTy -> SuccinctFunction (Set.singleton (rtypeToSuccinctType param) `Set.union` paramSet) retTy
    ty'                             -> SuccinctFunction (Set.singleton (rtypeToSuccinctType param)) ty'
  in if Set.size vars == 0 then ty else simplifySuccinctType $ SuccinctAll vars ty
rtypeToSuccinctType t@(LetT id varty bodyty) = let
  vars = extractRTyVars t
  ty = SuccinctLet id (rtypeToSuccinctType varty) (rtypeToSuccinctType bodyty)
  in if Set.size vars == 0 then ty else simplifySuccinctType $ SuccinctAll vars ty
rtypeToSuccinctType AnyT = SuccinctAny

toSuccinctType :: RSchema -> RSuccinctType
toSuccinctType (Monotype t) = rtypeToSuccinctType t
toSuccinctType (ForallT id t) = case toSuccinctType t of
  SuccinctAll ids ty -> SuccinctAll (Set.singleton id `Set.union` ids) ty
  ty                 -> SuccinctAll (Set.singleton id) ty
toSuccinctType (ForallP _ t) = toSuccinctType t

outOfSuccinctAll :: RSuccinctType -> RSuccinctType
outOfSuccinctAll (SuccinctFunction paramSet ret) = SuccinctFunction (Set.map outOfSuccinctAll paramSet) (outOfSuccinctAll ret)
outOfSuccinctAll (SuccinctDatatype ids tys cons) = SuccinctDatatype ids (Set.map outOfSuccinctAll tys) cons
outOfSuccinctAll (SuccinctAll ids ty) = ty
outOfSuccinctAll ty = ty

simplifySuccinctType :: RSuccinctType -> RSuccinctType
simplifySuccinctType t@(SuccinctFunction paramSet ret) = case ret of
  SuccinctFunction ps rt -> SuccinctFunction (paramSet `Set.union` ps) rt
  _ -> t
simplifySuccinctType t@(SuccinctDatatype idsIn tysIn consIn) = let
  fold_fun (accIds, accTys, accCons) ty = case ty of
    SuccinctDatatype ids tys cons -> (ids `Set.union` accIds, tys `Set.union` accTys, cons `Map.union` accCons)
    _ -> (accIds, Set.insert ty accTys, accCons)
  (ids, tys, cons) = Set.foldl fold_fun (idsIn, Set.empty, consIn) (Set.map simplifySuccinctType tysIn)
  in SuccinctDatatype ids tys cons
simplifySuccinctType t@(SuccinctAll ids ty) = case simplifySuccinctType ty of
  SuccinctAll ids' ty' -> SuccinctAll (ids `Set.union` ids') (outOfSuccinctAll ty')
  _ -> SuccinctAll ids (outOfSuccinctAll ty)
simplifySuccinctType t@(SuccinctComposite tys) = SuccinctComposite (Set.map simplifySuccinctType tys)
simplifySuccinctType t@(SuccinctInhabited ty) = SuccinctInhabited (simplifySuccinctType ty)
simplifySuccinctType t = t

type SuccTypeSubstitution = Map Id RSuccinctType

succinctTypeSubstitute :: SuccTypeSubstitution -> RSuccinctType -> RSuccinctType
succinctTypeSubstitute subst (SuccinctScalar baseT) = case baseT of
  TypeVarT _ a -> case Map.lookup a subst of
    Just t -> simplifySuccinctType $ succinctTypeSubstitute subst t -- TODO remove this key/value pair after we finish this substitution
    Nothing -> SuccinctScalar baseT
  _ -> SuccinctScalar baseT
succinctTypeSubstitute subst (SuccinctFunction tArgs tRes) = simplifySuccinctType $ SuccinctFunction tArgs' tRes'
  where
    tArgs' = Set.map (succinctTypeSubstitute subst) tArgs
    tRes' = succinctTypeSubstitute subst tRes
succinctTypeSubstitute subst (SuccinctDatatype idSet tySet constructors) = simplifySuccinctType $ SuccinctDatatype idSet tySet' constructors
  where
    tySet' = Set.map (succinctTypeSubstitute subst) tySet
succinctTypeSubstitute subst (SuccinctAll idSet ty) = simplifySuccinctType $ SuccinctAll idSet' ty'
  where
    idSet' = Set.filter (\id -> not $ isJust (Map.lookup id subst)) idSet
    ty' = succinctTypeSubstitute subst ty
succinctTypeSubstitute subst (SuccinctComposite tySet) = simplifySuccinctType $ SuccinctComposite tySet'
  where
    tySet' = Set.map (succinctTypeSubstitute subst) tySet
succinctTypeSubstitute subst (SuccinctLet id tDef tBody) = simplifySuccinctType $ SuccinctLet id tDef' tBody'
  where
    tDef' = succinctTypeSubstitute subst tDef
    tBody' = succinctTypeSubstitute subst tBody
succinctTypeSubstitute subst SuccinctAny = SuccinctAny
succinctTypeSubstitute subst (SuccinctInhabited t) = simplifySuccinctType $ SuccinctInhabited (succinctTypeSubstitute subst t)
  -- where
  --   getFromTy (SuccinctFunction paramSet retTy) = if retTy == sty then Just (SuccinctComposite paramSet) else Nothing
  --   getFromTy (SuccinctAll idSet ty) = case ty of
  --     SuccinctFunction pty rty -> let (unified, substitution) = unify env rty sty
  --                                     pty' = Set.map (succinctTypeSubstitute substitution) pty
  --                                 in if unified then Just (SuccinctComposite pty') else Nothing
  --     _                        -> let (unified, substitution) = unify env ty sty
  --                                 in if unified then Just (succinctTypeSubstitute substitution ty) else Nothing
  --   getFromTy ty = if ty == sty then Just ty else Nothing
    -- allSatTy = Map.map fromJust $ Map.filter isJust $ Map.map getFromTy (env ^. succinctSymbols)

--   let env' = 
-- -- if this variable is a constructor
--     if Set.size ids == 1 
--       then case Map.lookup (Set.take 1 ids) (env ^. datatypes) of
--         Just dtDef -> if Set.member name Set.fromList (df ^. constructors)
--           then (succinctSymbols %~ Map.insert name (SuccinctDatatype ids tys (Map.singleton (Set.take 1 ids) (Set.singleton name)))) env
--           else env
-- -- if this variable has not yet been assigned with some constructor
--       else if Set.size cons == 0
--         then let consSet = Set.map (\id -> (id, Set.fromList ((fromJust (Map.lookup id (env ^. datatypes))) ^. constructors))) ids
--                  consMap = Set.foldl (\acc (id,set) -> Map.insert id set acc) Map.empty consSet
--           in (succinctSymbols %~ Map.insert name (SuccinctDatatype ids tys consMap)) env
--         else env

unifySuccinct :: RSuccinctType -> RSuccinctType -> [Id] -> (Bool, [SuccTypeSubstitution])
unifySuccinct comp target boundedTys = case (comp, target) of
  (SuccinctScalar (TypeVarT _ id), target) -> if id `elem` boundedTys then (False, [Map.empty]) else (True, [Map.singleton id target])
  (SuccinctScalar t1, SuccinctScalar t2) -> (t1 == t2, [Map.empty])
  (SuccinctDatatype idSet1 tySet1 consMap1, SuccinctDatatype idSet2 tySet2 consMap2) -> 
    if idSet1 `Set.isSubsetOf` idSet2
      then 
        let 
          isTyVar ty = case ty of 
            SuccinctScalar (TypeVarT _ _) -> True
            _                             -> False
          getTyVar (SuccinctScalar (TypeVarT _ id)) = id
          isBound tv = tv `elem` boundedTys -- [TODO] is the bounded value checked correctly?
          -- bound1 = tySet1
          bound1 = (Set.filter (not . isTyVar) tySet1) `Set.union` (Set.filter (isBound . getTyVar) (Set.filter isTyVar tySet1)) 
          -- bound2 = (Set.filter (not . isTyVar) tySet2) `Set.union` (Set.filter (isBound . getTyVar) (Set.filter isTyVar tySet2))
          bound2 = tySet2
        in 
          if bound1 `Set.isSubsetOf` bound2
            then
              let consMapDiff = Map.intersectionWith Set.difference consMap1 consMap2
                  isConsMatch = Map.foldl (\acc s -> acc && (Set.null s)) True consMapDiff
              in if isConsMatch
                then
                  let 
                    consDiff = idSet2 `Set.difference` idSet1
                    tyDiff = bound2 `Set.difference` bound1
                    freeVt = tySet1 `Set.difference` bound1
                    optCons = idSet2 `Set.intersection` idSet1
                    optTy = tySet1 `Set.intersection` tySet2
                  in (True, allCombos consDiff tyDiff freeVt optCons optTy)
                else (False, [Map.empty])
            else (False, [Map.empty])
      else (False, [Map.empty])
  _ -> (False, [Map.empty])
  where
    powerset s = 
      if s == Set.empty 
        then Set.singleton Set.empty
        else Set.map (Set.insert x) pxs `Set.union` pxs
          where (x, xs) = Set.deleteFindMin s
                pxs = powerset xs

    distribute :: (Ord a) => Int -> Set a -> [[Set a]]
    distribute 1 elements = [[elements]]
    distribute n elements = 
      let pset = powerset elements
          allRemain s = Set.toList $ Set.filter ((elements `Set.difference` s) `Set.isSubsetOf`) pset
          mergeRemain s acc ss = acc ++ (List.map ((:) s) (distribute (n-1) ss))
      in Set.foldl (\acc s -> acc ++ (List.foldl (mergeRemain s) [] (allRemain s))) [] pset

    allCombos :: Set (Id,Int) -> Set RSuccinctType -> Set RSuccinctType -> Set (Id,Int) -> Set RSuccinctType -> [SuccTypeSubstitution]
    allCombos cons tys freeVars tcons tty =
      if length freeVars == 0 -- (length cons /= 0 || length tys /= 0) && (length freeVars == 0) -- no freeVars to fill
        then [Map.empty]
        else
          let mustTys = distribute (Set.size freeVars) tys
              mustCons = distribute (Set.size freeVars) cons
              -- optTy = Set.toList $ powerset tty
              -- optCon = Set.toList $ powerset tcons
              optTys = replicate (Set.size freeVars) $ Set.toList $ powerset tty
              optCons = replicate (Set.size freeVars) $ Set.toList $ powerset tcons
              optAssign [] = [[]]
              optAssign (t:ts) = [x:y | x <- t, y <- optAssign ts]
              combine x y = map (\(a,b) -> a `Set.union` b) (List.zip x y)
              finalTys = [combine x y | x <- mustTys, y <- optAssign optTys]
              finalCons = [combine x y | x <- mustCons, y <- optAssign optCons]
              assign vars x y = case (vars, x, y) of
                ((SuccinctScalar (TypeVarT _ id)):vs, xx:xs, yy:ys) -> if Set.null xx 
                  then if Set.size yy > 0
                    then Map.insert id (Set.findMin yy) (assign vs xs ys)
                    else Map.empty
                  else Map.insert id (SuccinctDatatype xx yy Map.empty) (assign vs xs ys)
                _ -> Map.empty
              isValid x y = if Set.null x
                then True
                else let cnt = Set.foldl (\acc (_,n)->if n>acc then n else acc) 0 x
                         len = (Set.size y) + (Set.foldl (\acc (_,n)->if n==0 then acc+1 else acc) 0 x)
                     in (cnt > 1 && len >= 1) || (cnt == 0 && (len == 0 || len == 1)) || (cnt == 1 && len == 1)
              resultMap = [assign (Set.toList freeVars) c t | c <- finalCons, t <- finalTys,
                                                              (foldl (\acc (x,y) -> acc && (isValid x y)) True (zip c t))]
          in resultMap

getDestructors :: Id -> RType -> Map Id RType
getDestructors name ty = case ty of
  FunctionT _ tArg tRet -> let 
    retTy = getFunRet ty
    resMap = getDestructors name tRet
    in
    Map.insert (name++"_match_"++(show (Map.size resMap))) (FunctionT "x" retTy tArg) resMap
  _ -> Map.empty
  where
    getFunRet t = case t of
      FunctionT _ _ t' -> getFunRet t'
      _ -> t

getSuccinctDestructors :: Id -> RSuccinctType -> Set RSuccinctType
getSuccinctDestructors name sty = case sty of
  SuccinctFunction params ret -> case ret of
    SuccinctDatatype ids tys consMap -> let
      (datatypeName, _) = Set.findMin ids
      destructors = Set.map (\param -> SuccinctFunction (Set.singleton (SuccinctDatatype ids tys (Map.singleton datatypeName (Set.singleton name)))) param) params
      in destructors
    _ -> Set.empty
  _ -> Set.empty

reverseGraph :: Map RSuccinctType (Map RSuccinctType (Set Id)) -> Map RSuccinctType (Map RSuccinctType (Set Id))
reverseGraph graph = reverseGraphHelper Map.empty graph
  where
    fold_fun acc k v = Map.foldlWithKey' (\tmap k' v' -> Map.insertWith mergeMapOfSet k' v' tmap) acc (Map.map (\s -> Map.singleton k s) v)
    reverseGraphHelper acc g = Map.foldlWithKey' fold_fun Map.empty g

allSuccinctNodes :: Map RSuccinctType (Map RSuccinctType (Set Id)) -> Set RSuccinctType
allSuccinctNodes graph = let 
  filter_fun ty = case ty of
    SuccinctComposite _ -> False
    SuccinctInhabited _ -> False
    _ -> True
  allNodes = Map.foldl' (\acc map -> (Map.keysSet map) `Set.union` acc) (Map.keysSet graph) graph
  in Set.filter filter_fun allNodes

mergeMapOfSet :: Map RSuccinctType (Set Id) -> Map RSuccinctType (Set Id) -> Map RSuccinctType (Set Id)
mergeMapOfSet new old = Map.foldlWithKey' fold_fun old new
  where
    fold_fun accMap kty idSet = Map.insert kty ((Map.findWithDefault Set.empty kty accMap) `Set.union` idSet) accMap

getInhabitedNodes :: Map RSuccinctType (Map RSuccinctType (Set Id)) -> Set RSuccinctType
getInhabitedNodes graph = Set.filter filter_fun allNodes
  where
    allNodes = Map.foldl' (\acc map -> (Map.keysSet map) `Set.union` acc) (Map.keysSet graph) graph
    filter_fun ty = case ty of
      SuccinctInhabited _ -> True
      _ -> False

isSuccinctAll (SuccinctAll _ _) = True
isSuccinctAll _ = False

findDstNodesInGraph :: Map RSuccinctType (Map RSuccinctType (Set Id)) -> RSuccinctType -> [Id] -> Map RSuccinctType (Set Id)
findDstNodesInGraph graph typ boundTypeVars = case typ of
  SuccinctLet _ _ ty -> findDstNodesInGraph graph ty boundTypeVars
  _ -> let
    filter_fun k v = case typ of
      SuccinctDatatype ids tys _ -> case k of
        SuccinctDatatype ids' tys' _ -> ids == ids' && tys == tys'
        _ -> False
      SuccinctAll _ ty -> let (res,_) = unifySuccinct ty k boundTypeVars in res 
      _ -> k == typ
    candidateMap = Map.filterWithKey filter_fun graph
    in Map.foldl (\acc m -> Map.foldlWithKey (\accM kty set -> Map.insertWith Set.union kty set accM) acc m) Map.empty candidateMap

getReachableNodes :: Map RSuccinctType (Map RSuccinctType (Set Id)) -> Set RSuccinctType
getReachableNodes graph = getReachableNodesHelper graph Set.empty (getInhabitedNodes graph)
  where
    getReachableNodesHelper g visited toVisit = 
      if Set.size toVisit == 0
        then visited
        else let curr = Set.findMin toVisit
          in if Set.member curr visited 
            then rmUnreachableComposite $ getReachableNodesHelper g visited (Set.delete curr toVisit)
            else rmUnreachableComposite $ getReachableNodesHelper g (Set.insert curr visited) (Map.keysSet (findDstNodesInGraph graph curr []) `Set.union` (Set.delete curr toVisit))

rmUnreachableComposite :: Set RSuccinctType -> Set RSuccinctType
rmUnreachableComposite reachableSet = Set.foldl (\acc t -> if isCompositeReachable t then acc else Set.delete t acc) reachableSet (compositeNodes)
  where
    isCompositeNode ty = case ty of
      SuccinctComposite _ -> True
      _ -> False
    compositeNodes = Set.filter isCompositeNode reachableSet
    isCompositeReachable t = let SuccinctComposite tySet = t in 
      Set.foldl (\acc b -> acc && (Set.member b reachableSet)) True tySet

isReachable :: Map RSuccinctType (Map RSuccinctType (Set Id)) -> RSuccinctType -> Bool
isReachable graph ty = Set.member ty $ getReachableNodes graph

-- | function for debug
printGraph :: Map RSuccinctType (Map RSuccinctType (Set Id)) -> String
printGraph graph = Map.foldlWithKey' printMap "" graph
  where
    printMap acc k v = Set.foldl (\tmp x -> tmp ++ (show k) ++ x) acc (Map.foldlWithKey' printSet Set.empty v)
    printSet acc k s = acc `Set.union` Set.map (\x -> "--" ++ x ++ "-->" ++ (show k) ++ "\n") s