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
-- import Control.Monad
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

type RSuccinctType = SuccinctType Formula

baseToSuccinctType :: BaseType Formula -> RSuccinctType
baseToSuccinctType (DatatypeT id ts _) = SuccinctDatatype resIds resTys Map.empty
  where
    mergeDt (accIds, accTys) t = case rtypeToSuccinctType t of
      SuccinctDatatype ids tys _ -> (ids `Set.union` accIds, tys `Set.union` accTys)
      ty                         -> (accIds, Set.singleton ty `Set.union` accTys)
    (resIds, resTys) = foldl mergeDt (Set.singleton (id, length ts), Set.empty) ts
baseToSuccinctType t = SuccinctScalar t

rtypeToSuccinctType :: RType -> RSuccinctType
rtypeToSuccinctType (ScalarT bt _) = baseToSuccinctType bt
rtypeToSuccinctType (FunctionT _ param ret) = case rtypeToSuccinctType ret of
  SuccinctFunction paramSet retTy -> SuccinctFunction (Set.singleton (rtypeToSuccinctType param) `Set.union` paramSet) retTy
  t                               -> SuccinctFunction (Set.singleton (rtypeToSuccinctType param)) t
rtypeToSuccinctType (LetT id varty bodyty) = SuccinctLet id (rtypeToSuccinctType varty) (rtypeToSuccinctType bodyty)
rtypeToSuccinctType AnyT = SuccinctAny

toSuccinctType :: RSchema -> RSuccinctType
toSuccinctType (Monotype t) = rtypeToSuccinctType t
toSuccinctType (ForallT id t) = case toSuccinctType t of
  SuccinctAll ids ty -> SuccinctAll (Set.singleton id `Set.union` ids) ty
  ty                 -> SuccinctAll (Set.singleton id) ty
toSuccinctType (ForallP _ t) = toSuccinctType t


type SuccTypeSubstitution = Map Id RSuccinctType

succinctTypeSubstitute :: SuccTypeSubstitution -> RSuccinctType -> RSuccinctType
succinctTypeSubstitute subst (SuccinctScalar baseT) = case baseT of
  TypeVarT _ a -> case Map.lookup a subst of
    Just t -> succinctTypeSubstitute subst t
    Nothing -> SuccinctScalar baseT
  _ -> SuccinctScalar baseT
succinctTypeSubstitute subst (SuccinctFunction tArgs tRes) = SuccinctFunction tArgs' tRes'
  where
    tArgs' = Set.map (succinctTypeSubstitute subst) tArgs
    tRes' = succinctTypeSubstitute subst tRes
succinctTypeSubstitute subst (SuccinctDatatype idSet tySet constructors) = SuccinctDatatype idSet tySet' constructors
  where
    tySet' = Set.map (succinctTypeSubstitute subst) tySet
succinctTypeSubstitute subst (SuccinctAll idSet ty) = SuccinctAll idSet' ty'
  where
    idSet' = Set.filter (\id -> not $ isJust (Map.lookup id subst)) idSet
    ty' = succinctTypeSubstitute subst ty
succinctTypeSubstitute subst (SuccinctComposite tySet) = SuccinctComposite tySet'
  where
    tySet' = Set.map (succinctTypeSubstitute subst) tySet
succinctTypeSubstitute subst (SuccinctLet id tDef tBody) = SuccinctLet id tDef' tBody'
  where
    tDef' = succinctTypeSubstitute subst tDef
    tBody' = succinctTypeSubstitute subst tBody
succinctTypeSubstitute subst SuccinctAny = SuccinctAny
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