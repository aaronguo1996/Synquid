module Succinct where

import Data.List
import Data.Tuple
import Utility

data BaseType = 
    Int
  | Bool
  | String
  | Char
  | DT String Type
  | TVar String

data Type = 
    BType BaseType
  | Fun Type Type
  | TypeSet [Type]

data SuccinctType = 
    SuccFun [SuccinctType] Type
  | SuccVar [String] [SuccinctType]
  | SuccCom [SuccinctType]

type Context = [(String, Type)]

hasTVar :: Type -> Bool
hasTVar (BType (TVar _))    = True
hasTVar (BType _)           = False
hasTVar (Fun paramTy retTy) = (hasTVar paramTy) || (hasTVar retTy)

-- | convert data types into succinct ones
-- succinct type has type like set -> retTy
-- types in set have no duplicates
--
toSuccinctType :: Type -> SuccinctType
toSuccinctType (BType bt) = case bt of
    DT name ty | hasTVar ty -> case toSuccinctType ty of
                               SuccVar names tys -> SuccVar (removeDups (name:names) []) tys
                               _ -> SuccFun [] (BType bt)
               | otherwise -> SuccFun [] (BType bt)
    _ -> SuccFun [] (BType bt)
toSuccinctType (Fun paramTy retLst) = case (elemIndex succinctParam tyLst) of
    Just i  -> SuccFun tyLst retTy
    Nothing -> SuccFun ((toSuccinctType paramTy):tyLst) retTy
  where
    succinctParam = toSuccinctType paramTy
    SuccFun tyLst retTy = toSuccinctType retLst

typeToStr :: Type -> String
typeToStr (BType Int) = "Int"
typeToStr (BType Bool) = "Bool"
typeToStr (BType Char) = "Char"
typeToStr (BType String) = "String"
typeToStr (BType (DT name t)) = name ++ "_" ++ (typeToStr t)
typeToStr (BType (TVar name)) = name
typeToStr (Fun paramTy retTy) = (typeToStr paramTy) ++ "->" ++ (typeToStr retTy)
typeToStr (TypeSet tys) = "LB_"++ (foldl (\acc t -> acc ++ (typeToStr t) ++ "_") "" tys) ++"RB"

succinctToStr :: SuccinctType -> String
succinctToStr (SuccFun tyLst retTy) = "{" ++ (foldl (++) "" (map succinctToStr tyLst)) ++ "}->" ++ (typeToStr retTy)

renameVars :: Type -> Int -> Type
renameVars (BType (TVar name)) n = BType (TVar ("a_" ++ (show n)))
renameVars (Fun paramTy retTy) n = Fun (renameVars paramTy n) (renameVars retTy n)
renameVars (BType (DT name t)) n = BType (DT name (renameVars t n))
renameVars ty _                  = ty

-- substitution
subst :: String -> Type -> Type -> Type
subst target t (BType (TVar name)) = if name == target then t else BType (TVar name)
subst target t (BType (DT name ty)) = BType (DT name (subst target t ty))
subst target t (Fun paramTy retTy) = Fun (subst target t paramTy) (subst target t retTy)
subst target t ty = ty

-- getVars
getVars :: Type -> [String]
getVars (BType (TVar name)) = [name]
getVars (BType (DT name ty)) = removeDups (getVars ty) []
getVars (Fun paramTy retTy) = removeDups ((getVars paramTy) ++ (getVars retTy)) []
getVars _ = []

applyVars :: (String, Type) -> [Type] -> Context
applyVars (pn, t) bases = 
    let vars = getVars t
        cands = foldl (\acc x -> acc ++ (permutations x)) [] (lengthOf (length vars) (subsequences bases))
        pairs = map (\x -> zip vars x) cands
        substAll pair = foldl (\(name, acc) (n,tt) -> (name++"_"++(typeToStr tt), subst n tt acc)) (pn,t) pair
    in if length vars == 0 then [(pn, t)] else map (\x -> substAll x) pairs
-- applyVars (pn, BType (TVar name)) bases = map (\x -> (if pn /= "" then pn ++ "_" ++ (typeToStr x) else (typeToStr x), x)) bases
-- applyVars (pn, BType (DT name t)) bases = let vars = getVars t
--                                               comb = [(n, tt) | n <- vars, tt <- bases]

--                                           in map (\x -> (let suffix = fst x in (
--                                             if suffix == "" 
--                                               then pn 
--                                               else if pn == ""
--                                                      then suffix
--                                                      else pn ++ "_" ++ suffix, BType (DT name (snd x))))) appliedBase
-- applyVars (pn, Fun paramTy retTy) bases = let appliedParam = applyVars ("", paramTy) bases
--                                               appliedRet = applyVars ("", retTy) bases
--                                           in map (\((n1,t1),(n2,t2))->(
--                                             if n1 /= "" && n2 /= ""
--                                               then pn++"_"++n1++"_"++n2 
--                                               else if n1 == "" && n2 /= ""
--                                                      then pn++"_"++n2
--                                                      else if n1 /= "" && n2 == ""
--                                                             then pn++"_"++n1
--                                                             else pn, Fun t1 t2)) (zip appliedParam appliedRet)
-- applyVars ty _                          = [ty]

addCompoundTypes :: (String, SuccinctType) -> [(SuccinctType, Type)]
addCompoundTypes (_, SuccFun paramLst retTy)
    | length paramLst > 1 = [(SuccCom succLst,TypeSet typeLst)]
    | otherwise = []
  where
    typeLst = foldl (\acc x -> acc ++ (getTypes x)) [] paramLst
    succLst = map toSuccinctType typeLst
addCompoundTypes _ = []

getTypes :: SuccinctType -> [Type]
getTypes (SuccFun [] retTy) = [retTy]
getTypes (SuccFun tyLst retTy) = (foldl (\acc t -> acc ++ (getTypes t)) [] tyLst) ++ ([retTy])
getTypes (SuccVar nameLst tyLst) = foldl (\acc t -> acc ++ (getTypes t)) [] tyLst
getTypes (SuccCom tyLst) = let tys = foldl (\acc t -> acc ++ (getTypes t)) [] tyLst
                           in [TypeSet tys]

getBaseTypes :: [Type] -> [Type]
getBaseTypes []       = []
getBaseTypes (ty:tys) = case ty of
    BType (DT _ _) -> getBaseTypes tys
    BType (TVar _) -> getBaseTypes tys
    Fun paramTy retTy -> (getBaseTypes [paramTy]) ++ (getBaseTypes [retTy]) ++ (getBaseTypes tys)
    _              -> ty:(getBaseTypes tys)

toTypeIdx :: [Type] -> [(Type, Int)]
toTypeIdx tys = res
  where
    (_, res) = foldl addNew (0, []) tys
    addNew (cnt, acc) ty = case findPair acc ty of
      Just i -> (cnt, acc)
      Nothing -> (cnt+1, (ty, cnt):acc)

getTypeIdx :: [(Type, Int)] -> Type -> Int
getTypeIdx [] _ = -1
getTypeIdx ((ty, idx):tys) tyFind
  | ty == tyFind = idx
  | otherwise = getTypeIdx tys tyFind

getTypeName :: [(Type, Int)] -> Int -> String
getTypeName [] _ = ""
getTypeName ((ty, idx):tys) tyIdx
  | idx == tyIdx = typeToStr ty
  | otherwise = getTypeName tys tyIdx

instance Eq BaseType where
  Int == Int = True
  Bool == Bool = True
  Char == Char = True
  String == String = True
  DT n1 t1 == DT n2 t2 = (n1==n2) && (t1==t2)
  TVar n1 == TVar n2 = n1==n2
  _ == _ = False

instance Eq Type where
  BType a == BType b = a==b
  Fun a1Ty a2Ty == Fun b1Ty b2Ty = (a1Ty==a2Ty) && (b1Ty==b2Ty)
  TypeSet a == TypeSet b = (sort a)==(sort b)
  _ == _ = False

instance Eq SuccinctType where
  SuccFun aList aTy == SuccFun bList bTy = ((sort aList)==(sort bList)) && (aTy==bTy)
  SuccVar aList aTy == SuccVar bList bTy = ((sort aList)==(sort bList)) && (aTy==bTy)
  SuccCom aList == SuccCom bList = ((sort aList)==(sort bList))
  _ == _ = False

instance Ord BaseType where
  Int <= Bool = True
  Bool <= Int = False
  Int <= Char = True
  Char <= Int = False
  Int <= String = True
  String <= Int = False
  Int <= DT n t = True
  DT n t <= Int = False
  Int <= TVar n = True
  TVar n <= Int = False
  Bool <= Char = True
  Char <= Bool = False
  Bool <= String = True
  String <= Bool = False
  Bool <= DT n t = True
  DT n t <= Bool = False
  Bool <= TVar n = True
  TVar n <= Bool = False
  Char <= String = True
  String <= Char = False
  Char <= DT n t = True
  DT n t <= Char = False
  Char <= TVar n = True
  TVar n <= Char = False
  String <= DT n1 t1 = True
  DT n t <= String = False
  String <= TVar n = True
  TVar n <= String = False
  DT n t <= TVar n1 = True
  TVar n1 <= DT n t = False
  DT n1 t1 <= DT n2 t2 = (n1 <= n2)
  TVar n1 <= TVar n2 = n1<=n2

instance Ord Type where
  BType a <= BType b = a<=b
  Fun a1Ty a2Ty <= Fun b1Ty b2Ty = (a1Ty<=a2Ty) && (b1Ty<=b2Ty)
  TypeSet a <= TypeSet b = a<b

instance Ord SuccinctType where
  SuccFun aList aTy <= SuccFun bList bTy = (aList <= bList) && (aTy <= bTy)
  SuccVar aList aTy <= SuccVar bList bTy = (aList <= bList) && (aTy <= bTy)
  SuccCom aList <= SuccCom bList = (aList <= bList)