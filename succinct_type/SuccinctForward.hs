module SuccinctForward where

import Data.List
import Data.Tuple
import Utility

data BaseType = 
    Int
  | Bool
  | String
  | Char
  | Nil
  | DT String Type
  | TVar String
  deriving(Ord)

data Type = 
    BType BaseType
  | Fun Type Type
  | TypeSet [Type]
  deriving(Ord)

data SuccinctType = 
    SuccCons Type
  | SuccSgl Type
  | SuccFun [SuccinctType] SuccinctType
  | SuccVar [String] [SuccinctType]
  | SuccCom [SuccinctType]
  deriving(Ord)

type Context = [(String, Type)]

hasTVar :: Type -> Bool
hasTVar (BType (TVar _))    = True
hasTVar (BType (DT _ t))    = hasTVar t
hasTVar (BType _)           = False
hasTVar (Fun paramTy retTy) = (hasTVar paramTy) || (hasTVar retTy)

-- | convert data types into succinct ones
-- succinct type has type like set -> retTy
-- types in set have no duplicates
--
toSuccinctType :: Type -> SuccinctType
toSuccinctType (BType bt) = case bt of
    DT name ty -> case toSuccinctType ty of
                    SuccVar names tys -> SuccVar (removeDups (name:names) []) tys
                    SuccFun param ret -> SuccVar [name] (param ++ [ret])
                    SuccCom tys -> SuccVar [name] tys
    _ -> SuccFun [] (SuccSgl (BType bt))
toSuccinctType (Fun paramTy retLst) = case toSuccinctType retLst of
    SuccFun tyLst retTy -> case (elemIndex (toSuccinctType paramTy) tyLst) of
                             Just i  -> SuccFun tyLst retTy
                             Nothing -> SuccFun ((toSuccinctType paramTy):tyLst) retTy
    SuccVar names tys   -> SuccFun [toSuccinctType paramTy] (SuccVar names tys)
    SuccCom tys         -> SuccFun [toSuccinctType paramTy] (SuccCom tys)

addDstDot :: [(String,SuccinctType)] -> [(String,SuccinctType)]
addDstDot [] = []
addDstDot ((n,x):xs) = case x of
    SuccFun [] (SuccSgl t) -> (n++"_value",SuccCons t):((n,x):(addDstDot xs))
    _ -> (n,x):(addDstDot xs)

typeToStr :: Type -> String
typeToStr (BType Int) = "Int"
typeToStr (BType Bool) = "Bool"
typeToStr (BType Char) = "Char"
typeToStr (BType String) = "String"
typeToStr (BType Nil) = ""
typeToStr (BType (DT name t)) = name ++ (if typeToStr t == "" then "" else "_" ++ (typeToStr t))
typeToStr (BType (TVar name)) = name
typeToStr (Fun paramTy retTy) = (typeToStr paramTy) ++ "->" ++ (typeToStr retTy)
typeToStr (TypeSet tys) = "\"{"++ (foldl (\acc t -> acc ++ (typeToStr t) ++ ",") "" tys) ++"}\""

succinctToStr :: SuccinctType -> String
succinctToStr (SuccSgl t) = typeToStr t
succinctToStr (SuccCons t) = "Gotcha"
succinctToStr (SuccFun [] retTy) = succinctToStr retTy
succinctToStr (SuccFun tyLst retTy) = (foldl (\acc x -> acc++x++"_") "" (map succinctToStr tyLst)) ++ "_" ++ (succinctToStr retTy)
succinctToStr (SuccVar names tyLst) = (foldl (\acc x -> acc++x++"_") "" names) ++ (foldl (\acc x -> acc++x++"_") "" (map succinctToStr tyLst))
succinctToStr (SuccCom tyLst) = "\""++(foldl (\acc x -> acc++"+"++x) "" (map succinctToStr tyLst))++"\""

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

addCompoundTypes :: (String, SuccinctType) -> [SuccinctType]
addCompoundTypes (_, SuccFun paramLst retTy)
    | length paramLst > 1 = [SuccCom typeLst]
    | otherwise = []
  where
    typeLst = foldl (\acc x -> acc ++ (getTypes x)) [] paramLst
addCompoundTypes _ = []

getTypes :: SuccinctType -> [SuccinctType]
getTypes (SuccSgl ty) = [SuccSgl ty]
getTypes (SuccCons ty) = [SuccCons ty]
getTypes (SuccFun tyLst retTy) = (foldl (\acc t -> acc ++ (getTypes t)) [] tyLst) ++ (getTypes retTy)
getTypes (SuccVar nameLst tyLst) = [SuccVar nameLst tyLst]
getTypes (SuccCom tyLst) = [SuccCom tyLst] --(foldl (\acc t -> acc ++ (getTypes t)) [] tyLst) ++ 

getBaseTypes :: [Type] -> [Type]
getBaseTypes []       = []
getBaseTypes (ty:tys) = case ty of
    BType (DT _ _) -> if hasTVar ty then  getBaseTypes tys else ty:(getBaseTypes tys)
    BType (TVar _) -> getBaseTypes tys
    Fun paramTy retTy -> (getBaseTypes [paramTy]) ++ (getBaseTypes [retTy]) ++ (getBaseTypes tys)
    _              -> ty:(getBaseTypes tys)

toTypeIdx :: [SuccinctType] -> [(SuccinctType, Int)]
toTypeIdx tys = res
  where
    (_, res) = foldl addNew (0, []) tys
    addNew (cnt, acc) ty = case findPair acc ty of
      Just i -> (cnt, acc)
      Nothing -> (cnt+1, (ty, cnt):acc)

getTypeIdx :: [(SuccinctType, Int)] -> SuccinctType -> Int
getTypeIdx [] _ = -1
getTypeIdx ((ty, idx):tys) tyFind
  | ty == tyFind = idx
  | otherwise = getTypeIdx tys tyFind

getTypeName :: [(SuccinctType, Int)] -> Int -> String
getTypeName [] _ = ""
getTypeName ((ty, idx):tys) tyIdx
  | idx == tyIdx = succinctToStr ty
  | otherwise = getTypeName tys tyIdx

instance Eq BaseType where
  Int == Int = True
  Bool == Bool = True
  Char == Char = True
  String == String = True
  Nil == Nil = True
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
  SuccSgl a == SuccSgl b = (a==b)
  SuccCons a == SuccCons b = (a==b)
  _ == _ = False