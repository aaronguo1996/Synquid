module SuccinctBackward where

import Data.List
import Data.Tuple
import Utility

data Kind = 
    KnStar
  | KnArr Kind Kind

-- Original types
data Ty = 
    TyInt
  | TyBool
  | TyString
  | TyChar
  | TyFloat
  | TyUnit
  | TyTop
  | TyId String
  | TyArr Ty Ty
  | TyAll String Ty
  | TyDt String [Ty]
  deriving(Ord)

data Binding = 
    NameBind
  | VarBind STy
  | TyVarBind
  | TyAbbBind STy
  deriving(Eq)

-- Succinct types
data STy = 
    SRaw Ty
  | SArr [STy] STy
  | SDt [(String,Int)] [STy] -- names, number of dots, types
  | SAll [String] STy 
  | SCmp [STy]
  | SDone String -- nodes for type inhabitation
  deriving(Ord)

type Context = [(String, Binding)]
type SuccCtx = [(String, Binding)]

isNameBound :: SuccCtx -> String -> Bool
isNameBound []         name = False
isNameBound ((n,b):xs) name = if n==name then True else isNameBound xs name

pickFreshName :: SuccCtx -> String -> (Context,String)
pickFreshName ctx name = if isNameBound ctx name
                           then pickFreshName ctx (name++"_")
                           else (((name, NameBind):ctx), name)

-- getNameBound []         name = Nothing
getNameBound :: SuccCtx -> String -> Binding
getNameBound ((n,b):xs) name = if n==name then b else getNameBound xs name

bindIfFree :: SuccCtx -> STy -> SuccCtx
bindIfFree ctx sty = case sty of
    SRaw (TyId id) -> if isNameBound ctx id then [] else [(id, TyVarBind)]
    SRaw t         -> []
    SArr p r       -> let pctx = foldl (\acc x-> acc++(bindIfFree ctx x)) [] p in removeDups ((bindIfFree (ctx++pctx) r)++pctx) []
    SAll ns t      -> let (nctx, ctx) = foldl (\(actx,new) x -> if isNameBound actx x then (actx,new) else ((x,TyVarBind):actx,(x,TyVarBind):new)) (ctx,[]) ns
                      in removeDups (ctx++(bindIfFree nctx t)) []
    SDt ns ts      -> removeDups (foldl (\acc x-> acc++(bindIfFree ctx x)) [] ts) []
    SCmp ts        -> removeDups (foldl (\acc x-> acc++(bindIfFree ctx x)) [] ts) []
    SDone s        -> []

toSuccinctType :: Ty -> STy
toSuccinctType rawTy = case rawTy of
    TyArr t1 t2   -> case toSuccinctType t2 of
                       SArr param ret -> SArr (removeDups ((toSuccinctType t1):param) []) ret
                       ty             -> SArr [(toSuccinctType t1)] ty
    TyDt name tys -> let mergeDt (accName, accTys) t = 
                           case toSuccinctType t of
                             SDt names stys -> (removeDups (accName++names) []
                                               ,removeDups (accTys++stys) [])
                             ty             -> (accName
                                               , removeDups (ty:accTys) [])
                         (resNames, resTys) = foldl mergeDt ([(name, length tys)],[]) tys
                     in SDt resNames resTys
    TyAll name ty -> case toSuccinctType ty of
                       SAll names t -> SAll (removeDups (name:names) []) t
                       t            -> SAll [name] t
    -- TyId id       -> if isNameBound sctx id
    --                    then let (newCtx, newName) = pickFreshName sctx id 
    --                         in SRaw (TyId newName)
    --                    else SRaw ty
    ty            -> SRaw ty

type2str :: Bool -> Ty -> String
type2str outer ty = case ty of
    TyInt           -> "Int"
    TyBool          -> "Bool"
    TyString        -> "String"
    TyChar          -> "Char"
    TyFloat         -> "Float"
    TyUnit          -> "Unit"
    TyTop           -> "Top"
    TyId id         -> id
    TyArr param ret -> concat 
                       [if outer then "" else "("
                       ,type2str False param
                       ,"->"
                       ,type2str False ret
                       ,if outer then "" else ")"
                       ]
    TyAll name t    -> concat
                       [if outer then "" else "("
                       ,"All "
                       ,name
                       ,"."
                       ,type2str False t
                       ,if outer then "" else ")"
                       ]
    TyDt name tys   -> concat
                       ([if outer then "" else "("
                       ,name
                       ," "
                       ] ++ (map (\x->(type2str False x)++" ") tys) 
                       ++ [if outer then "" else ")"])

succinct2str :: STy -> String
succinct2str sty = case sty of
    SRaw t           -> type2str True t
    SArr param retTy -> concat 
                        ["{"
                        ,(foldl (\acc x->acc++(succinct2str x)++",") "" param)
                        ,"}->"
                        ,(succinct2str retTy)
                        ]
    SDt names tys    -> concat
                        ["{"
                        ,(foldl (\acc (x,n)->acc++x++(replicate n '*')++",") "" names)
                        ," | "
                        ,(foldl (\acc x->acc++(succinct2str x)++",") "" tys)
                        ,"}"
                        ]
    SAll names ty    -> concat
                        ["All {"
                        ,(foldl (\acc x->acc++x++",") "" names)
                        ,"}. "
                        ,(succinct2str ty)
                        ]
    SCmp tys         -> concat
                        ["{"
                        ,(foldl (\acc x->acc++(succinct2str x)++",") "" tys)
                        ,"}"
                        ]
    SDone s          -> ""


subst :: String -> String -> Ty -> Ty
subst oldName newName ty = case ty of
    TyId id    -> if id==oldName then TyId newName else ty
    TyArr p r  -> TyArr (subst oldName newName p) (subst oldName newName r)
    TyAll n t  -> if n==oldName 
                    then TyAll newName (subst oldName newName t)
                    else TyAll n (subst oldName newName t)
    TyDt n t   -> TyDt n (map (subst oldName newName) t)
    _          -> ty

isTypeEq :: Ty -> Ty -> Bool
isTypeEq ty1 ty2 = case (ty1, ty2) of
    (TyInt, TyInt)             -> True
    (TyBool, TyBool)           -> True
    (TyString, TyString)       -> True
    (TyChar, TyChar)           -> True
    (TyFloat, TyFloat)         -> True
    (TyUnit, TyUnit)           -> True
    (TyTop, TyTop)             -> True
    (TyId id1, TyId id2)       -> id1==id2
    (TyArr p1 r1, TyArr p2 r2) -> (isTypeEq p1 p2) && (isTypeEq r1 r2)
    (TyAll n1 t1, TyAll n2 t2) -> let fresht2 = subst n2 n1 t2 
                                  in isTypeEq t1 fresht2
    (TyDt n1 tl1, TyDt n2 tl2) -> let f acc (x,y) = acc && (isTypeEq x y)
                                      lenCmp = (length tl1)==(length tl2)
                                      stl1 = sort tl1
                                      stl2 = sort tl2
                                      lstCmp = foldl f True (zip stl1 stl2)
                                  in (n1==n2) && lenCmp && lstCmp
    (_,_)                      -> False

isSTypeEq :: STy -> STy -> Bool
isSTypeEq sty1 sty2 = case (sty1, sty2) of
    (SRaw t1   , SRaw t2)    -> isTypeEq t1 t2
    (SArr p1 r1, SArr p2 r2) -> let f acc (x,y) = acc && (isSTypeEq x y)
                                    lenCmp = (length p1)==(length p2)
                                    sp1 = sort p1
                                    sp2 = sort p2
                                    paramCmp = foldl f True (zip sp1 sp2)
                                    retCmp = (isSTypeEq r1 r2)
                                in lenCmp && paramCmp && retCmp
    (SAll n1 t1, SAll n2 t2) -> let sn1 = sort n1
                                    sn2 = sort n2
                                in (sn1==sn2) && (isSTypeEq t1 t2)
    (SDt n1 t1 , SDt n2 t2)  -> let sn1 = sort n1
                                    sn2 = sort n2
                                    st1 = sort t1
                                    st2 = sort t2
                                in (sn1==sn2) && (st1==st2)
    (SCmp t1   , SCmp t2)    -> let st1 = sort t1
                                    st2 = sort t2
                                in st1==st2
    (SDone s1  , SDone s2)   -> s1==s2
    (_         , _)          -> False

refineSuccinct :: STy -> STy
refineSuccinct sty = case sty of
    SRaw t   -> SRaw t
    SArr p r -> SArr (map refineSuccinct p) (refineSuccinct r)
    SAll n t -> let tt = refineSuccinct t in case tt of
                  SAll nn ts -> SAll (removeDups (n++nn) []) ts
                  _          -> SAll n tt
    SDt n t  -> let tt = map refineSuccinct t 
                    fold_fun (accn,acct) x = case x of 
                      SDt nn ts -> (accn++nn, acct++ts)
                      _         -> (accn, x:acct) 
                    (names, tys) = foldl fold_fun (n, []) tt
                in SDt (removeDups names []) (removeDups tys [])
    SCmp t   -> SCmp (map refineSuccinct t)
    SDone s  -> sty

substs :: String -> STy -> STy -> STy
substs name sty oldSty = case oldSty of
    SRaw (TyId id) -> if name == id then sty else oldSty
    SRaw t         -> SRaw t 
    SArr p r       -> refineSuccinct (SArr (map (substs name sty) p) (substs name sty r))
    SAll n t       -> case elemIndex name n of
                        Just i  -> refineSuccinct (SAll (delete name n) (substs name sty t))
                        Nothing -> refineSuccinct (SAll n (substs name sty t))
    SDt n t        -> refineSuccinct (SDt n (map (substs name sty) t))
    SCmp t         -> refineSuccinct (SCmp (map (substs name sty) t))

changeName :: String -> String -> STy -> STy
changeName oldName newName sty = case sty of
    SRaw t   -> SRaw (subst oldName newName t)
    SArr p r -> SArr (map (changeName oldName newName) p) (changeName oldName newName r)
    SAll n t -> case elemIndex oldName n of
                  Just i  -> SAll (newName:(delete oldName n)) (changeName oldName newName t)
                  Nothing -> SAll n (changeName oldName newName t)
    SDt n t  -> SDt n (map (changeName oldName newName) t)
    SCmp t   -> SCmp (map (changeName oldName newName) t)

unify :: STy -> STy -> SuccCtx -> (Bool,[SuccCtx])
unify comp target ctx = case (comp, target) of
    (SRaw (TyId id),target) -> (True, [[(id, TyAbbBind target)]])
    (SRaw t1, SRaw t2)      -> if isTypeEq t1 t2 then (True, [[("", TyAbbBind target)]]) else (False, [])
    (SDt n1 t1, SDt n2 t2)  -> let sn1 = sort n1
                                   sn2 = sort n2
                               in if isSubsequenceOf sn1 sn2
                                    then let getBnd acc x = case x of
                                                              SRaw (TyId id) -> if isNameBound ctx id then x:acc else acc
                                                              _              -> x:acc
                                             bound1 = foldl getBnd [] (sort t1)
                                             bound2 = foldl getBnd [] (sort t2)
                                         in if isSubsequenceOf bound1 bound2
                                              then let consDiff = sn2 \\ sn1
                                                       tysDiff = bound2 \\ bound1
                                                   in allPoss consDiff tysDiff ((sort t1) \\ bound1) (intersect sn1 sn2) (intersect bound1 bound2)
                                              else (False, [])
                                    else (False, [])
    _                       -> (False, [])
  where
    allPoss cons tys freeVars tcons tty = if (length cons /= 0 || length tys /= 0) && (length freeVars == 0) -- no freeVars to fill
                                            then (False, [])
                                            else let mustTys = divideDup (length freeVars) tys
                                                     fold_fun acc elem = acc++(divide (length freeVars) elem)
                                                     mustCons = foldl fold_fun [] (permutations cons)
                                                     opt_fun acc elem = acc++(divideOpt (length freeVars) elem)
                                                     optionalTys = foldl opt_fun [] (permutations tty)
                                                     optionalCons = foldl opt_fun [] (permutations tcons)
                                                     connect x y = map (\(a,b)-> a++b) (zip x y)
                                                     finalTys = [connect x y | x<-mustTys, y<-optionalTys]
                                                     finalCons = [connect x y | x<-mustCons, y<-optionalCons]
                                                     assign vars x y = case (vars, x,y) of
                                                                         ([], [], [])                         -> []
                                                                         ((SRaw (TyId var)):vs, xx:xs, yy:ys) -> case xx of
                                                                             [] | length yy > 0 -> (var, TyAbbBind (head yy)):(assign vs xs ys)
                                                                                | otherwise     -> []
                                                                             _  -> (var, TyAbbBind (SDt xx yy)):(assign vs xs ys)
                                                                         _                                    -> []
                                                     isValid x y = case (x,y) of
                                                                     ([],[])    -> True
                                                                     ([],[y])   -> True
                                                                     (xx:xs, _) -> let cnt = foldl (\acc (_,n)->if n>acc then n else acc) 0 x
                                                                                       len = (length y) + (foldl (\acc (_,n)->if n==0 then acc+1 else acc) 0 x)
                                                                                   in (cnt > 1 && len >= 1) || (cnt == 0 && (len == 0 || len == 1)) || (cnt == 1 && len == 1)
                                                                     _          -> False
                                                 in (True, [assign freeVars c t | c <- finalCons,
                                                                                  t <- finalTys,
                                                                                  (foldl (\acc (x,y) -> acc && (isValid x y)) True (zip c t))])

rootTypeOf :: SuccCtx -> STy -> [(String,STy)]
rootTypeOf []     sty = []
rootTypeOf (x:xs) sty = let ctx = (x:xs)
                            (n, t) = x 
                        in case t of
    -- VarBind (SRaw (TyId id))   -> let (_,nid) = pickFreshName ctx id
    --                               in ([(id,TyVarBind nid),(nid,TyAbbBind sty)], x:res)
    VarBind (SRaw t1)          -> case sty of
                                    SRaw t2 -> if isTypeEq t1 t2 then ((n, SDone n):res) else res
                                    _       -> res
    VarBind (SDone s1)         -> if isSTypeEq (SDone s1) sty then ((n, SDone n):res) else res
    VarBind (SArr param retTy) -> if isSTypeEq retTy sty 
                                    then if length param == 1
                                           then (n, head param):res 
                                           else (n, SCmp param):res
                                    else res
    VarBind (SDt names tys)    -> if isSTypeEq (SDt names tys) sty then ((n, SDone n):res) else res
    VarBind (SAll names ty)    -> let (_,newNames) = foldl (\(lctx,acc) x -> let (nctx, name) = pickFreshName lctx x in (nctx,acc++[name])) (ctx,[]) names
                                      newTy = foldl (\acc (x,y) -> if x/=y then changeName x y acc else acc) ty (zip names newNames)
                                  in case newTy of 
                                    SArr param tty -> let (unified, nctx) = unify tty sty ctx
                                                          fold_fun acc x = case x of
                                                                             (n, TyAbbBind ty) -> substs n ty acc
                                                                             _                 -> acc
                                                      in if unified 
                                                           then let newParam localctx = map (\tt -> foldl fold_fun tt localctx) param
                                                                in foldl (\acc lctx -> let np = newParam lctx in (if length np == 1 then (n, head np) else (n, SCmp np)):acc) res nctx
                                                           else res
                                    _              -> let (unified, nctx) = unify newTy sty ctx
                                                      --in (foldl (\acc tx -> acc++(map (\(_,TyAbbBind tt) -> (n,tt)) tx)) [] nctx) ++ res
                                                      in if unified then [(n, SDone n)] ++ res else res
    _                          -> res
  where
    res = rootTypeOf xs sty

hasSeen :: [STy] -> STy -> Bool
hasSeen tys t = case elemIndex t tys of
    Just _  -> True
    Nothing -> False

traversal :: SuccCtx -> [STy] -> STy -> [(STy,String,STy)]
traversal sctx seen sty = case sty of
    SCmp tys -> let (want, _) = foldl (\(acc,s) x->(acc++(if hasSeen s x then [] else traversal sctx (x:s) x),x:s)) (res,seen) tys 
                    cmpEdges = map (\t -> (sty,"",t)) tys
                in want++cmpEdges
    SDone s  -> []
    _        -> res ++ case leaves of
                  [] -> []
                  _  -> let (want, _) = foldl (\(acc,s) (n,x)->
                                                (acc ++ (if (hasSeen s x) || (isSTypeEq x sty) 
                                                           then [] 
                                                           else traversal sctx (x:s) x), x:s)) ([],seen) leaves
                        in want
  where
    leaves = case sty of
               SAll names ty -> let newCtx = map (\x->(x,TyVarBind)) names in (rootTypeOf (sctx++newCtx) ty)
               SCmp tys      -> []
               _             -> rootTypeOf (sctx++(bindIfFree sctx sty)) sty
    res = map (\(n,t)->(sty,n,t)) leaves

isReachable :: [(STy,String,STy)] -> [STy] -> STy -> Bool
isReachable []    _    _  = False
isReachable edges seen ty = case ty of
    SDone _  -> True
    SCmp tys -> foldl (\acc x -> (acc && isReachable edges (x:seen) x)) True (getDsts seen ty)
    _        -> foldl (\acc x -> (acc || isReachable edges (x:seen) x)) False (getDsts seen ty)
  where 
    getDsts seen t = let fold_fun (acc, s) (from,_,to) = 
                             if (from == t) && (not (hasSeen s to))
                                 then (to:acc, t:s)
                                 else (acc, s)
                         (res,_) = foldl fold_fun ([],seen) edges
                      in res

prune :: [(STy, String, STy)] -> [STy] -> [(STy, String, STy)]
prune edges unreach = let
    filter_fun (from,_,to) = 
        case elemIndex from unreach of
            Just i  -> False
            Nothing -> case elemIndex to unreach of
                           Just j  -> False
                           Nothing -> True
    in filter filter_fun edges

-- utility functions
toTypeIndices :: (Eq a) => [a] -> [(Int, a)]
toTypeIndices tys = let 
    fold_fun (accLst, curr) x = case elemIndex x (snd (unzip accLst)) of
        Just _  -> (accLst, curr)
        Nothing -> ((curr,x):accLst, curr+1)
    (res, _) = foldl fold_fun ([],0) tys
    in res

getTypeIndex :: (Eq a) => [(Int, a)] -> a -> Int
getTypeIndex []         ty = -1
getTypeIndex ((i,t):xs) ty = if t == ty then i else getTypeIndex xs ty

getTypeByIndex :: [(Int, STy)] -> Int -> STy
getTypeByIndex []          _  = SDone ""
getTypeByIndex ((i,t):xs) idx = if i == idx then t else getTypeByIndex xs idx

getUniqueSet :: (Eq a) => [(a, b, a)] -> [a]
getUniqueSet [] = []
getUniqueSet ((x,_,y):xs) = removeDups (x:(y:(getUniqueSet xs))) []

getTypeName :: [(Int, STy)] -> Int -> String
getTypeName indices idx = "\"" ++ (succinct2str (getTypeByIndex indices idx)) ++ "\""

instance Eq Ty where
    a == b = isTypeEq a b

instance Eq STy where
    a == b = isSTypeEq a b