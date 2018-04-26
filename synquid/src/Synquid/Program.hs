{-# LANGUAGE TemplateHaskell, DeriveFunctor #-}

-- | Executable programs
module Synquid.Program where

import Synquid.Logic
import Synquid.Type as Type
import Synquid.Tokens
import Synquid.Util
import Synquid.Error
import Synquid.Succinct

import Data.Maybe
import Data.Either
import Data.List as List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad
import Control.Lens as Lens
import Debug.Trace

{- Program terms -}

-- | One case inside a pattern match expression
data Case t = Case {
  constructor :: Id,      -- ^ Constructor name
  argNames :: [Id],       -- ^ Bindings for constructor arguments
  expr :: Program t       -- ^ Result of the match in this case
} deriving (Show, Eq, Ord, Functor)

-- | Program skeletons parametrized by information stored symbols, conditionals, and by node types
data BareProgram t =
  PSymbol Id |                                -- ^ Symbol (variable or constant)
  PApp (Program t) (Program t) |              -- ^ Function application
  PFun Id (Program t) |                       -- ^ Lambda abstraction
  PIf (Program t) (Program t) (Program t) |   -- ^ Conditional
  PMatch (Program t) [Case t] |               -- ^ Pattern match on datatypes
  PFix [Id] (Program t) |                     -- ^ Fixpoint
  PLet Id (Program t) (Program t) |           -- ^ Let binding
  PHole |                                     -- ^ Hole (program to fill in)
  PErr                                        -- ^ Error
  deriving (Show, Eq, Ord, Functor)

-- | Programs annotated with types
data Program t = Program {
  content :: BareProgram t,
  typeOf :: t
} deriving (Show, Functor)

instance Eq (Program t) where
  (==) (Program l _) (Program r _) = l == r

instance Ord (Program t) where
  (<=) (Program l _) (Program r _) = l <= r

-- | Untyped programs
type UProgram = Program RType
-- | Refinement-typed programs
type RProgram = Program RType

untyped c = Program c AnyT
uHole = untyped PHole
isHole (Program PHole _) = True
isHole _ = False

eraseTypes :: RProgram -> UProgram
eraseTypes = fmap (const AnyT)

symbolName (Program (PSymbol name) _) = name
symbolList (Program (PSymbol name) _) = [name]
symbolList (Program (PApp fun arg) _) = symbolList fun ++ symbolList arg

symbolsOf (Program p _) = case p of
  PSymbol name -> Set.singleton name
  PApp fun arg -> symbolsOf fun `Set.union` symbolsOf arg
  PFun x body -> symbolsOf body
  PIf cond thn els -> symbolsOf cond `Set.union` symbolsOf thn `Set.union` symbolsOf els
  PMatch scr cases -> symbolsOf scr `Set.union` Set.unions (map (symbolsOf . expr) cases)
  PFix x body -> symbolsOf body
  PLet x def body -> symbolsOf def `Set.union` symbolsOf body
  _ -> Set.empty

errorProgram = Program PErr (vart dontCare ftrue)
isError (Program PErr _) = True
isError _ = False

-- | Substitute a symbol for a subterm in a program
programSubstituteSymbol :: Id -> RProgram -> RProgram -> RProgram
programSubstituteSymbol name subterm (Program p t) = Program (programSubstituteSymbol' p) t
  where
    pss = programSubstituteSymbol name subterm

    programSubstituteSymbol' (PSymbol x) = if x == name then content subterm else p
    programSubstituteSymbol' (PApp fun arg) = PApp (pss fun) (pss arg)
    programSubstituteSymbol' (PFun name pBody) = PFun name (pss pBody)
    programSubstituteSymbol' (PIf c p1 p2) = PIf (pss c) (pss p1) (pss p2)
    programSubstituteSymbol' (PMatch scr cases) = PMatch (pss scr) (map (\(Case ctr args pBody) -> Case ctr args (pss pBody)) cases)
    programSubstituteSymbol' (PFix args pBody) = PFix args (pss pBody)
    programSubstituteSymbol' (PLet x pDef pBody) = PLet x (pss pDef) (pss pBody)

-- | Convert an executable formula into a program
fmlToProgram :: Formula -> RProgram
fmlToProgram (BoolLit b) = Program (PSymbol $ show b) (ScalarT BoolT $ valBool |=| BoolLit b)
fmlToProgram (IntLit i) = Program (PSymbol $ show i) (ScalarT IntT $ valInt |=| IntLit i)
fmlToProgram (Var s x) = Program (PSymbol x) (addRefinement (fromSort s) (varRefinement x s))
fmlToProgram fml@(Unary op e) = let
    s = sortOf fml
    p = fmlToProgram e
    fun = Program (PSymbol $ unOpTokens Map.! op) (FunctionT "x" (typeOf p) opRes)
  in Program (PApp fun p) (addRefinement (fromSort s) (Var s valueVarName |=| fml))
  where
    opRes
      | op == Not = bool $ valBool |=| fnot (intVar "x")
      | otherwise = int $ valInt |=| Unary op (intVar "x")
fmlToProgram fml@(Binary op e1 e2) = let
    s = sortOf fml
    p1 = fmlToProgram e1
    p2 = fmlToProgram e2
    fun1 = Program (PSymbol $ binOpTokens Map.! op) (FunctionT "x" (typeOf p1) (FunctionT "y" (typeOf p2) opRes))
    fun2 = Program (PApp fun1 p1) (FunctionT "y" (typeOf p2) opRes)
  in Program (PApp fun2 p2) (addRefinement (fromSort s) (Var s valueVarName |=| fml))
  where
    opRes
      | op == Times || op == Times || op == Times = int $ valInt |=| Binary op (intVar "x") (intVar "y")
      | otherwise                                 = bool $ valBool |=| Binary op (intVar "x") (intVar "y")
fmlToProgram fml@(Pred s x (f:fs)) = Program (PApp fn (curriedApp (fmlToProgram f) fs)) AnyT --(addRefinement (fromSort s) (varRefinement x s))
  where
    fn = Program (PSymbol x) (FunctionT x AnyT AnyT {-(fromSort s)-})
    curriedApp :: RProgram -> [Formula] -> RProgram
    curriedApp p [] = p
    curriedApp p (f:fs) = curriedApp (Program (PApp p (fmlToProgram f)) AnyT {-fromSort s -}) fs

-- | Convert an executable formula into an untyped program
fmlToUProgram :: Formula -> RProgram
fmlToUProgram (BoolLit b) = Program (PSymbol $ show b) AnyT
fmlToUProgram (IntLit i) = Program (PSymbol $ show i) AnyT
fmlToUProgram (Var s x) = Program (PSymbol x) AnyT
fmlToUProgram fml@(Unary op e) = let
    p = fmlToUProgram e
    fun = Program (PSymbol $ unOpTokens Map.! op) AnyT
  in Program (PApp fun p) AnyT
fmlToUProgram fml@(Binary op e1 e2) = let
    p1 = fmlToUProgram e1
    p2 = fmlToUProgram e2
    fun1 = Program (PSymbol $ binOpTokens Map.! op) AnyT
    fun2 = Program (PApp fun1 p1) AnyT
  in Program (PApp fun2 p2) AnyT
fmlToUProgram fml@(Pred _ x (f:fs)) = Program (PApp fn (curriedApp (fmlToUProgram f) fs)) AnyT
  where
    fn = Program (PSymbol x) AnyT
    curriedApp :: RProgram -> [Formula] -> RProgram
    curriedApp p [] = p
    curriedApp p (f:fs) = curriedApp (Program (PApp p (fmlToUProgram f)) AnyT) fs
fmlToUProgram (Ite gf f1 f2) = Program (PIf gp p1 p2) AnyT
  where
    gp = fmlToUProgram gf
    p1 = fmlToUProgram f1
    p2 = fmlToUProgram f2
fmlToUProgram (Cons _ x (f:fs)) = Program (PApp fn (curriedApp (fmlToUProgram f) fs)) AnyT
  where
    fn = Program (PSymbol x) AnyT
    curriedApp :: RProgram -> [Formula] -> RProgram
    curriedApp p [] = p
    curriedApp p (f:fs) = curriedApp (Program (PApp p (fmlToUProgram f)) AnyT) fs
fmlToUProgram (SetLit _ [])     = Program (PSymbol emptySetCtor) AnyT
fmlToUProgram (SetLit _ [f])     = Program (PApp (Program (PSymbol singletonCtor) AnyT) (fmlToUProgram f)) AnyT
fmlToUProgram (SetLit _ (f:fs)) = Program (PApp ins (curriedApp (fmlToUProgram f) fs)) AnyT
  where
    ins = Program (PSymbol insertSetCtor) AnyT
    emp = Program (PSymbol emptySetCtor) AnyT
    curriedApp :: RProgram -> [Formula] -> RProgram
    curriedApp p [] = Program (PApp p emp) AnyT
    curriedApp p (f:fs) = curriedApp (Program (PApp p (fmlToUProgram f)) AnyT) fs

-- | 'renameAsImpl' @p t@: change argument names in function type @t@ to be the same as in the abstraction @p@
renameAsImpl :: (Id -> Bool) -> UProgram -> RType -> RType
renameAsImpl isBound = renameAsImpl' Map.empty
  where
    renameAsImpl' subst (Program (PFun y pRes) _) (FunctionT x tArg tRes) = case tArg of
      ScalarT baseT fml -> FunctionT y (substituteInType isBound subst tArg) (renameAsImpl' (Map.insert x (Var (toSort baseT) y) subst) pRes tRes)
      _ -> FunctionT y (substituteInType isBound subst tArg) (renameAsImpl' subst pRes tRes)
    renameAsImpl' subst  _ t = substituteInType isBound subst t

{- Top-level definitions -}

-- | User-defined datatype representation
data DatatypeDef = DatatypeDef {
  _typeParams :: [Id],              -- ^ Type parameters
  _predParams :: [PredSig],         -- ^ Signatures of predicate parameters
  _predVariances :: [Bool],         -- ^ For each predicate parameter, whether it is contravariant
  _constructors :: [Id],            -- ^ Constructor names
  _wfMetric :: Maybe Id             -- ^ Name of the measure that serves as well founded termination metric
} deriving (Show, Eq, Ord)

makeLenses ''DatatypeDef

-- | One case in a measure definition: constructor name, arguments, and body
data MeasureCase = MeasureCase Id [Id] Formula
  deriving (Show, Eq, Ord)

-- | User-defined measure function representation
data MeasureDef = MeasureDef {
  _inSort :: Sort,
  _outSort :: Sort,
  _definitions :: [MeasureCase],
  _postcondition :: Formula
} deriving (Show, Eq, Ord)

makeLenses ''MeasureDef

{- Evaluation environment -}

-- | Typing environment
data Environment = Environment {
  -- | Variable part:
  _symbols :: Map Int (Map Id RSchema),    -- ^ Variables and constants (with their refinement types), indexed by arity
  _succinctSymbols :: Map Id RSuccinctType,    -- ^ Symbols with succinct types
  _succinctGraph :: Map RSuccinctType (Map RSuccinctType (Set Id)), -- ^ Graph built upon succinct types
  _undecidableSymbols :: Set (RSuccinctType, RSuccinctType, Id), -- ^ the going to type has some variable in it to be decided until the graph is built
  _reachableSymbols :: Set RSuccinctType, -- ^ reachable symbols in the succinct graph
  _boundTypeVars :: [Id],                  -- ^ Bound type variables
  _boundPredicates :: [PredSig],           -- ^ Argument sorts of bound abstract refinements
  _assumptions :: Set Formula,             -- ^ Unknown assumptions
  _shapeConstraints :: Map Id SType,       -- ^ For polymorphic recursive calls, the shape their types must have
  _usedScrutinees :: [RProgram],           -- ^ Program terms that has already been scrutinized
  _unfoldedVars :: Set Id,                 -- ^ In eager match mode, datatype variables that can be scrutinized
  _letBound :: Set Id,                     -- ^ Subset of symbols that are let-bound
  -- | Constant part:
  _constants :: Set Id,                    -- ^ Subset of symbols that are constants
  _datatypes :: Map Id DatatypeDef,        -- ^ Datatype definitions
  _globalPredicates :: Map Id [Sort],      -- ^ Signatures (resSort:argSorts) of module-level logic functions (measures, predicates)
  _measures :: Map Id MeasureDef,          -- ^ Measure definitions
  _typeSynonyms :: Map Id ([Id], RType),   -- ^ Type synonym definitions
  _unresolvedConstants :: Map Id RSchema   -- ^ Unresolved types of components (used for reporting specifications with macros)
} deriving (Show)

makeLenses ''Environment

instance Eq Environment where
  (==) e1 e2 = (e1 ^. symbols) == (e2 ^. symbols) && (e1 ^. assumptions) == (e2 ^. assumptions)

instance Ord Environment where
  (<=) e1 e2 = (e1 ^. symbols) <= (e2 ^. symbols) && (e1 ^. assumptions) <= (e2 ^. assumptions)

-- | Empty environment
emptyEnv = Environment {
  _symbols = Map.empty,
  _succinctSymbols = Map.empty,
  _succinctGraph = Map.empty,
  _undecidableSymbols = Set.empty,
  _reachableSymbols = Set.empty,
  _boundTypeVars = [],
  _boundPredicates = [],
  _assumptions = Set.empty,
  _shapeConstraints = Map.empty,
  _usedScrutinees = [],
  _unfoldedVars = Set.empty,
  _letBound = Set.empty,
  _constants = Set.empty,
  _globalPredicates = Map.empty,
  _datatypes = Map.empty,
  _measures = Map.empty,
  _typeSynonyms = Map.empty,
  _unresolvedConstants = Map.empty
}

-- | 'symbolsOfArity' @n env@: all symbols of arity @n@ in @env@
symbolsOfArity n env = Map.findWithDefault Map.empty n (env ^. symbols)

-- | All symbols in an environment
allSymbols :: Environment -> Map Id RSchema
allSymbols env = Map.unions $ Map.elems (env ^. symbols)

-- | 'lookupSymbol' @name env@ : type of symbol @name@ in @env@, including built-in constants
lookupSymbol :: Id -> Int -> Bool -> Environment -> Maybe RSchema
lookupSymbol name a hasSet env
  | a == 0 && name == "True"                          = Just $ Monotype $ ScalarT BoolT valBool
  | a == 0 && name == "False"                         = Just $ Monotype $ ScalarT BoolT (fnot valBool)
  | a == 0 && isJust asInt                            = Just $ Monotype $ ScalarT IntT (valInt |=| IntLit (fromJust asInt))
  | a == 1 && (name `elem` Map.elems unOpTokens)      = let op = head $ Map.keys $ Map.filter (== name) unOpTokens in Just $ unOpType op
  | isBinary && hasSet                                = let ops = Map.keys $ Map.filter (== name) binOpTokens
    in Just $ binOpType $ case tail ops of
        [] -> head ops
        _  -> head $ tail ops -- To account for set operator overloading
  | isBinary                                          = let op = head $ Map.keys $ Map.filter (== name) binOpTokens in Just $ binOpType op
  | otherwise                                         = Map.lookup name (allSymbols env)
  where
    isBinary = a == 2 && (name `elem` Map.elems binOpTokens)
    asInt = asInteger name

symbolAsFormula :: Environment -> Id -> RType -> Formula
symbolAsFormula _ name t | arity t > 0
                      = error $ unwords ["symbolAsFormula: not a scalar symbol", name]
symbolAsFormula env name t
  | name == "True"    = BoolLit True
  | name == "False"   = BoolLit False
  | isJust asInt      = IntLit (fromJust asInt)
  | isConstructor     = Cons sort name []
  | otherwise         = Var sort name
  where
    isConstructor = isJust (lookupConstructor name env)
    sort = toSort (baseTypeOf t)
    asInt = asInteger name

unOpType Neg       = Monotype $ FunctionT "x" intAll (int (valInt |=| fneg (intVar "x")))
unOpType Not       = Monotype $ FunctionT "x" boolAll (bool (valBool |=| fnot (boolVar "x")))
binOpType Times     = Monotype $ FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |*| intVar "y")))
binOpType Plus      = Monotype $ FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |+| intVar "y")))
binOpType Minus     = Monotype $ FunctionT "x" intAll (FunctionT "y" intAll (int (valInt |=| intVar "x" |-| intVar "y")))
binOpType Eq        = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |=| vartVar "a" "y"))))
binOpType Neq       = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |/=| vartVar "a" "y"))))
binOpType Lt        = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |<| vartVar "a" "y"))))
binOpType Le        = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |<=| vartVar "a" "y"))))
binOpType Gt        = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |>| vartVar "a" "y"))))
binOpType Ge        = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (vartAll "a") (bool (valBool |=| (vartVar "a" "x" |>=| vartVar "a" "y"))))
binOpType And       = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" |&| boolVar "y"))))
binOpType Or        = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" ||| boolVar "y"))))
binOpType Implies   = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" |=>| boolVar "y"))))
binOpType Iff       = Monotype $ FunctionT "x" boolAll (FunctionT "y" boolAll (bool (valBool |=| (boolVar "x" |<=>| boolVar "y"))))
binOpType Union     = ForallT "a" $ Monotype $ FunctionT "x" (setAll "a") (FunctionT "y" (setAll "a") (Type.set "a" (valSet "a" |=| setVar "a" "x" /+/ setVar "a" "y")))
binOpType Intersect = ForallT "a" $ Monotype $ FunctionT "x" (setAll "a") (FunctionT "y" (setAll "a") (Type.set "a" (valSet "a" |=| setVar "a" "x" /*/ setVar "a" "y")))
binOpType Diff      = ForallT "a" $ Monotype $ FunctionT "x" (setAll "a") (FunctionT "y" (setAll "a") (Type.set "a" (valSet "a" |=| setVar "a" "x" /-/ setVar "a" "y")))
binOpType Member    = ForallT "a" $ Monotype $ FunctionT "x" (vartAll "a") (FunctionT "y" (setAll "a") (bool (valBool |=| vartVar "a" "x" `fin` setVar "a" "y")))
binOpType Subset    = ForallT "a" $ Monotype $ FunctionT "x" (setAll "a") (FunctionT "y" (setAll "a") (bool (valBool |=| setVar "a" "x" /<=/ setVar "a" "y")))

-- | Is @name@ a constant in @env@ including built-in constants)?
isConstant name env = (name `elem` ["True", "False"]) ||
                      isJust (asInteger name) ||
                      (name `elem` Map.elems unOpTokens) ||
                      (name `elem` Map.elems binOpTokens) ||
                      (name `Set.member` (env ^. constants))

-- | 'isBound' @tv env@: is type variable @tv@ bound in @env@?
isBound :: Environment -> Id -> Bool
isBound env tv = tv `elem` env ^. boundTypeVars

addVariable :: Id -> RType -> Environment -> Environment
addVariable name t env = addPolyVariable name (Monotype t) env

addPolyVariable :: Id -> RSchema -> Environment -> Environment
addPolyVariable name sch env =  let 
  n  = arity (toMonotype sch) 
  env' = addSuccinctSymbol name sch env
  in (symbols %~ Map.insertWith Map.union n (Map.singleton name sch)) env'

-- | 'addConstant' @name t env@ : add type binding @name@ :: Monotype @t@ to @env@
addConstant :: Id -> RType -> Environment -> Environment
addConstant name t = addPolyConstant name (Monotype t)

-- | 'addPolyConstant' @name sch env@ : add type binding @name@ :: @sch@ to @env@
addPolyConstant :: Id -> RSchema -> Environment -> Environment
addPolyConstant name sch = addPolyVariable name sch . (constants %~ Set.insert name)

addLetBound :: Id -> RType -> Environment -> Environment
addLetBound name t = addVariable name t . (letBound %~ Set.insert name)

addUnresolvedConstant :: Id -> RSchema -> Environment -> Environment
addUnresolvedConstant name sch = unresolvedConstants %~ Map.insert name sch

removeVariable :: Id -> Environment -> Environment
removeVariable name env = case Map.lookup name (allSymbols env) of
  Nothing -> env
  Just sch -> over symbols (Map.insertWith (flip Map.difference) (arity $ toMonotype sch) (Map.singleton name sch)) . over constants (Set.delete name) $ env

embedContext :: Environment -> RType -> (Environment, RType)
embedContext env (LetT x tDef tBody) =
  let
    (env', tDef') = embedContext (removeVariable x env) tDef
    (env'', tBody') = embedContext env' tBody
  in (addLetBound x tDef' env'', tBody')
-- TODO: function?
embedContext env t = (env, t)

unfoldAllVariables env = over unfoldedVars (Set.union (Map.keysSet (symbolsOfArity 0 env) Set.\\ (env ^. constants))) env

addMeasure :: Id -> MeasureDef -> Environment -> Environment
addMeasure measureName m = over measures (Map.insert measureName m)

addBoundPredicate :: PredSig -> Environment -> Environment
addBoundPredicate sig = over boundPredicates (sig :)

addGlobalPredicate :: Id -> Sort -> [Sort] -> Environment -> Environment
addGlobalPredicate predName resSort argSorts = over globalPredicates (Map.insert predName (resSort : argSorts))

addTypeSynonym :: Id -> [Id] -> RType -> Environment -> Environment
addTypeSynonym name tvs t = over typeSynonyms (Map.insert name (tvs, t))

-- | 'addDatatype' @name env@ : add datatype @name@ to the environment
addDatatype :: Id -> DatatypeDef -> Environment -> Environment
addDatatype name dt = over datatypes (Map.insert name dt)

-- | 'lookupConstructor' @ctor env@ : the name of the datatype for which @ctor@ is registered as a constructor in @env@, if any
lookupConstructor :: Id -> Environment -> Maybe Id
lookupConstructor ctor env = let m = Map.filter (\dt -> ctor `elem` dt ^. constructors) (env ^. datatypes)
  in if Map.null m
      then Nothing
      else Just $ fst $ Map.findMin m

-- | 'addTypeVar' @a@ : Add bound type variable @a@ to the environment
addTypeVar :: Id -> Environment -> Environment
addTypeVar a = over boundTypeVars (a :)

-- | 'addAssumption' @f env@ : @env@ with extra assumption @f@
addAssumption :: Formula -> Environment -> Environment
addAssumption f = assumptions %~ Set.insert f

-- | 'addScrutinee' @p env@ : @env@ with @p@ marked as having been scrutinized already
addScrutinee :: RProgram -> Environment -> Environment
addScrutinee p = usedScrutinees %~ (p :)

allPredicates env = Map.fromList (map (\(PredSig pName argSorts resSort) -> (pName, resSort:argSorts)) (env ^. boundPredicates)) `Map.union` (env ^. globalPredicates)

-- | 'allMeasuresOf' @dtName env@ : all measure of datatype with name @dtName@ in @env@
allMeasuresOf dtName env = Map.filter (\(MeasureDef (DataS sName _) _ _ _) -> dtName == sName) $ env ^. measures

-- | 'allMeasurePostconditions' @baseT env@ : all nontrivial postconditions of measures of @baseT@ in case it is a datatype
allMeasurePostconditions includeQuanitifed baseT@(DatatypeT dtName tArgs _) env =
    let
      allMeasures = Map.toList $ allMeasuresOf dtName env
      isAbstract = null $ ((env ^. datatypes) Map.! dtName) ^. constructors
    in catMaybes $ map extractPost allMeasures ++
                   if isAbstract then map contentProperties allMeasures else [] ++
                   if includeQuanitifed then map elemProperties allMeasures else []
  where
    extractPost (mName, MeasureDef _ outSort _ fml) =
      if fml == ftrue
        then Nothing
        else Just $ substitute (Map.singleton valueVarName (Pred outSort mName [Var (toSort baseT) valueVarName])) fml

    contentProperties (mName, MeasureDef (DataS _ vars) a _ _) = case elemIndex a vars of
      Nothing -> Nothing
      Just i -> let (ScalarT elemT fml) = tArgs !! i -- @mName@ "returns" one of datatype's parameters: transfer the refinement onto the value of the measure
                in let
                    elemSort = toSort elemT
                    measureApp = Pred elemSort mName [Var (toSort baseT) valueVarName]
                   in Just $ substitute (Map.singleton valueVarName measureApp) fml
    contentProperties (mName, MeasureDef {}) = Nothing

    elemProperties (mName, MeasureDef (DataS _ vars) (SetS a) _ _) = case elemIndex a vars of
      Nothing -> Nothing
      Just i -> let (ScalarT elemT fml) = tArgs !! i -- @mName@ is a set of datatype "elements": add an axiom that every element of the set has that property
                in if fml == ftrue || fml == ffalse || not (Set.null $ unknownsOf fml)
                    then Nothing
                    else  let
                            elemSort = toSort elemT
                            scopedVar = Var elemSort "_x"
                            setVal = Pred (SetS elemSort) mName [Var (toSort baseT) valueVarName]
                          in Just $ All scopedVar (fin scopedVar setVal |=>| substitute (Map.singleton valueVarName scopedVar) fml)
    elemProperties (mName, MeasureDef {}) = Nothing

allMeasurePostconditions _ _ _ = []

typeSubstituteEnv :: TypeSubstitution -> Environment -> Environment
typeSubstituteEnv tass = over symbols (Map.map (Map.map (schemaSubstitute tass)))

-- | Insert weakest refinement
refineTop :: Environment -> SType -> RType
refineTop env (ScalarT (DatatypeT name tArgs pArgs) _) =
  let variances = env ^. (datatypes . to (Map.! name) . predVariances) in
  ScalarT (DatatypeT name (map (refineTop env) tArgs) (map (BoolLit . not) variances)) ftrue
refineTop _ (ScalarT IntT _) = ScalarT IntT ftrue
refineTop _ (ScalarT BoolT _) = ScalarT BoolT ftrue
refineTop _ (ScalarT (TypeVarT vSubst a) _) = ScalarT (TypeVarT vSubst a) ftrue
refineTop env (FunctionT x tArg tFun) = FunctionT x (refineBot env tArg) (refineTop env tFun)

-- | Insert strongest refinement
refineBot :: Environment -> SType -> RType
refineBot env (ScalarT (DatatypeT name tArgs pArgs) _) =
  let variances = env ^. (datatypes . to (Map.! name) . predVariances) in
  ScalarT (DatatypeT name (map (refineBot env) tArgs) (map BoolLit variances)) ffalse
refineBot _ (ScalarT IntT _) = ScalarT IntT ffalse
refineBot _ (ScalarT BoolT _) = ScalarT BoolT ffalse
refineBot _ (ScalarT (TypeVarT vSubst a) _) = ScalarT (TypeVarT vSubst a) ffalse
refineBot env (FunctionT x tArg tFun) = FunctionT x (refineTop env tArg) (refineBot env tFun)



{- Input language declarations -}

-- | Constructor signature: name and type
data ConstructorSig = ConstructorSig Id RType
  deriving (Show, Eq)

constructorName (ConstructorSig name _) = name

data BareDeclaration =
  TypeDecl Id [Id] RType |                                  -- ^ Type name, variables, and definition
  FuncDecl Id RSchema |                                     -- ^ Function name and signature
  DataDecl Id [Id] [(PredSig, Bool)] [ConstructorSig] |     -- ^ Datatype name, type parameters, predicate parameters, and constructor definitions
  MeasureDecl Id Sort Sort Formula [MeasureCase] Bool |     -- ^ Measure name, input sort, output sort, postcondition, definition cases, and whether this is a termination metric
  PredDecl PredSig |                                        -- ^ Module-level predicate
  QualifierDecl [Formula] |                                 -- ^ Qualifiers
  MutualDecl [Id] |                                         -- ^ Mutual recursion group
  InlineDecl Id [Id] Formula |                              -- ^ Inline predicate
  SynthesisGoal Id UProgram                                 -- ^ Name and template for the function to reconstruct
  deriving (Show, Eq)

type Declaration = Pos BareDeclaration

isSynthesisGoal (Pos _ (SynthesisGoal _ _)) = True
isSynthesisGoal _ = False

{- Misc -}

-- | Typing constraints
data Constraint = Subtype Environment RType RType Bool Id
  | WellFormed Environment RType
  | WellFormedCond Environment Formula
  | WellFormedMatchCond Environment Formula
  | WellFormedPredicate Environment [Sort] Id
  deriving (Show, Eq, Ord)

-- | Synthesis goal
data Goal = Goal {
  gName :: Id,                  -- ^ Function name
  gEnvironment :: Environment,  -- ^ Enclosing environment
  gSpec :: RSchema,             -- ^ Specification
  gImpl :: UProgram,            -- ^ Implementation template
  gDepth :: Int,                -- ^ Maximum level of auxiliary goal nesting allowed inside this goal
  gSourcePos :: SourcePos,      -- ^ Source Position,
  gSynthesize :: Bool           -- ^ Synthesis flag (false implies typechecking only)
} deriving (Show, Eq, Ord)


unresolvedType env ident = (env ^. unresolvedConstants) Map.! ident
unresolvedSpec goal = unresolvedType (gEnvironment goal) (gName goal)

-- Remove measure being typechecked from environment
filterEnv :: Environment -> Id -> Environment
filterEnv e m = Lens.set measures (Map.filterWithKey (\k _ -> k == m) (e ^. measures)) e

-- Transform a resolved measure into a program
measureProg :: Id -> MeasureDef -> UProgram
measureProg name (MeasureDef inSort outSort defs post) = Program {
  typeOf = t, content = PFun "THIS" Program{ content = PMatch Program{ content = PSymbol "THIS", typeOf = t } (map mCase defs), typeOf = t} }
  where
    t   = AnyT

-- Transform between case types
mCase :: MeasureCase -> Case RType
mCase (MeasureCase con args body) = Case{constructor = con, argNames = args, expr = fmlToUProgram body}

-- Transform type signature into a synthesis/typechecking schema
generateSchema :: Environment -> Id -> Sort -> Sort -> Formula -> RSchema
--generateSchema e name (DataS inS sorts) outSort post = typePolymorphic (getTypeParams e inS) (getPredParams e inS) name (DataS inS sorts) outSort post
-- predicate polymorphic only:
generateSchema e name (DataS inS sorts) outSort post = predPolymorphic (getPredParams e inS) [] name (DataS inS sorts) outSort post

getTypeParams :: Environment -> Id -> [Id]
getTypeParams e name = case Map.lookup name (e ^. datatypes) of
  Just d -> d ^. typeParams
  Nothing -> []

getPredParams :: Environment -> Id -> [PredSig]
getPredParams e name = case Map.lookup name (e ^. datatypes) of
  Just d -> d ^. predParams
  Nothing -> []

-- Wrap function in appropriate type-polymorphic Schema skeleton
typePolymorphic :: [Id] -> [PredSig] -> Id -> Sort -> Sort -> Formula -> SchemaSkeleton Formula
typePolymorphic [] ps name inSort outSort f = predPolymorphic ps [] name inSort outSort f
typePolymorphic (x:xs) ps name inSort outSort f = ForallT x (typePolymorphic xs ps name inSort outSort f)

-- Wrap function in appropriate predicate-polymorphic SchemaSkeleton
predPolymorphic :: [PredSig] -> [Id] -> Id -> Sort -> Sort -> Formula -> SchemaSkeleton Formula
predPolymorphic [] ps name inSort outSort f = genSkeleton name ps inSort outSort f
predPolymorphic (x:xs) ps name inSort outSort f = ForallP x (predPolymorphic xs  ((predSigName x) : ps) name inSort outSort f)

-- Generate non-polymorphic core of schema
-- TODO: don't hard code qs
genSkeleton :: Id -> [Id] -> Sort -> Sort -> Formula -> SchemaSkeleton Formula
genSkeleton name preds inSort outSort post = Monotype (FunctionT "THIS" (ScalarT inType ftrue) (ScalarT outType post))
  where
    inType  = case inSort of
      (DataS name args) -> DatatypeT name (map fromSort args) pforms
      _ -> (baseTypeOf . fromSort) inSort
    outType = (baseTypeOf . fromSort) outSort
    pforms = fmap predform preds
    predform x = Pred AnyS x []

-- Default set implementation -- Needed to typecheck measures involving sets
defaultSetType :: BareDeclaration
defaultSetType = DataDecl name typeVars preds cons
  where
    name = setTypeName
    typeVars = ["a"]
    preds = []
    cons = [empty,single,insert]
    empty = ConstructorSig emptySetCtor (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True))
    single = ConstructorSig singletonCtor (FunctionT "x" (ScalarT (TypeVarT Map.empty "a") (BoolLit True)) (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True)))
    insert = ConstructorSig insertSetCtor (FunctionT "x" (ScalarT (TypeVarT Map.empty "a") (BoolLit True)) (FunctionT "xs" (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True)) (ScalarT (DatatypeT setTypeName [ScalarT (TypeVarT Map.empty "a") (BoolLit True)] []) (BoolLit True))))


-- Succinct type operations
addSuccinctSymbol :: Id -> RSchema -> Environment -> Environment
addSuccinctSymbol name t env = case t of 
  Monotype (LetT id tDef tBody) -> addSuccinctSymbol name (Monotype tBody) $ addSuccinctSymbol id (Monotype tDef) env
  _ -> let
    succinctTy = case toSuccinctType t of
      SuccinctAll vars ty -> SuccinctAll vars (refineSuccinctDatatype name ty env)
      ty -> refineSuccinctDatatype name ty env
    -- if it is a constructor, we add its corresponding destructors as well
    envWithDestructors = let
      consIds = concatMap (\dt -> (dt ^. constructors)) (Map.elems (env ^. datatypes))
      in if Set.member name (Set.fromList consIds)
        then case succinctTy of
          SuccinctAll vars ty -> addDestructors name (Set.map (\t -> SuccinctAll vars t) (getSuccinctDestructors name ty)) env
          _ -> addDestructors name (getSuccinctDestructors name succinctTy) env
        else env
    envWithSelf = addEdge name succinctTy envWithDestructors
    -- envWithAll = envWithSelf
    envWithAll = let 
      addedTys = (allSuccinctNodes (envWithSelf ^. succinctGraph)) `Set.difference` (allSuccinctNodes (env ^. succinctGraph))
      in Set.foldl' (\accEnv elmt -> let
        (ty,ty',id) = elmt
        tyVars = extractSuccinctTyVars ty'
        substs = map (\ts -> foldl' (\acc (x,y) -> Map.insert x y acc) Map.empty (zip (Set.toList tyVars) ts)) $ sequence (replicate (Set.size tyVars) (Set.toList addedTys))
        tys = map (\substitution -> succinctTypeSubstitute substitution ty') substs
        in foldl' (\acc typ -> (succinctGraph %~ Map.insertWith mergeMapOfSet ty (Map.singleton typ (Set.singleton id))) acc) accEnv tys
      ) envWithSelf (envWithSelf ^. undecidableSymbols)
    reachableSet = getReachableNodes $ reverseGraph (envWithAll ^. succinctGraph)
    prunedEnv = (reachableSymbols %~ Set.union reachableSet) envWithAll
    in (succinctSymbols %~ Map.insert name succinctTy) prunedEnv

refineSuccinctDatatype :: Id -> RSuccinctType -> Environment -> RSuccinctType
refineSuccinctDatatype name sty env = case sty of
  SuccinctDatatype ids tys cons -> let
    consMap = Set.foldl (\accMap (id,_) -> foldl (\acc c -> Map.insert c id acc) accMap (case (Map.lookup id (env ^. datatypes)) of
      Just dt -> dt ^. constructors
      Nothing -> [])) Map.empty ids
    -- consMap = Set.foldl' (\acc (id,set) -> Map.insert id set acc) Map.empty consSet
    -- (singleId,_) = Set.findMin ids
    in if Map.member name consMap
      then SuccinctDatatype ids tys (Map.singleton (fromJust (Map.lookup name consMap)) (Set.singleton name))
      -- else 
      --   if Map.null consMap
      --   then let (myid,_) = Set.findMin ids in case Map.lookup myid (env ^. typeSynonyms) of
      --     Nothing -> SuccinctDatatype ids tys cons
      --     Just (tVars, t) -> rtypeToSuccinctType $ noncaptureTypeSubst tVars [refineSort (toSort (TypeVarT Map.empty myid)) (BoolLit True)] t
        else SuccinctDatatype ids tys cons
      -- case Map.lookup singleId (env ^. datatypes) of
      --   Just dtDef -> if Set.member name (Set.fromList (dtDef ^. constructors))
      --     then SuccinctDatatype ids tys (Map.singleton singleId (Set.singleton name))
      --     else SuccinctDatatype ids tys consMap
      --   Nothing -> SuccinctDatatype ids tys consMap
  SuccinctFunction params ret -> SuccinctFunction (Set.map (\arg -> refineSuccinctDatatype (name++"00") arg env) params) (refineSuccinctDatatype name ret env)
  SuccinctComposite tys -> SuccinctComposite (Set.map (\ty -> refineSuccinctDatatype "" ty env) tys)
  ty' -> ty'

addDestructors :: Id -> Set RSuccinctType -> Environment -> Environment
addDestructors name destructors env = let
  (resEnv, _) = Set.foldl' (\(accEnv,idx) ty -> (addEdge (name++"_match_"++(show idx)) ty accEnv, idx+1)) (env, 0) destructors
  (env', _) = Set.foldl' (\(accEnv,idx) ty -> ((succinctSymbols %~ Map.insert (name++"_match_"++(show idx)) ty) accEnv, idx+1)) (resEnv, 0) destructors
  in env'

addEdge :: Id -> RSuccinctType -> Environment -> Environment
addEdge name (SuccinctFunction argSet retTy) env = 
  let
    argTy = if Set.size argSet == 1 then Set.findMin argSet else SuccinctComposite argSet
    --addedRetEnv = (succinctGraph %~ Map.insertWith Map.union retTy (Map.singleton argTy (Set.singleton name))) env
    addedRetEnv = (succinctGraph %~ Map.insertWith mergeMapOfSet retTy (Map.singleton argTy (Set.singleton name))) env
  in Set.foldl' (\acc elem -> (succinctGraph %~ Map.insertWith mergeMapOfSet (SuccinctComposite argSet) (Map.singleton elem (Set.singleton ""))) acc) addedRetEnv argSet
addEdge name (SuccinctAll idSet ty) env = case ty of 
  SuccinctFunction pty rty -> let 
    fold_fun accEnv sty = let 
      (unified, substitutions) = unifySuccinct rty sty (accEnv ^. boundTypeVars)
      pty' = map (\substitution -> Set.map (succinctTypeSubstitute substitution) pty) substitutions -- list of possible ptys
      in if unified 
        then foldl' (\acc ptySet -> if Set.foldl (\acc t -> Set.size (extractSuccinctTyVars t) > 0 || acc) False ptySet
          then let 
            tyVars = Set.foldl (\set t -> set `Set.union` (extractSuccinctTyVars t)) Set.empty ptySet
            substs = map (\ts -> foldl' (\acc (x,y) -> Map.insert x y acc) Map.empty (zip (Set.toList tyVars) ts)) $ sequence (replicate (Set.size tyVars) (Set.toList (allSuccinctNodes (acc ^. succinctGraph))))
            tys = map (\substitution -> Set.map (succinctTypeSubstitute substitution) ptySet) substs
            tmpEnv = foldl' (\acc' typ -> (succinctGraph %~ Map.insertWith mergeMapOfSet sty (Map.singleton (if Set.size typ == 1 then Set.findMin typ else SuccinctComposite typ) (Set.singleton name))) acc') acc tys
            in (undecidableSymbols %~ Set.insert (sty, if Set.size ptySet == 1 then Set.findMin ptySet else SuccinctComposite ptySet, name)) tmpEnv
          else (succinctGraph %~ Map.insertWith mergeMapOfSet sty (Map.singleton (if Set.size ptySet == 1 then Set.findMin ptySet else SuccinctComposite ptySet) (Set.singleton name))) acc
        ) accEnv pty'
        else accEnv
    in Set.foldl' fold_fun env (allSuccinctNodes (env ^. succinctGraph))
  _                        -> let 
    fold_fun accEnv sty = let 
      (unified, substitutions) = unifySuccinct ty sty (accEnv ^. boundTypeVars)
      tys = map (\substitution -> succinctTypeSubstitute substitution ty) substitutions
      in if unified 
        then foldl' (\acc ty' -> if Set.size (extractSuccinctTyVars ty') > 0
          then let 
            tyVars = extractSuccinctTyVars ty'
            substs = map (\ts -> foldl' (\acc (x,y) -> Map.insert x y acc) Map.empty (zip (Set.toList tyVars) ts)) $ sequence (replicate (Set.size tyVars) (Set.toList (allSuccinctNodes (acc ^. succinctGraph))))
            substedTys = map (\substitution -> succinctTypeSubstitute substitution ty') substs
            tmpEnv = foldl' (\acc' typ -> (succinctGraph %~ Map.insertWith mergeMapOfSet sty (Map.singleton (SuccinctInhabited typ) (Set.singleton name))) acc') acc substedTys
            in (undecidableSymbols %~ Set.insert (sty, SuccinctInhabited ty', name)) tmpEnv
          else (succinctGraph %~ Map.insertWith mergeMapOfSet sty (Map.singleton (SuccinctInhabited ty') (Set.singleton name))) acc
        ) accEnv tys 
        else accEnv
    in Set.foldl' fold_fun env (allSuccinctNodes (env ^. succinctGraph))
addEdge name typ env = 
  let
    inhabitedEnv = (succinctGraph %~ Map.insertWith mergeMapOfSet typ (Map.singleton (SuccinctInhabited typ) (Set.singleton name))) env
    isPolyTypes ty = case ty of
      SuccinctAll _ _ -> True
      _               -> False
    polyTypes = Map.filter isPolyTypes (env ^. succinctSymbols)
    env' = Map.foldlWithKey (\accEnv k v -> case v of
      SuccinctFunction pty rty -> let
        (unified, substitutions) = unifySuccinct typ rty (env ^. boundTypeVars)
        pty' = map (\substitution -> Set.map (succinctTypeSubstitute substitution) pty) substitutions
        in if unified
          then foldl' (\acc ptySet -> if Set.foldl (\acc t -> Set.size (extractSuccinctTyVars t) > 0 || acc) False ptySet
            then let 
              tyVars = Set.foldl (\set t -> set `Set.union` (extractSuccinctTyVars t)) Set.empty ptySet
              substs = map (\ts -> foldl' (\acc (x,y) -> Map.insert x y acc) Map.empty (zip (Set.toList tyVars) ts)) $ sequence (replicate (Set.size tyVars) (Set.toList (allSuccinctNodes (acc ^. succinctGraph))))
              substedTys = map (\substitution -> Set.map (succinctTypeSubstitute substitution) ptySet) substs
              tmpEnv = foldl' (\acc' tySet -> (succinctGraph %~ Map.insertWith mergeMapOfSet typ (Map.singleton (if Set.size tySet == 1 then Set.findMin tySet else SuccinctComposite tySet) (Set.singleton k))) acc') acc substedTys
              in (undecidableSymbols %~ Set.insert (typ, if Set.size ptySet == 1 then Set.findMin ptySet else SuccinctComposite ptySet, k)) tmpEnv
            else (succinctGraph %~ Map.insertWith mergeMapOfSet typ (Map.singleton (if Set.size ptySet == 1 then Set.findMin ptySet else SuccinctComposite ptySet) (Set.singleton k))) acc
          ) accEnv pty'
          else accEnv
      _ -> let
        (unified, substitutions) = unifySuccinct typ v (env ^. boundTypeVars)
        tys = map (\substitution -> succinctTypeSubstitute substitution v) substitutions
        in if unified
          then foldl' (\acc ty' -> if Set.size (extractSuccinctTyVars ty') > 0
            then let 
              tyVars = extractSuccinctTyVars ty'
              substs = map (\ts -> foldl' (\acc (x,y) -> Map.insert x y acc) Map.empty (zip (Set.toList tyVars) ts)) $ sequence (replicate (Set.size tyVars) (Set.toList (allSuccinctNodes (acc ^. succinctGraph))))
              substedTys = map (\substitution -> succinctTypeSubstitute substitution ty') substs
              tmpEnv = foldl' (\acc' ty -> (succinctGraph %~ Map.insertWith mergeMapOfSet typ (Map.singleton (SuccinctInhabited ty) (Set.singleton k))) acc') acc substedTys
              in (undecidableSymbols %~ Set.insert (typ, SuccinctInhabited ty', k)) tmpEnv
            else (succinctGraph %~ Map.insertWith mergeMapOfSet typ (Map.singleton (SuccinctInhabited ty') (Set.singleton k))) acc) accEnv tys
          else accEnv) inhabitedEnv polyTypes
  in env'