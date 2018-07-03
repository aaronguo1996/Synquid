{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}

-- | Incremental solving of subtyping and well-formedness constraints
module Synquid.TypeConstraintSolver (
  ErrorMessage,
  TypingParams (..),
  TypingState (..),
  typingConstraints,
  predAssignment,
  idCount,
  qualifierMap,
  hornClauses,
  candidates,
  simpleConstraints,
  errorContext,
  isFinal,
  TCSolver,
  runTCSolver,
  initTypingState,
  addTypingConstraint,
  addFixedUnknown,
  setUnknownRecheck,
  solveTypeConstraints,
  simplifyAllConstraints,
  getViolatingLabels,  
  solveAllCandidates,
  matchConsType,
  hasPotentialScrutinees,
  freshId,
  freshVar,
  finalizeType,
  finalizeProgram,
  initEnv,
  allScalars,
  condQualsGen,
  updateConstraintEnv,
  isCondConstraint
) where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.SolverMonad
import Synquid.Util
import Synquid.Resolver (addAllVariables)

import Data.Maybe
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Applicative hiding (empty)
import Control.Lens hiding (both)
import Debug.Trace

{- Interface -}

-- | Parameters of type constraint solving
data TypingParams = TypingParams {
  _condQualsGen :: Environment -> [Formula] -> QSpace,              -- ^ Qualifier generator for conditionals
  _matchQualsGen :: Environment -> [Formula] -> QSpace,             -- ^ Qualifier generator for match scrutinees
  _typeQualsGen :: Environment -> Formula -> [Formula] -> QSpace,   -- ^ Qualifier generator for types
  _predQualsGen :: Environment -> [Formula] -> [Formula] -> QSpace, -- ^ Qualifier generator for bound predicates
  _tcSolverSplitMeasures :: Bool,
  _tcSolverLogLevel :: Int    -- ^ How verbose logging is  
}

makeLenses ''TypingParams

-- | State of type constraint solving
data TypingState = TypingState {
  -- Persistent state:
  _typingConstraints :: [Constraint],           -- ^ Typing constraints yet to be converted to horn clauses
  _predAssignment :: Substitution,              -- ^ Current assignment to free predicate variables  _qualifierMap :: QMap,
  _qualifierMap :: QMap,                        -- ^ Current state space for predicate unknowns
  _candidates :: [Candidate],                   -- ^ Current set of candidate liquid assignments to unknowns
  _initEnv :: Environment,                      -- ^ Initial environment
  _idCount :: Map String Int,                   -- ^ Number of unique identifiers issued so far
  _isFinal :: Bool,                             -- ^ Has the entire program been seen?
  -- Temporary state:
  _simpleConstraints :: [Constraint],           -- ^ Typing constraints that cannot be simplified anymore and can be converted to horn clauses or qualifier maps
  _hornClauses :: [(Formula, Id)],              -- ^ Horn clauses generated from subtyping constraints
  _consistencyChecks :: [Formula],              -- ^ Formulas generated from type consistency constraints
  _errorContext :: (SourcePos, Doc)             -- ^ Information to be added to all type errors
}

makeLenses ''TypingState

-- | Computations that solve type constraints, parametrized by the the horn solver @s@
type TCSolver s = StateT TypingState (ReaderT TypingParams (ExceptT ErrorMessage s))

-- | 'runTCSolver' @params st go@ : execute a typing computation @go@ with typing parameters @params@ in a typing state @st@
runTCSolver :: TypingParams -> TypingState -> TCSolver s a -> s (Either ErrorMessage (a, TypingState))
runTCSolver params st go = runExceptT $ runReaderT (runStateT go st) params  

-- | Initial typing state in the initial environment @env@
initTypingState :: MonadHorn s => Environment -> s TypingState
initTypingState env = do
  initCand <- initHornSolver env
  return $ TypingState {
    _typingConstraints = [],
    _predAssignment = Map.empty,
    _qualifierMap = Map.empty,
    _candidates = [initCand],
    _initEnv = env,
    _idCount = Map.empty,
    _isFinal = False,
    _simpleConstraints = [],
    _hornClauses = [],
    _consistencyChecks = [],
    _errorContext = (noPos, empty)
  }

-- | Impose typing constraint @c@ on the programs
addTypingConstraint c = over typingConstraints (nub . (c :))

-- | Solve @typingConstraints@: either strengthen the current candidates and return shapeless type constraints or fail
solveTypeConstraints :: MonadHorn s => TCSolver s TypeSubstitution
solveTypeConstraints = do
  subst <- simplifyAllConstraints
  typeSubstituteConstraints subst
  scs <- use simpleConstraints
  writeLog 3 (text "Simple Constraints" $+$ (vsep $ map pretty scs))  
  
  psubst <- processAllPredicates
  -- predSubstituteConstraints psubst
  processAllConstraints
  generateAllHornClauses
  
  solveHornClauses
  checkTypeConsistency  
    
  hornClauses .= []
  consistencyChecks .= []

  return subst
  
{- Repair-specific interface -}

getViolatingLabels :: MonadHorn s => TCSolver s (Set Id)
getViolatingLabels = do
  scs <- use simpleConstraints
  writeLog 2 (text "Simple Constraints" $+$ (vsep $ map pretty scs))

  processAllPredicates  
  processAllConstraints
  generateAllHornClauses

  clauses <- use hornClauses
  -- TODO: this should probably be moved to Horn solver
  let (nontermClauses, termClauses) = partition isNonTerminal clauses
  qmap <- use qualifierMap
  cands <- use candidates
  env <- use initEnv
  
  writeLog 2 (vsep [
    nest 2 $ text "Terminal Horn clauses" $+$ vsep (map (\(fml, l) -> text l <> text ":" <+> pretty fml) termClauses), 
    nest 2 $ text "Nonterminal Horn clauses" $+$ vsep (map (\(fml, l) -> text l <> text ":" <+> pretty fml) nontermClauses), 
    nest 2 $ text "QMap" $+$ pretty qmap])        
  
  (newCand:[]) <- lift . lift . lift $ refineCandidates (map fst nontermClauses) qmap (instantiateConsAxioms env Nothing) cands    
  candidates .= [newCand]  
  invalidTerminals <- filterM (isInvalid newCand (instantiateConsAxioms env Nothing)) termClauses
  return $ Set.fromList $ map snd invalidTerminals
  where
    isNonTerminal (Binary Implies _ (Unknown _ _), _) = True
    isNonTerminal _ = False

    isInvalid cand extractAssumptions (fml,_) = do
      cands' <- lift . lift . lift $ checkCandidates False [fml] extractAssumptions [cand]
      return $ null cands'
      
{- Implementation -}      
      
-- | Decompose and unify typing constraints; 
-- return shapeless type constraints: constraints involving only free type variables, which impose no restrictions yet, but might in the future
simplifyAllConstraints :: MonadHorn s => TCSolver s TypeSubstitution
simplifyAllConstraints = do
  tcs <- use typingConstraints
  writeLog 3 (text "Typing Constraints" $+$ (vsep $ map pretty tcs))
  typingConstraints .= []
  substs <- foldM (\accSubst tc -> do
    let tc' = typeSubstituteConstraint accSubst tc
    subst <- simplifyConstraint tc'
    return $ Map.union accSubst subst
    ) Map.empty tcs
  typeSubstituteConstraints substs
  
  substs' <- if (Map.size substs > 0) then simplifyAllConstraints else return Map.empty

  return $ Map.union substs substs'
  
-- | Assign unknowns to all free predicate variables  
processAllPredicates :: MonadHorn s => TCSolver s Substitution
processAllPredicates = do
  tcs <- use typingConstraints
  typingConstraints .= []
  predSubst <- foldM (\accSubst tc -> do
    -- let tc' = predSubstituteConstraint accSubst tc
    subst <- processPredicate tc
    return $ Map.union accSubst subst
    ) Map.empty tcs
  pass <- use predAssignment
  writeLog 3 (text "Pred assignments" $+$
              vMapDoc text pretty pass)
  return predSubst
      
-- | Eliminate type and predicate variables, generate qualifier maps
processAllConstraints :: MonadHorn s => TCSolver s ()
processAllConstraints = do  
  tcs <- use simpleConstraints
  simpleConstraints .= []
  mapM_ processConstraint tcs
    
-- | Convert simple subtyping constraints into horn clauses
generateAllHornClauses :: MonadHorn s => TCSolver s ()
generateAllHornClauses = do
  tcs <- use simpleConstraints
  simpleConstraints .= []
  mapM_ generateHornClauses tcs
  
-- | Signal type error  
throwError :: MonadHorn s => Doc -> TCSolver s ()  
throwError msg = do
  (pos, ec) <- use errorContext
  lift $ lift $ throwE $ ErrorMessage TypeError pos (msg $+$ ec)

-- | Refine the current liquid assignments using the horn clauses
solveHornClauses :: MonadHorn s => TCSolver s ()
solveHornClauses = do
  clauses <- use hornClauses
  qmap <- use qualifierMap
  cands <- use candidates
  env <- use initEnv
  cands' <- lift . lift . lift $ refineCandidates (map fst clauses) qmap (instantiateConsAxioms env Nothing) cands
    
  when (null cands') (throwError $ text "Cannot find sufficiently strong refinements")
  candidates .= cands'
  
solveAllCandidates :: MonadHorn s => TCSolver s ()  
solveAllCandidates = do
  cands <- use candidates
  cands' <- concat <$> mapM solveCandidate cands
  candidates .= cands'
  where
    solveCandidate c@(Candidate s valids invalids _) = 
      if Set.null invalids
        then return [c]
        else do
          qmap <- use qualifierMap
          env <- use initEnv        
          cands' <- lift . lift . lift $ refineCandidates [] qmap (instantiateConsAxioms env Nothing) [c]
          concat <$> mapM solveCandidate cands'

-- | Filter out liquid assignments that are too strong for current consistency checks  
checkTypeConsistency :: MonadHorn s => TCSolver s ()  
checkTypeConsistency = do
  clauses <- use consistencyChecks
  cands <- use candidates
  env <- use initEnv  
  cands' <- lift . lift . lift $ checkCandidates True clauses (instantiateConsAxioms env Nothing) cands
  when (null cands') (throwError $ text "Found inconsistent refinements")
  candidates .= cands'

-- | Simplify @c@ into a set of simple and shapeless constraints, possibly extended the current type assignment or predicate assignment
simplifyConstraint :: MonadHorn s => Constraint -> TCSolver s TypeSubstitution
simplifyConstraint c = do
  pass <- use predAssignment
  subst <- simplifyConstraint' pass c
  return subst

-- Any type: drop
simplifyConstraint'  _ (Subtype _ _ AnyT _ _) = return Map.empty
simplifyConstraint' _ c@(Subtype _ AnyT _ _ _) = return Map.empty
simplifyConstraint' _ c@(WellFormed _ AnyT) = return Map.empty
-- Any datatype: drop only if lhs is a datatype
simplifyConstraint' _ (Subtype _ (ScalarT (DatatypeT _ _ _) _) t _ _) | t == anyDatatype = return Map.empty
-- Well-formedness of a known predicate drop  
simplifyConstraint' pass c@(WellFormedPredicate _ _ p) | p `Map.member` pass = return Map.empty

-- Two unknown free variables: nothing can be done for now
simplifyConstraint' _ c@(Subtype env (ScalarT (TypeVarT _ a) _) (ScalarT (TypeVarT _ b) _) _ _) | not (isBound env a) && not (isBound env b)
  = if a == b
      then error $ show $ text "simplifyConstraint: equal type variables on both sides"
      else ifM (use isFinal) 
            (do -- This is a final pass: assign an arbitrary type to one of the variables
              let subst = Map.singleton a intAll
              typeSubstituteConstraints subst
              let c' = typeSubstituteConstraint subst c
              subst' <- simplifyConstraint c'
              return $ Map.union subst subst') 
            (modify (addTypingConstraint c) >> return Map.empty)
simplifyConstraint' _ c@(WellFormed env (ScalarT (TypeVarT _ a) _)) | not (isBound env a) 
  = modify (addTypingConstraint c) >> return Map.empty
simplifyConstraint' _ c@(WellFormedPredicate _ _ _) = modify (addTypingConstraint c) >> return Map.empty

-- Let types: extend environment (has to be done before trying to extend the type assignment)
simplifyConstraint' _ (Subtype env (LetT x tDef tBody) t consistent label)
  = simplifyConstraint (Subtype (addVariable x tDef env) tBody t consistent label) -- ToDo: make x unique?
simplifyConstraint' _ (Subtype env t (LetT x tDef tBody) consistent label)
  = simplifyConstraint (Subtype (addVariable x tDef env) t tBody consistent label) -- ToDo: make x unique? 
  
-- Unknown free variable and a type: extend type assignment
simplifyConstraint' _ c@(Subtype env (ScalarT (TypeVarT _ a) _) t _ _) | not (isBound env a) = do
  writeLog 3 $ text "CALL UNIFY FROM" <+> pretty c
  (a, t') <- unify env a t
  let subst = Map.singleton a t'
  typeSubstituteConstraints subst
  subst' <- simplifyConstraint $ typeSubstituteConstraint subst c
  return $ Map.union subst subst'
simplifyConstraint' _ c@(Subtype env t (ScalarT (TypeVarT _ a) _) _ _) | not (isBound env a)  = do
  writeLog 3 $ text "CALL UNIFY FROM" <+> pretty c
  (a, t') <- unify env a t
  let subst = Map.singleton a t'
  typeSubstituteConstraints subst
  subst' <- simplifyConstraint $ typeSubstituteConstraint subst c
  return $ Map.union subst subst'

-- Compound types: decompose
simplifyConstraint' _ (Subtype env (ScalarT (DatatypeT name (tArg:tArgs) pArgs) fml) (ScalarT (DatatypeT name' (tArg':tArgs') pArgs') fml') consistent label)
  = do
      subst1 <- simplifyConstraint (Subtype env tArg tArg' consistent label)
      subst2 <- simplifyConstraint $ typeSubstituteConstraint subst1 (Subtype env (ScalarT (DatatypeT name tArgs pArgs) fml) (ScalarT (DatatypeT name' tArgs' pArgs') fml') consistent label)
      return $ Map.union subst1 subst2
simplifyConstraint' _ (Subtype env (ScalarT (DatatypeT name [] (pArg:pArgs)) fml) (ScalarT (DatatypeT name' [] (pArg':pArgs')) fml') consistent label)
  = do
      let variances = _predVariances ((env ^. datatypes) Map.! name)
      let isContra = variances !! (length variances - length pArgs - 1) -- Is pArg contravariant?
      subst1 <- if isContra
        then simplifyConstraint (Subtype env (int $ pArg') (int $ pArg) consistent label)
        else simplifyConstraint (Subtype env (int $ pArg) (int $ pArg') consistent label)
      subst2 <- simplifyConstraint $ typeSubstituteConstraint subst1 (Subtype env (ScalarT (DatatypeT name [] pArgs) fml) (ScalarT (DatatypeT name' [] pArgs') fml') consistent label)      
      return $ Map.union subst1 subst2
simplifyConstraint' _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) False label)
  = do
      subst1 <- simplifyConstraint (Subtype env tArg2 tArg1 False label)
      subst2 <- if isScalarType tArg1
        then simplifyConstraint $ typeSubstituteConstraint subst1 (Subtype (addVariable y tArg2 env) (renameVar (isBound env) x y tArg1 tRes1) tRes2 False label)
        else simplifyConstraint $ typeSubstituteConstraint subst1 (Subtype env tRes1 tRes2 False label)
      return $ Map.union subst1 subst2
simplifyConstraint' _ (Subtype env (FunctionT x tArg1 tRes1) (FunctionT y tArg2 tRes2) True label)
  = if isScalarType tArg1
      then simplifyConstraint (Subtype (addVariable x tArg1 env) tRes1 tRes2 True label)
      else simplifyConstraint (Subtype env tRes1 tRes2 True label)
simplifyConstraint' _ c@(WellFormed env (ScalarT (DatatypeT name tArgs _) fml))
  = do
      substs <- mapM (simplifyConstraint . WellFormed env) tArgs
      simpleConstraints %= (c :)
      return $ Map.unions substs
simplifyConstraint' _ (WellFormed env (FunctionT x tArg tRes))
  = do
      subst1 <- simplifyConstraint (WellFormed env tArg)
      subst2 <- simplifyConstraint $ typeSubstituteConstraint subst1 (WellFormed (addVariable x tArg env) tRes)
      return $ Map.union subst1 subst2
simplifyConstraint' _ (WellFormed env (LetT x tDef tBody))
  = simplifyConstraint (WellFormed (addVariable x tDef env) tBody)

-- Simple constraint: return
simplifyConstraint' _ c@(Subtype _ (ScalarT baseT _) (ScalarT baseT' _) _ _) | baseT == baseT' = simpleConstraints %= (c :) >> return Map.empty
simplifyConstraint' _ c@(WellFormed _ (ScalarT baseT _)) = simpleConstraints %= (c :) >> return Map.empty
simplifyConstraint' _ c@(WellFormedCond _ _) = simpleConstraints %= (c :) >> return Map.empty
simplifyConstraint' _ c@(WellFormedMatchCond _ _) = simpleConstraints %= (c :) >> return Map.empty
-- Otherwise (shape mismatch): fail
simplifyConstraint' _ (Subtype _ t t' _ _) = do
  throwError $ text  "Cannot match shape" <+> squotes (pretty $ shape t) $+$ text "with shape" <+> squotes (pretty $ shape t')
  return Map.empty

-- | Unify type variable @a@ with type @t@ or fail if @a@ occurs in @t@
unify env a t = if a `Set.member` typeVarsOf t
  then error $ show $ text "simplifyConstraint: type variable occurs in the other type"
  else do
    t' <- fresh env t
    writeLog 3 (text "UNIFY" <+> text a <+> text "WITH" <+> pretty t <+> text "PRODUCING" <+> pretty t')
    return (a, t')
    
-- Predicate well-formedness: shapeless or simple depending on type variables  
processPredicate c@(WellFormedPredicate env argSorts p) = do
  let typeVars = Set.toList $ Set.unions $ map typeVarsOfSort argSorts
  if any isFreeVariable typeVars
    then do
      writeLog 3 $ text "WARNING: free vars in predicate" <+> pretty c
      modify $ addTypingConstraint c -- Still has type variables: cannot determine shape
      return Map.empty
    else do
      let u = p
      let subst = Map.singleton p (Unknown Map.empty u)
      addPredAssignment p (Unknown Map.empty u)
      let args = zipWith Var argSorts deBrujns
      let vars = allScalars env
      pq <- asks _predQualsGen
      addQuals u (pq (addAllVariables args env) args vars)
      return subst
  where
    isFreeVariable a = not (isBound env a)
processPredicate c = modify (addTypingConstraint c) >> return Map.empty

-- | Eliminate type and predicate variables from simple constraints, create qualifier maps, split measure-based subtyping constraints
processConstraint :: MonadHorn s => Constraint -> TCSolver s ()
processConstraint c@(Subtype env (ScalarT baseTL l) (ScalarT baseTR r) False label) | baseTL == baseTR
  = if l == ffalse || r == ftrue
      then return ()
      else do
        pass <- use predAssignment
        let subst = substitutePredicate pass
        let l' = subst l
        let r' = subst r
        let c' = Subtype env (ScalarT baseTL l') (ScalarT baseTR r') False label
        if Set.null $ (predsOf l' `Set.union` predsOf r') Set.\\ (Map.keysSet $ allPredicates env)
            then case baseTL of -- Subtyping of datatypes: try splitting into individual constraints between measures
                  DatatypeT dtName _ _ -> do
                    let measures = Map.keysSet $ allMeasuresOf dtName env
                    let isAbstract = null $ ((env ^. datatypes) Map.! dtName) ^. constructors
                    let vals = filter (\v -> varName v == valueVarName) . Set.toList . varsOf $ r'
                    let rConjuncts = conjunctsOf r'
                    doSplit <- asks _tcSolverSplitMeasures
                    if not doSplit || isAbstract || null vals || (not . Set.null . unknownsOf) (l' |&| r') -- TODO: unknowns can be split if we know their potential valuations
                      then simpleConstraints %= (c' :) -- Constraint has unknowns (or RHS doesn't contain _v)
                      else case splitByPredicate measures (head vals) (Set.toList rConjuncts) of
                            Nothing -> simpleConstraints %= (c' :) -- RHS cannot be split, add whole thing
                            Just mr -> if rConjuncts `Set.isSubsetOf` (Set.unions $ Map.elems mr)
                                        then do
                                          let lConjuncts = conjunctsOf $ instantiateCons (head vals) l'
                                          case splitByPredicate measures (head vals) (Set.toList lConjuncts) of -- Every conjunct of RHS is about some `m _v` (where m in measures)
                                              Nothing -> simpleConstraints %= (c :) -- LHS cannot be split, add whole thing for now
                                              Just ml -> mapM_ (addSplitConstraint ml) (toDisjointGroups mr)
                                        else simpleConstraints %= (c' :) -- Some conjuncts of RHS are no covered (that is, do not contains _v), add whole thing                       
                  _ -> simpleConstraints %= (c' :)
          else modify $ addTypingConstraint c' -- Constraint contains free predicate: add back and wait until more type variables get unified, so predicate variables can be instantiated
  where
    instantiateCons val fml@(Binary Eq v (Cons _ _ _)) | v == val = conjunction $ instantiateConsAxioms env (Just val) fml
    instantiateCons _ fml = fml
    
    addSplitConstraint :: MonadHorn s => Map Id (Set Formula) -> (Set Id, Set Formula) -> TCSolver s ()
    addSplitConstraint ml (measures, rConjuncts) = do
      let rhs = conjunction rConjuncts
      let lhs = conjunction $ setConcatMap (\measure -> Map.findWithDefault Set.empty measure ml) measures
      let c' = Subtype env (ScalarT baseTL lhs) (ScalarT baseTR rhs) False label
      writeLog 3 $ text "addSplitConstraint" <+> pretty c'
      simpleConstraints %= (c' :)    
      
processConstraint (Subtype env (ScalarT baseTL l) (ScalarT baseTR r) True label) | baseTL == baseTR
  = do
      pass <- use predAssignment
      let subst = substitutePredicate pass
      let l' = subst l
      let r' = subst r
      if l' == ftrue || r' == ftrue
        then return ()
        else simpleConstraints %= (Subtype env (ScalarT baseTL l') (ScalarT baseTR r') True label :)
processConstraint (WellFormed env t@(ScalarT baseT fml)) 
  = case fml of
      Unknown _ u -> do
        qmap <- use qualifierMap
        tq <- asks _typeQualsGen
        -- Only add qualifiers if it's a new variable; multiple well-formedness constraints could have been added for constructors
        let env' = addVariable valueVarName t env
        when (not $ Map.member u qmap) $ addQuals u (tq env' (Var (toSort baseT) valueVarName) (allScalars env'))
      _ -> return ()
processConstraint (WellFormedCond env (Unknown _ u))
  = do
      cq <- asks _condQualsGen
      addQuals u (cq env (allScalars env))
processConstraint (WellFormedMatchCond env (Unknown _ u))
  = do
      mq <- asks _matchQualsGen
      addQuals u (mq env (allPotentialScrutinees env))
processConstraint c = error $ show $ text "processConstraint: not a simple constraint" <+> pretty c

generateHornClauses :: MonadHorn s => Constraint -> TCSolver s ()
generateHornClauses c@(Subtype env (ScalarT baseTL l) (ScalarT baseTR r) False label) | baseTL == baseTR
  = do
      qmap <- use qualifierMap
      let relevantVars = potentialVars qmap (l |&| r)
      emb <- embedding env relevantVars True
      clauses <- lift . lift . lift $ preprocessConstraint (conjunction (Set.insert l emb) |=>| r)
      hornClauses %= (zip clauses (repeat label) ++)
generateHornClauses (Subtype env (ScalarT baseTL l) (ScalarT baseTR r) True _) | baseTL == baseTR
  = do
      qmap <- use qualifierMap
      let relevantVars = potentialVars qmap (l |&| r)
      emb <- embedding env relevantVars False
      let clause = conjunction (Set.insert l $ Set.insert r emb)
      consistencyChecks %= (clause :)
generateHornClauses c = error $ show $ text "generateHornClauses: not a simple subtyping constraint" <+> pretty c          

-- | 'allScalars' @env@ : logic terms for all scalar symbols in @env@
allScalars :: Environment -> [Formula]
allScalars env = catMaybes $ map toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (_, ForallT _ _) = Nothing
    toFormula (x, _) | x `Set.member` (env ^. letBound) = Nothing
    toFormula (x, Monotype t) = case t of
      ScalarT IntT  (Binary Eq _ (IntLit n)) -> Just $ IntLit n
      ScalarT BoolT (Var _ _) -> Just $ BoolLit True
      ScalarT BoolT (Unary Not (Var _ _)) -> Just $ BoolLit False
      ScalarT (DatatypeT dt [] []) (Binary Eq _ cons@(Cons _ name [])) | x == name -> Just cons
      ScalarT b _ -> Just $ Var (toSort b) x
      _ -> Nothing    
    
-- | 'allPotentialScrutinees' @env@ : logic terms for all scalar symbols in @env@
allPotentialScrutinees :: Environment -> [Formula]
allPotentialScrutinees env = catMaybes $ map toFormula $ Map.toList $ symbolsOfArity 0 env
  where
    toFormula (x, Monotype t) = case t of
      ScalarT b@(DatatypeT _ _ _) _ ->
        if Set.member x (env ^. unfoldedVars) && not (Program (PSymbol x) t `elem` (env ^. usedScrutinees))
          then Just $ Var (toSort b) x
          else Nothing
      _ -> Nothing 
    toFormula _ = Nothing
    
hasPotentialScrutinees :: Monad s => Environment -> TCSolver s Bool
hasPotentialScrutinees env = do
  return $ not $ null $ allPotentialScrutinees env
  
-- | Assumptions encoded in an environment    
embedding :: Monad s => Environment -> Set Id -> Bool -> TCSolver s (Set Formula)
embedding env vars includeQuantified = do
    -- tass <- use typeAssignment
    pass <- use predAssignment
    qmap <- use qualifierMap
    let ass = Set.map (substitutePredicate pass) $ (env ^. assumptions)
    let allVars = vars `Set.union` potentialVars qmap (conjunction ass)
    return $ addBindings env pass qmap ass allVars    
  where
    addBindings env pass qmap fmls vars = 
      if Set.null vars
        then fmls
        else let (x, rest) = Set.deleteFindMin vars in
              case Map.lookup x (allSymbols env) of
                Nothing -> addBindings env pass qmap fmls rest -- Variable not found (useful to ignore value variables)
                Just (Monotype t) -> case t of
                  ScalarT baseT fml -> 
                    let fmls' = Set.fromList $ map (substitute (Map.singleton valueVarName (Var (toSort baseT) x)) . substitutePredicate pass)
                                          (fml : allMeasurePostconditions includeQuantified baseT env) in
                    let newVars = Set.delete x $ setConcatMap (potentialVars qmap) fmls' in
                    addBindings env pass qmap (fmls `Set.union` fmls') (rest `Set.union` newVars)
                  LetT y tDef tBody -> addBindings (addVariable x tBody . addVariable y tDef . removeVariable x $ env) pass qmap fmls vars
                  AnyT -> Set.singleton ffalse
                  _ -> error $ unwords ["embedding: encountered non-scalar variable", x, "in 0-arity bucket"]
                Just sch -> addBindings env pass qmap fmls rest -- TODO: why did this work before?
    allSymbols env = symbolsOfArity 0 env
    
bottomValuation :: QMap -> Formula -> Formula
bottomValuation qmap fml = applySolution bottomSolution fml
  where
    unknowns = Set.toList $ unknownsOf fml
    bottomSolution = Map.fromList $ zip (map unknownName unknowns) (map (Set.fromList . lookupQualsSubst qmap) unknowns)

-- | 'potentialVars' @qmap fml@ : variables of @fml@ if all unknowns get strongest valuation according to @quals@    
potentialVars :: QMap -> Formula -> Set Id
potentialVars qmap fml = Set.map varName $ varsOf $ bottomValuation qmap fml

-- | 'freshId' @prefix@ : fresh identifier starting with @prefix@
freshId :: Monad s => String -> TCSolver s String
freshId prefix = do
  i <- uses idCount (Map.findWithDefault 0 prefix)
  idCount %= Map.insert prefix (i + 1)
  return $ prefix ++ show i

freshVar :: Monad s => Environment -> String -> TCSolver s String 
freshVar env prefix = do
  x <- freshId prefix
  if Map.member x (allSymbols env)
    then freshVar env prefix
    else return x

-- | 'fresh' @t@ : a type with the same shape as @t@ but fresh type variables, fresh predicate variables, and fresh unknowns as refinements
fresh :: Monad s => Environment -> RType -> TCSolver s RType
fresh env (ScalarT (TypeVarT vSubst a) _) | not (isBound env a) = do
  -- Free type variable: replace with fresh free type variable
  a' <- freshId "A"
  return $ ScalarT (TypeVarT vSubst a') ftrue
fresh env (ScalarT baseT _) = do
  baseT' <- freshBase baseT
  -- Replace refinement with fresh predicate unknown:
  k <- freshId "U"
  return $ ScalarT baseT' (Unknown Map.empty k)
  where
    freshBase (DatatypeT name tArgs _) = do
      -- Replace type arguments with fresh types:
      tArgs' <- mapM (fresh env) tArgs
      -- Replace predicate arguments with fresh predicate variables:
      let (DatatypeDef tParams pParams _ _ _) = (env ^. datatypes) Map.! name
      pArgs' <- mapM (\sig -> freshPred env . map (noncaptureSortSubst tParams (map (toSort . baseTypeOf) tArgs')) . predSigArgSorts $ sig) pParams  
      return $ DatatypeT name tArgs' pArgs'
    freshBase baseT = return baseT
fresh env (FunctionT x tArg tFun) = do
  liftM2 (FunctionT x) (fresh env tArg) (fresh env tFun)
fresh env t = let (env', t') = embedContext env t in fresh env' t'
  
freshPred env sorts = do
  p' <- freshId "P"
  modify $ addTypingConstraint (WellFormedPredicate env sorts p')
  let args = zipWith Var sorts deBrujns 
  return $ Pred BoolS p' args  
  
-- addTypeAssignment tv t = typeAssignment %= Map.insert tv t
addPredAssignment p fml = predAssignment %= Map.insert p fml  
  
addQuals :: MonadHorn s => Id -> QSpace -> TCSolver s ()
addQuals name quals = do
  quals' <- lift . lift . lift $ pruneQualifiers quals
  qualifierMap %= Map.insert name quals'
  
-- | Add unknown @name@ with valuation @valuation@ to solutions of all candidates  
addFixedUnknown :: MonadHorn s => Id -> Set Formula -> TCSolver s ()  
addFixedUnknown name valuation = do
    addQuals name (toSpace Nothing (Set.toList valuation))
    candidates %= map update
  where
    update cand = cand { solution = Map.insert name valuation (solution cand) }
    
-- | Set valuation of unknown @name@ to @valuation@
-- and re-check all potentially affected constraints in all candidates 
setUnknownRecheck :: MonadHorn s => Id -> Set Formula -> Set Id -> TCSolver s ()
setUnknownRecheck name valuation duals = do
  writeLog 3 $ text "Re-checking candidates after updating" <+> text name
  cands@(cand:_) <- use candidates
  let clauses = Set.filter (\fml -> name `Set.member` (Set.map unknownName (unknownsOf fml))) (validConstraints cand) -- First candidate cannot have invalid constraints
  let cands' = map (\c -> c { solution = Map.insert name valuation (solution c) }) cands
  env <- use initEnv
  cands'' <- lift . lift . lift $ checkCandidates False (Set.toList clauses) (instantiateConsAxioms env Nothing) cands'
    
  if null cands''
    then throwError $ text "Re-checking candidates failed"
    else do
      let liveClauses = Set.filter (\fml -> duals `disjoint` (Set.map unknownName (unknownsOf fml))) (validConstraints cand)
      candidates .= map (\c -> c { 
                                  validConstraints = Set.intersection liveClauses (validConstraints c), 
                                  invalidConstraints = Set.intersection liveClauses (invalidConstraints c) }) cands'' -- Remove Horn clauses produced by now eliminated code
  
-- | 'instantiateConsAxioms' @env fml@ : If @fml@ contains constructor applications, return the set of instantiations of constructor axioms for those applications in the environment @env@ 
instantiateConsAxioms :: Environment -> Maybe Formula -> Formula -> Set Formula  
instantiateConsAxioms env mVal fml = let inst = instantiateConsAxioms env mVal in
  case fml of
    Cons resS@(DataS dtName _) ctor args -> Set.unions $ Set.fromList (map (measureAxiom resS ctor args) (Map.elems $ allMeasuresOf dtName env)) : 
                                                         map (instantiateConsAxioms env Nothing) args
    Unary op e -> inst e
    Binary op e1 e2 -> inst e1 `Set.union` inst e2
    Ite e0 e1 e2 -> inst e0 `Set.union` inst e1 `Set.union` inst e2
    SetLit _ elems -> Set.unions (map inst elems)
    SetComp _ e -> inst e
    Pred _ p args -> Set.unions $ map inst args
    _ -> Set.empty  
  where
    measureAxiom resS ctor args (MeasureDef inSort _ defs _) = 
      let 
        MeasureCase _ vars body = head $ filter (\(MeasureCase c _ _) -> c == ctor) defs
        sParams = map varSortName (sortArgsOf inSort) -- sort parameters in the datatype declaration
        sArgs = sortArgsOf resS -- actual sort argument in the constructor application
        body' = noncaptureSortSubstFml sParams sArgs body -- measure definition with actual sorts for all subexpressions
        newValue = case mVal of
                      Nothing -> Cons resS ctor args
                      Just val -> val
        subst = Map.fromList $ (valueVarName, newValue) : zip vars args -- substitute formals for actuals and constructor application or provided value for _v    
      in substitute subst body'
    
-- | 'matchConsType' @formal@ @actual@ : unify constructor return type @formal@ with @actual@
matchConsType formal@(ScalarT (DatatypeT d vars pVars) _) actual@(ScalarT (DatatypeT d' args pArgs) _) | d == d' 
  = do
      writeLog 3 $ text "Matching constructor type" $+$ pretty formal $+$ text "with scrutinee" $+$ pretty actual
      subst <- foldM (\accSubst ((ScalarT (TypeVarT _ a) (BoolLit True)),t) -> do
        let subst' = Map.insert a t accSubst
        typeSubstituteConstraints subst'
        return subst'
        ) (Map.empty) (zip vars args) --addTypeAssignment a t) vars args
      pSubst <- foldM (\accSubst ((Pred BoolS p _), fml) -> do
        addPredAssignment p fml
        let psubst = Map.insert p fml accSubst
        -- predSubstituteConstraints psubst
        return psubst
        ) Map.empty (zip pVars pArgs)
      return (subst, pSubst)
matchConsType t t' = error $ show $ text "matchConsType: cannot match" <+> pretty t <+> text "against" <+> pretty t'

    
-- | Substitute type variables, predicate variables, and predicate unknowns in @t@
-- using current type assignment, predicate assignment, and liquid assignment
finalizeType :: Monad s => RType -> TCSolver s RType
finalizeType t = do
  -- tass <- use typeAssignment
  pass <- use predAssignment
  sol <- uses candidates (solution . head)
  return $ (typeApplySolution sol . typeSubstitutePred pass) t
    
-- | Substitute type variables, predicate variables, and predicate unknowns in @p@
-- using current type assignment, predicate assignment, and liquid assignment
finalizeProgram :: Monad s => RProgram -> TCSolver s RProgram
finalizeProgram p = do
  -- tass <- use typeAssignment
  pass <- use predAssignment
  sol <- uses candidates (solution . head)
  return $ fmap (typeApplySolution sol . typeSubstitutePred pass) p
  
instance Eq TypingState where
  (==) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (_idCount st1) == restrictDomain (Set.fromList ["a", "u"]) (_idCount st2)) &&
                  _candidates st1 == _candidates st2

instance Ord TypingState where
  (<=) st1 st2 = (restrictDomain (Set.fromList ["a", "u"]) (_idCount st1) <= restrictDomain (Set.fromList ["a", "u"]) (_idCount st2)) &&
                _candidates st1 <= _candidates st2  
  
writeLog level msg = do
  maxLevel <- asks _tcSolverLogLevel
  if level <= maxLevel then traceShow (plain msg) $ return () else return ()
  
updateConstraintEnv :: Environment -> Constraint -> Constraint
updateConstraintEnv env (Subtype _ typl typr flag id) = Subtype env typl typr flag id
updateConstraintEnv env (WellFormed _ typ) = WellFormed env typ
updateConstraintEnv env (WellFormedCond _ fml) = WellFormedCond env fml
updateConstraintEnv env (WellFormedMatchCond _ fml) = WellFormedMatchCond env fml
updateConstraintEnv env (WellFormedPredicate _ sorts id) = WellFormedPredicate env sorts id

isCondConstraint (WellFormedCond _ _) = True
isCondConstraint _ = False

updateAllConstraintsEnv :: MonadHorn s => Environment -> TCSolver s ()
updateAllConstraintsEnv env = do
  tcs <- use typingConstraints
  typingConstraints .= map (updateConstraintEnv env) tcs

typeSubstituteConstraints :: MonadHorn s => TypeSubstitution -> TCSolver s ()
typeSubstituteConstraints subst = do
  typingConstraints %= map (typeSubstituteConstraint subst)
  simpleConstraints %= map (typeSubstituteConstraint subst)

predSubstituteConstraints :: MonadHorn s => Substitution -> TCSolver s ()
predSubstituteConstraints pass = do
  -- typingConstraints %= map (predSubstituteConstraint pass)
  simpleConstraints %= map (predSubstituteConstraint pass)

-- | when there is a new type assignment, substitute it in all the constraints
typeSubstituteConstraint :: TypeSubstitution -> Constraint -> Constraint
typeSubstituteConstraint tass (Subtype env typl typr flag id) = Subtype (typeSubstituteEnv tass env) (typeSubstitute tass typl) (typeSubstitute tass typr) flag id
typeSubstituteConstraint tass (WellFormed env typ) = WellFormed (typeSubstituteEnv tass env) (typeSubstitute tass typ)
typeSubstituteConstraint tass (WellFormedCond env fml) = WellFormedCond (typeSubstituteEnv tass env) (sortSubstituteFml (asSortSubst tass) fml)
typeSubstituteConstraint tass (WellFormedMatchCond env fml) = WellFormedMatchCond (typeSubstituteEnv tass env) (sortSubstituteFml (asSortSubst tass) fml)
typeSubstituteConstraint tass (WellFormedPredicate env sorts id) = WellFormedPredicate (typeSubstituteEnv tass env) (map (sortSubstitute (asSortSubst tass)) sorts) id

predSubstituteConstraint ::  Substitution -> Constraint -> Constraint
predSubstituteConstraint pass (Subtype env typl typr flag id) = Subtype env (typeSubstitutePred pass typl) (typeSubstitutePred pass typr) flag id
predSubstituteConstraint pass (WellFormed env typ) = WellFormed env (typeSubstitutePred pass typ)
predSubstituteConstraint pass (WellFormedCond env fml) = WellFormedCond env (substitutePredicate pass fml)
predSubstituteConstraint pass (WellFormedMatchCond env fml) = WellFormedMatchCond env (substitutePredicate pass fml)
predSubstituteConstraint pass (WellFormedPredicate env sorts id) = WellFormedPredicate env sorts id