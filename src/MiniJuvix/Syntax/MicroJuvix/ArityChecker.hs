module MiniJuvix.Syntax.MicroJuvix.ArityChecker
  ( module MiniJuvix.Syntax.MicroJuvix.ArityChecker,
    module MiniJuvix.Syntax.MicroJuvix.MicroJuvixArityResult,
    module MiniJuvix.Syntax.MicroJuvix.ArityChecker.Error,
  )
where

import MiniJuvix.Internal.NameIdGen
import MiniJuvix.Prelude hiding (fromEither)
import MiniJuvix.Syntax.MicroJuvix.ArityChecker.Arity
import MiniJuvix.Syntax.MicroJuvix.ArityChecker.Error
import MiniJuvix.Syntax.MicroJuvix.ArityChecker.LocalVars
import MiniJuvix.Syntax.MicroJuvix.InfoTable
import MiniJuvix.Syntax.MicroJuvix.Language.Extra
import MiniJuvix.Syntax.MicroJuvix.MicroJuvixArityResult
import MiniJuvix.Syntax.MicroJuvix.MicroJuvixResult

entryMicroJuvixArity ::
  Members '[Error ArityCheckerError, NameIdGen] r =>
  MicroJuvixResult ->
  Sem r MicroJuvixArityResult
entryMicroJuvixArity res@MicroJuvixResult {..} = do
  r <- runReader table (mapM checkModule _resultModules)
  return
    MicroJuvixArityResult
      { _resultMicroJuvixResult = res,
        _resultModules = r
      }
  where
    table :: InfoTable
    table = buildTable _resultModules

checkModule ::
  Members '[Reader InfoTable, NameIdGen, Error ArityCheckerError] r =>
  Module ->
  Sem r Module
checkModule Module {..} = do
  _moduleBody' <- checkModuleBody _moduleBody
  return
    Module
      { _moduleBody = _moduleBody',
        ..
      }

checkModuleBody ::
  Members '[Reader InfoTable, NameIdGen, Error ArityCheckerError] r =>
  ModuleBody ->
  Sem r ModuleBody
checkModuleBody ModuleBody {..} = do
  _moduleStatements' <- mapM checkStatement _moduleStatements
  return
    ModuleBody
      { _moduleStatements = _moduleStatements'
      }

checkInclude ::
  Members '[Reader InfoTable, NameIdGen, Error ArityCheckerError] r =>
  Include ->
  Sem r Include
checkInclude = traverseOf includeModule checkModule

checkStatement ::
  Members '[Reader InfoTable, NameIdGen, Error ArityCheckerError] r =>
  Statement ->
  Sem r Statement
checkStatement s = case s of
  StatementFunction fun -> StatementFunction <$> checkFunctionDef fun
  StatementInclude i -> StatementInclude <$> checkInclude i
  StatementForeign {} -> return s
  StatementInductive {} -> return s
  StatementAxiom {} -> return s

checkFunctionDef ::
  Members '[Reader InfoTable, NameIdGen, Error ArityCheckerError] r =>
  FunctionDef ->
  Sem r FunctionDef
checkFunctionDef FunctionDef {..} = do
  arity <- typeArity _funDefType
  _funDefClauses' <- mapM (checkFunctionClause arity) _funDefClauses
  return
    FunctionDef
      { _funDefClauses = _funDefClauses',
        ..
      }

checkFunctionClause ::
  Members '[Reader InfoTable, NameIdGen, Error ArityCheckerError] r =>
  Arity ->
  FunctionClause ->
  Sem r FunctionClause
checkFunctionClause ari cl = do
  hint <- guessArity (cl ^. clauseBody)
  (patterns', locals, bodyAri) <- checkLhs loc hint ari (cl ^. clausePatterns)
  body' <- runReader locals (checkExpression bodyAri (cl ^. clauseBody))
  return
    FunctionClause
      { _clauseName = cl ^. clauseName,
        _clausePatterns = patterns',
        _clauseBody = body'
      }
  where
    name = cl ^. clauseName
    loc = getLoc name

guessArity ::
  forall r.
  Members '[Reader InfoTable] r =>
  Expression ->
  Sem r (Maybe Arity)
guessArity = \case
  ExpressionHole {} -> return Nothing
  ExpressionFunction {} -> return (Just ArityUnit)
  ExpressionLiteral {} -> return (Just arityLiteral)
  ExpressionApplication a -> appHelper a
  ExpressionIden i -> idenHelper i
  where
    idenHelper :: Iden -> Sem r (Maybe Arity)
    idenHelper i = case i of
      IdenVar {} -> return Nothing
      _ -> Just <$> runReader (LocalVars mempty) (idenArity i)

    appHelper :: Application -> Sem r (Maybe Arity)
    appHelper a = do
      f' <- arif
      return (f' >>= \f'' -> foldArity <$> refine (unfoldArity f'') args)
      where
        (f, args) = second (map fst . toList) (unfoldApplication' a)

        refine :: [ArityParameter] -> [IsImplicit] -> Maybe [ArityParameter]
        refine ps as = case (ps, as) of
          (ParamExplicit {} : ps', Explicit : as') -> refine ps' as'
          (ParamImplicit {} : ps', Implicit : as') -> refine ps' as'
          (ParamImplicit {} : ps', as'@(Explicit : _)) -> refine ps' as'
          (ParamExplicit {} : _, Implicit : _) -> Nothing
          (ps', []) -> Just ps'
          ([], _ : _) -> Nothing

        arif :: Sem r (Maybe Arity)
        arif = case f of
          ExpressionHole {} -> return Nothing
          ExpressionApplication {} -> impossible
          ExpressionFunction {} -> return (Just ArityUnit)
          ExpressionLiteral {} -> return (Just arityLiteral)
          ExpressionIden i -> idenHelper i

-- | The arity of all literals is assumed to be: {} -> 1
arityLiteral :: Arity
arityLiteral =
  ArityFunction
    FunctionArity
      { _functionArityLeft = ParamImplicit,
        _functionArityRight = ArityUnit
      }

checkLhs ::
  forall r.
  Members '[Reader InfoTable, NameIdGen, Error ArityCheckerError] r =>
  Interval ->
  Maybe Arity ->
  Arity ->
  [Pattern] ->
  Sem r ([Pattern], LocalVars, Arity)
checkLhs loc hint ariSignature pats = do
  (locals, (pats', bodyAri)) <- runState emptyLocalVars (goLhs ariSignature pats)
  return (pats', locals, bodyAri)
  where
    -- returns the expanded patterns and the rest of the Arity (the arity of the
    -- body once all the patterns have been processed).
    -- Does not insert holes greedily. I.e. implicit wildcards are only inserted
    -- between explicit parameters already in the pattern.
    goLhs :: Arity -> [Pattern] -> Sem (State LocalVars ': r) ([Pattern], Arity)
    goLhs a = \case
      [] -> return $ case hint >>= tailHelper a of
        Nothing -> ([], a)
        Just tailUnderscores ->
          let a' = foldArity (drop tailUnderscores (unfoldArity a))
           in (replicate tailUnderscores wildcard, a')
      lhs@(p : ps) -> case a of
        ArityUnit ->
          throw
            ( ErrLhsTooManyPatterns
                LhsTooManyPatterns
                  { _lhsTooManyPatternsRemaining = p :| ps
                  }
            )
        ArityUnknown -> do
          p' <- checkPattern ArityUnknown p
          first (p' :) <$> goLhs ArityUnknown ps
        ArityFunction (FunctionArity l r) ->
          case (getPatternBraces p, l) of
            (Just b, ParamImplicit) -> do
              b' <- checkPattern (arityParameter l) b
              first (b' :) <$> goLhs r ps
            (Just x, ParamExplicit {}) ->
              throw
                ( ErrExpectedExplicitPattern
                    ExpectedExplicitPattern
                      { _expectedExplicitPattern = x
                      }
                )
            (Nothing, ParamImplicit) ->
              first (wildcard :) <$> goLhs r lhs
            (Nothing, ParamExplicit pa) -> do
              p' <- checkPattern pa p
              first (p' :) <$> goLhs r ps
      where
        wildcard :: Pattern
        wildcard = PatternBraces (PatternWildcard (Wildcard loc))

    tailHelper :: Arity -> Arity -> Maybe Int
    tailHelper a target
      | notNull a' && all (== ParamImplicit) a' = Just (length a')
      | otherwise = Nothing
      where
        a' = dropSuffix target' (unfoldArity a)
        target' = unfoldArity target

    getPatternBraces :: Pattern -> Maybe Pattern
    getPatternBraces p = case p of
      PatternBraces {} -> Just p
      _ -> Nothing

checkPattern ::
  Members '[Reader InfoTable, Error ArityCheckerError, State LocalVars] r =>
  Arity ->
  Pattern ->
  Sem r Pattern
checkPattern ari = \case
  PatternBraces p -> checkPattern ari p
  PatternVariable v -> addArity v ari $> PatternVariable v
  PatternWildcard i -> return (PatternWildcard i)
  PatternConstructorApp c -> case ari of
    ArityUnit -> PatternConstructorApp <$> checkConstructorApp c
    ArityUnknown -> PatternConstructorApp <$> checkConstructorApp c
    ArityFunction {} ->
      throw
        ( ErrPatternFunction
            PatternFunction
              { _patternFunction = c
              }
        )

checkConstructorApp ::
  forall r.
  Members '[Reader InfoTable, Error ArityCheckerError, State LocalVars] r =>
  ConstructorApp ->
  Sem r ConstructorApp
checkConstructorApp ca@(ConstructorApp c ps) = do
  args <- (^. constructorInfoArgs) <$> lookupConstructor c
  arities <- mapM typeArity args
  let n = length arities
      lps = length ps
  when
    (n /= lps)
    ( throw
        ( ErrWrongConstructorAppLength
            WrongConstructorAppLength
              { _wrongConstructorAppLength = ca,
                _wrongConstructorAppLengthExpected = n
              }
        )
    )
  ps' <- zipWithM checkPattern arities ps
  return (ConstructorApp c ps')

idenArity :: Members '[Reader LocalVars, Reader InfoTable] r => Iden -> Sem r Arity
idenArity = \case
  IdenFunction f -> lookupFunction f >>= typeArity . (^. functionInfoDef . funDefType)
  IdenConstructor c -> constructorType c >>= typeArity
  IdenVar v -> getLocalArity v
  IdenAxiom a -> lookupAxiom a >>= typeArity . (^. axiomInfoType)
  IdenInductive i -> inductiveType i >>= typeArity

typeArity :: forall r. Members '[Reader InfoTable] r => Type -> Sem r Arity
typeArity = go
  where
    go :: Type -> Sem r Arity
    go = \case
      TypeIden i -> goIden i
      TypeApp {} -> return ArityUnit
      TypeFunction f -> ArityFunction <$> goFun f
      TypeAbs f -> ArityFunction <$> goAbs f
      TypeHole {} -> return ArityUnknown
      TypeUniverse {} -> return ArityUnit

    goIden :: TypeIden -> Sem r Arity
    goIden = \case
      TypeIdenVariable {} -> return ArityUnknown
      TypeIdenInductive {} -> return ArityUnit
      TypeIdenAxiom ax -> do
        ty <- (^. axiomInfoType) <$> lookupAxiom ax
        go ty

    goFun :: Function -> Sem r FunctionArity
    goFun (Function l r) = do
      l' <- ParamExplicit <$> go l
      r' <- go r
      return
        FunctionArity
          { _functionArityLeft = l',
            _functionArityRight = r'
          }
    goAbs :: TypeAbstraction -> Sem r FunctionArity
    goAbs t = do
      r' <- go (t ^. typeAbsBody)
      return (FunctionArity l r')
      where
        l :: ArityParameter
        l = case t ^. typeAbsImplicit of
          Implicit -> ParamImplicit
          Explicit -> ParamExplicit ArityUnit

checkExpression ::
  forall r.
  Members '[Reader InfoTable, NameIdGen, Error ArityCheckerError, Reader LocalVars] r =>
  Arity ->
  Expression ->
  Sem r Expression
checkExpression hintArity expr = case expr of
  ExpressionIden {} -> appHelper expr []
  ExpressionApplication a -> goApp a
  ExpressionLiteral {} -> appHelper expr []
  ExpressionFunction {} -> return expr
  ExpressionHole {} -> return expr
  where
    goApp :: Application -> Sem r Expression
    goApp = uncurry appHelper . second toList . unfoldApplication'

    appHelper :: Expression -> [(IsImplicit, Expression)] -> Sem r Expression
    appHelper fun args = do
      args' :: [(IsImplicit, Expression)] <- case fun of
        ExpressionHole {} -> mapM (secondM (checkExpression ArityUnknown)) args
        ExpressionIden i -> idenArity i >>= helper (getLoc i)
        ExpressionLiteral l -> helper (getLoc l) arityLiteral
        ExpressionFunction f ->
          throw
            ( ErrFunctionApplied
                FunctionApplied
                  { _functionAppliedFunction = f,
                    _functionAppliedArguments = args
                  }
            )
        ExpressionApplication {} -> impossible
      return (foldApplication fun args')
      where
        helper :: Interval -> Arity -> Sem r [(IsImplicit, Expression)]
        helper i ari = do
          let argsAris :: [Arity]
              argsAris = map toArity (unfoldArity ari)
              toArity :: ArityParameter -> Arity
              toArity = \case
                ParamExplicit a -> a
                ParamImplicit -> ArityUnit
          mapM
            (secondM (uncurry checkExpression))
            [(i', (a, e')) | (a, (i', e')) <- zip (argsAris ++ repeat ArityUnknown) args]
            >>= addHoles i hintArity ari
        addHoles ::
          Interval ->
          Arity ->
          Arity ->
          [(IsImplicit, Expression)] ->
          Sem r [(IsImplicit, Expression)]
        addHoles loc hint = go 0
          where
            go ::
              Int ->
              Arity ->
              [(IsImplicit, Expression)] ->
              Sem r [(IsImplicit, Expression)]
            go idx ari goargs = case (ari, goargs) of
              (ArityFunction (FunctionArity ParamImplicit r), (Implicit, e) : rest) ->
                ((Implicit, e) :) <$> go (succ idx) r rest
              (ArityFunction (FunctionArity (ParamExplicit {}) r), (Explicit, e) : rest) ->
                ((Explicit, e) :) <$> go (succ idx) r rest
              (ArityFunction (FunctionArity ParamImplicit _), [])
                -- When there are no remaining arguments and the expected arity of the
                -- expression matches the current arity we should *not* insert a hole.
                | ari == hint -> return []
              (ArityFunction (FunctionArity ParamImplicit r), _) -> do
                h <- newHole loc
                ((Implicit, ExpressionHole h) :) <$> go (succ idx) r goargs
              (ArityFunction (FunctionArity (ParamExplicit {}) _), (Implicit, _) : _) ->
                throw
                  ( ErrExpectedExplicitArgument
                      ExpectedExplicitArgument
                        { _expectedExplicitArgumentApp = (fun, args),
                          _expectedExplicitArgumentIx = idx
                        }
                  )
              (ArityUnit, []) -> return []
              (ArityFunction (FunctionArity (ParamExplicit _) _), []) -> return []
              (ArityUnit, _ : _) ->
                throw
                  ( ErrTooManyArguments
                      TooManyArguments
                        { _tooManyArgumentsApp = (fun, args),
                          _tooManyArgumentsUnexpected = length goargs
                        }
                  )
              (ArityUnknown, []) -> return []
              (ArityUnknown, p : ps) -> (p :) <$> go (succ idx) ArityUnknown ps

newHole :: Member NameIdGen r => Interval -> Sem r Hole
newHole loc = (`Hole` loc) <$> freshNameId
