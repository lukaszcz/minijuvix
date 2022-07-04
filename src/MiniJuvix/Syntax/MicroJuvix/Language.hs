module MiniJuvix.Syntax.MicroJuvix.Language
  ( module MiniJuvix.Syntax.MicroJuvix.Language,
    module MiniJuvix.Syntax.Abstract.Name,
    module MiniJuvix.Syntax.Concrete.Loc,
    module MiniJuvix.Syntax.IsImplicit,
    module MiniJuvix.Syntax.Universe,
    module MiniJuvix.Syntax.Hole,
    module MiniJuvix.Syntax.Wildcard,
    module MiniJuvix.Syntax.Concrete.LiteralLoc,
    module MiniJuvix.Syntax.Concrete.Builtins,
  )
where

import MiniJuvix.Prelude
import MiniJuvix.Syntax.Abstract.Name
import MiniJuvix.Syntax.Concrete.Builtins
import MiniJuvix.Syntax.Concrete.LiteralLoc
import MiniJuvix.Syntax.Concrete.Loc
import MiniJuvix.Syntax.ForeignBlock
import MiniJuvix.Syntax.Hole
import MiniJuvix.Syntax.IsImplicit
import MiniJuvix.Syntax.Universe hiding (smallUniverse)
import MiniJuvix.Syntax.Wildcard

data Module = Module
  { _moduleName :: Name,
    _moduleBody :: ModuleBody
  }

newtype Include = Include
  { _includeModule :: Module
  }

newtype ModuleBody = ModuleBody
  { _moduleStatements :: [Statement]
  }

data Statement
  = StatementInductive InductiveDef
  | StatementFunction FunctionDef
  | StatementForeign ForeignBlock
  | StatementAxiom AxiomDef
  | StatementInclude Include

data AxiomDef = AxiomDef
  { _axiomName :: AxiomName,
    _axiomBuiltin :: Maybe BuiltinAxiom,
    _axiomType :: Expression
  }

data FunctionDef = FunctionDef
  { _funDefName :: FunctionName,
    _funDefType :: Expression,
    _funDefClauses :: NonEmpty FunctionClause,
    _funDefBuiltin :: Maybe BuiltinFunction
  }

data FunctionClause = FunctionClause
  { _clauseName :: FunctionName,
    _clausePatterns :: [Pattern],
    _clauseBody :: Expression
  }

data Iden
  = IdenFunction Name
  | IdenConstructor Name
  | IdenVar VarName
  | IdenAxiom Name
  | IdenInductive Name
  deriving stock (Eq, Generic)

instance Hashable Iden

data TypedExpression = TypedExpression
  { _typedType :: Expression,
    _typedExpression :: Expression
  }

data Expression
  = ExpressionIden Iden
  | ExpressionApplication Application
  | ExpressionFunction2 Function2
  | ExpressionLiteral LiteralLoc
  | ExpressionHole Hole
  | ExpressionUniverse SmallUniverse
  deriving stock (Eq, Generic)

instance Hashable Expression

data Application = Application
  { _appLeft :: Expression,
    _appRight :: Expression,
    _appImplicit :: IsImplicit
  }

-- TODO: Eq and Hashable instances ignore the _typAppImplicit field
--  to workaround a crash in Micro->Mono translation when looking up
-- a concrete type.
instance Eq Application where
  (Application l r _) == (Application l' r' _) = (l == l') && (r == r')

instance Hashable Application where
  hashWithSalt salt (Application l r _) = hashWithSalt salt (l, r)

-- | Fully applied constructor in a pattern.
data ConstructorApp = ConstructorApp
  { _constrAppConstructor :: Name,
    _constrAppParameters :: [Pattern]
  }

data Pattern
  = PatternVariable VarName
  | PatternConstructorApp ConstructorApp
  | PatternWildcard Wildcard
  | PatternBraces Pattern

newtype InductiveParameter = InductiveParameter
  { _inductiveParamName :: VarName
  }
  deriving stock (Eq)

data InductiveDef = InductiveDef
  { _inductiveName :: InductiveName,
    _inductiveBuiltin :: Maybe BuiltinInductive,
    _inductiveParameters :: [InductiveParameter],
    _inductiveConstructors :: [InductiveConstructorDef]
  }

data InductiveConstructorDef = InductiveConstructorDef
  { _constructorName :: ConstrName,
    _constructorParameters :: [Expression]
  }

-- TODO: Eq and Hashable instances ignore the _typAppImplicit field
--  to workaround a crash in Micro->Mono translation when looking up
-- a concrete type.
data FunctionParameter = FunctionParameter
  { _paramName :: Maybe VarName,
    _paramImplicit :: IsImplicit,
    _paramType :: Expression
  }
  deriving stock (Eq, Generic)

instance Hashable FunctionParameter

data Function2 = Function2
  { _function2Left :: FunctionParameter,
    _function2Right :: Expression
  }
  deriving stock (Eq, Generic)

instance Hashable Function2

makeLenses ''Module
makeLenses ''Include
makeLenses ''FunctionDef
makeLenses ''FunctionClause
makeLenses ''InductiveDef
makeLenses ''AxiomDef
makeLenses ''ModuleBody
makeLenses ''Application
makeLenses ''TypedExpression
makeLenses ''Function2
makeLenses ''FunctionParameter
makeLenses ''InductiveParameter
makeLenses ''InductiveConstructorDef
makeLenses ''ConstructorApp

instance HasAtomicity Application where
  atomicity = const (Aggregate appFixity)

instance HasAtomicity Expression where
  atomicity e = case e of
    ExpressionIden {} -> Atom
    ExpressionApplication a -> atomicity a
    ExpressionLiteral l -> atomicity l
    ExpressionHole {} -> Atom
    ExpressionUniverse u -> atomicity u
    ExpressionFunction2 f -> atomicity f

instance HasAtomicity Function2 where
  atomicity = const (Aggregate funFixity)

instance HasAtomicity ConstructorApp where
  atomicity (ConstructorApp _ args)
    | null args = Atom
    | otherwise = Aggregate appFixity

instance HasAtomicity Pattern where
  atomicity p = case p of
    PatternConstructorApp a -> atomicity a
    PatternVariable {} -> Atom
    PatternWildcard {} -> Atom
    PatternBraces {} -> Atom

instance HasLoc FunctionParameter where
  getLoc f = v (getLoc (f ^. paramType))
    where
      v = case getLoc <$> f ^. paramName of
        Nothing -> id
        Just i -> (i <>)

instance HasLoc Function2 where
  getLoc (Function2 l r) = getLoc l <> getLoc r

instance HasLoc Expression where
  getLoc = \case
    ExpressionIden i -> getLoc i
    ExpressionApplication a -> getLoc (a ^. appLeft)
    ExpressionLiteral l -> getLoc l
    ExpressionHole h -> getLoc h
    ExpressionUniverse u -> getLoc u
    ExpressionFunction2 u -> getLoc u

instance HasLoc Iden where
  getLoc = \case
    IdenFunction f -> getLoc f
    IdenConstructor c -> getLoc c
    IdenVar v -> getLoc v
    IdenAxiom a -> getLoc a
    IdenInductive a -> getLoc a

instance HasLoc Pattern where
  getLoc = \case
    PatternVariable v -> getLoc v
    PatternConstructorApp a -> getLoc a
    PatternBraces p -> getLoc p
    PatternWildcard i -> getLoc i

instance HasLoc ConstructorApp where
  getLoc (ConstructorApp c ps) =
    case last <$> nonEmpty ps of
      Just p -> getLoc c <> getLoc p
      Nothing -> getLoc c
