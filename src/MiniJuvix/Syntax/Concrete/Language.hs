{-# LANGUAGE UndecidableInstances #-}

module MiniJuvix.Syntax.Concrete.Language
  ( module MiniJuvix.Syntax.Concrete.Language,
    module MiniJuvix.Syntax.Concrete.Name,
    module MiniJuvix.Syntax.Concrete.Scoped.NameRef,
    module MiniJuvix.Syntax.Concrete.Builtins,
    module MiniJuvix.Syntax.Concrete.Loc,
    module MiniJuvix.Syntax.Hole,
    module MiniJuvix.Syntax.Concrete.LiteralLoc,
    module MiniJuvix.Syntax.IsImplicit,
    module MiniJuvix.Syntax.Backends,
    module MiniJuvix.Syntax.ForeignBlock,
    module MiniJuvix.Syntax.Concrete.Scoped.VisibilityAnn,
    module MiniJuvix.Syntax.Concrete.PublicAnn,
    module MiniJuvix.Syntax.Concrete.ModuleIsTop,
    module MiniJuvix.Syntax.Concrete.Language.Stage,
    module MiniJuvix.Syntax.Wildcard,
    module MiniJuvix.Syntax.Fixity,
    module MiniJuvix.Syntax.Usage,
    module MiniJuvix.Syntax.Universe,
  )
where

import Data.Kind qualified as GHC
import MiniJuvix.Prelude hiding (show)
import MiniJuvix.Syntax.Backends
import MiniJuvix.Syntax.Concrete.Builtins
import MiniJuvix.Syntax.Concrete.Language.Stage
import MiniJuvix.Syntax.Concrete.LiteralLoc
import MiniJuvix.Syntax.Concrete.Loc
import MiniJuvix.Syntax.Concrete.ModuleIsTop
import MiniJuvix.Syntax.Concrete.Name
import MiniJuvix.Syntax.Concrete.PublicAnn
import MiniJuvix.Syntax.Concrete.Scoped.Name (unqualifiedSymbol)
import MiniJuvix.Syntax.Concrete.Scoped.Name qualified as S
import MiniJuvix.Syntax.Concrete.Scoped.Name.NameKind
import MiniJuvix.Syntax.Concrete.Scoped.NameRef
import MiniJuvix.Syntax.Concrete.Scoped.VisibilityAnn
import MiniJuvix.Syntax.Fixity
import MiniJuvix.Syntax.ForeignBlock
import MiniJuvix.Syntax.Hole
import MiniJuvix.Syntax.IsImplicit
import MiniJuvix.Syntax.Universe
import MiniJuvix.Syntax.Usage
import MiniJuvix.Syntax.Wildcard
import Prelude (show)

--------------------------------------------------------------------------------
-- Parsing stages
--------------------------------------------------------------------------------

type SymbolType :: Stage -> GHC.Type
type family SymbolType s = res | res -> s where
  SymbolType 'Parsed = Symbol
  SymbolType 'Scoped = S.Symbol

type ModuleRefType :: Stage -> GHC.Type
type family ModuleRefType s = res | res -> s where
  ModuleRefType 'Parsed = Name
  ModuleRefType 'Scoped = ModuleRef

type IdentifierType :: Stage -> GHC.Type
type family IdentifierType s = res | res -> s where
  IdentifierType 'Parsed = Name
  IdentifierType 'Scoped = ScopedIden

type HoleType :: Stage -> GHC.Type
type family HoleType s = res | res -> s where
  HoleType 'Parsed = Interval
  HoleType 'Scoped = Hole

type PatternAtomIdenType :: Stage -> GHC.Type
type family PatternAtomIdenType s = res | res -> s where
  PatternAtomIdenType 'Parsed = Name
  PatternAtomIdenType 'Scoped = PatternScopedIden

type ExpressionType :: Stage -> GHC.Type
type family ExpressionType s = res | res -> s where
  ExpressionType 'Parsed = ExpressionAtoms 'Parsed
  ExpressionType 'Scoped = Expression

type PatternType :: Stage -> GHC.Type
type family PatternType s = res | res -> s where
  PatternType 'Parsed = PatternAtom 'Parsed
  PatternType 'Scoped = Pattern

type family ImportType (s :: Stage) :: GHC.Type where
  ImportType 'Parsed = TopModulePath
  ImportType 'Scoped = Module 'Scoped 'ModuleTop

type ModulePathType :: Stage -> ModuleIsTop -> GHC.Type
type family ModulePathType s t = res | res -> t s where
  ModulePathType 'Parsed 'ModuleTop = TopModulePath
  ModulePathType 'Scoped 'ModuleTop = S.TopModulePath
  ModulePathType 'Parsed 'ModuleLocal = Symbol
  ModulePathType 'Scoped 'ModuleLocal = S.Symbol

--------------------------------------------------------------------------------
-- Top level statement
--------------------------------------------------------------------------------

data Statement (s :: Stage)
  = StatementOperator OperatorSyntaxDef
  | StatementTypeSignature (TypeSignature s)
  | StatementImport (Import s)
  | StatementInductive (InductiveDef s)
  | StatementModule (Module s 'ModuleLocal)
  | StatementOpenModule (OpenModule s)
  | StatementFunctionClause (FunctionClause s)
  | StatementAxiom (AxiomDef s)
  | StatementEval (Eval s)
  | StatementPrint (Print s)
  | StatementForeign ForeignBlock
  | StatementCompile (Compile s)

deriving stock instance
  ( Show (ImportType s),
    Show (ModulePathType s 'ModuleLocal),
    Show (PatternType s),
    Show (SymbolType s),
    Show (IdentifierType s),
    Show (ModuleRefType s),
    Show (ExpressionType s)
  ) =>
  Show (Statement s)

deriving stock instance
  ( Eq (ImportType s),
    Eq (PatternType s),
    Eq (ModulePathType s 'ModuleLocal),
    Eq (SymbolType s),
    Eq (IdentifierType s),
    Eq (ModuleRefType s),
    Eq (ExpressionType s)
  ) =>
  Eq (Statement s)

deriving stock instance
  ( Ord (ImportType s),
    Ord (PatternType s),
    Ord (ModulePathType s 'ModuleLocal),
    Ord (SymbolType s),
    Ord (IdentifierType s),
    Ord (ModuleRefType s),
    Ord (ExpressionType s)
  ) =>
  Ord (Statement s)

--------------------------------------------------------------------------------
-- Import statement
--------------------------------------------------------------------------------

newtype Import (s :: Stage) = Import
  { _importModule :: ImportType s
  }

deriving stock instance (Show (ImportType s)) => Show (Import s)

deriving stock instance (Eq (ImportType s)) => Eq (Import s)

deriving stock instance (Ord (ImportType s)) => Ord (Import s)

instance HasLoc (Import 'Parsed) where
  getLoc (Import t) = getLoc t

--------------------------------------------------------------------------------
-- Operator syntax declaration
--------------------------------------------------------------------------------

data OperatorSyntaxDef = OperatorSyntaxDef
  { _opSymbol :: Symbol,
    _opFixity :: Fixity
  }
  deriving stock (Show, Eq, Ord)

instance HasLoc OperatorSyntaxDef where
  getLoc OperatorSyntaxDef {..} = getLoc _opSymbol

-------------------------------------------------------------------------------
-- Type signature declaration
-------------------------------------------------------------------------------

data TypeSignature (s :: Stage) = TypeSignature
  { _sigName :: FunctionName s,
    _sigType :: ExpressionType s,
    _sigBuiltin :: Maybe BuiltinFunction,
    _sigTerminating :: Bool
  }

deriving stock instance (Show (ExpressionType s), Show (SymbolType s)) => Show (TypeSignature s)

deriving stock instance (Eq (ExpressionType s), Eq (SymbolType s)) => Eq (TypeSignature s)

deriving stock instance (Ord (ExpressionType s), Ord (SymbolType s)) => Ord (TypeSignature s)

-------------------------------------------------------------------------------
-- Axioms
-------------------------------------------------------------------------------

data AxiomDef (s :: Stage) = AxiomDef
  { _axiomName :: SymbolType s,
    _axiomBuiltin :: Maybe BuiltinAxiom,
    _axiomType :: ExpressionType s
  }

deriving stock instance (Show (ExpressionType s), Show (SymbolType s)) => Show (AxiomDef s)

deriving stock instance (Eq (ExpressionType s), Eq (SymbolType s)) => Eq (AxiomDef s)

deriving stock instance (Ord (ExpressionType s), Ord (SymbolType s)) => Ord (AxiomDef s)

-------------------------------------------------------------------------------
-- Lift type construction declaration
-------------------------------------------------------------------------------

type InductiveConstructorName s = SymbolType s

type InductiveName s = SymbolType s

data InductiveConstructorDef (s :: Stage) = InductiveConstructorDef
  { _constructorName :: InductiveConstructorName s,
    _constructorType :: ExpressionType s
  }

deriving stock instance (Show (ExpressionType s), Show (SymbolType s)) => Show (InductiveConstructorDef s)

deriving stock instance (Eq (ExpressionType s), Eq (SymbolType s)) => Eq (InductiveConstructorDef s)

deriving stock instance (Ord (ExpressionType s), Ord (SymbolType s)) => Ord (InductiveConstructorDef s)

data InductiveParameter (s :: Stage) = InductiveParameter
  { _inductiveParameterName :: SymbolType s,
    _inductiveParameterType :: ExpressionType s
  }

deriving stock instance (Show (ExpressionType s), Show (SymbolType s)) => Show (InductiveParameter s)

deriving stock instance (Eq (ExpressionType s), Eq (SymbolType s)) => Eq (InductiveParameter s)

deriving stock instance (Ord (ExpressionType s), Ord (SymbolType s)) => Ord (InductiveParameter s)

data InductiveDef (s :: Stage) = InductiveDef
  { _inductiveBuiltin :: Maybe BuiltinInductive,
    _inductiveName :: InductiveName s,
    _inductiveParameters :: [InductiveParameter s],
    _inductiveType :: Maybe (ExpressionType s),
    _inductiveConstructors :: [InductiveConstructorDef s]
  }

deriving stock instance (Show (ExpressionType s), Show (SymbolType s)) => Show (InductiveDef s)

deriving stock instance (Eq (ExpressionType s), Eq (SymbolType s)) => Eq (InductiveDef s)

deriving stock instance (Ord (ExpressionType s), Ord (SymbolType s)) => Ord (InductiveDef s)

--------------------------------------------------------------------------------
-- Pattern
--------------------------------------------------------------------------------

data PatternApp = PatternApp
  { _patAppLeft :: Pattern,
    _patAppRight :: Pattern
  }
  deriving stock (Show, Eq, Ord)

data PatternInfixApp = PatternInfixApp
  { _patInfixLeft :: Pattern,
    _patInfixConstructor :: ConstructorRef,
    _patInfixRight :: Pattern
  }
  deriving stock (Show, Eq, Ord)

instance HasFixity PatternInfixApp where
  getFixity (PatternInfixApp _ op _) = fromMaybe impossible (op ^. constructorRefName . S.nameFixity)

data PatternPostfixApp = PatternPostfixApp
  { _patPostfixParameter :: Pattern,
    _patPostfixConstructor :: ConstructorRef
  }
  deriving stock (Show, Eq, Ord)

instance HasFixity PatternPostfixApp where
  getFixity (PatternPostfixApp _ op) = fromMaybe impossible (op ^. constructorRefName . S.nameFixity)

data Pattern
  = PatternVariable (SymbolType 'Scoped)
  | PatternConstructor ConstructorRef
  | PatternApplication PatternApp
  | PatternInfixApplication PatternInfixApp
  | PatternPostfixApplication PatternPostfixApp
  | PatternBraces Pattern
  | PatternWildcard Wildcard
  | PatternEmpty
  deriving stock (Show, Eq, Ord)

instance HasAtomicity Pattern where
  atomicity e = case e of
    PatternVariable {} -> Atom
    PatternConstructor {} -> Atom
    PatternApplication {} -> Aggregate appFixity
    PatternInfixApplication a -> Aggregate (getFixity a)
    PatternPostfixApplication p -> Aggregate (getFixity p)
    PatternWildcard {} -> Atom
    PatternBraces {} -> Atom
    PatternEmpty -> Atom

--------------------------------------------------------------------------------
-- Pattern section
--------------------------------------------------------------------------------

data PatternScopedIden
  = PatternScopedVar S.Symbol
  | PatternScopedConstructor ConstructorRef
  deriving stock (Show, Ord, Eq)

data PatternAtom (s :: Stage)
  = PatternAtomIden (PatternAtomIdenType s)
  | PatternAtomWildcard Wildcard
  | PatternAtomEmpty
  | PatternAtomParens (PatternAtoms s)
  | PatternAtomBraces (PatternAtoms s)

data PatternAtoms (s :: Stage) = PatternAtoms
  { _patternAtoms :: NonEmpty (PatternAtom s),
    _patternAtomsLoc :: Interval
  }

--------------------------------------------------------------------------------
-- Function binding declaration
--------------------------------------------------------------------------------

type FunctionName s = SymbolType s

data FunctionClause (s :: Stage) = FunctionClause
  { _clauseOwnerFunction :: FunctionName s,
    _clausePatterns :: [PatternType s],
    _clauseBody :: ExpressionType s,
    _clauseWhere :: Maybe (WhereBlock s)
  }

deriving stock instance
  ( Show (PatternType s),
    Show (IdentifierType s),
    Show (ModuleRefType s),
    Show (SymbolType s),
    Show (ExpressionType s)
  ) =>
  Show (FunctionClause s)

deriving stock instance
  ( Eq (PatternType s),
    Eq (IdentifierType s),
    Eq (ModuleRefType s),
    Eq (SymbolType s),
    Eq (ExpressionType s)
  ) =>
  Eq (FunctionClause s)

deriving stock instance
  ( Ord (PatternType s),
    Ord (IdentifierType s),
    Ord (ModuleRefType s),
    Ord (SymbolType s),
    Ord (ExpressionType s)
  ) =>
  Ord (FunctionClause s)

--------------------------------------------------------------------------------
-- Module declaration
--------------------------------------------------------------------------------

type LocalModuleName s = SymbolType s

data Module (s :: Stage) (t :: ModuleIsTop) = Module
  { _modulePath :: ModulePathType s t,
    _moduleParameters :: [InductiveParameter s],
    _moduleBody :: [Statement s]
  }

deriving stock instance
  ( Show (ModulePathType s t),
    Show (ModulePathType s 'ModuleLocal),
    Show (ImportType s),
    Show (PatternType s),
    Show (IdentifierType s),
    Show (ModuleRefType s),
    Show (SymbolType s),
    Show (ExpressionType s)
  ) =>
  Show (Module s t)

deriving stock instance
  ( Eq (ModulePathType s t),
    Eq (ModulePathType s 'ModuleLocal),
    Eq (ImportType s),
    Eq (PatternType s),
    Eq (IdentifierType s),
    Eq (ModuleRefType s),
    Eq (SymbolType s),
    Eq (ExpressionType s)
  ) =>
  Eq (Module s t)

deriving stock instance
  ( Ord (ModulePathType s t),
    Ord (ModulePathType s 'ModuleLocal),
    Ord (ImportType s),
    Ord (PatternType s),
    Ord (IdentifierType s),
    Ord (ModuleRefType s),
    Ord (SymbolType s),
    Ord (ExpressionType s)
  ) =>
  Ord (Module s t)

data UsingHiding
  = Using (NonEmpty Symbol)
  | Hiding (NonEmpty Symbol)
  deriving stock (Show, Eq, Ord)

type ModuleRef = ModuleRef' 'S.Concrete

newtype ModuleRef' (c :: S.IsConcrete) = ModuleRef'
  { _unModuleRef' :: Σ ModuleIsTop (TyCon1 (ModuleRef'' c))
  }

instance SingI c => Show (ModuleRef' c) where
  show (ModuleRef' (isTop :&: r)) = case isTop of
    SModuleLocal -> case sing :: S.SIsConcrete c of
      S.SConcrete -> show r
      S.SNotConcrete -> show r
    SModuleTop -> case sing :: S.SIsConcrete c of
      S.SConcrete -> show r
      S.SNotConcrete -> show r

getNameRefId :: forall c. SingI c => RefNameType c -> S.NameId
getNameRefId = case sing :: S.SIsConcrete c of
  S.SConcrete -> (^. S.nameId)
  S.SNotConcrete -> (^. S.nameId)

getModuleExportInfo :: ModuleRef' c -> ExportInfo
getModuleExportInfo (ModuleRef' (_ :&: ModuleRef'' {..})) = _moduleExportInfo

getModuleRefNameType :: ModuleRef' c -> RefNameType c
getModuleRefNameType (ModuleRef' (_ :&: ModuleRef'' {..})) = _moduleRefName

instance SingI c => Eq (ModuleRef' c) where
  (==) = (==) `on` (getNameRefId . getModuleRefNameType)

instance SingI c => Ord (ModuleRef' c) where
  compare = compare `on` (getNameRefId . getModuleRefNameType)

data ModuleRef'' (c :: S.IsConcrete) (t :: ModuleIsTop) = ModuleRef''
  { _moduleRefName :: RefNameType c,
    _moduleExportInfo :: ExportInfo,
    _moduleRefModule :: Module 'Scoped t
  }

instance Show (RefNameType s) => Show (ModuleRef'' s t) where
  show ModuleRef'' {..} = show _moduleRefName

data SymbolEntry
  = EntryAxiom (AxiomRef' 'S.NotConcrete)
  | EntryInductive (InductiveRef' 'S.NotConcrete)
  | EntryFunction (FunctionRef' 'S.NotConcrete)
  | EntryConstructor (ConstructorRef' 'S.NotConcrete)
  | EntryModule (ModuleRef' 'S.NotConcrete)
  deriving stock (Show)

-- | Symbols that a module exports
newtype ExportInfo = ExportInfo
  { _exportSymbols :: HashMap Symbol SymbolEntry
  }
  deriving stock (Show)

data OpenModule (s :: Stage) = OpenModule
  { _openModuleName :: ModuleRefType s,
    _openModuleImport :: Bool,
    _openParameters :: [ExpressionType s],
    _openUsingHiding :: Maybe UsingHiding,
    _openPublic :: PublicAnn
  }

deriving stock instance
  ( Eq (IdentifierType s),
    Eq (SymbolType s),
    Eq (ModuleRefType s),
    Eq (PatternType s),
    Eq (ExpressionType s)
  ) =>
  Eq (OpenModule s)

deriving stock instance
  ( Ord (IdentifierType s),
    Ord (SymbolType s),
    Ord (PatternType s),
    Ord (ModuleRefType s),
    Ord (ExpressionType s)
  ) =>
  Ord (OpenModule s)

deriving stock instance
  ( Show (IdentifierType s),
    Show (ModuleRefType s),
    Show (ExpressionType s)
  ) =>
  Show (OpenModule s)

--------------------------------------------------------------------------------
-- Expression
--------------------------------------------------------------------------------

type ScopedIden = ScopedIden' 'S.Concrete

data ScopedIden' (n :: S.IsConcrete)
  = ScopedAxiom (AxiomRef' n)
  | ScopedInductive (InductiveRef' n)
  | ScopedVar S.Symbol
  | ScopedFunction (FunctionRef' n)
  | ScopedConstructor (ConstructorRef' n)

deriving stock instance
  (Eq (RefNameType s)) => Eq (ScopedIden' s)

deriving stock instance
  (Ord (RefNameType s)) => Ord (ScopedIden' s)

deriving stock instance
  (Show (RefNameType s)) => Show (ScopedIden' s)

identifierName :: forall n. SingI n => ScopedIden' n -> RefNameType n
identifierName = \case
  ScopedAxiom a -> a ^. axiomRefName
  ScopedInductive i -> i ^. inductiveRefName
  ScopedVar v ->
    ( case sing :: S.SIsConcrete n of
        S.SConcrete -> id
        S.SNotConcrete -> set S.nameConcrete ()
    )
      (unqualifiedSymbol v)
  ScopedFunction f -> f ^. functionRefName
  ScopedConstructor c -> c ^. constructorRefName

data Expression
  = ExpressionIdentifier ScopedIden
  | ExpressionParensIdentifier ScopedIden
  | ExpressionApplication Application
  | ExpressionInfixApplication InfixApplication
  | ExpressionPostfixApplication PostfixApplication
  | ExpressionLambda (Lambda 'Scoped)
  | ExpressionMatch (Match 'Scoped)
  | ExpressionLetBlock (LetBlock 'Scoped)
  | ExpressionUniverse Universe
  | ExpressionLiteral LiteralLoc
  | ExpressionFunction (Function 'Scoped)
  | ExpressionHole (HoleType 'Scoped)
  | ExpressionBraces (WithLoc Expression)
  deriving stock (Show, Eq, Ord)

instance HasAtomicity Expression where
  atomicity e = case e of
    ExpressionIdentifier {} -> Atom
    ExpressionHole {} -> Atom
    ExpressionParensIdentifier {} -> Atom
    ExpressionApplication {} -> Aggregate appFixity
    ExpressionInfixApplication a -> Aggregate (getFixity a)
    ExpressionPostfixApplication a -> Aggregate (getFixity a)
    ExpressionLambda {} -> Atom
    ExpressionLiteral {} -> Atom
    ExpressionMatch {} -> Atom
    ExpressionLetBlock {} -> Atom
    ExpressionBraces {} -> Atom
    ExpressionUniverse {} -> Atom
    ExpressionFunction {} -> Aggregate funFixity

--------------------------------------------------------------------------------
-- Match expression
--------------------------------------------------------------------------------

data MatchAlt (s :: Stage) = MatchAlt
  { matchAltPattern :: PatternType s,
    matchAltBody :: ExpressionType s
  }

deriving stock instance
  ( Show (ExpressionType s),
    Show (PatternType s)
  ) =>
  Show (MatchAlt s)

deriving stock instance
  ( Eq (ExpressionType s),
    Eq (PatternType s)
  ) =>
  Eq (MatchAlt s)

deriving stock instance
  ( Ord (ExpressionType s),
    Ord (PatternType s)
  ) =>
  Ord (MatchAlt s)

data Match (s :: Stage) = Match
  { matchExpression :: ExpressionType s,
    matchAlts :: [MatchAlt s]
  }

deriving stock instance
  ( Show (ExpressionType s),
    Show (PatternType s)
  ) =>
  Show (Match s)

deriving stock instance
  ( Eq (ExpressionType s),
    Eq (PatternType s)
  ) =>
  Eq (Match s)

deriving stock instance
  ( Ord (ExpressionType s),
    Ord (PatternType s)
  ) =>
  Ord (Match s)

--------------------------------------------------------------------------------
-- Function expression
--------------------------------------------------------------------------------

data FunctionParameter (s :: Stage) = FunctionParameter
  { _paramName :: Maybe (SymbolType s),
    _paramUsage :: Maybe Usage,
    _paramImplicit :: IsImplicit,
    _paramType :: ExpressionType s
  }

deriving stock instance
  (Show (ExpressionType s), Show (SymbolType s)) =>
  Show (FunctionParameter s)

deriving stock instance
  (Eq (ExpressionType s), Eq (SymbolType s)) =>
  Eq (FunctionParameter s)

deriving stock instance
  (Ord (ExpressionType s), Ord (SymbolType s)) =>
  Ord (FunctionParameter s)

data Function (s :: Stage) = Function
  { _funParameter :: FunctionParameter s,
    _funReturn :: ExpressionType s
  }

deriving stock instance (Show (ExpressionType s), Show (SymbolType s)) => Show (Function s)

deriving stock instance (Eq (ExpressionType s), Eq (SymbolType s)) => Eq (Function s)

deriving stock instance (Ord (ExpressionType s), Ord (SymbolType s)) => Ord (Function s)

--------------------------------------------------------------------------------
-- Where block clauses
--------------------------------------------------------------------------------

newtype WhereBlock (s :: Stage) = WhereBlock
  { whereClauses :: NonEmpty (WhereClause s)
  }

deriving stock instance
  ( Show (PatternType s),
    Show (IdentifierType s),
    Show (ModuleRefType s),
    Show (SymbolType s),
    Show (ExpressionType s)
  ) =>
  Show (WhereBlock s)

deriving stock instance
  ( Eq (PatternType s),
    Eq (IdentifierType s),
    Eq (ModuleRefType s),
    Eq (SymbolType s),
    Eq (ExpressionType s)
  ) =>
  Eq (WhereBlock s)

deriving stock instance
  ( Ord (PatternType s),
    Ord (IdentifierType s),
    Ord (ModuleRefType s),
    Ord (SymbolType s),
    Ord (ExpressionType s)
  ) =>
  Ord (WhereBlock s)

data WhereClause (s :: Stage)
  = WhereOpenModule (OpenModule s)
  | WhereTypeSig (TypeSignature s)
  | WhereFunClause (FunctionClause s)

deriving stock instance
  ( Show (PatternType s),
    Show (IdentifierType s),
    Show (ModuleRefType s),
    Show (SymbolType s),
    Show (ExpressionType s)
  ) =>
  Show (WhereClause s)

deriving stock instance
  ( Eq (PatternType s),
    Eq (IdentifierType s),
    Eq (ModuleRefType s),
    Eq (SymbolType s),
    Eq (ExpressionType s)
  ) =>
  Eq (WhereClause s)

deriving stock instance
  ( Ord (PatternType s),
    Ord (IdentifierType s),
    Ord (ModuleRefType s),
    Ord (SymbolType s),
    Ord (ExpressionType s)
  ) =>
  Ord (WhereClause s)

--------------------------------------------------------------------------------
-- Lambda expression
--------------------------------------------------------------------------------

-- Notes: An empty lambda, here called 'the impossible case', is a lambda
-- expression with empty list of arguments and empty body.

newtype Lambda (s :: Stage) = Lambda
  { _lambdaClauses :: [LambdaClause s]
  }

deriving stock instance
  ( Show (PatternType s),
    Show (ExpressionType s)
  ) =>
  Show (Lambda s)

deriving stock instance
  ( Eq (PatternType s),
    Eq (ExpressionType s)
  ) =>
  Eq (Lambda s)

deriving stock instance
  ( Ord (PatternType s),
    Ord (ExpressionType s)
  ) =>
  Ord (Lambda s)

data LambdaClause (s :: Stage) = LambdaClause
  { lambdaParameters :: NonEmpty (PatternType s),
    lambdaBody :: ExpressionType s
  }

deriving stock instance
  ( Show (PatternType s),
    Show (ExpressionType s)
  ) =>
  Show (LambdaClause s)

deriving stock instance
  ( Eq (PatternType s),
    Eq (ExpressionType s)
  ) =>
  Eq (LambdaClause s)

deriving stock instance
  ( Ord (PatternType s),
    Ord (ExpressionType s)
  ) =>
  Ord (LambdaClause s)

--------------------------------------------------------------------------------
-- Application expression
--------------------------------------------------------------------------------

data Application = Application
  { _applicationFunction :: Expression,
    _applicationParameter :: Expression
  }
  deriving stock (Show, Eq, Ord)

data InfixApplication = InfixApplication
  { _infixAppLeft :: Expression,
    _infixAppOperator :: ScopedIden,
    _infixAppRight :: Expression
  }
  deriving stock (Show, Eq, Ord)

instance HasFixity InfixApplication where
  getFixity (InfixApplication _ op _) = fromMaybe impossible (identifierName op ^. S.nameFixity)

data PostfixApplication = PostfixApplication
  { _postfixAppParameter :: Expression,
    _postfixAppOperator :: ScopedIden
  }
  deriving stock (Show, Eq, Ord)

instance HasFixity PostfixApplication where
  getFixity (PostfixApplication _ op) = fromMaybe impossible (identifierName op ^. S.nameFixity)

--------------------------------------------------------------------------------
-- Let block expression
--------------------------------------------------------------------------------

data LetBlock (s :: Stage) = LetBlock
  { _letClauses :: [LetClause s],
    _letExpression :: ExpressionType s
  }

deriving stock instance
  ( Show (PatternType s),
    Show (IdentifierType s),
    Show (ModuleRefType s),
    Show (SymbolType s),
    Show (ExpressionType s)
  ) =>
  Show (LetBlock s)

deriving stock instance
  ( Eq (PatternType s),
    Eq (IdentifierType s),
    Eq (ModuleRefType s),
    Eq (SymbolType s),
    Eq (ExpressionType s)
  ) =>
  Eq (LetBlock s)

deriving stock instance
  ( Ord (PatternType s),
    Ord (IdentifierType s),
    Ord (ModuleRefType s),
    Ord (SymbolType s),
    Ord (ExpressionType s)
  ) =>
  Ord (LetBlock s)

data LetClause (s :: Stage)
  = LetTypeSig (TypeSignature s)
  | LetFunClause (FunctionClause s)

deriving stock instance
  ( Show (PatternType s),
    Show (IdentifierType s),
    Show (ModuleRefType s),
    Show (SymbolType s),
    Show (ExpressionType s)
  ) =>
  Show (LetClause s)

deriving stock instance
  ( Eq (PatternType s),
    Eq (IdentifierType s),
    Eq (ModuleRefType s),
    Eq (SymbolType s),
    Eq (ExpressionType s)
  ) =>
  Eq (LetClause s)

deriving stock instance
  ( Ord (PatternType s),
    Ord (IdentifierType s),
    Ord (ModuleRefType s),
    Ord (SymbolType s),
    Ord (ExpressionType s)
  ) =>
  Ord (LetClause s)

--------------------------------------------------------------------------------
-- Compile statements
--------------------------------------------------------------------------------

data Compile s = Compile
  { _compileName :: SymbolType s,
    _compileBackendItems :: [BackendItem]
  }

deriving stock instance
  (Show (SymbolType s)) => Show (Compile s)

deriving stock instance
  (Ord (SymbolType s)) => Ord (Compile s)

deriving stock instance
  (Eq (SymbolType s)) => Eq (Compile s)

--------------------------------------------------------------------------------
-- Debugging statements
--------------------------------------------------------------------------------

newtype Eval (s :: Stage) = Eval {evalExpression :: ExpressionType s}

deriving stock instance
  Show (ExpressionType s) => Show (Eval s)

deriving stock instance
  Eq (ExpressionType s) => Eq (Eval s)

deriving stock instance
  Ord (ExpressionType s) => Ord (Eval s)

--------------------------------------------------------------------------------

newtype Print (s :: Stage) = Print {printExpression :: ExpressionType s}

deriving stock instance
  Show (ExpressionType s) => Show (Print s)

deriving stock instance
  Eq (ExpressionType s) => Eq (Print s)

deriving stock instance
  Ord (ExpressionType s) => Ord (Print s)

--------------------------------------------------------------------------------
-- Expression atom
--------------------------------------------------------------------------------

-- | Expressions without application
data ExpressionAtom (s :: Stage)
  = AtomIdentifier (IdentifierType s)
  | AtomLambda (Lambda s)
  | AtomHole (HoleType s)
  | AtomBraces (WithLoc (ExpressionType s))
  | AtomLetBlock (LetBlock s)
  | AtomUniverse Universe
  | AtomFunction (Function s)
  | AtomFunArrow
  | AtomMatch (Match s)
  | AtomLiteral LiteralLoc
  | AtomParens (ExpressionType s)

data ExpressionAtoms (s :: Stage) = ExpressionAtoms
  { _expressionAtoms :: NonEmpty (ExpressionAtom s),
    _expressionAtomsLoc :: Interval
  }

--------------------------------------------------------------------------------

makeLenses ''Function
makeLenses ''InductiveDef
makeLenses ''PostfixApplication
makeLenses ''InfixApplication
makeLenses ''Application
makeLenses ''LetBlock
makeLenses ''FunctionParameter
makeLenses ''Import
makeLenses ''OperatorSyntaxDef
makeLenses ''InductiveConstructorDef
makeLenses ''Module
makeLenses ''TypeSignature
makeLenses ''AxiomDef
makeLenses ''FunctionClause
makeLenses ''InductiveParameter
makeLenses ''ModuleRef'
makeLenses ''ModuleRef''
makeLenses ''OpenModule
makeLenses ''PatternApp
makeLenses ''PatternInfixApp
makeLenses ''PatternPostfixApp
makeLenses ''Compile
makeLenses ''PatternAtoms
makeLenses ''ExpressionAtoms

instance HasAtomicity (PatternAtom 'Parsed) where
  atomicity = const Atom

deriving stock instance
  ( Show (ExpressionType s),
    Show (IdentifierType s),
    Show (PatternAtomIdenType s),
    Show (PatternType s)
  ) =>
  Show (PatternAtom s)

deriving stock instance
  ( Eq (ExpressionType s),
    Eq (IdentifierType s),
    Eq (PatternAtomIdenType s),
    Eq (PatternType s)
  ) =>
  Eq (PatternAtom s)

deriving stock instance
  ( Ord (ExpressionType s),
    Ord (IdentifierType s),
    Ord (PatternAtomIdenType s),
    Ord (PatternType s)
  ) =>
  Ord (PatternAtom s)

deriving stock instance
  ( Show (ExpressionType s),
    Show (IdentifierType s),
    Show (PatternAtomIdenType s),
    Show (PatternType s)
  ) =>
  Show (PatternAtoms s)

instance HasLoc (PatternAtoms s) where
  getLoc = (^. patternAtomsLoc)

instance
  ( Eq (ExpressionType s),
    Eq (IdentifierType s),
    Eq (PatternAtomIdenType s),
    Eq (PatternType s)
  ) =>
  Eq (PatternAtoms s)
  where
  (==) = (==) `on` (^. patternAtoms)

instance
  ( Ord (ExpressionType s),
    Ord (IdentifierType s),
    Ord (PatternAtomIdenType s),
    Ord (PatternType s)
  ) =>
  Ord (PatternAtoms s)
  where
  compare = compare `on` (^. patternAtoms)

deriving stock instance
  ( Show (ExpressionType s),
    Show (IdentifierType s),
    Show (ModuleRefType s),
    Show (HoleType s),
    Show (SymbolType s),
    Show (PatternType s)
  ) =>
  Show (ExpressionAtom s)

deriving stock instance
  ( Eq (ExpressionType s),
    Eq (IdentifierType s),
    Eq (HoleType s),
    Eq (ModuleRefType s),
    Eq (SymbolType s),
    Eq (PatternType s)
  ) =>
  Eq (ExpressionAtom s)

deriving stock instance
  ( Ord (ExpressionType s),
    Ord (IdentifierType s),
    Ord (ModuleRefType s),
    Ord (HoleType s),
    Ord (SymbolType s),
    Ord (PatternType s)
  ) =>
  Ord (ExpressionAtom s)

deriving stock instance
  ( Show (ExpressionType s),
    Show (IdentifierType s),
    Show (ModuleRefType s),
    Show (HoleType s),
    Show (SymbolType s),
    Show (PatternType s)
  ) =>
  Show (ExpressionAtoms s)

instance HasLoc (ExpressionAtoms s) where
  getLoc = (^. expressionAtomsLoc)

instance HasAtomicity (ExpressionAtoms 'Parsed) where
  atomicity ExpressionAtoms {..} = case _expressionAtoms of
    (_ :| []) -> Atom
    (_ :| _)
      | AtomFunArrow `elem` _expressionAtoms -> Aggregate funFixity
      | otherwise -> Aggregate appFixity

instance
  ( Eq (ExpressionType s),
    Eq (IdentifierType s),
    Eq (ModuleRefType s),
    Eq (HoleType s),
    Eq (SymbolType s),
    Eq (PatternType s)
  ) =>
  Eq (ExpressionAtoms s)
  where
  (==) = (==) `on` (^. expressionAtoms)

instance
  ( Ord (ExpressionType s),
    Ord (IdentifierType s),
    Ord (ModuleRefType s),
    Ord (HoleType s),
    Ord (SymbolType s),
    Ord (PatternType s)
  ) =>
  Ord (ExpressionAtoms s)
  where
  compare = compare `on` (^. expressionAtoms)

--------------------------------------------------------------------------------

idenOverName :: (forall s. S.Name' s -> S.Name' s) -> ScopedIden -> ScopedIden
idenOverName f = \case
  ScopedAxiom a -> ScopedAxiom (over axiomRefName f a)
  ScopedInductive i -> ScopedInductive (over inductiveRefName f i)
  ScopedVar v -> ScopedVar (f v)
  ScopedFunction fun -> ScopedFunction (over functionRefName f fun)
  ScopedConstructor c -> ScopedConstructor (over constructorRefName f c)

entryPrism :: (S.Name' () -> S.Name' ()) -> SymbolEntry -> (S.Name' (), SymbolEntry)
entryPrism f = \case
  EntryAxiom a -> (a ^. axiomRefName, EntryAxiom (over axiomRefName f a))
  EntryInductive i -> (i ^. inductiveRefName, EntryInductive (over inductiveRefName f i))
  EntryFunction fun -> (fun ^. functionRefName, EntryFunction (over functionRefName f fun))
  EntryConstructor c -> (c ^. constructorRefName, EntryConstructor (over constructorRefName f c))
  EntryModule m -> (getModuleRefNameType m, EntryModule (overModuleRef'' (over moduleRefName f) m))

entryOverName :: (S.Name' () -> S.Name' ()) -> SymbolEntry -> SymbolEntry
entryOverName f = snd . entryPrism f

entryName :: SymbolEntry -> S.Name' ()
entryName = fst . entryPrism id

entryIsExpression :: SymbolEntry -> Bool
entryIsExpression = \case
  EntryAxiom {} -> True
  EntryInductive {} -> True
  EntryFunction {} -> True
  EntryConstructor {} -> True
  EntryModule {} -> False

instance HasLoc SymbolEntry where
  getLoc = (^. S.nameDefined) . entryName

overModuleRef'' :: forall s s'. (forall t. ModuleRef'' s t -> ModuleRef'' s' t) -> ModuleRef' s -> ModuleRef' s'
overModuleRef'' f = over unModuleRef' (\(t :&: m'') -> t :&: f m'')

symbolEntryToSName :: SymbolEntry -> S.Name' ()
symbolEntryToSName = \case
  EntryAxiom a -> a ^. axiomRefName
  EntryInductive i -> i ^. inductiveRefName
  EntryFunction f -> f ^. functionRefName
  EntryConstructor c -> c ^. constructorRefName
  EntryModule m -> getModuleRefNameType m

instance HasNameKind SymbolEntry where
  getNameKind = getNameKind . entryName
