{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}

module MiniJuvix.Syntax.Scoped.Name where

import Lens.Micro.Platform
import Data.Stream (Stream (Cons))
import qualified MiniJuvix.Syntax.Concrete.Name as C
import qualified MiniJuvix.Syntax.Concrete.Fixity as C
import MiniJuvix.Utils.Prelude

--------------------------------------------------------------------------------
-- Names
--------------------------------------------------------------------------------

newtype NameId = NameId Word64
  deriving stock (Show, Eq, Ord, Generic)

data AbsModulePath = AbsModulePath {
  absTopModulePath :: C.TopModulePath,
  absLocalPath :: [C.Symbol]
  }
  deriving stock (Show, Eq, Generic)

instance Hashable AbsModulePath

-- | Appends a local path to the absolute path
-- e.g. TopMod.Local <.> Inner == TopMod.Local.Inner
(<.>) :: AbsModulePath -> C.Symbol -> AbsModulePath
absP <.> localMod = absP {absLocalPath = absLocalPath absP ++ [localMod] }

allNameIds :: Stream NameId
allNameIds = NameId <$> ids
  where
    ids :: Stream Word64
    ids = aux minBound
    aux i = Cons i (aux (succ i))

instance Hashable NameId

data NameFixity =
  NoFixity
  | SomeFixity C.Fixity
  deriving stock (Show, Eq)

data NameKind
  = -- | Constructor name.
    KNameConstructor
  | -- | Name introduced by the inductive keyword.
    KNameInductive
  | -- | Name of a defined function (top level or let/where block).
    KNameFunction
  | -- | A locally bound name (patterns, arguments, etc.).
    KNameLocal
  deriving stock (Show, Eq)

canHaveFixity :: NameKind -> Bool
canHaveFixity k = case k of
  KNameConstructor -> True
  KNameInductive -> True
  KNameFunction -> True
  KNameLocal -> False

type Name = Name' C.Name

type Symbol = Name' C.Symbol

data Name' n = Name'
  { _nameId :: NameId,
    _nameConcrete :: n,
    _nameKind :: NameKind,
    _nameDefinedIn :: AbsModulePath,
    _nameFixity :: NameFixity
  }
  deriving stock (Show)
makeLenses ''Name'

instance Eq (Name' n) where
  (==) = (==) `on` _nameId

instance Ord (Name' n) where
  compare = compare `on` _nameId

instance Hashable (Name' n) where
  hashWithSalt salt = hashWithSalt salt . _nameId
