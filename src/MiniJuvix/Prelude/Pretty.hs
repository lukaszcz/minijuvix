module MiniJuvix.Prelude.Pretty
  ( module MiniJuvix.Prelude.Pretty,
    module Prettyprinter,
    module Prettyprinter.Render.Terminal,
  )
where

import MiniJuvix.Prelude.Base
import Prettyprinter hiding (hsep, vsep)
import Prettyprinter qualified as PP
import Prettyprinter.Render.Terminal (AnsiStyle)
import Prettyprinter.Render.Terminal qualified as Ansi
import Prettyprinter.Render.Text qualified as Text
import Prelude

class HasAnsiBackend a where
  toAnsiStream :: a -> SimpleDocStream Ansi.AnsiStyle
  toAnsiStream = layoutPretty defaultLayoutOptions . toAnsiDoc

  toAnsiDoc :: a -> Doc Ansi.AnsiStyle

class HasTextBackend a where
  toTextStream :: a -> SimpleDocStream b
  toTextStream = layoutPretty defaultLayoutOptions . toTextDoc

  toTextDoc :: a -> Doc b

data AnsiText = forall t.
  (HasAnsiBackend t, HasTextBackend t) =>
  AnsiText
  { _ansiText :: t
  }

instance HasTextBackend AnsiText where
  toTextStream (AnsiText t) = toTextStream t
  toTextDoc (AnsiText t) = toTextDoc t

instance HasAnsiBackend AnsiText where
  toAnsiStream (AnsiText t) = toAnsiStream t
  toAnsiDoc (AnsiText t) = toAnsiDoc t

instance HasTextBackend (Doc a) where
  toTextDoc = unAnnotate
  toTextStream = unAnnotateS . layoutPretty defaultLayoutOptions

instance HasAnsiBackend (Doc Ansi.AnsiStyle) where
  toAnsiDoc = id
  toAnsiStream = layoutPretty defaultLayoutOptions

instance Show AnsiText where
  show (AnsiText t) = unpack (Text.renderStrict (toTextStream t))

instance Pretty AnsiText where
  pretty (AnsiText t) = pretty (Text.renderStrict (toTextStream t))

renderIO :: (HasAnsiBackend a, HasTextBackend a) => Bool -> a -> IO ()
renderIO useColors = hRenderIO useColors stdout

hRenderIO :: (HasAnsiBackend a, HasTextBackend a) => Bool -> Handle -> a -> IO ()
hRenderIO useColors h
  | useColors = Ansi.renderIO h . toAnsiStream
  | otherwise = Text.renderIO h . toTextStream

toAnsiText :: (HasAnsiBackend a, HasTextBackend a) => Bool -> a -> Text
toAnsiText useColors
  | useColors = Ansi.renderStrict . toAnsiStream
  | otherwise = Text.renderStrict . toTextStream

prettyText :: Pretty a => a -> Text
prettyText = Text.renderStrict . layoutPretty defaultLayoutOptions . pretty

vsep :: Foldable f => f (Doc a) -> Doc a
vsep = PP.vsep . toList

vsep2 :: [Doc a] -> Doc a
vsep2 = concatWith (\a b -> a <> line <> line <> b)

hsep :: Foldable f => f (Doc a) -> Doc a
hsep = PP.hsep . toList

vsepMaybe :: Foldable f => f (Doc a) -> Maybe (Doc a)
vsepMaybe l
  | null l = Nothing
  | otherwise = Just (vsep l)

hsepMaybe :: Foldable f => f (Doc a) -> Maybe (Doc a)
hsepMaybe l
  | null l = Nothing
  | otherwise = Just (hsep l)

ordinal :: Int -> Doc a
ordinal = \case
  1 -> "first"
  2 -> "second"
  3 -> "third"
  4 -> "fourth"
  5 -> "fifth"
  6 -> "sixth"
  7 -> "seventh"
  8 -> "eighth"
  9 -> "ninth"
  10 -> "tenth"
  11 -> "eleventh"
  12 -> "twelfth"
  n -> pretty n <> "th"
