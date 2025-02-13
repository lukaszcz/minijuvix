module MiniJuvix.Syntax.Concrete.Scoped.Error.Pretty.Ansi where

import MiniJuvix.Syntax.Concrete.Scoped.Error.Ann
import MiniJuvix.Syntax.Concrete.Scoped.Pretty.Ansi qualified as S
import Prettyprinter.Render.Terminal

stylize :: Eann -> AnsiStyle
stylize a = case a of
  Highlight -> colorDull Red
  ScopedAnn s -> S.stylize s
