module MiniJuvix.Syntax.MonoJuvix.Pretty.Ansi where

import MiniJuvix.Prelude
import MiniJuvix.Syntax.MonoJuvix.Language
import MiniJuvix.Syntax.MonoJuvix.Pretty.Ann
import MiniJuvix.Syntax.MonoJuvix.Pretty.Base
import Prettyprinter
import Prettyprinter.Render.Terminal

printPrettyCodeDefault :: PrettyCode c => c -> IO ()
printPrettyCodeDefault = printPrettyCode defaultOptions

printPrettyCode :: PrettyCode c => Options -> c -> IO ()
printPrettyCode = hPrintPrettyCode stdout

hPrintPrettyCode :: PrettyCode c => Handle -> Options -> c -> IO ()
hPrintPrettyCode h opts = renderIO h . docStream' opts

renderPrettyCode :: PrettyCode c => Options -> c -> Text
renderPrettyCode opts = renderStrict . docStream' opts

docStream' :: PrettyCode c => Options -> c -> SimpleDocStream AnsiStyle
docStream' opts =
  reAnnotateS stylize . docStream opts

stylize :: Ann -> AnsiStyle
stylize a = case a of
  AnnKind k -> nameKindAnsi k
  AnnKeyword -> colorDull Blue
  AnnLiteralString -> colorDull Red
  AnnLiteralInteger -> colorDull Cyan
