module BackendC.Positive where

import Base
import Data.Text.IO qualified as TIO
import MiniJuvix.Pipeline
import MiniJuvix.Translation.MonoJuvixToMiniC as MiniC
import System.IO.Extra (withTempDir)
import System.Process qualified as P

data PosTest = PosTest
  { _name :: String,
    _relDir :: FilePath
  }

makeLenses ''PosTest

root :: FilePath
root = "tests/positive/MiniC"

mainFile :: FilePath
mainFile = "Input.mjuvix"

expectedFile :: FilePath
expectedFile = "expected.golden"

testDescr :: PosTest -> TestDescr
testDescr PosTest {..} =
  let tRoot = root </> _relDir
   in TestDescr
        { _testName = _name,
          _testRoot = tRoot,
          _testAssertion = Steps $ \step -> do
            step "Check clang and wasmer are on path"
            assertCmdExists "clang"
            assertCmdExists "wasmer"

            step "Lookup WASI_SYSROOT_PATH"
            sysrootPath <-
              assertEnvVar
                "Env var WASI_SYSROOT_PATH missing. Set to the location of the wasi-clib sysroot"
                "WASI_SYSROOT_PATH"

            step "C Generation"
            let entryPoint = EntryPoint "." (pure mainFile)
            p :: MiniC.MiniCResult <- runIO (upToMiniC entryPoint)

            actual <-
              withTempDir
                ( \dirPath -> do
                    let cOutputFile = dirPath </> "out.c"
                        wasmOutputFile = dirPath </> "out.wasm"
                    TIO.writeFile cOutputFile (p ^. MiniC.resultCCode)
                    step "WASM generation"
                    P.callProcess
                      "clang"
                      [ "-nodefaultlibs",
                        "-lc",
                        "--target=wasm32-wasi",
                        "--sysroot",
                        sysrootPath,
                        "-o",
                        wasmOutputFile,
                        cOutputFile
                      ]
                    step "WASM execution"
                    pack <$> P.readProcess "wasmer" [wasmOutputFile] ""
                )

            expected <- TIO.readFile expectedFile
            step "Compare expected and actual program output"
            assertEqDiff ("check: WASM output = " <> expectedFile) actual expected
        }

allTests :: TestTree
allTests =
  testGroup
    "Backend C positive tests"
    (map (mkTest . testDescr) tests)

tests :: [PosTest]
tests =
  [ PosTest "HelloWorld" "HelloWorld",
    PosTest "Inductive types and pattern matching" "Nat",
    PosTest "Polymorphic types" "Polymorphism",
    PosTest "Multiple modules" "MultiModules",
    PosTest "Higher Order Functions" "HigherOrder"
  ]
