module MiniJuvix.Prelude.Files where

import Data.HashMap.Strict qualified as HashMap
import MiniJuvix.Prelude.Base

newtype FilesError = StdlibShadowing FileInfo
  deriving stock (Show)

newtype FileInfo = FileInfo
  { _fileInfoPath :: FilePath }
  deriving stock (Show)

data Files m a where
  ReadFile' :: FilePath -> Files m (Either FilesError Text)
  EqualPaths' :: FilePath -> FilePath -> Files m (Maybe Bool)
  RegisterStdlib :: [(FilePath, Text)] -> Files m ()

makeSem ''Files

newtype FilesState = FilesState
  {_stdlibTable :: HashMap FilePath Text}

makeLenses ''FilesState
makeLenses ''FileInfo

initState :: FilesState
initState = FilesState mempty

readStdLibOrFile :: FilePath -> HashMap FilePath Text -> IO (Either FilesError Text)
readStdLibOrFile f stdlib = do
  cf <- canonicalizePath f
  case HashMap.lookup cf stdlib of
    Nothing -> Right <$> readFile f
    Just c -> do
      ifM (doesFileExist f) (return $ Left (StdlibShadowing (FileInfo f))) (return (Right c))

seqFst :: (IO a, b) -> IO (a, b)
seqFst (ma, b) = do
  a <- ma
  return (a, b)

canonicalizeStdlib :: [(FilePath, Text)] -> IO (HashMap FilePath Text)
canonicalizeStdlib stdlib = HashMap.fromList <$> mapM seqFst (first canonicalizePath <$> stdlib)

runFilesIO' :: forall r a. Member (Embed IO) r => Sem (Files ': r) a -> Sem (State FilesState ': r) a
runFilesIO' = reinterpret $ \case
  ReadFile' f -> do
    stdlib <- gets (^. stdlibTable)
    embed (readStdLibOrFile f stdlib)
  EqualPaths' f h -> embed $ do
    f' <- canonicalizePath f
    h' <- canonicalizePath h
    return (Just (equalFilePath f' h'))
  RegisterStdlib stdlib -> do
    s <- embed (FilesState <$> canonicalizeStdlib stdlib)
    put s

runFilesIO :: Member (Embed IO) r => Sem (Files ': r) a -> Sem r a
runFilesIO = evalState initState . runFilesIO'

runFilesEmpty :: Sem (Files ': r) a -> Sem r a
runFilesEmpty = runFilesPure mempty

runFilesPure :: HashMap FilePath Text -> Sem (Files ': r) a -> Sem r a
runFilesPure fs = interpret $ \case
  ReadFile' f -> case HashMap.lookup f fs of
    Nothing ->
      error $
        pack $
          "file "
            <> f
            <> " does not exist."
            <> "\nThe contents of the mocked file system are:\n"
            <> unlines (HashMap.keys fs)
    Just c -> return (Right c)
  EqualPaths' _ _ -> return Nothing
  RegisterStdlib {} -> return ()
