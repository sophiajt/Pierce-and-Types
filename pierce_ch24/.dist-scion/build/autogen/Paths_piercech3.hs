module Paths_piercech3 (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName
  ) where

import Data.Version (Version(..))
import System.Environment (getEnv)

version :: Version
version = Version {versionBranch = [0,1], versionTags = []}

bindir, libdir, datadir, libexecdir :: FilePath

bindir     = "/Users/jonathan/.cabal/bin"
libdir     = "/Users/jonathan/.cabal/lib/piercech3-0.1/ghc-6.12.3"
datadir    = "/Users/jonathan/.cabal/share/piercech3-0.1"
libexecdir = "/Users/jonathan/.cabal/libexec"

getBinDir, getLibDir, getDataDir, getLibexecDir :: IO FilePath
getBinDir = catch (getEnv "piercech3_bindir") (\_ -> return bindir)
getLibDir = catch (getEnv "piercech3_libdir") (\_ -> return libdir)
getDataDir = catch (getEnv "piercech3_datadir") (\_ -> return datadir)
getLibexecDir = catch (getEnv "piercech3_libexecdir") (\_ -> return libexecdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
