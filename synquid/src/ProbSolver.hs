{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}

module ProbSolver where

import Synquid.Logic
import Synquid.Type
import Synquid.Program
import Synquid.Error
import Synquid.Pretty
import Synquid.Parser (parseFromFile, parseProgram, toErrorMessage)
import Synquid.Resolver (resolveDecls)
import Synquid.Succinct
import Synquid.Util

import Control.Monad
import Control.Lens ((^.))
import System.Exit
import System.Console.CmdArgs
import System.Console.ANSI
import System.FilePath
import Data.Maybe (mapMaybe)

-- data ProbContext = ProbContext {
--   _parent :: Maybe Id,
--   _sibling :: Maybe Id,
--   _type :: SuccinctType
-- } deriving(Eq)

-- makeLenses ''ProbContext

parseExample :: String -> IO()
parseExample file = do
  parseResult <- parseFromFile parseProgram file
  case parseResult of
    Left parseErr -> print "error" >> exitFailure
    -- Right ast -> print $ vsep $ map pretty ast
    Right decls -> print $ pretty (filter isSynthesisGoal decls)
-- parameterizeComps

-- getProbContext

-- countRules

-- countContext
data CommandLineArgs = Synthesis {
    file :: String
  }
  deriving (Data, Typeable, Show, Eq)

synt = Synthesis {  
  file                = ""              &= typFile &= argPos 0
}

mode = cmdArgsMode $ modes [synt] &=
  help "Synquid program synthesizer"

main = do
  Synthesis file <- cmdArgsRun mode
  parseExample file
