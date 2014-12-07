module Main
       ( main ) where

import Control.Lens
import Control.Monad (void)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Lazy (evalStateT)

import qualified Data.Map as Map (empty)

import System.Environment (getArgs)

import Language.JavaScript
import Language.JavaScript.Parser
import Language.JavaScript.Host.Console

main :: IO ()
main = do
  (file:_) <- getArgs
  source <- readFile file
  let eAST = parseJavaScript source
  void $ runHostedJavaScript source console
