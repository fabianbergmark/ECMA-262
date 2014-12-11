module Main
       ( main ) where

import Control.Monad (void)

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
