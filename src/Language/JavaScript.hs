module Language.JavaScript
       where

import Control.Applicative ((<$>))

import Text.Parsec (ParseError)

import Language.JavaScript.Interpret
import Language.JavaScript.Parser

runJavaScript :: (Functor m, Monad m) =>
                 String -> m (Either ParseError (Either Value Completion))
runJavaScript source = do
  let eAST = parseJavaScript source
  case eAST of
   Right ast -> do
     Right <$> runJavaScriptT initialState (interpret ast)
   Left e -> return (Left e)

runHostedJavaScript :: (Functor m, Monad m) =>
                       String ->
                       JavaScriptT m () ->
                       m (Either ParseError (Either Value Completion))
runHostedJavaScript source hostInit = do
  let eAST = parseJavaScript source
  case eAST of
   Right ast -> do
     Right <$> runJavaScriptT initialState (hostInit >> interpret ast)
   Left e -> return (Left e)
