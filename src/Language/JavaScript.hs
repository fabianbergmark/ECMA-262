module Language.JavaScript
       ( interpretJavaScript
       , interpretHostedJavaScript
       , runJavaScript
       , runHostedJavaScript ) where

import Control.Applicative ((<$>))

import Text.Parsec (ParseError)

import Language.JavaScript.AST
import Language.JavaScript.Interpret
import Language.JavaScript.Parser

interpretJavaScript :: (Functor m, Monad m) =>
                       Program ->
                       m (Either Value Completion)
interpretJavaScript program = do
  runJavaScriptT initialState (interpret program)

interpretHostedJavaScript :: (Functor m, Monad m) =>
                       Program ->
                       JavaScriptT m () ->
                       m (Either Value Completion)
interpretHostedJavaScript program hostInit = do
  runJavaScriptT initialState (hostInit >> interpret program)

runJavaScript :: (Functor m, Monad m) =>
                 String -> m (Either ParseError (Either Value Completion))
runJavaScript source = do
  let eAST = parseJavaScript source
  case eAST of
   Right ast -> do
     Right <$> interpretJavaScript ast
   Left e -> return (Left e)

runHostedJavaScript :: (Functor m, Monad m) =>
                       String ->
                       JavaScriptT m () ->
                       m (Either ParseError (Either Value Completion))
runHostedJavaScript source hostInit = do
  let eAST = parseJavaScript source
  case eAST of
   Right ast -> do
     Right <$> interpretHostedJavaScript ast hostInit
   Left e -> return (Left e)
