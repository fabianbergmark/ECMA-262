module Language.JavaScript.Host where

import Control.Lens

import Language.JavaScript.Interpret

defineGlobalProperty :: (Monad m) =>
                        JavaScriptT m (String, Property) ->
                        JavaScriptT m ()
defineGlobalProperty create = do
  (i, p) <- create
  global <- use globalObject
  property global i ?= p
