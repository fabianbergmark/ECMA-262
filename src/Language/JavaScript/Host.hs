module Language.JavaScript.Host where

import Control.Lens

import Language.JavaScript.Interpret

defineGlobalProperty :: (Monad m) =>
                        String -> Property -> JavaScriptT m ()
defineGlobalProperty i p = do
  global <- use globalObject
  property global i ?= p
