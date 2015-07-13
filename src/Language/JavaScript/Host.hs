module Language.JavaScript.Host
       ( FromJSValue(..)
       , ToJSValue(..)
       , defineGlobalProperty ) where

import Control.Lens

import Language.JavaScript.Interpret

class FromJSValue a where
  fromJSValue :: Value -> JavaScriptT m a

class ToJSValue a where
  toJSValue :: a -> JavaScriptT m Value

defineGlobalProperty :: (Monad m) =>
                        String -> Property -> JavaScriptT m ()
defineGlobalProperty i p = do
  global <- use globalObject
  property global i ?= p
