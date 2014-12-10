module Language.JavaScript.Host.Console where

import Control.Lens

import Control.Monad (forM)
import Control.Monad.IO.Class (MonadIO(..))

import Data.List (intersperse)

import Language.JavaScript.Host
import Language.JavaScript.Interpret
import Language.JavaScript.SubType

import qualified Data.Map as Map (empty, fromList)

console :: (Functor m, Monad m, MonadIO m) =>
           JavaScriptT m ()
console = do
  consoleLogId <- createNextInternalId
  op <- use objectPrototypeObject
  fp <- use functionPrototypeObject
  let consoleLogObj = Object consoleLogId
      consoleLogObjInt = ObjectInternal {
        objectInternalProperties        = Map.empty,
        objectInternalPrototype         = const $ return (JSExist fp),
        objectInternalClass             = "Function",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Just consoleLogCallImpl,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

  mInternalObject consoleLogObj ?= consoleLogObjInt

  consoleId <- createNextInternalId
  let consoleObj = Object consoleId
      consoleObjInt = ObjectInternal {
        objectInternalProperties        = Map.fromList
         [ ("log", PropertyData $ DataDescriptor {
               dataDescriptorValue          = inj consoleLogObj,
               dataDescriptorWritable       = True,
               dataDescriptorEnumerable     = False,
               dataDescriptorConfigurable   = True }) ],
        objectInternalPrototype         = const $ return (JSExist op),
        objectInternalClass             = "Object",
        objectInternalExtensible        = const $ return True,
        objectInternalGet               = getImpl,
        objectInternalGetOwnProperty    = getOwnPropertyImpl,
        objectInternalGetProperty       = getPropertyImpl,
        objectInternalPut               = putImpl,
        objectInternalCanPut            = canPutImpl,
        objectInternalHasProperty       = hasPropertyImpl,
        objectInternalDelete            = deleteImpl,
        objectInternalDefaultValue      = defaultValueImpl,
        objectInternalDefineOwnProperty = defineOwnPropertyImpl,
        objectInternalPrimitiveValue    = Nothing,
        objectInternalConstruct         = Nothing,
        objectInternalCall              = Nothing,
        objectInternalHasInstance       = Nothing,
        objectInternalScope             = Nothing,
        objectInternalFormalParameters  = Nothing,
        objectInternalCode              = Nothing,
        objectInternalTargetFunction    = Nothing,
        objectInternalBoundThis         = Nothing,
        objectInternalBoundArguments    = Nothing,
        objectInternalMatch             = Nothing,
        objectInternalParameterMap      = Nothing }

  mInternalObject consoleObj ?= consoleObjInt

  defineGlobalProperty
    "console"
    (PropertyData DataDescriptor {
        dataDescriptorValue          = inj consoleObj,
        dataDescriptorWritable       = True,
        dataDescriptorEnumerable     = False,
        dataDescriptorConfigurable   = True })

consoleLogCallImpl :: (Functor m, Monad m, MonadIO m) => InternalCallType m
consoleLogCallImpl f this (List args) = do
  forM (intersperse (inj " ") args) $ \v -> toString v >>= liftIO . putStr
  liftIO $ putStrLn ""
  return (inj Undefined)
