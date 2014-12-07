module Language.JavaScript.Util
       where

import Text.Parsec

applyRest :: Stream s m t =>
             ParsecT s u m (b -> ParsecT s u m b) -> b -> ParsecT s u m b
applyRest pr a = do
  mr <- optionMaybe $ try pr
  case mr of
   Just r -> r a
   Nothing -> return a
