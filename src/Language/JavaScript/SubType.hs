{-# LANGUAGE FlexibleInstances,
             MultiParamTypeClasses,
             TypeOperators,
             TypeSynonymInstances #-}

module Language.JavaScript.SubType
       where

import Control.Monad (join)

type a + b = Either a b
infixr 6 +

class Inject sub sup where
  inj :: sub -> sup

instance Inject a a where
  inj = id

instance Inject a (a + b) where
  inj = Left

class Project sup sub where
  prj :: sup -> Maybe sub

instance Project a a where
  prj = Just

instance (Project a c) => Project (a + b) c where
  prj (Left x) = prj x
  prj _ = Nothing

s :: a + c -> a + b + c
s (Left v) = Left v
s (Right v) = Right . Right $ v

s2 :: a + b + d -> a + b + c + d
s2 (Left v) = Left v
s2 (Right (Left v)) = Right . Left $ v
s2 (Right (Right v)) = Right . Right . Right $ v

r = Right

l = Left
