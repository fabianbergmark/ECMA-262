{-# LANGUAGE OverlappingInstances,
             FlexibleInstances,
             IncoherentInstances,
             MultiParamTypeClasses,
             TypeOperators,
             TypeSynonymInstances #-}

module Language.JavaScript.SubType
       where

import Control.Monad (join)

type a + b = Either a b
infixr 6 +

class SubType sub sup where
  inj :: sub -> sup
  prj :: sup -> Maybe sub

instance SubType a a where
  inj = id
  prj = Just

instance SubType a (a + b) where
  inj = Left
  prj (Left x) = Just x
  prj _ = Nothing

instance (SubType a c) => SubType a (b + c) where
  inj = Right . inj
  prj (Right c) = prj c
  prj _ = Nothing

instance (SubType b d) => SubType (a + b) (a + c + d) where
  inj (Left a) = Left a
  inj (Right b) = Right . Right $ inj b
  prj (Left a) = Just (Left a)
  prj (Right (Left _)) = Nothing
  prj (Right (Right d)) = Right `fmap` prj d

instance SubType a b => SubType a (Maybe b) where
  inj = Just . inj
  prj a = join $ fmap prj a
