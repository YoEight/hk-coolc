{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Unique where

import Data.Int
import Data.HashTable

data Unique = MkUnique Int

instance Show Unique where
  show (MkUnique x) = show x

class Uniquable a where
  getUnique :: a -> Unique

instance Uniquable Int where
  getUnique = MkUnique . fromIntegral . hashInt

instance Uniquable String where
  getUnique = MkUnique . fromIntegral . hashString

getKey :: Unique -> Int
getKey (MkUnique x) = x