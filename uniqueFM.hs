module UniqueFM where

import Data.Maybe
import qualified Data.IntMap as I

import Unique

newtype UniqueFM a = UFM { unUFM :: I.IntMap a }

emptyUFM :: UniqueFM a
emptyUFM = UFM I.empty

singletonUFM :: Uniquable k => k -> a -> UniqueFM a
singletonUFM k a = UFM $ I.singleton (getKey $ getUnique k) a

insertUFM :: Uniquable k => k -> a -> UniqueFM a -> UniqueFM a 
insertUFM k a m = insertUFM_u (getUnique k) a m

insertUFM_u :: Unique -> a -> UniqueFM a -> UniqueFM a
insertUFM_u k a (UFM m) = UFM $ I.insert (getKey k) a m 

listToUFM :: Uniquable k => [(k, a)] -> UniqueFM a
listToUFM = foldl (\m (k, a) -> insertUFM k a m) emptyUFM

listToUFM_u :: [(Unique, a)] -> UniqueFM a
listToUFM_u = foldl (\m (k, a) -> insertUFM_u k a m) emptyUFM

lookupUFM :: Uniquable k => k -> UniqueFM a -> Maybe a
lookupUFM k m = lookupUFM_u (getUnique k) m

lookupUFM_u :: Unique -> UniqueFM a -> Maybe a
lookupUFM_u k (UFM m) = I.lookup (getKey k) m

memberUFM :: Uniquable k => k -> UniqueFM a -> Bool
memberUFM k = isJust . lookupUFM k 

memberUFM_u :: Unique -> UniqueFM a -> Bool
memberUFM_u k = isJust . lookupUFM_u k