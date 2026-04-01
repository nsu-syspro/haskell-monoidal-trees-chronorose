{-# OPTIONS_GHC -Wall #-}

-- The above pragma enables all warnings

module Task2.PQueue where

import Common.MonoidalTree
import Common.PriorityQueue
import Data.Bifunctor (Bifunctor (second))
import Task1 (Measured (..), MinMax (..))
import Task2.Tree

-- * Priority queue definition

-- | Priority queue based on binary tree
newtype PQueue k v = PQueue {getTree :: Tree (MinMax k) (Entry k v)}
  deriving (Show, Eq)

-- | Priority queue entry wrapper
newtype Entry k v = Entry {getEntry :: (k, v)}
  deriving (Show, Eq)

instance (Ord k) => Measured (MinMax k) (Entry k v) where
  measure (Entry (k, _)) = measure k

-- * Priority queue instance

treeExtractMin :: forall k v. (Ord k) => Tree (MinMax k) (Entry k v) -> Maybe (v, Tree (MinMax k) (Entry k v))
treeExtractMin Empty = Nothing
treeExtractMin (Leaf a) = Just ((snd . getEntry) a, Empty)
treeExtractMin (Branch m l r) =
  let (leftMin, _) = getMinMax ((measure :: Tree (MinMax k) (Entry k v) -> MinMax k) l)
      (centralMin, _) = getMinMax m
      tree = if leftMin == centralMin then treeExtractMin l else treeExtractMin r
   in fmap (\(v, t) -> (v, if leftMin == centralMin then branch t r else branch l t)) tree

treeExtractMax :: forall k v. (Ord k) => Tree (MinMax k) (Entry k v) -> Maybe (v, Tree (MinMax k) (Entry k v))
treeExtractMax Empty = Nothing
treeExtractMax (Leaf a) = Just ((snd . getEntry) a, Empty)
treeExtractMax (Branch m l r) =
  let (_, rightMax) = getMinMax ((measure :: Tree (MinMax k) (Entry k v) -> MinMax k) r)
      (_, centralMax) = getMinMax m
      tree = if rightMax == centralMax then treeExtractMin r else treeExtractMin l
   in fmap (\(v, t) -> (v, if rightMax == centralMax then branch l t else branch t r)) tree

instance PriorityQueue PQueue where
  empty = PQueue Empty
  toPriorityQueue = foldr (uncurry insert) empty
  entries = foldr ((:) . getEntry) [] . getTree
  insert k v (PQueue tree) = PQueue (Entry (k, v) <| tree)
  extractMin = fmap (second (foldr (uncurry insert . getEntry) empty)) . treeExtractMin . getTree
  extractMax = fmap (second (foldr (uncurry insert . getEntry) empty)) . treeExtractMax . getTree
