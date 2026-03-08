{-# OPTIONS_GHC -Wall #-}
-- The above pragma enables all warnings

module Task2.PQueue where

import Common.PriorityQueue

import Task1 (Measured(..), MinMax(..))
import Task2.Tree

-- * Priority queue definition

-- | Priority queue based on binary tree
newtype PQueue k v = PQueue { getTree :: Tree (MinMax k) (Entry k v) }
  deriving (Show, Eq)

-- | Priority queue entry wrapper
newtype Entry k v = Entry { getEntry :: (k, v) }
  deriving (Show, Eq)

instance Ord k => Measured (MinMax k) (Entry k v) where
  measure = error "TODO: define measure (Measured (MinMax k) (Task2.Entry k v))"

-- * Priority queue instance

instance PriorityQueue PQueue where
  empty = error "TODO: define empty (PriorityQueue Task2.PQueue)"
  toPriorityQueue = error "TODO: define toPriorityQueue (PriorityQueue Task2.PQueue)"
  entries = error "TODO: define entries (PriorityQueue Task2.PQueue)"
  insert = error "TODO: define insert (PriorityQueue Task2.PQueue)"
  extractMin = error "TODO: define extractMin (PriorityQueue Task2.PQueue)"
  extractMax = error "TODO: define extractMax (PriorityQueue Task2.PQueue)"
