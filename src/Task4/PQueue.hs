{-# OPTIONS_GHC -Wall #-}
-- The above pragma enables all warnings

module Task4.PQueue where

import Common.PriorityQueue

import Task1 (Measured(..), MinMax(..))
import Task4.Tree

newtype PQueue k v = PQueue { getTree :: Tree (MinMax k) (Entry k v) }
  deriving (Show, Eq)

-- | Priority queue entry wrapper
newtype Entry k v = Entry { getEntry :: (k, v) }
  deriving (Show, Eq)

-- | Measures given entry using both minimum and maximum priority 'k'
instance Ord k => Measured (MinMax k) (Entry k v) where
  measure = error "TODO: define measure (Measured (MinMax k) (Task4.Entry k v))"

-- * Priority queue instance

instance PriorityQueue PQueue where
  empty = error "TODO: define empty (PriorityQueue Task4.PQueue)"
  toPriorityQueue = error "TODO: define toPriorityQueue (PriorityQueue Task4.PQueue)"
  entries = error "TODO: define entries (PriorityQueue Task4.PQueue)"
  insert = error "TODO: define insert (PriorityQueue Task4.PQueue)"
  extractMin = error "TODO: define extractMin (PriorityQueue Task4.PQueue)"
  extractMax = error "TODO: define extractMax (PriorityQueue Task4.PQueue)"
