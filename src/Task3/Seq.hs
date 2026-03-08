{-# OPTIONS_GHC -Wall #-}
-- The above pragma enables all warnings

module Task3.Seq where

import Common.Sequence

import Task1 (Measured(..), Size(..))
import Task3.Tree

-- * Sequence definition

-- | Random-access sequence based on binary tree
newtype Seq a = Seq { getTree :: Tree (Size a) (Elem a) }
  deriving (Show, Eq)

-- | Sequence element wrapper
newtype Elem a = Elem { getElem :: a }
  deriving (Show, Eq)

-- | Measures given element as 'Size 1'
instance Measured (Size a) (Elem a) where
  measure = error "TODO: define measure (Measured (Size a) (Task3.Elem a))"

instance Foldable Seq where
  foldMap = error "TODO: define foldMap (Foldable Task3.Seq)"

  -- An O(1) implementation of length is possible
  -- due to size of the tree being cached at each node
  length :: forall a. Seq a -> Int
  length = error "TODO: define length (Foldable Task3.Seq)"

-- * Sequence instance

instance Sequence Seq where
  empty = error "TODO: define empty (Sequence Task3.Seq)"
  toSequence = error "TODO: define toSequence (Sequence Task3.Seq)"
  (+|) = error "TODO: define (+|) (Sequence Task3.Seq)"
  (|+) = error "TODO: define (|+) (Sequence Task3.Seq)"
  insertAt = error "TODO: define insertAt (Sequence Task3.Seq)"
  removeAt = error "TODO: define removeAt (Sequence Task3.Seq)"
  elemAt = error "TODO: define elemAt (Sequence Task3.Seq)"
