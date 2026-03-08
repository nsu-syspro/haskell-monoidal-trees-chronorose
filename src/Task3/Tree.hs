{-# OPTIONS_GHC -Wall #-}
-- The above pragma enables all warnings

module Task3.Tree where

import Common.MonoidalTree

import Task1 (Measured(..))

-- * 2-3 tree definition

-- | 2-3 tree with values 'a' in leaves
-- Intermediate nodes contain only accumulated measure 'm'
data Tree m a
  = Empty
  | Leaf a
  | Node2 m (Tree m a) (Tree m a)
  | Node3 m (Tree m a) (Tree m a) (Tree m a)
  deriving (Show, Eq)

-- | Measures given tree using provided measure of 'a'
instance Measured m a => Measured m (Tree m a) where
  measure = error "TODO: define measure (Measured m (Task3.Tree m a))"

instance Foldable (Tree m) where
  foldMap = error "TODO: define foldMap (Foldable (Task3.Tree m))"

-- * Smart constructors

leaf :: a -> Tree m a
leaf = error "TODO: define leaf (Task3.Tree)"

node2 :: Measured m a => Tree m a -> Tree m a -> Tree m a
node2 = error "TODO: define node2 (Task3.Tree)"

node3 :: Measured m a => Tree m a -> Tree m a -> Tree m a -> Tree m a
node3 = error "TODO: define node3 (Task3.Tree)"

-- * Monoidal tree instance

instance MonoidalTree Tree where
  toTree = error "TODO: define toTree (MonoidalTree Task3.Tree)"
  (<|) = error "TODO: define (<|) (MonoidalTree Task3.Tree)"
  (|>) = error "TODO: define (|>) (MonoidalTree Task3.Tree)"
