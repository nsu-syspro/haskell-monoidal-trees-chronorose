{-# OPTIONS_GHC -Wall #-}
-- The above pragma enables all warnings

module Task2.Tree where

import Common.MonoidalTree

import Task1 (Measured(..))

-- * Binary tree definition

-- | Binary tree with values 'a' in leaves
-- Intermediate branches contain only accumulated measure 'm'
data Tree m a
  = Empty
  | Leaf a
  | Branch m (Tree m a) (Tree m a)
  deriving (Show, Eq)

-- | Measures given tree using provided measure of 'a'
instance Measured m a => Measured m (Tree m a) where
  measure = error "TODO: define measure (Measured m (Task2.Tree m a))"

instance Foldable (Tree m) where
  foldMap = error "TODO: define foldMap (Foldable (Task2.Tree m))"

-- * Smart constructors

leaf :: a -> Tree m a
leaf = error "TODO: define leaf (Task2.Tree)"

branch :: Measured m a => Tree m a -> Tree m a -> Tree m a
branch = error "TODO: define branch (Task2.Tree)"

-- * Monoidal tree instance

instance MonoidalTree Tree where
  toTree = error "TODO: define toTree (MonoidalTree Task2.Tree)"
  (<|) = error "TODO: define (<|) (MonoidalTree Task2.Tree)"
  (|>) = error "TODO: define (|>) (MonoidalTree Task2.Tree)"
