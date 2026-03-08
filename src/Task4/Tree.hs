{-# OPTIONS_GHC -Wall #-}
-- The above pragma enables all warnings

module Task4.Tree where

import Common.MonoidalTree

import Task1 (Measured(..))

-- * Finger tree definition

-- | Finger tree with values 'a' in leaves
-- Intermediate branches contain only accumulated measure 'm'
data Tree m a
  = Empty
  | Single a
  | Deep m (Digit a) (Tree m (Node m a)) (Digit a)
  deriving (Show, Eq)

-- | 2-3 node of finger tree
data Node m a
  = Node2 m a a
  | Node3 m a a a
  deriving (Show, Eq)

-- | Finger tree digit
data Digit a
  = One   a
  | Two   a a
  | Three a a a
  | Four  a a a a
  deriving (Show, Eq)

-- | Measures given tree using provided measure of 'a'
instance Measured m a => Measured m (Tree m a) where
  measure = error "TODO: define measure (Measured m (Task4.Tree m a))"

-- | Measures given node using provided measure of 'a'
instance Measured m a => Measured m (Node m a) where
  measure = error "TODO: define measure (Measured m (Task4.Node m a))"

-- | Measures given digit using provided measure of 'a'
instance Measured m a => Measured m (Digit a) where
  measure = error "TODO: define measure (Measured m (Task4.Digit m a))"

instance Foldable (Tree m) where
  foldMap = error "TODO: define foldMap (Foldable (Task4.Tree m))"

instance Foldable (Node m) where
  foldMap = error "TODO: define foldMap (Foldable (Task4.Node m))"

instance Foldable Digit where
  foldMap = error "TODO: define foldMap (Foldable (Task4.Digit m))"

-- * Smart constructors

single :: a -> Tree m a
single = error "TODO: define single (Task4.Tree)"

node2 :: Measured m a => a -> a -> Node m a
node2 = error "TODO: define node2 (Task4.Tree)"

node3 :: Measured m a => a -> a -> a -> Node m a
node3 = error "TODO: define node3 (Task4.Tree)"

deep :: Measured m a => Digit a -> Tree m (Node m a) -> Digit a -> Tree m a
deep = error "TODO: define deep (Task4.Tree)"

-- * Monoidal tree instance

instance MonoidalTree Tree where
  toTree = error "TODO: define toTree (MonoidalTree Task4.Tree)"
  (<|) = error "TODO: define (<|) (MonoidalTree Task4.Tree)"
  (|>) = error "TODO: define (|>) (MonoidalTree Task4.Tree)"

-- * Utility functions

-- | Split result with left part, middle element and right part
data Split f a = Split (f a) a (f a)
  deriving (Show, Eq)

-- | Helper function for spliting tree based on given predicate and starting accumulator value
splitTree :: Measured m a => (m -> Bool) -> m -> Tree m a -> Maybe (Split (Tree m) a)
splitTree = error "TODO: define splitTree"

-- | Splits tree based on given predicate
split :: Measured m a => (m -> Bool) -> Tree m a -> (Tree m a, Tree m a)
split = error "TODO: define split"

-- | Concatenates two trees
infixr 6 ><
(><) :: Measured m a => Tree m a -> Tree m a -> Tree m a
(><) = error "TODO: define (><)"

