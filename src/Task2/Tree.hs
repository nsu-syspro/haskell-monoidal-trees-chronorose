{-# OPTIONS_GHC -Wall #-}

-- The above pragma enables all warnings

module Task2.Tree where

import Common.MonoidalTree
import Task1 (Measured (..))

-- * Binary tree definition

-- | Binary tree with values 'a' in leaves
-- Intermediate branches contain only accumulated measure 'm'
data Tree m a
  = Empty
  | Leaf a
  | Branch m (Tree m a) (Tree m a)
  deriving (Show, Eq)

-- | Measures given tree using provided measure of 'a'
instance (Measured m a) => Measured m (Tree m a) where
  measure Empty = mempty
  measure (Leaf a) = measure a
  measure (Branch m _ _) = m

instance Foldable (Tree m) where
  foldMap _ Empty = mempty
  foldMap f (Leaf a) = f a
  foldMap f (Branch _ l r) = foldMap f l <> foldMap f r

-- * Smart constructors

leaf :: a -> Tree m a
leaf = Leaf

branch :: (Measured m a) => Tree m a -> Tree m a -> Tree m a
branch a b = Branch (measure a <> measure b) a b

-- * Monoidal tree instance

instance MonoidalTree Tree where
  toTree = foldr (<|) Empty
  value <| Empty = leaf value
  value <| tree = branch (leaf value) tree
  Empty |> value = leaf value
  tree |> value = branch tree (leaf value)
