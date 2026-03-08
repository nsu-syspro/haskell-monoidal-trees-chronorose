{-# OPTIONS_GHC -Wall #-}
-- The above pragma enables all warnings

module Common.MonoidalTree where

import Task1

-- | Tree with values 'a' measured using measure 'm'
class MonoidalTree t where

  -- | Converts Foldable 'f' to a tree
  --
  -- For instances implementing Foldable themselves,
  -- order should be consistent with corresponding 'toList':
  --
  -- > toList . toTree == id
  toTree :: (Foldable f, Measured m a) => f a -> t m a

  -- | Prepends given value to tree
  (<|) :: Measured m a => a -> t m a -> t m a

  -- | Appends given value to tree
  (|>) :: Measured m a => t m a -> a -> t m a
