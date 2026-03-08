{-# OPTIONS_GHC -Wall #-}
-- The above pragma enables all warnings

module Common.Sequence where

-- | Random-access sequence
class Foldable s => Sequence s where

  -- | Empty sequence
  empty :: s a

  -- | Converts given Foldable 'f' to a sequence
  -- preserving the order:
  --
  -- > toList . toSequence == id
  toSequence :: Foldable f => f a -> s a

  -- | Prepends given element to sequence
  (+|) :: a -> s a -> s a

  -- | Appends given element to sequence
  (|+) :: s a -> a -> s a

  -- | Inserts given element into specified position in sequence
  insertAt :: Int -> a -> s a -> s a

  -- | Removes element at specified position in sequence
  removeAt :: Int -> s a -> s a

  -- | Returns element at specified position in sequence
  -- if it exists wrapped into 'Just' or 'Nothing' otherwise
  elemAt :: Int -> s a -> Maybe a
