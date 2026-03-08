{-# OPTIONS_GHC -Wall #-}
-- The above pragma enables all warnings

module Common.PriorityQueue where

-- | Priority queue supporting both highest and lowest priority access
--
-- * Priority: 'k'
-- * Value: 'v'
class PriorityQueue q where

  -- | Empty queue
  empty :: q k v

  -- | Converts given Foldable 'f' to priority queue
  toPriorityQueue :: (Foldable f, Ord k) => f (k, v) -> q k v

  -- | Returns elements 'v' paired with their priority 'k'
  entries :: q k v -> [(k, v)]

  -- | Inserts given value with priority into queue
  insert :: Ord k => k -> v -> q k v -> q k v

  -- | Returns lowest priority value paired with queue without
  -- that element wrapped into 'Just' if such element exists (non-empty queue),
  -- or returns 'Nothing' otherwise
  extractMin :: Ord k => q k v -> Maybe (v, q k v)

  -- | Returns highest priority value paired with queue without
  -- that element wrapped into 'Just' if such element exists (non-empty queue),
  -- or returns 'Nothing' otherwise
  extractMax :: Ord k => q k v -> Maybe (v, q k v)


