{-# OPTIONS_GHC -Wall #-}

-- The above pragma enables all warnings

module Task2.Seq where

-- import Common.MonoidalTree
import Common.Sequence
import Data.Foldable (Foldable (foldl'))
import Task1 (Measured (..), Size (..))
import Task2.Tree

-- * Sequence definition

-- | Random-access sequence based on binary tree
newtype Seq a = Seq {getTree :: Tree (Size a) (Elem a)}
  deriving (Show, Eq)

-- | Sequence element wrapper
newtype Elem a = Elem {getElem :: a}
  deriving (Show, Eq)

-- | Measures given element as 'Size 1'
instance Measured (Size a) (Elem a) where
  measure = const $ Size 1

instance Foldable Seq where
  foldMap f a = foldMap (f . getElem) (getTree a)

  -- An O(1) implementation of length is possible
  -- due to size of the tree being cached at each node
  length :: forall a. Seq a -> Int
  length = getSize . (measure :: Tree (Size a) (Elem a) -> Size a) . getTree

-- * Sequence instance

-- TODO: generalize, beautify, simplify
treeInsertAt :: Int -> a -> Tree (Size a) (Elem a) -> Tree (Size a) (Elem a)
treeInsertAt _ v Empty = (leaf . Elem) v
treeInsertAt ind v (Leaf a) = if ind <= 0 then branch (leaf $ Elem v) (Leaf a) else branch (Leaf a) (leaf $ Elem v)
treeInsertAt ind v (Branch _ l r) =
  let leftMeasure :: Int
      leftMeasure = (getSize . (measure :: Tree (Size a) (Elem a) -> Size a)) l
   in if ind <= leftMeasure
        then branch (treeInsertAt ind v l) r
        else branch l (treeInsertAt (ind - leftMeasure) v r)

treeElemAt :: Int -> Tree (Size a) (Elem a) -> Maybe a
treeElemAt _ Empty = Nothing
treeElemAt ind (Leaf a) = if ind == 0 then (Just . getElem) a else Nothing
treeElemAt ind (Branch _ l r) =
  let leftMeasure :: Int
      leftMeasure = (getSize . (measure :: Tree (Size a) (Elem a) -> Size a)) l
   in if ind < leftMeasure
        then treeElemAt ind l
        else treeElemAt (ind - leftMeasure) r

treeRemoveAt :: Int -> Tree (Size a) (Elem a) -> Tree (Size a) (Elem a)
treeRemoveAt _ Empty = Empty
treeRemoveAt ind (Leaf a) = if ind == 0 then Empty else Leaf a
treeRemoveAt ind (Branch _ l r) =
  let leftMeasure :: Int
      leftMeasure = (getSize . (measure :: Tree (Size a) (Elem a) -> Size a)) l
   in if ind < leftMeasure
        then case treeRemoveAt ind l of
          Empty -> r
          tree -> branch tree r
        else case treeRemoveAt (ind - leftMeasure) r of
          Empty -> l
          tree -> branch l tree

instance Sequence Seq where
  empty = Seq Empty
  toSequence = foldl' (|+) empty
  (+|) = insertAt 0
  (|+) sq = flip (insertAt (length sq)) sq
  insertAt ind v = Seq . treeInsertAt ind v . getTree
  removeAt ind = Seq . treeRemoveAt ind . getTree
  elemAt ind = treeElemAt ind . getTree
