{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module CommonSuite where

import Test.Tasty
import Test.Tasty.QuickCheck

import Common.MonoidalTree
import Common.Sequence
import Common.PriorityQueue
import qualified Common.PriorityQueue as P

import Task1
import Data.Foldable (toList)
import Data.List ((!?), sort)

-- * MonoidalTree

treeInvariants :: forall t m a.
    (MonoidalTree t, Arbitrary (t m a), Arbitrary a, Show (t m a), Show a, Measured m a) =>
    String -> Int -> (t m a -> Property) -> TestTree
treeInvariants name n invariant =
  testGroup name
    [ testProperty "toTree xs" $
        withMaxSuccess n $
          \xs -> invariant (toTree @t @[] xs)

    , testProperty "x <| xs" $
        withMaxSuccess n $
          \(x, xs) -> invariant (x <| xs)

    , testProperty "xs |> x" $
        withMaxSuccess n $
          \(xs, x) -> invariant (xs |> x)
    ]

monoidalProprties :: forall t. (Foldable (t ()), MonoidalTree t) => Int -> TestTree
monoidalProprties n =
  testGroup "MonoidalTree"
    [ testProperty "toList (toTree xs) = xs" $
        withMaxSuccess n $ counterexample "unexpected order for" $
          \xs ->
            (toList . toTree @t @[] @() @Int) xs === xs

    , testProperty "toList . (x <|) . toTree == (x :)" $
        withMaxSuccess n $ counterexample "unexpected result for (x, xs)" $
          \(x, xs) ->
            (toList . (x <|) . toTree @t @[] @() @Int) xs === x : xs

    , testProperty "toList . (|> x) . toTree == (++ [x])" $
        withMaxSuccess n $ counterexample "unexpected result for (x, xs)" $
          \(x, xs) ->
            (toList . (|> x) . toTree @t @[] @() @Int) xs === xs ++ [x]
    ]

-- * Sequence

seqInvariants :: forall t a.
    (Sequence t, Arbitrary (t a), Arbitrary a, Show (t a), Show a) =>
    String -> Int -> (t a -> Property) -> TestTree
seqInvariants name n invariant =
  testGroup name
    [ testProperty "toSequence xs" $
        withMaxSuccess n $
          \xs -> invariant (toSequence @t @[] xs)

    , testProperty "x +| xs" $
        withMaxSuccess n $
          \(x, xs) -> invariant (x +| xs)

    , testProperty "xs |+ x" $
        withMaxSuccess n $
          \(xs, x) -> invariant (xs |+ x)

    , testProperty "insertAt i x xs" $
        withMaxSuccess n $
          \(i, x, xs) ->
            classify (0 <= i && i < length (toList xs)) "inbounds" $
              invariant (insertAt i x xs)

    , testProperty "removeAt x xs" $
        withMaxSuccess n $
          \(i, xs) ->
            classify (0 <= i && i < length (toList xs)) "inbounds" $
              invariant (removeAt i xs)
    ]

seqProprties :: forall t a.
    (Sequence t, Arbitrary (t a), Arbitrary a, Show (t a), Show a, Eq a) =>
    Int -> TestTree
seqProprties n =
  testGroup "Sequence"
    [ testProperty "toList . toSequence = id" $
        withMaxSuccess n $ counterexample "unexpected result for (xs)" $
          \xs ->
            toList (toSequence @t @[] @a xs) === xs

    , testProperty "toList . (x +|) . toSequence == (x :)" $
        withMaxSuccess n $ counterexample "unexpected result for (x, xs)" $
          \(x, xs) ->
            (toList . (x +|) . toSequence @t @[] @a) xs === x : xs

    , testProperty "toList . (|+ x) . toSequence == (++ [x])" $
        withMaxSuccess n $ counterexample "unexpected result for (x, xs)" $
          \(x, xs) ->
            (toList . (|+ x) . toSequence @t @[] @a) xs === xs ++ [x]

    , testProperty "toList . insertAt i x . toSequence" $
        withMaxSuccess n $ counterexample "unexpected result for (i, x, xs)" $
          \(i, x, xs) ->
            classify (0 <= i && i < length xs) "inbounds" $
              (toList . insertAt i x . toSequence @t @[] @a) xs === insertList i x xs

    , testProperty "toList . removeAt i . toSequence" $
        withMaxSuccess n $ counterexample "unexpected result for (i, xs)" $
          \(i, xs) ->
            classify (0 <= i && i < length xs) "inbounds" $
              (toList . removeAt i . toSequence @t @[] @a) xs === removeList i xs

    , testProperty "elemAt i . toSequence == (!? i)" $
        withMaxSuccess n $ counterexample "unexpected result for (i, xs)" $
          \(i, xs) ->
            classify (0 <= i && i < length xs) "inbounds" $
              (elemAt i . toSequence @t @[] @a) xs === xs !? i

    , testProperty "(elemAt i . insertAt i x) xs == Just x" $
        withMaxSuccess n $ counterexample "unexpected result for ((x, xs), i)" $
          \(x, xs) ->
            forAll (choose (0, length (toList xs))) $ \i ->
              (elemAt i . insertAt @t @a i x) xs === Just x
    ]

-- * PriorityQueue

pqueueInvariants :: forall t k v.
    (PriorityQueue t, Arbitrary (t k v), Arbitrary k, Arbitrary v, Show (t k v), Show v, Show k, Ord k, Eq (t k v)) =>
    String -> Int -> (t k v -> Property) -> TestTree
pqueueInvariants name n invariant =
  testGroup name
    [ testProperty "toPriorityQueue xs" $
        withMaxSuccess n $
          \xs -> invariant (toPriorityQueue @t @[] xs)

    , testProperty "insert k v xs" $
        withMaxSuccess n $
          \(k, v, xs) -> invariant (insert k v xs)

    , testProperty "extractMin xs" $
        withMaxSuccess n $
          \xs ->
            classify (xs == P.empty) "empty" $
              case extractMin xs of
                Nothing -> counterexample "returned Nothing for non-empty queue" (xs === P.empty)
                Just (_, xs') -> invariant xs'

    , testProperty "extractMax xs" $
        withMaxSuccess 1000 $
          \xs ->
            classify (xs == P.empty) "empty" $
              case extractMax xs of
                Nothing -> counterexample "returned Nothing for non-empty queue" (xs === P.empty)
                Just (_, xs') -> invariant xs'
    ]

pqueueProprties :: forall t k v.
    (PriorityQueue t, Arbitrary (t k v), Arbitrary k, Arbitrary v,
     Show (t k v), Show v, Show k, Ord v, Ord k, Num k, Bounded k) =>
    Int -> TestTree
pqueueProprties n =
  testGroup "PriorityQueue"
    [ testProperty "sort . entries . toPriorityQueue = sort" $
        withMaxSuccess n $ counterexample "unexpected result for (xs)" $
          \xs ->
            (sort . entries . toPriorityQueue @t @[] @k @v) xs === sort xs

    , testProperty "sort . entries . insert k v . toPriorityQueue == sort . ((k, v) :)" $
        withMaxSuccess n $ counterexample "unexpected result for (k, v, xs)" $
          \(k, v, xs) ->
            (sort . entries . insert k v . toPriorityQueue @t @[] @k @v) xs === sort ((k, v) : xs)

    , testProperty "(extractMin . insert minValue x) xs == Just (x, xs)" $
        withMaxSuccess n $
          \(Blind (v, xs)) ->
            let kmin = case map fst $ entries @t @k @v xs of
                  [] -> 1
                  xs' -> minimum xs'
                k = kmin - 1
            in counterexample ("unexpected result for `extractMin (insert "
                                 <> show k <> " " <> show v <> " " <> show xs <> ")`") $
                kmin /= minBound ==> (fmap entries <$> (extractMin . insert k v) xs) === Just (v, entries xs)

    , testProperty "(extractMax . insert maxValue x) xs == Just (x, xs)" $
        withMaxSuccess n $
          \(Blind (v, xs)) ->
            let kmax = case map fst $ entries @t @k @v xs of
                  [] -> 1
                  xs' -> maximum xs'
                k = kmax + 1
            in counterexample ("unexpected result for `extractMax (insert "
                                 <> show k <> " " <> show v <> " " <> show xs <> ")`") $
                kmax /= maxBound ==> (fmap entries <$> (extractMax . insert k v) xs) === Just (v, entries xs)
    ]

instance {-# INCOHERENT #-} Measured () a where
  measure _ = mempty

insertList :: Int -> a -> [a] -> [a]
insertList i x xs = let (l, r) = splitAt i xs in l ++ [x] ++ r

removeList :: Int -> [a] -> [a]
removeList i xs = take i xs ++ drop (i + 1) xs
