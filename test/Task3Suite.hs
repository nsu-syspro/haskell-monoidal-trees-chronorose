{-# LANGUAGE TypeAbstractions #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Task3Suite where

import Test.Tasty hiding (TestTree)
import qualified Test.Tasty as TT
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit

import CommonSuite
import Common.MonoidalTree
import Common.Sequence
import qualified Common.Sequence as S
import Common.PriorityQueue
import qualified Common.PriorityQueue as P
import Data.Foldable (toList)
import Data.Monoid (Sum(..))

import Task1
import Task3.Tree (Tree(..), leaf, node2, node3)
import qualified Task3.Tree as T
import Task3.Seq (Seq(..), Elem(..))
import qualified Task3.Seq as S
import Task3.PQueue (PQueue(..), Entry(..))
import qualified Task3.PQueue as P


task3Tests :: TT.TestTree
task3Tests = testGroup "Task3"
  [ testGroup "Tree"
    [ testGroup "Smart constructors"
      [ testProperty "leaf" $
          withMaxSuccess 100 $ counterexample "unexpected result for" $
            \s ->
              leaf @String @String s === Leaf s

      , testProperty "node2" $
          withMaxSuccess 100 $ counterexample "unexpected result for" $
            \(TestTree l, TestTree r) ->
              node2 @(Sum Int) @(Sum Int) l r === Node2 (measure l <> measure r) l r

      , testProperty "node3" $
          withMaxSuccess 100 $ counterexample "unexpected result for" $
            \(TestTree l, TestTree m, TestTree r) ->
              node3 @(Sum Int) @(Sum Int) l m r === Node3 (measure l <> measure m <> measure r) l m r
      ]

    , testGroup "Tree invariants"
      [ treeInvariants "Valid structure" 100 $
          isValidTree @(Sum Int) @(Sum Int) measure . unTestTree

      , treeInvariants "Balanced (all leaves have same depth)" 100 $
          isValidTree @() @Int measure . unTestTree
      ]

    , monoidalProprties @Tree 1000

    , testProperty "measure of tree is consistent" $
        withMaxSuccess 100 $ counterexample "unexpected measure for" $
          \(TestTree @(Sum Int) @(Sum Int) tree) ->
            measure tree === case tree of
                Empty -> mempty
                Leaf v -> measure v
                Node2 m _ _ -> m
                Node3 m _ _ _ -> m

    , testProperty "toList traverses via in-order" $
        withMaxSuccess 1000 $ counterexample "unexpected order for" $
          \(TestTree @() @Int tree) ->
            toList tree === case tree of
                Empty -> []
                Leaf v -> [v]
                Node2 _ l r -> toList l ++ toList r
                Node3 _ l m r -> toList l ++ toList m ++ toList r
    ]

  , testGroup "Seq"
    [ testCase "empty constructor" $ do
        assertEqual "empty @Int" (Seq T.Empty) (S.empty @Seq @Int)

    , testGroup "Tree invariants"
      [ seqInvariants "Valid structure" 100 $
          isValidTree measure . S.getTree @Int . unTestSeq

      , seqInvariants "Balanced (all leaves have same depth)" 100 $
          isValidTree measure . S.getTree @Int . unTestSeq
      ]

    , seqProprties @TestSeq @Int 1000
    ]

  , testGroup "PQueue"
    [ testCase "empty constructor" $ do
        assertEqual "empty @Int @Int" (PQueue T.Empty) (P.empty @PQueue @Int @Int)

    , testGroup "Tree invariants"
      [ pqueueInvariants "Valid structure" 100 $
          isValidTree measure . P.getTree @Int @Int . unTestPQueue

      , pqueueInvariants "Balanced (all leaves have same depth)" 100 $
          isValidTree measure . P.getTree @Int @Int . unTestPQueue
      ]

    , pqueueProprties @TestPQueue @Int @Int 1000
    ]
  ]

task3Checks :: TT.TestTree
task3Checks = testGroup "SelfCheck3"
  [ testGroup "Tree invariants"
    [ testGroup "Valid structure"
      [ testProperty "arbitrary" $
        withMaxSuccess 100 $
          \(TestTree xs) ->
            classify (xs == Empty) "empty" $
              isValidTree @(Sum Int) @(Sum Int) (measure . TestTree) xs

      , testProperty "shrink" $
        withMaxSuccess 100 $ noShrinking $
          \xs ->
            conjoin $ (\(TestTree xs') ->
                  isValidTree @(Sum Int) @(Sum Int) (measure . TestTree) xs') <$> shrink xs
      ]

    , testGroup "Balanced (all leaves have same depth)"
      [ testProperty "arbitrary" $
        withMaxSuccess 100 $
          \(TestTree xs) ->
            classify (xs == Empty) "empty" $
              isBalancedTree @() @Int xs

      , testProperty "shrink" $
        withMaxSuccess 100 $ noShrinking $
          \xs ->
            conjoin $ (\(TestTree xs') ->
                  isBalancedTree @() @Int xs') <$> shrink xs
      ]
    ]
  ]

-- * Common

isValidTree :: (Eq m, Measured m a, Show m, Show a) => (Tree m a -> m) -> Tree m a -> Property
isValidTree _ Empty = property True
isValidTree f t = counterexample ("invalid tree " <> show t) $ isValidSubtree f t

isValidSubtree :: (Eq m, Measured m a, Show m, Show a) => (Tree m a -> m) -> Tree m a -> Property
isValidSubtree _ Empty = counterexample "unexpected Empty node" False
isValidSubtree _ (Leaf _) = property True
isValidSubtree f t@(Node2 n l r) =
       counterexample ("inconsistent measure " <> show t) (n == f l <> f r)
  .&&. isValidSubtree f l
  .&&. isValidSubtree f r
isValidSubtree f t@(Node3 n l m r) =
       counterexample ("inconsistent measure " <> show t) (n == f l <> f m <> f r)
  .&&. isValidSubtree f l
  .&&. isValidSubtree f m
  .&&. isValidSubtree f r

isBalancedTree :: (Show m, Show a) => Tree m a -> Property
isBalancedTree t =
  let depths = leafDepths 0 t
  in  counterexample ("unbalanced tree " <> show t) $
        counterexample ("leaf depths: " <> show depths) $
          sameElements depths

sameElements :: Eq a => [a] -> Bool
sameElements [] = True
sameElements (x:xs) = all (== x) xs

leafDepths :: Int -> Tree m a -> [Int]
leafDepths _ Empty = []
leafDepths d (Leaf _) = [d]
leafDepths d (Node2 _ l r) = leafDepths (d + 1) l ++ leafDepths (d + 1) r
leafDepths d (Node3 _ l m r) = leafDepths (d + 1) l ++ leafDepths (d + 1) m ++ leafDepths (d + 1) r

-- * Tree

newtype TestTree m a = TestTree { unTestTree :: Tree m a }
  deriving MonoidalTree

instance (Show m, Show a) => Show (TestTree m a) where
  show (TestTree x) = show x

instance Measured m a => Measured m (TestTree m a) where
  measure (TestTree t) = measure (TestNETree t)

instance (Measured m a, Arbitrary a) => Arbitrary (TestTree m a) where
  arbitrary = frequency
    [ (1, pure (TestTree Empty))
    , (99, TestTree . unTestNETree <$> arbitrary)
    ]
  shrink = shrinkMap (TestTree . unTestNETree) (TestNETree . unTestTree)

newtype TestNETree m a = TestNETree { unTestNETree :: Tree m a }

instance (Show m, Show a) => Show (TestNETree m a) where
  show (TestNETree x) = show x

instance Measured m a => Measured m (TestNETree m a) where
  measure (TestNETree Empty) = mempty
  measure (TestNETree (Leaf x)) = measure x
  measure (TestNETree (Node2 m _ _)) = m
  measure (TestNETree (Node3 m _ _ _)) = m

testLeaf :: a -> TestNETree m a
testLeaf = TestNETree . Leaf

testNode2 :: Measured m a => TestNETree m a -> TestNETree m a -> TestNETree m a
testNode2 l r = TestNETree $ Node2 (measure l <> measure r) (unTestNETree l) (unTestNETree r)

testNode3 :: Measured m a => TestNETree m a -> TestNETree m a -> TestNETree m a -> TestNETree m a
testNode3 l m r = TestNETree $ Node3 (measure l <> measure m <> measure r) (unTestNETree l) (unTestNETree m) (unTestNETree r)

instance (Measured m a, Arbitrary a) => Arbitrary (TestNETree m a) where
  arbitrary = sized arbitrarySizedNETree
  shrink (TestNETree Empty) = []
  shrink (TestNETree (Leaf x)) = map testLeaf (shrink x)
  shrink (TestNETree (Node2 _ l r)) =
    -- shrink to subterms
    map TestNETree [l, r] ++
    -- recursively shrink subterms
    shrink (TestNETree l) ++
    shrink (TestNETree r)
  shrink (TestNETree (Node3 _ l m r)) =
    -- shrink to subterms
    map TestNETree [l, m, r] ++
    -- shrink to node2
    [ testNode2 (TestNETree l) (TestNETree m)
    , testNode2 (TestNETree m) (TestNETree r)
    , testNode2 (TestNETree l) (TestNETree r)
    ] ++
    -- recursively shrink subterms
    shrink (TestNETree l) ++
    shrink (TestNETree m) ++
    shrink (TestNETree r)

arbitrarySizedNETree :: (Measured m a, Arbitrary a) => Int -> Gen (TestNETree m a)
arbitrarySizedNETree 0 = testLeaf <$> arbitrary
arbitrarySizedNETree 1 = oneof
  [ (\(l, r) -> testNode2 (testLeaf l) (testLeaf r)) <$> arbitrary
  , (\(l, m, r) -> testNode3 (testLeaf l) (testLeaf m) (testLeaf r)) <$> arbitrary
  ]
arbitrarySizedNETree h = do
  let h' = h `div` 2
  l <- arbitrarySizedNETree h'
  r <- arbitrarySizedNETree h'
  oneof
    [ pure $ testNode2 l r
    , do
      m <- arbitrarySizedNETree h'
      pure $ testNode3 l m r
    ]

-- * Seq

newtype TestSeq a = TestSeq { unTestSeq :: Seq a }
  deriving (Foldable, Sequence)

instance Show a => Show (TestSeq a) where
  show (TestSeq x) = show x

instance Arbitrary a => Arbitrary (Elem a) where
  arbitrary = Elem <$> arbitrary
  shrink = shrinkMap Elem getElem

instance Arbitrary a => Arbitrary (TestSeq a) where
  arbitrary = TestSeq . Seq . unTestTree <$> arbitrary
  shrink = shrinkMap (TestSeq . Seq . unTestTree) (TestTree . S.getTree . unTestSeq)

-- * PQueue

newtype TestPQueue k v = TestPQueue { unTestPQueue :: PQueue k v }
  deriving (PriorityQueue, Eq)

instance (Show k, Show v) => Show (TestPQueue k v) where
  show (TestPQueue x) = show x

instance (Arbitrary k, Arbitrary v) => Arbitrary (Entry k v) where
  arbitrary = Entry <$> arbitrary
  shrink = shrinkMap Entry getEntry

instance (Ord k, Arbitrary k, Arbitrary v) => Arbitrary (TestPQueue k v) where
  arbitrary = TestPQueue . PQueue . unTestTree <$> arbitrary
  shrink = shrinkMap (TestPQueue . PQueue . unTestTree) (TestTree . P.getTree . unTestPQueue)
