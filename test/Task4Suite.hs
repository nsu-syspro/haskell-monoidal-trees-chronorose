{-# LANGUAGE TypeAbstractions #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Task4Suite where

import Test.Tasty hiding (TestTree)
import qualified Test.Tasty as TT
import Test.Tasty.QuickCheck hiding ((><))
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
import Task4.Tree (Tree(..), Node(..), Digit(..), single, node2, node3, split, (><))
import qualified Task4.Tree as T
import Task4.Seq (Seq(..), Elem(..))
import qualified Task4.Seq as S
import Task4.PQueue (PQueue(..), Entry(..))
import qualified Task4.PQueue as P


task4Tests :: TT.TestTree
task4Tests = testGroup "Task4"
  [ testGroup "Tree"
    [ testGroup "Smart constructors"
      [ testProperty "single" $
          withMaxSuccess 100 $ counterexample "unexpected result for" $
            \s ->
              single @String @String s === Single s

      , testProperty "node2" $
          withMaxSuccess 100 $ counterexample "unexpected result for" $
            \(l, r) ->
              node2 @(Sum Int) @(Sum Int) l r === Node2 (measure l <> measure r) l r

      , testProperty "node3" $
          withMaxSuccess 100 $ counterexample "unexpected result for" $
            \(l, m, r) ->
              node3 @(Sum Int) @(Sum Int) l m r === Node3 (measure l <> measure m <> measure r) l m r

      -- TODO: deep
      ]

    , testGroup "Tree invariants"
      [ treeInvariants "Valid structure" 100 $
          isValidTree @(Sum Int) @(Sum Int) measure measure . unTestTree
      ]

    , monoidalProprties @Tree 1000

    , testProperty "measure of tree is consistent" $
        withMaxSuccess 100 $ counterexample "unexpected measure for" $
          \(TestTree @(Sum Int) @(Sum Int) tree) ->
            measure tree === case tree of
                Empty -> mempty
                Single v -> measure v
                Deep m _ _ _ -> m

    , testProperty "toList traverses via in-order" $
        withMaxSuccess 1000 $ counterexample "unexpected order for" $
          \(TestTree @() @Int tree) ->
            toList tree === case tree of
                Empty -> []
                Single v -> [v]
                Deep _ l m r -> toList l ++ concatMap toList (toList m) ++ toList r

    , testProperty "toList . uncurry (><) . split (Sum x <) . toTree == id" $
        withMaxSuccess 1000 $ counterexample "unexpected result for (x, xs)" $
          \(x, xs) ->
            classify (Sum x < sum xs) "inbounds" $
              (toList . uncurry (><) . split (Sum x <) . toTree @Tree @[] @(Sum Int) @(Sum Int)) xs === xs
    ]

  , testGroup "Seq"
    [ testCase "empty constructor" $ do
        assertEqual "empty @Int" (Seq T.Empty) (S.empty @Seq @Int)

    , testGroup "Tree invariants"
      [ seqInvariants "Valid structure" 100 $
          isValidTree measure measure . S.getTree @Int . unTestSeq
      ]

    , seqProprties @TestSeq @Int 1000
    ]

  , testGroup "PQueue"
    [ testCase "empty constructor" $ do
        assertEqual "empty @Int @Int" (PQueue T.Empty) (P.empty @PQueue @Int @Int)

    , testGroup "Tree invariants"
      [ pqueueInvariants "Valid structure" 100 $
          isValidTree measure measure . P.getTree @Int @Int . unTestPQueue
      ]

    , pqueueProprties @TestPQueue @Int @Int 1000
    ]
  ]

task4Checks :: TT.TestTree
task4Checks = testGroup "SelfCheck4"
  [ testGroup "Tree invariants"
    [ testGroup "Valid structure"
      [ testProperty "arbitrary" $
        withMaxSuccess 100 $
          \(TestTree xs) ->
            classify (xs == Empty) "empty" $
              isValidTree @(Sum Int) @(Sum Int) (measure . TestTree) (measure . TestDigit) xs

      , testProperty "shrink" $
        withMaxSuccess 100 $ noShrinking $
          \xs ->
            conjoin $ (\(TestTree xs') ->
                  isValidTree @(Sum Int) @(Sum Int) (measure . TestTree) (measure . TestDigit) xs') <$> take 100 (shrink xs)
      ]
    ]
  ]

-- * Common

isValidTree :: (Eq m, Measured m (Digit a), Measured m a, Show m, Show a)
            => (forall b. Measured m b => Tree m b -> m)
            -> (forall b. Measured m b => Digit b -> m)
            -> Tree m a -> Property
isValidTree _ _ Empty = property True
isValidTree _ _ (Single _) = property True
isValidTree ft fd t@(Deep n l m r) = counterexample ("inconsistent measure " <> show t) $ n == fd l <> ft m <> fd r
  .&&. isValidTree ft fd m
  .&&. conjoin (map (isValidNode measure) $ treeToList m)

isValidNode :: (Eq m, Measured m a, Show m, Show a) => (a -> m) -> Node m a -> Property
isValidNode f t@(Node2 m a b) = counterexample ("inconsistent measure " <> show t) $ m == f a <> f b
isValidNode f t@(Node3 m a b c) = counterexample ("inconsistent measure " <> show t) $ m == f a <> f b <> f c

treeToList :: Tree m a -> [a]
treeToList Empty = []
treeToList (Single x) = [x]
treeToList (Deep _ l m r) = digitToList l ++ concatMap nodeToList (treeToList m) ++ digitToList r

nodeToList :: Node m a -> [a]
nodeToList (Node2 _ l r) = [l, r]
nodeToList (Node3 _ l m r) = [l, m, r]

digitToList :: Digit a -> [a]
digitToList (One a) = [a]
digitToList (Two a b) = [a, b]
digitToList (Three a b c) = [a, b, c]
digitToList (Four a b c d) = [a, b, c, d]

-- * Tree

newtype TestDigit a = TestDigit { unTestDigit :: Digit a }

instance Show a => Show (TestDigit a) where
  show (TestDigit x) = show x

instance Measured m a => Measured m (TestDigit a) where
  measure (TestDigit (One a)) = measure a
  measure (TestDigit (Two a b)) = measure a <> measure b
  measure (TestDigit (Three a b c)) = measure a <> measure b <> measure c
  measure (TestDigit (Four a b c d)) = measure a <> measure b <> measure c <> measure d

instance (Arbitrary a) => Arbitrary (TestDigit a) where
  arbitrary = TestDigit <$> oneof
    [ One <$> arbitrary
    , Two <$> arbitrary <*> arbitrary
    , Three <$> arbitrary <*> arbitrary <*> arbitrary
    , Four <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
    ]
  shrink (TestDigit (One a)) = [TestDigit (One a') | a' <- shrink a]
  shrink (TestDigit (Two a b)) =
       shrink (TestDigit (One a))
    ++ [TestDigit (Two a' b') | (a', b') <- shrink (a, b)]
  shrink (TestDigit (Three a b c)) =
       shrink (TestDigit (Two a b))
    ++ [TestDigit (Three a' b' c') | (a', b', c') <- shrink (a, b, c)]
  shrink (TestDigit (Four a b c d)) =
       shrink (TestDigit (Three a b c))
    ++ [TestDigit (Four a' b' c' d') | (a', b', c', d') <- shrink (a, b, c, d)]

instance (Measured m a, Arbitrary a) => Arbitrary (Node m a) where
  arbitrary = oneof
    [ testNode2 <$> arbitrary <*> arbitrary
    , testNode3 <$> arbitrary <*> arbitrary <*> arbitrary
    ]
  shrink ((Node2 _ a b)) = [testNode2 a' b' | (a', b') <- shrink (a, b)]
  shrink ((Node3 _ a b c)) =
       shrink (testNode2 a b)
    ++ shrink (testNode2 b c)
    ++ shrink (testNode2 a c)
    ++ [testNode3 a' b' c' | (a', b', c') <- shrink (a, b, c)]

newtype TestTree m a = TestTree { unTestTree :: Tree m a }
  deriving MonoidalTree

instance (Show m, Show a) => Show (TestTree m a) where
  show (TestTree x) = show x

instance Measured m a => Measured m (TestTree m a) where
  measure (TestTree Empty) = mempty
  measure (TestTree (Single x)) = measure x
  measure (TestTree (Deep m _ _ _)) = m

testSingle :: a -> TestTree m a
testSingle = TestTree . Single

testNode2 :: Measured m a => a -> a -> Node m a
testNode2 l r = Node2 (measure l <> measure r) l r

testNode3 :: Measured m a => a -> a -> a -> Node m a
testNode3 l m r = Node3 (measure l <> measure m <> measure r) l m r

testDeep :: (Measured m (TestDigit a), Measured m a) => TestDigit a -> TestTree m (Node m a) -> TestDigit a -> TestTree m a
testDeep l m r = TestTree $ Deep (measure l <> measure m <> measure r) (unTestDigit l) (unTestTree m) (unTestDigit r)

testNodeMeasure :: Node m a -> m
testNodeMeasure (Node2 m _ _) = m
testNodeMeasure (Node3 m _ _ _) = m

instance (Measured m a, Arbitrary a) => Arbitrary (TestTree m a) where
  arbitrary = sized arbitrarySizedTree
  shrink (TestTree Empty) = []
  shrink (TestTree (Single x)) = TestTree Empty : (testSingle <$> shrink x)
  shrink (TestTree (Deep _ l m r)) =
       [TestTree Empty]
    ++ map testSingle (digitToList l ++ digitToList r)
    ++ [testDeep l' m' r' | (l', m', r') <- shrink (TestDigit l, TestTree m, TestDigit r)]

arbitrarySizedTree :: (Measured m (TestDigit a), Measured m a, Arbitrary a) => Int -> Gen (TestTree m a)
arbitrarySizedTree 0 = pure $ TestTree Empty
arbitrarySizedTree 1 = testSingle <$> arbitrary
arbitrarySizedTree h = do
  h' <- chooseInt (0, h - 1)
  l <- arbitrary
  m <- arbitrarySizedTree h'
  r <- arbitrary
  pure $ testDeep l m r

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
