module Task1Suite where

import Test.Tasty
import Test.Tasty.QuickCheck hiding (getSize)

import Task1

task1Tests :: TestTree
task1Tests = testGroup "Task1"
  [ testGroup "Min"
    [ monoidTests (getTestMin @Int)
    , testProperty "measure consistency: measure xs == minimum xs" $
        withMaxSuccess 100 $ counterexample "unexpected measure for" $
          \xs ->
            let m = measure @(Min Int) @[Int] xs
            in m === case xs of
              [] -> PosInf
              _  -> Min (minimum xs)
    ]

  , testGroup "Max"
    [ monoidTests (getTestMax @Int)
    , testProperty "measure consistency: measure xs == maximum xs" $
        withMaxSuccess 100 $ counterexample "unexpected measure for" $
          \xs ->
            let m = measure @(Max Int) @[Int] xs
            in m === case xs of
              [] -> NegInf
              _  -> Max (maximum xs)
    ]

  , testGroup "MinMax"
    [ monoidTests (getTestMinMax @Int)
    , testProperty "measure consistency: measure xs == (minimum xs, maximum xs)" $
        withMaxSuccess 100 $ counterexample "unexpected measure for" $
          \xs ->
            let m = measure @(MinMax Int) @[Int] xs
            in m === case xs of
              [] -> MinMax (PosInf, NegInf)
              _  -> MinMax (Min (minimum xs), Max (maximum xs))
    ]

  , testGroup "Size"
    [ monoidTests getTestSize
    , testProperty "measure consistency: measure xs == length xs" $
        withMaxSuccess 100 $ counterexample "unexpected measure for" $
          \xs ->
            getSize (measure @(Size Int) @[Int] xs) === length xs
    ]
  ]

monoidTests :: (Arbitrary t, Show m, Show t, Monoid m, Eq m) => (t -> m) -> TestTree
monoidTests unwrap = testGroup "Monoid laws"
    [ testProperty "associativity: (x <> y) <> z == x <> (y <> z)" $
        withMaxSuccess 100 $ counterexample "unexpected result of " $
          \(tx, ty, tz) ->
            let (x, y, z) = (unwrap tx, unwrap ty, unwrap tz)
            in (x <> y) <> z === x <> (y <> z)

    , testProperty "left identity: mempty <> x == x" $
        withMaxSuccess 100 $ counterexample "unexpected result of " $
          \t ->
            let x = unwrap t
            in mempty <> x == x

    , testProperty "right identity: x <> mempty == x" $
        withMaxSuccess 100 $ counterexample "unexpected result of " $
          \t ->
            let x = unwrap t
            in x <> mempty == x
    ]

task1Checks :: TestTree
task1Checks = testGroup "SelfCheck1"
  [ testGroup "Measured"
    [ testProperty "measure of string is string" $
        withMaxSuccess 100 $ counterexample "unexpected measure for" $
          \xs -> measure @String @String xs === xs

    , testProperty "measure of list of strings is concat" $
        withMaxSuccess 100 $ counterexample "unexpected measure for" $
          \xs -> measure @String @[String] xs === concat xs
    ]
  ]

-- * Min

newtype TestMin a = TestMin { getTestMin :: Min a }

instance Show a => Show (TestMin a) where
  show (TestMin x) = show x

instance Arbitrary a => Arbitrary (TestMin a) where
  arbitrary = frequency
    [ (1, pure $ TestMin PosInf)
    , (9, TestMin . Min <$> arbitrary)
    ]
  shrink (TestMin PosInf) = []
  shrink (TestMin (Min x)) = map TestMin $ PosInf : map Min (shrink x)

-- * Max

newtype TestMax a = TestMax { getTestMax :: Max a }

instance Show a => Show (TestMax a) where
  show (TestMax x) = show x

instance Arbitrary a => Arbitrary (TestMax a) where
  arbitrary = frequency
    [ (1, pure $ TestMax NegInf)
    , (9, TestMax . Max <$> arbitrary)
    ]
  shrink (TestMax NegInf) = []
  shrink (TestMax (Max x)) = map TestMax $ NegInf : map Max (shrink x)

-- * MinMax

newtype TestMinMax a = TestMinMax { getTestMinMax :: MinMax a }

instance Show a => Show (TestMinMax a) where
  show (TestMinMax x) = show x

instance Arbitrary a => Arbitrary (TestMinMax a) where
  arbitrary = do
    TestMin x <- arbitrary
    TestMax y <- arbitrary
    pure $ TestMinMax (MinMax (x, y))
  shrink (TestMinMax (MinMax (x, y))) =
    [ TestMinMax (MinMax (mx, my))
    | TestMin mx <- shrink (TestMin x)
    , TestMax my <- shrink (TestMax y)
    ]

-- * Size

newtype TestSize a = TestSize { getTestSize :: Size a }

instance Show (TestSize a) where
  show (TestSize x) = show x

instance Arbitrary (TestSize a) where
  arbitrary = TestSize . Size . getNonNegative <$> arbitrary
  shrink = map (TestSize . Size . getNonNegative) . shrink . NonNegative . getSize . getTestSize
