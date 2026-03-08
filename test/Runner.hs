import Test.Tasty

import Task1Suite (task1Tests, task1Checks)
import Task2Suite (task2Tests, task2Checks)
import Task3Suite (task3Tests, task3Checks)
import Task4Suite (task4Tests, task4Checks)

main :: IO ()
main = defaultMain $ testGroup "" [checks, tests]

checks :: TestTree
checks = testGroup "Checks"
  [ task1Checks
  , task2Checks
  , task3Checks
  , task4Checks
  ]

tests :: TestTree
tests = testGroup "Tests"
  [ task1Tests
  , task2Tests
  , task3Tests
  , task4Tests
  ]
