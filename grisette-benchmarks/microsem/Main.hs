module Main where

import Ordered
import Prog
import System.TimeIt
import Test.QuickCheck
import Unordered

runAllBenchmark :: Int -> IO ((Double, Int), (Double, Int), (Double, Int))
runAllBenchmark v = do
  p <- generate $ resize 15 $ genProg 10 1 (chooseInt (0, v))
  let p1 = genCond p
  r1 <- timeItT $ do
    let n = benchmarkUnordered p1
    n `seq` return n
  print r1
  r2 <- timeItT $ do
    let n = benchmarkSorted p1
    n `seq` return n
  print r2
  {-r3 <- timeItT $ do
    let n = benchmarkNaive p1
    n `seq` return n
  print r3-}
  return (r1, r2, (0, 0)) -- r3)

main :: IO ()
main = do
  runAllBenchmark 50 >>= print
  runAllBenchmark 50 >>= print
  runAllBenchmark 50 >>= print
  runAllBenchmark 50 >>= print
  runAllBenchmark 50 >>= print
