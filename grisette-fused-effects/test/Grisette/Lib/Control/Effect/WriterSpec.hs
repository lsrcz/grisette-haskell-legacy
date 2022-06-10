module Grisette.Lib.Control.Effect.WriterSpec where

import Control.Carrier.Lift
import Control.Carrier.Writer.Strict
import Data.Monoid
import Grisette.Core
import Grisette.Lib.Control.Carrier.Lift ()
import Grisette.Lib.Control.Carrier.Writer.Strict ()
import Grisette.Lib.Control.Effect.Writer
import Grisette.TestUtils.SBool
import Test.Hspec

spec :: Spec
spec = do
  describe "Writer effect functions should work" $ do
    let w1 = mrgTell (10 :: Sum Int) :: WriterC (Sum Int) (LiftC (UnionMBase SBool)) ()
    let w2 = mrgTell (20 :: Sum Int) :: WriterC (Sum Int) (LiftC (UnionMBase SBool)) ()
    let w1' = tell (10 :: Sum Int) >> return 20 :: WriterC (Sum Int) (LiftC (UnionMBase SBool)) (Sum Int)
    let w2' = tell (20 :: Sum Int) >> return 10 :: WriterC (Sum Int) (LiftC (UnionMBase SBool)) (Sum Int)
    it "mrgTell should work" $ do
      runM (runWriter w1) `shouldBe` mrgReturn (10, ())
      runM (runWriter w2) `shouldBe` mrgReturn (20, ())
      runM (runWriter $ w1 >> w2) `shouldBe` mrgReturn (30, ())
    it "mrgListen should work" $ do
      runM (runWriter $ mrgListen w1')
        `shouldBe` mrgReturn ((10, (10, 20)) :: (Sum Int, (Sum Int, Sum Int)))
      runM (runWriter $ mrgListen w2')
        `shouldBe` mrgReturn ((20, (20, 10)) :: (Sum Int, (Sum Int, Sum Int)))
      runM (runWriter $ w1' >> mrgListen w2')
        `shouldBe` mrgReturn ((30, (20, 10)) :: (Sum Int, (Sum Int, Sum Int)))
    it "mrgListens should work" $ do
      runM (runWriter $ mrgListens (+ 1) w1')
        `shouldBe` mrgReturn ((10, (11, 20)) :: (Sum Int, (Sum Int, Sum Int)))
      runM (runWriter $ mrgListens (+ 1) w2')
        `shouldBe` mrgReturn ((20, (21, 10)) :: (Sum Int, (Sum Int, Sum Int)))
      runM (runWriter $ w1' >> mrgListens (+ 1) w2')
        `shouldBe` mrgReturn ((30, (21, 10)) :: (Sum Int, (Sum Int, Sum Int)))
    it "mrgCensor should work" $ do
      runM (runWriter $ mrgCensor (+ (1 :: Sum Int)) w1')
        `shouldBe` mrgReturn ((11, 20) :: (Sum Int, Sum Int))
      runM (runWriter $ mrgCensor (+ (1 :: Sum Int)) w2')
        `shouldBe` mrgReturn ((21, 10) :: (Sum Int, Sum Int))
      runM (runWriter $ w1' >> mrgCensor (+ (1 :: Sum Int)) w2')
        `shouldBe` mrgReturn ((31, 10) :: (Sum Int, Sum Int))
