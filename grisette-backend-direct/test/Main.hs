{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Grisette.TestUtils.Runner
import qualified Spec

main :: IO ()
main = runGrisetteTests "backend-direct" Spec.spec
