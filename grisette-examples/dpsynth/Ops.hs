{-# LANGUAGE OverloadedStrings #-}

module Ops where

import Core
import qualified Data.HashMap.Strict as M
import Grisette

availableUnary :: (SupportedPrim a, Num (Sym a)) => UnaryFuncMap (Sym a)
availableUnary =
  M.fromList
    [ ("zero", const $ mrgReturn 0),
      ("-", mrgReturn . negate),
      ("id", mrgReturn)
    ]

availableBinary :: (SupportedPrim a, Num (Sym a), SOrd SymBool (Sym a)) => BinaryFuncMap (Sym a)
availableBinary =
  M.fromList
    [ ("+", \x y -> mrgReturn $ x + y),
      ("-", \x y -> mrgReturn $ x - y),
      ("-comp", \x y -> mrgReturn $ y - x),
      ("max", \x y -> mrgReturn $ mrgIte (x >=~ y :: SymBool) x y),
      ("min", \x y -> mrgReturn $ mrgIte (x >=~ y :: SymBool) y x)
    ]
