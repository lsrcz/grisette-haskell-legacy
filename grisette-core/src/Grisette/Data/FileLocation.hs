{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
module Grisette.Data.FileLocation (
    FileLocation (..),
    nameWithLoc,
    slocsymb,
    ilocsymb,
) where

import Language.Haskell.TH
import Debug.Trace.LocationTH (__LOCATION__)
import GHC.Generics
import Control.DeepSeq
import Grisette.Data.Class.PrimWrapper
import Language.Haskell.TH.Syntax
import Data.Hashable
import Grisette.Data.Class.GenSym

-- File location type.
data FileLocation = FileLocation {locPath :: String, locLineno :: Int, locSpan :: (Int, Int)}
  deriving (Eq, Ord, Generic, Lift, NFData, Hashable)

instance Show FileLocation where
  show (FileLocation p l (s1, s2)) = p ++ ":" ++ show l ++ ":" ++ show s1 ++ "-" ++ show s2

parseFileLocation :: String -> FileLocation
parseFileLocation str =
  let
    r = reverse str
    (s2, r1) = break (=='-') r
    (s1, r2) = break (==':') $ tail r1
    (l, p) = break (==':') $ tail r2
  in
    FileLocation (reverse $ tail p) (read $ reverse l) (read $ reverse s1, read $ reverse s2)

-- | Identifier with the current location as extra information.
--
-- >>> $$(nameWithLoc "a")
-- a:<interactive>:4:4-18
--
-- The uniqueness is ensured for the call to 'nameWithLoc' at different location.
nameWithLoc :: String -> Q (TExp GenSymIdent)
nameWithLoc s = [|| nameWithInfo s (parseFileLocation $$(unsafeTExpCoerce __LOCATION__)) ||]

-- | Generate simply-named symbolic variables. The file location will be attached to identifier.
--
-- $$(slocsymb "a") :: SymBool
-- a:<interactive>:7:4-15
--
-- The uniqueness is ensured for the call to 'slocsymb' at different location.
slocsymb :: (PrimWrapper s c) => String -> Q (TExp s)
slocsymb nm = [|| sinfosymb nm (parseFileLocation $$(unsafeTExpCoerce __LOCATION__)) ||]

-- | Generate indexed symbolic variables. The file location will be attached to identifier.
--
-- $$(ilocsymb 1 "a") :: SymBool
-- a@1:<interactive>:10:4-17
--
-- The uniqueness is ensured for the call to 'ilocsymb' at different location.
ilocsymb :: (PrimWrapper s c) => Int -> String -> Q (TExp s)
ilocsymb idx nm = [|| iinfosymb idx nm (parseFileLocation $$(unsafeTExpCoerce __LOCATION__)) ||]
