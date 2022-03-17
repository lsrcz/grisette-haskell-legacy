{-# LANGUAGE DeriveAnyClass #-}
module Utils.SBool where
import Grisette.Data.Class.Bool
import Grisette.Data.Class.PrimWrapper
import qualified Data.HashSet as S
import Grisette.Data.Class.ExtractSymbolics
import GHC.Generics
import Data.Hashable
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.Mergeable
import Grisette.Control.Monad

{-
data Term
  = SBoolTerm SBool
  | SIntTerm SInteger
  deriving (Show, Eq)

data SInteger
  = CInteger Integer
  | SSInteger String
  | ISInteger Int String
  deriving (Show, Eq)
  -}

data SBool
  = CBool Bool
  | SSBool String 
  | ISBool Int String 
  | Or SBool SBool
  | And SBool SBool
  | Not SBool
  | Equal SBool SBool
  | ITE SBool SBool SBool
  deriving (Show, Eq)

instance Mergeable SBool SBool where
  mergeStrategy = SimpleStrategy ites

instance SimpleMergeable SBool SBool where
  mrgIte = ites
instance SEq SBool SBool where
  (CBool l) ==~ (CBool r) = CBool (l == r)
  (CBool True) ==~ r = r
  (CBool False) ==~ r = nots r
  l ==~ (CBool True) = l
  l ==~ (CBool False) = nots l
  l ==~ r 
    | l == r = CBool True
    | otherwise = Equal l r

instance SOrd SBool SBool where
  l <=~ r = nots l ||~ r
  l <~ r = nots l &&~ r
  l >=~ r = l ||~ nots r
  l >~ r = l &&~ nots r
  symCompare l r =
    mrgIf (nots l &&~ r)
      (mrgReturn LT)
      (mrgIf (l ==~ r) (mrgReturn EQ) (mrgReturn GT))
instance PrimWrapper SBool Bool where
  conc = CBool
  concView (CBool x) = Just x
  concView _ = Nothing
  ssymb = SSBool
  isymb = ISBool

instance ITEOp SBool SBool where
  ites cond l r = ITE cond l r

instance LogicalOp SBool where
  CBool True ||~ _ = CBool True
  CBool False ||~ r = r
  _ ||~ CBool True = CBool True
  l ||~ CBool False = l
  l ||~ r = Or l r
  CBool False &&~ _ = CBool False
  CBool True &&~ r = r
  _ &&~ CBool False = CBool False
  l &&~ CBool True = l
  l &&~ r = And l r
  nots (CBool x) = CBool (not x)
  nots v = Not v
  
instance SymBoolOp SBool

data Symbol = SSymbol String | ISymbol Int String deriving (Generic, Show, Eq, Hashable)

instance ExtractSymbolics (S.HashSet Symbol) SBool where
  extractSymbolics = go S.empty
    where
      go s (CBool _) = s
      go s (SSBool sym) = S.insert (SSymbol sym) s
      go s (ISBool i sym) = S.insert (ISymbol i sym) s
      go s (Or l r) = go (go s l) r
      go s (And l r) = go (go s l) r
      go s (Not v) = go s v
      go s (Equal l r) = go (go s l) r
      go s (ITE c l r) = go (go (go s l) r) c
