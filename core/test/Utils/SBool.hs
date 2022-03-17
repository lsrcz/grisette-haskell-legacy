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
import Grisette.Data.Class.SymEval
import qualified Data.HashMap.Strict as M

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

instance SymEval (M.HashMap Symbol Bool) SBool where
  symeval _ _ c@(CBool _) = c
  symeval fillDefault model s@(SSBool sym) = case M.lookup (SSymbol sym) model of
    Just v -> CBool v
    Nothing -> if fillDefault then (CBool False) else s
  symeval fillDefault model s@(ISBool i sym) = case M.lookup (ISymbol i sym) model of
    Just v -> CBool v
    Nothing -> if fillDefault then (CBool False) else s
  symeval fillDefault model (Or l r) = symeval fillDefault model l ||~ symeval fillDefault model r
  symeval fillDefault model (And l r) = symeval fillDefault model l &&~ symeval fillDefault model r
  symeval fillDefault model (Not v) = nots (symeval fillDefault model v)
  symeval fillDefault model (Equal l r) = symeval fillDefault model l ==~ symeval fillDefault model r
  symeval fillDefault model (ITE c l r) = ites (symeval fillDefault model c)
    (symeval fillDefault model l) (symeval fillDefault model r)

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
  ites (CBool True) l _ = l
  ites (CBool False) _ r = r
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
