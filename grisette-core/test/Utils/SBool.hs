{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Utils.SBool where
import Grisette.Data.Class.Bool
import Grisette.Data.Class.PrimWrapper
import qualified Data.HashSet as S
import Grisette.Data.Class.ExtractSymbolics
import Data.Hashable
import Grisette.Data.Class.SOrd
import Grisette.Data.Class.SimpleMergeable
import Grisette.Data.Class.Mergeable
import Grisette.Control.Monad
import Grisette.Data.Class.Evaluate
import qualified Data.HashMap.Strict as M
import Grisette.Data.Class.ToCon
import Grisette.Data.Class.ToSym
import Grisette.Data.Class.GenSym
import Control.Monad.State
import Control.Monad.Reader
import Data.Typeable

data SBool where
  CBool :: Bool -> SBool
  SSBool :: String -> SBool
  ISSBool :: (Typeable a, Show a, Eq a, Hashable a) => String -> a -> SBool
  ISBool :: Int -> String -> SBool
  IISBool :: (Typeable a, Show a, Eq a, Hashable a) => Int -> String -> a -> SBool
  Or :: SBool -> SBool -> SBool
  And :: SBool -> SBool -> SBool
  Not :: SBool -> SBool
  Equal :: SBool -> SBool -> SBool
  ITE :: SBool -> SBool -> SBool -> SBool

instance Show SBool where
  show (CBool v) = "CBool " ++ show v
  show (SSBool s) = "SSBool " ++ s
  show (ISSBool s info) = "ISSBool " ++ s ++ " " ++ show info
  show (ISBool i s) = "ISBool " ++ show i ++ " " ++ s
  show (IISBool i s info) = "IISBool " ++ show i ++ " " ++ show s ++ " " ++ show info
  show (Or l r) = "Or (" ++ show l ++ ") (" ++ show r ++ ")"
  show (And l r) = "And (" ++ show l ++ ") (" ++ show r ++ ")"
  show (Not v) = "Not (" ++ show v ++ ")"
  show (Equal l r) = "Equal (" ++ show l ++ ") (" ++ show r ++ ")"
  show (ITE c l r) = "ITE (" ++ show c ++ ") (" ++ show l ++ ") (" ++ show r ++ ")"

instance Eq SBool where
  CBool l == CBool r = l == r
  SSBool l == SSBool r = l == r
  ISSBool s1 (info1 :: a) == ISSBool s2 (info2 :: b) = case eqT @a @b of
    Just Refl -> s1 == s2 && info1 == info2
    Nothing -> False
  ISBool i1 s1 == ISBool i2 s2 = i1 == i2 && s1 == s2
  IISBool i1 s1 (info1 :: a) == IISBool i2 s2 (info2 :: b) = case eqT @a @b of
    Just Refl -> i1 == i2 && s1 == s2 && info1 == info2
    Nothing -> False
  Or l1 r1 == Or l2 r2 = l1 == l2 && r1 == r2
  And l1 r1 == And l2 r2 = l1 == l2 && r1 == r2
  Not v1 == Not v2 = v1 == v2
  Equal l1 r1 == Equal l2 r2 = l1 == l2 && r1 == r2
  ITE c1 l1 r1 == ITE c2 l2 r2 = c1 == c2 && l1 == l2 && r1 == r2
  _ == _ = False
  
instance Mergeable SBool SBool where
  mergeStrategy = SimpleStrategy ites

instance SimpleMergeable SBool SBool where
  mrgIte = ites

instance Evaluate (M.HashMap Symbol Bool) SBool where
  evaluate _ _ c@(CBool _) = c
  evaluate fillDefault model s@(SSBool sym) = case M.lookup (SSymbol sym) model of
    Just v -> CBool v
    Nothing -> if fillDefault then (CBool False) else s
  evaluate fillDefault model s@(ISSBool sym info) = case M.lookup (ISSymbol sym info) model of
    Just v -> CBool v
    Nothing -> if fillDefault then (CBool False) else s
  evaluate fillDefault model s@(ISBool i sym) = case M.lookup (ISymbol i sym) model of
    Just v -> CBool v
    Nothing -> if fillDefault then (CBool False) else s
  evaluate fillDefault model s@(IISBool i sym info) = case M.lookup (IISymbol i sym info) model of
    Just v -> CBool v
    Nothing -> if fillDefault then (CBool False) else s
  evaluate fillDefault model (Or l r) = evaluate fillDefault model l ||~ evaluate fillDefault model r
  evaluate fillDefault model (And l r) = evaluate fillDefault model l &&~ evaluate fillDefault model r
  evaluate fillDefault model (Not v) = nots (evaluate fillDefault model v)
  evaluate fillDefault model (Equal l r) = evaluate fillDefault model l ==~ evaluate fillDefault model r
  evaluate fillDefault model (ITE c l r) = ites (evaluate fillDefault model c)
    (evaluate fillDefault model l) (evaluate fillDefault model r)

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
  sinfosymb = ISSBool
  isymb = ISBool
  iinfosymb = IISBool

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

data Symbol where
  SSymbol :: String -> Symbol
  ISSymbol :: (Typeable a, Show a, Eq a, Hashable a) => String -> a -> Symbol
  ISymbol :: Int -> String -> Symbol
  IISymbol :: (Typeable a, Show a, Eq a, Hashable a) => Int -> String -> a -> Symbol
  -- deriving (Generic, Show, Eq, Hashable)

instance Show Symbol where
  show (SSymbol s) = "SSymbol " ++ s
  show (ISSymbol s info) = "ISSymbol " ++ s ++ " " ++ show info
  show (ISymbol i s) = "ISymbol " ++ show i ++ " " ++ s
  show (IISymbol i s info) = "IISymbol " ++ show i ++ " " ++ s ++ " " ++ show info

instance Eq Symbol where
  SSymbol s1 == SSymbol s2 = s1 == s2
  ISSymbol s1 (info1 :: info1) == ISSymbol s2 (info2 :: info2) = 
    case eqT @info1 @info2 of
      Just Refl -> s1 == s2 && info1 == info2
      _ -> False
  ISymbol i1 s1 == ISymbol i2 s2 = i1 == i2 && s1 == s2
  IISymbol i1 s1 (info1 :: info1) == IISymbol i2 s2 (info2 :: info2) =
    case eqT @info1 @info2 of
      Just Refl -> i1 == i2 && s1 == s2 && info1 == info2
      _ -> False
  _ == _ = False

instance Hashable Symbol where
  s `hashWithSalt` SSymbol s1 = s `hashWithSalt` s1
  s `hashWithSalt` ISSymbol s1 info = s `hashWithSalt` s1 `hashWithSalt` info
  s `hashWithSalt` ISymbol i1 s1 = s `hashWithSalt` i1 `hashWithSalt` s1
  s `hashWithSalt` IISymbol i1 s1 info1 = s `hashWithSalt` i1 `hashWithSalt` s1 `hashWithSalt` info1

instance ExtractSymbolics (S.HashSet Symbol) SBool where
  extractSymbolics = go S.empty
    where
      go s (CBool _) = s
      go s (SSBool sym) = S.insert (SSymbol sym) s
      go s (ISSBool sym info) = S.insert (ISSymbol sym info) s
      go s (ISBool i sym) = S.insert (ISymbol i sym) s
      go s (IISBool i sym info) = S.insert (IISymbol i sym info) s
      go s (Or l r) = go (go s l) r
      go s (And l r) = go (go s l) r
      go s (Not v) = go s v
      go s (Equal l r) = go (go s l) r
      go s (ITE c l r) = go (go (go s l) r) c

instance ToCon SBool Bool where
  toCon (CBool v) = Just v
  toCon _ = Nothing

instance ToCon SBool SBool where
  toCon = Just

instance ToSym Bool SBool where
  toSym = CBool

instance ToSym SBool SBool where
  toSym = id

instance GenSym SBool () SBool where

instance GenSymSimple SBool () SBool where
  genSymSimpleFresh _ = do
    ident <- ask
    idx@(GenSymIndex i) <- get
    put $ idx + 1
    case ident of
      GenSymIdent s -> return $ ISBool i s
      GenSymIdentWithInfo s info -> return $ IISBool i s info

instance GenSym SBool SBool SBool where

instance GenSymSimple SBool SBool SBool where
  genSymSimpleFresh _ = genSymSimpleFresh @SBool ()

