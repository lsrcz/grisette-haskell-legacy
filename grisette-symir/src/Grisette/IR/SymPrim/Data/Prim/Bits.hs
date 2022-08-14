{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Grisette.IR.SymPrim.Data.Prim.Bits (
  pattern BitsConcTerm,
  AndBits(..),
  bitand,
  pattern AndBitsTerm,
  OrBits(..),
  bitor,
  pattern OrBitsTerm,
  XorBits(..),
  bitxor,
  pattern XorBitsTerm,
  ComplementBits(..),
  bitneg,
  pattern ComplementBitsTerm,
  ShiftBits(..),
  bitshift,
  pattern ShiftBitsTerm,
  RotateBits(..),
  bitrotate,
  pattern RotateBitsTerm,
) where

import Control.DeepSeq
import Data.Bits
import Data.Typeable
import Grisette.IR.SymPrim.Data.Prim.Helpers
import Grisette.IR.SymPrim.Data.Prim.PartialEval
import Grisette.IR.SymPrim.Data.Prim.Unfold
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.Term
import Language.Haskell.TH.Syntax
import Data.Hashable
import Language.Haskell.TH.Syntax.Compat
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.InternedCtors
import Grisette.IR.SymPrim.Data.Prim.InternedTerm.TermUtils

bitsConcTermView :: (Bits b, Typeable b) => Term a -> Maybe b
bitsConcTermView (ConcTerm _ b) = cast b
bitsConcTermView _ = Nothing

pattern BitsConcTerm :: forall b a. (Bits b, Typeable b) => b -> Term a
pattern BitsConcTerm b <- (bitsConcTermView -> Just b)

-- bitand
data AndBits x where
  AndBits :: (Bits x) => AndBits x

instance Eq (AndBits x) where
  _ == _ = True

instance Hashable (AndBits x) where
  s `hashWithSalt` _ = s `hashWithSalt` typeRep (Proxy @AndBits)

instance (Show (AndBits x)) where
  show AndBits = "AndBits"

instance Lift (AndBits x) where
  lift = unTypeSplice . liftTyped
  liftTyped AndBits = [||AndBits||]

instance NFData (AndBits x) where
  rnf AndBits = ()

bitand :: forall a. (Bits a, SupportedPrim a) => Term a -> Term a -> Term a
bitand = partialEvalBinary @(AndBits a) AndBits

instance (Bits a, SupportedPrim a) => BinaryCommPartialStrategy (AndBits a) a a where
  singleConstantHandler _ c k
    | c == zeroBits = Just $ concTerm zeroBits
    | c == complement zeroBits = Just k
  singleConstantHandler _ _ _ = Nothing

instance (Bits a, SupportedPrim a) => BinaryPartialStrategy (AndBits a) a a a where
  extractora _ = bitsConcTermView
  extractorb _ = bitsConcTermView
  allConstantHandler _ i j = Just $ concTerm $ i .&. j
  nonBinaryConstantHandler _ i j
    | i == j = Just i
  nonBinaryConstantHandler _ _ _ = Nothing

instance (Bits a, SupportedPrim a) => BinaryOp (AndBits a) a a a where
  partialEvalBinary tag l r = binaryUnfoldOnce (binaryPartial tag) (constructBinary tag) l r
  pformatBinary _ l r = "(bitand " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern AndBitsTerm :: forall a. (Bits a, Typeable a) => Term a -> Term a -> Term a
pattern AndBitsTerm l r <- BinaryTermPatt (AndBits :: AndBits a) l r

-- bitor
data OrBits x where
  OrBits :: (Bits x) => OrBits x

instance Eq (OrBits x) where
  _ == _ = True

instance Hashable (OrBits x) where
  s `hashWithSalt` _ = s `hashWithSalt` typeRep (Proxy @OrBits)

instance (Show (OrBits x)) where
  show OrBits = "OrBits"

instance Lift (OrBits x) where
  lift = unTypeSplice . liftTyped
  liftTyped OrBits = [||OrBits||]

instance NFData (OrBits x) where
  rnf OrBits = ()

bitor :: forall a. (Bits a, SupportedPrim a) => Term a -> Term a -> Term a
bitor = partialEvalBinary @(OrBits a) OrBits

instance (Bits a, SupportedPrim a) => BinaryCommPartialStrategy (OrBits a) a a where
  singleConstantHandler _ c k
    | c == zeroBits = Just k
    | c == complement zeroBits = Just $ concTerm $ complement zeroBits
  singleConstantHandler _ _ _ = Nothing

instance (Bits a, SupportedPrim a) => BinaryPartialStrategy (OrBits a) a a a where
  extractora _ = bitsConcTermView
  extractorb _ = bitsConcTermView
  allConstantHandler _ i j = Just $ concTerm $ i .|. j
  nonBinaryConstantHandler _ i j
    | i == j = Just i
  nonBinaryConstantHandler _ _ _ = Nothing

instance (Bits a, SupportedPrim a) => BinaryOp (OrBits a) a a a where
  partialEvalBinary tag l r = binaryUnfoldOnce (binaryPartial tag) (constructBinary tag) l r
  pformatBinary _ l r = "(bitor " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern OrBitsTerm :: forall a. (Bits a, Typeable a) => Term a -> Term a -> Term a
pattern OrBitsTerm l r <- BinaryTermPatt (OrBits :: OrBits a) l r

-- bitxor
data XorBits x where
  XorBits :: (Bits x) => XorBits x

instance Eq (XorBits x) where
  _ == _ = True

instance Hashable (XorBits x) where
  s `hashWithSalt` _ = s `hashWithSalt` typeRep (Proxy @XorBits)

instance (Show (XorBits x)) where
  show XorBits = "XorBits"

instance Lift (XorBits x) where
  liftTyped XorBits = [||XorBits||]

instance NFData (XorBits x) where
  rnf XorBits = ()

bitxor :: forall a. (Bits a, SupportedPrim a) => Term a -> Term a -> Term a
bitxor = partialEvalBinary @(XorBits a) XorBits

instance (Bits a, SupportedPrim a) => BinaryCommPartialStrategy (XorBits a) a a where
  singleConstantHandler _ c k
    | c == zeroBits = Just k
    | c == complement zeroBits = Just $ bitneg k
  singleConstantHandler _ _ _ = Nothing

instance (Bits a, SupportedPrim a) => BinaryPartialStrategy (XorBits a) a a a where
  extractora _ = bitsConcTermView
  extractorb _ = bitsConcTermView
  allConstantHandler _ i j = Just $ concTerm $ i `xor` j
  nonBinaryConstantHandler _ i j
    | i == j = Just $ concTerm zeroBits
  nonBinaryConstantHandler _ (ComplementBitsTerm i) (ComplementBitsTerm j) =
    Just $ bitxor i j
  nonBinaryConstantHandler _ (ComplementBitsTerm i) j =
    Just $ bitneg (bitxor i j)
  nonBinaryConstantHandler _ i (ComplementBitsTerm j) =
    Just $ bitneg (bitxor i j)
  nonBinaryConstantHandler _ _ _ = Nothing

instance (Bits a, SupportedPrim a) => BinaryOp (XorBits a) a a a where
  partialEvalBinary tag l r = binaryUnfoldOnce (binaryPartial tag) (constructBinary tag) l r
  pformatBinary _ l r = "(bitxor " ++ pformat l ++ " " ++ pformat r ++ ")"

pattern XorBitsTerm :: forall a. (Bits a, Typeable a) => Term a -> Term a -> Term a
pattern XorBitsTerm l r <- BinaryTermPatt (XorBits :: XorBits a) l r

-- complement
data ComplementBits x where
  ComplementBits :: (Bits x) => ComplementBits x

instance Eq (ComplementBits x) where
  _ == _ = True

instance Hashable (ComplementBits x) where
  s `hashWithSalt` _ = s `hashWithSalt` typeRep (Proxy @ComplementBits)

instance (Show (ComplementBits x)) where
  show ComplementBits = "ComplementBits"

instance Lift (ComplementBits x) where
  liftTyped ComplementBits = [||ComplementBits||]

instance NFData (ComplementBits x) where
  rnf ComplementBits = ()

bitneg :: forall a. (Bits a, SupportedPrim a) => Term a -> Term a
bitneg = partialEvalUnary @(ComplementBits a) ComplementBits

instance (Bits a, SupportedPrim a) => UnaryPartialStrategy (ComplementBits a) a a where
  extractor _ = bitsConcTermView
  constantHandler _ n = Just $ concTerm $ complement n 
  nonConstantHandler _ (ComplementBitsTerm x) = Just x
  nonConstantHandler _ _ = Nothing

instance (Bits a, SupportedPrim a) => UnaryOp (ComplementBits a) a a where
  partialEvalUnary s v = unaryUnfoldOnce (unaryPartial s) (constructUnary s) v
  pformatUnary _ v = "(bitneg " ++ pformat v ++ ")"

pattern ComplementBitsTerm :: forall a. (Bits a, Typeable a) => Term a -> Term a
pattern ComplementBitsTerm b <- UnaryTermPatt (ComplementBits :: ComplementBits a) b

-- shift
data ShiftBits x where
  ShiftBits :: (Bits x) => Int -> ShiftBits x

instance Eq (ShiftBits x) where
  (ShiftBits l) == (ShiftBits r) = l == r

instance Hashable (ShiftBits x) where
  s `hashWithSalt` (ShiftBits i) = s `hashWithSalt` i

instance (Show (ShiftBits x)) where
  show (ShiftBits n) = "Shift " ++ show n

instance Lift (ShiftBits x) where
  liftTyped (ShiftBits n) = [||ShiftBits n||]

instance NFData (ShiftBits x) where
  rnf (ShiftBits x) = x `seq` ()

bitshift :: forall a. (Bits a, SupportedPrim a) => Term a -> Int -> Term a
bitshift l n = partialEvalUnary @(ShiftBits a) (ShiftBits n) l

instance (Bits a, SupportedPrim a) => UnaryPartialStrategy (ShiftBits a) a a where
  extractor _ = bitsConcTermView
  constantHandler (ShiftBits i) n = Just $ concTerm $ n `shift` i
  nonConstantHandler (ShiftBits 0) x = Just x
  nonConstantHandler (ShiftBits a) _
    | case bitSizeMaybe (zeroBits :: a) of
        Nothing -> False
        Just s -> a >= s =
      Just $ concTerm zeroBits
  nonConstantHandler (ShiftBits i) (ShiftBitsTerm (b1 :: Term a) j)
    | (i >= 0 && j >= 0) || (i <= 0 && j <= 0) = Just $ bitshift b1 (i + j)
  nonConstantHandler _ _ = Nothing

instance (Bits a, SupportedPrim a) => UnaryOp (ShiftBits a) a a where
  partialEvalUnary s v = unaryUnfoldOnce (unaryPartial s) (constructUnary s) v
  pformatUnary (ShiftBits i) v = "(shift " ++ show i ++ " " ++ pformat v ++ ")"

pattern ShiftBitsTerm :: forall a. (Bits a, Typeable a) => Term a -> Int -> Term a
pattern ShiftBitsTerm b i <- UnaryTermPatt (ShiftBits i :: ShiftBits a) b

-- rotate
data RotateBits x where
  RotateBits :: (Bits x) => Int -> RotateBits x

instance Eq (RotateBits x) where
  (RotateBits l) == (RotateBits r) = l == r

instance Hashable (RotateBits x) where
  s `hashWithSalt` (RotateBits i) = s `hashWithSalt` i

instance (Show (RotateBits x)) where
  show (RotateBits n) = "Rotate " ++ show n

instance Lift (RotateBits x) where
  liftTyped (RotateBits n) = [||RotateBits n||]

instance NFData (RotateBits x) where
  rnf (RotateBits x) = x `seq` ()

bitrotate :: forall a. (Bits a, SupportedPrim a) => Term a -> Int -> Term a
bitrotate l n = partialEvalUnary @(RotateBits a) (RotateBits n) l

instance (Bits a, SupportedPrim a) => UnaryPartialStrategy (RotateBits a) a a where
  extractor _ = bitsConcTermView
  constantHandler (RotateBits i) n = Just $ concTerm $ n `rotate` i
  nonConstantHandler (RotateBits 0) x = Just x
  nonConstantHandler (RotateBits a) x
    | case bsize of
        Nothing -> False
        Just s -> s /= 0 && (a >= s || a < 0) = do
          cbsize <- bsize
          if a >= cbsize then
            return $ bitrotate x (a - cbsize)
          else
            return $ bitrotate x (a + cbsize)
    where
      bsize = bitSizeMaybe (zeroBits :: a)
  nonConstantHandler (RotateBits i) (RotateBitsTerm (b1 :: Term a) j) =
    Just $ bitrotate b1 (i + j)
  nonConstantHandler _ _ = Nothing

instance (Bits a, SupportedPrim a) => UnaryOp (RotateBits a) a a where
  partialEvalUnary s v = unaryUnfoldOnce (unaryPartial s) (constructUnary s) v
  pformatUnary (RotateBits i) v = "(rotate " ++ show i ++ " " ++ pformat v ++ ")"

pattern RotateBitsTerm :: forall a. (Bits a, Typeable a) => Term a -> Int -> Term a
pattern RotateBitsTerm b i <- UnaryTermPatt (RotateBits i :: RotateBits a) b
