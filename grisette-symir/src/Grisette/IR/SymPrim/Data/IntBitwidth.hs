{-# LANGUAGE TemplateHaskell #-}

module Grisette.IR.SymPrim.Data.IntBitwidth where
import Language.Haskell.TH
import Data.Bits (FiniteBits(finiteBitSize))

intBitwidthQ :: TypeQ
intBitwidthQ = return $ LitT (NumTyLit $ toInteger $ finiteBitSize (undefined :: Int))
