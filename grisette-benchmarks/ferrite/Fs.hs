module Fs where

import Grisette
import Lang

class (ToSym conc symb, ToCon symb conc, Evaluate Model symb) => FileSystem conc symb | conc -> symb, symb -> conc where
  crack :: conc -> [SysCall] -> [UnionM InodeOp]
  execute :: symb -> InodeOp -> UnionM symb
  ondisk :: symb -> Name -> UnionM (Maybe [SymBool])

  -- conc is ignored here
  reorder :: conc -> InodeOp -> InodeOp -> Bool
