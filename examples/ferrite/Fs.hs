module Fs where
import Lang
import Grisette.SymPrim.Term
import Grisette.Core

class (ToSym conc symb, ToCon symb conc, SymEval Model symb) => FileSystem conc symb | conc -> symb, symb -> conc where
  crack :: conc -> [SysCall] -> [UnionM InodeOp]
  execute :: symb -> InodeOp -> UnionM symb
  ondisk :: symb -> Name -> UnionM (Maybe [SymBool])
  -- conc is ignored here
  reorder :: conc -> InodeOp -> InodeOp -> Bool
