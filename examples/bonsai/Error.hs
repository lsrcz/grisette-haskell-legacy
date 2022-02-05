module Error where
import GHC.Generics
import Grisette.Core
import Grisette.SymPrim.Term
import Grisette.Backend.SBV
import Control.DeepSeq

data BonsaiError
  = BonsaiTypeError
  | BonsaiExecError
  | BonsaiRecursionError
  deriving (Show, Eq, Generic, Mergeable SymBool, ToCon BonsaiError, NFData)

instance TransformError BonsaiError BonsaiError where
  transformError = id

data VerifyTyper a = VerifyTyper
instance SolverTranslation (VerifyTyper a) BonsaiError a where
  errorTranslation _ BonsaiExecError = True
  errorTranslation _ _ = False
  valueTranslation _ _ = conc False
