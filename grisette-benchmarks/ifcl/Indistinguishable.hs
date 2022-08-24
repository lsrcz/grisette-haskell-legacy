module Indistinguishable where

import Grisette
import Instructions
import Machine
import Value

indistinguishablePCValue :: PCValue -> PCValue -> SymBool
indistinguishablePCValue (PCValue lint llabel) (PCValue rint rlabel) =
  llabel ==~ rlabel &&~ (llabel ||~ lint ==~ rint)

indistinguishableMemValue :: MemValue -> MemValue -> SymBool
indistinguishableMemValue (MPCValue l) (MPCValue r) = indistinguishablePCValue l r
indistinguishableMemValue (ReturnAddr lpc _) (ReturnAddr rpc _) = indistinguishablePCValue lpc rpc
indistinguishableMemValue _ _ = conc False

indistinguishableInstruction :: Instruction -> Instruction -> SymBool
indistinguishableInstruction l r =
  l
    ==~ r
    ||~ ( case (l, r) of
            (Push v1, Push v2) -> indistinguishablePCValue v1 v2
            _ -> conc False
        )

indistinguishableList :: (a -> a -> SymBool) -> [UnionM a] -> [UnionM a] -> SymBool
indistinguishableList f l1 l2 =
  conc (length l1 == length l2)
    &&~ foldr (&&~) (conc True) (zipWith (\l r -> f #~ l #~ r) l1 l2)

indistinguishableProgram :: Program -> Program -> SymBool
indistinguishableProgram = indistinguishableList indistinguishableInstruction

indistinguishableMemValueList :: [UnionM MemValue] -> [UnionM MemValue] -> SymBool
indistinguishableMemValueList = indistinguishableList indistinguishableMemValue

indistinguishablePCValueList :: [UnionM PCValue] -> [UnionM PCValue] -> SymBool
indistinguishablePCValueList = indistinguishableList indistinguishablePCValue

memIndistinguishable :: Machine -> Program -> Machine -> Program -> SymBool
memIndistinguishable (Machine (PCValue _ l0) _ mem0) p0 (Machine (PCValue _ l1) _ mem1) p1 =
  l0 ==~ l1 &&~ (l0 ||~ ((indistinguishablePCValueList #~ mem0 #~ mem1) &&~ indistinguishableProgram p0 p1))
