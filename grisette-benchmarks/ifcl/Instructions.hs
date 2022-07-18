{-# LANGUAGE TemplateHaskell #-}

module Instructions where

import Data.List.Unique
import Data.Proxy
import GHC.Generics
import Grisette
import Value

data Instruction
  = Halt
  | Noop
  | Push PCValue
  | Pop
  | Store
  | Load
  | Add
  | Add1
  | Load1
  | Store1AB
  | Store1B
  | Jump
  | Jump1AB
  | Jump1B
  | StoreCR
  | PopCR
  | Return
  | Call PCValue PCValue
  | Call1B PCValue
  | Return1B PCValue
  | Return1AB PCValue
  deriving (Show, Eq, Generic)
  deriving (SEq SymBool, Mergeable SymBool, Evaluate Model) via (Default Instruction)

$(makeUnionMWrapper "u" ''Instruction)

data InstructionSpec
  = HaltIns
  | NoopIns
  | PushIns
  | PopIns
  | StoreIns
  | LoadIns
  | AddIns
  | Add1Ins
  | Load1Ins
  | Store1ABIns
  | Store1BIns
  | JumpIns
  | Jump1ABIns
  | Jump1BIns
  | StoreCRIns
  | PopCRIns
  | ReturnIns
  | CallIns
  | Call1BIns
  | Return1BIns
  | Return1ABIns
  deriving (Show, Eq, Ord)

instance GenSym SymBool InstructionSpec Instruction

instance GenSymSimple SymBool InstructionSpec Instruction where
  genSymSimpleFresh _ HaltIns = return Halt
  genSymSimpleFresh _ NoopIns = return Noop
  genSymSimpleFresh proxy PushIns = Push <$> genSymSimpleFresh proxy ()
  genSymSimpleFresh _ PopIns = return Pop
  genSymSimpleFresh _ StoreIns = return Store
  genSymSimpleFresh _ LoadIns = return Load
  genSymSimpleFresh _ AddIns = return Add
  genSymSimpleFresh _ Add1Ins = return Add1
  genSymSimpleFresh _ Load1Ins = return Load1
  genSymSimpleFresh _ Store1ABIns = return Store1AB
  genSymSimpleFresh _ Store1BIns = return Store1B
  genSymSimpleFresh _ JumpIns = return Jump
  genSymSimpleFresh _ Jump1ABIns = return Jump1AB
  genSymSimpleFresh _ Jump1BIns = return Jump1B
  genSymSimpleFresh _ StoreCRIns = return StoreCR
  genSymSimpleFresh _ PopCRIns = return PopCR
  genSymSimpleFresh _ ReturnIns = return Return
  genSymSimpleFresh proxy CallIns =
    Call <$> genSymSimpleFresh proxy () <*> genSymSimpleFresh proxy ()
  genSymSimpleFresh proxy Call1BIns = Call1B <$> genSymSimpleFresh proxy ()
  genSymSimpleFresh proxy Return1BIns = Return1B <$> genSymSimpleFresh proxy ()
  genSymSimpleFresh proxy Return1ABIns = Return1AB <$> genSymSimpleFresh proxy ()

instance GenSym SymBool [InstructionSpec] Instruction where
  genSymFresh spec =
    let uniqSpec = sortUniq spec
     in do
          l <- traverse (genSymSimpleFresh (Proxy :: Proxy SymBool)) uniqSpec
          choose l

instance GenSym SymBool Instruction Instruction

instance GenSymSimple SymBool Instruction Instruction where
  genSymSimpleFresh = derivedSameShapeGenSymSimpleFresh
