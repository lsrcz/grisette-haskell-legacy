{-# LANGUAGE TemplateHaskell #-}

module Instructions where

import Data.List.Extra
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

instance GenSymSimple InstructionSpec Instruction where
  genSymSimpleFresh HaltIns = return Halt
  genSymSimpleFresh NoopIns = return Noop
  genSymSimpleFresh PushIns = Push <$> genSymSimpleFresh ()
  genSymSimpleFresh PopIns = return Pop
  genSymSimpleFresh StoreIns = return Store
  genSymSimpleFresh LoadIns = return Load
  genSymSimpleFresh AddIns = return Add
  genSymSimpleFresh Add1Ins = return Add1
  genSymSimpleFresh Load1Ins = return Load1
  genSymSimpleFresh Store1ABIns = return Store1AB
  genSymSimpleFresh Store1BIns = return Store1B
  genSymSimpleFresh JumpIns = return Jump
  genSymSimpleFresh Jump1ABIns = return Jump1AB
  genSymSimpleFresh Jump1BIns = return Jump1B
  genSymSimpleFresh StoreCRIns = return StoreCR
  genSymSimpleFresh PopCRIns = return PopCR
  genSymSimpleFresh ReturnIns = return Return
  genSymSimpleFresh CallIns =
    Call <$> genSymSimpleFresh () <*> genSymSimpleFresh ()
  genSymSimpleFresh Call1BIns = Call1B <$> genSymSimpleFresh ()
  genSymSimpleFresh Return1BIns = Return1B <$> genSymSimpleFresh ()
  genSymSimpleFresh Return1ABIns = Return1AB <$> genSymSimpleFresh ()

sortUniq :: Ord a => [a] -> [a]
sortUniq = sort . nubOrd

instance GenSym SymBool [InstructionSpec] Instruction where
  genSymFresh spec =
    let uniqSpec = sortUniq spec
     in do
          l <- traverse genSymSimpleFresh uniqSpec
          choose l

instance GenSym SymBool Instruction Instruction

instance GenSymSimple Instruction Instruction where
  genSymSimpleFresh = derivedSameShapeGenSymSimpleFresh
