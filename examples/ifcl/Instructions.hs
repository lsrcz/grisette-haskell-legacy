{-# LANGUAGE TemplateHaskell #-}

module Instructions where

import Data.List (sort)
import Data.List.Unique
import GHC.Generics
import Grisette.Core
import Grisette.SymPrim.Term
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
  deriving (Show, Eq, Generic, Mergeable SymBool, SEq SymBool, SymEval Model)

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

instance SymGen SymBool InstructionSpec Instruction

instance SymGenSimple SymBool InstructionSpec Instruction where
  genSymSimpleIndexed HaltIns = return Halt
  genSymSimpleIndexed NoopIns = return Noop
  genSymSimpleIndexed PushIns = Push <$> genSymSimpleIndexed @SymBool ()
  genSymSimpleIndexed PopIns = return Pop
  genSymSimpleIndexed StoreIns = return Store
  genSymSimpleIndexed LoadIns = return Load
  genSymSimpleIndexed AddIns = return Add
  genSymSimpleIndexed Add1Ins = return Add1
  genSymSimpleIndexed Load1Ins = return Load1
  genSymSimpleIndexed Store1ABIns = return Store1AB
  genSymSimpleIndexed Store1BIns = return Store1B
  genSymSimpleIndexed JumpIns = return Jump
  genSymSimpleIndexed Jump1ABIns = return Jump1AB
  genSymSimpleIndexed Jump1BIns = return Jump1B
  genSymSimpleIndexed StoreCRIns = return StoreCR
  genSymSimpleIndexed PopCRIns = return PopCR
  genSymSimpleIndexed ReturnIns = return Return
  genSymSimpleIndexed CallIns =
    Call <$> genSymSimpleIndexed @SymBool () <*> genSymSimpleIndexed @SymBool ()
  genSymSimpleIndexed Call1BIns = Call1B <$> genSymSimpleIndexed @SymBool ()
  genSymSimpleIndexed Return1BIns = Return1B <$> genSymSimpleIndexed @SymBool ()
  genSymSimpleIndexed Return1ABIns = Return1AB <$> genSymSimpleIndexed @SymBool ()

instance SymGen SymBool [InstructionSpec] Instruction where
  genSymIndexed spec =
    let uniqSpec = uniq $ sort spec
     in do
          l <- traverse (genSymSimpleIndexed @SymBool) uniqSpec
          choose (head l) (tail l)

instance SymGen SymBool Instruction Instruction

instance SymGenSimple SymBool Instruction Instruction where
  genSymSimpleIndexed i = genSymIndexedWithDerivedSameShape @SymBool i
