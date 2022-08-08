{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.DeepSeq
import Control.Monad.Except
import Grisette
import IFCLInterpreter
import Indistinguishable
import Instructions
import Machine
import Utils.Timing

data EENIWitness = EENIWitness Program Program deriving (Show)

data VerifyEENI = VerifyEENI

instance ToAssertion VerifyEENI SymBool (Either VerificationConditions ()) where
  toAssertion _ (Left AssertionViolation) = conc True
  toAssertion _ _ = conc False

verifyEENI ::
  (GenSymSimple pspec Program) =>
  GrisetteSMTConfig n ->
  (Machine -> Program -> SymBool) ->
  (Machine -> Program -> Machine -> Program -> SymBool) ->
  Int ->
  pspec ->
  IO (Maybe EENIWitness)
verifyEENI config end indistinguishable steps progSpec =
  let p0 = genSymSimple progSpec "a"
      p1 = genSymSimple p0 "b"
      m0 = freshMachine 2
      m1 = freshMachine 2
      r0 = merge $ withExceptT (const AssumptionViolation) $ step steps m0 p0
      r1 = merge $ withExceptT (const AssumptionViolation) $ step steps m1 p1
      res = runExceptT $ do
        symFailIfNot AssumptionViolation (indistinguishable m0 p0 m1 p1)
        m0k <- r0
        m1k <- r1
        symFailIfNot AssumptionViolation (end m0k p0)
        symFailIfNot AssumptionViolation (end m1k p1)
        symFailIfNot AssertionViolation (indistinguishable m0k p0 m1k p1)
   in do
        _ <- timeItAll "evaluate1" $ runExceptT r0 `deepseq` return ()
        _ <- timeItAll "evaluate2" $ runExceptT r1 `deepseq` return ()
        m <- timeItAll "Lowering/Solving" $ solve VerifyEENI config res
        case m of
          Left _ -> do return Nothing
          Right mo -> return $ Just $ EENIWitness (evaluate True mo p0) (evaluate True mo p1)

runCexCase ::
  (GenSymSimple pspec Program) =>
  String ->
  GrisetteSMTConfig n ->
  (Machine -> Program -> SymBool) ->
  Int ->
  pspec ->
  IO EENIWitness
runCexCase nm config end steps progSpec = do
  putStrLn $ "Running " ++ nm
  r <- verifyEENI config end memIndistinguishable steps progSpec
  case r of
    Nothing -> error "Warning: failed to find the counter example"
    Just v -> print v >> return v

runValidCase ::
  (GenSymSimple pspec Program) =>
  String ->
  GrisetteSMTConfig n ->
  (Machine -> Program -> SymBool) ->
  Int ->
  pspec ->
  IO ()
runValidCase nm config end steps progSpec = do
  putStrLn $ "Running " ++ nm
  r <- verifyEENI config end memIndistinguishable steps progSpec
  case r of
    Nothing -> putStrLn "Verified"
    Just v -> error $ "Found cex: " ++ show v

main :: IO ()
main = timeItAll "Overall" $ do
  {-
    print (genSymSimple @SymBool NoopIns "a" :: Instruction)
    print (genSym @SymBool NoopIns "a" :: UUnionM Instruction)
    print (genSym @SymBool (ListSpec 0 2 [NoopIns, PushIns]) "a" :: UUnionM [UUnionM Instruction])

    print $ step 10 (freshMachine 2) [uHalt]
    print $ step 1 (freshMachine 2) [uPush $ PCValue 1 (conc False)]
    print $
      step
        2
        (freshMachine 2)
        [ uPush $ PCValue 1 (conc False),
          uPush $ PCValue 1 (conc True)
        ]
    print $
      step
        2
        (freshMachine 2)
        [ uPush $ PCValue 1 (conc False),
          uPush $ PCValue 0 (conc True)
        ]
    let p1 =
          [ uPush $ PCValue 1 (conc False),
            uPush $ PCValue 1 (conc True),
            uStore1AB
          ]
    let p2 =
          [ uPush $ PCValue 1 (conc False),
            uPush $ PCValue 0 (conc True),
            uStore1AB
          ]
    print $
      step
        3
        (freshMachine 2)
        p1
    print $
      step
        3
        (freshMachine 2)
        p2

    print $ do
      i <- step 3 (freshMachine 2) p1
      j <- step 3 (freshMachine 2) p2
      mrgReturn $ memIndistinguishable i p1 j p2

    let p3 =
          [ uPush $ PCValue 5 (conc False),
            uCall (PCValue 0 (conc False)) (PCValue 1 (conc False)),
            uPush $ PCValue 1 (conc False),
            uStoreCR,
            uHalt,
            uPush $ PCValue 2 (conc True),
            uReturn
          ]
    print $ step 3 (freshMachine 2) p3
    print $ step 3 (freshMachine 2) p3
    let p4 =
          [ uPush $ PCValue 5 (conc False),
            uCall (PCValue 0 (conc False)) (PCValue 1 (conc False)),
            uPush $ PCValue 1 (conc False),
            uStoreCR,
            uHalt,
            uPush $ PCValue 6 (conc True),
            uReturn
          ]
    print $ step 7 (freshMachine 2) p4

    let p5 =
          [ uPush $ PCValue 5 (conc False),
            uCall (PCValue 0 (conc False)) (PCValue 1 (conc False)),
            uPush $ PCValue 0 (conc False),
            uStoreCR,
            uHalt,
            uPush $ PCValue 0 (conc False),
            uPush $ PCValue 9 (conc True),
            uCall (PCValue 0 (conc False)) (PCValue 0 (conc False)),
            uPop,
            uPush $ PCValue 0 (conc False),
            uReturn
          ]
    print $ step 12 (freshMachine 2) p5
    let p6 =
          [ uPush $ PCValue 5 (conc False),
            uCall (PCValue 0 (conc False)) (PCValue 1 (conc False)),
            uPush $ PCValue 0 (conc False),
            uStoreCR,
            uHalt,
            uPush $ PCValue 0 (conc False),
            uPush $ PCValue 8 (conc True),
            uCall (PCValue 0 (conc False)) (PCValue 0 (conc False)),
            uPop,
            uPush $ PCValue 0 (conc False),
            uReturn
          ]
    print $ step 12 (freshMachine 2) p6
    let p7 =
          [ uPush $ PCValue 5 (conc True),
            uPush $ PCValue 7 (conc False),
            uCall (PCValue 1 (conc False)) (PCValue 0 (conc False)),
            uHalt,
            uPop,
            uPush $ PCValue 4 (conc False),
            uReturn,
            uCall (PCValue 0 (conc False)) (PCValue 1 (conc False)),
            uPush $ PCValue 1 (conc False),
            uStoreCR
          ]
    print $ step 10 (freshMachine 2) p7
    let p8 =
          [ uPush $ PCValue 4 (conc True),
            uPush $ PCValue 7 (conc False),
            uCall (PCValue 1 (conc False)) (PCValue 0 (conc False)),
            uHalt,
            uPop,
            uPush $ PCValue 4 (conc False),
            uReturn,
            uCall (PCValue 0 (conc False)) (PCValue 1 (conc False)),
            uPush $ PCValue 1 (conc False),
            uStoreCR
          ]
    print $ step 10 (freshMachine 2) p8
    -}

  let config = BoundedReasoning @5 boolector {verbose = False}

  _ <-
    runCexCase
      "Fig. 1"
      config
      isHalted
      3
      (SimpleListSpec 3 [HaltIns, NoopIns, PushIns, PopIns, Add1Ins, Load1Ins, Store1ABIns])
  _ <-
    runCexCase
      "Fig. 2"
      config
      isHalted
      3
      (SimpleListSpec 3 [HaltIns, NoopIns, PushIns, PopIns, Add1Ins, Load1Ins, Store1BIns])
  _ <-
    runCexCase
      "Fig. 3"
      config
      isHalted
      5
      (SimpleListSpec 5 [HaltIns, NoopIns, PushIns, PopIns, Add1Ins, Load1Ins, StoreIns])
  _ <-
    runCexCase
      "Fig. 2"
      config
      isHalted
      7
      (SimpleListSpec 7 [HaltIns, NoopIns, PushIns, PopIns, AddIns, Load1Ins, StoreIns])

  _ <-
    runValidCase
      "*"
      config
      isHalted
      7
      (SimpleListSpec 7 [HaltIns, NoopIns, PushIns, PopIns, AddIns, LoadIns, StoreIns])
  _ <-
    runValidCase
      "+"
      config
      isHalted
      8
      (SimpleListSpec 8 [HaltIns, NoopIns, PushIns, PopIns, AddIns, LoadIns, StoreIns])

  _ <-
    runCexCase
      "11"
      config
      isHalted
      6
      (SimpleListSpec 6 [HaltIns, NoopIns, PushIns, PopIns, AddIns, LoadIns, StoreIns, Jump1ABIns])
  _ <-
    runCexCase
      "12"
      config
      isHalted
      4
      (SimpleListSpec 4 [HaltIns, NoopIns, PushIns, PopIns, AddIns, LoadIns, StoreIns, Jump1BIns])

  _ <-
    runValidCase
      "**"
      config
      isHalted
      7
      (SimpleListSpec 7 [HaltIns, NoopIns, PushIns, PopIns, AddIns, LoadIns, StoreIns, JumpIns])
  _ <-
    runValidCase
      "++"
      config
      isHalted
      8
      (SimpleListSpec 8 [HaltIns, NoopIns, PushIns, PopIns, AddIns, LoadIns, StoreIns, JumpIns])

  _ <-
    runCexCase
      "Fig. 13"
      config
      isHaltedWithLow
      7
      (SimpleListSpec 7 [HaltIns, NoopIns, PushIns, PopIns, AddIns, LoadIns, StoreIns, Call1BIns, Return1ABIns])
  _ <-
    runCexCase
      "Fig. 15"
      config
      isHaltedWithLow
      8
      (SimpleListSpec 8 [HaltIns, NoopIns, PushIns, PopIns, AddIns, LoadIns, StoreCRIns, Call1BIns, Return1ABIns])
  _ <-
    runCexCase
      "Fig. 16"
      config
      isHaltedWithLow
      8
      (SimpleListSpec 8 [HaltIns, NoopIns, PushIns, PopIns, AddIns, LoadIns, StoreCRIns, Call1BIns, Return1BIns])
  _ <-
    runCexCase
      "Fig. 17"
      config
      isHaltedWithLow
      10
      (SimpleListSpec 10 [HaltIns, NoopIns, PushIns, PopIns, AddIns, LoadIns, StoreCRIns, CallIns, ReturnIns])
  _ <-
    runCexCase
      "Fig. 13*"
      config
      isHaltedWithLow
      7
      (Exact [PushIns, Call1BIns, HaltIns, PushIns, PushIns, StoreIns, Return1ABIns])
  _ <-
    runCexCase
      "Fig. 15*"
      config
      isHaltedWithLow
      8
      (Exact [PushIns, PushIns, Call1BIns, PushIns, StoreCRIns, HaltIns, PushIns, Return1ABIns])
  _ <-
    runCexCase
      "Fig. 16*"
      config
      isHaltedWithLow
      9
      (Exact [PushIns, PushIns, Call1BIns, PushIns, StoreCRIns, HaltIns, Return1BIns, PushIns, Return1BIns])
  _ <-
    runCexCase
      "Fig. 17*"
      config
      isHaltedWithLow
      13
      (Exact [PushIns, CallIns, PushIns, StoreCRIns, HaltIns, PushIns, PushIns, CallIns, PopIns, PushIns, ReturnIns])

  return ()

{-
r <-
  verifyEENI
    config
    isHaltedWithLow
    memIndistinguishable
    10
    10
    [NoopIns, PushIns, PopIns, HaltIns, AddIns, LoadIns, StoreCRIns, CallIns, ReturnIns]
print r
-}
