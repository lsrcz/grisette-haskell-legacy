{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Core
  ( ConProgram (..),
    Program (..),
    ConAST (..),
    AST (..),
    uArg,
    uUnary,
    uBinary,
    uNoMrg,
    uConst,
    CombASTSpec (..),
    CombASTSpec0 (..),
    CombProgramSpec (..),
    ExtProgramSpec (..),
    UnaryFuncMap,
    BinaryFuncMap,
    interpretSketch,
    synth,
    synth1,
  )
where

import Control.Monad.Reader
import Control.Monad.Trans.Except
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.Char
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Hashable
import Data.List hiding (inits)
import GHC.Generics
import Grisette
import Data.Maybe

data ConProgram val = ConProgram
  { cinits :: [val],
    cupdates :: [ConAST val],
    cterminate :: ConAST val,
    cinputNum :: Int
  }
  deriving (Generic)

instance Show val => Show (ConProgram val) where
  show (ConProgram i u t a) =
    unlines $
      [ "def f("
          ++ intercalate
            ", "
            ((\x -> let nm = chr $ ord 'a' + x in nm : " = [" ++ [nm] ++ "1, ..., " ++ [nm] ++ "n]") <$> [0 .. a -1])
          ++ "):"
      ]
        ++ fmap (\(n, _) -> "  p" ++ show n ++ " = array()") (zip [1 :: Int ..] i)
        ++ fmap (\(n, v) -> "  p" ++ show n ++ "[0] = " ++ show v) (zip [1 :: Int ..] i)
        ++ ["  for i from 1 to n:"]
        ++ fmap (\(n, v) -> "    p" ++ show n ++ "[i] = " ++ formatConAST a "i - 1" v) (zip [1 :: Int ..] u)
        ++ ["  return " ++ formatConAST 0 "n" t]

data Program val = Program
  { inits :: [UnionM val],
    updates :: [UnionM (AST val)],
    terminate :: UnionM (AST val),
    inputNum :: Int
  }
  deriving (Show, Generic)

deriving via
  (Default (AST val))
  instance
    SEq SymBool val => SEq SymBool (AST val)

deriving via
  (Default (Program val))
  instance
    SEq SymBool val => SEq SymBool (Program val)

deriving via
  (Default (ConProgram cval))
  instance
    ToCon sval cval => ToCon (Program sval) (ConProgram cval)

deriving via
  (Default (Program sval))
  instance
    (Mergeable SymBool sval, ToSym cval sval) => ToSym (ConProgram cval) (Program sval)

deriving via
  (Default (Program val))
  instance
    Mergeable SymBool val => Mergeable SymBool (Program val)

deriving via
  (Default (Program val))
  instance
    (Mergeable SymBool val, Evaluate Model val) => Evaluate Model (Program val)

data ConAST val
  = ConArg Int
  | ConConst val
  | ConUnary B.ByteString (ConAST val)
  | ConBinary B.ByteString (ConAST val) (ConAST val)
  | ConNoMrg (ConAST val)
  deriving (Generic)

formatConAST :: (Show val) => Int -> String -> ConAST val -> String
formatConAST n idx (ConArg v)
  | v < n = chr (ord 'a' + v) : "[i]"
  | otherwise = 'p' : show (v - n + 1) ++ "[" ++ idx ++ "]"
formatConAST _ _ (ConConst v) = show v
formatConAST n idx (ConUnary f sub)
  | isAlpha (C.head f) = C.unpack f ++ "(" ++ formatConAST n idx sub ++ ")"
  | otherwise = "(" ++ C.unpack f ++ " " ++ formatConAST n idx sub ++ ")"
formatConAST n idx (ConBinary f l r)
  | isAlpha (C.head f) = C.unpack f ++ "(" ++ formatConAST n idx l ++ ", " ++ formatConAST n idx r ++ ")"
  | otherwise = "(" ++ formatConAST n idx l ++ " " ++ C.unpack f ++ " " ++ formatConAST n idx r ++ ")"
formatConAST n idx (ConNoMrg v) = formatConAST n idx v

deriving via
  (Default (ConAST cval))
  instance
    ToCon sval cval => ToCon (AST sval) (ConAST cval)

data AST val
  = Arg (UnionM Int)
  | Const (UnionM val)
  | Unary (UnionM B.ByteString) (UnionM (AST val))
  | Binary (UnionM B.ByteString) (UnionM (AST val)) (UnionM (AST val))
  | NoMrg (UnionM (AST val))
  deriving (Show, Generic, Eq, Hashable)

instance Mergeable SymBool val => Mergeable SymBool (AST val) where
  mergingStrategy = SortedStrategy (\case
    Arg {} -> 0 :: Int
    Const {} -> 1
    Unary {} -> 2
    Binary {} -> 3
    NoMrg {} -> 4
    ) (\case
      0 -> SimpleStrategy $ \cond (Arg l) (Arg r) -> Arg $ mrgIf cond l r
      1 -> SimpleStrategy $ \cond (Const l) (Const r) -> Const $ mrgIf cond l r
      2 -> SimpleStrategy $ \cond (Unary lf l) (Unary rf r) ->
        Unary (mrgIf cond lf rf) (mrgIf cond l r)
      3 -> SimpleStrategy $ \cond (Binary lf ll lr) (Binary rf rl rr) ->
        Binary (mrgIf cond lf rf) (mrgIf cond ll rl) (mrgIf cond lr rr)
      4 -> NoStrategy
      _ -> undefined
    )

deriving via
  (Default (AST val))
  instance
    (Evaluate Model val, Mergeable SymBool val) => Evaluate Model (AST val)

deriving via
  (Default (AST sval))
  instance
    (ToSym cval sval, Mergeable SymBool sval) => ToSym (ConAST cval) (AST sval)

type UnaryFuncMap val = M.HashMap B.ByteString (val -> ExceptT VerificationConditions UnionM val)

type BinaryFuncMap val = M.HashMap B.ByteString (val -> val -> ExceptT VerificationConditions UnionM val)

data CombASTSpec0 sval = CombASTSpec0
  { unaryDepth :: Int,
    binaryDepth :: Int,
    unaries :: [B.ByteString],
    binaries :: [B.ByteString]
  }

data CombASTSpec sval = CombASTSpec
  { combSpec0 :: CombASTSpec0 sval,
    combArgs :: [Int]
  }

$(makeUnionMWrapper "u" ''AST)

instance Mergeable SymBool sval => GenSym SymBool (CombASTSpec sval) (AST sval) where
  genSymFresh ::
    forall m u.
    ( MonadGenSymFresh m,
      MonadUnion SymBool u
    ) =>
    CombASTSpec sval ->
    m (u (AST sval))
  genSymFresh (CombASTSpec spec args) = liftToMonadUnion <$> go (unaryDepth spec) (binaryDepth spec)
    where
      currUnaries = unaries spec
      currBinaries = binaries spec
      {-currSlots = slotsASTSpec spec
      currInputNum = inputNumASTSpec spec-}
      argGen :: m (UnionM (AST sval))
      argGen = mrgFmap Arg . mrgReturn <$> choose args -- [0 .. currSlots + currInputNum - 1]
      uGen :: Int -> m (UnionM (AST sval))
      uGen u
        | u <= 0 = argGen
        | otherwise = do
          uf <- choose currUnaries
          l <- uGen (u - 1)
          return $ uUnary uf l
      sp n = [(n - x, x) | x <- [0 .. n `div` 2]]
      go :: Int -> Int -> m (UnionM (AST sval))
      go u b
        | b <= 0 = uGen u
        | b == 1 = do
          bf <- choose currBinaries
          l <- uGen u
          r <- uGen u
          return $ uBinary bf l r
        {-  
        | b == 3 = do
          ll1 <- uGen u
          ll2l <- uGen u
          bfll2 <- choose currBinaries
          ll <- chooseU [ll1, uBinary bfll2 ll1 ll2l]
          lr <- uGen u
          bfl <- choose currBinaries
          let l = uBinary bfl ll lr

          r1 <- uGen u
          r2r <- uGen u
          bfr2 <- choose currBinaries
          r <- chooseU [r1, uBinary bfr2 r1 r2r]
          bf <- choose currBinaries
          return $ uBinary bf l r-}

        {-
        v1 <- uGen u
        v2 <- uGen u
        l2 <- go u 1
        bfl1 <- choose currBinaries
        let l1 = Binary bfl1 l2 v1

        bfr2 <- choose currBinaries
        let r2 = Binary bfr2 v1 v2

        bft <- choose currBinaries
        l <- chooseU [mrgReturn l1, l2]
        r <- chooseU [v2, mrgReturn r2]
        return $ uBinary bft l r
        -}
        | otherwise = do
          x <- traverse (uncurry $ golr u) $ sp (b - 1)
          chooseU x
      golr u b1 b2 = do
        bf <- choose currBinaries
        l <- go u b1
        r <- go u b2
        return $ uBinary bf l r

data CombProgramSpec cval sval = CombProgramSpec
  { initsSpec :: [cval],
    updatesSpec :: CombASTSpec0 sval,
    terminateSpec :: CombASTSpec0 sval,
    slots :: Int,
    inputNumSpec :: Int
  }

instance (ToSym cval sval, Mergeable SymBool sval) => GenSym SymBool (CombProgramSpec cval sval) (Program sval)

instance (ToSym cval sval, Mergeable SymBool sval) => GenSymSimple (CombProgramSpec cval sval) (Program sval) where
  genSymSimpleFresh ::
    forall m.
    ( MonadGenSymFresh m
    ) =>
    CombProgramSpec cval sval ->
    m (Program sval)
  genSymSimpleFresh spec = do
    i <- initsGen
    u <- updatesGen
    t <- terminateGen
    return $ Program i u t (inputNumSpec spec)
    where
      initGen :: m (UnionM sval)
      initGen = choose $ toSym <$> initsSpec spec
      updateGen :: m (UnionM (AST sval))
      updateGen = genSymFresh (CombASTSpec (updatesSpec spec) [0..slots spec + inputNumSpec spec - 1])
      terminateGen :: m (UnionM (AST sval))
      terminateGen = genSymFresh (CombASTSpec (terminateSpec spec) [0..slots spec - 1])
      initsGen :: m [UnionM sval]
      initsGen = traverse (const initGen) [1 .. slots spec]
      updatesGen :: m [UnionM (AST sval)]
      updatesGen = traverse (const updateGen) [1 .. slots spec]

data ExtProgramSpec cval sval = ExtProgramSpec
  { extInitsSpec :: [cval],
    extsSpec :: CombASTSpec0 sval,
    extsOpt :: B.ByteString,
    extsSlots :: Int,
    extsInputNum :: Int
    }

instance (ToSym cval sval, Mergeable SymBool sval) => GenSym SymBool (ExtProgramSpec cval sval) (Program sval)
instance (ToSym cval sval, Mergeable SymBool sval) => GenSymSimple (ExtProgramSpec cval sval) (Program sval) where
  genSymSimpleFresh ::
    forall m.
    ( MonadGenSymFresh m
    ) =>
    ExtProgramSpec cval sval ->
    m (Program sval)
  genSymSimpleFresh spec = do
    i <- initsGen
    o <- optsGen
    t <- terGen [0..extsSlots spec - 1]
    return $ Program i o t (extsInputNum spec)
    where
      initGen :: m (UnionM sval)
      initGen = choose $ toSym <$> extInitsSpec spec
      initsGen :: m [UnionM sval]
      initsGen = traverse (const initGen) [1 .. extsSlots spec]
      extGen :: Int -> m (UnionM (AST sval))
      extGen i = genSymFresh (CombASTSpec (extsSpec spec) [0, i])
      extsGen :: m [UnionM (AST sval)]
      extsGen = traverse extGen [1..extsSlots spec]

      allSelects :: [a] -> [[a]]
      allSelects [] = [[]]
      allSelects (x:xs) = concat [[x:y, y] | y <- allSelects xs]
      buildOpt :: [AST sval] -> AST sval
      buildOpt [] = undefined
      buildOpt [a] = a
      buildOpt (x:xs) = Binary (mrgReturn $ extsOpt spec) (mrgReturn x) $ mrgReturn (buildOpt xs)
      optGen :: m (UnionM (AST sval))
      optGen = do
        exts <- extsGen
        let m = filter (not . null) $ allSelects $ NoMrg <$> exts
        let j = buildOpt <$> m
        choose j
        {-
        ev <- traverse (\x -> chooseU [x, uConst $ toSym $ extsOptDefaultVal spec]) exts
        case ev of
          [] -> undefined
          umb : umbs -> return $ foldl (uBinary (mrgReturn $ extsOpt spec)) umb umbs
          -}
      optsGen :: m [UnionM (AST sval)]
      optsGen = traverse (const optGen) [1 .. extsSlots spec]

      terGen :: [Int] -> m (UnionM (AST sval))
      terGen [i] = return $ uArg $ mrgReturn i
      terGen (x:xs) = uBinary (mrgReturn $ extsOpt spec) (uArg $ mrgReturn x) <$> terGen xs
      terGen _ = undefined


interpretIntAST ::
  (Mergeable SymBool val, Eq val, Hashable val) =>
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  [UnionM val] ->
  AST val ->
  ExceptT VerificationConditions UnionM val
interpretIntAST u b args = htmemo go
  where
    go (Arg v) = mrgLift $ do
      vv <- v
      args !! vv
    go (Const v) = mrgLift v
    go (Unary f sub) = do
      v <- go #~ sub
      f1 <- lift f
      (u M.! f1) v
    go (Binary f l r) = do
      lv <- go #~ l
      rv <- go #~ r
      f1 <- lift f
      (b M.! f1) lv rv
    go (NoMrg x) = go #~ x

interpretSketch ::
  forall val.
  (Mergeable SymBool val, Eq val, Hashable val) =>
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  Program val ->
  [[UnionM val]] ->
  ExceptT VerificationConditions UnionM val
interpretSketch u b sk = go (inits sk)
  where
    go :: [UnionM val] -> [[UnionM val]] -> ExceptT VerificationConditions UnionM val
    go v [] = interpretIntAST u b v #~ terminate sk
    go v (a : as) = do
      r <-
        mrgTraverse
          (\(x :: UnionM (AST val)) -> mrgFmap mrgReturn $ interpretIntAST u b (a ++ v) #~ x)
          (updates sk)
      go r as

synth ::
  (ExtractSymbolics (S.HashSet TermSymbol) val, Mergeable SymBool val, SEq SymBool val, ToCon val cval, Evaluate Model val, Eq val, Hashable val) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  [[[UnionM val]]] ->
  [[UnionM val]] ->
  ([[UnionM val]] -> SymBool) ->
  ([[UnionM val]] -> val) ->
  Program val ->
  IO (Maybe ([[[UnionM val]]], ConProgram cval))
synth config u b cexs inputs inputSpace spec sketch = do
  m <- cegisWithExcept DefaultVerificationCondition config inputs $ do
    symAssume $ inputSpace inputs
    -- symAssume $ wellFormedProgram sketch
    mrgTraverse_ (\x -> do
      let corr = spec x
      res <- interpretSketch u b sketch x
      symAssert $ corr ==~ res) (inputs : cexs)
  case m of
    Left _ -> return Nothing
    Right (r, mo) -> return $ Just (r, evaluateToCon mo sketch)

verify ::
  (ExtractSymbolics (S.HashSet TermSymbol) val, Mergeable SymBool val, SEq SymBool val, ToCon val cval, Evaluate Model val, Eq val, Hashable val) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  [[UnionM val]] ->
  ([[UnionM val]] -> SymBool) ->
  ([[UnionM val]] -> val) ->
  Program val ->
  IO (Maybe [[cval]])
verify config u b inputs inputSpace spec sketch = do
  m <- solveWithExcept DefaultVerificationCondition config $ do
    symAssume $ inputSpace inputs
    -- symAssume $ wellFormedProgram sketch
    let corr = spec inputs
    res <- interpretSketch u b sketch inputs
    symAssert $ corr ==~ res
  case m of
    Left _ -> return Nothing
    Right mo -> return $ Just (fmap (fromJust . toCon . \(SingleU x) -> x) <$> evaluate True mo inputs)

synth1 ::
  forall n inputSpec val cval.
  ( GenSym SymBool inputSpec val,
    ExtractSymbolics (S.HashSet TermSymbol) val,
    Mergeable SymBool val,
    SEq SymBool val,
    ToSym cval val,
    ToCon val cval,
    Evaluate Model val, Show val, Eq val, Hashable val
  ) =>
  GrisetteSMTConfig n ->
  UnaryFuncMap val ->
  BinaryFuncMap val ->
  inputSpec ->
  ([[UnionM val]] -> SymBool) ->
  ([[UnionM val]] -> val) ->
  Program val ->
  IO (Maybe (ConProgram cval))
synth1 config u b inputSpec inputSpace spec sketch = go [] 3
  where
    go origCexs n = do
      print n
      let inputs = genSymSimple (SimpleListSpec n (SimpleListSpec (fromIntegral $ inputNum sketch) inputSpec)) "a" :: [[UnionM val]]
      synthed <- synth config u b origCexs inputs inputSpace spec sketch
      case synthed of
        Nothing -> return Nothing
        Just (cexs, cp) -> do
          print cexs
          let inputs1 = genSymSimple (SimpleListSpec (n + 1) (SimpleListSpec (fromIntegral $ inputNum sketch) inputSpec)) "a" :: [[UnionM val]]
          v :: Maybe [[cval]] <- verify config u b inputs1 inputSpace spec (toSym cp)
          case v of
            Just _ -> go (cexs ++ origCexs) (n + 1)
            Nothing -> return $ Just cp
