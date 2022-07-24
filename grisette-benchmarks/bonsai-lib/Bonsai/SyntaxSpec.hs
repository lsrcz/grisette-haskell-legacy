module Bonsai.SyntaxSpec
  ( Rule (..),
    (-*),
    Generation (..),
    (-->),
    OptimSyntaxSpec,
    nonTerminals,
    terminals,
    terminalToBV,
    bvToTerminal,
    generations,
    getRules,
    buildSyntax,
  )
where

import Data.Bits
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Hashable
import Data.List
import Data.String
import GHC.Generics
import GHC.TypeLits
import Grisette (WordN)

data Rule
  = SymRule B.ByteString
  | PairRule Rule Rule
  deriving (Eq, Generic, Hashable)

instance Show Rule where
  show (SymRule x) = C.unpack x
  show (PairRule l r) = "[" ++ show l ++ ", " ++ show r ++ "]"

ruleTerminals :: S.HashSet B.ByteString -> Rule -> S.HashSet B.ByteString
ruleTerminals s (SymRule n)
  | n `S.member` s = S.empty
  | otherwise = S.singleton n
ruleTerminals s (PairRule l r) = ruleTerminals s l <> ruleTerminals s r

instance IsString Rule where
  fromString = SymRule . C.pack

(-*) :: Rule -> Rule -> Rule
(-*) = PairRule

infixl 9 -*

data Generation = Generation B.ByteString [Rule]

(-->) :: B.ByteString -> [Rule] -> Generation
(-->) = Generation

instance Show Generation where
  show (Generation name rules) = C.unpack name ++ intercalate space (show <$> rules)
    where
      len = B.length name
      space = "\n" ++ replicate (len + 2) ' ' ++ "| "

data OptimSyntaxSpec n = OptimSyntaxSpecC
  { nonTerminals :: S.HashSet B.ByteString,
    terminals :: S.HashSet B.ByteString,
    terminalToBV :: B.ByteString -> Maybe (WordN n),
    bvToTerminal :: WordN n -> Maybe B.ByteString,
    generations :: [Generation],
    getRules :: B.ByteString -> Maybe [Rule]
  }

buildSyntax :: forall n. (KnownNat n, 1 <= n) => [Generation] -> OptimSyntaxSpec n
buildSyntax gens = OptimSyntaxSpecC nt t t2bv bv2t gens rulesf
  where
    gont [] = S.empty
    gont ((Generation name _) : xs) = S.insert name $ gont xs
    nt = gont gens
    t =
      foldl
        ( \acc (Generation _ rules) ->
            foldl (\acc1 rule -> S.union (ruleTerminals nt rule) acc1) acc rules
        )
        S.empty
        gens
    t2bvm :: M.HashMap B.ByteString (WordN n)
    t2bvm =
      fst $
        foldl
          ( \(acc, n) v ->
              if n == 0
                then error "The bit width is not large enough"
                else (M.insert v n acc, n `shift` 1)
          )
          (M.empty, 1)
          t
    t2bv s = M.lookup s t2bvm
    bv2tm :: M.HashMap (WordN n) B.ByteString
    bv2tm = M.foldlWithKey (\acc v n -> M.insert n v acc) M.empty t2bvm
    bv2t b = M.lookup b bv2tm
    rulesm :: M.HashMap B.ByteString [Rule]
    rulesm = foldl (\acc (Generation name rules) -> M.insert name rules acc) M.empty gens
    rulesf s = M.lookup s rulesm
