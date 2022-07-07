module SymBool where
import GHC.Generics
import Data.Hashable
import qualified Data.HashSet as S

data SymBool
  = Sym String
  | Con Bool
  | Or SymBool SymBool
  | And SymBool SymBool
  | Not SymBool
  | IteBool SymBool SymBool SymBool
  deriving (Show, Generic, Eq, Hashable)

ors :: SymBool -> SymBool -> SymBool
ors l@(Con True) _ = l
ors (Con False) r = r
ors _ r@(Con True) = r
ors l (Con False) = l
ors l r = Or l r

ands :: SymBool -> SymBool -> SymBool
ands l@(Con False) _ = l
ands (Con True) r = r
ands _ r@(Con False) = r
ands l (Con True) = l
ands l r = And l r

nots :: SymBool -> SymBool
nots (Con b) = Con $ not b
nots r = Not r

ites :: SymBool -> SymBool -> SymBool -> SymBool
ites (Con True) l _ = l
ites (Con False) _ r = r
ites c (Con True) r = ors c r
ites c (Con False) r = ands (nots c) r
ites c l (Con True) = ors (nots c) l
ites c l (Con False) = ands c l 
ites c l r = IteBool c l r

allSubSymBools :: [SymBool] -> S.HashSet SymBool
allSubSymBools [] = S.empty
allSubSymBools (v:vs) = go v (allSubSymBools vs)
  where
    go x@Sym{} s = S.insert x s
    go x@Con{} s = S.insert x s
    go x@(Or l r) s = go l (go r (S.insert x s))
    go x@(And l r) s = go l (go r (S.insert x s))
    go x@(Not n) s = go n (S.insert x s)
    go x@(IteBool c l r) s = go c (go l (go r (S.insert x s)))






