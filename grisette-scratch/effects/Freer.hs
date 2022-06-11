{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
module Freer where
import Control.Monad.Freer
import Grisette

data Branch bool a where
  Branch :: bool -> Branch bool Bool

branch :: (Member (Branch bool) effs) => bool -> Eff effs s -> Eff effs s -> Eff effs s
branch b l r = do
  br <- send $ Branch b
  if br then l else r

runBranch :: (SymBoolOp bool) => Eff (Branch bool ': effs) a -> UnionMBase bool (Eff effs a)
runBranch = undefined

runUnion :: Eff '[UnionM] a -> UnionM a
runUnion = runM

eif :: (SymBoolOp bool, LastMember (UnionMBase bool) effs) => bool -> Eff effs s -> Eff effs s -> Eff effs s
eif b l r = do
  br <- sendM $ mrgIf b (return False) (return True)
  if br then l else r


