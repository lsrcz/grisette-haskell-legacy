{-# LANGUAGE TemplateHaskell #-}
module Quasiquote where
import Language.Haskell.TH.Quote
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Language.Haskell.TH
import Text.Megaparsec
import Parser

cosette :: QuasiQuoter
cosette = QuasiQuoter { 
    quoteExp = compile . C.pack
  , quotePat = notHandled "patterns"
  , quoteType = notHandled "types"
  , quoteDec = notHandled "declarations"
  }
  where
    notHandled things =
      error $ things ++ " are not handled by the cosette quasiquoter"

compile :: B.ByteString -> Q Exp
compile s = case runParser wholeStringQuery "input" s of
  Left peb ->
    let msg = errorBundlePretty peb in
    [| error msg |]
  Right qu ->
    [| qu |]
    
