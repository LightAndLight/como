{-# language OverloadedLists, OverloadedStrings #-}
module Parser where

import Syntax (Exp(..), Ty(..))

import Control.Applicative ((<|>))
import Data.Text (Text)
import qualified Text.Parser.Token.Highlight as Highlight
import Text.Trifecta hiding (space)

space :: CharParsing m => m ()
space = () <$ oneOf " \t"

tk :: CharParsing m => m a -> m a
tk m = m <* many space

rightarrow :: CharParsing m => m ()
rightarrow = () <$ text "->"

pident :: (TokenParsing m, Monad m) => Unspaced m Text
pident =
  ident $
  IdentifierStyle
  { _styleName = "variable"
  , _styleStart = lower
  , _styleLetter = alphaNum
  , _styleReserved = ["let"]
  , _styleHighlight = Highlight.Identifier
  , _styleReservedHighlight = Highlight.ReservedIdentifier
  }

pty :: TokenParsing m => Unspaced m Ty
pty = arr
  where
    arr =
      (\a -> maybe a (TyArr a)) <$>
      compound <*>
      optional (tk (try $ many space *> rightarrow) *> arr)
    compound =
      TyBox <$ tk (text "Box") <*>
      between (tk $ char '[') (char ']') (sepBy (tk pty) (tk $ char ',')) <*>
      atom <|>
      atom
    atom =
      TyNat <$ text "Nat" <|>
      between (tk $ char '(') (char ')') (tk $ pty)

pexp :: (TokenParsing m, Monad m) => Unspaced m Exp
pexp = lam
  where
    lam =
      (\(n, ty) -> Lam n ty) <$ char '\\' <*>
      (between (tk $ char '(') (char ')') $ (,) <$> pident <* text ":" <*> pty) <* tk rightarrow <*>
      pexp
