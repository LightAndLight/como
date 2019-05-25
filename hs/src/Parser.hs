{-# language OverloadedLists, OverloadedStrings #-}
{-# language TypeApplications #-}
module Parser where

import Syntax (Exp(..), Ty(..), abstract, abstractM)

import Control.Applicative ((<|>))
import Text.Parser.LookAhead
import qualified Text.Parser.Token.Highlight as Highlight
import Text.Trifecta hiding (space)

space :: CharParsing m => m ()
space = () <$ oneOf " \t"

tk :: CharParsing m => m a -> m a
tk m = m <* many space

rightarrow :: CharParsing m => m ()
rightarrow = () <$ text "->"

idStyle :: CharParsing m => IdentifierStyle m
idStyle =
  IdentifierStyle
  { _styleName = "variable"
  , _styleStart = lower
  , _styleLetter = alphaNum
  , _styleReserved = ["let", "in", "caseNat", "zero", "suc"]
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

pexp :: (LookAheadParsing m, TokenParsing m, Monad m) => Unspaced m Exp
pexp =
  letBox_ <|>
  lam <|>
  app
  where
    letBox_ =
      (\ts n a -> LetBox ts n a . abstractM n) <$ tk (reserve idStyle "let") <* tk (char '[') <*>
      optional (tk $ sepBy1 (tk pty) (tk $ char ',')) <* tk (char '|') <*>
      tk (ident idStyle) <* tk (string "|]") <* tk (char '=') <*>
      tk pexp <* tk (reserve idStyle "in") <*>
      pexp

    app =
      NatCase <$ tk (reserve idStyle "caseNat") <*> tk atom <*> tk atom <*> atom <|>
      NatSuc <$ tk (reserve idStyle "suc") <*> atom <|>
      foldl1 App <$>
        sepBy1
          atom
          (try $
           some space <*
           Unspaced (lookAhead $ () <$ runUnspaced atom_ <|> () <$ oneOf "[("))

    lam =
      (\(n, ty) -> Lam n ty . abstract n) <$ tk (char '\\') <*>
      tk
        (between
           (tk $ char '(')
           (char ')')
           ((,) <$> tk (ident idStyle) <* tk (text ":") <*> tk pty) <?>
         "annotated binder") <* tk rightarrow <*>
      pexp

    box =
      (\ts a -> Box ts $ foldr (\(n, _) -> abstract n) a ts) <$ tk (char '[') <*>
      sepBy
        ((,) <$> tk (ident idStyle) <* tk (text ":") <*> tk pty)
        (tk $ char ',') <* tk (char '|') <*>
      tk pexp <* text "|]"

    name =
      (\i -> maybe (Name i) (MName i)) <$>
      ident idStyle <*>
      optional (between (tk $ char '[') (char ']') $ sepBy (tk pexp) (tk $ char ','))

    atom_ =
      NatZero <$ reserve idStyle "zero" <|>
      name

    enclosed =
      box <|>
      between (tk $ char '(') (char ')') (tk pexp)

    atom = atom_ <|> enclosed
