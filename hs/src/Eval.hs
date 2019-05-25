{-# language BangPatterns #-}
{-# language LambdaCase #-}
module Eval where

import Data.Map (Map)
import Data.Text (Text)

import qualified Data.Map as Map

import Syntax

data Value
  = VLam Text Ty Exp
  | VBox [(Text, Ty)] Exp
  | VNatZero
  | VNatSuc Value
  deriving (Eq, Ord, Show)

fromValue :: Value -> Exp
fromValue v =
  case v of
    VLam a b c -> Lam a b c
    VBox a b -> Box a b
    VNatZero -> NatZero
    VNatSuc a -> NatSuc $ fromValue a

eval :: Map Text Exp -> Exp -> Value
eval nctx e =
  case e of
    Name n ->
      case Map.lookup n nctx of
        Nothing -> error "eval: Name: stuck"
        Just v -> eval nctx v
    MName{} -> error "eval: MName: stuck"
    Var{} -> error "eval: Var: stuck"
    MVar{} -> error "eval: MVar: stuck"
    Lam name mty a -> VLam name mty a
    App a b ->
      let
        !a' = fromValue $ eval nctx a
        !b' = fromValue $ eval nctx b
      in
        eval nctx $ subst (\case; 0 -> b'; n -> Var (n-1)) a'
    Box ts a -> VBox ts a
    LetBox _ _ a b ->
      let
        !a' = eval nctx a
      in
        case a' of
          VBox _ a'' ->
            eval nctx $
            substM
              (\case
                  (0, _) -> a''
                  (_, []) -> error "impossible"
                  (n, _ : xs) -> MVar (n-1) xs)
              b
          _ -> error "eval: LetBox: stuck"
    NatZero -> VNatZero
    NatSuc a ->
      let
        !a' = eval nctx a
      in
        VNatSuc a'
    NatCase a b c ->
      let
        !a' = eval nctx a
        !b' = fromValue $ eval nctx b
        !c' = fromValue $ eval nctx c
      in
        case c' of
          NatZero -> a'
          NatSuc v ->
            eval nctx $
            subst (\case; 0 -> v; n -> Var (n-1)) b'
          _ -> error "eval: NatCase: stuck"

-- | Staging evaluates all occurrences of LetBox
stage :: Map Text Exp -> Exp -> Exp
stage nctx e =
  case e of
    Name{} -> e
    MName a b -> MName a $ stage nctx <$> b
    Var{} -> e
    MVar a b -> MVar a $ stage nctx <$> b
    Lam a b c -> Lam a b $ stage nctx c
    App a b -> App (stage nctx a) (stage nctx b)
    Box a b -> Box a b
    LetBox _ _ c d ->
      case eval nctx $ stage nctx c of
        VBox _ c' ->
            substM
              (\case
                  (0, _) -> c'
                  (_, []) -> error "impossible"
                  (n, _ : xs) -> MVar (n-1) xs)
              (stage nctx d)
        _ -> error "stage: LetBox: stuck"
    NatZero -> e
    NatSuc a -> NatSuc $ stage nctx a
    NatCase a b c -> NatCase (stage nctx a) (stage nctx b) (stage nctx c)