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
        Nothing -> error "eval: Var: stuck"
        Just v -> eval nctx v
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
        !a' = fromValue $ eval nctx a
      in
        eval nctx $
        substM
          (\case
              (0, _) -> a'
              (_, []) -> error "impossible"
              (n, _ : xs) -> MVar (n-1) xs)
          b
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
