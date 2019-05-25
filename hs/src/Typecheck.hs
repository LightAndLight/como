module Typecheck where

import Data.Map (Map)
import Data.Text (Text)

import qualified Data.Map as Map

import Syntax (Exp(..), Ty(..))

data CheckErrorSubst
  = TooFewTerms [Exp] [Ty]
  | TooManyTerms [Exp] [Ty]
  | TypeErrors [CheckError]
  deriving (Eq, Ord, Show)

data CheckError
  = InferError InferError
  | TypeMismatch Ty Ty
  deriving (Eq, Ord, Show)

data InferError
  = NotInScope Text
  | NotInScopeM Text
  | NotInScopeName Text
  | LamBodyError InferError
  | AppLeftError InferError
  | AppRightError CheckError
  | BoxError InferError
  | LetBoxLeftError InferError
  | LetBoxRightError InferError
  | NatSucError CheckError
  | NatCase1Error InferError
  | NatCase2Error CheckError
  | NatCase3Error CheckError
  | ExpectedFunction Ty
  | ExpectedBox Ty
  | CheckErrorSubst Text CheckErrorSubst
  deriving (Eq, Ord, Show)

checkSubst ::
  Map Text Ty ->
  [([Ty], Ty)] ->
  [Ty] ->
  [Exp] ->
  [Ty] ->
  Either CheckErrorSubst [Exp]
checkSubst _ _ _ [] [] = pure []
checkSubst _ _ _ [] (x : ts) = Left $ TooFewTerms [] (x : ts)
checkSubst _ _ _ (x : us) [] = Left $ TooManyTerms (x : us) []
checkSubst nctx mctx ctx (u : us) (t : ts) =
  case checkSubst nctx mctx ctx us ts of
    Right us' ->
      case check nctx mctx ctx u t of
        Right u' -> pure $ u' : us'
        Left err -> Left $ TypeErrors [err]
    Left (TooFewTerms a b) -> Left $ TooFewTerms (u : a) (t : b)
    Left (TooManyTerms a b) -> Left $ TooManyTerms (u : a) (t : b)
    Left (TypeErrors errs) ->
      case check nctx mctx ctx u t of
        Right{} -> Left $ TypeErrors errs
        Left err -> Left $ TypeErrors (err : errs)

check ::
  Map Text Ty ->
  [([Ty], Ty)] ->
  [Ty] ->
  Exp ->
  Ty ->
  Either CheckError Exp
check nctx mctx ctx tm ty =
  case infer nctx mctx ctx tm of
    Right ty' ->
      case ty == ty' of
        True -> pure tm
        False -> Left $ TypeMismatch ty ty'
    Left err -> Left $ InferError err

index :: Int -> [a] -> Maybe a
index _ [] = Nothing
index 0 (x : xs) = Just x
index n (_ : xs) = index (n-1) xs

infer ::
  Map Text Ty ->
  [([Ty], Ty)] ->
  [Ty] ->
  Exp ->
  Either InferError Ty
infer nctx mctx ctx NatZero = pure TyNat
infer nctx mctx ctx (NatSuc n) =
  case check nctx mctx ctx n TyNat of
    Right{} -> pure TyNat
    Left err -> Left $ NatSucError err
infer nctx mctx ctx (NatCase z s n) =
  case infer nctx mctx ctx z of
    Right zTy ->
      case check nctx mctx ctx s (TyArr TyNat zTy) of
        Right{} ->
          case check nctx mctx ctx n TyNat of
            Right{} -> pure zTy
            Left err -> Left $ NatCase3Error err
        Left err -> Left $ NatCase2Error err
    Left err -> Left $ NatCase1Error err
infer nctx mctx ctx (Name n) =
  case Map.lookup n nctx of
    Just t -> pure t
    Nothing -> Left $ NotInScopeName n
infer nctx mctx ctx (Var n) =
  case index n ctx of
    Just t -> pure t
    Nothing -> Left $ NotInScope _
infer nctx mctx ctx (MVar n xs) =
  case index n mctx of
    Just (ts, t) ->
      case checkSubst nctx mctx ctx xs ts of
        Right{} -> pure t
        Left err -> Left $ CheckErrorSubst _ err
    Nothing -> Left $ NotInScopeM _
infer nctx mctx ctx (Lam name ty u) =
  case infer nctx mctx (ty : ctx) u of
    Right uTy -> pure $ TyArr ty uTy
    Left err -> Left $ LamBodyError err
infer nctx mctx ctx (App f x) =
  case infer nctx mctx ctx f of
    Right (TyArr a b) ->
      case check nctx mctx ctx x a of
        Right{} -> pure b
        Left err -> Left $ AppRightError err
    Right a -> Left $ ExpectedFunction a
    Left err -> Left $ AppLeftError err
infer nctx mctx ctx (Box ts u) =
  let tys = snd <$> ts in
  case infer mempty mctx tys u of
    Right ty -> pure $ TyBox tys ty
    Left err -> Left $ BoxError err
infer nctx mctx ctx (LetBox mtys name a b) =
  case infer nctx mctx ctx a of
    Right (TyBox ts ty) ->
      case infer nctx ((ts , ty) : mctx) ctx b of
        Right ty' -> pure ty'
        Left err -> Left $ LetBoxRightError err
    Right ty -> Left $ ExpectedBox ty
    Left err -> Left $ LetBoxLeftError err
