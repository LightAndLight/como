{-# language FlexibleContexts #-}
{-# language TemplateHaskell #-}
module Typecheck where

import Control.Lens.Getter (view)
import Control.Lens.Setter (locally)
import Control.Lens.TH (makeLenses)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader)
import Data.Map (Map)
import Data.Text (Text)

import qualified Data.Map as Map

import Syntax (Exp(..), Ty(..))

mkEnv :: Map Text Ty -> Env
mkEnv a = Env { _namesCtx = a, _modalCtx = [], _ctx = [] }

data Env
  = Env
  { _namesCtx :: Map Text Ty
  , _modalCtx :: [(Text, [Ty], Ty)]
  , _ctx :: [Ty]
  } deriving (Eq, Ord, Show)
makeLenses ''Env

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
  = NotInScope Int
  | NotInScopeM Int
  | NotInScopeMName Text
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
  MonadReader Env m =>
  [Exp] ->
  [Ty] ->
  ExceptT CheckErrorSubst m [Exp]
checkSubst [] [] = pure []
checkSubst [] (x : ts) = throwError $ TooFewTerms [] (x : ts)
checkSubst (x : us) [] = throwError $ TooManyTerms (x : us) []
checkSubst (u : us) (t : ts) = do
  res0 <- runExceptT $ checkSubst us ts
  case res0 of
    Right us' -> do
      res1 <- runExceptT $ check u t
      case res1 of
        Right u' -> pure $ u' : us'
        Left err -> throwError $ TypeErrors [err]
    Left (TooFewTerms a b) -> throwError $ TooFewTerms (u : a) (t : b)
    Left (TooManyTerms a b) -> throwError $ TooManyTerms (u : a) (t : b)
    Left (TypeErrors errs) -> do
      res1 <- runExceptT $ check u t
      case res1 of
        Right{} -> throwError $ TypeErrors errs
        Left err -> throwError $ TypeErrors (err : errs)

check ::
  MonadReader Env m =>
  Exp ->
  Ty ->
  ExceptT CheckError m Exp
check tm ty = do
  res0 <- runExceptT $ infer tm
  case res0 of
    Right ty' ->
      case ty == ty' of
        True -> pure tm
        False -> throwError $ TypeMismatch ty ty'
    Left err -> throwError $ InferError err

index :: Int -> [a] -> Maybe a
index _ [] = Nothing
index 0 (x : _) = Just x
index n (_ : xs) = index (n-1) xs

infer ::
  MonadReader Env m =>
  Exp ->
  ExceptT InferError m Ty
infer NatZero = pure TyNat
infer (NatSuc n) = do
  res0 <- runExceptT $ check n TyNat
  case res0 of
    Right{} -> pure TyNat
    Left err -> throwError $ NatSucError err
infer (NatCase z s n) = do
  res0 <- runExceptT $ infer z
  case res0 of
    Right zTy -> do
      res1 <- runExceptT $ check s (TyArr TyNat zTy)
      case res1 of
        Right{} -> do
          res2 <- runExceptT $ check n TyNat
          case res2 of
            Right{} -> pure zTy
            Left err -> throwError $ NatCase3Error err
        Left err -> throwError $ NatCase2Error err
    Left err -> throwError $ NatCase1Error err
infer (Name n) = do
  nctx <- view namesCtx
  case Map.lookup n nctx of
    Just t -> pure t
    Nothing -> throwError $ NotInScopeName n
infer (MName n _) = throwError $ NotInScopeMName n
infer (Var n) = do
  c <- view ctx
  case index n c of
    Just t -> pure t
    Nothing -> throwError $ NotInScope n
infer (MVar n xs) = do
  mctx <- view modalCtx
  case index n mctx of
    Just (name, ts, t) -> do
      res0 <- runExceptT $ checkSubst xs ts
      case res0 of
        Right{} -> pure t
        Left err -> throwError $ CheckErrorSubst name err
    Nothing -> throwError $ NotInScopeM n
infer (Lam _ ty u) = do
  res0 <- runExceptT $ locally ctx (ty :) (infer u)
  case res0 of
    Right uTy -> pure $ TyArr ty uTy
    Left err -> throwError $ LamBodyError err
infer (App f x) = do
  res0 <- runExceptT $ infer f
  case res0 of
    Right (TyArr a b) -> do
      res1 <- runExceptT $ check x a
      case res1 of
        Right{} -> pure b
        Left err -> throwError $ AppRightError err
    Right a -> throwError $ ExpectedFunction a
    Left err -> throwError $ AppLeftError err
infer (Box ts u) = do
  let tys = snd <$> ts
  res0 <-
    runExceptT $
    locally namesCtx (const mempty) $
    locally ctx (const tys) (infer u)
  case res0 of
    Right ty -> pure $ TyBox tys ty
    Left err -> throwError $ BoxError err
infer (LetBox _ name a b) = do
  res0 <- runExceptT $ infer a
  case res0 of
    Right (TyBox ts ty) -> do
      -- TODO: typecheck the annotations
      res1 <- runExceptT $ locally modalCtx ((name, ts, ty) :) (infer b)
      case res1 of
        Right ty' -> pure ty'
        Left err -> throwError $ LetBoxRightError err
    Right ty -> throwError $ ExpectedBox ty
    Left err -> throwError $ LetBoxLeftError err
