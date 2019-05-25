module Syntax where

import Data.Text (Text)

data Ty
  = TyArr Ty Ty
  | TyBox [Ty] Ty
  | TyNat
  deriving (Eq, Ord, Show)

data Exp
  = Name Text
  | MName Text [Exp]
  | Var !Int
  | MVar !Int [Exp]
  | Lam Text Ty Exp
  | App Exp Exp
  | Box [(Text, Ty)] Exp
  | LetBox (Maybe [Ty]) Text Exp Exp
  | NatZero
  | NatSuc Exp
  | NatCase Exp Exp Exp
  deriving (Eq, Ord, Show)

rho :: (Int -> Int) -> Int -> Int
rho _ 0 = 0
rho f n = f (n-1) + 1

-- | Renaming bound variables
rename :: (Int -> Int) -> Exp -> Exp
rename _ (Name a) = Name a
rename f (MName a as) = MName a $ rename f <$> as
rename f (Var x) = Var (f x)
rename f (MVar x as) = MVar x (rename f <$> as)
rename f (Lam name ty a) = Lam name ty (rename (rho f) a)
rename f (App a b) = App (rename f a) (rename f b)
rename _ (Box vs a) = Box vs a
rename f (LetBox tys name a b) = LetBox tys name (rename f a) (rename f b)
rename _ NatZero = NatZero
rename f (NatSuc n) = NatSuc (rename f n)
rename f (NatCase z s n) = NatCase (rename f z) (rename f s) (rename f n)

-- | Renaming bound modal variables
renameM :: (Int -> Int) -> Exp -> Exp
renameM _ (Name a) = Name a
renameM f (MName a as) = MName a $ renameM f <$>  as
renameM _ (Var x) = Var x
renameM f (MVar x as) = MVar (f x) (renameM f <$> as)
renameM f (Lam name ty a) = Lam name ty (renameM f a)
renameM f (App a b) = App (renameM f a) (renameM f b)
renameM f (Box tys a) = Box tys (renameM f a)
renameM f (LetBox name tys a b) = LetBox name tys (renameM f a) (renameM (rho f) b)
renameM _ NatZero = NatZero
renameM f (NatSuc n) = NatSuc (renameM f n)
renameM f (NatCase z s n) = NatCase (renameM f z) (renameM f s) (renameM f n)

sigma :: (Int -> Exp) -> Int -> Exp
sigma _ 0 = Var 0
sigma f n = rename (+1) $ f (n-1)

sigmaM :: ((Int, [Exp]) -> Exp) -> (Int, [Exp]) -> Exp
sigmaM _ (0, xs) = MVar 0 xs
sigmaM _ (_, []) = error "impossible"
sigmaM f (n, _ : xs) = renameM (+1) $ f (n-1, xs)

-- | Substitution
subst :: (Int -> Exp) -> Exp -> Exp
subst _ (Name a) = Name a
subst f (MName a as) = MName a $ subst f <$> as
subst f (Var x) = f x
subst f (MVar x xs) = MVar x (subst f <$> xs)
subst f (Lam name ty a) = Lam name ty (subst (sigma f) a)
subst f (App a b) = App (subst f a) (subst f b)
subst _ (Box tys a) = Box tys a
subst f (LetBox tys name a b) = LetBox tys name (subst f a) (subst (renameM (+1) . f) b)
subst _ NatZero = NatZero
subst f (NatSuc n) = NatSuc (subst f n)
subst f (NatCase z s n) = NatCase (subst f z) (subst f s) (subst f n)

getExp :: [Exp] -> Int -> Exp
getExp [] _ = error "impossible"
getExp (x : _) 0 = x
getExp (_ : xs) n = getExp xs (n-1)

-- | Modal substitution
substM :: ((Int, [Exp]) -> Exp) -> Exp -> Exp
substM _ (Name a) = Name a
substM f (MName a as) = MName a $ substM f <$> as
substM _ (Var x) = Var x
substM f (MVar x as) = subst (getExp (substM f <$> as)) (f (x, as))
substM f (Lam name ty a) = Lam name ty (substM f a)
substM f (App a b) = App (substM f a) (substM f b)
substM f (Box tys a) = Box tys (substM f a)
substM f (LetBox tys name a b) = LetBox tys name (substM f a) (substM (sigmaM f) b)
substM _ NatZero = NatZero
substM f (NatSuc n) = NatSuc (substM f n)
substM f (NatCase z s n) = NatCase (substM f z) (substM f s) (substM f n)

-- | Bind a variable
abstract :: Text -> Exp -> Exp
abstract n = go 0
  where
    go depth e =
      case e of
        Name n' -> if n == n' then Var depth else Name n'
        MName a as -> MName a $ go depth <$> as
        Var v -> if v < depth then Var v else Var (v+1)
        MVar a b -> MVar a (go depth <$> b)
        Lam name ty a -> Lam name ty $ go (depth+1) a
        App a b -> App (go depth a) (go depth b)
        Box a b -> Box a b
        LetBox tys name a b -> LetBox tys name (go depth a) (go depth b)
        NatZero -> NatZero
        NatSuc a -> NatSuc $ go depth a
        NatCase a b c -> NatCase (go depth a) (go depth b) (go depth c)

-- | Bind a modal variable
--
-- Also abstracts over relevant `Name`s by converting them to `MVar _ []`
abstractM :: Text -> Exp -> Exp
abstractM n = go 0
  where
    go depth e =
      case e of
        Name n' -> if n == n' then MVar depth [] else Name n'
        MName n' as ->
          (if n == n' then MVar depth else MName n') (go depth <$> as)
        Var v -> Var v
        MVar a b -> MVar (if a < depth then a else a+1) (go depth <$> b)
        Lam name ty a -> Lam name ty $ go depth a
        App a b -> App (go depth a) (go depth b)
        Box a b -> Box a $ go depth b
        LetBox tys name a b -> LetBox tys name (go depth a) (go (depth+1) b)
        NatZero -> NatZero
        NatSuc a -> NatSuc $ go depth a
        NatCase a b c -> NatCase (go depth a) (go depth b) (go depth c)