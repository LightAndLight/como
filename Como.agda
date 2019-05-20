module Como where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Data.List using (List; _∷_; []; _++_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

data Ty : Set where
  Arr : Ty → Ty → Ty
  Box : List Ty → Ty → Ty

infix 3 _∈_
data _∈_ {A : Set} : A → List A → Set where
  here : ∀{x xs} → x ∈ x ∷ xs
  there : ∀{y x xs} → x ∈ xs → x ∈ y ∷ xs

data Lookup {A : Set} : ℕ → A → List A → Set where
  here : ∀{x xs} → Lookup zero x (x ∷ xs)
  there : ∀{n x y xs} → Lookup n x xs → Lookup (suc n) x (y ∷ xs)

toℕ : ∀{A : Set} {x : A} {xs} → x ∈ xs → ℕ
toℕ here = zero
toℕ (there a) = suc (toℕ a)

inj₁-∈ : ∀{A : Set} {x : A} {xs ys} → x ∈ xs → x ∈ xs ++ ys
inj₁-∈ here = here
inj₁-∈ (there a) = there (inj₁-∈ a)

inj₂-∈ : ∀{A : Set} {x : A} {xs ys} → x ∈ ys → x ∈ xs ++ ys
inj₂-∈ {_} {_} {[]} a = a
inj₂-∈ {_} {_} {x ∷ xs} a = there (inj₂-∈ a)

data All {A : Set} (p : A → Set) : List A → Set where
  All-nil : All p []
  All-cons : ∀{x xs} → p x → All p xs → All p (x ∷ xs)

map-All :
  ∀{A : Set} {p p' : A → Set} →
  (∀{x} → p x → p' x) →
  ∀{xs} → All p xs → All p' xs
map-All f All-nil = All-nil
map-All f (All-cons x₁ a) = All-cons (f x₁) (map-All f a)

data Tm : List (List Ty × Ty) → List Ty → Ty → Set where
  Var : ∀{A Δ Γ} → A ∈ Γ → Tm Δ Γ A
  CVar : ∀{Ψ A Δ Γ} → (Ψ , A) ∈ Δ → All (Tm Δ Γ) Ψ → Tm Δ Γ A

  →I : ∀{B Δ Γ} → (A : Ty) → Tm Δ (A ∷ Γ) B → Tm Δ Γ (Arr A B)
  →E : ∀{A B Δ Γ} → Tm Δ Γ (Arr A B) → Tm Δ Γ A → Tm Δ Γ B

  ■I : ∀{A Δ Ψ Γ} → Tm Δ Ψ A → Tm Δ Γ (Box Ψ A)
  ■E : ∀{A B Δ Ψ Γ} → Tm Δ Γ (Box Ψ A) → Tm ((Ψ , A) ∷ Δ) Γ B → Tm Δ Γ B

ρ :
  ∀{A : Set} {xs xs' : List A} →
  (∀{x} → x ∈ xs → x ∈ xs') →
  ∀{x y} → x ∈ y ∷ xs → x ∈ y ∷ xs'
ρ f here = here
ρ f (there a) = there (f a)

mutual
  {-

  I would use map-All to map across the proof, but agda doesn't know it's terminating.
  This way is explicitly structural-recursive.

  -}
  rename-All : ∀{Γ Γ'} → (∀{A} → A ∈ Γ → A ∈ Γ') → ∀{Δ Ψ} → All (Tm Δ Γ) Ψ → All (Tm Δ Γ') Ψ
  rename-All f All-nil = All-nil
  rename-All f (All-cons x₁ a) = All-cons (rename f x₁) (rename-All f a)

  rename : ∀{Γ Γ'} → (∀{A} → A ∈ Γ → A ∈ Γ') → ∀{A Δ} → Tm Δ Γ A → Tm Δ Γ' A
  rename f (Var x) = Var (f x)
  rename f (CVar x prf) = CVar x (rename-All f prf)
  rename f (→I ty a) = →I ty (rename (ρ f) a)
  rename f (→E a a₁) = →E (rename f a) (rename f a₁)
  rename f (■I a) = ■I a
  rename f (■E a a₁) = ■E (rename f a) (rename f a₁)

mutual
  rename-C-All : ∀{Δ Δ'} → (∀{A} → A ∈ Δ → A ∈ Δ') → ∀{Γ Ψ} → All (Tm Δ Γ) Ψ → All (Tm Δ' Γ) Ψ
  rename-C-All f All-nil = All-nil
  rename-C-All f (All-cons x₁ a) = All-cons (rename-C f x₁) (rename-C-All f a)

  rename-C : ∀{Δ Δ'} → (∀{A} → A ∈ Δ → A ∈ Δ') → ∀{A Γ} → Tm Δ Γ A → Tm Δ' Γ A
  rename-C f (Var x) = Var x
  rename-C f (CVar x prf) = CVar (f x) (rename-C-All f prf)
  rename-C f (→I ty a) = →I ty (rename-C f a)
  rename-C f (→E a a₁) = →E (rename-C f a) (rename-C f a₁)
  rename-C f (■I a) = ■I (rename-C f a)
  rename-C f (■E a a₁) = ■E (rename-C f a) (rename-C (ρ f) a₁)

context-identity : ∀{Δ Ψ} → All (Tm Δ Ψ) Ψ
context-identity {Δ} {[]} = All-nil
context-identity {Δ} {x ∷ xs} = All-cons (Var here) (rename-All there context-identity)

σ-C :
  ∀{Δ Δ'} →
  (∀{Ψ A} → (Ψ , A) ∈ Δ → Tm Δ' Ψ A) →
  ∀{Ψ A B} → (Ψ , A) ∈ B ∷ Δ → Tm (B ∷ Δ') Ψ A
σ-C f here = CVar here context-identity
σ-C f (there a) = rename-C there (f a)

upgrade :
  ∀{A Δ Γ Ψ} →
  Tm Δ Ψ A →
  All (Tm Δ Γ) Ψ →
  Tm Δ Γ A
upgrade a All-nil = rename (λ ()) a
{- this is like whoa. what does it mean, exactly? -}
upgrade a (All-cons x xs) = →E (upgrade (→I _ a) xs) x

mutual
  subst-C-All :
    ∀{Γ Δ Δ'} →
    (∀{Ψ A} → (Ψ , A) ∈ Δ → Tm Δ' Ψ A) →
    ∀{Ψ} → All (Tm Δ Γ) Ψ → All (Tm Δ' Γ) Ψ
  subst-C-All f All-nil = All-nil
  subst-C-All f (All-cons x₁ a) = All-cons (subst-C f x₁) (subst-C-All f a)

  subst-C : ∀{Γ Δ Δ'} → (∀{Ψ A} → (Ψ , A) ∈ Δ → Tm Δ' Ψ A) → ∀{A} → Tm Δ Γ A → Tm Δ' Γ A
  subst-C f (Var x) = Var x
  subst-C f (CVar x prf) = upgrade (f x) (subst-C-All f prf)
  subst-C f (→I ty a) = →I ty (subst-C f a)
  subst-C f (→E a a₁) = →E (subst-C f a) (subst-C f a₁)
  subst-C f (■I a) = ■I (subst-C f a)
  subst-C f (■E a a₁) = ■E (subst-C f a) (subst-C (σ-C f) a₁)

σ :
  ∀{Δ Γ Γ'} →
  (∀{A} → A ∈ Γ → Tm Δ Γ' A) →
  ∀{A B} → A ∈ B ∷ Γ → Tm Δ (B ∷ Γ') A
σ f here = Var here
σ f (there a) = rename there (f a)

mutual
  subst-All :
    ∀{Γ Γ' Δ} →
    (∀{A} → A ∈ Γ → Tm Δ Γ' A) →
    ∀{Ψ} → All (Tm Δ Γ) Ψ → All (Tm Δ Γ') Ψ
  subst-All f All-nil = All-nil
  subst-All f (All-cons x₁ a) = All-cons (subst f x₁) (subst-All f a)

  subst : ∀{Γ Γ' Δ} → (∀{A} → A ∈ Γ → Tm Δ Γ' A) → ∀{A} → Tm Δ Γ A → Tm Δ Γ' A
  subst f (Var x) = f x
  subst f (CVar x x₁) = CVar x (subst-All f x₁)
  subst f (→I ty a) = →I ty (subst (σ f) a)
  subst f (→E a a₁) = →E (subst f a) (subst f a₁)
  subst f (■I a) = ■I a
  subst f (■E a a₁) = ■E (subst f a) (subst (rename-C there ∘ f) a₁)


data Value {Δ} {Γ} : ∀{A} → Tm Δ Γ A → Set where
  v-→I : ∀{B} → (A : Ty) → (a : Tm Δ (A ∷ Γ) B) → Value (→I A a)
  v-■I : ∀{A Ψ} {a : Tm Δ Ψ A} → Value (■I a)

data _↓_ {Δ Γ} : ∀{A} → Tm Δ Γ A → Tm Δ Γ A → Set where
  ↓-→E₁ :
    ∀{A B} {a a' : Tm Δ Γ (Arr A B)} {b} →
    a ↓ a' →
    →E a b ↓ →E a' b
  ↓-→E₂ :
    ∀{A B} {a : Tm Δ Γ (Arr A B)} {b b'} →
    Value a →
    b ↓ b' →
    →E a b ↓ →E a b'
  ↓-β :
    ∀{A B} {a : Tm Δ (A ∷ Γ) B} {b} →
    Value b →
    →E (→I A a) b ↓ subst (λ { here → b; (there p) → Var p }) a
  ↓-■E₁ :
    ∀{A B Ψ} {a a' : Tm Δ Γ (Box Ψ A)} {b : Tm ((Ψ , A) ∷ Δ) Γ B} →
    a ↓ a' →
    ■E a b ↓ ■E a' b
  ↓-unbox :
    ∀{A B Ψ} {a} {b : Tm ((Ψ , A) ∷ Δ) Γ B} →
    ■E (■I a) b ↓ subst-C (λ { here → a; (there p) → CVar p context-identity }) b

value-¬↓ : ∀{Δ Γ A} {tm : Tm Δ Γ A} → (v : Value tm) → ¬( ∃[ tm' ]( tm ↓ tm' ))
value-¬↓ (v-→I _ _) (tm' , ())
value-¬↓ v-■I (tm' , ())

progress : ∀{A} → (tm : Tm [] [] A) → Value tm ⊎ (∃[ tm' ](tm ↓ tm'))
progress (Var ())
progress (CVar () _)
progress (→I ty tm) = inj₁ (v-→I ty tm)
progress (→E a b) with progress a
progress (→E a b) | inj₂ (a' , a↓a') = inj₂ (→E a' b , ↓-→E₁ a↓a')
progress (→E a b) | inj₁ va with progress b
progress (→E a b) | inj₁ va | inj₂ (b' , b↓b') = inj₂ (→E a b' , ↓-→E₂ va b↓b')
progress (→E (→I ty e) b) | inj₁ (v-→I .ty .e) | inj₁ vb = inj₂ (_ , ↓-β vb)
progress (■I tm) = inj₁ v-■I
progress (■E tm tm₁) with progress tm
progress (■E tm tm₁) | inj₂ (tm' , tm↓tm') = inj₂ (■E tm' tm₁ , ↓-■E₁ tm↓tm')
progress (■E (■I a) tm₁) | inj₁ v-■I = inj₂ (_ , ↓-unbox)

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : ¬ A → Dec A

data U : Set where
  U-Var : ℕ → U
  U-CVar : ℕ → List U → U

  U-→I : Ty → U → U
  U-→E : U → U → U

  U-■I : U → U
  U-■E : U → U → U

ρ-U : (ℕ → ℕ) → (ℕ → ℕ)
ρ-U f zero = zero
ρ-U f (suc x) = suc (f x)

mutual
  rename-List : (ℕ → ℕ) → List U → List U
  rename-List f [] = []
  rename-List f (x ∷ xs) = rename-U f x ∷ rename-List f xs

  rename-U : (ℕ → ℕ) → U → U
  rename-U f (U-Var x) = U-Var (f x)
  rename-U f (U-CVar x y) = U-CVar x (rename-List f y)
  rename-U f (U-→I x a) = U-→I x (rename-U (ρ-U f) a)
  rename-U f (U-→E a a₁) = U-→E (rename-U f a) (rename-U f a₁)
  rename-U f (U-■I a) = U-■I a
  rename-U f (U-■E a b) = U-■E (rename-U f a) (rename-U f b)

mutual
  untag-All : ∀{Δ Γ xs} → All (Tm Δ Γ) xs → List U
  untag-All All-nil = []
  untag-All (All-cons x xs) = untag x ∷ untag-All xs

  untag : ∀{Δ Γ ty} → Tm Δ Γ ty → U
  untag (Var x) = U-Var (toℕ x)
  untag (CVar x y) = U-CVar (toℕ x) (untag-All y)
  untag (→I A t) = U-→I A (untag t)
  untag (→E t u) = U-→E (untag t) (untag u)
  untag (■I t) = U-■I (untag t)
  untag (■E t u) = U-■E (untag t) (untag u)

data Check (Δ : List (List Ty × Ty)) (Γ : List Ty) : U → Ty → Set where
  yes : ∀{u ty} → (tm : Tm Δ Γ ty) → untag tm ≡ u → Check Δ Γ u ty
  not-in-scope :
    ∀{t n} →
    ¬(Lookup n t Γ) →
    Check Δ Γ (U-Var n) t
  not-in-scope-C :
    ∀{t n σ} →
    ((Ψ : List Ty) → ¬(Lookup n (Ψ , t) Δ)) →
    Check Δ Γ (U-CVar n σ) t
  Γ-type-mismatch :
    ∀{t n} →
    (u : Ty) →
    (Lookup n u Γ) →
    ¬(u ≡ t) →
    Check Δ Γ (U-Var n) t

mutual
  untag-rename-All :
    ∀{xs} {Δ} {Γ Γ'} →
    (f : ∀{x} → x ∈ Γ → x ∈ Γ') →
    (g : ℕ → ℕ) →
    (∀{x : Ty} → (p : x ∈ Γ) → toℕ (f p) ≡ g (toℕ p)) →
    (tm : All (Tm Δ Γ) xs) →
    untag-All (rename-All f tm) ≡ rename-List g (untag-All tm)
  untag-rename-All f g prf All-nil = refl
  untag-rename-All f g prf (All-cons x xs)
    rewrite
      untag-rename f g prf x |
      untag-rename-All f g prf xs = refl

  untag-rename :
    ∀{A} {Δ} {Γ Γ'} →
    (f : ∀{x} → x ∈ Γ → x ∈ Γ') →
    (g : ℕ → ℕ) →
    (∀{x : Ty} → (p : x ∈ Γ) → toℕ (f p) ≡ g (toℕ p)) →
    (tm : Tm Δ Γ A) →
    untag (rename f tm) ≡ rename-U g (untag tm)
  untag-rename f g prf (Var x) = cong U-Var (prf x)
  untag-rename f g prf (CVar x σ) = cong (U-CVar (toℕ x)) (untag-rename-All f g prf σ)
  untag-rename f g prf (→I A tm) =
    cong
      (U-→I A)
      (untag-rename (ρ f) (ρ-U g) (λ{ here → refl; (there p) → cong suc (prf p) }) tm)
  untag-rename f g prf (→E tm tm₁)
    rewrite
      untag-rename f g prf tm |
      untag-rename f g prf tm₁ = refl
  untag-rename f g prf (■I tm) = refl
  untag-rename f g prf (■E tm tm₁)
    rewrite
      untag-rename f g prf tm |
      untag-rename f g prf tm₁ = refl

untag-rename-there :
  ∀{A B u Δ Γ} →
  (tm : Tm Δ Γ A) →
  untag tm ≡ u →
  untag (rename (there {_} {B}) tm) ≡ rename-U suc u
untag-rename-there (Var x) refl = refl
untag-rename-there (CVar x x₁) refl =
  cong (U-CVar (toℕ x)) (untag-rename-All there suc (λ p → refl) x₁)
untag-rename-there (→I A tm) refl =
  cong
    (U-→I A)
    (untag-rename (ρ there) (ρ-U suc) (λ{ here → refl; (there p) → refl }) tm)
untag-rename-there {_} {B} (→E tm tm₁) refl
  rewrite
    untag-rename (there {_} {B}) suc (λ p → refl) tm₁ |
    untag-rename (there {_} {B}) suc (λ p → refl) tm
    = refl
untag-rename-there (■I tm) refl = refl
untag-rename-there {_} {B} (■E tm tm₁) refl
  rewrite
    untag-rename (there {_} {B}) suc (λ p → refl) tm |
    untag-rename (there {_} {B}) suc (λ p → refl) tm₁
    = refl

weaken-Check : ∀{Γ u ty A} → Check [] Γ u ty → Check [] (A ∷ Γ) (rename-U suc u) ty
weaken-Check (yes tm x) =
  yes (rename there tm) (untag-rename-there tm x)
weaken-Check (not-in-scope ty-notin-Γ) =
  not-in-scope λ{ (there p) → ty-notin-Γ p }
weaken-Check (not-in-scope-C ty-notin-Δ) =
  not-in-scope-C (λ Ψ ())
weaken-Check (Γ-type-mismatch u lookup-u u¬≡ty) =
  Γ-type-mismatch u (there lookup-u) u¬≡ty

eqTy : (t u : Ty) → t ≡ u ⊎ ¬(t ≡ u)
eqTy (Arr t t₁) (Arr u u₁) with eqTy t u
eqTy (Arr t t₁) (Arr .t u₁) | inj₁ refl with eqTy t₁ u₁
eqTy (Arr t t₁) (Arr .t .t₁) | inj₁ refl | inj₁ refl = inj₁ refl
eqTy (Arr t t₁) (Arr .t u₁) | inj₁ refl | inj₂ contra = inj₂ λ{ refl → contra refl }
eqTy (Arr t t₁) (Arr u u₁) | inj₂ contra = inj₂ λ{ refl → contra refl }
eqTy (Arr t t₁) (Box u u₁) = inj₂ (λ ())
eqTy (Box t t₁) (Arr u u₁) = inj₂ (λ ())
eqTy (Box [] t₁) (Box [] u₁) with eqTy t₁ u₁
eqTy (Box [] t₁) (Box [] .t₁) | inj₁ refl = inj₁ refl
eqTy (Box [] t₁) (Box [] u₁) | inj₂ contra = inj₂ λ{ refl → contra refl }
eqTy (Box [] t₁) (Box (x ∷ u) u₁) = inj₂ (λ ())
eqTy (Box (x ∷ t) t₁) (Box [] u₁) = inj₂ (λ ())
eqTy (Box (x ∷ t) t₁) (Box (x₁ ∷ u) u₁) with eqTy x x₁
eqTy (Box (x ∷ t) t₁) (Box (x₁ ∷ u) u₁) | inj₂ contra = inj₂ λ{ refl → contra refl }
eqTy (Box (x ∷ t) t₁) (Box (x₁ ∷ u) u₁) | inj₁ refl with eqTy (Box t t₁) (Box u u₁)
eqTy (Box (x ∷ t) t₁) (Box (x ∷ u) u₁) | inj₁ refl | inj₁ refl = inj₁ refl
eqTy (Box (x ∷ t) t₁) (Box (x ∷ u) u₁) | inj₁ refl | inj₂ contra =
  inj₂ λ{ refl → contra refl }

check : (Δ : List (List Ty × Ty)) → (Γ : List Ty) → (u : U) → (t : Ty) → Check Δ Γ u t
check Δ Γ (U-→I x u) t = {!!}
check Δ Γ (U-→E u u₁) t = {!!}
check Δ Γ (U-■I u) t = {!!}
check Δ Γ (U-■E u u₁) t = {!!}
check Δ Γ (U-CVar a σ) t = {!!}
check Δ [] (U-Var a) t = not-in-scope λ ()
check Δ (x ∷ xs) (U-Var a) t = {!!}
