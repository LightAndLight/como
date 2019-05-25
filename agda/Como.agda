module Como where

open import Function using (_∘_)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤)
open import Data.List using (List; _∷_; []; _++_; zip; boolFilter; any)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

data Ty : Set where
  Arr : Ty → Ty → Ty
  Box : List Ty → Ty → Ty
  Nat : Ty

data Not-Arrow : Ty → Set where
  ■-Not-Arrow : ∀{A B} → Not-Arrow (Box A B)
  Nat-Not-Arrow : Not-Arrow Nat

Not-Arrow-correct : ∀{a} → Not-Arrow a → (x y : Ty) → ¬(a ≡ Arr x y)
Not-Arrow-correct ■-Not-Arrow x y ()
Not-Arrow-correct Nat-Not-Arrow x y ()

data Not-Box : Ty → Set where
  →-Not-Box : ∀{A B} → Not-Box (Arr A B)
  Nat-Not-Box : Not-Box Nat

Not-Box-correct : ∀{a} → Not-Box a → (x : List Ty) → (y : Ty) → ¬(a ≡ Box x y)
Not-Box-correct →-Not-Box x y ()
Not-Box-correct Nat-Not-Box x y ()

data Not-Nat : Ty → Set where
  →-Not-Nat : ∀{A B} → Not-Nat (Arr A B)
  Box-Not-Nat : ∀{A B} → Not-Nat (Box A B)

Not-Nat-correct : ∀{a} → Not-Nat a → (x : List Ty) → (y : Ty) → ¬(a ≡ Nat)
Not-Nat-correct →-Not-Nat x y ()
Not-Nat-correct Box-Not-Nat x y ()

isYes : ∀{P : Set} → Dec P → Bool
isYes (yes _) = true
isYes (no _) = false

eqTy : (t u : Ty) → Dec (t ≡ u)
eqTy (Arr t t₁) Nat = no (λ ())
eqTy (Arr t t₁) (Arr u u₁) with eqTy t u
eqTy (Arr t t₁) (Arr .t u₁) | yes refl with eqTy t₁ u₁
eqTy (Arr t t₁) (Arr .t .t₁) | yes refl | yes refl = yes refl
eqTy (Arr t t₁) (Arr .t u₁) | yes refl | no contra = no λ{ refl → contra refl }
eqTy (Arr t t₁) (Arr u u₁) | no contra = no λ{ refl → contra refl }
eqTy (Arr t t₁) (Box u u₁) = no (λ ())
eqTy (Box t t₁) Nat = no (λ ())
eqTy (Box t t₁) (Arr u u₁) = no (λ ())
eqTy (Box [] t₁) (Box [] u₁) with eqTy t₁ u₁
eqTy (Box [] t₁) (Box [] .t₁) | yes refl = yes refl
eqTy (Box [] t₁) (Box [] u₁) | no contra = no λ{ refl → contra refl }
eqTy (Box [] t₁) (Box (x ∷ u) u₁) = no (λ ())
eqTy (Box (x ∷ t) t₁) (Box [] u₁) = no (λ ())
eqTy (Box (x ∷ t) t₁) (Box (x₁ ∷ u) u₁) with eqTy x x₁
eqTy (Box (x ∷ t) t₁) (Box (x₁ ∷ u) u₁) | no contra = no λ{ refl → contra refl }
eqTy (Box (x ∷ t) t₁) (Box (x₁ ∷ u) u₁) | yes refl with eqTy (Box t t₁) (Box u u₁)
eqTy (Box (x ∷ t) t₁) (Box (x ∷ u) u₁) | yes refl | yes refl = yes refl
eqTy (Box (x ∷ t) t₁) (Box (x ∷ u) u₁) | yes refl | no contra =
  no λ{ refl → contra refl }
eqTy Nat Nat = yes refl
eqTy Nat (Box _ _) = no (λ ())
eqTy Nat (Arr _ _) = no (λ ())

infix 3 _∈_
data _∈_ {A : Set} : A → List A → Set where
  here : ∀{x xs} → x ∈ x ∷ xs
  there : ∀{y x xs} → x ∈ xs → x ∈ y ∷ xs

infix 3 _⊆_
data _⊆_ {A : Set} : List A → List A → Set where
  ⊆-nil : ∀{xs} → [] ⊆ xs
  ⊆-cons-r : ∀{x ys xs} → ys ⊆ xs → ys ⊆ x ∷ xs
  ⊆-cons-both : ∀{ys xs} → (x : A) → ys ⊆ xs → x ∷ ys ⊆ x ∷ xs

data Lookup {A : Set} : ℕ → A → List A → Set where
  here : ∀{x xs} → Lookup zero x (x ∷ xs)
  there : ∀{n x y xs} → Lookup n x xs → Lookup (suc n) x (y ∷ xs)

decLookup : ∀{A : Set} → (n : ℕ) → (xs : List A) → Dec (∃[ x ]( Lookup n x xs))
decLookup n [] = no (λ{ (x , ()) })
decLookup zero (x ∷ xs) = yes (x , here)
decLookup (suc n) (x ∷ xs) with decLookup n xs
... | yes (a , prf) = yes (a , there prf)
... | no contra = no (λ{ (a , there p) → contra (a , p) })

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

data Tm (Δ : List (List Ty × Ty)) (Γ : List Ty) : Ty → Set where
  Var : ∀{A} → A ∈ Γ → Tm Δ Γ A
  CVar : ∀{Ψ A} → (Ψ , A) ∈ Δ → All (Tm Δ Γ) Ψ → Tm Δ Γ A

  →I : ∀{B} → (A : Ty) → Tm Δ (A ∷ Γ) B → Tm Δ Γ (Arr A B)
  →E : ∀{A B} → Tm Δ Γ (Arr A B) → Tm Δ Γ A → Tm Δ Γ B

  ■I : ∀{A} → (Ψ : List Ty) → Tm Δ Ψ A → Tm Δ Γ (Box Ψ A)
  ■E : ∀{A B Ψ} → Tm Δ Γ (Box Ψ A) → Tm ((Ψ , A) ∷ Δ) Γ B → Tm Δ Γ B

  ■sub : ∀{X A Ψ} → Tm Δ Γ (Box (X ∷ Ψ) A) → Tm Δ [] X → Tm Δ Γ (Box Ψ A)

  NatI-zero : Tm Δ Γ Nat
  NatI-suc : Tm Δ Γ Nat → Tm Δ Γ Nat
  NatE : ∀{A} → Tm Δ Γ A → Tm Δ Γ (Arr Nat A) → Tm Δ Γ Nat → Tm Δ Γ A

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
  rename f (■I Ψ a) = ■I Ψ a
  rename f (■E a a₁) = ■E (rename f a) (rename f a₁)
  rename f (■sub a b) = ■sub (rename f a) b
  rename f NatI-zero = NatI-zero
  rename f (NatI-suc n) = NatI-suc (rename f n)
  rename f (NatE z s n) = NatE (rename f z) (rename f s) (rename f n)

mutual
  rename-C-All : ∀{Δ Δ'} → (∀{A} → A ∈ Δ → A ∈ Δ') → ∀{Γ Ψ} → All (Tm Δ Γ) Ψ → All (Tm Δ' Γ) Ψ
  rename-C-All f All-nil = All-nil
  rename-C-All f (All-cons x₁ a) = All-cons (rename-C f x₁) (rename-C-All f a)

  rename-C : ∀{Δ Δ'} → (∀{A} → A ∈ Δ → A ∈ Δ') → ∀{A Γ} → Tm Δ Γ A → Tm Δ' Γ A
  rename-C f (Var x) = Var x
  rename-C f (CVar x prf) = CVar (f x) (rename-C-All f prf)
  rename-C f (→I ty a) = →I ty (rename-C f a)
  rename-C f (→E a a₁) = →E (rename-C f a) (rename-C f a₁)
  rename-C f (■I Ψ a) = ■I Ψ (rename-C f a)
  rename-C f (■E a a₁) = ■E (rename-C f a) (rename-C (ρ f) a₁)
  rename-C f (■sub a b) = ■sub (rename-C f a) (rename-C f b)
  rename-C f NatI-zero = NatI-zero
  rename-C f (NatI-suc n) = NatI-suc (rename-C f n)
  rename-C f (NatE z s n) = NatE (rename-C f z) (rename-C f s) (rename-C f n)

context-identity : ∀{Δ Ψ} → All (Tm Δ Ψ) Ψ
context-identity {Δ} {[]} = All-nil
context-identity {Δ} {x ∷ xs} = All-cons (Var here) (rename-All there context-identity)

σ-C :
  ∀{Δ Δ'} →
  (∀{Ψ A} → (Ψ , A) ∈ Δ → Tm Δ' Ψ A) →
  ∀{Ψ A B} → (Ψ , A) ∈ B ∷ Δ → Tm (B ∷ Δ') Ψ A
σ-C f here = CVar here context-identity
σ-C f (there a) = rename-C there (f a)

alls :
  ∀{Γ Δ Ψ} →
  All (Tm Δ Γ) Ψ →
  (∀{A} → A ∈ Ψ → Tm Δ Γ A)
alls All-nil ()
alls (All-cons x a) here = x
alls (All-cons x a) (there prf) = alls a prf

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
  subst f (■I Ψ a) = ■I Ψ a
  subst f (■E a a₁) = ■E (subst f a) (subst (rename-C there ∘ f) a₁)
  subst f (■sub a b) = ■sub (subst f a) b
  subst f NatI-zero = NatI-zero
  subst f (NatI-suc n) = NatI-suc (subst f n)
  subst f (NatE z s n) = NatE (subst f z) (subst f s) (subst f n)

mutual
  subst-C-All :
    ∀{Γ Δ Δ'} →
    (∀{Ψ A} → (Ψ , A) ∈ Δ → Tm Δ' Ψ A) →
    ∀{Ψ} → All (Tm Δ Γ) Ψ → All (Tm Δ' Γ) Ψ
  subst-C-All f All-nil = All-nil
  subst-C-All f (All-cons x₁ a) = All-cons (subst-C f x₁) (subst-C-All f a)

  subst-C : ∀{Γ Δ Δ'} → (∀{Ψ A} → (Ψ , A) ∈ Δ → Tm Δ' Ψ A) → ∀{A} → Tm Δ Γ A → Tm Δ' Γ A
  subst-C f (Var x) = Var x
  subst-C f (CVar x prf) = subst (alls (subst-C-All f prf)) (f x)
  subst-C f (→I ty a) = →I ty (subst-C f a)
  subst-C f (→E a a₁) = →E (subst-C f a) (subst-C f a₁)
  subst-C f (■I Ψ a) = ■I Ψ (subst-C f a)
  subst-C f (■E a a₁) = ■E (subst-C f a) (subst-C (σ-C f) a₁)
  subst-C f (■sub a b) = ■sub (subst-C f a) (subst-C f b)
  subst-C f NatI-zero = NatI-zero
  subst-C f (NatI-suc n) = NatI-suc (subst-C f n)
  subst-C f (NatE z s n) = NatE (subst-C f z) (subst-C f s) (subst-C f n)

data Value {Δ} {Γ} : ∀{A} → Tm Δ Γ A → Set where
  v-→I : ∀{B} → (A : Ty) → (a : Tm Δ (A ∷ Γ) B) → Value (→I A a)
  v-■I : ∀{A Ψ} {a : Tm Δ Ψ A} → Value (■I Ψ a)
  v-NatI-zero : Value NatI-zero
  v-NatI-suc : ∀{n} → Value n → Value (NatI-suc n)

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
  ↓-■sub₁ :
    ∀{A X Ψ} {a a' : Tm Δ Γ (Box (X ∷ Ψ) A)} {b} →
    a ↓ a' →
    ■sub a b ↓ ■sub a' b
  ↓-■sub₂ :
    ∀{A X Ψ} {a : Tm Δ Γ (Box (X ∷ Ψ) A)} {b b'} →
    Value a →
    b ↓ b' →
    ■sub a b ↓ ■sub a b'
  ↓-■sub :
    ∀{A X Ψ} {a : Tm Δ (X ∷ Ψ) A} {b} →
    Value b →
    ■sub (■I (X ∷ Ψ) a) b ↓ ■I Ψ (subst (λ{ here → rename (λ ()) b; (there p) → Var p }) a)
  ↓-unbox :
    ∀{A B Ψ} {a} {b : Tm ((Ψ , A) ∷ Δ) Γ B} →
    ■E (■I Ψ a) b ↓ subst-C (λ { here → a; (there p) → CVar p context-identity }) b
  ↓-NatI-suc : ∀{n n'} → n ↓ n' → NatI-suc n ↓ NatI-suc n'

  ↓-NatE₁ : ∀{A} {z z' : Tm Δ Γ A} {s n} → z ↓ z' → NatE z s n ↓ NatE z' s n
  ↓-NatE₂ : ∀{A} {z : Tm Δ Γ A} {s s' n} → Value z → s ↓ s' → NatE z s n ↓ NatE z s' n
  ↓-NatE₃ : ∀{A} {z : Tm Δ Γ A} {s n n'} → Value z → Value s → n ↓ n' → NatE z s n ↓ NatE z s n'
  ↓-NatE-zero : ∀{A} {z : Tm Δ Γ A} {s} → NatE z s NatI-zero ↓ z
  ↓-NatE-suc :
    ∀{A} {z : Tm Δ Γ A} {s n} →
    NatE z s (NatI-suc n) ↓ →E s n

value-¬↓ : ∀{Δ Γ A} {tm : Tm Δ Γ A} → (v : Value tm) → ¬( ∃[ tm' ]( tm ↓ tm' ))
value-¬↓ (v-→I _ _) (tm' , ())
value-¬↓ v-■I (tm' , ())
value-¬↓ v-NatI-zero (tm' , ())
value-¬↓ (v-NatI-suc v) (NatI-suc n , ↓-NatI-suc n↓n') = value-¬↓ v (n , n↓n')

progress : ∀{A} → (tm : Tm [] [] A) → Value tm ⊎ (∃[ tm' ](tm ↓ tm'))
progress (Var ())
progress (CVar () _)
progress (→I ty tm) = inj₁ (v-→I ty tm)
progress (→E a b) with progress a
progress (→E a b) | inj₂ (a' , a↓a') = inj₂ (→E a' b , ↓-→E₁ a↓a')
progress (→E a b) | inj₁ va with progress b
progress (→E a b) | inj₁ va | inj₂ (b' , b↓b') = inj₂ (→E a b' , ↓-→E₂ va b↓b')
progress (→E (→I ty e) b) | inj₁ (v-→I .ty .e) | inj₁ vb = inj₂ (_ , ↓-β vb)
progress (■I Ψ tm) = inj₁ v-■I
progress (■E tm tm₁) with progress tm
progress (■E tm tm₁) | inj₂ (tm' , tm↓tm') = inj₂ (■E tm' tm₁ , ↓-■E₁ tm↓tm')
progress (■E (■I Ψ a) tm₁) | inj₁ v-■I = inj₂ (_ , ↓-unbox)
progress (■sub a b) with progress a
progress (■sub a b) | inj₁ va with progress b
progress (■sub (■I (X ∷ Ψ) a) b) | inj₁ v-■I | inj₁ vb = inj₂ (_ , ↓-■sub vb)
progress (■sub a b) | inj₁ va | inj₂ (b' , b↓b') = inj₂ (■sub a b' , ↓-■sub₂ va b↓b')
progress (■sub a b) | inj₂ (a' , a↓a') = inj₂ (■sub a' b , ↓-■sub₁ a↓a')
progress NatI-zero = inj₁ v-NatI-zero
progress (NatI-suc n) with progress n
progress (NatI-suc n) | inj₁ vn = inj₁ (v-NatI-suc vn)
progress (NatI-suc n) | inj₂ (n' , n↓n') = inj₂ (NatI-suc n' , ↓-NatI-suc n↓n')
progress (NatE z s n) with progress z
progress (NatE z s n) | inj₂ (z' , z↓z') = inj₂ (NatE z' s n , ↓-NatE₁ z↓z')
progress (NatE z s n) | inj₁ vz with progress s
progress (NatE z s n) | inj₁ vz | inj₂ (s' , s↓s') = inj₂ (NatE z s' n , ↓-NatE₂ vz s↓s')
progress (NatE z s n) | inj₁ vz | inj₁ vs with progress n
progress (NatE z s n) | inj₁ vz | inj₁ vs | inj₂ (n' , n↓n') =
  inj₂ (NatE z s n' , ↓-NatE₃ vz vs n↓n')
progress (NatE z s .NatI-zero) | inj₁ vz | inj₁ vs | inj₁ v-NatI-zero = inj₂ (z , ↓-NatE-zero)
progress (NatE z s (NatI-suc n)) | inj₁ vz | inj₁ vs | inj₁ (v-NatI-suc vn) =
  inj₂ (→E s n , ↓-NatE-suc)

data U : Set where
  U-Var : ℕ → U
  U-CVar : ℕ → List U → U

  U-→I : Ty → U → U
  U-→E : U → U → U

  U-■I : List Ty → U → U
  U-■E : U → U → U
  U-■sub : U → U → U

  U-NatI-zero : U
  U-NatI-suc : U → U
  U-NatE : U → U → U → U

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
  rename-U f (U-■I Ψ a) = U-■I Ψ a
  rename-U f (U-■E a b) = U-■E (rename-U f a) (rename-U f b)
  rename-U f (U-■sub a b) = U-■sub (rename-U f a) b
  rename-U f U-NatI-zero = U-NatI-zero
  rename-U f (U-NatI-suc n) = U-NatI-suc (rename-U f n)
  rename-U f (U-NatE z s n) = U-NatE (rename-U f z) (rename-U f s) (rename-U f n)

mutual
  untag-All : ∀{Δ Γ xs} → All (Tm Δ Γ) xs → List U
  untag-All All-nil = []
  untag-All (All-cons x xs) = untag x ∷ untag-All xs

  untag : ∀{Δ Γ ty} → Tm Δ Γ ty → U
  untag (Var x) = U-Var (toℕ x)
  untag (CVar x y) = U-CVar (toℕ x) (untag-All y)
  untag (→I A t) = U-→I A (untag t)
  untag (→E t u) = U-→E (untag t) (untag u)
  untag (■I Ψ t) = U-■I Ψ (untag t)
  untag (■E t u) = U-■E (untag t) (untag u)
  untag (■sub a b) = U-■sub (untag a) (untag b)
  untag NatI-zero = U-NatI-zero
  untag (NatI-suc n) = U-NatI-suc (untag n)
  untag (NatE z s n) = U-NatE (untag z) (untag s) (untag n)

data _<_ {A B : Set} : List A → List B → Set where
  nil-< : ∀{x xs} → [] < (x ∷ xs)
  cons-< : ∀{x xs y ys} → xs < ys → (x ∷ xs) < (y ∷ ys)

mutual
  data CheckError (Δ : List (List Ty × Ty)) (Γ : List Ty) : U → Ty → Set where
    infer-error :
      ∀{u t} →
      InferError Δ Γ u →
      CheckError Δ Γ u t
    type-mismatch :
      ∀{t} →
      (t' : Ty) →
      (tm : Tm Δ Γ t') →
      ¬(t ≡ t') →
      CheckError Δ Γ (untag tm) t

  data InferError (Δ : List (List Ty × Ty)) (Γ : List Ty) : U → Set where
    not-in-scope :
      ∀{n} →
      ¬(Σ[ t ∈ Ty ](Lookup n t Γ)) →
      InferError Δ Γ (U-Var n)
    not-in-scope-C :
      ∀{n σ} →
      ¬(Σ[ t ∈ List Ty × Ty ](Lookup n t Δ)) →
      InferError Δ Γ (U-CVar n σ)
    →I-body-error :
      ∀{x b} →
      InferError Δ (x ∷ Γ) b →
      InferError Δ Γ (U-→I x b)
    →E-left-error :
      ∀{f x} →
      InferError Δ Γ f →
      InferError Δ Γ (U-→E f x)
    →E-right-error :
      ∀{f x t} →
      CheckError Δ Γ x t →
      InferError Δ Γ (U-→E f x)
    ■I-error :
      ∀{Ψ x} →
      InferError Δ Ψ x →
      InferError Δ Γ (U-■I Ψ x)
    ■E-left-error :
      ∀{x y} →
      InferError Δ Γ x →
      InferError Δ Γ (U-■E x y)
    ■E-right-error :
      ∀{a b x Ψ t} →
      InferError ((Ψ , t) ∷ Δ) Γ x →
      InferError Δ Γ (U-■E a b)
    ■sub-left-error :
      ∀{x y} →
      InferError Δ Γ x →
      InferError Δ Γ (U-■sub x y)
    ■sub-right-error :
      ∀{x y} →
      (Y : Ty) →
      CheckError Δ [] y Y →
      InferError Δ Γ (U-■sub x y)
    ■sub-empty-ctx :
      ∀{y A} →
      (tm : Tm Δ Γ (Box [] A)) →
      InferError Δ Γ (U-■sub (untag tm) y)
    NatI-suc-error :
      ∀{n} →
      CheckError Δ Γ n Nat →
      InferError Δ Γ (U-NatI-suc n)
    NatE-1-error :
      ∀{z s n} →
      InferError Δ Γ z →
      InferError Δ Γ (U-NatE z s n)
    NatE-2-error :
      ∀{A z s n} →
      CheckError Δ Γ s (Arr Nat A)→
      InferError Δ Γ (U-NatE z s n)
    NatE-3-error :
      ∀{z s n} →
      CheckError Δ Γ n Nat →
      InferError Δ Γ (U-NatE z s n)
    expected-function :
      ∀{t x} →
      (tm : Tm Δ Γ t) →
      Not-Arrow t →
      InferError Δ Γ (U-→E (untag tm) x)
    expected-box :
      ∀{t x} →
      (tm : Tm Δ Γ t) →
      Not-Box t →
      InferError Δ Γ (U-■E (untag tm) x)
    expected-box-sub :
      ∀{t x} →
      (tm : Tm Δ Γ t) →
      Not-Box t →
      InferError Δ Γ (U-■sub (untag tm) x)
    type-error-σ :
      ∀{n Ψ t σ} →
      Lookup n (Ψ , t) Δ →
      CheckError-σ Δ Γ σ Ψ →
      InferError Δ Γ (U-CVar n σ)

  data CheckError-σ (Δ : List (List Ty × Ty)) (Γ : List Ty) : List U → List Ty → Set where
    too-few-terms : ∀{us ts} → us < ts → CheckError-σ Δ Γ us ts
    too-many-terms : ∀{us ts} → ts < us → CheckError-σ Δ Γ us ts
    type-errors :
      ∀{us us' ts ts'} →
      us ⊆ us' →
      ts ⊆ ts' →
      All (λ{ (u , t) → CheckError Δ Γ u t}) (zip us ts) →
      CheckError-σ Δ Γ us' ts'

data Check-σ (Δ : List (List Ty × Ty)) (Γ : List Ty) : List U → List Ty → Set where
  yes-σ : ∀{us ts} → (xs : All (Tm Δ Γ) ts) → untag-All xs ≡ us → Check-σ Δ Γ us ts
  no-σ : ∀{us ts} → CheckError-σ Δ Γ us ts → Check-σ Δ Γ us ts

data Check (Δ : List (List Ty × Ty)) (Γ : List Ty) : U → Ty → Set where
  yes : ∀{u ty} → (tm : Tm Δ Γ ty) → untag tm ≡ u → Check Δ Γ u ty
  no : ∀{u t} → CheckError Δ Γ u t → Check Δ Γ u t

data Infer (Δ : List (List Ty × Ty)) (Γ : List Ty) : U → Set where
  yes : ∀{u} → (ty : Ty) → (tm : Tm Δ Γ ty) → untag tm ≡ u → Infer Δ Γ u
  no : ∀{u} → InferError Δ Γ u → Infer Δ Γ u

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
  untag-rename f g prf (■I Ψ tm) = refl
  untag-rename f g prf (■E tm tm₁)
    rewrite
      untag-rename f g prf tm |
      untag-rename f g prf tm₁ = refl
  untag-rename f g prf (■sub tm tm₁) rewrite untag-rename f g prf tm = refl
  untag-rename f g x NatI-zero = refl
  untag-rename f g x (NatI-suc n) = cong U-NatI-suc (untag-rename f g x n)
  untag-rename f g x (NatE z s n)
    rewrite
      untag-rename f g x z |
      untag-rename f g x s |
      untag-rename f g x n
      = refl

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
untag-rename-there (■I Ψ tm) refl = refl
untag-rename-there {_} {B} (■E tm tm₁) refl
  rewrite
    untag-rename (there {_} {B}) suc (λ p → refl) tm |
    untag-rename (there {_} {B}) suc (λ p → refl) tm₁
    = refl
untag-rename-there {_} {B} (■sub tm tm₁) refl
  rewrite
    untag-rename (there {_} {B}) suc (λ p → refl) tm |
    untag-rename (there {_} {B}) suc (λ p → refl) tm₁
    = refl
untag-rename-there NatI-zero refl = refl
untag-rename-there (NatI-suc n) refl = cong U-NatI-suc (untag-rename-there n refl)
untag-rename-there {_} {B} (NatE z s n) refl
  rewrite
    untag-rename (there {_} {B}) suc (λ p → refl) z |
    untag-rename (there {_} {B}) suc (λ p → refl) s |
    untag-rename (there {_} {B}) suc (λ p → refl) n
    = refl

Lookup-∈ : ∀{A : Set} {x : A} {n xs} → Lookup n x xs → x ∈ xs
Lookup-∈ here = here
Lookup-∈ (there p) = there (Lookup-∈ p)

toℕ-Lookup-∈ :
  ∀{A : Set} {a} {x : A} {xs} →
  (prf : Lookup a x xs) →
  toℕ (Lookup-∈ prf) ≡ a
toℕ-Lookup-∈ {_} {_} {_} {_} here = refl
toℕ-Lookup-∈ {_} {_} {_} {_} (there prf) = cong suc (toℕ-Lookup-∈ {_} {_} {_} {_} prf)

mutual
  check-σ :
    (Δ : List (List Ty × Ty)) →
    (Γ : List Ty) →
    (us : List U) →
    (ts : List Ty) →
    Check-σ Δ Γ us ts
  check-σ Δ Γ [] [] = yes-σ All-nil refl
  check-σ Δ Γ [] (x ∷ ts) = no-σ (too-few-terms nil-<)
  check-σ Δ Γ (x ∷ us) [] = no-σ (too-many-terms nil-<)
  check-σ Δ Γ (u ∷ us) (t ∷ ts) with check-σ Δ Γ us ts
  check-σ Δ Γ (u ∷ us) (t ∷ ts) | yes-σ tms refl with check Δ Γ u t
  ... | yes tm refl = yes-σ (All-cons tm tms) refl
  ... | no err =
    no-σ (type-errors (⊆-cons-both u ⊆-nil) (⊆-cons-both t ⊆-nil) (All-cons err All-nil))
  check-σ Δ Γ (u ∷ us) (t ∷ ts) | no-σ (too-few-terms x) = no-σ (too-few-terms (cons-< x))
  check-σ Δ Γ (u ∷ us) (t ∷ ts) | no-σ (too-many-terms x) = no-σ (too-many-terms (cons-< x))
  check-σ Δ Γ (u ∷ us) (t ∷ ts) | no-σ (type-errors ⊆1 ⊆2 errs) with check Δ Γ u t
  ... | yes _ _ = no-σ (type-errors (⊆-cons-r ⊆1) (⊆-cons-r ⊆2) errs)
  ... | no err = no-σ (type-errors (⊆-cons-both u ⊆1) (⊆-cons-both t ⊆2) (All-cons err errs))

  check : (Δ : List (List Ty × Ty)) → (Γ : List Ty) → (u : U) → (t : Ty) → Check Δ Γ u t
  check Δ Γ tm ty with infer Δ Γ tm
  check Δ Γ tm ty | yes ty' tm' refl with eqTy ty ty'
  check Δ Γ _ ty | yes ty' tm' refl | yes refl = yes tm' refl
  check Δ Γ _ ty | yes ty' tm' refl | no contra = no (type-mismatch ty' tm' contra)
  check Δ Γ tm ty | no err = no (infer-error err)

  infer : (Δ : List (List Ty × Ty)) → (Γ : List Ty) → (u : U) → Infer Δ Γ u
  infer Δ Γ U-NatI-zero = yes Nat NatI-zero refl
  infer Δ Γ (U-NatI-suc n) with check Δ Γ n Nat
  infer Δ Γ (U-NatI-suc n) | yes tm refl = yes Nat (NatI-suc tm) refl
  infer Δ Γ (U-NatI-suc n) | no err = no (NatI-suc-error err)
  infer Δ Γ (U-NatE z s n) with infer Δ Γ z
  infer Δ Γ (U-NatE z s n) | yes zTy z' refl with check Δ Γ s (Arr Nat zTy)
  infer Δ Γ (U-NatE .(untag z') s n) | yes zTy z' refl | yes s' refl with check Δ Γ n Nat
  infer Δ Γ (U-NatE .(untag z') .(untag s') n) | yes zTy z' refl | yes s' refl | yes n' refl =
    yes zTy (NatE z' s' n') refl
  infer Δ Γ (U-NatE .(untag z') .(untag s') n) | yes zTy z' refl | yes s' refl | no err =
    no (NatE-3-error err)
  infer Δ Γ (U-NatE .(untag z') s n) | yes zTy z' refl | no err = no (NatE-2-error err)
  infer Δ Γ (U-NatE z s n) | no err = no (NatE-1-error err)
  infer Δ Γ (U-Var n) with decLookup n Γ
  infer Δ Γ (U-Var n) | yes (t , prf) =
    yes t (Var (Lookup-∈ prf)) (cong U-Var (toℕ-Lookup-∈ prf))
  infer Δ Γ (U-Var n) | no contra = no (not-in-scope contra)
  infer Δ Γ (U-CVar n σ) with decLookup n Δ
  infer Δ Γ (U-CVar n σ) | yes ((Ψ , t) , prf) with check-σ Δ Γ σ Ψ
  infer Δ Γ (U-CVar n σ) | yes ((Ψ , t) , prf) | yes-σ tms refl =
    yes t (CVar (Lookup-∈ prf) tms) (cong (λ x → U-CVar x (untag-All tms)) (toℕ-Lookup-∈ prf))
  infer Δ Γ (U-CVar n σ) | yes ((Ψ , t) , prf) | no-σ x = no (type-error-σ prf x)
  infer Δ Γ (U-CVar n σ) | no contra = no (not-in-scope-C contra)
  infer Δ Γ (U-→I x u) with infer Δ (x ∷ Γ) u
  infer Δ Γ (U-→I x u) | yes ty tm refl = yes (Arr x ty) (→I x tm) refl
  infer Δ Γ (U-→I x u) | no err = no (→I-body-error err)
  infer Δ Γ (U-→E f x) with infer Δ Γ f
  infer Δ Γ (U-→E f x) | yes (Arr A B) tm refl with check Δ Γ x A
  infer Δ Γ (U-→E _ x) | yes (Arr A B) tm refl | yes x' refl = yes B (→E tm x') refl
  infer Δ Γ (U-→E _ x) | yes (Arr A B) tm refl | no err = no (→E-right-error err)
  infer Δ Γ (U-→E f x) | yes (Box _ _) tm refl = no (expected-function tm ■-Not-Arrow)
  infer Δ Γ (U-→E f x) | yes Nat tm refl = no (expected-function tm Nat-Not-Arrow)
  infer Δ Γ (U-→E f x) | no err = no (→E-left-error err)
  infer Δ Γ (U-■I Ψ u) with infer Δ Ψ u
  infer Δ Γ (U-■I Ψ u) | yes ty tm refl = yes (Box Ψ ty) (■I Ψ tm) refl
  infer Δ Γ (U-■I Ψ u) | no err = no (■I-error err)
  infer Δ Γ (U-■E a b) with infer Δ Γ a
  infer Δ Γ (U-■E .(untag tm) b) | yes (Box Ψ ty) tm refl with infer ((Ψ , ty) ∷ Δ) Γ b
  infer Δ Γ (U-■E .(untag tm) b) | yes (Box Ψ ty) tm refl | yes bty btm refl =
   yes bty (■E tm btm) refl
  infer Δ Γ (U-■E .(untag tm) b) | yes (Box Ψ ty) tm refl | no err = no (■E-right-error err)
  infer Δ Γ (U-■E .(untag tm) b) | yes (Arr _ _) tm refl = no (expected-box tm →-Not-Box)
  infer Δ Γ (U-■E .(untag tm) b) | yes Nat tm refl = no (expected-box tm Nat-Not-Box)
  infer Δ Γ (U-■E a b) | no err = no (■E-left-error err)
  infer Δ Γ (U-■sub a b) with infer Δ Γ a
  infer Δ Γ (U-■sub a b) | yes (Box [] ty) tm refl = no (■sub-empty-ctx tm)
  infer Δ Γ (U-■sub a b) | yes (Box (X ∷ Ψ) ty) tm refl with check Δ [] b X
  infer Δ Γ (U-■sub a b) | yes (Box (X ∷ Ψ) ty) tm refl | yes b' refl =
    yes (Box Ψ ty) (■sub tm b') refl
  infer Δ Γ (U-■sub a b) | yes (Box (X ∷ Ψ) ty) tm refl | no err = no (■sub-right-error X err)
  infer Δ Γ (U-■sub a b) | yes (Arr _ _) tm refl = no (expected-box-sub tm →-Not-Box)
  infer Δ Γ (U-■sub a b) | yes Nat tm refl = no (expected-box-sub tm Nat-Not-Box)
  infer Δ Γ (U-■sub a b) | no err = no (■sub-left-error err)

to : (A B : Ty) → Tm [] [] (Arr (Box (A ∷ []) B) (Arr A (Box [] B)))
to A B =
  →I (Box (A ∷ []) B)
  (→I A
  (■sub (Var (there here)) {!!}))

{-

given    y : Box [] B

⟨ λx. ~y ⟩ desugars to

let Box a = y in
let Box b = Box[y : B](λ(x : A). y) in
Box[]( b[a] )



{
or this?


let Box b = Box[y](λ(x : A). y) in
Box[]( let Box a = x in b[a] )

nah this isn't well-typed
}


-}
test : (A B : Ty) → Tm [] (Box [] B ∷ []) (Box [] (Arr A B))
test A B =
  ■E (Var here)
  (■E (■I (B ∷ []) (→I A (Var (there here))))
  (■I [] (CVar here (All-cons (CVar (there here) All-nil) All-nil))))

{-

given    f : Box [] (A -> B)

⟨ λ(x : A). ~f x ⟩ desugars to

let Box a = f in
let Box b = Box[f : A -> B](λ(x : A). f x) in
Box[]( b[a] )

-}

{-

given    f : Box [] (A -> B -> C),  x : Box [] A

⟨ ~f ~x ⟩ desugars to

let Box f' = f in
let Box x' = x in
let Box b = Box[f : A -> B -> C, x : A](f x) in
Box[]( b[f', x'] )

it has type Box[](B -> C)

-}
test2 : (A B C : Ty) → Tm [] (Box [] A ∷ Box [] (Arr A (Arr B C)) ∷ []) (Box [] (Arr B C))
test2 A B C =
  ■E (Var (there here))
  (■E (Var here)
  (■E (■I (Arr A (Arr B C) ∷ A ∷ []) (→E (Var here) (Var (there here))))
  (■I [] (CVar here (All-cons (CVar (there (there here)) All-nil) (All-cons (CVar (there here) All-nil) All-nil))))))
