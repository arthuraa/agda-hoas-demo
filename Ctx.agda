{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Unit
open import Data.Product

infixl 2 _,,_

data pair (A : Set) (B : A → Set) : Set where
  _,,_ : (a : A) → B a → pair A B

π₁ : {A : Set} {B : A → Set} → pair A B → A
π₁ (γ ,, _) = γ

π₂ : {A : Set} {B : A → Set} (p : pair A B) → B (π₁ p)
π₂ (_ ,, a) = a

mutual

  data Ctx : Set where
    ∅ : Ctx
    _,,_  : (Γ : Ctx) → (⟦ Γ ⟧ → Type) → Ctx

  postulate Type : Set
  ⟦_⟧  : Ctx → Set
  postulate ⟦_⟧ₜ : Type → Set

  ⟦ ∅ ⟧ = ⊤
  ⟦ Γ ,, T ⟧ = pair ⟦ Γ ⟧ λ γ → ⟦ T γ ⟧ₜ

data Var (Γ : Ctx) (T : ⟦ Γ ⟧ → Type) : Ctx → Set where
  zero : Var Γ T (Γ ,, T)
  suc  : ∀ {Δ S} → Var Γ T Δ → Var Γ T (Δ ,, S)

π : ∀ {Γ} {T} {Δ} → Var Γ T Δ → ⟦ Δ ⟧ → ⟦ Γ ⟧
π zero    (γ ,, x) = γ
π (suc i) (γ ,, x) = π i γ

⟦_⟧ᵥ : ∀ {Γ} {T} {Δ} → (v : Var Γ T Δ) → (δ : ⟦ Δ ⟧) → ⟦ T (π v δ) ⟧ₜ
⟦ v ⟧ᵥ γ = go _ γ v
  where
  go : ∀ {Γ} {T} Δ → (δ : ⟦ Δ ⟧) → (v : Var Γ T Δ) → ⟦ T (π v δ) ⟧ₜ
  go ∅ _ ()
  go (Δ ,, S) (δ ,, x) zero    = x
  go (Δ ,, S) (δ ,, x) (suc v) = go Δ δ v

pb : {Γ Δ : Ctx} (f : ⟦ Γ ⟧ → ⟦ Δ ⟧) → Σ[ Ξ ∈ Ctx ] (⟦ Ξ ⟧ → ⟦ Γ ⟧)
pb {Γ} {∅} _ = Γ , λ γ → γ
pb {Γ} {Δ ,, T} f =
  (proj₁ p ,, (λ ξ → T (π₁ (f (proj₂ p ξ))))) , λ ξ → proj₂ p (π₁ ξ)
  where
  p : _
  p = pb (λ γ → π₁ (f γ))
