{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Unit
open import Data.Product

infixl 2 _,,_

mutual

  data Ctx : Set where
    ∅ : Ctx
    _,,_  : (Γ : Ctx) → (⟦ Γ ⟧ → Type) → Ctx

  postulate Type : Set
  ⟦_⟧  : Ctx → Set
  postulate ⟦_⟧ₜ : Type → Set

  ⟦ ∅ ⟧ = ⊤
  ⟦ Γ ,, T ⟧ = Σ[ γ ∈ ⟦ Γ ⟧ ] ⟦ T γ ⟧ₜ

data Var (Γ : Ctx) (T : ⟦ Γ ⟧ → Type) : Ctx → Set where
  zero : Var Γ T (Γ ,, T)
  suc  : ∀ {Δ S} → Var Γ T Δ → Var Γ T (Δ ,, S)

π : ∀ {Γ} {T} {Δ} → Var Γ T Δ → ⟦ Δ ⟧ → ⟦ Γ ,, T ⟧
π zero    γ = γ
π (suc i) γ = π i (proj₁ γ)

⟦_⟧ᵥ : ∀ {Γ} {T} {Δ} → (v : Var Γ T Δ) → (δ : ⟦ Δ ⟧) → ⟦ T (proj₁ (π v δ)) ⟧ₜ
⟦ v ⟧ᵥ δ = proj₂ (π v δ)

pb : {Γ Δ : Ctx} (f : ⟦ Γ ⟧ → ⟦ Δ ⟧) → Σ[ Ξ ∈ Ctx ] (⟦ Ξ ⟧ → ⟦ Γ ⟧)
pb {Γ} {∅} _ = Γ , λ γ → γ
pb {Γ} {Δ ,, T} f =
  (proj₁ p ,, (λ ξ → T (proj₁ (f (proj₂ p ξ))))) , λ ξ → proj₂ p (proj₁ ξ)
  where
  p : _
  p = pb (λ γ → proj₁ (f γ))
