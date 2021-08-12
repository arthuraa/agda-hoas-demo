{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Unit
open import Data.Product

infixl 2 _,,_

mutual

  data Ctx : Set₁ where
    ∅ : Ctx
    _,,_  : (Γ : Ctx) → (⟦ Γ ⟧ → Type) → Ctx

  postulate Type : Set₁
  ⟦_⟧  : Ctx → Set
  postulate ⟦_⟧ₜ : Type → Set₀

  ⟦ ∅ ⟧ = ⊤
  ⟦ Γ ,, T ⟧ = Σ[ γ ∈ ⟦ Γ ⟧ ] ⟦ T γ ⟧ₜ

data Var : (Γ : Ctx) (T : ⟦ Γ ⟧ → Type) → Set₁ where
  here : (Γ : Ctx) → (T : ⟦ Γ ⟧ → Type)  →
         Var (Γ ,, T) (λ γ → T (proj₁ γ))
  next : (Γ : Ctx) → (T S : ⟦ Γ ⟧ → Type) → Var Γ S →
         Var (Γ ,, T) (λ γ → S (proj₁ γ))

⟦_⟧ᵥ : {Γ : Ctx} {T : ⟦ Γ ⟧ → Type} → (v : Var Γ T) → (γ : ⟦ Γ ⟧) → ⟦ T γ ⟧ₜ
⟦ here Γ T ⟧ᵥ γ = proj₂ γ
⟦ next Γ T S v ⟧ᵥ γ = ⟦ v ⟧ᵥ (proj₁ γ)

pb : {Γ Δ : Ctx} (f : ⟦ Γ ⟧ → ⟦ Δ ⟧) → Σ[ Ξ ∈ Ctx ] (⟦ Ξ ⟧ → ⟦ Γ ⟧)
pb {Γ} {∅} _ = Γ , λ γ → γ
pb {Γ} {Δ ,, T} f =
  (proj₁ p ,, (λ ξ → T (proj₁ (f (proj₂ p ξ))))) , λ ξ → proj₂ p (proj₁ ξ)
  where
  p : _
  p = pb (λ γ → proj₁ (f γ))
