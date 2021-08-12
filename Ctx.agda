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
