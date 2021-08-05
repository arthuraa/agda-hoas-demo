{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Unit
open import Data.Product

infixl 2 _`,_

mutual

  data Ctx : Set₁ where
    ∅ : Ctx
    _`,_  : (Γ : Ctx) → Type Γ → Ctx

  postulate Type : Ctx → Set₁
  ⟦_⟧ : Ctx → Set
  postulate ⟦_⟧ₜ : {Γ : Ctx} → Type Γ → ⟦ Γ ⟧ → Set

  ⟦ ∅ ⟧ = ⊤
  ⟦ Γ `, T ⟧ = Σ[ γ ∈ ⟦ Γ ⟧ ] ⟦ T ⟧ₜ γ

postulate weak : (Γ : Ctx) → (T S : Type Γ) → Type (Γ `, T)
postulate ⟦weak⟧ : ∀ (Γ : Ctx) (T S : Type Γ) (γ : ⟦ Γ `, T ⟧) →
                   ⟦ weak Γ T S ⟧ₜ γ ≡ ⟦ S ⟧ₜ (proj₁ γ)
{-# REWRITE ⟦weak⟧ #-}

data Var : (Γ : Ctx) (T : ⟦ Γ ⟧ → Set) → Set₁ where
  here : (Γ : Ctx) → (T : Type Γ) → Var (Γ `, T) (λ γ → ⟦ T ⟧ₜ (proj₁ γ))
  next : (Γ : Ctx) → (T : Type Γ) (S : ⟦ Γ ⟧ → Set) → Var Γ S →
         Var (Γ `, T) (λ γ → S (proj₁ γ))

⟦_⟧ᵥ : {Γ : Ctx} {T : ⟦ Γ ⟧ → Set} →
       (v : Var Γ T) → (γ : ⟦ Γ ⟧) → T γ
⟦ here Γ T ⟧ᵥ γ = proj₂ γ
⟦ next Γ T S v ⟧ᵥ γ = ⟦ v ⟧ᵥ (proj₁ γ)
