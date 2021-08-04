{-# OPTIONS --rewriting --prop #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Unit
open import Data.Product

mutual

  data Ctx : Set₁ where
    empty : Ctx
    cons  : (Γ : Ctx) → Type Γ → Ctx

  postulate Type : Ctx → Set₁
  ⟦_⟧ : Ctx → Set
  postulate ⟦_⟧ₜ : {Γ : Ctx} → Type Γ → ⟦ Γ ⟧ → Set

  ⟦ empty ⟧ = ⊤
  ⟦ cons Γ T ⟧ = Σ[ γ ∈ ⟦ Γ ⟧ ] ⟦ T ⟧ₜ γ

postulate weak : (Γ : Ctx) → (T S : Type Γ) → Type (cons Γ T)
postulate ⟦weak⟧ : ∀ (Γ : Ctx) (T S : Type Γ) (γ : ⟦ cons Γ T ⟧) →
                   ⟦ weak Γ T S ⟧ₜ γ ≡ ⟦ S ⟧ₜ (proj₁ γ)
{-# REWRITE ⟦weak⟧ #-}

data Var : (Γ : Ctx) (T : ⟦ Γ ⟧ → Set) → Set₁ where
  here : (Γ : Ctx) → (T : Type Γ) → Var (cons Γ T) (λ γ → ⟦ T ⟧ₜ (proj₁ γ))
  next : (Γ : Ctx) → (T : Type Γ) (S : ⟦ Γ ⟧ → Set) → Var Γ S →
         Var (cons Γ T) (λ γ → S (proj₁ γ))

⟦_⟧ᵥ : {Γ : Ctx} {T : ⟦ Γ ⟧ → Set} →
       (v : Var Γ T) → (γ : ⟦ Γ ⟧) → T γ
⟦ here Γ T ⟧ᵥ γ = proj₂ γ
⟦ next Γ T S v ⟧ᵥ γ = ⟦ v ⟧ᵥ (proj₁ γ)
