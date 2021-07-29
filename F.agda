{-# OPTIONS --rewriting --prop #-}

module F where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Term
open import Type

postulate _∈_ : Term → Type → Set

postulate
  ∈-Arr-I : ∀ e τ₁ τ₂ → (∀ x → x ∈ τ₁ → e x ∈ τ₂) → TmAbs e ∈ TyArr τ₁ τ₂

postulate
  ∈-Arr-E : ∀ e₁ e₂ τ₁ τ₂ → e₂ ∈ TyArr τ₁ τ₂ → e₁ ∈ τ₁ → TmApp e₂ e₁ ∈ τ₂

postulate
  ∈-All-I : ∀ e τ → (∀ σ → e ∈ τ σ) → e ∈ TyAll τ

postulate
  ∈-All-E : ∀ e τ₁ τ₂ → e ∈ TyAll τ₁ → e ∈ τ₁ τ₂

postulate
  ∈-Elim : {@♭ l : Level} (@♭ A : ∀ {t} {τ} → t ∈ τ → Set l) →
           (@♭ H-Arr-I : ∀ e τ₁ τ₂ (d : ∀ x → x ∈ τ₁ → e x ∈ τ₂) →
                         (∀ x → (d' : x ∈ τ₁) → A d' → A (d _ d')) →
                         A (∈-Arr-I e _ _ d)) →
           (@♭ H-Arr-E : ∀ e₁ e₂ τ₁ τ₂ →
                         ∀ (d₂ : e₂ ∈ TyArr τ₁ τ₂) → A d₂ →
                         ∀ (d₁ : e₁ ∈ τ₁) → A d₁ →
                         A (∈-Arr-E e₁ e₂ τ₁ τ₂ d₂ d₁)) →
           (@♭ H-All-I : ∀ e τ →
                         ∀ (d : ∀ σ → e ∈ τ σ) → (∀ σ → A (d σ)) →
                         A (∈-All-I e τ d)) →
           (@♭ H-All-E : ∀ e τ₁ τ₂ →
                         ∀ (d : e ∈ TyAll τ₁) → A d →
                         A (∈-All-E e τ₁ τ₂ d)) →
           (@♭ t : Term) (@♭ τ : Type) (@♭ d : t ∈ τ) → A d


id-tm : Term
id-tm = TmAbs (λ t → t)

id-ty : Type
id-ty = TyAll (λ τ → TyArr τ τ)

id-tm-id-ty : id-tm ∈ id-ty
id-tm-id-ty =
  ∈-All-I id-tm _ (λ τ → ∈-Arr-I (λ x → x) τ τ (λ x x∈τ → x∈τ))
