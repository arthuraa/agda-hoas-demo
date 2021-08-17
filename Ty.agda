{-# OPTIONS --rewriting --prop #-}

module Ty where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Ctx

infix 2 `∀_
infixr 7 _—→_

postulate `Ty : Type

Ty : Set
Ty = ⟦ `Ty ⟧ₜ

module Internal where

  data Ty' : Set where
    `∀_ : (Ty → Ty) → Ty'
    _—→_ : Ty → Ty → Ty'

postulate fold-Ty : Internal.Ty' → Ty
{-# INJECTIVE fold-Ty #-}

`∀_ : (Ty → Ty) → Ty
`∀_ T = fold-Ty (Internal.`∀ T)

_—→_ : Ty → Ty → Ty
T —→ S = fold-Ty (Internal._—→_ T S)

Ty-abs : {Γ : Ctx} → (⟦ Γ ⟧ → Ty → Ty) → ⟦ Γ ,, (λ _ → `Ty) ⟧ → Ty
Ty-abs T γ = T (π₁ γ) (π₂ γ)

postulate
  Ty-elim : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Ty) → Set l) →
    (HV : ∀ (@♭ Γ Δ) (@♭ α : Var Δ _ Γ) → A Γ ⟦ α ⟧ᵥ) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty) →
      A (Γ ,, λ _ → `Ty) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Ty) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty) → A Γ T

postulate
  Ty-elim-V : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Ty) → Set l) →
    (HV : ∀ (@♭ Γ Δ) (@♭ α : Var Δ _ Γ) → A Γ ⟦ α ⟧ᵥ) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty) →
      A (Γ ,, λ _ → `Ty) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Ty) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ Δ) (@♭ α : Var Δ _ Γ) →
    Ty-elim A HV H∀ H→ Γ ⟦ α ⟧ᵥ ≡ HV Γ Δ α

postulate
  Ty-elim-∀ : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Ty) → Set l) →
    (HV : ∀ (@♭ Γ Δ) (@♭ α : Var Δ _ Γ) → A Γ ⟦ α ⟧ᵥ) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty) →
      A (Γ ,, λ _ → `Ty) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Ty) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty) →
    Ty-elim A HV H∀ H→ Γ (λ γ → `∀ T γ) ≡
    H∀ Γ T (Ty-elim A HV H∀ H→ (Γ ,, λ _ → `Ty) (Ty-abs T))

postulate
  Ty-elim-→ : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Ty) → Set l) →
    (HV : ∀ (@♭ Γ Δ) (@♭ α : Var Δ _ Γ) → A Γ ⟦ α ⟧ᵥ) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty) →
      A (Γ ,, λ _ → `Ty) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Ty) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Ty) →
    Ty-elim A HV H∀ H→ Γ (λ γ → T1 γ —→ T2 γ) ≡
    H→ Γ T1 T2 (Ty-elim A HV H∀ H→ Γ T1) (Ty-elim A HV H∀ H→ Γ T2)

{-# REWRITE Ty-elim-V #-}
{-# REWRITE Ty-elim-∀ #-}
{-# REWRITE Ty-elim-→ #-}
