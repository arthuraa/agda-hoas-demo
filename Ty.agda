{-# OPTIONS --rewriting --prop #-}

module Ty where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Vec

infix 2 `∀_
infixr 7 _—→_

postulate Ty : Set

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

⟦_⟧ : ℕ → Set
⟦ Γ ⟧ = Vec Ty Γ

& : {Γ : ℕ} → Fin Γ → ⟦ Γ ⟧ → Ty
& v γ = lookup γ v

Ty-abs : {Γ : ℕ} → (⟦ Γ ⟧ → Ty → Ty) → ⟦ suc Γ ⟧ → Ty
Ty-abs T (S ∷ γ) = T γ S

postulate
  Ty-elim : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Ty) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ α : Fin Γ) → A Γ (& α)) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty) →
      A (suc Γ) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Ty) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty) → A Γ T

postulate
  Ty-elim-V : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Ty) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ α : Fin Γ) → A Γ (& α)) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty) →
      A (suc Γ) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Ty) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ) (@♭ α : Fin Γ) →
    Ty-elim A HV H∀ H→ Γ (& α) ≡ HV Γ α

postulate
  Ty-elim-∀ : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Ty) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ α : Fin Γ) → A Γ (& α)) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty) →
      A (suc Γ) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Ty) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty) →
    Ty-elim A HV H∀ H→ Γ (λ γ → `∀ T γ) ≡
    H∀ Γ T (Ty-elim A HV H∀ H→ (suc Γ) (Ty-abs T))

postulate
  Ty-elim-→ : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Ty) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ α : Fin Γ) → A Γ (& α)) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty) →
      A (suc Γ) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Ty) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Ty) →
    Ty-elim A HV H∀ H→ Γ (λ γ → T1 γ —→ T2 γ) ≡
    H→ Γ T1 T2 (Ty-elim A HV H∀ H→ Γ T1) (Ty-elim A HV H∀ H→ Γ T2)

{-# REWRITE Ty-elim-V #-}
{-# REWRITE Ty-elim-∀ #-}
{-# REWRITE Ty-elim-→ #-}
