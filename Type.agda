{-# OPTIONS --rewriting --prop #-}

module Type where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Vec

infix 2 `∀_
infixr 7 _—→_

postulate Type : Set

module Internal where

  data Type' : Set where
    `∀_ : (Type → Type) → Type'
    _—→_ : Type → Type → Type'

postulate fold-Type : Internal.Type' → Type
{-# INJECTIVE fold-Type #-}

`∀_ : (Type → Type) → Type
`∀_ T = fold-Type (Internal.`∀ T)

_—→_ : Type → Type → Type
T —→ S = fold-Type (Internal._—→_ T S)

⟦_⟧ : ℕ → Set
⟦ Γ ⟧ = Vec Type Γ

& : {Γ : ℕ} → Fin Γ → ⟦ Γ ⟧ → Type
& v γ = lookup γ v

Ty-abs : {Γ : ℕ} → (⟦ Γ ⟧ → Type → Type) → ⟦ suc Γ ⟧ → Type
Ty-abs T (S ∷ γ) = T γ S

postulate
  Type-elim : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Type) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ α : Fin Γ) → A Γ (& α)) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Type → Type) →
      A (suc Γ) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Type) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Type) → A Γ T

postulate
  Type-elim-V : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Type) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ α : Fin Γ) → A Γ (& α)) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Type → Type) →
      A (suc Γ) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Type) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ) (@♭ α : Fin Γ) →
    Type-elim A HV H∀ H→ Γ (& α) ≡ HV Γ α

postulate
  Type-elim-∀ : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Type) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ α : Fin Γ) → A Γ (& α)) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Type → Type) →
      A (suc Γ) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Type) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Type → Type) →
    Type-elim A HV H∀ H→ Γ (λ γ → `∀ T γ) ≡
    H∀ Γ T (Type-elim A HV H∀ H→ (suc Γ) (Ty-abs T))

postulate
  Type-elim-→ : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Type) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ α : Fin Γ) → A Γ (& α)) →
    (H∀ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Type → Type) →
      A (suc Γ) (Ty-abs T) →
      A Γ (λ γ → `∀ T γ)) →
    (H→ : ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Type) →
      A Γ T1 → A Γ T2 → A Γ (λ γ → T1 γ —→ T2 γ)) →
    ∀ (@♭ Γ) (@♭ T1 T2 : ⟦ Γ ⟧ → Type) →
    Type-elim A HV H∀ H→ Γ (λ γ → T1 γ —→ T2 γ) ≡
    H→ Γ T1 T2 (Type-elim A HV H∀ H→ Γ T1) (Type-elim A HV H∀ H→ Γ T2)

{-# REWRITE Type-elim-V #-}
{-# REWRITE Type-elim-∀ #-}
{-# REWRITE Type-elim-→ #-}
