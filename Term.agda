{-# OPTIONS --rewriting --prop #-}

module Term where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Product hiding (∃; ∃!)
open import Data.Sum
open import Data.Nat
open import Data.Fin hiding (_+_; cast)
open import Data.Vec
open import Flat
open import Ctx

infix 6 ƛ_
infixl 7 _·_

postulate Term : Set

postulate  _·_ : Term → Term → Term

postulate ƛ_ : (Term → Term) → Term

postulate ·-inj : ∀ t₁ t₁' t₂ t₂' →
                  t₁ · t₂ ≡ t₁' · t₂' → t₁ ≡ t₁' × t₂ ≡ t₂'

postulate ƛ-inj : ∀ t t' → ƛ t ≡ ƛ t' → t ≡ t'

postulate ƛ-·-disj : ∀ t t₁ t₂ → ƛ t ≢ t₁ · t₂

postulate Term-Type : {Γ : Ctx} → Type Γ

postulate ⟦Term-Type⟧ₜ : ∀ Γ → ⟦ Term-Type {Γ} ⟧ₜ ≡ λ γ → Term

{-# REWRITE ⟦Term-Type⟧ₜ #-}

postulate
  Term-elim : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ v : Var Γ (λ _ → Term)) → A Γ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (cons Γ Term-Type) (λ γ → t (proj₁ γ) (proj₂ γ)) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term) → A Γ t


postulate
  Term-elim-V : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ v : Var Γ (λ _ → Term)) → A Γ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (cons Γ Term-Type) (λ γ → t (proj₁ γ) (proj₂ γ)) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ v : Var Γ (λ _ → Term)) →
    Term-elim A HV Hƛ H· Γ ⟦ v ⟧ᵥ ≡ HV Γ v

postulate
  Term-elim-ƛ : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ v : Var Γ (λ _ → Term)) → A Γ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (cons Γ Term-Type) (λ γ → t (proj₁ γ) (proj₂ γ)) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
    Term-elim A HV Hƛ H· Γ (λ γ → ƛ (t γ)) ≡
    Hƛ Γ t
     (Term-elim A HV Hƛ H· (cons Γ Term-Type) (λ γ → t (proj₁ γ) (proj₂ γ)))

postulate
  Term-elim-· : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ v : Var Γ (λ _ → Term)) → A Γ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (cons Γ Term-Type) (λ γ → t (proj₁ γ) (proj₂ γ)) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
    Term-elim A HV Hƛ H· Γ (λ γ → t1 γ · t2 γ) ≡
    H· Γ t1 t2 (Term-elim A HV Hƛ H· Γ t1) (Term-elim A HV Hƛ H· Γ t2)

{-# REWRITE Term-elim-V #-}
{-# REWRITE Term-elim-ƛ #-}
{-# REWRITE Term-elim-· #-}
