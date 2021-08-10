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
-- open import Ctx

infix 6 ƛ_
infixl 7 _·_

postulate Term : Set

module Internal where

  data Term' : Set where
    _·_ : Term → Term → Term'
    ƛ_ : (Term → Term) → Term'

postulate ⟨_⟩ : Internal.Term' → Term
{-# INJECTIVE ⟨_⟩ #-}

_·_ : Term → Term → Term
t1 · t2 = ⟨ Internal._·_ t1 t2 ⟩

ƛ_ : (Term → Term) → Term
ƛ_ t = ⟨ Internal.ƛ t ⟩

module Term where

  Ctx : Set
  Ctx = ℕ

  ⟦_⟧ : Ctx → Set
  ⟦ Γ ⟧ = Vec Term Γ

  Var : Ctx → Set
  Var = Fin

  ⟦_⟧ᵥ : {Γ : Ctx} → Var Γ → ⟦ Γ ⟧ → Term
  ⟦ x ⟧ᵥ γ = lookup γ x

  abs : {Γ : Ctx} → (⟦ Γ ⟧ → Term → Term) → ⟦ suc Γ ⟧ → Term
  abs t γ = t (tail γ) (head γ)

open Term

postulate
  Term-elim : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ v : Var Γ) → A Γ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (suc Γ) (abs t) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term) → A Γ t


postulate
  Term-elim-V : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ v : Var Γ) → A Γ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (suc Γ) (abs t) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ v : Var Γ) →
    Term-elim A HV Hƛ H· Γ ⟦ v ⟧ᵥ ≡ HV Γ v

postulate
  Term-elim-ƛ : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ v : Var Γ) → A Γ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (suc Γ) (abs t) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
    Term-elim A HV Hƛ H· Γ (λ γ → ƛ (t γ)) ≡
    Hƛ Γ t (Term-elim A HV Hƛ H· (suc Γ) (abs t))

postulate
  Term-elim-· : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ v : Var Γ) → A Γ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (suc Γ) (abs t) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
    Term-elim A HV Hƛ H· Γ (λ γ → t1 γ · t2 γ) ≡
    H· Γ t1 t2 (Term-elim A HV Hƛ H· Γ t1) (Term-elim A HV Hƛ H· Γ t2)

{-# REWRITE Term-elim-V #-}
{-# REWRITE Term-elim-ƛ #-}
{-# REWRITE Term-elim-· #-}
