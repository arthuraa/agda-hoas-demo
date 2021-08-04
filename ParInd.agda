{-# OPTIONS --rewriting --prop #-}

module ParInd where

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
open import Term

infix 2 _⇒_

data _⇒_ : Term → Term → Set where

  prefl : ∀ t → t ⇒ t

  papp : ∀ t₁ t₁' t₂ t₂' →
         t₁ ⇒ t₁' →
         t₂ ⇒ t₂' →
         t₁ · t₂ ⇒ t₁' · t₂'

  pabs : ∀ t t' →
         (∀ x → t x ⇒ t' x) →
         ƛ t ⇒ ƛ t'

  pbeta : ∀ {t₁ t₁' : Term → Term} {t₂ t₂' : Term} →
          (∀ x → t₁ x ⇒ t₁' x) →
          t₂ ⇒ t₂' →
          (ƛ t₁) · t₂ ⇒ (t₁' t₂')


diag-aux-⇒ : ∀ (@♭ n) (@♭ t1 : Vec Term n → Term) t2 t' →
             ∀ γ (f : Fin n → Res) → (∀ i → f i ≡ inj₁ (lookup γ i)) →
             t1 γ ≡ t2 → t2 ⇒ t' →
             diag-aux-spec t' (diag-aux n t1 γ f)
diag-aux-⇒ n t1 .t2 .t2 γ f f-γ e (prefl t2)
  rewrite (sym e) = diag-aux-refl n t1 γ f f-γ
diag-aux-⇒ n t1 .(t21 · t22) .(t21' · t22') γ f f-γ e
  (papp t21 t21' t22 t22' p1 p2) = p
  where

  p : diag-aux-spec (t21' · t22') (diag-aux n t1 γ f)
  p = {!!}
