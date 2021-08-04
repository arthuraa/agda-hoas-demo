{-# OPTIONS --rewriting --prop #-}

module Par where

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
open import Term

infix 2 _⇒_

postulate _⇒_ : Term → Term → Set

mutual





postulate
  papp : ∀ {t1 t1' t2 t2'} →
    t1 ⇒ t1' →
    t2 ⇒ t2' →
    t1 · t2 ⇒ t1' · t2'

postulate
  pabs : ∀ t t' →
    (∀ (x : Term) → x ⇒ x → t x ⇒ t' x) →
    ƛ t ⇒ ƛ t'

postulate
  pbeta : ∀ {t1 t1' : Term → Term} {t2 t2'} →
    (∀ (x : Term) → x ⇒ x → t1 x ⇒ t1' x) →
    t2 ⇒ t2' →
    (ƛ t1) · t2 ⇒ t1' t2'


{-

postulate
  ⇒-elim :
    ∀ {l : Level} →
    ∀ (A : (@♭ n : ℕ) → (@♭ t t' : Vec Term n → Term) →
           (@♭ p : ∀ γ → (∀ i → lookup γ i ⇒ lookup γ i) → t γ ⇒ t' γ) → Set l) →
    (∀ (@♭ n) (@♭ x : Fin n) →
      A n (λ γ → lookup γ x) (λ γ → lookup γ x) (λ γ γ⇒ → γ⇒ x)) →
    (∀ (@♭ n) (@♭ t1 t1' t2 t2' : Vec Term n → Term) (@♭ p1) (@♭ p2) →
      A n t1 t1' p1 →
      A n t2 t2' p2 →
      A n (λ γ → t1 γ · t2 γ) (λ γ → t1' γ · t2' γ)
          (λ γ γ⇒γ → papp (p1 γ γ⇒γ) (p2 γ γ⇒γ))) →
    (∀ (@♭ n) (@♭ t t' : Vec Term n → Term → Term) →
     ∀ (@♭ p : ∀ γ → (∀ i → lookup γ i ⇒ lookup γ i) → ∀ x → x ⇒ x →
               t γ x ⇒ t' γ x) →
     A (suc n) (λ γ → t (tail γ) (head γ)) (λ γ → t' (tail γ) (head γ))
       (λ γ γ⇒γ → p (tail γ) (tail-env {γ = γ} γ⇒γ) (head γ) (head-env {γ = γ} γ⇒γ)) →
     A n (λ γ → ƛ t γ) (λ γ → ƛ t' γ) (λ γ γ⇒γ → pabs _ _ (p γ γ⇒γ))) →
    (∀ (@♭ n) (@♭ t1 t1' : Vec Term n → Term → Term) (@♭ t2 t2' : Vec Term n → Term) →
     ∀ (@♭ p1 : ∀ γ → (∀ i → lookup γ i ⇒ lookup γ i) → ∀ x → x ⇒ x →
                t1 γ x ⇒ t1' γ x) →
     ∀ (@♭ p2 : ∀ γ → (∀ i → lookup γ i ⇒ lookup γ i) → t2 γ ⇒ t2' γ) →
      A (suc n) (λ γ → t1 (tail γ) (head γ)) (λ γ → t1' (tail γ) (head γ))
        (λ γ γ⇒γ → p1 (tail γ) (tail-env {γ = γ} γ⇒γ) (head γ) (head-env {γ = γ} γ⇒γ)) →
      A n t2 t2' p2 →
      A n (λ γ → (ƛ t1 γ) · t2 γ) (λ γ → t1' γ (t2' γ))
          (λ γ γ⇒γ → pbeta (p1 γ γ⇒γ) (p2 γ γ⇒γ))) →
    ∀ (@♭ n t t' p) → A n t t' p

-}
