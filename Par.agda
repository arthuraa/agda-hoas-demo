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
open import Ctx

infix 3 _⇒_
infix 3 _`⇒_

postulate _⇒_ : Term → Term → Set

postulate
  papp : ∀ {t1 t1' t2 t2'} →
    t1 ⇒ t1' →
    t2 ⇒ t2' →
    t1 · t2 ⇒ t1' · t2'

postulate
  pabs : ∀ {t t'} →
    (∀ (x : Term) → x ⇒ x → t x ⇒ t' x) →
    ƛ t ⇒ ƛ t'

postulate
  pbeta : ∀ {t1 t1' : Term → Term} {t2 t2'} →
    (∀ (x : Term) → x ⇒ x → t1 x ⇒ t1' x) →
    t2 ⇒ t2' →
    (ƛ t1) · t2 ⇒ t1' t2'

postulate
  _`⇒_ : {@♭ Γ : Ctx} → (@♭ t1 t2 : ⟦ Γ ⟧ → Term) → Type Γ

postulate
  ⟦⇒-Type⟧ₜ : ∀ {@♭ Γ : Ctx} (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
              ⟦ t1 `⇒ t2 ⟧ₜ ≡ λ γ → t1 γ ⇒ t2 γ

{-# REWRITE ⟦⇒-Type⟧ₜ #-}

Term-λ : {Γ : Ctx} → (⟦ Γ ⟧ → Term → Term) → ⟦ Γ `, `Term ⟧ → Term
Term-λ t γ = t (proj₁ γ) (proj₂ γ)

⇒-λ : {@♭ Γ : Ctx} {t1 t2 : ⟦ Γ ⟧ → Term → Term} →
      (p : ∀ γ x → x ⇒ x → t1 γ x ⇒ t2 γ x) →
      (γ : ⟦ Γ `, `Term `,  proj₂ `⇒ proj₂ ⟧) →
      Term-λ t1 (proj₁ γ) ⇒ Term-λ t2 (proj₁ γ)

⇒-λ {Γ} {t1} {t2} p ( ( γ , x ) , x⇒x ) = p γ x x⇒x

postulate
  ⇒-elim :
    ∀ {l : Level} →
    ∀ (A : ∀ (@♭ Γ) → (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
           (@♭ p : ∀ γ → t1 γ ⇒ t2 γ) → Set l) →
    ∀ (HV : ∀ (@♭ Γ) → (@♭ t t' : ⟦ Γ ⟧ → Term) →
            ∀ (@♭ v : Var Γ (λ γ → t γ ⇒ t' γ)) →
            A Γ t t' ⟦ v ⟧ᵥ) →
    ∀ (H· : ∀ (@♭ Γ) → (@♭ t1 t1' t2 t2' : ⟦ Γ ⟧ → Term) →
            ∀ (@♭ p1 : ∀ γ → t1 γ ⇒ t1' γ) →
            ∀ (@♭ p2 : ∀ γ → t2 γ ⇒ t2' γ) →
            A Γ t1 t1' p1 →
            A Γ t2 t2' p2 →
            A Γ _ _ (λ γ → papp (p1 γ) (p2 γ))) →
    ∀ (Hƛ : ∀ (@♭ Γ) → (@♭ t t' : ⟦ Γ ⟧ → Term → Term) →
            ∀ (@♭ p : ∀ γ x → x ⇒ x → t γ x ⇒ t' γ x) →
            A (Γ `, `Term `, proj₂ `⇒ proj₂) _ _ (⇒-λ p) →
            A Γ _ _ (λ γ → pabs (p γ))) →
    ∀ (Hβ : ∀ (@♭ Γ) → (@♭ t1 t1' : ⟦ Γ ⟧ → Term → Term) →
            ∀ (@♭ t2 t2' : ⟦ Γ ⟧ → Term) →
            ∀ (@♭ p1 : ∀ γ x → x ⇒ x → t1 γ x ⇒ t1' γ x) →
            ∀ (@♭ p2 : ∀ γ → t2 γ ⇒ t2' γ) →
            A (Γ `, `Term `, proj₂ `⇒ proj₂) _ _ (⇒-λ p1) →
            A Γ _ _ p2 →
            A Γ _ _ (λ γ → pbeta (p1 γ) (p2 γ))) →
    ∀ (@♭ Γ t1 t2 p) → A Γ t1 t2 p


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
