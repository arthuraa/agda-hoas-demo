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
-- open import Ctx

infix 3 _⇒_

postulate _⇒_ : Term → Term → Set

postulate
  prefl : ∀ t → t ⇒ t

postulate
  papp : ∀ {t1 t1' t2 t2'} →
    t1 ⇒ t1' →
    t2 ⇒ t2' →
    t1 · t2 ⇒ t1' · t2'

postulate
  pabs : ∀ {t t'} →
    (∀ (x : Term) → t x ⇒ t' x) →
    ƛ t ⇒ ƛ t'

postulate
  pbeta : ∀ {t1 t1' : Term → Term} {t2 t2'} →
    (∀ (x : Term) → t1 x ⇒ t1' x) →
    t2 ⇒ t2' →
    (ƛ t1) · t2 ⇒ t1' t2'

postulate
  ⇒-elim :
    ∀ {l : Level} →
    ∀ (A : ∀ (@♭ Γ) → (@♭ t1 t2 : Term.⟦ Γ ⟧ → Term) → Set l) →
    ∀ (HR : ∀ (@♭ Γ) (@♭ t) → A Γ t t) →
    ∀ (H· : ∀ (@♭ Γ) (@♭ t1 t1' t2 t2') → A Γ t1 t1' → A Γ t2 t2' →
            A Γ (λ γ → t1 γ · t2 γ) (λ γ → t1' γ · t2' γ)) →
    ∀ (Hƛ : ∀ (@♭ Γ) →
            ∀ (@♭ t t' : Term.⟦ Γ ⟧ → Term → Term) →
            A (suc Γ) (Term.abs t) (Term.abs t') →
            A Γ (λ γ → ƛ t γ) (λ γ → ƛ t' γ)) →
    ∀ (Hβ : ∀ (@♭ Γ) →
            ∀ (@♭ t1 t1' : Term.⟦ Γ ⟧ → Term → Term) →
            ∀ (@♭ t2 t2') →
            A (suc Γ) (Term.abs t1) (Term.abs t1') →
            A Γ t2 t2' →
            A Γ (λ γ → (ƛ t1 γ) · t2 γ) (λ γ → t1' γ (t2' γ))) →
    ∀ (@♭ Γ t1 t2) →
    ∀ (@♭ p : ∀ γ → t1 γ ⇒ t2 γ) → A Γ t1 t2

abs :
  ∀ {@♭ Γ} {@♭ t1 t1' : Term.⟦ Γ ⟧ → Term → Term} →
  (p : ∀ γ x → t1 γ x ⇒ t1' γ x) →
  ∀ γ → Term.abs t1 γ ⇒ Term.abs t1' γ
abs p γ = p (tail γ) (head γ)

up : ∀ {@♭ Γ Δ} → @♭ (Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧) → Term.⟦ suc Δ ⟧ → Term.⟦ suc Γ ⟧
up ts (x ∷ γ) = x ∷ ts γ

⇒-up : ∀ {@♭ Γ Δ} →
       ∀ {@♭ t t' : Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧} →
       (∀ γ i → lookup (t γ) i ⇒ lookup (t' γ) i) →
       ∀ γ i → lookup (up t γ) i ⇒ lookup (up t' γ) i
⇒-up p (x ∷ γ) zero = prefl x
⇒-up p (x ∷ γ) (suc i) = p γ i

⇒-subst-refl :
  ∀ (@♭ Γ Δ) →
  ∀ (@♭ t1 : Term.⟦ Γ ⟧ → Term) →
  ∀ (@♭ t2 t2' : Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧) →
  ∀ (@♭ p2 : ∀ γ i → lookup (t2 γ) i ⇒ lookup (t2' γ) i) →
  ∀ γ → t1 (t2 γ) ⇒ t1 (t2' γ)
⇒-subst-refl Γ Δ t1 t2 t2' p2 γ =
  Term-elim A HV Hƛ H· Γ t1 Δ t2 t2' p2 γ
  where
  A : ∀ (@♭ Γ) (@♭ t1 : Term.⟦ Γ ⟧ → Term) → Set
  A Γ t1 =
    ∀ (@♭ Δ) →
    ∀ (@♭ t2 t2' : Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧) →
    ∀ (@♭ p2 : ∀ γ i → lookup (t2 γ) i ⇒ lookup (t2' γ) i) →
    ∀ γ → t1 (t2 γ) ⇒ t1 (t2' γ)

  HV : _
  HV Γ x1 Δ t2 t2' p2 γ = p2 γ x1

  Hƛ : _
  Hƛ Γ t1 IH1 Δ t2 t2' p2 γ =
    pabs (λ x → IH1 (suc Δ) (up t2) (up t2') (⇒-up p2) (x ∷ γ))

  H· : _
  H· Γ t1 t1' IH1 IH1' Δ t2 t2' p2 γ =
    papp (IH1 Δ t2 t2' p2 γ) (IH1' Δ t2 t2' p2 γ)

⇒-subst-gen :
  ∀ (@♭ Γ Δ) →
  ∀ (@♭ t1 t1' : Term.⟦ Γ ⟧ → Term) →
  ∀ (@♭ t2 t2' : Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧) →
  ∀ (@♭ p1 : ∀ γ   → t1 γ ⇒ t1' γ) →
  ∀ (@♭ p2 : ∀ γ i → lookup (t2 γ) i ⇒ lookup (t2' γ) i) →
  ∀ γ → t1 (t2 γ) ⇒ t1' (t2' γ)
⇒-subst-gen Γ Δ t1 t1' t2 t2' p1 p2 γ =
  ⇒-elim A HR H· Hƛ Hβ Γ t1 t1' p1 Δ t2 t2' p2 γ
  where
  A : ∀ (@♭ Γ) (@♭ t1 t1' : Term.⟦ Γ ⟧ → Term) → Set
  A Γ t1 t1' =
    ∀ (@♭ Δ) →
    ∀ (@♭ t2 t2' : Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧) →
    ∀ (@♭ p2 : ∀ γ i → lookup (t2 γ) i ⇒ lookup (t2' γ) i) →
    ∀ γ → t1 (t2 γ) ⇒ t1' (t2' γ)

  HR : _
  HR Γ t1 Δ t2 t2' p2 γ = ⇒-subst-refl Γ Δ t1 t2 t2' p2 γ

  H· : _
  H· Γ t11 t11' t12 t12' IH1 IH2 Δ t2 t2' p2 γ =
    papp (IH1 Δ t2 t2' p2 γ) (IH2 Δ t2 t2' p2 γ)

  Hƛ : _
  Hƛ Γ t1 t1' IH Δ t2 t2' p2 γ =
    pabs (λ x → IH (suc Δ) (up t2) (up t2') (⇒-up p2) (x ∷ γ))

  Hβ : _
  Hβ Γ t11 t11' t12 t12' IH1 IH2 Δ t2 t2' p2 γ =
    pbeta (λ x → IH1 (suc Δ) (up t2) (up t2') (⇒-up p2) (x ∷ γ))
          (IH2 Δ t2 t2' p2 γ)

⇒-abs :
  ∀ {@♭ Γ} →
  ∀ {@♭ t t' : Term.⟦ Γ ⟧ → Term → Term} →
  ∀ (@♭ p : ∀ γ x → t γ x ⇒ t' γ x) →
  ∀ γ → Term.abs t γ ⇒ Term.abs t' γ
⇒-abs p (x ∷ γ) = p γ x

⇒-subst-lem :
  ∀ {@♭ Γ} →
  ∀ {@♭ t t' : Term.⟦ Γ ⟧ → Term} →
  ∀ (@♭ p : ∀ γ → t γ ⇒ t' γ) →
  ∀ γ i → lookup (t γ ∷ γ) i ⇒ lookup (t' γ ∷ γ) i
⇒-subst-lem p γ zero = p γ
⇒-subst-lem p γ (suc i) = prefl (lookup γ i)

⇒-subst-n :
  ∀ (@♭ Γ) →
  ∀ (@♭ t1 t1' : Term.⟦ Γ ⟧ → Term → Term) →
  ∀ (@♭ t2 t2' : Term.⟦ Γ ⟧ → Term) →
  ∀ (@♭ p1 : ∀ γ x → t1 γ x ⇒ t1' γ x) →
  ∀ (@♭ p2 : ∀ γ → t2 γ ⇒ t2' γ) →
  ∀ γ → t1 γ (t2 γ) ⇒ t1' γ (t2' γ)
⇒-subst-n Γ t1 t1' t2 t2' p1 p2 γ =
  ⇒-subst-gen (suc Γ) Γ (Term.abs t1) (Term.abs t1')
    (λ γ → t2 γ ∷ γ) (λ γ → t2' γ ∷ γ) (⇒-abs p1) (⇒-subst-lem p2) γ

⇒-subst-1 :
  ∀ (@♭ t1 t1' : Term → Term) →
  ∀ (@♭ t2 t2' : Term) →
  ∀ (@♭ p1 : ∀ x → t1 x ⇒ t1' x) →
  ∀ (@♭ p2 : t2 ⇒ t2') →
  t1 t2 ⇒ t1' t2'
⇒-subst-1 t1 t1' t2 t2' p1 p2 =
  ⇒-subst-n zero (λ _ → t1) (λ _ → t1') (λ _ → t2) (λ _ → t2')
            (λ _ → p1) (λ _ → p2) []
