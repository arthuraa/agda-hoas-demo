{-# OPTIONS --rewriting --prop #-}

module F where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (lookup)
open import Data.List
open import Type hiding (⟦_⟧)

infix 2 `λ_
infix 2 `Λ
infixl 1 _·_
infixl 1 _%_

postulate Term : Type → Set

module QuoteTerm where

  data Term' : Type → Set where
    `λ_ : {T S : Type} → (Term T → Term S) → Term' (T —→ S)
    _·_ : {T S : Type} → Term (T —→ S) → Term T → Term' S
    `Λ : (T : Type → Type) → ((S : Type) → Term (T S)) → Term' (`∀ T)
    _%_ : {T : Type → Type} → (Term (`∀ T)) → (S : Type) → Term' (T S)

postulate fold-Term : {T : Type} → QuoteTerm.Term' T → Term T
{-# INJECTIVE fold-Term #-}

`λ_ : {T S : Type} → (Term T → Term S) → Term (T —→ S)
`λ M = fold-Term (QuoteTerm.`λ M)

_·_ : {T S : Type} → Term (T —→ S) → Term T → Term S
M · N = fold-Term (QuoteTerm._·_ M N)

`Λ : (T : Type → Type) → ((S : Type) → Term (T S)) → Term (`∀ T)
`Λ T M = fold-Term (QuoteTerm.`Λ T M)

_%_ : {T : Type → Type} → (Term (`∀ T)) → (S : Type) → Term (T S)
M % S = fold-Term (QuoteTerm._%_ M S)

⟦_⟧ : List Type → Set
⟦ Γ ⟧ = ∀ i → Term (lookup Γ i)

abs : {Γ : List Type} → {T S : Type} → (⟦ Γ ⟧ → Term T → Term S) → ⟦ T ∷ Γ ⟧ → Term S
abs t γ = t (λ i → γ (suc i)) (γ zero)

postulate
  Term-elim : {l : Level}
    (A : (@♭ Γ : List Type) → (@♭ T : Type) →
         (@♭ t : ⟦ Γ ⟧ → Term T) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ i) → A Γ (lookup Γ i) (λ γ → γ i)) →
    (Hλ : ∀ (@♭ Γ) (@♭ T S) (@♭ t : ⟦ Γ ⟧ → Term T → Term S) →
          A (T ∷ Γ) S (abs t) →
          A Γ (T —→ S) (λ γ → `λ t γ)) →
    (H· : ∀ (@♭ Γ) (@♭ T S) (@♭ M : ⟦ Γ ⟧ → Term (T —→ S)) (@♭ N : ⟦ Γ ⟧ → Term T) →
          A Γ (T —→ S) M → A Γ T N →
          A Γ S (λ γ → M γ · N γ)) →
    (HΛ : ∀ (@♭ Γ) (@♭ T : Type → Type) → (@♭ M : ⟦ Γ ⟧ → ∀ S → Term (T S)) →
          (∀ (@♭ S) → A Γ (T S) (λ γ → M γ S)) →
          A Γ (`∀ T) (λ γ → `Λ T (M γ))) →
    (H[] : ∀ (@♭ Γ) (@♭ T : Type → Type) (@♭ M : ⟦ Γ ⟧ → Term (`∀ T)) (@♭ S) →
           A Γ (`∀ T) M →
           A Γ (T S) (λ γ → M γ % S)) →
    ∀ (@♭ Γ) (@♭ T) (@♭ t) → A Γ T t

postulate
  Term-elim-λ : {l : Level}
    (A : (@♭ Γ : List Type) → (@♭ T : Type) →
         (@♭ t : ⟦ Γ ⟧ → Term T) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ i) → A Γ (lookup Γ i) (λ γ → γ i)) →
    (Hλ : ∀ (@♭ Γ) (@♭ T S) (@♭ t : ⟦ Γ ⟧ → Term T → Term S) →
          A (T ∷ Γ) S (abs t) →
          A Γ (T —→ S) (λ γ → `λ t γ)) →
    (H· : ∀ (@♭ Γ) (@♭ T S) (@♭ M : ⟦ Γ ⟧ → Term (T —→ S)) (@♭ N : ⟦ Γ ⟧ → Term T) →
          A Γ (T —→ S) M → A Γ T N →
          A Γ S (λ γ → M γ · N γ)) →
    (HΛ : ∀ (@♭ Γ) (@♭ T : Type → Type) → (@♭ M : ⟦ Γ ⟧ → ∀ S → Term (T S)) →
          (∀ (@♭ S) → A Γ (T S) (λ γ → M γ S)) →
          A Γ (`∀ T) (λ γ → `Λ T (M γ))) →
    (H[] : ∀ (@♭ Γ) (@♭ T : Type → Type) (@♭ M : ⟦ Γ ⟧ → Term (`∀ T)) (@♭ S) →
           A Γ (`∀ T) M →
           A Γ (T S) (λ γ → M γ % S)) →
    ∀ (@♭ Γ) (@♭ T S) (@♭ t) →
    Term-elim A HV Hλ H· HΛ H[] Γ (T —→ S) (λ γ → `λ t γ) ≡
    Hλ Γ T S t (Term-elim A HV Hλ H· HΛ H[] (T ∷ Γ) S (abs t))


postulate
  Term-elim-Λ : {l : Level}
    (A : (@♭ Γ : List Type) → (@♭ T : Type) →
         (@♭ t : ⟦ Γ ⟧ → Term T) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ i) → A Γ (lookup Γ i) (λ γ → γ i)) →
    (Hλ : ∀ (@♭ Γ) (@♭ T S) (@♭ t : ⟦ Γ ⟧ → Term T → Term S) →
          A (T ∷ Γ) S (abs t) →
          A Γ (T —→ S) (λ γ → `λ t γ)) →
    (H· : ∀ (@♭ Γ) (@♭ T S) (@♭ M : ⟦ Γ ⟧ → Term (T —→ S)) (@♭ N : ⟦ Γ ⟧ → Term T) →
          A Γ (T —→ S) M → A Γ T N →
          A Γ S (λ γ → M γ · N γ)) →
    (HΛ : ∀ (@♭ Γ) (@♭ T : Type → Type) → (@♭ M : ⟦ Γ ⟧ → ∀ S → Term (T S)) →
          (∀ (@♭ S) → A Γ (T S) (λ γ → M γ S)) →
          A Γ (`∀ T) (λ γ → `Λ T (M γ))) →
    (H[] : ∀ (@♭ Γ) (@♭ T : Type → Type) (@♭ M : ⟦ Γ ⟧ → Term (`∀ T)) (@♭ S) →
           A Γ (`∀ T) M →
           A Γ (T S) (λ γ → M γ % S)) →
    ∀ (@♭ Γ) (@♭ T) (@♭ t) →
    Term-elim A HV Hλ H· HΛ H[] Γ (`∀ T) (λ γ → `Λ T (t γ)) ≡
    HΛ Γ T t (λ S → Term-elim A HV Hλ H· HΛ H[] Γ (T S) (λ γ → t γ S))

postulate
  Term-elim-[] : {l : Level}
    (A : (@♭ Γ : List Type) → (@♭ T : Type) →
         (@♭ t : ⟦ Γ ⟧ → Term T) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ i) → A Γ (lookup Γ i) (λ γ → γ i)) →
    (Hλ : ∀ (@♭ Γ) (@♭ T S) (@♭ t : ⟦ Γ ⟧ → Term T → Term S) →
          A (T ∷ Γ) S (abs t) →
          A Γ (T —→ S) (λ γ → `λ t γ)) →
    (H· : ∀ (@♭ Γ) (@♭ T S) (@♭ M : ⟦ Γ ⟧ → Term (T —→ S)) (@♭ N : ⟦ Γ ⟧ → Term T) →
          A Γ (T —→ S) M → A Γ T N →
          A Γ S (λ γ → M γ · N γ)) →
    (HΛ : ∀ (@♭ Γ) (@♭ T : Type → Type) → (@♭ M : ⟦ Γ ⟧ → ∀ S → Term (T S)) →
          (∀ (@♭ S) → A Γ (T S) (λ γ → M γ S)) →
          A Γ (`∀ T) (λ γ → `Λ T (M γ))) →
    (H[] : ∀ (@♭ Γ) (@♭ T : Type → Type) (@♭ M : ⟦ Γ ⟧ → Term (`∀ T)) (@♭ S) →
           A Γ (`∀ T) M →
           A Γ (T S) (λ γ → M γ % S)) →
    ∀ (@♭ Γ) (@♭ T) (@♭ t) (@♭ S) →
    Term-elim A HV Hλ H· HΛ H[] Γ (T S) (λ γ → t γ % S) ≡
    H[] Γ T t S (Term-elim A HV Hλ H· HΛ H[] Γ (`∀ T) (λ γ → t γ))

{-# REWRITE Term-elim-λ #-}
{-# REWRITE Term-elim-Λ #-}
{-# REWRITE Term-elim-[] #-}
