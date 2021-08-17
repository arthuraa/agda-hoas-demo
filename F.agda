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
open import Ty hiding (⟦_⟧)

infix 2 `λ_
infix 2 `Λ
infixl 1 _·_
infixl 1 _%_

postulate Tm : Ty → Set

module QuoteTm where

  data Tm' : Ty → Set where
    `λ_ : {T S : Ty} → (Tm T → Tm S) → Tm' (T —→ S)
    _·_ : {T S : Ty} → Tm (T —→ S) → Tm T → Tm' S
    `Λ : (T : Ty → Ty) → ((S : Ty) → Tm (T S)) → Tm' (`∀ T)
    _%_ : {T : Ty → Ty} → (Tm (`∀ T)) → (S : Ty) → Tm' (T S)

postulate fold-Tm : {T : Ty} → QuoteTm.Tm' T → Tm T
{-# INJECTIVE fold-Tm #-}

`λ_ : {T S : Ty} → (Tm T → Tm S) → Tm (T —→ S)
`λ M = fold-Tm (QuoteTm.`λ M)

_·_ : {T S : Ty} → Tm (T —→ S) → Tm T → Tm S
M · N = fold-Tm (QuoteTm._·_ M N)

`Λ : (T : Ty → Ty) → ((S : Ty) → Tm (T S)) → Tm (`∀ T)
`Λ T M = fold-Tm (QuoteTm.`Λ T M)

_%_ : {T : Ty → Ty} → (Tm (`∀ T)) → (S : Ty) → Tm (T S)
M % S = fold-Tm (QuoteTm._%_ M S)

⟦_⟧ : List Ty → Set
⟦ Γ ⟧ = ∀ i → Tm (lookup Γ i)

abs : {Γ : List Ty} → {T S : Ty} → (⟦ Γ ⟧ → Tm T → Tm S) → ⟦ T ∷ Γ ⟧ → Tm S
abs t γ = t (λ i → γ (suc i)) (γ zero)

postulate
  Tm-elim : {l : Level}
    (A : (@♭ Γ : List Ty) → (@♭ T : Ty) →
         (@♭ t : ⟦ Γ ⟧ → Tm T) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ i) → A Γ (lookup Γ i) (λ γ → γ i)) →
    (Hλ : ∀ (@♭ Γ) (@♭ T S) (@♭ t : ⟦ Γ ⟧ → Tm T → Tm S) →
          A (T ∷ Γ) S (abs t) →
          A Γ (T —→ S) (λ γ → `λ t γ)) →
    (H· : ∀ (@♭ Γ) (@♭ T S) (@♭ M : ⟦ Γ ⟧ → Tm (T —→ S)) (@♭ N : ⟦ Γ ⟧ → Tm T) →
          A Γ (T —→ S) M → A Γ T N →
          A Γ S (λ γ → M γ · N γ)) →
    (HΛ : ∀ (@♭ Γ) (@♭ T : Ty → Ty) → (@♭ M : ⟦ Γ ⟧ → ∀ S → Tm (T S)) →
          (∀ (@♭ S) → A Γ (T S) (λ γ → M γ S)) →
          A Γ (`∀ T) (λ γ → `Λ T (M γ))) →
    (H[] : ∀ (@♭ Γ) (@♭ T : Ty → Ty) (@♭ M : ⟦ Γ ⟧ → Tm (`∀ T)) (@♭ S) →
           A Γ (`∀ T) M →
           A Γ (T S) (λ γ → M γ % S)) →
    ∀ (@♭ Γ) (@♭ T) (@♭ t) → A Γ T t

postulate
  Tm-elim-λ : {l : Level}
    (A : (@♭ Γ : List Ty) → (@♭ T : Ty) →
         (@♭ t : ⟦ Γ ⟧ → Tm T) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ i) → A Γ (lookup Γ i) (λ γ → γ i)) →
    (Hλ : ∀ (@♭ Γ) (@♭ T S) (@♭ t : ⟦ Γ ⟧ → Tm T → Tm S) →
          A (T ∷ Γ) S (abs t) →
          A Γ (T —→ S) (λ γ → `λ t γ)) →
    (H· : ∀ (@♭ Γ) (@♭ T S) (@♭ M : ⟦ Γ ⟧ → Tm (T —→ S)) (@♭ N : ⟦ Γ ⟧ → Tm T) →
          A Γ (T —→ S) M → A Γ T N →
          A Γ S (λ γ → M γ · N γ)) →
    (HΛ : ∀ (@♭ Γ) (@♭ T : Ty → Ty) → (@♭ M : ⟦ Γ ⟧ → ∀ S → Tm (T S)) →
          (∀ (@♭ S) → A Γ (T S) (λ γ → M γ S)) →
          A Γ (`∀ T) (λ γ → `Λ T (M γ))) →
    (H[] : ∀ (@♭ Γ) (@♭ T : Ty → Ty) (@♭ M : ⟦ Γ ⟧ → Tm (`∀ T)) (@♭ S) →
           A Γ (`∀ T) M →
           A Γ (T S) (λ γ → M γ % S)) →
    ∀ (@♭ Γ) (@♭ T S) (@♭ t) →
    Tm-elim A HV Hλ H· HΛ H[] Γ (T —→ S) (λ γ → `λ t γ) ≡
    Hλ Γ T S t (Tm-elim A HV Hλ H· HΛ H[] (T ∷ Γ) S (abs t))


postulate
  Tm-elim-Λ : {l : Level}
    (A : (@♭ Γ : List Ty) → (@♭ T : Ty) →
         (@♭ t : ⟦ Γ ⟧ → Tm T) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ i) → A Γ (lookup Γ i) (λ γ → γ i)) →
    (Hλ : ∀ (@♭ Γ) (@♭ T S) (@♭ t : ⟦ Γ ⟧ → Tm T → Tm S) →
          A (T ∷ Γ) S (abs t) →
          A Γ (T —→ S) (λ γ → `λ t γ)) →
    (H· : ∀ (@♭ Γ) (@♭ T S) (@♭ M : ⟦ Γ ⟧ → Tm (T —→ S)) (@♭ N : ⟦ Γ ⟧ → Tm T) →
          A Γ (T —→ S) M → A Γ T N →
          A Γ S (λ γ → M γ · N γ)) →
    (HΛ : ∀ (@♭ Γ) (@♭ T : Ty → Ty) → (@♭ M : ⟦ Γ ⟧ → ∀ S → Tm (T S)) →
          (∀ (@♭ S) → A Γ (T S) (λ γ → M γ S)) →
          A Γ (`∀ T) (λ γ → `Λ T (M γ))) →
    (H[] : ∀ (@♭ Γ) (@♭ T : Ty → Ty) (@♭ M : ⟦ Γ ⟧ → Tm (`∀ T)) (@♭ S) →
           A Γ (`∀ T) M →
           A Γ (T S) (λ γ → M γ % S)) →
    ∀ (@♭ Γ) (@♭ T) (@♭ t) →
    Tm-elim A HV Hλ H· HΛ H[] Γ (`∀ T) (λ γ → `Λ T (t γ)) ≡
    HΛ Γ T t (λ S → Tm-elim A HV Hλ H· HΛ H[] Γ (T S) (λ γ → t γ S))

postulate
  Tm-elim-[] : {l : Level}
    (A : (@♭ Γ : List Ty) → (@♭ T : Ty) →
         (@♭ t : ⟦ Γ ⟧ → Tm T) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ i) → A Γ (lookup Γ i) (λ γ → γ i)) →
    (Hλ : ∀ (@♭ Γ) (@♭ T S) (@♭ t : ⟦ Γ ⟧ → Tm T → Tm S) →
          A (T ∷ Γ) S (abs t) →
          A Γ (T —→ S) (λ γ → `λ t γ)) →
    (H· : ∀ (@♭ Γ) (@♭ T S) (@♭ M : ⟦ Γ ⟧ → Tm (T —→ S)) (@♭ N : ⟦ Γ ⟧ → Tm T) →
          A Γ (T —→ S) M → A Γ T N →
          A Γ S (λ γ → M γ · N γ)) →
    (HΛ : ∀ (@♭ Γ) (@♭ T : Ty → Ty) → (@♭ M : ⟦ Γ ⟧ → ∀ S → Tm (T S)) →
          (∀ (@♭ S) → A Γ (T S) (λ γ → M γ S)) →
          A Γ (`∀ T) (λ γ → `Λ T (M γ))) →
    (H[] : ∀ (@♭ Γ) (@♭ T : Ty → Ty) (@♭ M : ⟦ Γ ⟧ → Tm (`∀ T)) (@♭ S) →
           A Γ (`∀ T) M →
           A Γ (T S) (λ γ → M γ % S)) →
    ∀ (@♭ Γ) (@♭ T) (@♭ t) (@♭ S) →
    Tm-elim A HV Hλ H· HΛ H[] Γ (T S) (λ γ → t γ % S) ≡
    H[] Γ T t S (Tm-elim A HV Hλ H· HΛ H[] Γ (`∀ T) (λ γ → t γ))

{-# REWRITE Tm-elim-λ #-}
{-# REWRITE Tm-elim-Λ #-}
{-# REWRITE Tm-elim-[] #-}
