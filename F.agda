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
open import Ctx
open import Ty

infix 2 `λ_
infix 2 `Λ
infixl 1 _·_
infixl 1 _%_

postulate `Tm : Ty → Type

Tm : Ty → Set
Tm τ = ⟦ `Tm τ ⟧ₜ

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

_%_ : {T : Ty → Ty} → Tm (`∀ T) → (S : Ty) → Tm (T S)
M % S = fold-Tm (QuoteTm._%_ M S)

abs : {Γ : Ctx} → {T S : ⟦ Γ ⟧ → Ty} →
  ((γ : ⟦ Γ ⟧) → Tm (T γ) → Tm (S γ)) →
  (γ : ⟦ Γ ,, (λ γ → `Tm (T γ)) ⟧) → Tm (S (π₁ γ))
abs t γ = t (π₁ γ) (π₂ γ)

postulate
  Tm-elim : {l : Level}
    (A : (@♭ Γ : Ctx) → (@♭ T : ⟦ Γ ⟧ → Ty) →
         (@♭ t : (γ : ⟦ Γ ⟧) → Tm (T γ)) → Set l) →
    (HV : ∀ (@♭ Γ Δ) (@♭ T : ⟦ Δ ⟧ → Ty)
          (@♭ v : Var Δ (λ δ → `Tm (T δ)) Γ) →
          A Γ _ ⟦ v ⟧ᵥ) →
    (Hλ : ∀ (@♭ Γ) (@♭ T S : ⟦ Γ ⟧ → Ty)
          (@♭ M : ∀ γ → Tm (T γ) → Tm (S γ)) →
          A _ _ (abs M) →
          A Γ (λ γ → T γ —→ S γ) (λ γ → `λ M γ)) →
    (H· : ∀ (@♭ Γ) (@♭ T S : ⟦ Γ ⟧ → Ty)
          (@♭ M : ∀ γ → Tm (T γ —→ S γ))
          (@♭ N : ∀ γ → Tm (T γ)) →
          A _ _ M → A _ _ N →
          A _ _ (λ γ → M γ · N γ)) →
    (HΛ : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty) →
          (@♭ M : ∀ γ S → Tm (T γ S)) →
          A _ _ (λ γ → M (π₁ γ) (π₂ γ)) →
          A _ _ (λ γ → `Λ (T γ) (M γ))) →
    (H[] : ∀ (@♭ Γ) (@♭ T : ⟦ Γ ⟧ → Ty → Ty)
           (@♭ M : ∀ γ → Tm (`∀ T γ)) (@♭ S : ⟦ Γ ⟧ → Ty) →
           A _ _ M →
           A _ _ (λ γ → M γ % S γ)) →
    ∀ (@♭ Γ) (@♭ T) (@♭ M) → A Γ T M

postulate
  Tm-elim-V :
    ∀ {l : Level} A HV Hλ H· HΛ H[] →
    ∀ (@♭ Γ Δ) (@♭ T : ⟦ Δ ⟧ → Ty) (@♭ v : Var Δ (λ δ → `Tm (T δ)) Γ) →
    Tm-elim {l} A HV Hλ H· HΛ H[] Γ _ ⟦ v ⟧ᵥ ≡ HV Γ Δ T v

postulate
  Tm-elim-λ :
    ∀ {l : Level} A HV Hλ H· HΛ H[] →
    ∀ (@♭ Γ T S M) →
    Tm-elim {l} A HV Hλ H· HΛ H[] Γ _ (λ γ → `λ M γ) ≡
    Hλ Γ T S M (Tm-elim A HV Hλ H· HΛ H[] _ _ (abs M))

postulate
  Tm-elim-· :
    ∀ {l : Level} A HV Hλ H· HΛ H[] →
    ∀ (@♭ Γ T S M N) →
    Tm-elim {l} A HV Hλ H· HΛ H[] Γ _ (λ γ → M γ · N γ) ≡
    H· Γ T S M N (Tm-elim A HV Hλ H· HΛ H[] Γ _ M) (Tm-elim A HV Hλ H· HΛ H[] Γ _ N)


postulate
  Tm-elim-Λ :
    ∀ {l : Level} A HV Hλ H· HΛ H[] →
    ∀ (@♭ Γ) (@♭ T) (@♭ M) →
    Tm-elim {l} A HV Hλ H· HΛ H[] Γ (λ γ → `∀ T γ) (λ γ → `Λ (T γ) (M γ)) ≡
    HΛ Γ T M (Tm-elim A HV Hλ H· HΛ H[] (Γ ,, λ _ → `Ty) _ (λ γ → M (π₁ γ) (π₂ γ)))

postulate
  Tm-elim-[] :
    ∀ {l : Level} A HV Hλ H· HΛ H[] →
    ∀ (@♭ Γ) (@♭ T) (@♭ M) (@♭ S) →
    Tm-elim {l} A HV Hλ H· HΛ H[] Γ _ (λ γ → M γ % S γ) ≡
    H[] Γ T M S (Tm-elim A HV Hλ H· HΛ H[] Γ _ M)


{-# REWRITE Tm-elim-V #-}
{-# REWRITE Tm-elim-λ #-}
{-# REWRITE Tm-elim-· #-}
{-# REWRITE Tm-elim-Λ #-}
{-# REWRITE Tm-elim-[] #-}
