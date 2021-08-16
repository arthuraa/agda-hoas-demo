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

postulate `Term : Type

Term : Set
Term = ⟦ `Term ⟧ₜ

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

abs : {Γ : Ctx} → (⟦ Γ ⟧ → Term → Term) → ⟦ Γ ,, (λ _ → `Term) ⟧ → Term
abs t γ = t (π₁ γ) (π₂ γ)

postulate
  Term-elim : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ Δ) (@♭ v : Var Γ (λ _ → `Term) Δ) → A Δ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (Γ ,, (λ _ → `Term)) (abs t) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term) → A Γ t


postulate
  Term-elim-V : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ Δ) (@♭ v : Var Γ (λ _ → `Term) Δ) → A Δ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (Γ ,, (λ _ → `Term)) (abs t) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ Δ) (@♭ v : Var Γ (λ _ → `Term) Δ) →
    Term-elim A HV Hƛ H· Δ ⟦ v ⟧ᵥ ≡ HV Γ Δ v

postulate
  Term-elim-ƛ : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ Δ) (@♭ v : Var Γ (λ _ → `Term) Δ) → A Δ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (Γ ,, (λ _ → `Term)) (abs t) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
    Term-elim A HV Hƛ H· Γ (λ γ → ƛ (t γ)) ≡
    Hƛ Γ t (Term-elim A HV Hƛ H· (Γ ,, (λ _ → `Term)) (abs t))

postulate
  Term-elim-· : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ Δ) (@♭ v : Var Γ (λ _ → `Term) Δ) → A Δ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
      A (Γ ,, (λ _ → `Term)) (abs t) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
    Term-elim A HV Hƛ H· Γ (λ γ → t1 γ · t2 γ) ≡
    H· Γ t1 t2 (Term-elim A HV Hƛ H· Γ t1) (Term-elim A HV Hƛ H· Γ t2)

{-# REWRITE Term-elim-V #-}
{-# REWRITE Term-elim-ƛ #-}
{-# REWRITE Term-elim-· #-}

Term-cong1 :
  ∀ {l  : Level} →
  ∀ (A  : Term → Set l) →
  ∀ (Hƛ : ∀ (t : Term → Term) → (∀ x → A x → A (t x)) → A (ƛ t)) →
  ∀ (H· : ∀ t1 t2 → A t1 → A t2 → A (t1 · t2)) →
  ∀ {@♭ Γ} (@♭ t : ⟦ Γ ⟧ → Term) →
  ∀ γ → (∀ Δ (v : Var Δ _ Γ) → A (⟦ v ⟧ᵥ γ)) → A (t γ)
Term-cong1 {l} A Hƛ H· t = Term-elim A' HV' Hƛ' H·' _ t
  where
  A' : ∀ (@♭ Γ) (@♭ A : ⟦ Γ ⟧ → Term) → Set l
  A' Γ t = ∀ γ → (∀ Δ (v : Var Δ _ Γ) → A (⟦ v ⟧ᵥ γ)) → A (t γ)

  HV' : _
  HV' Γ Δ x γ A-γ = A-γ Γ x

  Hƛ' : _
  Hƛ' Γ t IH γ A-γ = Hƛ (t γ) (λ x A-x → IH (γ ,, x) (A-γ' x A-x))
    where
    A-γ' : ∀ x → A x → ∀ Δ (v : Var Δ _ (Γ ,, (λ _ → `Term))) → A (⟦ v ⟧ᵥ (γ ,, x))
    A-γ' x A-x .Γ zero = A-x
    A-γ' x A-x Δ (suc v) = A-γ Δ v

  H·' : _
  H·' Γ t1 t2 IH1 IH2 γ A-γ = H· _ _ (IH1 γ A-γ) (IH2 γ A-γ)

Term-cong2 :
  ∀ {l  : Level} →
  ∀ (A  : Term → Term → Set l) →
  ∀ (Hƛ : ∀ (t1 t2 : Term → Term) →
          (∀ x → A x x → A (t1 x) (t2 x)) → A (ƛ t1) (ƛ t2)) →
  ∀ (H· : ∀ t11 t12 t21 t22 → A t11 t21 → A t12 t22 →
          A (t11 · t12) (t21 · t22)) →
  ∀ {@♭ Γ} (@♭ t : ⟦ Γ ⟧ → Term) →
  ∀ γ1 γ2 → (∀ Δ (v : Var Δ _ Γ) → A (⟦ v ⟧ᵥ γ1) (⟦ v ⟧ᵥ γ2)) → A (t γ1) (t γ2)
Term-cong2 {l} A Hƛ H· t = Term-elim A' HV' Hƛ' H·' _ t
  where
  A' : ∀ (@♭ Γ) (@♭ A : ⟦ Γ ⟧ → Term) → Set l
  A' Γ t = ∀ γ1 γ2 → (∀ Δ (v : Var Δ _ Γ) → A (⟦ v ⟧ᵥ γ1) (⟦ v ⟧ᵥ γ2)) →
           A (t γ1) (t γ2)

  HV' : _
  HV' Γ Δ x γ1 γ2 A-γ = A-γ Γ x

  Hƛ' : _
  Hƛ' Γ t IH γ1 γ2 A-γ = Hƛ (t γ1) (t γ2)
    (λ x A-x → IH (γ1 ,, x) (γ2 ,, x) (A-γ' x A-x))
    where
    A-γ' : ∀ x → A x x → ∀ Δ (v : Var Δ _ (Γ ,, (λ _ → `Term))) →
           A (⟦ v ⟧ᵥ (γ1 ,, x)) (⟦ v ⟧ᵥ (γ2 ,, x))
    A-γ' x A-x .Γ zero = A-x
    A-γ' x A-x Δ (suc v) = A-γ Δ v

  H·' : _
  H·' Γ t1 t2 IH1 IH2 γ1 γ2 A-γ = H· _ _ _ _ (IH1 γ1 γ2 A-γ) (IH2 γ1 γ2 A-γ)
