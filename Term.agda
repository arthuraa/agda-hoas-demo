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

Term-cong1 :
  ∀ {l  : Level} →
  ∀ (A  : Term → Set l) →
  ∀ (Hƛ : ∀ (t : Term → Term) → (∀ x → A x → A (t x)) → A (ƛ t)) →
  ∀ (H· : ∀ t1 t2 → A t1 → A t2 → A (t1 · t2)) →
  ∀ {@♭ Γ} (@♭ t : ⟦ Γ ⟧ → Term) →
  ∀ γ → (∀ i → A (lookup γ i)) → A (t γ)
Term-cong1 {l} A Hƛ H· t = Term-elim A' HV' Hƛ' H·' _ t
  where
  A' : ∀ (@♭ Γ) (@♭ A : ⟦ Γ ⟧ → Term) → Set l
  A' Γ t = ∀ γ → (∀ i → A (lookup γ i)) → A (t γ)

  HV' : _
  HV' Γ x γ A-γ = A-γ x

  Hƛ' : _
  Hƛ' Γ t IH γ A-γ = Hƛ (t γ) (λ x A-x → IH (x ∷ γ) (A-x' x A-x))
    where
    A-x' : ∀ x → A x → ∀ i → A (lookup (x ∷ γ) i)
    A-x' x A-x zero = A-x
    A-x' x A-x (suc i) = A-γ i

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
  ∀ γ1 γ2 → (∀ i → A (lookup γ1 i) (lookup γ2 i)) → A (t γ1) (t γ2)
Term-cong2 {l} A Hƛ H· t = Term-elim A' HV' Hƛ' H·' _ t
  where
  A' : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term) → Set l
  A' Γ t = ∀ γ1 γ2 → (∀ i → A (lookup γ1 i) (lookup γ2 i)) →
           A (t γ1) (t γ2)

  HV' : _
  HV' Γ x γ1 γ2 A-γ = A-γ x

  Hƛ' : _
  Hƛ' Γ t IH γ1 γ2 A-γ =
    Hƛ (t γ1) (t γ2) (λ x A-x → IH (x ∷ γ1) (x ∷ γ2) (A-x' x A-x))
    where
    A-x' : ∀ x → A x x → ∀ i → A (lookup (x ∷ γ1) i) (lookup (x ∷ γ2) i)
    A-x' x A-x zero = A-x
    A-x' x A-x (suc i) = A-γ i

  H·' : _
  H·' Γ t1 t2 IH1 IH2 γ1 γ2 A-γ =
    H· _ _ _ _ (IH1 γ1 γ2 A-γ) (IH2 γ1 γ2 A-γ)
