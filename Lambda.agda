{-# OPTIONS --rewriting --prop #-}

module Lambda where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Fin
open import Data.Vec
open import Data.Nat

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

Ctx : Set
Ctx = ℕ

⟦_⟧ : Ctx → Set
⟦ Γ ⟧ = Vec Term Γ

Var : Ctx → Set
Var = Fin

abs : {Γ : ℕ} → (⟦ Γ ⟧ → Term → Term) → ⟦ suc Γ ⟧ → Term
abs t γ = t (tail γ) (head γ)

⟦_⟧ᵥ : {Γ : ℕ} → Var Γ → ⟦ Γ ⟧ → Term
⟦ v ⟧ᵥ γ = lookup γ v

postulate
  Term-elim : {l : Level}
    (A : ∀ (@♭ Γ) → @♭ (⟦ Γ ⟧ → Term) → Set l) →
    (HV : ∀ (@♭ Γ) (@♭ v : Fin Γ) → A Γ ⟦ v ⟧ᵥ) →
    (Hƛ : ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) → A (suc Γ) (abs t) →
      A Γ (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
      A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term) → A Γ t


postulate
  Term-elim-V :
    ∀ {l : Level} A HV Hƛ H· →
    ∀ (@♭ Γ)  (@♭ v : Var Γ) →
    Term-elim {l} A HV Hƛ H· Γ ⟦ v ⟧ᵥ ≡ HV Γ v

postulate
  Term-elim-ƛ :
    ∀ {l : Level} A HV Hƛ H· →
    ∀ (@♭ Γ) (@♭ t : ⟦ Γ ⟧ → Term → Term) →
    Term-elim {l} A HV Hƛ H· Γ (λ γ → ƛ (t γ)) ≡
    Hƛ Γ t (Term-elim A HV Hƛ H· (suc Γ) (abs t))

postulate
  Term-elim-· :
    ∀ {l : Level} A HV Hƛ H· →
    ∀ (@♭ Γ) (@♭ t1 t2 : ⟦ Γ ⟧ → Term) →
    Term-elim {l} A HV Hƛ H· Γ (λ γ → t1 γ · t2 γ) ≡
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
  ∀ γ → (∀ (v : Var Γ) → A (⟦ v ⟧ᵥ γ)) → A (t γ)
Term-cong1 {l} A Hƛ H· t = Term-elim A' HV' Hƛ' H·' _ t
  where
  A' : ∀ (@♭ Γ) (@♭ A : ⟦ Γ ⟧ → Term) → Set l
  A' Γ t = ∀ γ → (∀ (v : Var Γ) → A (⟦ v ⟧ᵥ γ)) → A (t γ)

  HV' : _
  HV' Γ x γ A-γ = A-γ x

  Hƛ' : _
  Hƛ' Γ t IH γ A-γ = Hƛ (t γ) (λ x A-x → IH (x ∷ γ) (A-γ' x A-x))
    where
    A-γ' : ∀ x → A x → ∀ (v : Var (suc Γ)) → A (⟦ v ⟧ᵥ (x ∷ γ))
    A-γ' x A-x zero = A-x
    A-γ' x A-x (suc v) = A-γ v

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
  ∀ γ1 γ2 → (∀ (v : Var Γ) → A (⟦ v ⟧ᵥ γ1) (⟦ v ⟧ᵥ γ2)) → A (t γ1) (t γ2)
Term-cong2 {l} A Hƛ H· t = Term-elim A' HV' Hƛ' H·' _ t
  where
  A' : ∀ (@♭ Γ) (@♭ A : ⟦ Γ ⟧ → Term) → Set l
  A' Γ t = ∀ γ1 γ2 → (∀ (v : Var Γ) → A (⟦ v ⟧ᵥ γ1) (⟦ v ⟧ᵥ γ2)) →
           A (t γ1) (t γ2)

  HV' : _
  HV' Γ x γ1 γ2 A-γ = A-γ x

  Hƛ' : _
  Hƛ' Γ t IH γ1 γ2 A-γ = Hƛ (t γ1) (t γ2)
    (λ x A-x → IH (x ∷ γ1) (x ∷ γ2) (A-γ' x A-x))
    where
    A-γ' : ∀ x → A x x → ∀ (v : Var (suc Γ)) →
           A (⟦ v ⟧ᵥ (x ∷ γ1)) (⟦ v ⟧ᵥ (x ∷ γ2))
    A-γ' x A-x zero = A-x
    A-γ' x A-x (suc v) = A-γ v

  H·' : _
  H·' Γ t1 t2 IH1 IH2 γ1 γ2 A-γ = H· _ _ _ _ (IH1 γ1 γ2 A-γ) (IH2 γ1 γ2 A-γ)
