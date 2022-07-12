{-# OPTIONS --rewriting --prop #-}

module Lambda where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Fin
open import Data.Vec
open import Data.Nat

{-

This file describes the syntax of λ terms with higher-order abstract syntax and
its associated elimination principles.  We begin by postulating the existence of
a type Λ for classifying λ terms.  This type comes with two constructors _·_ and
ƛ_, which correspond to application and λ abstraction.  To make the definition
more convenient to work with, the definition uses an auxiliary data type Λ' that
injects into Λ via the function ⟨_⟩.  This allows us to reason about these
constructors as if they came from a regular Agda data type.

-}

infixl 7 _·_
infix 6 ƛ_

postulate Λ : Set

module Internal where

  data Λ' : Set where
    _·_ : Λ → Λ → Λ'
    ƛ_ : (Λ → Λ) → Λ'

postulate ⟨_⟩ : Internal.Λ' → Λ
{-# INJECTIVE ⟨_⟩ #-}

_·_ : Λ → Λ → Λ
t1 · t2 = ⟨ Internal._·_ t1 t2 ⟩

ƛ_ : (Λ → Λ) → Λ
ƛ_ t = ⟨ Internal.ƛ t ⟩

{-

To illustrate this last point, here is how we can show that _·_ is injective and
disjoint from ƛ_, using just regular equality reasoning.

-}

·-injective : (t₁ t₂ t₁' t₂' : Λ) → t₁ · t₂ ≡ t₁' · t₂' →
  (t₁ ≡ t₁') × (t₂ ≡ t₂')
·-injective t₁ t₂ .t₁ .t₂ refl = ( refl , refl )

·-ƛ-disjoint : (t₁ t₂ : Λ) (t : Λ → Λ) → t₁ · t₂ ≡ ƛ t → ⊥
·-ƛ-disjoint t₁ t₂ t ()

{-

To manipulate λ terms, we need to postulate a case analysis principle for Λ.
Here it is:

-}

Λ^ : ℕ → Set
Λ^ zero = ⊤
Λ^ (suc Γ) = Λ^ Γ × Λ

⟦_⟧ : {n : ℕ} → Fin n → Λ^ n → Λ
⟦ zero ⟧ = proj₂
⟦ suc x ⟧ = λ γ → ⟦ x ⟧ (proj₁ γ)

postulate
  Λ-elim : {l : Level}
    (A : ∀ (@♭ n) → @♭ (Λ^ n → Λ) → Set l) →
    (HV : ∀ (@♭ n) (@♭ v : Fin n) → A n ⟦ v ⟧) →
    (Hƛ : ∀ (@♭ n) (@♭ t : Λ^ n → Λ → Λ) → A (suc n) (uncurry t) →
      A n (λ γ → ƛ t γ)) →
    (H· : ∀ (@♭ n) (@♭ t1 t2 : Λ^ n → Λ) →
      A n t1 → A n t2 → A n (λ γ → t1 γ · t2 γ)) →
    ∀ (@♭ n) (@♭ t : Λ^ n → Λ) → A n t

{-

This definition looks a bit different from elimination principles for usual data
types.  First, the type tells us that the eliminator applies to not to
individual Λ terms, but to _functions_ of type Λ^ n → Λ.  We use such functions
to represent terms with n free variables.  For example, an open term such as x y
could be represented as the function λ γ → ⟦ zero ⟧ γ · ⟦ suc zero ⟧ γ, where γ
: Λ^ 2.  By allowing the eliminator to handle open terms, we can traverse
application terms by uncurrying the underlying functions and adding an extra
variable into the "context", as we'll see shortly.

The other difference regarding Λ-elim is the ♭ modality that appears in many
arguments.  Roughly speaking, the modality ensures that the eliminator cannot be
applied to terms that have free variables of type Λ, which would render it
unsound.  Any variables of type Λ must be explicitly declared as functions
parameters, like we did in the type Λ^ n → Λ above.  We'll come back to this
modality shortly; for now, it suffices to say that we can convert from ♭
variables to regular ones, but not the other way around.

These two differences aside, the type of Λ-elim is not too surprising. It says
that, to compute a result A n t for some open term t : Λ^ n → Λ, it suffices to
do so for three kinds of terms, which correspond to the three "branch" arguments
HV, Hƛ and H·.  In the HV branch, we should produce a result for when the term
is a variable v, which is represented here by the corresponding projection
function ⟦ v ⟧ : Λ^ n → Λ.  In the Hƛ and H· branches, we need to produce a
result when the term begins with an application or an abstraction, but we are
allowed to use the result of calling the eliminator recursively on each subterm.
Note how, in Hƛ, we perform a recursive call to uncurry t, which corresponds to
moving the variable bound by the abstraction into the context of free variables.

We can use Agda's custom rewrite rules to describe how the eliminator computes.
The rules are not so well behaved because they are not confluent: for example,
if v is 1, then ⟦ v ⟧ reduces to λ γ → proj₂ (proj₁ γ), which is not covered by
any of the rewrite rules below.  Nevertheless, the rules are good enough to
cover the examples we'll consider here, so we'll stick to them for simplicity.

-}

postulate
  Λ-elim-V :
    ∀ {l : Level} A HV Hƛ H· →
    ∀ (@♭ n) (@♭ v : Fin n) →
    Λ-elim {l} A HV Hƛ H· n ⟦ v ⟧ ≡ HV n v

postulate
  Λ-elim-ƛ :
    ∀ {l : Level} A HV Hƛ H· →
    ∀ (@♭ n) (@♭ t : Λ^ n → Λ → Λ) →
    Λ-elim {l} A HV Hƛ H· n (λ γ → ƛ t γ) ≡
    Hƛ n _ (Λ-elim A HV Hƛ H· (suc n) (uncurry t))

postulate
  Λ-elim-· :
    ∀ {l : Level} A HV Hƛ H· →
    ∀ (@♭ n) (@♭ t1 t2 : Λ^ n → Λ) →
    Λ-elim {l} A HV Hƛ H· n (λ γ → t1 γ · t2 γ) ≡
    H· n t1 t2 (Λ-elim A HV Hƛ H· n t1) (Λ-elim A HV Hƛ H· n t2)

{-# REWRITE Λ-elim-V #-}
{-# REWRITE Λ-elim-ƛ #-}
{-# REWRITE Λ-elim-· #-}
