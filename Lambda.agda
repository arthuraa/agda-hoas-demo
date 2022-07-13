{-# OPTIONS --rewriting --prop #-}

module Lambda where

open import Agda.Primitive hiding (_⊔_)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product hiding (curry; uncurry)
open import Data.Fin
open import Data.Nat

open ≡-Reasoning

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

-- An n-ary product of terms, represented as a function from bounded naturals.
Λ^ : ℕ → Set
Λ^ n = Fin n → Λ

uncurry : ∀ {n} → (Λ^ n → Λ → Λ) → Λ^ (suc n) → Λ
uncurry f γ = f (λ x → γ (suc x)) (γ zero)

postulate
  Λ-elim : {l : Level}
    (A : ∀ (@♭ n) → @♭ (Λ^ n → Λ) → Set l) →
    (HV : ∀ (@♭ n) (@♭ v : Fin n) → A n (λ γ → γ v)) →
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
could be represented as the function λ γ → γ zero · γ (suc zero), where γ : Λ^
2.  By allowing the eliminator to handle open terms, we can traverse application
terms by uncurrying the underlying functions and adding an extra variable into
the "context", as we'll see shortly.

The other difference regarding Λ-elim is the ♭ modality that appears in many
arguments.  Roughly speaking, the modality ensures that the eliminator cannot be
applied to terms that have free variables of type Λ, which would render it
unsound.  Any variables of type Λ must be explicitly declared as functions
parameters, like we did in the type Λ^ n → Λ above.  We'll come back to this
point shortly; for now, it suffices to say that we can convert from ♭ variables
to regular ones, but not the other way around.

These two differences aside, the type of Λ-elim is not too surprising. It says
that, to compute a result A n t for some open term t : Λ^ n → Λ, it suffices to
do so for three kinds of terms, which correspond to the three "branch" arguments
HV, Hƛ and H·.  In the HV branch, we should produce a result for when the term
is a variable v, which is represented here by the corresponding projection
function (λ γ → γ v) : Λ^ n → Λ.  In the Hƛ and H· branches, we need to produce
a result when the term begins with an application or an abstraction, but we are
allowed to use the result of calling the eliminator recursively on each subterm.
Note how, in Hƛ, we perform a recursive call to uncurry t, which corresponds to
moving the variable bound by the abstraction into the context of free variables.

We can use Agda's custom rewrite rules to define how the eliminator computes.

-}

postulate
  Λ-elim-V :
    ∀ {l : Level} A HV Hƛ H· →
    ∀ (@♭ n) (@♭ v : Fin n) →
    Λ-elim {l} A HV Hƛ H· n (λ γ → γ v) ≡ HV n v

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

{-

To illustrate the use of Λ-elim, we can define a function that computes the
height of a term.  We add a successor for each constructor that we traverse,
taking the maximum of both heights when we traverse an application and returning
zero when we hit a variable.

-}

height : ∀ (@♭ n) (@♭ t : Λ^ n → Λ) → ℕ
height n t = Λ-elim (λ _ _ → ℕ) HV Hƛ H· n t
  where
  HV : _
  HV _ _ = 0

  Hƛ : _
  Hƛ n t height-t = suc height-t

  H· : _
  H· n t1 t2 height-t1 height-t2 = suc (height-t1 ⊔ height-t2)

{-

Here is one example showing how height computes on a term:

-}

ω : Λ
ω = (ƛ (λ x → x · x)) · (ƛ (λ x → x · x))

height-ω : height 0 (λ _ → ω) ≡ 3
height-ω = refl

{-

Before we move on to the rest of the development, a quick word about soundness.
As we have seen in the README, the possibility of doing case analysis on HOAS
terms can easily lead to inconsistencies in the theory.  This possibility is
ruled out here by our use of the ♭ modality.  Since we can go from ♭ variables
to regular ones, but not the other way around, we can only perform case analysis
using Λ-elim when defining functions of type @♭ Λ → Λ, but _not_ when defining
functions of type Λ → Λ.  This prevents us from writing the paradoxical term t
that we had defined earlier.

A bit more formally, we can validate the reasoning principles laid out here by a
presheaf model of type theory, as explained by Hofmann.  We consider the
following base category C.  The objects are natural numbers n, which model a
number of free variables.  A morphism of type n → m is a substitution of λ terms
with n free variables for the variables 0, …, m-1.  The identity morphism is
just the identity substitution, and composition is given by composition of
substitutions.  Like any presheaf category, PSh(C) is a model of type theory.
This model is equipped with a modality ♭, which maps a presheaf X to the
constant presheaf (♭X)(n) = X(0).  In PSh(C), we have an object Λ = Hom(-,1)
which we use to model the type of λ terms described above.  For general
category-theoretic reasons, we can show that the exponential object Λ^n → X is
just the presheaf m ↦ X(m + n).  In particular, ♭(Λ^n → Λ) is just the constant
presheaf over Λ(n) = Hom(n,1), which can be identified with the set of λ terms
with n free variables.  This implies that the abstraction term constructor has
the correct type (Λ → Λ) → Λ (since it binds one free variable).  It also
implies that the eliminator we defined is correct, since this is precisely the
eliminator that we would get for a usual well-scoped encoding of λ terms defined
as an inductive family.  (Indeed, as shown in DG.agda, the eliminator is enough
to establish that the HOAS encoding of λ terms is isomorphic to the more
conventional definition.)

We include here some auxliary definitions that we'll be useful later on. We
postulate functional extensionality so that we can prove the isomorphism
mentioned above.

-}

infixl 2 _▸_

-- Add a λ term to a tuple of terms
_▸_ : ∀ {n} → Λ^ n → Λ → Λ^ (suc n)
(γ ▸ t) zero = t
(γ ▸ t) (suc n) = γ n

curry : ∀ {n} → (Λ^ (suc n) → Λ) → Λ^ n → Λ → Λ
curry f γ t = f (γ ▸ t)

postulate
  funext : ∀ {l : Level} {A : Set l} {B : A → Set l} {f g : (x : A) → B x} →
    (∀ x → f x ≡ g x) →
    f ≡ g

uncurry-curry : ∀ {n} (f : Λ^ (suc n) → Λ) → uncurry (curry f) ≡ f
uncurry-curry {n} f = funext e₁
  where
  e₁ : ∀ γ → uncurry (curry f) γ ≡ f γ
  e₁ γ = begin
    uncurry (curry f) γ ≡⟨⟩
    curry f γ' (γ zero) ≡⟨⟩
    f (γ' ▸ γ zero) ≡⟨ cong f (funext e₂) ⟩
    f γ ∎
    where
    γ' : Λ^ n
    γ' x = γ (suc x)

    e₂ : ∀ x → (γ' ▸ γ zero) x ≡ γ x
    e₂ zero = refl
    e₂ (suc x) = refl
