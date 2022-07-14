{-# OPTIONS --rewriting --prop #-}

module Par where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Product hiding (∃; ∃!; uncurry; curry)
open import Data.Sum
open import Data.Nat
open import Data.Fin hiding (_+_; cast)
open import Flat
open import Lambda

{-

This case study demonstrates how we can reason about HOAS terms in Agda.  We are
going to prove that parallel reduction in the λ-calculus satisfies the diamond
property: if a term t parallel reduces to two other terms t₁ and t₂, then both
terms parallel reduce to another term t'.

Our development follows the proof of Masako Takahashi (Parallel Reductions in
λ-Calculus, Information and Computation 118(1), 1995), and is inspired by Dan
Licata's Twelf development of the same proof
(http://twelf.org/wiki/Church-Rosser_via_complete_development).

We begin by defining the parallel reduction relation on λ terms.  Note how the
⇒-ƛ and ⇒-β cases express that a reduction happens under a binder: we simply
assume that the bodies of the abstractions are related after we plug in some
arbitrary fresh variable x : Λ.  This style of specification is quite common in
HOAS developments.

-}

infix 3 _⇒_

data _⇒_ : Λ → Λ → Set where

  ⇒-refl : ∀ t → t ⇒ t

  ⇒-· : ∀ {t1 t1' t2 t2'} →
    t1 ⇒ t1' →
    t2 ⇒ t2' →
    t1 · t2 ⇒ t1' · t2'

  ⇒-ƛ : ∀ {t t'} →
    (∀ (x : Λ) → t x ⇒ t' x) →
    ƛ t ⇒ ƛ t'

  ⇒-β : ∀ {t1 t1' : Λ → Λ} {t2 t2'} →
    (∀ (x : Λ) → t1 x ⇒ t1' x) →
    t2 ⇒ t2' →
    (ƛ t1) · t2 ⇒ t1' t2'

{-

Although the definition of this type does not pose any issues, its default
eliminator is too weak to be useful.  To see why, suppose that we have two terms
t and t' with n free variables, represented as functions of type Λ^ n → Λ.  If t
γ ⇒ t' γ for every γ : Λ^ n, we would like to conclude that the last rule used
to show this relation does not depend on γ.  Indeed, in a traditional paper
proof, γ would correspond to object-level variables, and it does not make sense
to test what the variable actually is to choose which rule to apply.  This type
of reasoning is not possible with the eliminator we would obtain, because it
requires eliminating an arbitrary _function_ of type ∀ γ → t γ ⇒ t' γ, and the
default one only applies to types of the form t ⇒ t'.  We remedy this by adding
the eliminator we need as a postulate.

-}

postulate
  ⇒-elim :
    ∀ {l : Level} →
    ∀ (A : ∀ (@♭ n) → (@♭ t1 t2 : Λ^ n → Λ) → Set l) →
    ∀ (HR : ∀ (@♭ n) (@♭ t) → A n t t) →
    ∀ (H· : ∀ (@♭ n) (@♭ t1 t1' t2 t2') → A n t1 t1' → A n t2 t2' →
            A n (λ γ → t1 γ · t2 γ) (λ γ → t1' γ · t2' γ)) →
    ∀ (Hƛ : ∀ (@♭ n) →
            ∀ (@♭ t t' : Λ^ n → Λ → Λ) →
            A (suc n) (uncurry t) (uncurry t') →
            A n (λ γ → ƛ t γ) (λ γ → ƛ t' γ)) →
    ∀ (Hβ : ∀ (@♭ n) →
            ∀ (@♭ t1 t1' : Λ^ n → Λ → Λ) →
            ∀ (@♭ t2 t2') →
            A (suc n) (uncurry t1) (uncurry t1') →
            A n t2 t2' →
            A n (λ γ → (ƛ t1 γ) · t2 γ) (λ γ → t1' γ (t2' γ))) →
    ∀ (@♭ n t t') →
    ∀ (@♭ p : ∀ γ → t γ ⇒ t' γ) → A n t t'

{-

We can notice similarities with the definition of Λ-elim given earlier.  All λ
terms and proofs of parallel reduction are declared under the ♭ modality to
guarantee soundness.

As a warm-up exercise, we are going to show that parallel reduction is
compatible with substitution.  The first result along those lines, ⇒-subst-refl,
says that we can reduce any number of subterms of a term.  If we have an open
term t1 : Λ^ n → Λ, and two sequences of terms γ2 and γ2' that are pointwise
related by ⇒, then t γ2 ⇒ t γ2'.  The proof follows by induction on t1, using
Λ-elim.

-}

infixl 3 _⇒ₛ_

_⇒ₛ_ : ∀ {n} (γ γ' : Λ^ n) → Set
_⇒ₛ_ γ γ' = ∀ v → γ v ⇒ γ' v

infixl 2 _▸ₛ_

_▸ₛ_ : ∀ {n} {γ γ' : Λ^ n} {x x' : Λ} →
        γ ⇒ₛ γ' →
        x ⇒  x' →
        (γ ▸ x) ⇒ₛ (γ' ▸ x')
_▸ₛ_ ⇒-γ ⇒-x zero = ⇒-x
_▸ₛ_ ⇒-γ ⇒-x (suc v) = ⇒-γ v

⇒-subst-refl :
  ∀ (@♭ n) →
  ∀ (@♭ t1 : Λ^ n → Λ) →
  ∀ (γ2 γ2' : Λ^ n) →
  ∀ (p2 : γ2 ⇒ₛ γ2') →
  t1 γ2 ⇒ t1 γ2'
⇒-subst-refl n t1 = Λ-elim A HV Hƛ H· n t1
  where
  A : _
  A n t = (γ2 γ2' : Λ^ n) (p2 : γ2 ⇒ₛ γ2') → t γ2 ⇒ t γ2'

  HV : _
  HV n v γ2 γ2' p2 = p2 v

  Hƛ : _
  Hƛ n t IH γ2 γ2' p2 =
    ⇒-ƛ (λ x → IH (γ2 ▸ x) (γ2' ▸ x) (p2 ▸ₛ ⇒-refl x))

  H· : _
  H· n t1 t2 IH1 IH2 γ2 γ2' p2 = ⇒-· (IH1 γ2 γ2' p2) (IH2 γ2 γ2' p2)

{-

The next result, ⇒-subst, is a strengthening of the previous one.  In addition
to allowing the terms γ2 to reduce to γ2', we also allow t1 to reduce to some
t1' before plugging in the reduced values γ2'.  This time, the proof proceeds by
induction on the proof of reduction for t1 and t1'.  This is one place where we
need ⇒-elim to eliminate a function of the form ∀ γ → t1 γ ⇒ t1' γ rather than a
single proof of redution.  We need the function to state that t1 reduces.

-}

⇒-subst :
  ∀ (@♭ n) →
  ∀ (@♭ t1 t1' : Λ^ n → Λ) →
  ∀ (@♭ p1 : ∀ γ → t1 γ ⇒ t1' γ) →
  ∀ (γ2 γ2' : Λ^ n) →
  ∀ (p2 : γ2 ⇒ₛ γ2') →
  t1 γ2 ⇒ t1' γ2'
⇒-subst n t1 t1' p1 =
  ⇒-elim A HR H· Hƛ Hβ n t1 t1' p1
  where
  A : _
  A n t1 t1' = (γ2 γ2' : Λ^ n) (p2 : γ2 ⇒ₛ γ2') → t1 γ2 ⇒ t1' γ2'

  HR : _
  HR n t1 = ⇒-subst-refl n t1

  H· : _
  H· n t11 t11' t12 t12' IH1 IH2 γ2 γ2' p2 =
    ⇒-· (IH1 γ2 γ2' p2) (IH2 γ2 γ2' p2)

  Hƛ : _
  Hƛ n t1 t1' IH γ2 γ2' p2 =
    ⇒-ƛ (λ x → IH (γ2 ▸ x) (γ2' ▸ x) (p2 ▸ₛ ⇒-refl x))

  Hβ : _
  Hβ n t11 t11' t12 t12' IH1 IH2 γ2 γ2' p2 =
    ⇒-β (λ x → IH1 (γ2 ▸ x) (γ2' ▸ x) (p2 ▸ₛ ⇒-refl x))
        (IH2 γ2 γ2' p2)

{-

Now, let us shift gears and look at the proof of complete development itself.
The idea is to define a function diag on λ terms such that t' ⇒ diag t whenever
t ⇒ t'.  Since diag t does not depend on t', if we have some diverging reduction
t ⇒ t'', we can make t' and t'' meet on diag t.  For convenience, the return
type of diag won't be Λ, but the type Res n, Res which will make it easier to
tell whether its result is an abstraction or not.  We can convert from Res n to
a function Λ^ n → Λ with the term-of-res function.

Notice the behavior of diag when reducing an application t1 · t2 (H·), which is
defined in the res-· function.  If diag t1 is not an abstraction, which
corresponds to the inj₁ case of Res, the resulting term is another application.
But if diag t1 is an abstraction, we plug in diag t2 in its body.

-}

Res : ℕ → Set
Res n = (Λ^ n → Λ) ⊎ (Λ^ n → Λ → Λ)

term-of-res : ∀ {n} → Res n → Λ^ n → Λ
term-of-res (inj₁ t) = t
term-of-res (inj₂ t) γ = ƛ (t γ)

res-ƛ : ∀ {n} → Res (suc n) → Res n
res-ƛ t = inj₂ (curry (term-of-res t))

res-· : ∀ {n} → Res n → Res n → Res n
res-· (inj₁ t1) t2 = inj₁ (λ γ → t1 γ · term-of-res t2 γ)
res-· (inj₂ t1) t2 = inj₁ (λ γ → t1 γ (term-of-res t2 γ))

diag : ∀ {@♭ n} (@♭ t : Λ^ n → Λ) → Res n
diag t =
  Λ-elim _ HV Hƛ H· _ t
  where
  HV : _
  HV n x = inj₁ (λ γ → γ x)

  Hƛ : _
  Hƛ n t diag-t = res-ƛ diag-t

  H· : _
  H· n t1 t2 diag-t1 diag-t2 = res-· diag-t1 diag-t2

{-

To prove that diag is correct, we use the following predicate diag-spec.  As
shown in the lemma diag-term-of-res, the predicate roughly says that one open
term can reduce to another.  However, this alternative definition also keeps
track of whether the result of diag is an abstraction or not, which makes it
easier to reason by cases.

-}

data diag-spec {n} (t : Λ^ n → Λ) : Res n → Set where
  inj₁ : ∀ {t'} → (∀ γ → t γ ⇒ t' γ) → diag-spec t (inj₁ t')

  inj₂ : ∀ {t₀ t' : Λ^ n → Λ → Λ} →
         t ≡ (λ γ → ƛ t₀ γ) →
         (∀ γ x → t₀ γ x ⇒ t' γ x) →
         diag-spec t (inj₂ t')

diag-term-of-res : ∀ {n t t'} → diag-spec {n} t t' →
                   ∀ γ → t γ ⇒ term-of-res t' γ
diag-term-of-res (inj₁ p) γ = p γ
diag-term-of-res (inj₂ refl p) γ = ⇒-ƛ (p γ)

{-

This predicate is preserved by the functions res-ƛ and res-· used in the
definition of diag.  As a result, we can prove ⇒-diag, which states that t is
related to diag t.  The proof follows by induction on t.  Notice that, since
diag is defined using Λ-elim, this proof relies on the computational behavior of
Λ-elim.

-}

diag-res-ƛ : ∀ {n t t'} →
             diag-spec {suc n} t t' →
             diag-spec {n} (λ γ → ƛ (curry t γ)) (res-ƛ t')
diag-res-ƛ p = inj₂ refl (λ γ x → diag-term-of-res p (γ ▸ x))

diag-res-· : ∀ {n t1 t1' t2 t2'} →
             diag-spec {n} t1 t1' →
             diag-spec {n} t2 t2' →
             diag-spec (λ γ → t1 γ · t2 γ) (res-· t1' t2')
diag-res-· (inj₁ p1) p2 = inj₁ (λ γ → ⇒-· (p1 γ) (diag-term-of-res p2 γ))
diag-res-· (inj₂ refl p1) p2 = inj₁ (λ γ → ⇒-β (p1 γ) (diag-term-of-res p2 γ))


⇒-diag : ∀ {@♭ n} →
         ∀ (@♭ t : Λ^ n → Λ) →
         diag-spec t (diag t)
⇒-diag {n} t =
  -- Removing this type annotation causes type checking to diverge
  Λ-elim (λ n t → diag-spec t (diag t)) HV Hƛ H· n t
  where

  HV : _
  HV n v = inj₁ (λ γ → ⇒-refl (γ v))

  Hƛ : _
  Hƛ n t IH = diag-res-ƛ IH

  H· : _
  H· n t1 t2 IH1 IH2 = diag-res-· IH1 IH2

{-

Next, we show the triangle lemma, which says that any reduction t ⇒ t' can be
complete to t' ⇒ diag t.  The most intricate part of the proof is the diag-β
lemma, which handles the case where the reduction t ⇒ t' corresponds to the ⇒-β
rule.  The issue is that diag-β needs to invoke ⇒-subst twice.  Since ⇒-subst is
defined by ⇒-elim, the proofs of reduction that are feed into it need to be
marked with ♭, which means that this modality needs to be propagated to the
arguments of diag-β itself.  However, diag-β is applied to the inductive
hypotheses in triangle, which usually would not be marked with ♭. Fortunately,
we can prove ⇒-elim-♭ a derived eliminator for ⇒ which does allow us to assume
that.

-}

⇒-elim-♭ :
  ∀ {@♭ l : Level} →
  ∀ (@♭ A : ∀ (@♭ n) → (@♭ t1 t2 : Λ^ n → Λ) → Set l) →
  ∀ (@♭ HR : ∀ (@♭ n) (@♭ t) → A n t t) →
  ∀ (@♭ H· : ∀ (@♭ n) (@♭ t1 t1' t2 t2') →
             @♭ A n t1 t1' → @♭ A n t2 t2' →
             A n (λ γ → t1 γ · t2 γ) (λ γ → t1' γ · t2' γ)) →
  ∀ (@♭ Hƛ : ∀ (@♭ n) (@♭ t t' : Λ^ n → Λ → Λ) →
             @♭ A (suc n) (uncurry t) (uncurry t') →
             A n (λ γ → ƛ t γ) (λ γ → ƛ t' γ)) →
  ∀ (@♭ Hβ : ∀ (@♭ n) (@♭ t1 t1' : Λ^ n → Λ → Λ) (@♭ t2 t2') →
             @♭ A (suc n) (uncurry t1) (uncurry t1') →
             @♭ A n t2 t2' →
             A n (λ γ → (ƛ t1 γ) · t2 γ) (λ γ → t1' γ (t2' γ))) →
  ∀ (@♭ n t t') →
  ∀ (@♭ p : ∀ γ → t γ ⇒ t' γ) → A n t t'
⇒-elim-♭ A HR H· Hƛ Hβ n t t' p =
  from-♭ (⇒-elim (λ n t1 t2 → ♭ (A n t1 t2)) HR' H·' Hƛ' Hβ' n t t' p)
  where
  HR' : _
  HR' n t = to-♭ (HR n t)

  H·' : _
  H·' n t1 t1' t2 t2' (to-♭ IH1) (to-♭ IH2) = to-♭ (H· n t1 t1' t2 t2' IH1 IH2)

  Hƛ' : _
  Hƛ' n t t' (to-♭ IH) = to-♭ (Hƛ n t t' IH)

  Hβ' : _
  Hβ' n t1 t1' t2 t2' (to-♭ IH1) (to-♭ IH2) = to-♭ (Hβ n t1 t1' t2 t2' IH1 IH2)

⇒-uncurry :
  ∀ {@♭ n} {@♭ t1 t1' : Λ^ n → Λ → Λ} →
  (p : ∀ γ x → t1 γ x ⇒ t1' γ x) →
  ∀ γ → uncurry t1 γ ⇒ uncurry t1' γ
⇒-uncurry p γ = p (λ v → γ (suc v)) (γ zero)

⇒ₛ-refl : ∀ {n} {γ : Λ^ n} → γ ⇒ₛ γ
⇒ₛ-refl v = ⇒-refl _

diag-β : ∀ {@♭ n} {@♭ t1 t1' t2 t2'} →
         @♭ diag-spec {suc n} t1 t1' →
         @♭ diag-spec {n} t2 t2' →
         diag-spec (λ γ → curry t1 γ (t2 γ)) (res-· (res-ƛ t1') t2')
diag-β (inj₁ p1) p2 =
  inj₁ (λ γ → ⇒-subst _ _ _ p1 (γ ▸ _) (γ ▸ _)
              (⇒ₛ-refl ▸ₛ diag-term-of-res p2 γ))
diag-β {n} {t2 = t2} {t2' = t2'} (inj₂ {t1} {t1'} e p1) p2 rewrite e =
  inj₁ (λ γ → ⇒-ƛ (λ x → ⇒-subst (suc (suc n))
                          (uncurry t1) (uncurry t1') (⇒-uncurry p1)
                          (γ ▸ t2 γ ▸ x) (γ ▸ term-of-res t2' γ ▸ x) (p x γ)))
  where
  p : ∀ x γ → (γ ▸ t2 γ ▸ x) ⇒ₛ (γ ▸ term-of-res t2' γ ▸ x)
  p x γ = ⇒ₛ-refl ▸ₛ diag-term-of-res p2 γ ▸ₛ ⇒-refl x

triangle : ∀ (@♭ n) →
           ∀ (@♭ t t' : Λ^ n → Λ) →
           ∀ (@♭ p : ∀ γ → t γ ⇒ t' γ) →
           diag-spec t' (diag t)
triangle n t t' p =
  ⇒-elim-♭ (λ n t t' → diag-spec t' (diag t)) HR H· Hƛ Hβ n t t' p
  where

  HR : _
  HR n t = ⇒-diag t

  H· : _
  H· n t1 t1' t2 t2' IH1 IH2 = diag-res-· IH1 IH2

  Hƛ : _
  Hƛ n t t' IH = diag-res-ƛ IH

  Hβ : _
  Hβ n t1 t1' t2 t2' IH1 IH2 = diag-β IH1 IH2

{-

As sketched above, the diamond property of parallel reduction follows easily
from the triangle lemma.

-}

diamond : ∀ (@♭ n) →
          ∀ (@♭ t t1 t2 : Λ^ n → Λ) →
          ∀ (@♭ p1 : ∀ γ → t γ ⇒ t1 γ) →
          ∀ (@♭ p2 : ∀ γ → t γ ⇒ t2 γ) →
          Σ[ t' ∈ (Λ^ n → Λ) ]
            (∀ γ → t1 γ ⇒ t' γ) × (∀ γ → t2 γ ⇒ t' γ)
diamond n t t1 t2 p1 p2 =
  term-of-res (diag t) ,
    diag-term-of-res (triangle _ _ _ p1) ,
    diag-term-of-res (triangle _ _ _ p2)
