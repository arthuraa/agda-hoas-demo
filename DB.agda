{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Fin
open import Data.Nat
open import Lambda
open import Flat

open ≡-Reasoning

module DB where

{-

The elimination principle for λ terms we have postulated is essentially the same
we would have obtained for a traditional dependently typed encoding.  Because of
this coincidence, the two representations are isomorphic, as we'll show here.
We begin by defining an inductive family Λ[ n ] that represents λ terms with n
free variables.

-}

data Λ[_] : ℕ → Set where
  Var : ∀ {n} → Fin n → Λ[ n ]
  App : ∀ {n} → Λ[ n ] → Λ[ n ] → Λ[ n ]
  Abs : ∀ {n} → Λ[ suc n ] → Λ[ n ]

{-

The interp function below converts from Λ[ n ] to Λ, given some valuation γ : Λ^
n for interpreting free variables.

-}

interp : ∀ {n} → (t : Λ[ n ]) → Λ^ n → Λ
interp (Var x) γ = γ x
interp (App t₁ t₂) γ = interp t₁ γ · interp t₂ γ
interp (Abs t) γ = ƛ (curry (interp t) γ)

{-

Going the other way, we can use Λ-elim to construct a function that reifies a
HOAS λ term with n free variables as an element of Λ[ n ].  Note the use of the
♭ modality on the argument.

-}

reify : ∀ {@♭ n} → (@♭ t : Λ^ n → Λ) → Λ[ n ]
reify t = Λ-elim (λ n _ → Λ[ n ]) HV Hƛ H· _ t
  where
    HV : _
    HV _ v = Var v

    H· : _
    H· _ _ _ t₁ t₂ = App t₁ t₂

    Hƛ : _
    Hƛ _ _ t = Abs t

{-

Here is an example showing how reify computes on the looping λ term ω.

-}

reify-ω : reify {0} (λ _ → ω) ≡
          App (Abs (App (Var zero) (Var zero)))
              (Abs (App (Var zero) (Var zero)))
reify-ω = refl

{-

We can show that interp and reify are inverses of each other.  The proofs follow
by induction and equational reasoning.  Note that, to show that reify (interp
(Abs t)) ≡ Abs t, we need to use the uncurry-curry theorem, which requires
functional extensionality.

-}

reify-interp : ∀ {@♭ n} → (@♭ t : Λ[ n ]) → reify (interp t) ≡ t

reify-interp (Var x) = refl

reify-interp (App t₁ t₂) = begin
  reify (interp (App t₁ t₂)) ≡⟨⟩
  App (reify (interp t₁)) (reify (interp t₂)) ≡⟨ cong₂ App IH₁ IH₂ ⟩
  App t₁ t₂ ∎

  where
  IH₁ = reify-interp t₁
  IH₂ = reify-interp t₂

reify-interp (Abs t) = begin
  reify (interp (Abs t)) ≡⟨⟩
  reify (λ γ → (ƛ (curry (interp t) γ))) ≡⟨⟩
  Abs (reify (uncurry (curry (interp t)))) ≡⟨ cong Abs e ⟩
  Abs (reify (interp t)) ≡⟨ cong Abs (reify-interp t) ⟩
  Abs t ∎
  where
  e = cong-♭ reify (uncurry-curry (interp t))

interp-reify : ∀ {@♭ n} → (@♭ t : Λ^ n → Λ) → interp (reify t) ≡ t
interp-reify t = Λ-elim A HV Hƛ H· _ t
  where
  A : ∀ (@♭ n) → (@♭ t : Λ^ n → Λ) → Set
  A n t = interp (reify t) ≡ t

  HV : ∀ (@♭ n) (@♭ v : Fin n) → A n (λ γ → γ v)
  HV n v = refl

  Hƛ : ∀ (@♭ n) (@♭ t : Λ^ n → Λ → Λ) → A (suc n) (uncurry t) → A n (λ γ → ƛ t γ)
  Hƛ n t IH = begin
    interp (reify (λ γ → ƛ t γ))  ≡⟨⟩
    interp (Abs (reify (uncurry t)))  ≡⟨⟩
    abs (interp (reify (uncurry t))) ≡⟨ cong-♭ abs IH ⟩
    abs (uncurry t) ≡⟨⟩
    (λ γ → ƛ t γ) ∎
    where
    abs : (@♭ t' : Λ^ (suc n) → Λ) → Λ^ n → Λ
    abs t' γ = ƛ (curry t' γ)

  H· : ∀ (@♭ n) (@♭ t1 t2 : Λ^ n → Λ) → A n t1 → A n t2 → A n (λ γ → t1 γ · t2 γ)
  H· n t1 t2 IH1 IH2 = begin
    interp (reify (λ γ → t1 γ · t2 γ)) ≡⟨⟩
    app (interp (reify t1)) (interp (reify t2)) ≡⟨ cong₂-♭ app IH1 IH2 ⟩
    app t1 t2 ≡⟨⟩
    (λ γ → t1 γ · t2 γ) ∎
    where
    app : (@♭ t1 t2 : Λ^ n → Λ) → Λ^ n → Λ
    app t1 t2 γ = t1 γ · t2 γ
