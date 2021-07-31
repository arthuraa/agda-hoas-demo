{-# OPTIONS --rewriting --prop #-}

module Term where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin hiding (_+_; cast)
open import Data.Vec

infix 6 ƛ_
infixl 7 _·_

postulate Term : Set

postulate  _·_ : Term → Term → Term

postulate ƛ_ : (Term → Term) → Term

postulate ·-inj : ∀ t₁ t₁' t₂ t₂' →
                  t₁ · t₂ ≡ t₁' · t₂' → t₁ ≡ t₁' × t₂ ≡ t₂'

postulate ƛ-inj : ∀ t t' → ƛ t ≡ ƛ t' → t ≡ t'

postulate ƛ-·-disj : ∀ t t₁ t₂ → ƛ t ≢ t₁ · t₂

-- This is the most general elimination principle that I can think of.  It is a
-- direct translation of the canonical principle for indexed terms.
--
-- TODO: Is it OK that the result A is not restricted to closed terms?

postulate
  Term-elim : {@♭ l : Level}
              (@♭ A : ∀ n → (Vec Term n → Term) → Set l) →
              (@♭ _ : ∀ n x → A n (λ γ → lookup γ x)) →
              (@♭ _ : ∀ n t → A (suc n) t → A n (λ γ → ƛ (λ x → t (x ∷ γ)))) →
              (@♭ _ : ∀ n t1 t2 → A n t1 → A n t2 → A n (λ γ → t1 γ · t2 γ)) →
              (@♭ n : ℕ) (@♭ t : Vec Term n → Term) → A n t

{-
postulate
  Term-elim' : {@♭ l : Level}
               (@♭ A : ∀ (@♭ n) → (@♭ Vec Term n → Term) → Set l) →
               (@♭ _ : ∀ (@♭ n) (@♭ x) → A n (λ γ → lookup γ x)) →
               (@♭ _ : ∀ (@♭ n) (@♭ t) → A (suc n) t → A n (λ γ → ƛ (λ (x : Term) → t (x ∷ γ)))) →
               (@♭ _ : ∀ (@♭ n) (@♭ t1 t2) → A n t1 → A n t2 → A n (λ γ → t1 γ · t2 γ)) →
               (@♭ n : ℕ) (@♭ t : Vec Term n → Term) → A n t
-}

-- This is a special case of the previous lemma where we omit the context

elim-no-ctx : {@♭ l : Level} (@♭ A : Term → Set l) →
  (@♭ _ : (∀ t1 t2 → A t1 → A t2 → A (t1 · t2))) →
  (@♭ _ : (∀ f → (∀ t → A t → A (f t)) → A (ƛ f))) →
  (@♭ t : Term) → A t
elim-no-ctx {l} A H· Hƛ t =
  Term-elim A' H2` H2ƛ H2· zero (λ _ → t) [] (λ ())
  where
  A' : ∀ n → (Vec Term n → Term) → Set l
  A' n t = ∀ γ → (∀ x → A (lookup γ x)) → A (t γ)

  H2` : ∀ n x → A' n (λ γ → lookup γ x)
  H2` n x γ z = z x

  H2ƛ : ∀ n t → A' (suc n) t → A' n (λ γ → ƛ (λ x → t (x ∷ γ)))
  H2ƛ n t IHt γ Hγ = Hƛ (λ x → t (x ∷ γ)) (λ x Hx → IHt (x ∷ γ) (IHγ' x Hx))
    where IHγ' : ∀ x → A x → ∀ i → A (lookup (x ∷ γ) i)
          IHγ' x Hx zero = Hx
          IHγ' x Hx (suc i) = Hγ i

  H2· : ∀ n t1 t2 → A' n t1 → A' n t2 → A' n (λ γ → t1 γ · t2 γ)
  H2· n t1 t2 IH1 IH2 γ Hγ = H· (t1 γ) (t2 γ) (IH1 γ Hγ) (IH2 γ Hγ)


elim-ctx-fixed : {@♭ l : Level}
  {@♭ n : ℕ} (@♭ A : (Vec Term n → Term) → Set l) →
  (@♭ _ : ∀ x → A (λ γ → lookup γ x)) →
  (@♭ _ : ∀ (t : Vec Term (suc n) → Term) →
            (∀ t' → A t' → A (λ γ → t (t' γ ∷ γ))) →
            A (λ γ → ƛ (λ x → t (x ∷ γ)))) →
  (@♭ _ : ∀ t₁ t₂ → A t₁ → A t₂ → A (λ γ → t₁ γ · t₂ γ)) →
  (@♭ t : Vec Term n → Term) → A t
elim-ctx-fixed {l} {n} A H` Hƛ H· t =
  Term-elim A2 H2` H2ƛ H2· n t (λ γ → γ) H`
  where
  A2 : ∀ m → (Vec Term m → Term) → Set l
  A2 m t = ∀ (f : Vec Term n → Vec Term m) →
           (∀ x → A (λ γ → lookup (f γ) x)) →
           A (λ γ → t (f γ))

  H2` : ∀ m x → A2 m (λ γ → lookup γ x)
  H2` m x f p = p x

  H2ƛ : ∀ m t → A2 (suc m) t → A2 m (λ γ → ƛ (λ x → t (x ∷ γ)))
  H2ƛ m t IHt f pf = Hƛ g pg
    where
    g : Vec Term (suc n) → Term
    g (x ∷ γ) = t (x ∷ f γ)

    pg : (t' : Vec Term n → Term) → A t' → A (λ γ → g (t' γ ∷ γ))
    pg t' IHt' = IHt (λ γ → (t' γ ∷ f γ)) aux
      where
      aux : ∀ x → A (λ γ → lookup (t' γ ∷ f γ) x)
      aux zero = IHt'
      aux (suc x) = pf x

  H2· : ∀ m t1 t2 → A2 m t1 → A2 m t2 → A2 m (λ γ → t1 γ · t2 γ)
  H2· m t1 t2 IH1 IH2 f fp = H· (λ γ → t1 (f γ)) (λ γ → t2 (f γ)) (IH1 f fp) (IH2 f fp)

infix 2 _⇒_

data _⇒_ : Term → Term → Set where

  prefl : ∀ t → t ⇒ t

  papp : ∀ t₁ t₁' t₂ t₂' →
         t₁ ⇒ t₁' →
         t₂ ⇒ t₂' →
         t₁ · t₂ ⇒ t₁' · t₂'

  pabs : ∀ t t' →
         (∀ x → t x ⇒ t' x) →
         ƛ t ⇒ ƛ t'

  pbeta : ∀ {t₁ t₁' : Term → Term} {t₂ t₂' : Term} →
          (∀ x → t₁ x ⇒ t₁' x) →
          t₂ ⇒ t₂' →
          (ƛ t₁) · t₂ ⇒ (t₁' t₂')
