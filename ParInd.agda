{-# OPTIONS --rewriting --prop #-}

module ParInd where

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
open import Term

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

data diag-aux-spec : Term → Res → Set where

  inj₁ : ∀ t t' → t ⇒ t' → diag-aux-spec t (inj₁ t')

  inj₂ : ∀ (t t' : Term → Term) → (∀ x → t x ⇒ t' x) → diag-aux-spec (ƛ t) (inj₂ t')

diag-aux-term-of-res : ∀ {t r} → diag-aux-spec t r → t ⇒ term-of-res r
diag-aux-term-of-res (inj₁ t t' x) = x
diag-aux-term-of-res (inj₂ t t' x) = pabs t t' x

diag-aux-· : ∀ {t1 t1' t2 t2'} →
              diag-aux-spec t1 t1' →
              diag-aux-spec t2 t2' →
              diag-aux-spec (t1 · t2) (inj₁ (res-· t1' (term-of-res t2')))
diag-aux-· (inj₁ t1 t1' p1) (inj₁ t2 t2' p2) =
  inj₁ (t1 · t2) (t1' · t2') (papp t1 t1' t2 t2' p1 p2)
diag-aux-· (inj₁ t1 t1' p1) (inj₂ t2 t2' p2) =
  inj₁ (t1 · (ƛ t2)) (t1' · (ƛ t2'))
       (papp t1 t1' (ƛ t2) (ƛ t2') p1 (pabs t2 t2' p2))
diag-aux-· (inj₂ t1 t1' p1) (inj₁ t2 t2' p2) =
  inj₁ ((ƛ t1) · t2) (t1' t2') (pbeta p1 p2)
diag-aux-· (inj₂ t1 t1' p1) (inj₂ t2 t2' p2) =
  inj₁ ((ƛ t1) · (ƛ t2)) (t1' (ƛ t2')) (pbeta p1 (pabs t2 t2' p2))

diag-aux-refl : ∀ (@♭ n) (@♭ t : Vec Term n → Term) →
  ∀ γ → (f : Fin n → Res) → (∀ i → f i ≡ inj₁ (lookup γ i)) →
  diag-aux-spec (t γ) (diag-aux n t γ f)

diag-aux-refl n t =
  Term-elim A HV Hƛ H· n t
  where
  A : ∀ (@♭ n) → @♭ (Vec Term n → Term) → Set
  A n t = ∀ γ → (f : Fin n → Res) → (∀ i → f i ≡ inj₁ (lookup γ i)) →
          diag-aux-spec (t γ) (diag-aux n t γ f)

  HV : ∀ (@♭ n) (@♭ x : Fin n) → A n (λ γ → lookup γ x)
  HV n x γ f f-γ rewrite f-γ x = inj₁ _ _ (prefl (lookup γ x))

  Hƛ : ∀ (@♭ n) (@♭ t : Vec Term n → Term → Term) →
       A (suc n) (λ γ → t (tail γ) (head γ)) →
       ∀ γ → (f : Fin n → Res) → (∀ i → f i ≡ inj₁ (lookup γ i)) →
       diag-aux-spec (ƛ (t γ))
         (inj₂ (λ x → term-of-res (diag-aux (suc n) (λ γ → t (tail γ) (head γ))
                                  (x ∷ γ) (fin-elim _ (inj₁ x) f))))
  Hƛ n t IHt γ f f-γ =
    inj₂ (t γ) _ (λ x → diag-aux-term-of-res (IHt (x ∷ γ) _ (fin-elim _ refl f-γ)))


  H· : ∀ (@♭ n) (@♭ t1 t2 : Vec Term n → Term) →
       A n t1 → A n t2 →
       ∀ γ → (f : Fin n → Res) → (∀ i → f i ≡ inj₁ (lookup γ i)) →
       diag-aux-spec (t1 γ · t2 γ)
                      (inj₁ (res-· (diag-aux n t1 γ f)
                                   (term-of-res (diag-aux n t2 γ f))))


  H· n t1 t2 IH1 IH2 γ f f-γ =
    diag-aux-· (IH1 γ f f-γ) (IH2 γ f f-γ)

diag-aux-⇒ : ∀ (@♭ n) (@♭ t1 : Vec Term n → Term) t2 t' →
             ∀ γ (f : Fin n → Res) → (∀ i → f i ≡ inj₁ (lookup γ i)) →
             t1 γ ≡ t2 → t2 ⇒ t' →
             diag-aux-spec t' (diag-aux n t1 γ f)
diag-aux-⇒ n t1 .t2 .t2 γ f f-γ e (prefl t2)
  rewrite (sym e) = diag-aux-refl n t1 γ f f-γ
diag-aux-⇒ n t1 .(t21 · t22) .(t21' · t22') γ f f-γ e
  (papp t21 t21' t22 t22' p1 p2) = p
  where

  p : diag-aux-spec (t21' · t22') (diag-aux n t1 γ f)
  p = {!!}
