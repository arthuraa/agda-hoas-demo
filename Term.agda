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

postulate
  Term-elim : {l : Level}
    (A : ∀ (@♭ n) → @♭ (Vec Term n → Term) → Set l) →
    (∀ (@♭ n x) → A n (λ γ → lookup γ x)) →
    (∀ (@♭ n) (@♭ t : Vec Term n → Term → Term) →
       A (suc n) (λ γ → t (tail γ) (head γ)) → A n (λ γ → ƛ (t γ))) →
    (∀ (@♭ n t1 t2) → A n t1 → A n t2 → A n (λ γ → t1 γ · t2 γ)) →
    (@♭ n : ℕ) (@♭ t : Vec Term n → Term) → A n t

postulate
  Term-elim-V : {l : Level}
    (A : ∀ (@♭ n) → @♭ (Vec Term n → Term) → Set l) →
    (HV : ∀ (@♭ n x) → A n (λ γ → lookup γ x)) →
    (Hƛ : ∀ (@♭ n t) → A (suc n) (λ γ → t (tail γ) (head γ)) →
                       A n (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ n t1 t2) → A n t1 → A n t2 → A n (λ γ → t1 γ · t2 γ)) →
    (@♭ n : ℕ) (@♭ x : Fin n) →
    Term-elim A HV Hƛ H· n (λ γ → lookup γ x) ≡ HV n x

postulate
  Term-elim-ƛ : {l : Level}
    (A : ∀ (@♭ n) → @♭ (Vec Term n → Term) → Set l) →
    (HV : ∀ (@♭ n x) → A n (λ γ → lookup γ x)) →
    (Hƛ : ∀ (@♭ n t) → A (suc n) (λ γ → t (tail γ) (head γ)) →
                       A n (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ n t1 t2) → A n t1 → A n t2 → A n (λ γ → t1 γ · t2 γ)) →
    (@♭ n : ℕ) (@♭ t : Vec Term n → Term → Term) →
    Term-elim A HV Hƛ H· n (λ γ → ƛ (t γ)) ≡
    Hƛ n t
      (Term-elim A HV Hƛ H· (suc n) (λ γ → t (tail γ) (head γ)))

postulate
  Term-elim-· : {l : Level}
    (A : ∀ (@♭ n) → @♭ (Vec Term n → Term) → Set l) →
    (HV : ∀ (@♭ n x) → A n (λ γ → lookup γ x)) →
    (Hƛ : ∀ (@♭ n t) → A (suc n) (λ γ → t (tail γ) (head γ)) →
                       A n (λ γ → ƛ (t γ))) →
    (H· : ∀ (@♭ n t1 t2) → A n t1 → A n t2 → A n (λ γ → t1 γ · t2 γ)) →
    (@♭ n : ℕ) (@♭ t1 t2 : Vec Term n → Term) →
    Term-elim A HV Hƛ H· n (λ γ → t1 γ · t2 γ) ≡
    H· n t1 t2 (Term-elim A HV Hƛ H· n t1) (Term-elim A HV Hƛ H· n t2)

{-# REWRITE Term-elim-V #-}
{-# REWRITE Term-elim-ƛ #-}
{-# REWRITE Term-elim-· #-}

data ·-♭-spec : @♭ Term → Term → Term → Set where
  intro : ∀ (@♭ t1 t2) → ·-♭-spec (t1 · t2) t1 t2

·-♭ : ∀ {@♭ t} {t1} {t2} → t ≡ t1 · t2 → ·-♭-spec t t1 t2
·-♭ {t} {t1} {t2} e =
  Term-elim A HV Hƛ H· zero (λ _ → t) [] e refl
  where
  A : ∀ (@♭ n) → @♭ (Vec Term n → Term) → Set
  A n t = ∀ (@♭ γ) → t γ ≡ t1 · t2 → n ≡ zero → ·-♭-spec (t γ) t1 t2

  HV : _
  HV .(suc _) zero γ _ ()
  HV .(suc _) (suc x) γ _ ()

  Hƛ : _
  Hƛ n t _ γ e-t e-n with (ƛ-·-disj _ _ _ e-t)
  ... | ()

  H· : _
  H· n t1 t2 _ _ γ e-t e-n with ·-inj _ _ _ _ e-t
  ... | e1 , e2 rewrite sym e1 | sym e2 = intro (t1 γ) (t2 γ)


fin-elim : ∀ {l : Level} {n} (A : Fin (suc n) → Set l) →
  A zero → (∀ i → A (suc i)) → ∀ i → A i
fin-elim A AZ AS zero = AZ
fin-elim A AZ AS (suc i) = AS i

elim1g : {l : Level}
        (A : Term → Set l) →
        (∀ t → (∀ x → A x → A (t x)) → A (ƛ t)) →
        (∀ t1 t2 → A t1 → A t2 → A (t1 · t2)) →
        ∀ (@♭ n) (@♭ t : Vec Term n → Term) →
        ∀ γ → (∀ i → A (lookup γ i)) → A (t γ)
elim1g {l} A Hƛ H· n t γ Aγ =
  Term-elim A' HV' Hƛ' H·' n t γ Aγ
  where
  A' : ∀ (@♭ n) → @♭ (Vec Term n → Term) → Set l
  A' n t = ∀ γ → (∀ i → A (lookup γ i)) → A (t γ)

  HV' : ∀ (@♭ n x) → A' n (λ γ → lookup γ x)
  HV' n x γ Aγ = Aγ x

  Hƛ' : ∀ (@♭ n) (@♭ t : Vec Term n → Term → Term) →
        A' (suc n) (λ γ → t (tail γ) (head γ)) → A' n (λ γ → ƛ (t γ))
  Hƛ' n t IHt γ Aγ = Hƛ (t γ)
    (λ x Ax → IHt (x ∷ γ) (fin-elim (λ i → A (lookup (x ∷ γ) i)) Ax Aγ))

  H·' : ∀ (@♭ n t1 t2) → A' n t1 → A' n t2 → A' n (λ γ → t1 γ · t2 γ)
  H·' n t1 t2 IH1 IH2 γ Aγ = H· (t1 γ) (t2 γ) (IH1 γ Aγ) (IH2 γ Aγ)

elim1g-ƛ : {l : Level}
  (A : Term → Set l) →
  (Hλ : ∀ t → (∀ x → A x → A (t x)) → A (ƛ t)) →
  (H· : ∀ t1 t2 → A t1 → A t2 → A (t1 · t2)) →
  ∀ (@♭ n) (@♭ t : Vec Term n → Term → Term) →
  ∀ γ → (Aγ : ∀ i → A (lookup γ i)) →
  elim1g A Hλ H· n (λ γ → ƛ (t γ)) γ Aγ ≡
  Hλ (t γ)
     (λ x Ax → elim1g A Hλ H· (suc n) (λ γ → t (tail γ) (head γ)) (x ∷ γ)
               (fin-elim _ Ax Aγ))
elim1g-ƛ A Hλ H· n t γ Aγ = refl

elim1 : {l : Level}
        (A : Term → Set l) →
        (∀ t → (∀ x → A x → A (t x)) → A (ƛ t)) →
        (∀ t1 t2 → A t1 → A t2 → A (t1 · t2)) →
        ∀ (@♭ t) → A t
elim1 {l} A Hƛ H· t =
  elim1g A Hƛ H· zero (λ _ → t) [] (λ ())

Res : Set
Res = Term ⊎ (Term → Term)

term-of-res : Res → Term
term-of-res (inj₁ t) = t
term-of-res (inj₂ t) = ƛ t

res-· : Res → Term → Term
res-· (inj₁ t₁) t₂ = t₁ · t₂
res-· (inj₂ t₁) t₂ = t₁ t₂

diag-aux : ∀ (@♭ n) → @♭ (Vec Term n → Term) → ∀ γ → (∀ (i : Fin n) → Res) → Res
diag-aux =
 elim1g (λ _ → Res)
    (λ _ t → inj₂ λ x → term-of-res (t x (inj₁ x)))
    (λ _ _ t1 t2 → inj₁ (res-· t1 (term-of-res t2)))

diag : @♭ Term → Term
diag t = term-of-res (diag-aux zero (λ _ → t) [] (λ ()))

elim2g : {l : Level}
         (A : Term → Term → Set l) →
         (∀ t1 t2 → (∀ x1 x2 → A x1 x2 → A (t1 x1) (t2 x2)) →
           A (ƛ t1) (ƛ t2)) →
         (∀ t11 t12 t21 t22 → A t11 t12 → A t21 t22 →
           A (t11 · t21) (t12 · t22)) →
         ∀ (@♭ n) (@♭ t : Vec Term n → Term) →
         ∀ γ1 γ2 → (∀ i → A (lookup γ1 i) (lookup γ2 i)) → A (t γ1) (t γ2)
elim2g {l} A Hƛ H· n t γ1 γ2 Aγ =
  Term-elim A' HV' Hƛ' H·' n t γ1 γ2 Aγ
  where
  A' : ∀ (@♭ n) → @♭ (Vec Term n → Term) → Set l
  A' n t = ∀ γ1 γ2 → (∀ i → A (lookup γ1 i) (lookup γ2 i)) → A (t γ1) (t γ2)

  HV' : ∀ (@♭ n x) → A' n (λ γ → lookup γ x)
  HV' n x γ1 γ2 Aγ = Aγ x

  Hƛ' : ∀ (@♭ n) (@♭ t : Vec Term n → Term → Term) →
        A' (suc n) (λ γ → t (tail γ) (head γ)) →
        A' n (λ γ → ƛ (t γ))
  Hƛ' n t IHt γ1 γ2 Aγ = Hƛ (t γ1) (t γ2)
    λ x1 x2 Ax → IHt (x1 ∷ γ1) (x2 ∷ γ2)
      (fin-elim (λ z → A (lookup (x1 ∷ γ1) z) (lookup (x2 ∷ γ2) z)) Ax Aγ)

  H·' : ∀ (@♭ n t1 t2) → A' n t1 → A' n t2 → A' n (λ γ → t1 γ · t2 γ)
  H·' n t1 t2 IH1 IH2 γ1 γ2 Aγ =
    H· (t1 γ1) (t1 γ2) (t2 γ1) (t2 γ2) (IH1 γ1 γ2 Aγ) (IH2 γ1 γ2 Aγ)

elim2 : {l : Level}
        (A : Term → Term → Set l) →
        (∀ t1 t2 → (∀ x1 x2 → A x1 x2 → A (t1 x1) (t2 x2)) →
          A (ƛ t1) (ƛ t2)) →
        (∀ t11 t12 t21 t22 → A t11 t12 → A t21 t22 →
          A (t11 · t21) (t12 · t22)) →
        ∀ (@♭ t) → A t t
elim2 A Hƛ H· t = elim2g A Hƛ H· zero (λ _ → t) [] [] (λ ())

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

data pdiag-aux-type : Term → Res → Set where

  inj₁ : ∀ t t' → t ⇒ t' → pdiag-aux-type t (inj₁ t')

  inj₂ : ∀ (t t' : Term → Term) → (∀ x → t x ⇒ t' x) → pdiag-aux-type (ƛ t) (inj₂ t')

pdiag-aux-term-of-res : ∀ {t r} → pdiag-aux-type t r → t ⇒ term-of-res r
pdiag-aux-term-of-res (inj₁ t t' x) = x
pdiag-aux-term-of-res (inj₂ t t' x) = pabs t t' x

pdiag-aux-· : ∀ {t1 t1' t2 t2'} →
              pdiag-aux-type t1 t1' →
              pdiag-aux-type t2 t2' →
              pdiag-aux-type (t1 · t2) (inj₁ (res-· t1' (term-of-res t2')))
pdiag-aux-· (inj₁ t1 t1' p1) (inj₁ t2 t2' p2) =
  inj₁ (t1 · t2) (t1' · t2') (papp t1 t1' t2 t2' p1 p2)
pdiag-aux-· (inj₁ t1 t1' p1) (inj₂ t2 t2' p2) =
  inj₁ (t1 · (ƛ t2)) (t1' · (ƛ t2'))
       (papp t1 t1' (ƛ t2) (ƛ t2') p1 (pabs t2 t2' p2))
pdiag-aux-· (inj₂ t1 t1' p1) (inj₁ t2 t2' p2) =
  inj₁ ((ƛ t1) · t2) (t1' t2') (pbeta p1 p2)
pdiag-aux-· (inj₂ t1 t1' p1) (inj₂ t2 t2' p2) =
  inj₁ ((ƛ t1) · (ƛ t2)) (t1' (ƛ t2')) (pbeta p1 (pabs t2 t2' p2))

pdiag-aux : ∀ (@♭ n) (@♭ t : Vec Term n → Term) →
            ∀ γ → (f : Fin n → Res) → (∀ i → f i ≡ inj₁ (lookup γ i)) →
            pdiag-aux-type (t γ) (diag-aux n t γ f)

pdiag-aux n t =
  Term-elim A HV Hƛ H· n t
  where
  A : ∀ (@♭ n) → @♭ (Vec Term n → Term) → Set
  A n t = ∀ γ → (f : Fin n → Res) → (∀ i → f i ≡ inj₁ (lookup γ i)) →
          pdiag-aux-type (t γ) (diag-aux n t γ f)

  HV : ∀ (@♭ n) (@♭ x : Fin n) → A n (λ γ → lookup γ x)
  HV n x γ f f-γ rewrite f-γ x = inj₁ _ _ (prefl (lookup γ x))

  Hƛ : ∀ (@♭ n) (@♭ t : Vec Term n → Term → Term) →
       A (suc n) (λ γ → t (tail γ) (head γ)) →
       ∀ γ → (f : Fin n → Res) → (∀ i → f i ≡ inj₁ (lookup γ i)) →
       pdiag-aux-type (ƛ (t γ))
         (inj₂ (λ x → term-of-res (diag-aux (suc n) (λ γ → t (tail γ) (head γ))
                                  (x ∷ γ) (fin-elim _ (inj₁ x) f))))
  Hƛ n t IHt γ f f-γ =
    inj₂ (t γ) _ (λ x → pdiag-aux-term-of-res (IHt (x ∷ γ) _ (fin-elim _ refl f-γ)))


  H· : ∀ (@♭ n) (@♭ t1 t2 : Vec Term n → Term) →
       A n t1 → A n t2 →
       ∀ γ → (f : Fin n → Res) → (∀ i → f i ≡ inj₁ (lookup γ i)) →
       pdiag-aux-type (t1 γ · t2 γ)
                      (inj₁ (res-· (diag-aux n t1 γ f)
                                   (term-of-res (diag-aux n t2 γ f))))


  H· n t1 t2 IH1 IH2 γ f f-γ =
    pdiag-aux-· (IH1 γ f f-γ) (IH2 γ f f-γ)

pdiag : ∀ (@♭ t) → t ⇒ diag t
pdiag t = pdiag-aux-term-of-res (pdiag-aux zero (λ _ → t) [] _ (λ ()))
