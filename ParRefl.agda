{-# OPTIONS --rewriting --prop #-}

module Par where

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
open import Term

infix 2 _⇒_

postulate _⇒_ : Term → Term → Set

postulate
  prefl : ∀ t → t ⇒ t

postulate
  papp : ∀ {t1 t1' t2 t2'} →
    t1 ⇒ t1' →
    t2 ⇒ t2' →
    t1 · t2 ⇒ t1' · t2'

postulate
  pabs : ∀ t t' →
    (∀ (x : Term) → t x ⇒ t' x) →
    ƛ t ⇒ ƛ t'

postulate
  pbeta : ∀ {t1 t1' : Term → Term} {t2 t2'} →
    (∀ (x : Term) → t1 x ⇒ t1' x) →
    t2 ⇒ t2' →
    (ƛ t1) · t2 ⇒ t1' t2'

postulate
  ⇒-elim :
    ∀ {l : Level} →
    ∀ (A : (@♭ n : ℕ) → (@♭ t t' : Vec Term n → Term) →
           (@♭ p : ∀ γ → t γ ⇒ t' γ) → Set l) →
    (HR : ∀ (@♭ n) (@♭ t : Vec Term n → Term) →
          A n t t (λ γ → prefl (t γ))) →
    (H· : ∀ (@♭ n) (@♭ t1 t1' t2 t2' : Vec Term n → Term) →
          ∀ (@♭ p1 p2) →
          A n t1 t1' p1 → A n t2 t2' p2 →
          A n (λ γ → t1 γ · t2 γ) (λ γ → t1' γ · t2' γ)
              (λ γ → papp (p1 γ) (p2 γ))) →
    (Hƛ : ∀ (@♭ n) (@♭ t t' : Vec Term n → Term → Term) →
          ∀ (@♭ p : ∀ γ x → t γ x ⇒ t' γ x) →
          A (suc n) (λ γ → t (tail γ) (head γ)) (λ γ → t' (tail γ) (head γ))
                    (λ γ → p (tail γ) (head γ)) →
          A n (λ γ → ƛ (t γ)) (λ γ → ƛ (t' γ))
              (λ γ → pabs _ _ (p γ))) →
    (Hβ : ∀ (@♭ n) (@♭ t1 t1' : Vec Term n → Term → Term) →
          ∀ (@♭ t2 t2' : Vec Term n → Term) →
          ∀ (@♭ p1 : ∀ γ x → t1 γ x ⇒ t1' γ x) (@♭ p2) →
          A (suc n) (λ γ → t1 (tail γ) (head γ)) (λ γ → t1' (tail γ) (head γ))
                    (λ γ → p1 (tail γ) (head γ)) →
          A n t2 t2' p2 →
          A n _ _ (λ γ → pbeta (p1 γ) (p2 γ))) →
    ∀ (@♭ n) (@♭ t t' : Vec Term n → Term) (@♭ p) → A n t t' p

data diag-aux-spec : Term → Res → Set where

  inj₁ : ∀ t t' → t ⇒ t' → diag-aux-spec t (inj₁ t')

  inj₂ : ∀ (t t' : Term → Term) → (∀ x → t x ⇒ t' x) → diag-aux-spec (ƛ t) (inj₂ t')

diag-aux-term-of-res : ∀ {t r} → diag-aux-spec t r → t ⇒ term-of-res r
diag-aux-term-of-res (inj₁ t t' p) = p
diag-aux-term-of-res (inj₂ t t' p) = pabs t t' p

diag-aux-· : ∀ {t1 t1' t2 t2'} →
              diag-aux-spec t1 t1' →
              diag-aux-spec t2 t2' →
              diag-aux-spec (t1 · t2) (inj₁ (res-· t1' (term-of-res t2')))
diag-aux-· (inj₁ t1 t1' p1) (inj₁ t2 t2' p2) =
  inj₁ (t1 · t2) (t1' · t2') (papp p1 p2)
diag-aux-· (inj₁ t1 t1' p1) (inj₂ t2 t2' p2) =
  inj₁ (t1 · (ƛ t2)) (t1' · (ƛ t2'))
       (papp  p1 (pabs t2 t2' p2))
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

triangle-aux' : ∀ (@♭ n) (@♭ t t' : Vec Term n → Term) →
  ∀ (@♭ p : ∀ γ → t γ ⇒ t' γ) →
  ∀ (γ γ' : Vec Term n) (f f' : Fin n → Res) →
  (∀ i → f  i ≡ inj₁ (lookup γ i)) →
  (∀ i → f' i ≡ inj₁ (lookup γ' i)) →
  (∀ i → lookup γ i ⇒ lookup γ' i) →
  diag-aux-spec (t' γ) (diag-aux n t γ' f)
triangle-aux' n t t' p γ γ' f f' f-γ f'-γ γ⇒γ' =
  ⇒-elim A HR H· Hƛ Hβ n t t' p γ γ' f f' f-γ f'-γ γ⇒γ'
  where
  A : _
  A n t t' p = ∀ (γ γ' : Vec Term n) (f f' : Fin n → Res) →
    (∀ i → f  i ≡ inj₁ (lookup γ i)) →
    (∀ i → f' i ≡ inj₁ (lookup γ' i)) →
    (∀ i → lookup γ i ⇒ lookup γ' i) →
    diag-aux-spec (t' γ) (diag-aux n t γ' f)

  HR : _
  HR n t γ γ' f f' _ _ γ⇒γ' = {!!}

  H· : _
  H· = {!!}

  Hƛ : _
  Hƛ = {!!}

  Hβ : _
  Hβ = {!!}




triangle-aux : ∀ (@♭ n) (@♭ t t' : Vec Term n → Term) →
  ∀ (@♭ p : ∀ γ → t γ ⇒ t' γ) →
  ∀ (γ : Vec Term n) (f : Fin n → Res) →
  (∀ i → f i ≡ inj₁ (lookup γ i)) →
  diag-aux-spec (t' γ) (diag-aux n t γ f)
triangle-aux n t t' p γ f f-γ =
  ⇒-elim A HR H· Hƛ Hβ n t t' p γ f f-γ
  where
  A : _
  A n t t' p = ∀ γ (f : Fin n → Res) →
               (∀ i → f i ≡ inj₁ (lookup γ i)) →
               diag-aux-spec (t' γ) (diag-aux n t γ f)

  HR : _
  HR n t γ f f-γ = diag-aux-refl n t γ f f-γ

  H· : _
  H· n t1 t1' t2 t2' p1 p2 IH1 IH2 γ f f-γ =
    diag-aux-· (IH1 γ f f-γ) (IH2 γ f f-γ)

  Hƛ : _
  Hƛ n t t' p IH γ f f-γ =
    inj₂ (t' γ) t'' IH'
    where
    f' : Term → Fin (suc n) → Res
    f' x = fin-elim _ (inj₁ x) f

    f'-γ : ∀ x i → f' x i ≡ inj₁ (lookup (x ∷ γ) i)
    f'-γ x = fin-elim _ refl f-γ

    t'' : Term → Term
    t'' x = term-of-res (diag-aux (suc n) (λ γ → t (tail γ) (head γ)) (x ∷ γ) (f' x))

    IH' : _
    IH' x = diag-aux-term-of-res (IH (x ∷ γ) (f' x) (f'-γ x))


  Hβ : _
  Hβ n t1 t1' t2 t2' p1 p2 IH1 IH2 γ f f-γ =
    inj₁ (t1' γ (t2' γ)) t'' IH'
    where
    f' : Term → Fin (suc n) → Res
    f' x = fin-elim _ (inj₁ x) f

    f'-γ : ∀ x i → f' x i ≡ inj₁ (lookup (x ∷ γ) i)
    f'-γ x = fin-elim _ refl f-γ

    t2'' : Term
    t2'' = term-of-res (diag-aux n t2 γ f)

    t1'' : Term → Term
    t1'' x = term-of-res (diag-aux (suc n) (λ γ → t1 (tail γ) (head γ)) (x ∷ γ) (f' x))
    t'' : Term
    t'' = t1'' t2''

    IH2' : t2' γ ⇒ t2''
    IH2' = diag-aux-term-of-res (IH2 γ f f-γ)

    IH1' : ∀ x → t1' γ x ⇒ t1'' x
    IH1' x = diag-aux-term-of-res (IH1 (x ∷ γ) (f' x) (f'-γ x))

    IH' : _
    IH' = {!pbeta!} -- Here we are screwed, because we need to
