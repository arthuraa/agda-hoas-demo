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
open import Flat

infix 3 _⇒_

postulate _⇒_ : Term → Term → Set

postulate
  prefl : ∀ t → t ⇒ t

postulate
  papp : ∀ {t1 t1' t2 t2'} →
    t1 ⇒ t1' →
    t2 ⇒ t2' →
    t1 · t2 ⇒ t1' · t2'

postulate
  pabs : ∀ {t t'} →
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
    ∀ (A : ∀ (@♭ Γ) → (@♭ t1 t2 : Term.⟦ Γ ⟧ → Term) → Set l) →
    ∀ (HR : ∀ (@♭ Γ) (@♭ t) → A Γ t t) →
    ∀ (H· : ∀ (@♭ Γ) (@♭ t1 t1' t2 t2') → A Γ t1 t1' → A Γ t2 t2' →
            A Γ (λ γ → t1 γ · t2 γ) (λ γ → t1' γ · t2' γ)) →
    ∀ (Hƛ : ∀ (@♭ Γ) →
            ∀ (@♭ t t' : Term.⟦ Γ ⟧ → Term → Term) →
            A (suc Γ) (Term.abs t) (Term.abs t') →
            A Γ (λ γ → ƛ t γ) (λ γ → ƛ t' γ)) →
    ∀ (Hβ : ∀ (@♭ Γ) →
            ∀ (@♭ t1 t1' : Term.⟦ Γ ⟧ → Term → Term) →
            ∀ (@♭ t2 t2') →
            A (suc Γ) (Term.abs t1) (Term.abs t1') →
            A Γ t2 t2' →
            A Γ (λ γ → (ƛ t1 γ) · t2 γ) (λ γ → t1' γ (t2' γ))) →
    ∀ (@♭ Γ t1 t2) →
    ∀ (@♭ p : ∀ γ → t1 γ ⇒ t2 γ) → A Γ t1 t2

abs :
  ∀ {@♭ Γ} {@♭ t1 t1' : Term.⟦ Γ ⟧ → Term → Term} →
  (p : ∀ γ x → t1 γ x ⇒ t1' γ x) →
  ∀ γ → Term.abs t1 γ ⇒ Term.abs t1' γ
abs p γ = p (tail γ) (head γ)

up : ∀ {@♭ Γ Δ} → (Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧) → Term.⟦ suc Δ ⟧ → Term.⟦ suc Γ ⟧
up ts (x ∷ γ) = x ∷ ts γ

⇒-up : ∀ {@♭ Γ Δ} →
       ∀ {t t' : Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧} →
       (∀ γ i → lookup (t γ) i ⇒ lookup (t' γ) i) →
       ∀ γ i → lookup (up t γ) i ⇒ lookup (up t' γ) i
⇒-up p (x ∷ γ) zero = prefl x
⇒-up p (x ∷ γ) (suc i) = p γ i

⇒-subst-refl :
  ∀ (@♭ Γ Δ) →
  ∀ (@♭ t1 : Term.⟦ Γ ⟧ → Term) →
  ∀ (t2 t2' : Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧) →
  ∀ (p2 : ∀ γ i → lookup (t2 γ) i ⇒ lookup (t2' γ) i) →
  ∀ γ → t1 (t2 γ) ⇒ t1 (t2' γ)
⇒-subst-refl Γ Δ t1 t2 t2' p2 γ =
  Term-elim A HV Hƛ H· Γ t1 Δ t2 t2' p2 γ
  where
  A : ∀ (@♭ Γ) (@♭ t1 : Term.⟦ Γ ⟧ → Term) → Set
  A Γ t1 =
    ∀ (@♭ Δ) →
    ∀ (t2 t2' : Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧) →
    ∀ (p2 : ∀ γ i → lookup (t2 γ) i ⇒ lookup (t2' γ) i) →
    ∀ γ → t1 (t2 γ) ⇒ t1 (t2' γ)

  HV : _
  HV Γ x1 Δ t2 t2' p2 γ = p2 γ x1

  Hƛ : _
  Hƛ Γ t1 IH1 Δ t2 t2' p2 γ =
    pabs (λ x → IH1 (suc Δ) (up t2) (up t2') (⇒-up p2) (x ∷ γ))

  H· : _
  H· Γ t1 t1' IH1 IH1' Δ t2 t2' p2 γ =
    papp (IH1 Δ t2 t2' p2 γ) (IH1' Δ t2 t2' p2 γ)

⇒-subst-gen :
  ∀ (@♭ Γ Δ) →
  ∀ (@♭ t1 t1' : Term.⟦ Γ ⟧ → Term) →
  ∀ (t2 t2' : Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧) →
  ∀ (@♭ p1 : ∀ γ   → t1 γ ⇒ t1' γ) →
  ∀ (p2 : ∀ γ i → lookup (t2 γ) i ⇒ lookup (t2' γ) i) →
  ∀ γ → t1 (t2 γ) ⇒ t1' (t2' γ)
⇒-subst-gen Γ Δ t1 t1' t2 t2' p1 p2 γ =
  ⇒-elim A HR H· Hƛ Hβ Γ t1 t1' p1 Δ t2 t2' p2 γ
  where
  A : ∀ (@♭ Γ) (@♭ t1 t1' : Term.⟦ Γ ⟧ → Term) → Set
  A Γ t1 t1' =
    ∀ (@♭ Δ) →
    ∀ (t2 t2' : Term.⟦ Δ ⟧ → Term.⟦ Γ ⟧) →
    ∀ (p2 : ∀ γ i → lookup (t2 γ) i ⇒ lookup (t2' γ) i) →
    ∀ γ → t1 (t2 γ) ⇒ t1' (t2' γ)

  HR : _
  HR Γ t1 Δ t2 t2' p2 γ = ⇒-subst-refl Γ Δ t1 t2 t2' p2 γ

  H· : _
  H· Γ t11 t11' t12 t12' IH1 IH2 Δ t2 t2' p2 γ =
    papp (IH1 Δ t2 t2' p2 γ) (IH2 Δ t2 t2' p2 γ)

  Hƛ : _
  Hƛ Γ t1 t1' IH Δ t2 t2' p2 γ =
    pabs (λ x → IH (suc Δ) (up t2) (up t2') (⇒-up p2) (x ∷ γ))

  Hβ : _
  Hβ Γ t11 t11' t12 t12' IH1 IH2 Δ t2 t2' p2 γ =
    pbeta (λ x → IH1 (suc Δ) (up t2) (up t2') (⇒-up p2) (x ∷ γ))
          (IH2 Δ t2 t2' p2 γ)

⇒-abs :
  ∀ {@♭ Γ} →
  ∀ {@♭ t t' : Term.⟦ Γ ⟧ → Term → Term} →
  ∀ (@♭ p : ∀ γ x → t γ x ⇒ t' γ x) →
  ∀ γ → Term.abs t γ ⇒ Term.abs t' γ
⇒-abs p (x ∷ γ) = p γ x

⇒-subst-lem :
  ∀ {@♭ Γ} →
  ∀ {t t' : Term.⟦ Γ ⟧ → Term} →
  ∀ (p : ∀ γ → t γ ⇒ t' γ) →
  ∀ γ i → lookup (t γ ∷ γ) i ⇒ lookup (t' γ ∷ γ) i
⇒-subst-lem p γ zero = p γ
⇒-subst-lem p γ (suc i) = prefl (lookup γ i)

⇒-subst-n :
  ∀ {@♭ Γ} →
  ∀ {@♭ t1 t1' : Term.⟦ Γ ⟧ → Term → Term} →
  ∀ {t2 t2' : Term.⟦ Γ ⟧ → Term} →
  ∀ (@♭ p1 : ∀ γ x → t1 γ x ⇒ t1' γ x) →
  ∀ (p2 : ∀ γ → t2 γ ⇒ t2' γ) →
  ∀ γ → t1 γ (t2 γ) ⇒ t1' γ (t2' γ)
⇒-subst-n {Γ} {t1} {t1'} {t2} {t2'} p1 p2 γ =
  ⇒-subst-gen (suc Γ) Γ (Term.abs t1) (Term.abs t1')
    (λ γ → t2 γ ∷ γ) (λ γ → t2' γ ∷ γ) (⇒-abs p1) (⇒-subst-lem p2) γ

⇒-subst-1 :
  ∀ (@♭ t1 t1' : Term → Term) →
  ∀ (t2 t2' : Term) →
  ∀ (@♭ p1 : ∀ x → t1 x ⇒ t1' x) →
  ∀ (p2 : t2 ⇒ t2') →
  t1 t2 ⇒ t1' t2'
⇒-subst-1 t1 t1' t2 t2' p1 p2 =
  ⇒-subst-n {zero} (λ _ → p1) (λ _ → p2) []

Res : Term.Ctx → Set
Res Γ = (Term.⟦ Γ ⟧ → Term) ⊎ (Term.⟦ Γ ⟧ → Term → Term)

term-of-res : ∀ {Γ} → Res Γ → Term.⟦ Γ ⟧ → Term
term-of-res (inj₁ t) = t
term-of-res (inj₂ t) γ = ƛ (t γ)

res-ƛ : ∀ {Γ} → Res (suc Γ) → Res Γ
res-ƛ t = inj₂ (λ γ x → term-of-res t (x ∷ γ))

res-· : ∀ {Γ} → Res Γ → Res Γ → Res Γ
res-· (inj₁ t1) t2 = inj₁ (λ γ → t1 γ · term-of-res t2 γ)
res-· (inj₂ t1) t2 = inj₁ (λ γ → t1 γ (term-of-res t2 γ))

diag : ∀ {@♭ Γ} (@♭ t : Term.⟦ Γ ⟧ → Term) → Res Γ
diag {Γ} t =
  Term-elim (λ Γ _ → Res Γ) HV Hƛ H· Γ t
  where
  HV : _
  HV Γ x = inj₁ (λ γ → lookup γ x)

  Hƛ : _
  Hƛ Γ _ IH = res-ƛ IH

  H· : _
  H· Γ _ _ IH1 IH2 = res-· IH1 IH2

data diag-spec {Γ} (t : Term.⟦ Γ ⟧ → Term) : Res Γ → Set where
  inj₁ : ∀ {t'} → (∀ γ → t γ ⇒ t' γ) → diag-spec t (inj₁ t')

  inj₂ : ∀ {t₀ t' : Term.⟦ Γ ⟧ → Term → Term} →
         t ≡ (λ γ → ƛ t₀ γ) →
         (∀ γ x → t₀ γ x ⇒ t' γ x) →
         diag-spec t (inj₂ t')

diag-term-of-res : ∀ {Γ t t'} → diag-spec {Γ} t t' →
                   ∀ γ → t γ ⇒ term-of-res t' γ
diag-term-of-res (inj₁ p) γ = p γ
diag-term-of-res (inj₂ refl p) γ = pabs (p γ)

diag-res-ƛ : ∀ {Γ t t'} →
             diag-spec {suc Γ} t t' →
             diag-spec {Γ} (λ γ → ƛ (λ x → t (x ∷ γ))) (res-ƛ t')
diag-res-ƛ p = inj₂ refl (λ γ x → diag-term-of-res p (x ∷ γ))

diag-res-· : ∀ {Γ t1 t1' t2 t2'} →
             diag-spec {Γ} t1 t1' →
             diag-spec {Γ} t2 t2' →
             diag-spec (λ γ → t1 γ · t2 γ) (res-· t1' t2')
diag-res-· (inj₁ p1) p2 = inj₁ (λ γ → papp (p1 γ) (diag-term-of-res p2 γ))
diag-res-· (inj₂ refl p1) p2 = inj₁ (λ γ → pbeta (p1 γ) (diag-term-of-res p2 γ))


⇒-diag : ∀ {@♭ Γ} →
         ∀ (@♭ t : Term.⟦ Γ ⟧ → Term) →
         diag-spec t (diag t)
⇒-diag {Γ} t =
  Term-elim (λ Γ t → diag-spec t (diag t))
    HV Hƛ H· Γ t
  where

  HV : _
  HV Γ v = inj₁ (λ γ → prefl (lookup γ v))

  Hƛ : _
  Hƛ Γ t IH = diag-res-ƛ IH

  H· : _
  H· Γ t1 t2 IH1 IH2 = diag-res-· IH1 IH2

diag-β : ∀ {@♭ Γ} {@♭ t1 t1' t2 t2'} →
         @♭ diag-spec {suc Γ} t1 t1' →
         @♭ diag-spec {Γ} t2 t2' →
         diag-spec (λ γ → t1 (t2 γ ∷ γ)) (res-· (res-ƛ t1') t2')
diag-β (inj₁ p1) p2 =
  inj₁ (λ γ → ⇒-subst-n (λ γ x → p1 (x ∷ γ)) (diag-term-of-res p2) γ)
diag-β {Γ} {t2 = t2} {t2' = t2'} (inj₂ {t1} {t1'} e p1) p2 rewrite e =
  inj₁ (λ γ → pabs (λ x → ⇒-subst-gen (suc (suc Γ)) (suc Γ)
                          (Term.abs t1) (Term.abs t1')
                          σ σ' (abs p1) p (x ∷ γ)))
  where
  σ : _
  σ γ = head γ ∷ t2 (tail γ) ∷ tail γ

  σ' : _
  σ' γ = head γ ∷ term-of-res t2' (tail γ) ∷ tail γ

  p : _
  p γ zero = prefl _
  p γ (suc zero) = diag-term-of-res p2 (tail γ)
  p γ (suc (suc x)) = prefl _

triangle : ∀ (@♭ Γ) →
           ∀ (@♭ t t' : Term.⟦ Γ ⟧ → Term) →
           ∀ (@♭ p : ∀ γ → t γ ⇒ t' γ) →
           diag-spec t' (diag t)
triangle Γ t t' p =
  from-♭ (⇒-elim (λ Γ t t' → ♭ (diag-spec t' (diag t))) HR H· Hƛ Hβ Γ t t' p)
  where

  HR : _
  HR Γ t = to-♭ (⇒-diag t)

  H· : _
  H· Γ t1 t1' t2 t2' (to-♭ IH1) (to-♭ IH2) = to-♭ (diag-res-· IH1 IH2)

  Hƛ : _
  Hƛ Γ t t' (to-♭ IH) = to-♭ (diag-res-ƛ IH)

  Hβ : _
  Hβ Γ t1 t1' t2 t2' (to-♭ IH1) (to-♭ IH2) = to-♭ (diag-β IH1 IH2)

diamond : ∀ (@♭ Γ) →
          ∀ (@♭ t t1 t2 : Term.⟦ Γ ⟧ → Term) →
          ∀ (@♭ p1 : ∀ γ → t γ ⇒ t1 γ) →
          ∀ (@♭ p2 : ∀ γ → t γ ⇒ t2 γ) →
          Σ[ t' ∈ (Term.⟦ Γ ⟧ → Term) ]
            (∀ γ → t1 γ ⇒ t' γ) × (∀ γ → t2 γ ⇒ t' γ)
diamond Γ t t1 t2 p1 p2 =
  term-of-res (diag t) ,
    diag-term-of-res (triangle _ _ _ p1) ,
    diag-term-of-res (triangle _ _ _ p2)
