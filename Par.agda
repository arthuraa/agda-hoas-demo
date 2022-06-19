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
open import Flat
open import Lambda

infix 3 _⇒_

postulate _⇒_ : Λ → Λ → Set

postulate
  prefl : ∀ t → t ⇒ t

postulate
  papp : ∀ {t1 t1' t2 t2'} →
    t1 ⇒ t1' →
    t2 ⇒ t2' →
    t1 · t2 ⇒ t1' · t2'

postulate
  pabs : ∀ {t t'} →
    (∀ (x : Λ) → t x ⇒ t' x) →
    ƛ t ⇒ ƛ t'

postulate
  pbeta : ∀ {t1 t1' : Λ → Λ} {t2 t2'} →
    (∀ (x : Λ) → t1 x ⇒ t1' x) →
    t2 ⇒ t2' →
    (ƛ t1) · t2 ⇒ t1' t2'

postulate
  ⇒-elim :
    ∀ {l : Level} →
    ∀ (A : ∀ (@♭ Γ) → (@♭ t1 t2 : C⟦ Γ ⟧ → Λ) → Set l) →
    ∀ (HR : ∀ (@♭ Γ) (@♭ t) → A Γ t t) →
    ∀ (H· : ∀ (@♭ Γ) (@♭ t1 t1' t2 t2') → A Γ t1 t1' → A Γ t2 t2' →
            A Γ (λ γ → t1 γ · t2 γ) (λ γ → t1' γ · t2' γ)) →
    ∀ (Hƛ : ∀ (@♭ Γ) →
            ∀ (@♭ t t' : C⟦ Γ ⟧ → Λ → Λ) →
            A (suc Γ) (abs t) (abs t') →
            A Γ (λ γ → ƛ t γ) (λ γ → ƛ t' γ)) →
    ∀ (Hβ : ∀ (@♭ Γ) →
            ∀ (@♭ t1 t1' : C⟦ Γ ⟧ → Λ → Λ) →
            ∀ (@♭ t2 t2') →
            A (suc Γ) (abs t1) (abs t1') →
            A Γ t2 t2' →
            A Γ (λ γ → (ƛ t1 γ) · t2 γ) (λ γ → t1' γ (t2' γ))) →
    ∀ (@♭ Γ t1 t2) →
    ∀ (@♭ p : ∀ γ → t1 γ ⇒ t2 γ) → A Γ t1 t2

par-abs :
  ∀ {@♭ Γ} {@♭ t1 t1' : C⟦ Γ ⟧ → Λ → Λ} →
  (p : ∀ γ x → t1 γ x ⇒ t1' γ x) →
  ∀ γ → abs t1 γ ⇒ abs t1' γ
par-abs p γ = p (tail γ) (head γ)

_⊢_⇒ₛ_ : ∀ Γ (γ γ' : C⟦ Γ ⟧) → Set
_⊢_⇒ₛ_ Γ γ γ' = ∀ (v : Var Γ) → V⟦ v ⟧ γ ⇒ V⟦ v ⟧ γ'

infixl 2 _,,ₛ_

_,,ₛ_ : ∀ {Γ} {γ γ' : C⟦ Γ ⟧} {x x' : Λ} →
        Γ ⊢ γ ⇒ₛ γ' →
        x ⇒  x' →
        (suc Γ) ⊢ (x ∷ γ) ⇒ₛ (x' ∷ γ')
_,,ₛ_ {Γ} ⇒-γ ⇒-x zero = ⇒-x
_,,ₛ_ {Γ} ⇒-γ ⇒-x (suc v) = ⇒-γ v

preflₛ : ∀ {Γ} {γ : C⟦ Γ ⟧} → Γ ⊢ γ ⇒ₛ γ
preflₛ v = prefl _

⇒-subst :
  ∀ (@♭ Γ) →
  ∀ (@♭ t1 t1' : C⟦ Γ ⟧ → Λ) →
  ∀ (@♭ p1 : ∀ γ  → t1 γ ⇒ t1' γ) →
  ∀ (γ2 γ2' : C⟦ Γ ⟧) →
  ∀ (p2 : _ ⊢ γ2 ⇒ₛ γ2') →
  t1 γ2 ⇒ t1' γ2'
⇒-subst Γ t1 t1' p1 =
  ⇒-elim A HR H· Hƛ Hβ Γ t1 t1' p1
  where
  A : _
  A Γ t1 t1' = (γ2 γ2' : C⟦ Γ ⟧) (p2 : _ ⊢ γ2 ⇒ₛ γ2') → t1 γ2 ⇒ t1' γ2'

  HR : _
  HR Γ t1 = λ γ2 γ2' p2 →
    Λ-cong2 _⇒_ (λ _ _ IH → pabs (λ x → IH x (prefl x)))
    (λ _ _ _ _ IH1 IH2 → papp IH1 IH2) t1 γ2 γ2' p2

  H· : _
  H· Γ t11 t11' t12 t12' IH1 IH2 = λ γ2 γ2' p2 →
    papp (IH1 γ2 γ2' p2) (IH2 γ2 γ2' p2)

  Hƛ : _
  Hƛ Γ t1 t1' IH γ2 γ2' p2 =
    pabs (λ x → IH (x ∷ γ2) (x ∷ γ2') (p2 ,,ₛ prefl x))

  Hβ : _
  Hβ Γ t11 t11' t12 t12' IH1 IH2 γ2 γ2' p2 =
    pbeta (λ x → IH1 (x ∷ γ2) (x ∷ γ2') (p2 ,,ₛ prefl x))
          (IH2 γ2 γ2' p2)

Res : Ctx → Set
Res Γ = (C⟦ Γ ⟧ → Λ) ⊎ (C⟦ Γ ⟧ → Λ → Λ)

term-of-res : ∀ {Γ} → Res Γ → C⟦ Γ ⟧ → Λ
term-of-res (inj₁ t) = t
term-of-res (inj₂ t) γ = ƛ (t γ)

res-ƛ : ∀ {Γ} → Res (suc Γ) → Res Γ
res-ƛ t = inj₂ (λ γ x → term-of-res t (x ∷ γ))

res-· : ∀ {Γ} → Res Γ → Res Γ → Res Γ
res-· (inj₁ t1) t2 = inj₁ (λ γ → t1 γ · term-of-res t2 γ)
res-· (inj₂ t1) t2 = inj₁ (λ γ → t1 γ (term-of-res t2 γ))

diag : ∀ {@♭ Γ} (@♭ t : C⟦ Γ ⟧ → Λ) → Res Γ
diag {Γ} t =
  Λ-elim _ HV Hƛ H· Γ t
  where
  HV : _
  HV Γ x = inj₁ (λ γ → V⟦ x ⟧ γ)

  Hƛ : _
  Hƛ Γ _ IH = res-ƛ IH

  H· : _
  H· Γ _ _ IH1 IH2 = res-· IH1 IH2

data diag-spec {Γ} (t : C⟦ Γ ⟧ → Λ) : Res Γ → Set where
  inj₁ : ∀ {t'} → (∀ γ → t γ ⇒ t' γ) → diag-spec t (inj₁ t')

  inj₂ : ∀ {t₀ t' : C⟦ Γ ⟧ → Λ → Λ} →
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
         ∀ (@♭ t : C⟦ Γ ⟧ → Λ) →
         diag-spec t (diag t)
⇒-diag {Γ} t =
  -- Removing this type annotation causes type checking to diverge
  Λ-elim (λ Γ t → diag-spec t (diag t)) HV Hƛ H· Γ t
  where

  HV : _
  HV Γ v = inj₁ (λ γ → prefl (V⟦ v ⟧ γ))

  Hƛ : _
  Hƛ Γ t IH = diag-res-ƛ IH

  H· : _
  H· Γ t1 t2 IH1 IH2 = diag-res-· IH1 IH2

diag-β : ∀ {@♭ Γ} {@♭ t1 t1' t2 t2'} →
         @♭ diag-spec {suc Γ} t1 t1' →
         @♭ diag-spec {Γ} t2 t2' →
         diag-spec (λ γ → t1 (t2 γ ∷ γ)) (res-· (res-ƛ t1') t2')
diag-β (inj₁ p1) p2 =
  inj₁ (λ γ → ⇒-subst _ _ _ p1 (_ ∷ γ) (_ ∷ γ)
              (preflₛ {_} {γ} ,,ₛ diag-term-of-res p2 γ))
diag-β {Γ} {t2 = t2} {t2' = t2'} (inj₂ {t1} {t1'} e p1) p2 rewrite e =
  inj₁ (λ γ → pabs (λ x → ⇒-subst (suc (suc Γ))
                          (abs t1) (abs t1') (par-abs p1)
                          (x ∷ t2 γ ∷ γ) (x ∷ term-of-res t2' γ ∷ γ) (p x γ)))
  where
  p : ∀ x γ → _ ⊢ (x ∷ t2 γ ∷ γ) ⇒ₛ (x ∷ term-of-res t2' γ ∷ γ)
  p x γ = preflₛ {_} {γ} ,,ₛ diag-term-of-res p2 γ ,,ₛ prefl x

triangle : ∀ (@♭ Γ) →
           ∀ (@♭ t t' : C⟦ Γ ⟧ → Λ) →
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
          ∀ (@♭ t t1 t2 : C⟦ Γ ⟧ → Λ) →
          ∀ (@♭ p1 : ∀ γ → t γ ⇒ t1 γ) →
          ∀ (@♭ p2 : ∀ γ → t γ ⇒ t2 γ) →
          Σ[ t' ∈ (C⟦ Γ ⟧ → Λ) ]
            (∀ γ → t1 γ ⇒ t' γ) × (∀ γ → t2 γ ⇒ t' γ)
diamond Γ t t1 t2 p1 p2 =
  term-of-res (diag t) ,
    diag-term-of-res (triangle _ _ _ p1) ,
    diag-term-of-res (triangle _ _ _ p2)
