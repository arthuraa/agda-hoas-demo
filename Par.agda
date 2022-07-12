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
    ∀ (@♭ n t1 t2) →
    ∀ (@♭ p : ∀ γ → t1 γ ⇒ t2 γ) → A n t1 t2

par-uncurry :
  ∀ {@♭ n} {@♭ t1 t1' : Λ^ n → Λ → Λ} →
  (p : ∀ γ x → t1 γ x ⇒ t1' γ x) →
  ∀ γ → uncurry t1 γ ⇒ uncurry t1' γ
par-uncurry p γ = p (proj₁ γ) (proj₂ γ)

_⊢_⇒ₛ_ : ∀ n (γ γ' : Λ^ n) → Set
_⊢_⇒ₛ_ n γ γ' = ∀ (v : Fin n) → ⟦ v ⟧ γ ⇒ ⟦ v ⟧ γ'

infixl 2 _,ₛ_

_,ₛ_ : ∀ {n} {γ γ' : Λ^ n} {x x' : Λ} →
        n ⊢ γ ⇒ₛ γ' →
        x ⇒  x' →
        (suc n) ⊢ (γ , x) ⇒ₛ (γ' , x')
_,ₛ_ {n} ⇒-γ ⇒-x zero = ⇒-x
_,ₛ_ {n} ⇒-γ ⇒-x (suc v) = ⇒-γ v

preflₛ : ∀ {n} {γ : Λ^ n} → n ⊢ γ ⇒ₛ γ
preflₛ v = prefl _

⇒-subst-refl :
  ∀ (@♭ n) →
  ∀ (@♭ t : Λ^ n → Λ) →
  ∀ (γ2 γ2' : Λ^ n) →
  ∀ (p2 : _ ⊢ γ2 ⇒ₛ γ2') →
  t γ2 ⇒ t γ2'
⇒-subst-refl n t = Λ-elim A HV Hƛ H· n t
  where
  A : _
  A n t = (γ2 γ2' : Λ^ n) (p2 : _ ⊢ γ2 ⇒ₛ γ2') → t γ2 ⇒ t γ2'

  HV : _
  HV n v γ2 γ2' p2 = p2 v

  Hƛ : _
  Hƛ n t IH γ2 γ2' p2 =
    pabs (λ x → IH (γ2 , x) (γ2' , x) (p2 ,ₛ prefl x))

  H· : _
  H· n t1 t2 IH1 IH2 γ2 γ2' p2 = papp (IH1 γ2 γ2' p2) (IH2 γ2 γ2' p2)


⇒-subst :
  ∀ (@♭ n) →
  ∀ (@♭ t1 t1' : Λ^ n → Λ) →
  ∀ (@♭ p1 : ∀ γ  → t1 γ ⇒ t1' γ) →
  ∀ (γ2 γ2' : Λ^ n) →
  ∀ (p2 : _ ⊢ γ2 ⇒ₛ γ2') →
  t1 γ2 ⇒ t1' γ2'
⇒-subst n t1 t1' p1 =
  ⇒-elim A HR H· Hƛ Hβ n t1 t1' p1
  where
  A : _
  A n t1 t1' = (γ2 γ2' : Λ^ n) (p2 : _ ⊢ γ2 ⇒ₛ γ2') → t1 γ2 ⇒ t1' γ2'

  HR : _
  HR n t1 = ⇒-subst-refl n t1

  H· : _
  H· n t11 t11' t12 t12' IH1 IH2 = λ γ2 γ2' p2 →
    papp (IH1 γ2 γ2' p2) (IH2 γ2 γ2' p2)

  Hƛ : _
  Hƛ n t1 t1' IH γ2 γ2' p2 =
    pabs (λ x → IH (γ2 , x) (γ2' , x) (p2 ,ₛ prefl x))

  Hβ : _
  Hβ n t11 t11' t12 t12' IH1 IH2 γ2 γ2' p2 =
    pbeta (λ x → IH1 (γ2 , x) (γ2' , x) (p2 ,ₛ prefl x))
          (IH2 γ2 γ2' p2)

Res : ℕ → Set
Res n = (Λ^ n → Λ) ⊎ (Λ^ n → Λ → Λ)

term-of-res : ∀ {n} → Res n → Λ^ n → Λ
term-of-res (inj₁ t) = t
term-of-res (inj₂ t) γ = ƛ (t γ)

res-ƛ : ∀ {n} → Res (suc n) → Res n
res-ƛ t = inj₂ (λ γ x → term-of-res t (γ , x))

res-· : ∀ {n} → Res n → Res n → Res n
res-· (inj₁ t1) t2 = inj₁ (λ γ → t1 γ · term-of-res t2 γ)
res-· (inj₂ t1) t2 = inj₁ (λ γ → t1 γ (term-of-res t2 γ))

diag : ∀ {@♭ n} (@♭ t : Λ^ n → Λ) → Res n
diag {n} t =
  Λ-elim _ HV Hƛ H· n t
  where
  HV : _
  HV n x = inj₁ (λ γ → ⟦ x ⟧ γ)

  Hƛ : _
  Hƛ n _ IH = res-ƛ IH

  H· : _
  H· n _ _ IH1 IH2 = res-· IH1 IH2

data diag-spec {n} (t : Λ^ n → Λ) : Res n → Set where
  inj₁ : ∀ {t'} → (∀ γ → t γ ⇒ t' γ) → diag-spec t (inj₁ t')

  inj₂ : ∀ {t₀ t' : Λ^ n → Λ → Λ} →
         t ≡ (λ γ → ƛ t₀ γ) →
         (∀ γ x → t₀ γ x ⇒ t' γ x) →
         diag-spec t (inj₂ t')

diag-term-of-res : ∀ {n t t'} → diag-spec {n} t t' →
                   ∀ γ → t γ ⇒ term-of-res t' γ
diag-term-of-res (inj₁ p) γ = p γ
diag-term-of-res (inj₂ refl p) γ = pabs (p γ)

diag-res-ƛ : ∀ {n t t'} →
             diag-spec {suc n} t t' →
             diag-spec {n} (λ γ → ƛ (curry t γ)) (res-ƛ t')
diag-res-ƛ p = inj₂ refl (λ γ x → diag-term-of-res p (γ , x))

diag-res-· : ∀ {n t1 t1' t2 t2'} →
             diag-spec {n} t1 t1' →
             diag-spec {n} t2 t2' →
             diag-spec (λ γ → t1 γ · t2 γ) (res-· t1' t2')
diag-res-· (inj₁ p1) p2 = inj₁ (λ γ → papp (p1 γ) (diag-term-of-res p2 γ))
diag-res-· (inj₂ refl p1) p2 = inj₁ (λ γ → pbeta (p1 γ) (diag-term-of-res p2 γ))


⇒-diag : ∀ {@♭ n} →
         ∀ (@♭ t : Λ^ n → Λ) →
         diag-spec t (diag t)
⇒-diag {n} t =
  -- Removing this type annotation causes type checking to diverge
  Λ-elim (λ n t → diag-spec t (diag t)) HV Hƛ H· n t
  where

  HV : _
  HV n v = inj₁ (λ γ → prefl (⟦ v ⟧ γ))

  Hƛ : _
  Hƛ n t IH = diag-res-ƛ IH

  H· : _
  H· n t1 t2 IH1 IH2 = diag-res-· IH1 IH2

diag-β : ∀ {@♭ n} {@♭ t1 t1' t2 t2'} →
         @♭ diag-spec {suc n} t1 t1' →
         @♭ diag-spec {n} t2 t2' →
         diag-spec (λ γ → t1 (γ , t2 γ)) (res-· (res-ƛ t1') t2')
diag-β (inj₁ p1) p2 =
  inj₁ (λ γ → ⇒-subst _ _ _ p1 (γ , _) (γ , _)
              (preflₛ {_} {γ} ,ₛ diag-term-of-res p2 γ))
diag-β {n} {t2 = t2} {t2' = t2'} (inj₂ {t1} {t1'} e p1) p2 rewrite e =
  inj₁ (λ γ → pabs (λ x → ⇒-subst (suc (suc n))
                          (uncurry t1) (uncurry t1') (par-uncurry p1)
                          ((γ , t2 γ) , x) ((γ , term-of-res t2' γ) , x) (p x γ)))
  where
  p : ∀ x γ → _ ⊢ ((γ , t2 γ) , x) ⇒ₛ ((γ , term-of-res t2' γ) , x)
  p x γ = preflₛ {_} {γ} ,ₛ diag-term-of-res p2 γ ,ₛ prefl x

triangle : ∀ (@♭ n) →
           ∀ (@♭ t t' : Λ^ n → Λ) →
           ∀ (@♭ p : ∀ γ → t γ ⇒ t' γ) →
           diag-spec t' (diag t)
triangle n t t' p =
  from-♭ (⇒-elim (λ n t t' → ♭ (diag-spec t' (diag t))) HR H· Hƛ Hβ n t t' p)
  where

  HR : _
  HR n t = to-♭ (⇒-diag t)

  H· : _
  H· n t1 t1' t2 t2' (to-♭ IH1) (to-♭ IH2) = to-♭ (diag-res-· IH1 IH2)

  Hƛ : _
  Hƛ n t t' (to-♭ IH) = to-♭ (diag-res-ƛ IH)

  Hβ : _
  Hβ n t1 t1' t2 t2' (to-♭ IH1) (to-♭ IH2) = to-♭ (diag-β IH1 IH2)

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
