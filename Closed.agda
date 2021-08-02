{-# OPTIONS --rewriting --prop --cumulativity #-}

module Closed where

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

data pf {l} (P : Prop l) : Set l where
  mkpf : P → pf P

holds : ∀ {l} {P : Prop l} → pf P → P
holds (mkpf p) = p

infix 30 ⌊_⌋

postulate ⌊_⌋ : ∀ {l} → (A : Set l) → Prop
postulate sq : ∀ {l} → {A : Set l} → A → ⌊ A ⌋
postulate ⌊⌋-elim : ∀ {l} {A : Set l} {P : Prop} → ⌊ A ⌋ → (A → P) → P

⌊⌋-map : ∀ {l} {A B : Set l} → (A → B) → ⌊ A ⌋ → ⌊ B ⌋
⌊⌋-map f p = ⌊⌋-elim p (λ p → sq (f p))

_∧_ : Prop → Prop → Prop
P ∧ Q = ⌊ pf P × pf Q ⌋

∧-intro : ∀ {P Q : Prop} → P → Q → P ∧ Q
∧-intro pf-P pf-Q = sq ( mkpf pf-P , mkpf pf-Q )

∧-π₁ : ∀ {P Q : Prop} → P ∧ Q → P
∧-π₁ {P} {Q} P∧Q = ⌊⌋-elim P∧Q (λ p → holds (proj₁ p))

∧-π₂ : ∀ {P Q : Prop} → P ∧ Q → Q
∧-π₂ {P} {Q} P∧Q = ⌊⌋-elim P∧Q (λ p → holds (proj₂ p))

_∨_ : Prop → Prop → Prop
P ∨ Q = ⌊ pf P ⊎ pf Q ⌋

∨-ι₁ : ∀ {P Q : Prop} → P → P ∨ Q
∨-ι₁ pf-P = sq (inj₁ (mkpf pf-P))

∨-ι₂ : ∀ {P Q : Prop} → Q → P ∨ Q
∨-ι₂ pf-Q = sq (inj₂ (mkpf pf-Q))

∨-elim : ∀ {P Q R : Prop} → P ∨ Q → (P → R) → (Q → R) → R
∨-elim {P} {Q} {R} P∨Q i1 i2 = ⌊⌋-elim P∨Q p
  where p : pf P ⊎ pf Q → R
        p (inj₁ pf-P) = i1 (holds pf-P)
        p (inj₂ pf-Q) = i2 (holds pf-Q)

∃ : ∀ {l} {A : Set l} (P : A → Prop) → Prop
∃ P = ⌊ pf ((Q : Prop) → (∀ x → P x → Q) → Q) ⌋

∃-intro : ∀ {l} {A : Set l} {P : A → Prop} →
          ∀ x → P x → ∃ P
∃-intro x Px = sq (mkpf (λ Q p → p x Px))

∃-elim : ∀ {l} {A : Set l} {P : A → Prop} → ∃ P →
         {Q : Prop} → (∀ x → P x → Q) → Q
∃-elim ∃P {Q} p = ⌊⌋-elim ∃P (λ q → holds q Q p)

∃! : ∀ {l} {A : Set l} (P : A → Prop) → Prop
∃! {l} {A} P = ∃ {l} (λ x → P x ∧ ⌊ ((y : A) → P y → ⌊ _≡_ {l} x y ⌋) ⌋)

∃!-intro : ∀ {l} {A : Set l} {P : A → Prop} →
           ∀ x → P x → (∀ y → P y → ⌊ _≡_ {l} x y ⌋) → ∃! P
∃!-intro {l} x Px x-unique =
  ∃-intro {l} x (∧-intro Px (sq λ y Py → x-unique y Py))

∃!-elim : ∀ {l} {A : Set l} {P : A → Prop} → ∃! P →
          (Q : Prop) → (∀ x → P x → (∀ y → P y → ⌊ x ≡ y ⌋) → Q) → Q
∃!-elim ∃!P Q p = ∃-elim ∃!P (λ x Px → ⌊⌋-elim (∧-π₂ Px) ((p x (∧-π₁ Px))))

⌊⌋-trans : ∀ {l} {A : Set l} {x y z : A} → ⌊ x ≡ y ⌋ → ⌊ y ≡ z ⌋ → ⌊ x ≡ z ⌋
⌊⌋-trans e1 e2 = ⌊⌋-elim e1 λ e1 → ⌊⌋-map (trans e1) e2

⌊⌋-sym : ∀ {l} {A : Set l} {x y : A} → ⌊ x ≡ y ⌋ → ⌊ y ≡ x ⌋
⌊⌋-sym e = ⌊⌋-map sym e

postulate AC! : ∀ {l} {A : Set l} {P : A → Prop} → ∃! P → Σ[ x ∈ A ] pf (P x)

AC!-≡ : ∀ {l} {A : Set l} {P : A → Prop} (p : ∃! {l} P) →
        ∀ (x : A) (Px : P x) →
        ⌊ proj₁ (AC! p) ≡ x ⌋

AC!-≡ {l} p x Px = ∃!-elim {l} p (⌊ proj₁ (AC! {l} p) ≡ x ⌋)
  λ y Py y-unique → ⌊⌋-trans {l}
                    (⌊⌋-sym {l} (y-unique _ (holds (proj₂ (AC! p)))))
                    (y-unique _ Px)

id : Term
id = ƛ (λ x → x)

id-id : Term
id-id = id · id

id≢id-id : id ≢ id-id
id≢id-id = ƛ-·-disj _ _ _

postulate def : ∀ (t : Term) → (∃ (λ (f : Term → Term) → ⌊ t ≡ ƛ f ⌋)) ∨
                               (∃ (λ (ts : Term × Term) → ⌊ t ≡ (proj₁ ts) · (proj₂ ts) ⌋))

data def-alt-spec : Term → Set where
  def-ƛ : (f : Term → Term) → def-alt-spec (ƛ f)
  def-· : (t1 t2 : Term) → def-alt-spec (t1 · t2)

def-alt : (t : Term) → ⌊ def-alt-spec t ⌋
def-alt t = ∨-elim (def t)
            (λ p → ∃-elim p (λ f p → ⌊⌋-elim p (λ p → sq (c p (def-ƛ f)))))
            (λ p → ∃-elim p (λ ts p → ⌊⌋-elim p (λ p → sq (c p (def-· (proj₁ ts) (proj₂ ts))))))
  where c : ∀ {t1 t2} → t1 ≡ t2 → def-alt-spec t2 → def-alt-spec t1
        c refl p = p

data is-app-graph : Term → Term → Set where
  is-app-ƛ : (f : Term → Term) → is-app-graph (ƛ f) id
  is-app-· : (t1 t2 : Term) → is-app-graph (t1 · t2) id-id

is-app-graph-func : ∀ t1 t21 t22 → is-app-graph t1 t21 → is-app-graph t1 t22 → t21 ≡ t22
is-app-graph-func t1 = go t1 t1 refl
  where go : ∀ t11 t12 → t11 ≡ t12 → ∀ t21 t22 → is-app-graph t11 t21 → is-app-graph t12 t22 → t21 ≡ t22
        go .(ƛ f) .(ƛ f₁) e .id .id (is-app-ƛ f) (is-app-ƛ f₁) = refl
        go .(ƛ f) .(t1 · t2) e .id .id-id (is-app-ƛ f) (is-app-· t1 t2) with ƛ-·-disj _ _ _ e
        ... | ()
        go .(t1 · t2) .(ƛ f) e .id-id .id (is-app-· t1 t2) (is-app-ƛ f) with ƛ-·-disj _ _ _ (sym e)
        ... | ()
        go .(t1 · t2) .(t3 · t4) e .id-id .id-id (is-app-· t1 t2) (is-app-· t3 t4) = refl

is-app-graph-total : ∀ t → ⌊ ( Σ[ t' ∈ Term ] is-app-graph t t' ) ⌋
is-app-graph-total t = ⌊⌋-map f (def-alt t)
  where f : def-alt-spec t → Σ[ t' ∈ Term ] is-app-graph t t'
        f (def-ƛ f) = id , is-app-ƛ f
        f (def-· t1 t2) = id-id , is-app-· t1 t2

is-app-∃! : ∀ t → ∃! (λ t' → ⌊ is-app-graph t t' ⌋)
is-app-∃! t = ⌊⌋-elim (is-app-graph-total t)
  λ p → ∃!-intro (proj₁ p) (sq (proj₂ p)) λ y Py → ⌊⌋-elim Py (λ Py → sq (is-app-graph-func _ _ _ (proj₂ p) Py))

is-app : Term → Term
is-app t = proj₁ (AC! (is-app-∃! t))

exotic : Term
exotic = ƛ is-app
