{-# OPTIONS --rewriting --prop #-}

open import Relation.Binary.PropositionalEquality
import Axiom.Extensionality.Propositional as P
open import Data.Product
open import Data.Vec
open import Data.Fin
open import Data.Nat
open import Lambda

open ≡-Reasoning

module DB where

data Λ[_] : ℕ → Set where
  Var : ∀ {n} → Fin n → Λ[ n ]
  App : ∀ {n} → Λ[ n ] → Λ[ n ] → Λ[ n ]
  Abs : ∀ {n} → Λ[ suc n ] → Λ[ n ]

interp : ∀ {@♭ n} → (@♭ t : Λ[ n ]) → Λ^ n → Λ
interp (Var x) = ` x
interp (App t₁ t₂) γ = interp t₁ γ · interp t₂ γ
interp (Abs t) γ = ƛ (λ x → interp t (x , γ))

reify : ∀ {@♭ n} → (@♭ t : Λ^ n → Λ) → Λ[ n ]
reify t = Λ-elim (λ n _ → Λ[ n ]) HV Hƛ H· _ t
  where
    HV : _
    HV _ v = Var v

    H· : _
    H· _ _ _ t₁ t₂ = App t₁ t₂

    Hƛ : _
    Hƛ _ _ t = Abs t

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
  Abs (reify (interp t)) ≡⟨ cong Abs IH ⟩
  Abs t ∎
  where
  IH = reify-interp t

interp-reify : ∀ {@♭ n} → (@♭ t : Λ^ n → Λ) → interp (reify t) ≡ t
interp-reify t = Λ-elim A HV Hƛ H· _ t
  where
  A : ∀ (@♭ n) → (@♭ t : Λ^ n → Λ) → Set
  A n t = interp (reify t) ≡ t

  HV : ∀ (@♭ n) (@♭ v : Fin n) → A n (` v)
  HV n v = refl

  Hƛ : ∀ (@♭ n) (@♭ t : Λ^ n → Λ → Λ) → A (suc n) (abs t) → A n (λ γ → ƛ t γ)
  Hƛ n t IH = begin
    interp (reify (λ γ → ƛ t γ))  ≡⟨⟩
    interp (Abs (reify (abs t)))  ≡⟨⟩
    abs' (interp (reify (abs t))) ≡⟨ e ⟩
    abs' (abs t) ≡⟨⟩
    (λ γ → ƛ t γ) ∎
    where
    abs' : (@♭ t' : Λ^ (suc n) → Λ) → Λ^ n → Λ
    abs' t' γ = ƛ (λ x → t' (x , γ))

    e : abs' (interp (reify (abs t))) ≡ abs' (abs t)
    e rewrite IH = refl

  H· : ∀ (@♭ n) (@♭ t1 t2 : Λ^ n → Λ) → A n t1 → A n t2 → A n (λ γ → t1 γ · t2 γ)
  H· n t1 t2 IH1 IH2 = begin
    interp (reify (λ γ → t1 γ · t2 γ)) ≡⟨⟩
    app' (interp (reify t1)) (interp (reify t2)) ≡⟨ e ⟩
    (λ γ → t1 γ · t2 γ) ∎
    where
    app' : (@♭ t1 t2 : Λ^ n → Λ) → Λ^ n → Λ
    app' t1 t2 γ = t1 γ · t2 γ

    e : app' (interp (reify t1)) (interp (reify t2)) ≡
        λ γ → t1 γ · t2 γ
    e rewrite IH1 rewrite IH2 = refl
