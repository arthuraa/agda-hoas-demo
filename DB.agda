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

data Λ[_] : Ctx → Set where
  ` : ∀ {Γ} → Var Γ → Λ[ Γ ]
  App : ∀ {Γ} → Λ[ Γ ] → Λ[ Γ ] → Λ[ Γ ]
  Abs : ∀ {Γ} → Λ[ suc Γ ] → Λ[ Γ ]

interp : ∀ {@♭ Γ} → (@♭ t : Λ[ Γ ]) → C⟦ Γ ⟧ → Λ
interp (` x) = V⟦ x ⟧
interp (App t₁ t₂) γ = interp t₁ γ · interp t₂ γ
interp (Abs t) γ = ƛ (λ x → interp t (x , γ))

reify : ∀ {@♭ Γ} → (@♭ t : C⟦ Γ ⟧ → Λ) → Λ[ Γ ]
reify t = Λ-elim (λ Γ _ → Λ[ Γ ]) HV Hƛ H· _ t
  where
    HV : _
    HV _ v = ` v

    H· : _
    H· _ _ _ t₁ t₂ = App t₁ t₂

    Hƛ : _
    Hƛ _ _ t = Abs t

reify-interp : ∀ {@♭ Γ} → (@♭ t : Λ[ Γ ]) → reify (interp t) ≡ t

reify-interp (` x) = refl

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

interp-reify : ∀ {@♭ Γ} → (@♭ t : C⟦ Γ ⟧ → Λ) → interp (reify t) ≡ t
interp-reify t = Λ-elim A HV Hƛ H· _ t
  where
  A : ∀ (@♭ Γ) → (@♭ t : C⟦ Γ ⟧ → Λ) → Set
  A Γ t = interp (reify t) ≡ t

  HV : ∀ (@♭ Γ) (@♭ v : Var Γ) → A Γ (V⟦ v ⟧)
  HV Γ v = refl

  Hƛ : ∀ (@♭ Γ) (@♭ t : C⟦ Γ ⟧ → Λ → Λ) → A (suc Γ) (abs t) → A Γ (λ γ → ƛ t γ)
  Hƛ Γ t IH = begin
    interp (reify (λ γ → ƛ t γ))  ≡⟨⟩
    interp (Abs (reify (abs t)))  ≡⟨⟩
    abs' (interp (reify (abs t))) ≡⟨ e ⟩
    abs' (abs t) ≡⟨⟩
    (λ γ → ƛ t γ) ∎
    where
    abs' : (@♭ t' : C⟦ suc Γ ⟧ → Λ) → C⟦ Γ ⟧ → Λ
    abs' t' γ = ƛ (λ x → t' (x , γ))

    e : abs' (interp (reify (abs t))) ≡ abs' (abs t)
    e rewrite IH = refl

  H· : ∀ (@♭ Γ) (@♭ t1 t2 : C⟦ Γ ⟧ → Λ) → A Γ t1 → A Γ t2 → A Γ (λ γ → t1 γ · t2 γ)
  H· Γ t1 t2 IH1 IH2 = begin
    interp (reify (λ γ → t1 γ · t2 γ)) ≡⟨⟩
    app' (interp (reify t1)) (interp (reify t2)) ≡⟨ e ⟩
    (λ γ → t1 γ · t2 γ) ∎
    where
    app' : (@♭ t1 t2 : C⟦ Γ ⟧ → Λ) → C⟦ Γ ⟧ → Λ
    app' t1 t2 γ = t1 γ · t2 γ

    e : app' (interp (reify t1)) (interp (reify t2)) ≡
        λ γ → t1 γ · t2 γ
    e rewrite IH1 rewrite IH2 = refl
