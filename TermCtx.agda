{-# OPTIONS --rewriting --prop #-}

module TermCtx where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Ctx

postulate Term : Set

postulate TmApp : Term → Term → Term

postulate TmAbs : (Term → Term) → Term

postulate Term-Type-⊤ : Type Ctx-⊤

postulate el-Term : (x : ⊤) → el-ty Term-Type-⊤ x ≡ Term

{-# REWRITE el-Term #-}

Term-Type : (@♭ Γ : Ctx) → Type Γ
Term-Type Γ = Term-Type-⊤ ↑ λ _ → tt

Term-Ctx : (@♭ Γ : Ctx) → Ctx
Term-Ctx Γ = Ctx-Σ Γ (Term-Type Γ)

-- This is a very general principle that tries to work directly with contexts.
-- It looks unreadable

postulate
  Term-elim-ctx : {@♭ l : Level} (@♭ A : (Γ : Ctx) → (el Γ → Term) → Set l) →
                  (@♭ H-Var : (@♭ Γ : Ctx) (v : Var Γ (Term-Type Γ)) → A Γ ⟦ v ⟧) →
                  (@♭ H-App : (@♭ Γ : Ctx) (t1 t2 : el Γ → Term) → A Γ t1 → A Γ t2 →
                              A Γ (λ γ → TmApp (t1 γ) (t2 γ))) →
                  (@♭ H-Abs : (@♭ Γ : Ctx) (t : el (Term-Ctx Γ) → Term) →
                              A (Term-Ctx Γ) t →
                              A Γ (λ γ → TmAbs (λ t' → t ( γ , t' )))) →
                  (@♭ Γ : Ctx) (@♭ t : el Γ → Term) → A Γ t

-- This is a more restricted induction principle that does not explicitly
-- mention contexts.  It is not clear whether this is much worse than the one
-- above, but it is certainly much easier to read.

postulate
  Term-elim : {@♭ l : Level} (@♭ A : Term → Set l) →
              (@♭ _ : (∀ t1 t2 → A t1 → A t2 → A (TmApp t1 t2))) →
              (@♭ _ : (∀ f → (∀ t → A t → A (f t)) → A (TmAbs f))) →
              (@♭ t : Term) → A t

-- Similar to the above, but this time we allow proving properties of terms on
-- non-empty contexts.

postulate
  Term-elim-gen : {@♭ l : Level} (@♭ A : Term → Set l) →
                  (@♭ _ : (∀ t1 t2 → A t1 → A t2 → A (TmApp t1 t2))) →
                  (@♭ _ : (∀ f → (∀ t → A t → A (f t)) → A (TmAbs f))) →
                  (@♭ n : ℕ) (@♭ f : Vec Term n → Term) (ts : Vec Term n) →
                  (∀ i → A (lookup ts i)) → A (f ts)
