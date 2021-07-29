{-# OPTIONS --rewriting #-}

module Type where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat
open import Data.Fin
open import Data.Vec

postulate Type : Set

postulate TyArr : Type → Type → Type

postulate TyAll : (Type → Type) → Type

postulate
  Type-elim : {@♭ l : Level} (@♭ A : Type → Set l) →
    (@♭ H-Arr : ∀ t1 t2 → A t1 → A t2 → A (TyArr t1 t2)) →
    (@♭ H-All : ∀ f → (∀ t → A t → A (f t)) → A (TyAll f)) →
    (@♭ t : Type) → A t
