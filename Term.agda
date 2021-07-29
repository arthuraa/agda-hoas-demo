{-# OPTIONS --rewriting --prop #-}

module Term where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Data.Fin
open import Data.Vec

postulate Term : Set

postulate TmApp : Term → Term → Term

postulate TmAbs : (Term → Term) → Term

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
