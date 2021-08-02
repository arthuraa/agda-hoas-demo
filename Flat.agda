module Flat where

open import Agda.Primitive
open import Data.Vec
open import Data.Fin
open import Data.Nat

data ♭ {@♭ l} (@♭ A : Set l) : Set l where
  to-♭ : @♭ A → ♭ A

from-♭ : ∀ {@♭ l} {@♭ A : Set l} → ♭ A → A
from-♭ (to-♭ x) = x

map-♭ : ∀ {@♭ l} {@♭ A B : Set l} → @♭ (A → B) → ♭ A → ♭ B
map-♭ f (to-♭ x) = to-♭ (f x)

to-♭-ℕ : ℕ → ♭ ℕ
to-♭-ℕ zero = to-♭ zero
to-♭-ℕ (suc n) = map-♭ suc (to-♭-ℕ n)
