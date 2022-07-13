module Flat where

open import Agda.Primitive
open import Data.Vec
open import Data.Fin
open import Data.Nat
open import Relation.Binary.PropositionalEquality


data ♭ {@♭ l} (@♭ A : Set l) : Set l where
  to-♭ : @♭ A → ♭ A

from-♭ : ∀ {@♭ l} {@♭ A : Set l} → ♭ A → A
from-♭ (to-♭ x) = x

map-♭ : ∀ {@♭ l} {@♭ A B : Set l} → @♭ (A → B) → ♭ A → ♭ B
map-♭ f (to-♭ x) = to-♭ (f x)

to-♭-ℕ : ℕ → ♭ ℕ
to-♭-ℕ zero = to-♭ zero
to-♭-ℕ (suc n) = map-♭ suc (to-♭-ℕ n)

cong-♭ : ∀ {@♭ l₁} {l₂} {@♭ A : Set l₁} {B : Set l₂} (f : @♭ A → B) →
         ∀ {@♭ x₁ x₂} (ex : x₁ ≡ x₂) →
         f x₁ ≡ f x₂
cong-♭ f ex rewrite ex = refl

cong₂-♭ : ∀ {@♭ l₁ l₂} {l₃} {@♭ A : Set l₁} {@♭ B : Set l₂} {C : Set l₃} →
          ∀ (f : @♭ A → @♭ B → C) →
          ∀ {@♭ x₁ x₂} (ex : x₁ ≡ x₂) →
          ∀ {@♭ y₁ y₂} (ey : y₁ ≡ y₂) →
          f x₁ y₁ ≡ f x₂ y₂
cong₂-♭ f ex ey rewrite ex rewrite ey = refl
