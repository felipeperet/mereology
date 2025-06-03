-- Intuitionistic Mereology in Agda
-- Based on apartness, excess, and weak excess primitives.
module Intuitionistic where

open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Domain of mereological entities.
postulate 𝔼 : Set

-- Primitive notion of appartness and its axioms.
postulate _≠_ : 𝔼 → 𝔼 → Set
infix 40 _≠_

postulate ≠-irrefl : ∀ (a : 𝔼) → ¬ (a ≠ a)
postulate ≠-sym : ∀ (a b : 𝔼) → a ≠ b → b ≠ a
postulate ≠-cotrans : ∀ (a b c : 𝔼) → a ≠ b → (a ≠ c) ⊎ (b ≠ c)
postulate ≠-tight : ∀ (a b : 𝔼) → ¬ (a ≠ b) → (a ≡ b)
