-- Intuitionistic Mereology in Agda
-- Based on apartness and excess primitives.
module Intuitionistic where

open import Data.Product
open import Data.Sum
open import Relation.Nullary

-- Domain of mereological entities.
postulate 𝔼 : Set

-- Primitive notion of appartness and its axioms.
-- Appartness is a constructive form of inequality.
postulate _≠_ : 𝔼 → 𝔼 → Set
infix 40 _≠_

postulate ≠-irrefl : ∀ (x : 𝔼) → ¬ (x ≠ x)
postulate ≠-sym : ∀ (x y : 𝔼) → x ≠ y → y ≠ x
postulate ≠-cotrans : ∀ (x y z : 𝔼) → x ≠ y → (x ≠ z) ⊎ (z ≠ y)

-- Primitive notion of excess and its axioms.
-- Excess is a constructive form of the negation of a partial order.
postulate _≰_ : 𝔼 → 𝔼 → Set
infix 40 _≰_

postulate ≰-irrefl : ∀ (x : 𝔼) → ¬ (x ≰ x)
postulate ≰-cotrans : ∀ (x y z : 𝔼) → x ≰ y → (x ≰ z) ⊎ (z ≰ y)

-- Excess is co-antisymmetric (weakly linear).
postulate ≠-weakly-linear : ∀ (x y : 𝔼) → x ≠ y → (x ≰ y) ⊎ (y ≰ x)

-- Excess implies appartness.
postulate ≰-implies-≠ : ∀ (x y : 𝔼) → x ≰ y → x ≠ y

-- Def) Parthood.
-- We say that x is a part of y if x does not have any parts that y lacks.
-- In other words, every part of x is also a part of y.
_≤_ : 𝔼 → 𝔼 → Set
x ≤ y = ¬ (x ≰ y)

-- Def) Equality.
-- We say that x is equal to y if we cannot prove that x and y are apart.
-- Note: This is a negative characterization of equality.
_≡_ : 𝔼 → 𝔼 → Set
x ≡ y = ¬ (x ≠ y)

-- Def) Overlap.
-- We say that x and y overlap if there is a z such that z is part of x and z is also part of y.
-- In other words, x and y have a part in common.
_∘_ : 𝔼 → 𝔼 → Set
x ∘ y = ∃[ z ] (z ≤ x × z ≤ y)
