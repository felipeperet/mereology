-- Classical Mereology in Agda.
module Classical where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Domain of mereological entities.
postulate 𝔼 : Set

-- Primitive notion of parthood and its axioms.
postulate _⊑_ : 𝔼 → 𝔼 → Set
infix 50 _⊑_

postulate ⊑-refl : ∀ (x : 𝔼) → x ⊑ x
postulate ⊑-antisym : ∀ (x y : 𝔼) → x ⊑ y → y ⊑ x → x ≡ y
postulate ⊑-trans : ∀ (x y z : 𝔼) → x ⊑ y → y ⊑ z → x ⊑ z

-- Definition of Proper Parthood) x is a part of y but is not equal to y.
_⊏_ : 𝔼 → 𝔼 → Set
x ⊏ y = (x ⊑ y) × (x ≢ y)
infix 50 _⊏_

-- Definition of Overlap) x and y have a part in common.
_∘_ : 𝔼 → 𝔼 → Set
x ∘ y = ∃ λ z → (z ⊑ x) × (z ⊑ y)
infix 50 _∘_

-- Definition of Disjointness) x and y don't overlap.
disjoint : 𝔼 → 𝔼 → Set
disjoint x y = ¬ (x ∘ y)

-- Theorem) If x and y are equal, then x is part of y.
identity-implies-part : ∀ (x y : 𝔼) → x ≡ y → x ⊑ y
identity-implies-part x y refl = ⊑-refl _

-- Theorem) Nothing is a proper part of itself.
proper-part-irreflexive : ∀ (x : 𝔼) → ¬ (x ⊏ x)
proper-part-irreflexive x (_ , not-equal) = not-equal refl

-- Theorem) If x is a proper part of y, then y is not a part of x.
proper-part-asymmetric : ∀ (x y : 𝔼) → x ⊏ y → ¬ (y ⊑ x)
proper-part-asymmetric x y (x-part-y , not-equal) y-part-x =
  not-equal (⊑-antisym x y x-part-y y-part-x)
