--  (Basic Principles of Mereology).
namespace Mereology

variable {Entity : Type}

-- Definition of  Parthood) Fundamental Mereological Relation.
def is_part_of (x y : Entity) : Prop := sorry
infix:50 " ⊑ " => is_part_of

-- Simons Axioms:
-- 1. Axiom of Reflexivity) Everything is a part of itself.
axiom reflexivity : ∀ (x : Entity), x ⊑ x
-- 2. Axiom of Transitivity): If x is a part of y and y is a part of z, then x is part of z.
axiom transitivity : ∀ (x y z : Entity), x ⊑ y → y ⊑ z → x ⊑ z
-- 3. Axiom of Antisymmetry) If x is a part of y, and y is a part of x, then x = y.
axiom antisymmetry : ∀ (x y : Entity), x ⊑ y → y ⊑ x → x = y

-- Definition of Proper Parthood) x is a part of y but is not equal to y.
def proper_part_of (x y : Entity) := x ⊑ y ∧ x ≠ y
infix:50 " ⊏ " => proper_part_of

-- Definition of Overlap) x and y have a part in common.
def overlaps (x y : Entity) := ∃ z, z ⊑ x ∧ z ⊑ y
infix:50 " ○ " => overlaps

-- Definition of Disjointness) x and y don't overlap.
def disjoint (x y : Entity) := ¬(x ○ y)

-- Theorem) If x and y are equal, then x is part of y.
theorem identity_implies_part (x y : Entity) : x = y → x ⊑ y := by
  intro h
  rw [h]
  apply reflexivity

-- Theorem) Nothing is a proper part of itself.
theorem proper_part_irreflexive (x : Entity) : ¬(x ⊏ x) := by
  intro h
  cases h with
  | intro _ h₂ => apply h₂ rfl

-- Theorem) If x is a proper part of y, then y is not a part of x.
theorem proper_part_asymmetric (x y : Entity) : x ⊏ y → ¬(y ⊑ x) := by
  intros h₁ h₂
  cases h₁ with
  | intro h₁₁ _ =>
    have : x = y := antisymmetry x y h₁₁ h₂
    contradiction

end Mereology

namespace Temporal

variable {Time : Type}
variable (before : Time → Time → Prop)

-- Definition of Temporal Parthood) x is a part of y at time t.
def is_part_of_at {Entity} (x y : Entity) (t : Time) : Prop := sorry
notation:50 x " ⊑ " "[" t "] " y => is_part_of_at x y t

-- Definition of Eternal Parthood) x is always a part of y (when both exist).
def timeless_part_of {Entity} (x y : Entity) : Prop :=
  ∀ t : Time, x ⊑ [t] y

-- Definition of Temporary Parthood) x is sometimes a part of y.
def temporary_part_of {Entity} (x y : Entity) : Prop :=
  (∃ t : Time, x ⊑ [t] y) ∧ (∃ t : Time, ¬(x ⊑ [t] y))

end Temporal

namespace Embodiments

variable {Time : Type}

-- A Rigid Embodiment is made of:
-- 1. Material parts (stuff)
-- 2. Formal part (relation)

structure RigidEmbodiment (Entity : Type) where
  material_parts : List Entity
  formal_part : Entity → Entity → Prop -- Binary relation for simplicity

-- Fine's R1 Principle:
-- "a,b,c/R exists at time t if and only if R holds for a,b,c at time t"
def exists_at {Entity : Type} (e : RigidEmbodiment Entity) (t : Time) : Prop :=
  match e.material_parts with
  | [a, b] => e.formal_part a b
  | _ => True

-- Concrete example: Ham Sandwich
-- Material parts: bread1, ham, bread2
-- Formal part: "ham is between bread1 and bread2"

section Example
variable {Entity : Type} (bread1 ham bread2 : Entity)

def between (x y z : Entity) : Prop := sorry -- "y is between x and z"

def ham_sandwich : RigidEmbodiment Entity :=
  ⟨[bread1, bread2], λ x y => between x ham y⟩

end Example

end Embodiments

-- Definition of mereological simple.
def is_simple {Entity : Type} (x : Entity) : Prop := ∀ y, y ⊑ x → y = x

-- Definition of mereological simple.
def mereological_sum {Entity : Type} (xs : List Entity) : Entity := sorry
