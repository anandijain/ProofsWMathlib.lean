import ProofsWMathlib.Lean.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Partition

open Set

universe u
variable {α : Type u}


/-
2025/12/08

Proof Ch1 1.2 from Algebra Chapter 0:
Given a set S and an equivalence relation ~ on S.
P = {[a] | a ∈ S}

Prove that P defines a partition:
1) each x ∈ P nonempty,
2) ∀ x,y in P, x y disjoint
3) ⋃P = S

-/

/-
this example shows how to just use basic truths about Setoid, specifically transitivity
-/
example (r : Setoid α) (x y z : α) (h1 : r x y) (h2 : r y z) : r x z := by
    #check r.classes -- has type Set (Set α)
    exact r.trans h1 h2


/-
2)
-/
theorem classes_disjoint (r: Setoid a)
  (x y : Set a) (h1 : x ∈ r.classes) (h2 : y ∈ r.classes) (h3 : x ≠ y)
  : x ∩ y = ∅ := by
  


/-
3) S ⊆ ⋃X
the union of the classes covers the set over which the equivalence relation is defined

-/
theorem classes_cover_set (r : Setoid a) (x : a) : ∃ p, p ∈ r.classes ∧ x ∈ p := by
    -- this refine tactic breaks up the quantifier to take p = {y : a | r y x}
    -- then breaks up the and into showing this p in r.classes and x in p
    refine ⟨{y : a | r y x}, ?_, ?_⟩
    ·
        -- simp [Setoid.classes]
        simpa using (Setoid.mem_classes r x)
    ·
        -- set notation  x ∈ {y | r y x} is really just a lambda beta reduction where
        -- {y | r y x} is really fun y => r y x
        -- and x in notation becomes (fun y => r y x) x
        -- this becomes just the proposition r x x. so change does this
        -- then we exact with r.refl that is a term of type r x x
        change r x x
        -- #check r.refl x
        exact r.refl x

theorem classes_contain_set (r : Setoid a) : (Set.univ : Set a) ⊆ sUnion r.classes := by
  intro x hx
  rcases classes_cover_set (r := r) x with ⟨p, hp_classes, hx_in_p⟩
  exact (Set.mem_sUnion).2 ⟨p, hp_classes, hx_in_p⟩


theorem sUnion_classes_subset_univ (r : Setoid a) :
    sUnion r.classes ⊆ (Set.univ : Set a) := by
  intro x hx
  exact Set.mem_univ x


theorem set_eq_of_subset_of_subset' (A B : Set α) (hAB : A ⊆ B) (hBA : B ⊆ A) :
    A = B := by
  exact Set.Subset.antisymm hAB hBA

theorem sUnion_classes_equals_set (r : Setoid a) : (Set.univ : Set a) = sUnion r.classes := by
  exact Set.Subset.antisymm (classes_contain_set r) (sUnion_classes_subset_univ r)
