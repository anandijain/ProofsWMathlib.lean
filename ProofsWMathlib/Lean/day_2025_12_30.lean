import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Setoid.Partition
open Function

/-
Algebra Chapter 0. I.1.2

Prove that if ∼ is an equivalence relation on a set S, then the corresponding
family P∼ defined in §1.5 is indeed a partition of S: that is, its elements are
nonempty, disjoint, and their union is S. [§1.5]
-/

theorem setoid_trans (r : Setoid a) (x y z : a) (h : (r x y) ∧ (r y z)) : (r x z) := by
  rcases h with ⟨hP, hQ⟩
  exact r.trans hP hQ

theorem setoid_refl (r : Setoid a) : (∀ x : a, r x x) := by
    exact r.refl

theorem classes_nonempty (r : Setoid a) : ∅ ∉ r.classes := by
  simp [Setoid.classes]
  intro x h
  -- intro h
  have hx : x ∈ {x_1 | r x_1 x} := by
    apply r.refl x
  have he : x ∈ (∅ : Set a) := by
    -- simp [hx] at h
    rw [h]
    exact hx
  exact he

/-
it will be easier to show ∀ a, ∃! b ∈ c, a ∈ b then pw disjoint
-/
theorem classes_pw_disjoint (r : Setoid a) : (r.classes.PairwiseDisjoint id) := by
  -- simp [Set.PairwiseDisjoint, Set.Pairwise, Disjoint]
  -- exact r.classes.PairwiseDisjoint id
  -- simpa using (Setoid.IsPartition.pairwiseDisjoint (hc := Setoid.isPartition_classes r))
  have hc : Setoid.IsPartition r.classes := Setoid.isPartition_classes r
  simp [Setoid.IsPartition] at hc
  sorry
/-

the general proof is to deconstruct an iff of xe in x -> xe in y and xe in y -> xe in x.

this is a direct result of the transitivity of r.

we show that r z a1 and r z a2 => r a1 a2. then since we know xe in x, r xe a1, thus r xe a2.

and vice versa

-/
theorem nondisjoint_classes_eq (r : Setoid a) (h1 : x ∈ r.classes) (h2 : y ∈ r.classes)
  (hz : (z : a) ∈ x ∧ z ∈ y) : x = y := by
  rcases hz with ⟨inx, iny⟩

  rcases (by simpa [Setoid.classes] using h1) with ⟨a1, rfl⟩
  rcases (by simpa [Setoid.classes] using h2) with ⟨a2, rfl⟩

  have hzx : r z a1 := by exact inx
  have hzy : r z a2 := by exact iny
  have hxy : r a1 a2 := by exact r.trans (r.symm hzx) hzy

  ext xe
  constructor

  · intro hxe
    have hxex : r xe a1 := by simpa using hxe
    change r xe a2
    exact r.trans hxex hxy

  · intro hxe
    have hxex : r xe a2 := by simpa using hxe
    change r xe a1
    exact r.trans hxex (r.symm hxy)


theorem exists_class (r : Setoid a) :(∀ x : a, ∃ b ∈ r.classes, x ∈ b) := by
  intro x
  -- let xc := {z | r z x}
  -- then show that xc in r.classes and use xc as witness for b
  use {z | r z x}
  constructor
  · rw [Setoid.classes]
    use x
  · exact r.refl x

theorem covers_unique (r : Setoid a) : (∀ x : a, ∃! b ∈ r.classes, x ∈ b) := by
  intro x
  rcases exists_class r x with ⟨b, hb_classes, hxb⟩
  refine ⟨b, ?_, ?_⟩
  · change b ∈ r.classes ∧ x ∈ b
    exact ⟨hb_classes, hxb⟩
  · intro y
    simp
    intro hy hxe
    exact nondisjoint_classes_eq r hy hb_classes ⟨hxe, hxb⟩

theorem setoid_is_partition (r : Setoid a) : Setoid.IsPartition r.classes := by
  rw [Setoid.IsPartition]
  constructor
  · exact classes_nonempty r
  · exact covers_unique r


section right_inv_imp_surjective
/-
ACh0: I.2.2

2.2.  Prove statement (2) in Proposition 2.1. You may assume that given a family
of disjoint nonempty subsets of a set, there is a way to choose one element in each
member of the family13. [§2.5, V.3.3]

Proposition 2.1. Assume A = ∅, and let f : A → B be a function. Then
(1) f has a left-inverse if and only if it is injective.
(2) f has a right-inverse if and only if it is surjective.


(1)
  =>) if has left inv then g circ f = id_A
    a1 and a2 in A then gf(a1) = a1 gf(a2) = a2 so gf(a1) = gf(a2) only if a1=a2 (defn of injective)

-/

/-

this version of the proof attempts to use as much mathlib as possible
-/
theorem mathlib_inj_iff_has_left_inv (f : A -> B) [Nonempty A]
  : Injective f ↔ HasLeftInverse f := by
  constructor
  · sorry
  . exact Function.HasLeftInverse.injective


/-
using less mathlib
-/
theorem mathlib_inj_iff_has_left_inv2 (f : A -> B) (hne: Nonempty A)
  : Injective f ↔ HasLeftInverse f := by
  constructor
  · classical
    intro hinj
    -- so since a ≠ a' => f a ≠ f a' for each a in A, we can define g(f(a)) = a
    -- this satisfies the definition of a partial left inverse. so then since f is not
    -- guaranteed to be surjective, we choose an arbitrary element of a to send (B \ im f) to
    let g : B -> A :=
     fun b => dite (∃ a, f a = b)
              (fun h => Classical.choose h)
              (fun _ => Classical.choice hne)
    -- now we just need to show the left inverse property
    -- that ∀a g(f(a)) = a and that g is a total function
    -- g is already proved to be total, otherwise we could not construct a term of type B->A
    -- now all we need to do is show the left inv prop.
    refine ⟨g, ?_⟩
    intro a
    have hex : ∃ a' : A, f a' = f a := ⟨a, rfl⟩

  -- unfold g at (f a) and reduce the `dite`/`if` using hex
  -- after simp: goal becomes Classical.choose hex = a
    have blorp : Classical.choose hex = a := by
      apply hinj
      -- choose_spec hex : f (choose hex) = f a
      simpa using (Classical.choose_spec hex)

    -- now finish
    simp [g, hex, blorp]
  .
    -- we know that for all a in A g(f(a)) = a. this is hg. (definition of left inv)
    -- then the hypothesis of injectivity is that we have two elements a1 and a2 with the same image
    -- we assume then f a1 = f a2. to show that f is injective we need to show that a1 = a2
    -- since we also know that (g circ f) (a) = a = g(f(a))
    -- we can apply g to both sides and apply the left inverse identity to get g(f(a1)) = g(f(a2))
    -- then a1 and a2 must have been equal

    intro hl
    obtain ⟨g, hg⟩ := hl
    have hg_ := hg
    rw [LeftInverse] at hg
    rw [Injective]
    intros a1 a2 hf
    have foo : a1 = g (f a1) := by exact (hg a1).symm
    rw [hf] at foo
    rw [hg] at foo
    exact foo

-- theorem inj_iff_has_left_inv (f : A -> B) :
--   Function.Injective f ↔ ∃ (g : B -> A), g ∘ f = id := by
--   constructor
--   -- =>) injectivity implies left inv
--   · rw [Function.Injective]
--     intro finj
--     exact Function.Injective.exists_leftInverse

end right_inv_imp_surjective

/-
theorem demonstrating Classical.choose
-/
theorem hasa_prop (h : ∃ _ : A, True) : Nonempty A := by
  classical
  have foo : A := Classical.choose h
  exact ⟨foo⟩

/-
example showing how to use a element from nonempty type (via choice, not choose!)
not sure whats up exactly with noncomputable
-/
noncomputable example (hne : Nonempty A) : A := by
  classical
  exact Classical.choice hne


#check some 3



/-
following is one way to show that for a left inv g of f that g is surjective
  -- assume for contradiction that there is an a ∈ A st ∄b, g(b) = a (thus g not surj)
  -- then by definition of left inverse g(f(x)) = id_A, so such an a dne

but it is far easier to take a as any elt of A, then use (f a) as the witness for existential
then the definition of left inv gives a proof that this g (f a) = a.
since a was arbitrary, g is surjective.
-/
theorem g_surj_if_left_inv (f : A -> B) (h : LeftInverse g f) : (Surjective g) := by
  -- have finj : Injective f := by exact LeftInverse.injective h
  intro a
  refine ⟨f a, h a⟩


-- theorem inv_bij_is_bij (f : A -> B) (hl : LeftInverse g f) (hr : RightInverse g f) : Bijective g := by
--   have finj : Injective f := by exact (LeftInverse.injective g f)
--   have fsurj : Surjective f  := by exact (RightInverse.surjective g f)
