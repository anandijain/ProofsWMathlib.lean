import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Setoid.Partition

/-
1.2.  Prove that if ∼ is an equivalence relation on a set S, then the corresponding
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
  -- refine is rewriting the definition of exists unique into an exists goal and a unique goal
  refine ⟨{z : a | r z x}, ?_, ?_⟩
  · -- prove it’s in classes and contains x
    -- the way we do this is to effectively show that the b is the quivalence class of x
    -- tjis refine destrucrures the and, so that we show {z | r z x} is a class
    -- and x in this separately
    refine ⟨?_, ?_⟩
    · simp [Setoid.classes]
      use x
    · exact r.refl x
  · intro y hy -- now we show that forall y st y class and x in y implies [x] = [y]
    rcases hy with ⟨hy_classes, xin⟩
    -- if y is a class and x in y, then we can show that forall z in [x], r z y
    -- by symm we also show forall zz in [y] r zz x.
    -- this shows [x] ⊆ [y] and [y] ⊆ [x] thus [x] = [y]

    -- we show here that xc = [x] is a class and x ∈ xc

    let xc : Set a := {z : a | r z x}
    have hxc : x ∈ xc := by exact r.refl x

    have xc_class : xc ∈ r.classes := by
      simp [xc, Setoid.classes]
      use x

    exact nondisjoint_classes_eq r hy_classes xc_class ⟨xin, hxc⟩

theorem setoid_is_partition (r : Setoid a) : Setoid.IsPartition r.classes := by
  rw [Setoid.IsPartition]
  constructor
  · exact classes_nonempty r
  · exact covers_unique r
