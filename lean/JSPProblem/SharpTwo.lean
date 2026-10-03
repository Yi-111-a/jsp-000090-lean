import JSPProblem.Segment

/-!
# JSP-000090, round 137 — `JSPProblem/SharpTwo.lean`: **the constant `2` of Erdős Problem #73 at
# `k = 1` is optimal**, machine-checked on six vertices

Attack family 66, Part 6.  The instances proved in `JSPProblem/AttachPoints.lean` (round 136) and
`JSPProblem/Segment.lean` (this round) all deliver `CloseToBipartite 2 G` at `LocIndep 1`, and the
search `discovery/JSP-000090/r137.c` (question `Q7`) measures, over the **986 787** graphs with
`LocIndep 1` on `n ≤ 7` vertices, that `max τ_odd = 2`, the first example having **six** vertices.
This file makes that optimality a Lean theorem.

The witness `sharp2` on `Fin 6` has the nine edges

```
0-1  0-2  0-4  0-5  1-2  1-3  1-5  2-3  2-4
```

so its odd girth is `3`, it contains the four triangles `{0, 1, 2}`, `{0, 2, 4}`, `{1, 2, 3}`,
`{0, 1, 5}`, and it satisfies Erdős's hypothesis with `k = 1`.  Proved here:

* **`JSP90.locIndep_one_sharp2`** — `sharp2` satisfies `LocIndep 1` (exhaustive kernel decision over
  the `2 ^ 6` vertex sets), so it is a genuine member of the class of JSP-000090;
* **`JSP90.hitsOddCycles_sharp2_pair`** — the pair `{0, 2}` meets **every** odd cycle of `sharp2`,
  hence **`JSP90.closeToBipartite_two_sharp2`**: `CloseToBipartite 2 sharp2`;
* **`JSP90.not_closeToBipartite_one_sharp2`** — and **no single vertex does**: for every `v ∈ Fin 6`
  there is a triangle of `sharp2` avoiding `v`.  So `Erdős73On 1 1` is **false** and the constant `2`
  of the sharp case cannot be lowered; together with
  `JSP90.erdos73On_one_two_of_attachThreeResidualRefined` this pins the optimal value of `f(1)`;
* **`JSP90.boundary_sharp2_T`, `JSP90.card_attachPoints_sharp2`, `JSP90.card_boundary_sharp2`** — the
  fan of the triangle `{0, 1, 2}` is `{3, 4, 5}` (size `3`) and its attachment points are
  `{0, 1, 2}` (size `3`), while the certificate `{0, 2}` lies in the attachment points.  This is the
  smallest instance of `JSP90.AttachThreeResidualRefined` (round 137's residual): it is non-vacuous on
  six vertices and its constant is optimal there.  It also shows why neither of the round-134/135
  "small object" routes can work: **both** the fan and the attachment points have three elements.
-/

namespace JSP90

open Finset Fintype

noncomputable section

/-! ### The six-vertex witness `sharp2` -/

section SharpTwo

/-- **Adjacency in `sharp2`**: the nine edges

```
0-1  0-2  0-4  0-5  1-2  1-3  1-5  2-3  2-4
```

as a formula on `Fin.val`.  The three vertices `3`, `4`, `5` have degree `2`, which is what makes the
odd cycles easy to classify. -/
def sharp2Adj (v w : Fin 6) : Prop :=
  v.val ≠ w.val ∧
    ((v.val = 0 ∧ (w.val = 1 ∨ w.val = 2 ∨ w.val = 4 ∨ w.val = 5)) ∨
      (w.val = 0 ∧ (v.val = 1 ∨ v.val = 2 ∨ v.val = 4 ∨ v.val = 5)) ∨
      (v.val = 1 ∧ (w.val = 2 ∨ w.val = 3 ∨ w.val = 5)) ∨
      (w.val = 1 ∧ (v.val = 2 ∨ v.val = 3 ∨ v.val = 5)) ∨
      (v.val = 2 ∧ (w.val = 3 ∨ w.val = 4)) ∨
      (w.val = 2 ∧ (v.val = 3 ∨ v.val = 4)))

/-- **`sharp2Adj` is decidable**: it is a formula about `Nat`s. -/
instance instDecidableRelSharp2Adj (v w : Fin 6) : Decidable (sharp2Adj v w) := by
  unfold sharp2Adj
  infer_instance

/-- **The six-vertex sharpness witness.** -/
def sharp2 : SimpleGraph (Fin 6) where
  Adj := sharp2Adj
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

@[simp] theorem sharp2_adj {v w : Fin 6} : sharp2.Adj v w ↔ sharp2Adj v w := by
  unfold SimpleGraph.Adj sharp2
  rfl


/-- Adjacency of `sharp2` is decidable, so that every finite statement of this file is a kernel
computation. -/
instance instDecidableRelSharp2 : DecidableRel sharp2.Adj :=
  fun v w => inferInstanceAs (Decidable (sharp2Adj v w))

/-- One computable `DecidableEq (Fin n)` for the whole file (the trick of `JSPProblem/Fan4.lean`),
so that every finite statement of this file is a kernel computation.  It is declared **before** any
concrete finset of this file, so that all of them are built with this single instance — mixing two
instances in one file makes two syntactically identical finsets different terms, which Lean reports as
"synthesized type class instance is not definitionally equal". -/
local instance attachSharpTwoClassicalFin (n : ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

/-- **DISTINCT `Fin`s FROM THEIR VALUES.** -/
theorem fin_ne_of_val_ne {n : ℕ} {x y : Fin n} (h : x.val ≠ y.val) : x ≠ y := by
  intro hc
  exact h (congrArg Fin.val hc)



/-! ### The six vertices are pairwise distinguishable

With the classical `DecidableEq` in place (see the remark above), neither `decide` nor `simp` can
discharge an equation between two `Fin 6` numerals: they would have to run a decision procedure built
from `Classical.decEq`.  The fifteen facts below are proved once, from the *values* (a `Nat`
computation), and are then available to `simp` everywhere in this file. -/

section Numerals

@[simp] theorem fin6_ne_zero_one : ¬((0 : Fin 6) = 1) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_zero_two : ¬((0 : Fin 6) = 2) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_zero_three : ¬((0 : Fin 6) = 3) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_zero_four : ¬((0 : Fin 6) = 4) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_zero_five : ¬((0 : Fin 6) = 5) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_one_zero : ¬((1 : Fin 6) = 0) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_one_two : ¬((1 : Fin 6) = 2) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_one_three : ¬((1 : Fin 6) = 3) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_one_four : ¬((1 : Fin 6) = 4) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_one_five : ¬((1 : Fin 6) = 5) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_two_zero : ¬((2 : Fin 6) = 0) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_two_one : ¬((2 : Fin 6) = 1) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_two_three : ¬((2 : Fin 6) = 3) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_two_four : ¬((2 : Fin 6) = 4) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_two_five : ¬((2 : Fin 6) = 5) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_three_zero : ¬((3 : Fin 6) = 0) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_three_one : ¬((3 : Fin 6) = 1) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_three_two : ¬((3 : Fin 6) = 2) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_three_four : ¬((3 : Fin 6) = 4) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_three_five : ¬((3 : Fin 6) = 5) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_four_zero : ¬((4 : Fin 6) = 0) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_four_one : ¬((4 : Fin 6) = 1) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_four_two : ¬((4 : Fin 6) = 2) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_four_three : ¬((4 : Fin 6) = 3) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_four_five : ¬((4 : Fin 6) = 5) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_five_zero : ¬((5 : Fin 6) = 0) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_five_one : ¬((5 : Fin 6) = 1) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_five_two : ¬((5 : Fin 6) = 2) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_five_three : ¬((5 : Fin 6) = 3) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin6_ne_five_four : ¬((5 : Fin 6) = 4) :=
  fin_ne_of_val_ne (by decide)

@[simp] theorem fin3_ne_zero_one : ¬(((0 : Fin 3)) = 1) := fin_ne_of_val_ne (by decide)

@[simp] theorem fin3_ne_zero_two : ¬(((0 : Fin 3)) = 2) := fin_ne_of_val_ne (by decide)

@[simp] theorem fin3_ne_one_zero : ¬(((1 : Fin 3)) = 0) := fin_ne_of_val_ne (by decide)

@[simp] theorem fin3_ne_one_two : ¬(((1 : Fin 3)) = 2) := fin_ne_of_val_ne (by decide)

@[simp] theorem fin3_ne_two_zero : ¬(((2 : Fin 3)) = 0) := fin_ne_of_val_ne (by decide)

@[simp] theorem fin3_ne_two_one : ¬(((2 : Fin 3)) = 1) := fin_ne_of_val_ne (by decide)

end Numerals

/-! ### The three vertices of degree two -/

theorem neigh_sharp2_three : Neigh sharp2 3 = {1, 2} := by
  ext w
  simp only [Neigh, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, sharp2_adj]
  fin_cases w <;> simp [sharp2Adj]

theorem neigh_sharp2_four : Neigh sharp2 4 = {0, 2} := by
  ext w
  simp only [Neigh, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, sharp2_adj]
  fin_cases w <;> simp [sharp2Adj]

theorem neigh_sharp2_five : Neigh sharp2 5 = {0, 1} := by
  ext w
  simp only [Neigh, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, sharp2_adj]
  fin_cases w <;> simp [sharp2Adj]

section LocIndep

/-- The computable instance, shadowing `JSP90.attachSharpTwoClassicalFin` inside this section only. -/
local instance instDecidableEqFinSharpTwoCompute : DecidableEq (Fin 6) := instDecidableEqFin 6

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **`LocIndep 1 sharp2`**: every vertex set of `sharp2` carries an independent set of size
`≥ (|X| - 1) / 2`, by exhaustive decision over the `2 ^ 6` vertex sets.  So `sharp2` is a member of the
class of graphs covered by Erdős Problem #73 with `k = 1`. -/
theorem locIndep_one_sharp2 : LocIndep 1 sharp2 := by
  unfold LocIndep
  decide

end LocIndep



/-! ### The four triangles of `sharp2` -/

/-- **A CYCLE NUMBERING OF A TRIANGLE.** -/
def sharp2TCyc (a b c : Fin 6) : Fin 3 → Fin 6 :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else c

/-- **THREE PAIRWISE ADJACENT VERTICES ARE AN ODD CYCLE.** -/
theorem isOddCycle_tri_of_adj {a b c : Fin 6}
    (habc : sharp2.Adj a b ∧ sharp2.Adj b c ∧ sharp2.Adj c a)
    (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c) : IsOddCycle sharp2 {a, b, c} := by
  refine ⟨3, sharp2TCyc a b c, rfl, by omega, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [sharp2TCyc]
    all_goals first
      | exact habc.1.symm | exact habc.2.1.symm | exact habc.2.2.symm
      | exact habc.1 | exact habc.2.1 | exact habc.2.2
  · intro j
    fin_cases j
    · show sharp2.Adj a b
      exact habc.1
    · show sharp2.Adj b c
      exact habc.2.1
    · show sharp2.Adj c a
      exact habc.2.2
  · intro x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨⟨0, by decide⟩, by simp [sharp2TCyc]⟩
      · exact ⟨⟨1, by decide⟩, by simp [sharp2TCyc]⟩
      · exact ⟨⟨2, by decide⟩, by simp [sharp2TCyc]⟩
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [sharp2TCyc]

theorem adj_sharp2_01 : sharp2.Adj 0 1 := by simp [sharp2Adj]
theorem adj_sharp2_02 : sharp2.Adj 0 2 := by simp [sharp2Adj]
theorem adj_sharp2_04 : sharp2.Adj 0 4 := by simp [sharp2Adj]
theorem adj_sharp2_05 : sharp2.Adj 0 5 := by simp [sharp2Adj]
theorem adj_sharp2_12 : sharp2.Adj 1 2 := by simp [sharp2Adj]
theorem adj_sharp2_13 : sharp2.Adj 1 3 := by simp [sharp2Adj]
theorem adj_sharp2_15 : sharp2.Adj 1 5 := by simp [sharp2Adj]
theorem adj_sharp2_23 : sharp2.Adj 2 3 := by simp [sharp2Adj]
theorem adj_sharp2_24 : sharp2.Adj 2 4 := by simp [sharp2Adj]

/-- **THE TRIANGLE `{0, 1, 2}` IS AN ODD CYCLE.** -/
theorem isOddCycle_sharp2_012 : IsOddCycle sharp2 {0, 1, 2} := by
  have hne : (0 : Fin 6) ≠ 1 ∧ (0 : Fin 6) ≠ 2 ∧ (1 : Fin 6) ≠ 2 :=
    ⟨fin_ne_of_val_ne (by decide), fin_ne_of_val_ne (by decide), fin_ne_of_val_ne (by decide)⟩
  exact isOddCycle_tri_of_adj ⟨adj_sharp2_01, adj_sharp2_12, adj_sharp2_02.symm⟩ hne

/-- **THE TRIANGLE `{0, 2, 4}` IS AN ODD CYCLE.** -/
theorem isOddCycle_sharp2_024 : IsOddCycle sharp2 {0, 2, 4} := by
  have hne : (0 : Fin 6) ≠ 2 ∧ (0 : Fin 6) ≠ 4 ∧ (2 : Fin 6) ≠ 4 :=
    ⟨fin_ne_of_val_ne (by decide), fin_ne_of_val_ne (by decide), fin_ne_of_val_ne (by decide)⟩
  exact isOddCycle_tri_of_adj ⟨adj_sharp2_02, adj_sharp2_24, adj_sharp2_04.symm⟩ hne

/-- **THE TRIANGLE `{1, 2, 3}` IS AN ODD CYCLE.** -/
theorem isOddCycle_sharp2_123 : IsOddCycle sharp2 {1, 2, 3} := by
  have hne : (1 : Fin 6) ≠ 2 ∧ (1 : Fin 6) ≠ 3 ∧ (2 : Fin 6) ≠ 3 :=
    ⟨fin_ne_of_val_ne (by decide), fin_ne_of_val_ne (by decide), fin_ne_of_val_ne (by decide)⟩
  exact isOddCycle_tri_of_adj ⟨adj_sharp2_12, adj_sharp2_23, adj_sharp2_13.symm⟩ hne

/-- **THE TRIANGLE `{0, 1, 5}` IS AN ODD CYCLE.** -/
theorem isOddCycle_sharp2_015 : IsOddCycle sharp2 {0, 1, 5} := by
  have hne : (0 : Fin 6) ≠ 1 ∧ (0 : Fin 6) ≠ 5 ∧ (1 : Fin 6) ≠ 5 :=
    ⟨fin_ne_of_val_ne (by decide), fin_ne_of_val_ne (by decide), fin_ne_of_val_ne (by decide)⟩
  exact isOddCycle_tri_of_adj ⟨adj_sharp2_01, adj_sharp2_15, adj_sharp2_05.symm⟩ hne

/-! ### Part 1 — the pair `{0, 2}` meets every odd cycle -/

/-- **THE ODD CYCLES OF `sharp2` HAVE THREE OR FIVE VERTICES.** -/
theorem card_le_six_of_isOddCycle {C : Finset (Fin 6)} (hC : IsOddCycle sharp2 C) :
    C.card = 3 ∨ C.card = 5 := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hCcard : C.card = m := card_eq_cyclicOrder f hinj hCmem
  have hle : m ≤ 6 := by
    have h2 := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin m)))
      (t := (Finset.univ : Finset (Fin 6))) (f := f)
      (fun x _ => Finset.mem_univ (f x)) (fun _ _ _ _ hxy => hinj hxy)
    simpa using h2
  rw [hCcard]
  omega

/-- **A TRIANGLE OF `sharp2` CONTAINS `0` OR `2`.**  The three vertices of a triangle are pairwise
adjacent, so a vertex among `3, 4, 5` pins the triangle down to `{1, 2, 3}`, `{0, 2, 4}` or
`{0, 1, 5}`; a triangle inside `{0, 1, 2}` is `{0, 1, 2}`. -/
theorem zero_or_two_of_isOddCycle_card_three {C : Finset (Fin 6)} (hC : IsOddCycle sharp2 C)
    (h3 : C.card = 3) : 0 ∈ C ∨ 2 ∈ C := by
  by_cases hex : (C ∩ ({3, 4, 5} : Finset (Fin 6))).Nonempty
  · obtain ⟨v, hv⟩ := hex
    rcases Finset.mem_inter.mp hv with ⟨hvC, hv345⟩
    have hsub : C ⊆ insert v (Neigh sharp2 v) := by
      intro x hx
      by_cases hxv : x = v
      · rw [hxv]
        exact Finset.mem_insert.mpr (Or.inl rfl)
      · refine Finset.mem_insert.mpr (Or.inr ?_)
        rw [mem_neigh]
        exact adj_of_isOddCycle_card_three hC h3 hvC hx (Ne.symm hxv)
    rcases Finset.mem_insert.mp hv345 with hv3 | hv45
    · rcases hv3 with rfl
      rw [neigh_sharp2_three] at hsub
      have hCeq : C = insert 3 ({1, 2} : Finset (Fin 6)) :=
        Finset.eq_of_subset_of_card_le hsub (by rw [h3]; simp)
      rw [hCeq]
      exact Or.inr (by simp)
    · rcases Finset.mem_insert.mp hv45 with hv4 | hv5
      · rcases hv4 with rfl
        rw [neigh_sharp2_four] at hsub
        have hCeq : C = insert 4 ({0, 2} : Finset (Fin 6)) :=
          Finset.eq_of_subset_of_card_le hsub (by rw [h3]; simp)
        rw [hCeq]
        exact Or.inl (by simp)
      · rcases Finset.mem_singleton.mp hv5 with rfl
        rw [neigh_sharp2_five] at hsub
        have hCeq : C = insert 5 ({0, 1} : Finset (Fin 6)) :=
          Finset.eq_of_subset_of_card_le hsub (by rw [h3]; simp)
        rw [hCeq]
        exact Or.inl (by simp)
  · have hsub : C ⊆ ({0, 1, 2} : Finset (Fin 6)) := by
      intro x hx
      have hx345 : x ∉ ({3, 4, 5} : Finset (Fin 6)) := by
        intro hxm
        exact hex ⟨x, Finset.mem_inter.mpr ⟨hx, hxm⟩⟩
      fin_cases x <;> simp_all [Finset.mem_insert, Finset.mem_singleton]
    have hCeq : C = ({0, 1, 2} : Finset (Fin 6)) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [h3]; simp)
    rw [hCeq]
    exact Or.inl (by simp)

/-- **A FIVE-VERTEX SET OF `Fin 6` CONTAINS `0` OR `2`**: a five-element set misses exactly one of the
six vertices, and the two vertices `0` and `2` cannot both be missed. -/
theorem zero_or_two_of_card_five {C : Finset (Fin 6)} (h5 : C.card = 5) : 0 ∈ C ∨ 2 ∈ C := by
  by_contra hcon
  have h0 : (0 : Fin 6) ∉ C := fun h => hcon (Or.inl h)
  have h2 : (2 : Fin 6) ∉ C := fun h => hcon (Or.inr h)
  have hsub : C ⊆ ({1, 3, 4, 5} : Finset (Fin 6)) := by
    intro x hx
    fin_cases x <;> simp_all [Finset.mem_insert, Finset.mem_singleton]
  have hcard : ({1, 3, 4, 5} : Finset (Fin 6)).card = 4 := by
    have e : ({1, 3, 4, 5} : Finset (Fin 6)) = insert 1 (insert 3 (insert 4 (insert 5 ∅))) := rfl
    rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp)]
    simp
  have hle : C.card ≤ ({1, 3, 4, 5} : Finset (Fin 6)).card := Finset.card_le_card hsub
  rw [h5, hcard] at hle
  omega

/-- **`{0, 2}` MEETS EVERY ODD CYCLE OF `sharp2`.** -/
theorem hitsOddCycles_sharp2_pair : HitsOddCycles sharp2 {0, 2} := by
  intro C hC
  have hone : 0 ∈ C ∨ 2 ∈ C := by
    rcases card_le_six_of_isOddCycle hC with h3 | h5
    · exact zero_or_two_of_isOddCycle_card_three hC h3
    · exact zero_or_two_of_card_five h5
  rcases hone with hone | hone
  · rw [← Finset.nonempty_iff_ne_empty]
    refine ⟨0, ?_⟩
    rw [Finset.mem_inter, Finset.mem_insert]
    exact ⟨hone, Or.inl rfl⟩
  · rw [← Finset.nonempty_iff_ne_empty]
    refine ⟨2, ?_⟩
    rw [Finset.mem_inter, Finset.mem_insert]
    exact ⟨hone, Or.inr (Finset.mem_singleton.mpr rfl)⟩

/-- **`sharp2` IS `2`-CLOSE TO BIPARTITE**, with the certificate the pair `{0, 2}`. -/
theorem closeToBipartite_two_sharp2 : CloseToBipartite 2 sharp2 :=
  (closeToBipartite_iff_hitsOddCycles (G := sharp2) (m := 2)).mpr
    ⟨{0, 2}, by
      have e : ({0, 2} : Finset (Fin 6)) = insert 0 ({2} : Finset (Fin 6)) := rfl
      rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_singleton],
      hitsOddCycles_sharp2_pair⟩

/-! ### Part 2 — and no single vertex suffices: the constant `2` is optimal at `k = 1` -/

/-- **A SET OF AT MOST ONE ELEMENT IS A SINGLETON OR EMPTY.** -/
theorem card_le_one_cases {X : Finset (Fin 6)} (hX : X.card ≤ 1) :
    X = ∅ ∨ ∃ v : Fin 6, X = {v} := by
  rcases Nat.eq_zero_or_pos X.card with hz | hp
  · refine Or.inl ?_
    rw [Finset.card_eq_zero.mp hz]
  · have h1 : X.card = 1 := by omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
    exact Or.inr ⟨v, hv⟩

/-- **NO SINGLE VERTEX DELETION MAKES `sharp2` BIPARTITE**: for every vertex `v` there is a triangle
avoiding `v`. -/
theorem not_closeToBipartite_one_sharp2 : ¬ CloseToBipartite 1 sharp2 := by
  rintro ⟨X, hXcard, hbip⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin 6), IsOddCycle sharp2 T ∧ Disjoint T X := by
    rcases card_le_one_cases hXcard with hX0 | ⟨v, hXv⟩
    · exact ⟨{0, 1, 2}, isOddCycle_sharp2_012, by simp [hX0]⟩
    · rw [hXv]
      fin_cases v
      · exact ⟨{1, 2, 3}, isOddCycle_sharp2_123, by simp⟩
      · exact ⟨{0, 2, 4}, isOddCycle_sharp2_024, by simp⟩
      · exact ⟨{0, 1, 5}, isOddCycle_sharp2_015, by simp⟩
      · exact ⟨{0, 1, 2}, isOddCycle_sharp2_012, by simp⟩
      · exact ⟨{1, 2, 3}, isOddCycle_sharp2_123, by simp⟩
      · exact ⟨{0, 1, 2}, isOddCycle_sharp2_012, by simp⟩
  have hhits : HitsOddCycles sharp2 X := hitsOddCycles_of_isBipartite_delete hbip
  have hne : (T ∩ X).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    exact hhits T hT.1
  obtain ⟨w, hw⟩ := hne
  rcases Finset.mem_inter.mp hw with ⟨hwT, hwX⟩
  exact Finset.disjoint_left.mp hT.2 hwT hwX

/-- **THE OPTIMAL CONSTANT AT `k = 1` IS `2`, NOT `1`.**  `sharp2` satisfies `LocIndep 1` and is
`2`-close to bipartite but not `1`-close, so `Erdős73On 1 1` is false while
`JSP90.erdos73On_one_two_of_attachThreeResidualRefined` (with round 137's residual) would give
`Erdős73On 1 2`: the constant of the sharp case is forced to be `2`. -/
theorem optimal_constant_one_is_two :
    LocIndep 1 sharp2 ∧ CloseToBipartite 2 sharp2 ∧ ¬ CloseToBipartite 1 sharp2 :=
  ⟨locIndep_one_sharp2, closeToBipartite_two_sharp2, not_closeToBipartite_one_sharp2⟩

/-! ### Part 3 — the fan and the attachment points of the triangle `{0, 1, 2}` -/

/-- **THE FAN OF THE TRIANGLE `{0, 1, 2}` OF `sharp2` IS `{3, 4, 5}`.** -/
theorem boundary_sharp2_T : boundary sharp2 {0, 1, 2} = {3, 4, 5} := by
  ext x
  rw [mem_boundary]
  constructor
  · intro hx
    have hne : x ∉ ({0, 1, 2} : Finset (Fin 6)) := hx.1
    simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hne ⊢
    have h0 : x.val ≠ 0 := fun h => hne (Or.inl (Fin.ext h))
    have h1 : x.val ≠ 1 := fun h => hne (Or.inr (Or.inl (Fin.ext h)))
    have h2 : x.val ≠ 2 := fun h => hne (Or.inr (Or.inr (Fin.ext h)))
    have hlt := x.isLt
    rcases (show x.val = 3 ∨ x.val = 4 ∨ x.val = 5 by omega) with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · rw [h]
      exact ⟨by simp, 1, by simp, by simp [sharp2Adj]⟩
    · rw [h]
      exact ⟨by simp, 2, by simp, by simp [sharp2Adj]⟩
    · rw [h]
      exact ⟨by simp, 0, by simp, by simp [sharp2Adj]⟩

/-- **THE FAN OF THE TRIANGLE `{0, 1, 2}` HAS THREE ELEMENTS.** -/
theorem card_boundary_sharp2 : (boundary sharp2 {0, 1, 2}).card = 3 := by
  rw [boundary_sharp2_T]
  have e : ({3, 4, 5} : Finset (Fin 6)) = insert 3 (insert 4 (insert 5 ∅)) := rfl
  rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp)]
  simp

/-- **THE ATTACHMENT POINTS OF THE TRIANGLE `{0, 1, 2}` ARE ITS THREE VERTICES**: each of `0`, `1`,
`2` has a fan vertex as a neighbour (`0-4`, `1-3`, `2-3`), and the fan is disjoint from the
triangle. -/
theorem mem_attachPoints_sharp2_T {x : Fin 6} :
    x ∈ attachPoints sharp2 {0, 1, 2} ↔ x ∈ ({0, 1, 2} : Finset (Fin 6)) := by
  rw [mem_attachPoints]
  rw [boundary_sharp2_T]
  constructor
  · rintro ⟨hC, y, hy, hay⟩
    fin_cases y <;> fin_cases x <;> simp [sharp2Adj] at hay <;> simp_all
  · intro hx
    fin_cases x
    · exact ⟨by simp, 4, by simp, by simp [sharp2Adj]⟩
    · exact ⟨by simp, 5, by simp, by simp [sharp2Adj]⟩
    · exact ⟨by simp, 3, by simp, by simp [sharp2Adj]⟩
    all_goals exact absurd hx (by simp)

/-- **THE ATTACHMENT POINTS OF THE TRIANGLE `{0, 1, 2}` ARE `{0, 1, 2}`, OF SIZE `3`**: the first
six-vertex instance of `JSP90.AttachThreeResidualRefined` (`3 ≤ |attachPoints G C|`), with the
certificate `{0, 2}` lying in them. -/
theorem attachPoints_sharp2_T : attachPoints sharp2 {0, 1, 2} = {0, 1, 2} := by
  ext x
  exact mem_attachPoints_sharp2_T

theorem card_attachPoints_sharp2 : (attachPoints sharp2 {0, 1, 2}).card = 3 := by
  rw [attachPoints_sharp2_T]
  have e : ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 (insert 2 ∅)) := rfl
  rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp)]
  simp

/-- **THE TRIANGLE `{0, 1, 2}` IS A SHORTEST ODD CYCLE OF `sharp2`** (its length `3` is the odd
girth). -/
theorem short_of_isOddCycle_sharp2_012 {D : Finset (Fin 6)} (hD : IsOddCycle sharp2 D) :
    ({0, 1, 2} : Finset (Fin 6)).card ≤ D.card := by
  have h3 : ({0, 1, 2} : Finset (Fin 6)).card = 3 := by
    have e : ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 (insert 2 ∅)) := rfl
    rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
      Finset.card_insert_of_notMem (by simp)]
    simp
  rcases card_le_six_of_isOddCycle hD with hd | hd <;> omega

#print axioms JSP90.locIndep_one_sharp2
#print axioms JSP90.isOddCycle_tri_of_adj
#print axioms JSP90.isOddCycle_sharp2_012
#print axioms JSP90.isOddCycle_sharp2_024
#print axioms JSP90.isOddCycle_sharp2_123
#print axioms JSP90.isOddCycle_sharp2_015
#print axioms JSP90.card_le_six_of_isOddCycle
#print axioms JSP90.zero_or_two_of_isOddCycle_card_three
#print axioms JSP90.zero_or_two_of_card_five
#print axioms JSP90.hitsOddCycles_sharp2_pair
#print axioms JSP90.closeToBipartite_two_sharp2
#print axioms JSP90.card_le_one_cases
#print axioms JSP90.not_closeToBipartite_one_sharp2
#print axioms JSP90.optimal_constant_one_is_two
#print axioms JSP90.boundary_sharp2_T
#print axioms JSP90.card_boundary_sharp2
#print axioms JSP90.mem_attachPoints_sharp2_T
#print axioms JSP90.attachPoints_sharp2_T
#print axioms JSP90.card_attachPoints_sharp2
#print axioms JSP90.short_of_isOddCycle_sharp2_012

end SharpTwo

end

end JSP90
