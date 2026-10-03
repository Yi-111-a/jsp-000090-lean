/-
# JSP-000090, round 135 — `JSPProblem/Fan4.lean`: **the fan of a shortest odd cycle is unbounded at
# `k = 1`**, machine-checked on six vertices

Attack family 64, Part 4.  `JSPProblem/BoundaryOne.lean` proves that at `LocIndep 1` the *only*
object the constant of Erdős #73 has to pay for is the **fan** `boundary G C` of a shortest odd
cycle `C`, and that a fan of size `≤ 1` gives the sharp constant `2`.  The obvious remaining hope
would then be:

> ~~at `LocIndep 1` some odd cycle always has a fan of at most `m` vertices~~

**THIS IS FALSE for every `m ≥ 2`, and the smallest witness has six vertices:**

```
fan4  (on Fin 6)   edges  0-4  0-5  1-5  2-5  3-5  4-5
```

i.e. the triangle `{0, 4, 5}` with three pendant vertices at `5`.  Proved here:

* **`JSP90.locIndep_one_fan4`** — `fan4` satisfies Erdős's hypothesis with `k = 1` (an exhaustive
  kernel decision over the `2 ^ 6` vertex sets), so it is a genuine member of the class of
  JSP-000090;
* **`JSP90.mem_isOddCycle_fan4`** — **`{0, 4, 5}` is the *only* odd cycle of `fan4`**: a vertex of an
  odd cycle has at least two neighbours (`JSP90.two_le_card_neigh_of_mem_oddCycle`), while `1`, `2`
  and `3` are pendant, and an odd cycle has at least three vertices;
* **`JSP90.card_boundary_fan4`** — the fan of that cycle is `{1, 2, 3}`, of size `3`;
* **`JSP90.not_exists_boundary_le_two_fan4`** — **no odd cycle of `fan4` has a fan of at most two
  vertices**: the machine-checked refutation of the "small fan" route, and with it of every
  statement "`LocIndep 1` supplies an odd cycle whose fan has at most `m` elements" for `m ≥ 2`.
  No route through such a statement may be attempted again;
* **`JSP90.closeToBipartite_one_fan4`** — and yet `fan4` is `1`-close to bipartite (the certificate
  is the single vertex `5`), so the big fan is **not** a counterexample: it is exactly the case in
  which one vertex of the triangle does all the work.  The residual
  `JSP90.FanTwoResidual` of `JSPProblem/BoundaryOne.lean` concerns the fan of a shortest odd cycle
  of size `≥ 2` and is *not* refuted here.

Every statement exported by this file is instance-free, so it may be consumed from the classical
scope of the other files (the trick of `JSPProblem/Nonagon.lean`).
-/

import JSPProblem.BoundaryOne

namespace JSP90

open Finset Fintype

noncomputable section

/-- **One computable `DecidableEq (Fin n)` for the whole file** (the trick of
`JSPProblem/Nonagon.lean`), so that every finite statement below is a kernel computation. -/
local instance instDecidableEqFinFan4 (n : ℕ) : DecidableEq (Fin n) := instDecidableEqFin n

/-! ### The six-vertex witness `fan4` -/

section Fan4

/-- **Adjacency in `fan4`**: the six edges

```
0-4  0-5  1-5  2-5  3-5  4-5
```

as a formula on `Fin.val`: the triangle `{0, 4, 5}` together with three pendant vertices `1`, `2`,
`3` at the vertex `5`. -/
def fan4Adj (v w : Fin 6) : Prop :=
  v.val ≠ w.val ∧
    ((v.val = 0 ∧ (w.val = 4 ∨ w.val = 5)) ∨ (w.val = 0 ∧ (v.val = 4 ∨ v.val = 5)) ∨
      (v.val = 4 ∧ w.val = 5) ∨ (w.val = 4 ∧ v.val = 5) ∨
      (v.val ≤ 3 ∧ w.val = 5) ∨ (w.val ≤ 3 ∧ v.val = 5))

/-- **`fan4Adj` is decidable**: it is a formula about `Nat`s. -/
instance instDecidableRelFan4Adj (v w : Fin 6) : Decidable (fan4Adj v w) := by
  unfold fan4Adj
  infer_instance

/-- **The six-vertex witness.** -/
def fan4 : SimpleGraph (Fin 6) where
  Adj := fan4Adj
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

@[simp] theorem fan4_adj {v w : Fin 6} : fan4.Adj v w ↔ fan4Adj v w := by
  unfold SimpleGraph.Adj fan4
  rfl

/-- Adjacency of `fan4` is decidable. -/
local instance : DecidableRel fan4.Adj := fun v w => inferInstanceAs (Decidable (fan4Adj v w))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- **`LocIndep 1 fan4`**: every vertex set of `fan4` carries an independent set of size
`≥ (|X| - 1) / 2`, by exhaustive decision over the `2 ^ 6` vertex sets. -/
theorem locIndep_one_fan4 : LocIndep 1 fan4 := by
  unfold LocIndep
  decide

/-- **The neighbourhood of each pendant vertex**: the three pendant vertices `1`, `2`, `3` of
`fan4` have the vertex `5` as their only neighbour. -/
theorem neigh_fan4_one : Neigh fan4 1 = {5} := by
  ext w
  simp [Neigh, fan4_adj, fan4Adj]
  constructor
  · intro h
    exact Fin.ext h.2
  · intro h
    subst h
    exact ⟨by decide, rfl⟩

theorem neigh_fan4_two : Neigh fan4 2 = {5} := by
  ext w
  simp [Neigh, fan4_adj, fan4Adj]
  constructor
  · intro h
    exact Fin.ext h.2
  · intro h
    subst h
    exact ⟨by decide, rfl⟩

theorem neigh_fan4_three : Neigh fan4 3 = {5} := by
  ext w
  simp [Neigh, fan4_adj, fan4Adj]
  constructor
  · intro h
    exact Fin.ext h.2
  · intro h
    subst h
    exact ⟨by decide, rfl⟩

/-- **A PENDANT VERTEX OF `fan4` LIES ON NO ODD CYCLE.**  A vertex of an odd cycle has at least two
neighbours (`JSP90.two_le_card_neigh_of_mem_oddCycle`, `JSPProblem/Sparse.lean`), and `1`, `2`, `3`
have exactly one. -/
theorem not_mem_oddCycle_of_fan4_pendant {C : Finset (Fin 6)} (hC : IsOddCycle fan4 C)
    {v : Fin 6} (hv : v.val = 1 ∨ v.val = 2 ∨ v.val = 3) : v ∉ C := by
  intro hmem
  have h2 := two_le_card_neigh_of_mem_oddCycle hC hmem
  rcases hv with hv | hv | hv
  · have hv' : v = 1 := Fin.ext hv
    rw [hv', neigh_fan4_one] at h2
    simp at h2
  · have hv' : v = 2 := Fin.ext hv
    rw [hv', neigh_fan4_two] at h2
    simp at h2
  · have hv' : v = 3 := Fin.ext hv
    rw [hv', neigh_fan4_three] at h2
    simp at h2

/-- **THE CARDINALITY OF THE UNIQUE ODD CYCLE OF `fan4`.** -/
theorem card_fan4T : ({0, 4, 5} : Finset (Fin 6)).card = 3 := by
  have e : ({0, 4, 5} : Finset (Fin 6)) = insert 0 (insert 4 (insert 5 ∅)) := rfl
  rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp)]
  simp

/-- **THE ONLY ODD CYCLE OF `fan4` IS THE TRIANGLE `{0, 4, 5}`.** -/
theorem mem_isOddCycle_fan4 {C : Finset (Fin 6)} (hC : IsOddCycle fan4 C) : C = {0, 4, 5} := by
  have hsub : C ⊆ ({0, 4, 5} : Finset (Fin 6)) := by
    intro x hx
    have hne : x.val ≠ 1 ∧ x.val ≠ 2 ∧ x.val ≠ 3 := by
      exact ⟨fun h => not_mem_oddCycle_of_fan4_pendant hC (Or.inl h) hx,
        fun h => not_mem_oddCycle_of_fan4_pendant hC (Or.inr (Or.inl h)) hx,
        fun h => not_mem_oddCycle_of_fan4_pendant hC (Or.inr (Or.inr h)) hx⟩
    fin_cases x <;> simp_all
  have h3 := three_le_card_of_isOddCycle hC
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [card_fan4T]
  omega

/-- **The cyclic numbering of the triangle `{0, 4, 5}` of `fan4`**: the `if`-form, so that
`fin_cases` and `simp [cycSucc]` do the work. -/
def fan4TCyc : Fin 3 → Fin 6 :=
  fun i => if i.val = 0 then 0 else if i.val = 1 then 4 else 5

/-- **THE TRIANGLE `{0, 4, 5}` IS AN ODD CYCLE OF `fan4`.** -/
theorem isOddCycle_fan4_T : IsOddCycle fan4 {0, 4, 5} := by
  refine ⟨3, fan4TCyc, by decide, by decide, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [fan4TCyc]
  · intro j
    fin_cases j <;> simp [fan4TCyc, cycSucc, fan4_adj, fan4Adj]
  · intro x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨⟨0, by decide⟩, by simp [fan4TCyc]⟩
      · exact ⟨⟨1, by decide⟩, by simp [fan4TCyc]⟩
      · exact ⟨⟨2, by decide⟩, by simp [fan4TCyc]⟩
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [fan4TCyc]

/-! ### The fan of the unique odd cycle has size three -/

/-- **THE FAN OF THE UNIQUE ODD CYCLE OF `fan4` IS `{1, 2, 3}`.** -/
theorem boundary_fan4_T : boundary fan4 {0, 4, 5} = {1, 2, 3} := by
  ext x
  simp only [boundary, neighOf, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    rcases hx with ⟨hne, hnot⟩
    obtain ⟨w, hw, hadj⟩ := hne
    fin_cases x <;> simp_all
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨⟨5, by simp, by decide⟩, by simp⟩
    · exact ⟨⟨5, by simp, by decide⟩, by simp⟩
    · exact ⟨⟨5, by simp, by decide⟩, by simp⟩

/-- **THE FAN OF THE UNIQUE ODD CYCLE OF `fan4` HAS THREE ELEMENTS.** -/
theorem card_boundary_fan4 : (boundary fan4 {0, 4, 5}).card = 3 := by
  rw [boundary_fan4_T]
  have e : ({1, 2, 3} : Finset (Fin 6)) = insert 1 (insert 2 (insert 3 ∅)) := rfl
  rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp)]
  simp


/-- **NO ODD CYCLE OF `fan4` HAS A FAN OF AT MOST TWO VERTICES: THE "SMALL FAN" ROUTE IS DEAD.**

In words: `LocIndep 1` does **not** supply an odd cycle whose fan is small; the fan of the unique
odd cycle of `fan4` has three elements, and `fan4` satisfies `LocIndep 1`
(`JSP90.locIndep_one_fan4`).  Consequently no statement of the form "`LocIndep 1` supplies an odd
cycle with a fan of at most `m` elements" is available for any `m ≥ 2`. -/
theorem not_exists_boundary_le_two_fan4 :
    ¬ (∃ C : Finset (Fin 6), IsOddCycle fan4 C ∧ (boundary fan4 C).card ≤ 2) := by
  rintro ⟨C, hC, hb⟩
  rw [mem_isOddCycle_fan4 hC] at hb
  rw [card_boundary_fan4] at hb
  omega

/-- **THE FAN OF THE UNIQUE ODD CYCLE OF `fan4` HAS AT LEAST TWO ELEMENTS** (the instance of
`JSP90.FanTwoResidual` that this witness triggers, with the conclusion being *true*). -/
theorem two_le_card_boundary_fan4 : 2 ≤ (boundary fan4 {0, 4, 5}).card := by
  rw [card_boundary_fan4]
  omega

/-- **`fan4` IS `1`-CLOSE TO BIPARTITE**: the single vertex `5` meets its only odd cycle.  So the big
fan of `fan4` is not a counterexample to Erdős #73 at `k = 1`. -/
theorem closeToBipartite_one_fan4 : CloseToBipartite 1 fan4 := by
  refine (closeToBipartite_iff_hitsOddCycles (G := fan4) (m := 1)).mpr ⟨{5}, by simp, ?_⟩
  intro C hC
  have hC' : C = ({0, 4, 5} : Finset (Fin 6)) := mem_isOddCycle_fan4 hC
  rw [hC']
  refine Finset.nonempty_iff_ne_empty.mp ⟨5, ?_⟩
  simp

/-- **AND THE CONCLUSION OF ERDŐS #73 AT `k = 1` HOLDS FOR `fan4` WITH THE OPTIMAL CONSTANT `1`.** -/
theorem erdos73On_one_fan4 : CloseToBipartite 1 fan4 := closeToBipartite_one_fan4

end Fan4

end

end JSP90