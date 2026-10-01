/-
# JSP-000090 — the negative result of round 89: the cleanliness of a 2-cut is NOT automatic

`JSPProblem/HalfOne.lean` (round 89) proves the **refined cut step** and derives from it the
packing-counted cut lemma with the optimal `+1`:

```
(JSP90.VertexSplit.closeToBipartite_one_avoid_of_clean)
  every packing of odd cycles of G has at most r members
  + every bipartite part T_i has a bipartite half-piece T_i ∪ {b}      (the cut is "clean")
  + CloseToBipartite m on the half-pieces of the non-bipartite parts
  ⟹ CloseToBipartite (1 + m * r) G
```

The cleanliness hypothesis is what makes the counting work: `JSPProblem/Count.lean`'s
`VertexSplit.card_nonBipartiteParts_le_pack` bounds the number of **non-bipartite parts** by the
packing number, and a bipartite part costs nothing only if its half-piece `T_i ∪ {b}` is bipartite
too.  This file records, **by machine-checked counterexample**, that the hypothesis cannot be
dropped:

> **`JSP90.windmill_counting_fails`**  the *windmill* `wf` — the graph on `Fin 6` consisting of two
> triangles `0 - 1 - 2 - 0` and `0 - 3 - 4 - 0` sharing the single vertex `0`, together with the
> isolated vertex `5` — satisfies `LocIndep 1 wf` (so **every** packing of odd cycles of `wf` has at
> most **one** member), yet **both** of its half-pieces at the 2-cut `a = 5`, `b = 0` are triangles,
> hence non-bipartite (`JSP90.windmill_split_not_clean`).

So "the number of non-bipartite half-pieces is bounded by the packing number" is **false**: the
number of non-bipartite half-pieces can exceed `r` by an arbitrary amount, because two triangles
through the *same* vertex of the cut are not vertex-disjoint.  A future round must not re-attempt the
counting lemma for half-pieces without an extra hypothesis; the exact statement needed is recorded in
`discovery/JSP-000090/policy.json`.

This is a genuine obstruction, not an artefact of the formalisation: `wf` really is a `LocIndep 1`
graph whose two 2-cut half-pieces are both odd cycles.  It is *not* an obstruction to Erdős #73 — the
windmill is itself one vertex away from bipartite (`JSP90.windmill_closeToBipartite_one`) — so what
the counterexample blocks is exactly the *counting argument of the cut step*, and it says that the
counting must be done on the **parts** (as `JSPProblem/Count.lean` does), with the half-piece
hypothesis of round 89 kept as a separate assumption.

Everything here is proved: `LocIndep 1 wf` is the exhaustive kernel decision over all `2 ^ 6` vertex
sets (`JSP90.locIndep_one_wf`), the two half-pieces are exhibited as explicit 3-cycles
(`JSP90.not_isBipartite_half_wfs`), and the 2-cut `wfs` is a genuine `VertexSplit`.
-/

import JSPProblem.HalfOne
import JSPProblem.OffCycle

namespace JSP90

open Finset Fintype Set

noncomputable section

/-- **One computable `DecidableEq (Fin n)` for the whole file** (the trick of
`JSPProblem/Petersen.lean`), so that every finite statement below is decided by the kernel.
The `hdisj` field of `VertexSplit` mentions `Finset.inter` under the *classical* instance of
`JSPProblem/Separator.lean`; that field is therefore proved through plain `simp`, which matches up
to instances, rather than through a lemma stated under one particular `DecidableEq`. -/
local instance instDecidableEqFinWf (n : ℕ) : DecidableEq (Fin n) := instDecidableEqFin n

/-! ### The windmill graph

`wf` is the graph of two triangles sharing a single vertex, together with one isolated vertex:

```
        1                      3
       / \                    / \
      2 ——— 0 ————————— 4 ———— 0 (shared)          5   (isolated)
```

The numbering is `0, 1, 2` for the first triangle and `0, 3, 4` for the second, on `Fin 6`.  The
adjacency is given by a formula on `Fin.val`, so that every finite statement about `wf` below is a
kernel computation. -/

/-- **Adjacency in the windmill**: `v` and `w` are adjacent when `0` is one of them and the other
lies in `{1, 2, 3, 4}`, or when they are `1, 2`, or when they are `3, 4`. -/
def wfAdj (v w : Fin 6) : Prop :=
  v.val ≠ w.val ∧
    ((v.val = 0 ∧ (w.val = 1 ∨ w.val = 2 ∨ w.val = 3 ∨ w.val = 4)) ∨
      (w.val = 0 ∧ (v.val = 1 ∨ v.val = 2 ∨ v.val = 3 ∨ v.val = 4)) ∨
      (v.val = 1 ∧ w.val = 2) ∨ (w.val = 1 ∧ v.val = 2) ∨
      (v.val = 3 ∧ w.val = 4) ∨ (w.val = 3 ∧ v.val = 4))

/-- **`wfAdj` is decidable**: it is a formula about `Nat`s. -/
instance instDecidableRelWfAdj (v w : Fin 6) : Decidable (wfAdj v w) := by
  unfold wfAdj
  infer_instance

/-- **The windmill graph**: two triangles sharing the vertex `0`, and the isolated vertex `5`. -/
def wf : SimpleGraph (Fin 6) where
  Adj := wfAdj
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

@[simp] theorem wf_adj {v w : Fin 6} : wf.Adj v w ↔ wfAdj v w := by
  unfold SimpleGraph.Adj wf
  rfl

/-- Adjacency of `wf` is decidable. -/
local instance : DecidableRel wf.Adj := fun v w => inferInstanceAs (Decidable (wfAdj v w))

/-- **The two triangle orderings as explicit maps `Fin 3 → Fin 6`**, so that every statement about
them is a computation. -/
def tri012 : Fin 3 → Fin 6 := Fin.cases 0 (Fin.cases 1 (Fin.cases 2 Fin.elim0))

def tri034 : Fin 3 → Fin 6 := Fin.cases 0 (Fin.cases 3 (Fin.cases 4 Fin.elim0))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- **`LocIndep 1 wf`**: every vertex set of the windmill carries an independent set of size
`≥ (|X| - 1) / 2`, by exhaustive decision over the `2 ^ 6` vertex sets.  Erdős's local hypothesis
holds for the windmill with `k = 1`. -/
theorem locIndep_one_wf : LocIndep 1 wf := by
  unfold LocIndep
  decide

/-! ### The 2-cut of the windmill -/

/-- The parts of the windmill split: the two triangles minus their common vertex. -/
def wfPart : Fin 2 → Finset (Fin 6) := fun i =>
  if i.val = 0 then ({1, 2} : Finset (Fin 6)) else ({3, 4} : Finset (Fin 6))

theorem wfPart_0 : wfPart 0 = ({1, 2} : Finset (Fin 6)) := by simp [wfPart]

theorem wfPart_1 : wfPart 1 = ({3, 4} : Finset (Fin 6)) := by simp [wfPart]

/-- **`{1, 2} ∩ {3, 4} = ∅`**: the two triangles minus their common vertex do not meet. -/
theorem inter_12_34 : ({1, 2} : Finset (Fin 6)) ∩ {3, 4} = ∅ := by
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨z, hz⟩
  have h1 := (Finset.mem_inter.mp hz).1
  have h2 := (Finset.mem_inter.mp hz).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> simp_all

/-- ... and in the other order, for the reversed pair of parts. -/
theorem inter_34_12 : ({3, 4} : Finset (Fin 6)) ∩ {1, 2} = ∅ := by
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨z, hz⟩
  have h1 := (Finset.mem_inter.mp hz).1
  have h2 := (Finset.mem_inter.mp hz).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> simp_all

/-- **THE 2-CUT OF THE WINDMILL AT `a = 5`, `b = 0`.**  The two parts are the two triangles minus
their common vertex, `{1, 2}` and `{3, 4}`; they are pairwise anticomplete and `5` is isolated, so the
cut is proper.  Removing `{5, 0}` leaves exactly two components: this is a genuine 2-cut. -/
def wfs : VertexSplit wf 5 0 2 where
  parts := wfPart
  hne := by
    intro i
    rcases Nat.lt_or_ge i.val 1 with hi | hi
    · rw [show i = 0 from (Fin.ext (by omega)), wfPart_0]
      exact ⟨1, by decide⟩
    · rw [show i = 1 from (Fin.ext (by omega)), wfPart_1]
      exact ⟨3, by decide⟩
  hdisj := by
    intro i j hij
    rcases Nat.lt_or_ge i.val 1 with hi | hi
    · have i0 : i = 0 := Fin.ext (by omega)
      rcases Nat.lt_or_ge j.val 1 with hj | hj
      · have j0 : j = 0 := Fin.ext (by omega)
        exact absurd (Fin.ext (by omega)) hij
      · have j1 : j = 1 := Fin.ext (by omega)
        rw [i0, wfPart_0, j1, wfPart_1]
        ext z
        simp [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] <;> omega
    · have i1 : i = 1 := Fin.ext (by omega)
      rcases Nat.lt_or_ge j.val 1 with hj | hj
      · have j0 : j = 0 := Fin.ext (by omega)
        rw [i1, wfPart_1, j0, wfPart_0]
        ext z
        simp [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] <;> omega
      · have j1 : j = 1 := Fin.ext (by omega)
        exact absurd (Fin.ext (by omega)) hij
  hcov := by
    intro x
    fin_cases x <;> simp [wfPart]
  hanti := by
    intro i j hij x hx y hy
    rcases Nat.lt_or_ge i.val 1 with hi | hi
    · have i0 : i = 0 := Fin.ext (by omega)
      rcases Nat.lt_or_ge j.val 1 with hj | hj
      · have j0 : j = 0 := Fin.ext (by omega)
        exact absurd (Fin.ext (by omega)) hij
      · have j1 : j = 1 := Fin.ext (by omega)
        rw [i0, wfPart_0] at hx
        rw [j1, wfPart_1] at hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with hx | hx | hx <;> rcases hy with hy | hy <;> simp_all [wfAdj]
    · have i1 : i = 1 := Fin.ext (by omega)
      rcases Nat.lt_or_ge j.val 1 with hj | hj
      · have j0 : j = 0 := Fin.ext (by omega)
        rw [i1, wfPart_1] at hx
        rw [j0, wfPart_0] at hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with hx | hx | hx <;> rcases hy with hy | hy <;> simp_all [wfAdj]
      · have j1 : j = 1 := Fin.ext (by omega)
        exact absurd (Fin.ext (by omega)) hij
  hnadj := by simp [wfAdj]

/-- **Every packing of odd cycles of the windmill has at most one member.**  This is the *packing
number* side of the negative result: the windmill satisfies Erdős's local hypothesis with `k = 1`,
so by `LocIndep.oddCycleFamily_card_le` its packing number is at most `1`. -/
theorem packing_wf :
    ∀ C : Finset (Finset (Fin 6)), IsOddCycleFamily (G := wf) C → C.card ≤ 1 :=
  fun _C hC => (locIndep_one_wf).oddCycleFamily_card_le hC

/-! ### The two triangles are odd cycles -/

/-- **`tri012` takes its values in `{0, 1, 2}`** -/
theorem tri012_mem (j : Fin 3) : tri012 j ∈ ({0, 1, 2} : Finset (Fin 6)) := by
  fin_cases j <;> decide

/-- **`tri034` takes its values in `{0, 3, 4}`** -/
theorem tri034_mem (j : Fin 3) : tri034 j ∈ ({0, 3, 4} : Finset (Fin 6)) := by
  fin_cases j <;> decide

/-- **The cyclic ordering `tri012` walks the triangle `0 - 1 - 2 - 0` of the windmill.** -/
theorem tri012_cyc : ∀ j : Fin 3, wf.Adj (tri012 j) (tri012 (cycSucc j)) := by
  decide

/-- **The cyclic ordering `tri034` walks the triangle `0 - 3 - 4 - 0` of the windmill.** -/
theorem tri034_cyc : ∀ j : Fin 3, wf.Adj (tri034 j) (tri034 (cycSucc j)) := by
  decide

/-- **... and `tri012` walks that triangle inside the induced graph on `{0, 1, 2}`**, the half-piece
`T_1 ∪ {0}` of the windmill split. -/
theorem tri012_cyc' :
    ∀ j : Fin 3,
      (induceFinset wf ({0, 1, 2} : Finset (Fin 6))).Adj (tri012 j) (tri012 (cycSucc j)) := by
  intro j
  rw [induce_adj]
  exact ⟨tri012_mem j, tri012_mem (cycSucc j), tri012_cyc j⟩

/-- **... and `tri034` walks that triangle inside the induced graph on `{0, 3, 4}`**, the half-piece
`T_2 ∪ {0}` of the windmill split. -/
theorem tri034_cyc' :
    ∀ j : Fin 3,
      (induceFinset wf ({0, 3, 4} : Finset (Fin 6))).Adj (tri034 j) (tri034 (cycSucc j)) := by
  intro j
  rw [induce_adj]
  exact ⟨tri034_mem j, tri034_mem (cycSucc j), tri034_cyc j⟩

/-- **`tri012` is injective** -/
theorem tri012_inj : Function.Injective tri012 := by
  decide

/-- **`tri034` is injective** -/
theorem tri034_inj : Function.Injective tri034 := by
  decide


/-- **The triangle `0 - 1 - 2 - 0` is an odd cycle of `wf`.** -/
theorem exists_isOddCycle_wf : ∃ C : Finset (Fin 6), IsOddCycle wf C := by
  exact ⟨_, isOddCycle_image (H := wf) (m := 3) tri012 (by decide) (by decide) tri012_inj
    tri012_cyc⟩

/-- **The half-piece `T_1 ∪ {0}` of the windmill split carries the triangle `0 - 1 - 2 - 0`.** -/
theorem exists_isOddCycle_half_1 :
    ∃ C : Finset (Fin 6), IsOddCycle (induceFinset wf ({0, 1, 2} : Finset (Fin 6))) C := by
  exact ⟨_, isOddCycle_image (H := induceFinset wf ({0, 1, 2} : Finset (Fin 6))) (m := 3)
    tri012 (by decide) (by decide) tri012_inj tri012_cyc'⟩

/-- **The half-piece `T_2 ∪ {0}` of the windmill split carries the triangle `0 - 3 - 4 - 0`.** -/
theorem exists_isOddCycle_half_2 :
    ∃ C : Finset (Fin 6), IsOddCycle (induceFinset wf ({0, 3, 4} : Finset (Fin 6))) C := by
  exact ⟨_, isOddCycle_image (H := induceFinset wf ({0, 3, 4} : Finset (Fin 6))) (m := 3)
    tri034 (by decide) (by decide) tri034_inj tri034_cyc'⟩

/-- **The half-piece `T_1 ∪ {0}` of the windmill split is `{0, 1, 2}`.** -/
theorem half_1_eq : (insert 0 (wfPart 0) : Finset (Fin 6)) = {0, 1, 2} := by
  ext z
  simp [wfPart_0, Finset.mem_insert, Finset.mem_singleton]

/-- **The half-piece `T_2 ∪ {0}` of the windmill split is `{0, 3, 4}`.** -/
theorem half_2_eq : (insert 0 (wfPart 1) : Finset (Fin 6)) = {0, 3, 4} := by
  ext z
  simp [wfPart_1, Finset.mem_insert, Finset.mem_singleton]

/-- **The part `{1, 2}` of the windmill split is bipartite.** -/
theorem piece_1_bipartite : (induceFinset wf ({1, 2} : Finset (Fin 6))).IsBipartite := by
  refine ⟨fun v => ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩, ?_⟩
  intro v w hadj
  simp only [induce_adj] at hadj
  rcases hadj with ⟨h1, h2, hadj⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all [wfAdj]

/-- **The part `{3, 4}` of the windmill split is bipartite.** -/
theorem piece_2_bipartite : (induceFinset wf ({3, 4} : Finset (Fin 6))).IsBipartite := by
  refine ⟨fun v => ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩, ?_⟩
  intro v w hadj
  simp only [induce_adj] at hadj
  rcases hadj with ⟨h1, h2, hadj⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all [wfAdj]

/-- **Both parts of the windmill split are bipartite.** -/
theorem wfs_parts_bipartite : ∀ i : Fin 2, (induceFinset wf (wfs.parts i)).IsBipartite := by
  intro i
  change (induceFinset wf (wfPart i)).IsBipartite
  rcases Nat.lt_or_ge i.val 1 with hi | hi
  · rw [show i = 0 from (Fin.ext (by omega)), wfPart_0]
    exact piece_1_bipartite
  · rw [show i = 1 from (Fin.ext (by omega)), wfPart_1]
    exact piece_2_bipartite

/-- **THE MACHINE-CHECKED OBSTACLE: each half-piece `T_i ∪ {0}` of the windmill split is a triangle,
hence NOT bipartite.**  This is why the hypothesis of
`JSP90.VertexSplit.closeToBipartite_one_avoid_of_clean` cannot be dropped: a *bipartite* part may
well become non-bipartite when the cut vertex is added back to it. -/
theorem not_isBipartite_half_wfs :
    ∀ i : Fin 2, ¬ (induceFinset wf (insert 0 (wfs.parts i))).IsBipartite := by
  intro i
  rcases Nat.lt_or_ge i.val 1 with hi | hi
  · have i0 : i = 0 := Fin.ext (by omega)
    rw [i0]
    change ¬ (induceFinset wf (insert 0 (wfPart 0))).IsBipartite
    rw [half_1_eq, isBipartite_iff_no_oddCycle]
    exact fun h => h exists_isOddCycle_half_1
  · have i1 : i = 1 := Fin.ext (by omega)
    rw [i1]
    change ¬ (induceFinset wf (insert 0 (wfPart 1))).IsBipartite
    rw [half_2_eq, isBipartite_iff_no_oddCycle]
    exact fun h => h exists_isOddCycle_half_2

/-! ### The negative result of round 89 -/

/-- **`CloseToBipartite 1 wf`**: deleting the shared vertex `0` leaves two isolated edges, a bipartite
graph.  So the windmill is *not* an obstruction to Erdős #73 — it only blocks the counting argument
of the cut step. -/
theorem windmill_closeToBipartite_one : CloseToBipartite 1 wf := by
  refine ⟨({0} : Finset (Fin 6)), by decide, ?_⟩
  refine ⟨fun v => ⟨(v.val + 1) % 2, Nat.mod_lt _ (by decide)⟩, ?_⟩
  intro u v hadj
  rw [deleteFinset_adj] at hadj
  rcases hadj with ⟨h1, h2, hadj⟩
  simp only [Finset.mem_singleton] at h1 h2
  fin_cases u <;> fin_cases v <;> simp_all [wfAdj]

/-- **`¬ CloseToBipartite 0 wf`**: the windmill carries an odd cycle. -/
theorem windmill_not_closeToBipartite_zero : ¬ CloseToBipartite 0 wf := by
  rintro ⟨X, hX, hb⟩
  have hX' : X = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hX)
  rw [hX', deleteFinset_empty] at hb
  exact not_isOddCycle_of_isBipartite hb exists_isOddCycle_wf

/-- **THE WINDMILL SPLIT IS NOT CLEAN.**  Its parts are bipartite (`wfs_parts_bipartite`) but its
half-pieces are not (`not_isBipartite_half_wfs`), so the hypothesis of
`JSP90.VertexSplit.closeToBipartite_one_avoid_of_clean` genuinely fails on a graph satisfying
`LocIndep 1` whose packing number is one. -/
theorem windmill_split_not_clean :
    (∀ i : Fin 2, (induceFinset wf (wfs.parts i)).IsBipartite) ∧
      ¬ (∀ i : Fin 2, (induceFinset wf (wfs.parts i)).IsBipartite →
        (induceFinset wf (insert 0 (wfs.parts i))).IsBipartite) :=
  ⟨wfs_parts_bipartite, fun h => (not_isBipartite_half_wfs 0) (h 0 (wfs_parts_bipartite 0))⟩

/-- **THE NEGATIVE RESULT OF ROUND 89.**  The windmill `wf` has **two** non-bipartite half-pieces but
its packing number is at most **one**, so the counting lemma "`card (nonBipartiteHalfParts) ≤ r`" —
the one that would have made the refined cut step of `JSPProblem/HalfOne.lean` unconditionally
packing-counted, without the `hclean` hypothesis — is **FALSE**.

Concretely: `LocIndep 1 wf` holds, so every packing of odd cycles of `wf` has at most one member,
while both half-pieces `T_1 ∪ {0}` and `T_2 ∪ {0}` of the windmill split are triangles.  Hence the
cleanliness hypothesis of `JSP90.VertexSplit.closeToBipartite_one_avoid_of_clean` is genuinely
needed, and the counting of the cut step must be done on the **parts**
(`JSPProblem.VertexSplit.card_nonBipartiteParts_le_pack`), not on the half-pieces. -/
theorem windmill_counting_fails :
    LocIndep 1 wf ∧
      (∀ C : Finset (Finset (Fin 6)), IsOddCycleFamily (G := wf) C → C.card ≤ 1) ∧
      (∀ i : Fin 2, ¬ (induceFinset wf (insert 0 (wfs.parts i))).IsBipartite) ∧
      ¬ CloseToBipartite 0 wf ∧ CloseToBipartite 1 wf :=
  ⟨locIndep_one_wf, packing_wf, not_isBipartite_half_wfs, windmill_not_closeToBipartite_zero,
    windmill_closeToBipartite_one⟩

end

end JSP90
