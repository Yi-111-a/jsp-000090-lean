/-
# JSP-000090 — `JSPProblem/PetalFinite.lean`: the finite witnesses for the attachment-set axis

This file is the *computational* half of `JSPProblem/PetalBound.lean`; it exists because the
statements below must be elaborated with a **computable** `DecidableEq (Fin n)` (so that `decide` can
run in the kernel), while every statement of `JSPProblem/PetalBound.lean` must be elaborated with
the **classical** instance of `JSPProblem/Transversal.lean`, which is the one baked into
`JSP90.IsOddCycle` and `JSP90.PetalSet`.  Splitting the two scopes across two files is the only way
to keep both (`policy.json`, round 120: a `local instance` is *not* scoped to its `section`, and a
later re-declaration does **not** shadow a more specific one).

Every declaration exported here has an **instance-free statement**, so it can be used in the
classical scope of `PetalBound.lean`:

* **`g7`** on `Fin 7`: `K_4` on `{0, 1, 2, 3}` with an independent set `{4, 5, 6}`, where `4 ~ {0, 3}`,
  `5 ~ {1, 3}`, `6 ~ {2, 3}`.  `locIndep_two_g7` and `not_locIndep_one_g7` give
  **`MaxDef g7 = 2`**, the four cyclic orderings `g7cyc012`, `g7cyc034`, `g7cyc135`, `g7cyc236` with their injectivity and
  adjacency certificates (`g7cyc012_inj`, `g7cyc012_cyc`, …) are what `JSPProblem/PetalBound.lean`
  turns into odd cycles through the generic lemma `JSP90.isOddCycle_triple`;
* **`prop`** on `Fin 9`: the *propeller* — the triangle `0 - 1 - 2 - 0` with a pendant triangle at
  each of its three vertices (`0 - 3 - 4 - 0`, `1 - 5 - 6 - 0`, `2 - 7 - 8 - 0`).  `prop_adj` is a
  formula on `Fin.val` (each pendant is a fibre), `locIndep_three_prop` and `not_locIndep_two_prop`
  give **`MaxDef prop = 3`**, and the four cyclic orderings `propCCyc`, `propT0Cyc`, `propT1Cyc`,
  `propT2Cyc` are what `PetalBound.lean` turns into odd cycles.

`JSPProblem/PetalBound.lean` then turns these into the negative results of round 120:

* `PetalSet g7 g7C = g7C` with `|PetalSet| = 3 > 2 = MaxDef g7`: the attachment set is **not**
  charged against the deficiency;
* `PetalSet prop propC = propC` together with `¬ CloseToBipartite 2 prop`: the `|C| - 1` term of the
  two-attachment transversal is **not** enough once petals exist.
-/

import JSPProblem.Petal

namespace JSP90

open Finset Fintype Set

noncomputable section

/-- One computable `DecidableEq (Fin n)` for the whole file (the trick of
`JSPProblem/Petersen.lean`), so that every finite statement below is decided by the kernel. -/
local instance petalFiniteEqFin (n : ℕ) : DecidableEq (Fin n) := instDecidableEqFin n

/-! ### The seven-vertex graph `g7` -/

section G7

/-- **Adjacency in `g7`**: `K_4` on `{0, 1, 2, 3}`, an independent set `{4, 5, 6}`, and `4 ~ {0, 3}`,
`5 ~ {1, 3}`, `6 ~ {2, 3}`. -/
def g7Adj (v w : Fin 7) : Prop :=
  v.val ≠ w.val ∧
    ((v.val ≤ 3 ∧ w.val ≤ 3) ∨
      (v.val = 0 ∧ w.val = 4) ∨ (v.val = 4 ∧ w.val = 0) ∨
      (v.val = 1 ∧ w.val = 5) ∨ (v.val = 5 ∧ w.val = 1) ∨
      (v.val = 2 ∧ w.val = 6) ∨ (v.val = 6 ∧ w.val = 2) ∨
      (v.val = 3 ∧ w.val = 4) ∨ (v.val = 4 ∧ w.val = 3) ∨
      (v.val = 3 ∧ w.val = 5) ∨ (v.val = 5 ∧ w.val = 3) ∨
      (v.val = 3 ∧ w.val = 6) ∨ (v.val = 6 ∧ w.val = 3))

instance instDecidableG7Adj (v w : Fin 7) : Decidable (g7Adj v w) := by
  unfold g7Adj
  infer_instance

/-- **`g7`**: `K_4` with three extra vertices, each adjacent to two vertices of the `K_4`. -/
def g7 : SimpleGraph (Fin 7) where
  Adj := g7Adj
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

@[simp] theorem g7_adj {v w : Fin 7} : g7.Adj v w ↔ g7Adj v w := Iff.rfl

local instance instDecidableRelG7 : DecidableRel g7.Adj :=
  fun v w => inferInstanceAs (Decidable (g7Adj v w))

/-- The triangle `0 - 1 - 2 - 0`, as a cyclic ordering. -/
def g7cyc012 : Fin 3 → Fin 7 := Fin.cases 0 (Fin.cases 1 (Fin.cases 2 Fin.elim0))

/-- The triangle `0 - 3 - 4 - 0`. -/
def g7cyc034 : Fin 3 → Fin 7 := Fin.cases 0 (Fin.cases 3 (Fin.cases 4 Fin.elim0))

/-- The triangle `1 - 3 - 5 - 1`. -/
def g7cyc135 : Fin 3 → Fin 7 := Fin.cases 1 (Fin.cases 3 (Fin.cases 5 Fin.elim0))

/-- The triangle `2 - 3 - 6 - 2`. -/
def g7cyc236 : Fin 3 → Fin 7 := Fin.cases 2 (Fin.cases 3 (Fin.cases 6 Fin.elim0))

theorem g7cyc012_inj : Function.Injective g7cyc012 := by decide

theorem g7cyc034_inj : Function.Injective g7cyc034 := by decide

theorem g7cyc135_inj : Function.Injective g7cyc135 := by decide

theorem g7cyc236_inj : Function.Injective g7cyc236 := by decide

theorem g7cyc012_cyc : ∀ j : Fin 3, g7.Adj (g7cyc012 j) (g7cyc012 (cycSucc j)) := by decide

theorem g7cyc034_cyc : ∀ j : Fin 3, g7.Adj (g7cyc034 j) (g7cyc034 (cycSucc j)) := by decide

theorem g7cyc135_cyc : ∀ j : Fin 3, g7.Adj (g7cyc135 j) (g7cyc135 (cycSucc j)) := by decide

theorem g7cyc236_cyc : ∀ j : Fin 3, g7.Adj (g7cyc236 j) (g7cyc236 (cycSucc j)) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **`LocIndep 2 g7`**: the maximum deficiency of `g7` is at most two — exhaustive decision over the
`128` vertex sets. -/
theorem locIndep_two_g7 : LocIndep 2 g7 := by
  unfold LocIndep
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- `g7` satisfies no stronger local hypothesis, so its deficiency is **exactly** two: the vertex set
`{0, 1, 2, 3}` is a `K_4`, whose largest independent set has size one. -/
theorem not_locIndep_one_g7 : ¬ LocIndep 1 g7 := by
  unfold LocIndep
  decide

end G7

/-! ### The nine-vertex propeller `prop` -/

section Propeller

/-- **Adjacency in the propeller**: `Adj v w ↔ v ≠ w ∧` (`v` and `w` are both in `{0, 1, 2}`, or they
are the two extra vertices of the same pendant triangle, or one is `i ∈ {0, 1, 2}` and the other is
`3 + 2 i` or `4 + 2 i`).  So the graph is the triangle `{0, 1, 2}` with a pendant triangle
`{i, 3 + 2 i, 4 + 2 i}` at each of its vertices. -/
def propAdj (v w : Fin 9) : Prop :=
  v.val ≠ w.val ∧
    ((v.val ≤ 2 ∧ w.val ≤ 2) ∨
      (3 ≤ v.val ∧ 3 ≤ w.val ∧ (v.val - 3) / 2 = (w.val - 3) / 2) ∨
      (v.val ≤ 2 ∧ 3 ≤ w.val ∧ (w.val - 3) / 2 = v.val) ∨
      (3 ≤ v.val ∧ w.val ≤ 2 ∧ (v.val - 3) / 2 = w.val))

instance instDecidablePropAdj (v w : Fin 9) : Decidable (propAdj v w) := by
  unfold propAdj
  infer_instance

/-- **`prop`**: the propeller, the triangle `0 - 1 - 2 - 0` with a pendant triangle at each vertex. -/
def prop : SimpleGraph (Fin 9) where
  Adj := propAdj
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

@[simp] theorem prop_adj {v w : Fin 9} : prop.Adj v w ↔ propAdj v w := Iff.rfl

local instance instDecidableRelProp : DecidableRel prop.Adj :=
  fun v w => inferInstanceAs (Decidable (propAdj v w))

/-- The central triangle `0 - 1 - 2 - 0`. -/
def propCCyc : Fin 3 → Fin 9 := Fin.cases 0 (Fin.cases 1 (Fin.cases 2 Fin.elim0))

/-- The pendant triangle `0 - 3 - 4 - 0`. -/
def propT0Cyc : Fin 3 → Fin 9 := Fin.cases 0 (Fin.cases 3 (Fin.cases 4 Fin.elim0))

/-- The pendant triangle `1 - 5 - 6 - 0`. -/
def propT1Cyc : Fin 3 → Fin 9 := Fin.cases 1 (Fin.cases 5 (Fin.cases 6 Fin.elim0))

/-- The pendant triangle `2 - 7 - 8 - 0`. -/
def propT2Cyc : Fin 3 → Fin 9 := Fin.cases 2 (Fin.cases 7 (Fin.cases 8 Fin.elim0))

theorem propCCyc_inj : Function.Injective propCCyc := by decide

theorem propT0Cyc_inj : Function.Injective propT0Cyc := by decide

theorem propT1Cyc_inj : Function.Injective propT1Cyc := by decide

theorem propT2Cyc_inj : Function.Injective propT2Cyc := by decide

theorem propCCyc_cyc : ∀ j : Fin 3, prop.Adj (propCCyc j) (propCCyc (cycSucc j)) := by decide

theorem propT0Cyc_cyc : ∀ j : Fin 3, prop.Adj (propT0Cyc j) (propT0Cyc (cycSucc j)) := by decide

theorem propT1Cyc_cyc : ∀ j : Fin 3, prop.Adj (propT1Cyc j) (propT1Cyc (cycSucc j)) := by decide

theorem propT2Cyc_cyc : ∀ j : Fin 3, prop.Adj (propT2Cyc j) (propT2Cyc (cycSucc j)) := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **`LocIndep 3 prop`**: the maximum deficiency of the propeller is at most three — exhaustive
decision over the `512` vertex sets. -/
theorem locIndep_three_prop : LocIndep 3 prop := by
  unfold LocIndep
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- The propeller satisfies no stronger local hypothesis, so its deficiency is **exactly** three: the
three pendant triangles are vertex-disjoint odd cycles. -/
theorem not_locIndep_two_prop : ¬ LocIndep 2 prop := by
  unfold LocIndep
  decide

end Propeller

end

end JSP90