/-
# JSP-000090, round 134 — `JSPProblem/Nonagon.lean`: **the nine-vertex witness that refutes
# `JSP90.PetalSetLeTwoOfOne`**, i.e. the top target of rounds 119–131

Attack family 63, part 5.  The exhaustive search run this round
(`discovery/JSP-000090/r134.c`, over **all** graphs with `MaxDef ≤ 1` on `n ≤ 8` vertices —
55 179 262 of them — and then on `n = 9`) found, at `n = 9`, the **first graph of this development in
which a triangle has THREE attachment points**:

```
g9  (on Fin 9)   edges  0-5  0-6  0-7  0-8  1-5  1-6  2-5  2-8
                        3-6  3-7  4-7  4-8  5-7  6-8
```

`g9` satisfies `LocIndep 1 g9` (`JSP90.locIndep_one_g9`, an exhaustive kernel decision over the
`2 ^ 9` vertex sets) and it has **exactly two triangles**, `T₁ = {0, 5, 7}` and `T₂ = {0, 6, 8}`,
and **each of the three vertices of each triangle lies alone on an odd cycle**:

| triangle | attachment point | the petal |
| --- | --- | --- |
| `T₁ = {0,5,7}` | `0` | `{0,6,8}` = `T₂` |
| `T₁ = {0,5,7}` | `5` | `{1,2,5,6,8}` |
| `T₁ = {0,5,7}` | `7` | `{3,4,6,7,8}` |
| `T₂ = {0,6,8}` | `0` | `{0,5,7}` = `T₁` |
| `T₂ = {0,6,8}` | `6` | `{1,3,5,6,7}` |
| `T₂ = {0,6,8}` | `8` | `{2,4,5,7,8}` |

Consequences, all proved in `JSPProblem/AttachErase.lean` from the data of this file:

* **`JSP90.PetalSetLeTwoOfOne` IS FALSE** — `JSP90.not_petalSetLeTwoOfOne_g9`.  This was the single
  remaining residual of rounds 119–131 and the **top target** of
  `discovery/JSP-000090/policy.json` since round 123.  Every route through it — in particular
  `JSP90.closeToBipartite_two_of_triangle_petalSet_le_two` and
  `JSP90.erdos73On_one_of_triangle_of_petalSetLeTwoOfOne` — is machine-checkably **dead**;
* **`JSP90.PetalSetLeTwoOfOneAny` (Part 3 of `AttachErase.lean`) IS FALSE** as well;
* **`JSP90.ShortestOddCycleTransversal 2` (Part 3 of `AttachErase.lean`) IS FALSE**: both triangles
  are shortest odd cycles and neither admits a 2-transversal *inside it*
  (`JSP90.not_hitsOddCycles_erase_of_mem_g9_T₁`, `JSP90.not_hitsOddCycles_erase_of_mem_g9_T₂`);
* the conclusion of Erdős #73 at `k = 1` with the constant `2` is **not** refuted: `g9` is
  `CloseToBipartite 2` — the certificate is `{5, 6}`, which is **contained in no triangle and in no
  shortest odd cycle**.  So the sharp `k = 1` case is still `f(1) = 2`; only the *shape* of the
  transversal is wrong, and the correct statement is `JSP90.TwoTransversal 2`, which
  `JSPProblem/AttachErase.lean` proves **equivalent** to `Erdős73On 1 2`.

So after this round the sharp case `k = 1` of Erdős #73 has exactly one residual,
`JSP90.TwoTransversal 2` ⟺ `JSP90.Erdős73On 1 2`, and **three** candidate shapes for its
certificate have been refuted by machine-checked witnesses: two vertices of a triangle (this file),
`|C| - 1 + |PetalSet G C|` vertices (`JSPProblem/PetalBound.lean`, witness the propeller `prop`),
and the petals of a triangle (`JSPProblem/Petal3.lean`, witness `octa6`).
-/

import JSPProblem.PetalOverlap

namespace JSP90

open Finset Fintype

noncomputable section

/-- **One computable `DecidableEq (Fin n)` for the whole file** (the trick of
`JSPProblem/Petersen.lean` and `JSPProblem/Windmill.lean`), so that every finite statement below is
a kernel computation.  Every *statement* exported by this file is instance-free, so
`JSPProblem/AttachErase.lean` may consume them in its classical scope. -/
local instance instDecidableEqFinG9 (n : ℕ) : DecidableEq (Fin n) := instDecidableEqFin n

/-! ### The nine-vertex witness `g9` -/

section G9

/-- **Adjacency in `g9`**: the fourteen edges

```
0-5  0-6  0-7  0-8  1-5  1-6  2-5  2-8  3-6  3-7  4-7  4-8  5-7  6-8
```

as a formula on `Fin.val`, so that every finite statement about `g9` is a kernel computation. -/
def g9Adj (v w : Fin 9) : Prop :=
  v.val ≠ w.val ∧
    ((v.val = 0 ∧ (w.val = 5 ∨ w.val = 6 ∨ w.val = 7 ∨ w.val = 8)) ∨
      (w.val = 0 ∧ (v.val = 5 ∨ v.val = 6 ∨ v.val = 7 ∨ v.val = 8)) ∨
      (v.val = 1 ∧ w.val = 5) ∨ (w.val = 1 ∧ v.val = 5) ∨
      (v.val = 1 ∧ w.val = 6) ∨ (w.val = 1 ∧ v.val = 6) ∨
      (v.val = 2 ∧ w.val = 5) ∨ (w.val = 2 ∧ v.val = 5) ∨
      (v.val = 2 ∧ w.val = 8) ∨ (w.val = 2 ∧ v.val = 8) ∨
      (v.val = 3 ∧ w.val = 6) ∨ (w.val = 3 ∧ v.val = 6) ∨
      (v.val = 3 ∧ w.val = 7) ∨ (w.val = 3 ∧ v.val = 7) ∨
      (v.val = 4 ∧ w.val = 7) ∨ (w.val = 4 ∧ v.val = 7) ∨
      (v.val = 4 ∧ w.val = 8) ∨ (w.val = 4 ∧ v.val = 8) ∨
      (v.val = 5 ∧ w.val = 7) ∨ (w.val = 5 ∧ v.val = 7) ∨
      (v.val = 6 ∧ w.val = 8) ∨ (w.val = 6 ∧ v.val = 8))

/-- **`g9Adj` is decidable**: it is a formula about `Nat`s. -/
instance instDecidableRelG9Adj (v w : Fin 9) : Decidable (g9Adj v w) := by
  unfold g9Adj
  infer_instance

/-- **The nine-vertex witness.** -/
def g9 : SimpleGraph (Fin 9) where
  Adj := g9Adj
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

@[simp] theorem g9_adj {v w : Fin 9} : g9.Adj v w ↔ g9Adj v w := by
  unfold SimpleGraph.Adj g9
  rfl

/-- Adjacency of `g9` is decidable. -/
local instance : DecidableRel g9.Adj := fun v w => inferInstanceAs (Decidable (g9Adj v w))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- **`LocIndep 1 g9`**: every vertex set of `g9` carries an independent set of size
`≥ (|X| - 1) / 2`, by exhaustive decision over the `2 ^ 9` vertex sets.  Erdős's local hypothesis
holds for `g9` with `k = 1`, so `g9` is a genuine member of the class of JSP-000090. -/
theorem locIndep_one_g9 : LocIndep 1 g9 := by
  unfold LocIndep
  decide

/-! ### The two triangles and their six petals -/

/-- **The two triangles of `g9` as named vertex sets.** -/
def g9T1 : Finset (Fin 9) := {0, 5, 7}

def g9T2 : Finset (Fin 9) := {0, 6, 8}

/-- **The three petals of `T₁` and the three petals of `T₂`, as named vertex sets.** -/
def g9P5 : Finset (Fin 9) := {1, 2, 5, 6, 8}

def g9P7 : Finset (Fin 9) := {3, 4, 6, 7, 8}

def g9Q6 : Finset (Fin 9) := {1, 3, 5, 6, 7}

def g9Q8 : Finset (Fin 9) := {2, 4, 5, 7, 8}

/-- **The cyclic numbering of the triangle `T₁ = {0,5,7}` of `g9`.** -/
def g9T1Cyc : Fin 3 → Fin 9 :=
  Fin.cases 0 (Fin.cases 5 (Fin.cases 7 Fin.elim0))

/-- **`T₁ = {0, 5, 7}` is an odd cycle of `g9`.** -/
theorem isOddCycle_g9_T1 : IsOddCycle g9 g9T1 :=
  ⟨3, g9T1Cyc, by decide, by decide, by decide, by decide, by decide⟩

/-- **The cyclic numbering of the triangle `T₂ = {0,6,8}` of `g9`.** -/
def g9T2Cyc : Fin 3 → Fin 9 :=
  Fin.cases 0 (Fin.cases 6 (Fin.cases 8 Fin.elim0))

/-- **`T₂ = {0, 6, 8}` is an odd cycle of `g9`.** -/
theorem isOddCycle_g9_T2 : IsOddCycle g9 g9T2 :=
  ⟨3, g9T2Cyc, by decide, by decide, by decide, by decide, by decide⟩

/-- **The petal of `T₁` at `0` is `T₂` itself**, the cyclic numbering `0 ↦ 0, 1 ↦ 6, 2 ↦ 8`. -/
def g9P0Cyc : Fin 3 → Fin 9 :=
  Fin.cases 0 (Fin.cases 6 (Fin.cases 8 Fin.elim0))

/-- **The petal of `T₁` at `5` is `{1,2,5,6,8}`**, the `5`-cycle `5 - 1 - 6 - 8 - 2 - 5`. -/
def g9P5Cyc : Fin 5 → Fin 9 :=
  Fin.cases 5 (Fin.cases 1 (Fin.cases 6 (Fin.cases 8 (Fin.cases 2 Fin.elim0))))

/-- **The petal of `T₁` at `7` is `{3,4,6,7,8}`**, the `5`-cycle `7 - 3 - 6 - 8 - 4 - 7`. -/
def g9P7Cyc : Fin 5 → Fin 9 :=
  Fin.cases 7 (Fin.cases 3 (Fin.cases 6 (Fin.cases 8 (Fin.cases 4 Fin.elim0))))

/-- **The petal of `T₂` at `6` is `{1,3,5,6,7}`**, the `5`-cycle `6 - 1 - 5 - 7 - 3 - 6`. -/
def g9Q6Cyc : Fin 5 → Fin 9 :=
  Fin.cases 6 (Fin.cases 1 (Fin.cases 5 (Fin.cases 7 (Fin.cases 3 Fin.elim0))))

/-- **The petal of `T₂` at `8` is `{2,4,5,7,8}`**, the `5`-cycle `8 - 2 - 5 - 7 - 4 - 8`. -/
def g9Q8Cyc : Fin 5 → Fin 9 :=
  Fin.cases 8 (Fin.cases 2 (Fin.cases 5 (Fin.cases 7 (Fin.cases 4 Fin.elim0))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- **`{1,2,5,6,8}` is an odd cycle of `g9`** (the petal of `T₁` at `5`). -/
theorem isOddCycle_g9_P5 : IsOddCycle g9 g9P5 :=
  ⟨5, g9P5Cyc, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- **`{3,4,6,7,8}` is an odd cycle of `g9`** (the petal of `T₁` at `7`). -/
theorem isOddCycle_g9_P7 : IsOddCycle g9 g9P7 :=
  ⟨5, g9P7Cyc, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- **`{1,3,5,6,7}` is an odd cycle of `g9`** (the petal of `T₂` at `6`). -/
theorem isOddCycle_g9_Q6 : IsOddCycle g9 g9Q6 :=
  ⟨5, g9Q6Cyc, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- **`{2,4,5,7,8}` is an odd cycle of `g9`** (the petal of `T₂` at `8`). -/
theorem isOddCycle_g9_Q8 : IsOddCycle g9 g9Q8 :=
  ⟨5, g9Q8Cyc, by decide, by decide, by decide, by decide, by decide⟩

/-- **THE THREE PETALS OF `T₁ = {0,5,7}` MEET `T₁` IN EXACTLY `0`, `5` AND `7` RESPECTIVELY.** -/
theorem inter_g9_P0_T1 : g9T2 ∩ g9T1 = {0} := by decide

theorem inter_g9_P5_T1 : g9P5 ∩ g9T1 = {5} := by decide

theorem inter_g9_P7_T1 : g9P7 ∩ g9T1 = {7} := by decide

/-- **THE THREE PETALS OF `T₂ = {0,6,8}` MEET `T₂` IN EXACTLY `0`, `6` AND `8` RESPECTIVELY.** -/
theorem inter_g9_T1_T2 : g9T1 ∩ g9T2 = {0} := by decide

theorem inter_g9_Q6_T2 : g9Q6 ∩ g9T2 = {6} := by decide

theorem inter_g9_Q8_T2 : g9Q8 ∩ g9T2 = {8} := by decide

/-- **`{5, 6}` IS A CERTIFICATE FOR `CloseToBipartite 2 g9`** in the odd-cycle language: it is the
pair found by the search of `discovery/JSP-000090/r134.c`, which reports the largest odd cycle
transversal number of `g9` to be `2`.  The formal content of the certificate is in
`JSPProblem/AttachErase.lean`. -/
def g9Cert : Finset (Fin 9) := {5, 6}

theorem mem_g9Cert : ∀ v ∈ g9Cert, v.val = 5 ∨ v.val = 6 := by
  intro v hv
  simp only [g9Cert, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h | h <;> subst h <;> simp

end G9

end

end JSP90
