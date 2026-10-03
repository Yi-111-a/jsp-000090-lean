/-
# JSPProblem/PetalOverlap.lean — the **OVERLAP BUDGET**, and the machine-checked **REFUTATION** of the
# petal-overlap bound: the `k = 1` attachment route is closed

Attack family 61.  Rounds 119–130 attacked the case `k = 1` of Erdős Problem #73 through the
**attachment set** of a triangle: at `LocIndep 1` every odd cycle meets a triangle `T`, so `T` is an
odd cycle transversal, and the whole content of the case is

> `JSP90.PetalSetLeTwoOfOne` — *the attachment set of a triangle has at most **two** elements*, so
> two vertices of `T` suffice (round 123).

Round 131 does **not** attack that statement again.  It first proves the natural *counting*
statement behind the whole approach — **the overlap budget** (Part 1) — and then shows that the
budget is the **only** thing the counting gives: the two petals of a triangle at *distinct*
attachment points may meet in a **single** vertex even when `LocIndep 1` holds (Part 3).  The family
of statements

```lean
JSP90.PetalOverlapGe k :  ∀ G T D E a b, LocIndep k G → IsOddCycle G T → T.card = 3 →
    IsOddCycle G D → IsOddCycle G E → (D ∩ T = {a}) → (E ∩ T = {b}) → a ≠ b →
    ∃ S, S ⊆ D ∧ S ⊆ E ∧ 3 - k ≤ |S|
```

is therefore **refuted for every `k = 1, 2`** and holds exactly for `k = 0` and `k ≥ 3`
(`JSP90.petalOverlapGe_iff`), so no argument of that shape may be attempted again.

## What is proved

* **`JSP90.two_card_inter_add_one_le_card_of_isOddCycle_of_isIndepSet`** — the classical
  `α(C_m) ≤ ⌊m/2⌋` for an *arbitrary* independent set of `G` meeting an odd cycle, in the finset form
  the counting needs.
* **`JSP90.two_mul_card_add_two_card_inter_add_one_le_card_add_card_of_isOddCycle`** — **THE OVERLAP
  BUDGET, TWO CYCLES**: for odd cycles `D`, `E` and an independent `S ⊆ D ∪ E`,

  > `2 * |S| + 2 * |S ∩ D ∩ E| ≤ |D| + |E| - 2`.

  Every vertex of `S ∩ D ∩ E` is counted twice on the left and is therefore *wasted*: it is a vertex
  an independent set cannot use.
* **`JSP90.not_mem_inter_of_locIndep_one`** and
  **`JSP90.exists_indepSet_avoiding_inter_of_locIndep_one`** — **at `LocIndep 1`, the unique meeting
  point of two odd cycles that meet in exactly one point is in no independent set supplied by Erdős's
  hypothesis**.  (Machine check, `discovery/JSP-000090/r131d.c`: the corresponding *geometric* lemma —
  "that point is in every odd cycle" — is **false**, already for the 6-vertex 3-sun; the three
  triangles of Part 3 are the counterexample.)
* **`JSP90.two_le_card_inter_neigh_of_mem_isOddCycle`** and
  **`JSP90.subset_inter_neigh_of_card_neigh_eq_two`** — **a vertex of an odd cycle has two distinct
  neighbours inside the cycle**; hence a vertex of an odd cycle whose whole neighbourhood has two
  elements carries **both** of them on every odd cycle through it.  `JSPProblem/Layer.lean` has the
  version for a vertex avoiding `S`; this is the version for the cycle itself.
* **`JSP90.inter_sun3_petal_zero`, `JSP90.inter_sun3_petal_two`,
  `JSP90.card_inter_sun3_petals_eq_one`, `JSP90.sun3_three_petals_data`** — **the triangle
  `T₁ = {0, 1, 2}` of the 3-sun `sun3` (the graph round 123 called `g6`) has petals at the two
  *distinct* attachment points `0` and `2`, namely `T₃ = {0, 4, 5}` and `T₂ = {2, 3, 5}`, and these two
  petals meet in the single vertex `5`** — while `sun3` satisfies `LocIndep 1`
  (`JSP90.locIndep_one_sun3`) and needs two vertices to become bipartite
  (`JSP90.not_closeToBipartite_one_sun3`).
* **`JSP90.pinch`, `JSP90.locIndep_two_pinch`** — a triangle with a pendant triangle at each of two of
  its vertices: `LocIndep 2`, with the two petals of the central triangle **disjoint**.
* **`JSP90.not_petalOverlapGe_one`, `JSP90.not_petalOverlapGe_two`,
  `JSP90.petalOverlapGe_iff`** — **the complete classification of the petal-overlap bound**: it holds
  exactly for `k = 0` (vacuously, `LocIndep 0` forces bipartiteness) and `k ≥ 3` (trivially), and is
  **false for `k = 1` and `k = 2`**.
* **`JSP90.erdos73On_of_triangle_of_oddCycles_meet_two`** — **A NEW INSTANCE OF THE HEADLINE
  THEOREM, FOR EVERY `k`, WITH THE CONSTANT `2`**: if every odd cycle of `G` meets a fixed triangle in
  at least two vertices, two vertices suffice.  The hypothesis is structural — it counts nothing and
  bounds no size, no degree and no girth — and, exactly as in `JSP90.erdos73On_of_edgeCount`, Erdős's
  hypothesis is not needed for it.

## What is *not* proved

`jsp_000090_main` is **not** declared and `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas) is untouched, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.  `JSP90.PetalSetLeTwoOfOne` itself is untouched: the
exhaustive machine check of this round (`discovery/JSP-000090/r131d.c`, **all** `LocIndep 1` graphs on
`n ≤ 7` vertices, `986 787` of them at `n = 7`) still finds **no** triangle with three attachment
points, and Part 3 shows the bound is *attained* at `sun3`; so the residual of rounds 123–130 is
unchanged — the case of petals of length `≥ 5` — and the only counting available for it is the
budget of Part 1, which Part 4 shows to be exhausted.
-/

import JSPProblem.OneK
import JSPProblem.Finite
import JSPProblem.Sun
import JSPProblem.Branch
import Mathlib.Data.Finset.SDiff

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqPetalOverlap : DecidableEq V := Classical.decEq V

/-! ## Part 1 — THE OVERLAP BUDGET -/

section Budget

/-- **AN INDEPENDENT SET MEETS AN ODD CYCLE IN AT MOST HALF ITS VERTICES, ROUNDED DOWN.**

The classical `α(C_m) ≤ ⌊m / 2⌋`, in the form the counting needs: for an arbitrary independent set
`S` of `G` (not only of `G[C]`), `2 * |S ∩ C| + 1 ≤ |C|`.  A vertex of `S ∩ C` spends one unit of
the `+ 1` of Erdős's hypothesis. -/
theorem two_card_inter_add_one_le_card_of_isOddCycle_of_isIndepSet {C : Finset V}
    (hC : IsOddCycle G C) {S : Finset V} (hS : G.IsIndepSet S) :
    2 * (S ∩ C).card + 1 ≤ C.card := by
  have h1 : 2 * indepCard G C + 1 ≤ C.card := two_indepCard_add_one_le_card_oddCycle hC
  have h2 : (S ∩ C).card ≤ indepCard G C :=
    le_indepCard_of_isIndepSet Finset.inter_subset_right
      (isIndepSet_sub hS Finset.inter_subset_left)
  omega

/-- **`S` SPLITS OVER `D` AND `E`** when `S ⊆ D ∪ E`. -/
theorem eq_union_inter_inter_of_subset {D E S : Finset V} (hS : S ⊆ D ∪ E) :
    (S ∩ D) ∪ (S ∩ E) = S := by
  ext x
  simp only [Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩)
    · exact hx
    · exact hx
  · intro hx
    rcases Finset.mem_union.mp (hS hx) with hD | hE
    · exact Or.inl ⟨hx, hD⟩
    · exact Or.inr ⟨hx, hE⟩

/-- **`S` SPLITS OVER `D` AND `E`, WITH THE DOUBLE-COUNTED PART EXACTLY `S ∩ D ∩ E`.** -/
theorem card_eq_card_inter_add_card_inter_sub_card_inter {D E S : Finset V} (hS : S ⊆ D ∪ E) :
    (S ∩ D).card + (S ∩ E).card = S.card + (S ∩ D ∩ E).card := by
  have h1 := eq_union_inter_inter_of_subset hS
  have h2 : (S ∩ D) ∩ (S ∩ E) = S ∩ D ∩ E := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  have h3 := Finset.card_union_add_card_inter (S ∩ D) (S ∩ E)
  rw [h1, h2] at h3
  omega

/-- **THE OVERLAP BUDGET, TWO CYCLES.**  For odd cycles `D`, `E` of `G` and an independent set
`S ⊆ D ∪ E`,

> `2 * |S| + 2 * |S ∩ D ∩ E| ≤ |D| + |E| - 2`.

Indeed `|S| = |S ∩ D| + |S ∩ E| - |S ∩ D ∩ E|`, and each of `|S ∩ D|`, `|S ∩ E|` spends one unit of
the odd cycles' budget (`JSP90.two_card_inter_add_one_le_card_of_isOddCycle_of_isIndepSet`).  So a
vertex of `D ∩ E` that lies in `S` is counted twice on the left: the overlap is *not free*.  This is
the quantitative content of the "petals pairwise meet" analysis of rounds 123–126, and — see
Part 4 — it is all the counting can give. -/
theorem two_mul_card_add_two_card_inter_add_one_le_card_add_card_of_isOddCycle {D E : Finset V}
    (hD : IsOddCycle G D) (hE : IsOddCycle G E) {S : Finset V} (hSsub : S ⊆ D ∪ E)
    (hSi : G.IsIndepSet S) :
    2 * S.card + 2 * (S ∩ D ∩ E).card ≤ D.card + E.card - 2 := by
  have h1 := two_card_inter_add_one_le_card_of_isOddCycle_of_isIndepSet hD hSi
  have h2 := two_card_inter_add_one_le_card_of_isOddCycle_of_isIndepSet hE hSi
  have h3 := card_eq_card_inter_add_card_inter_sub_card_inter hSsub
  omega

/-- **AT `LocIndep 1`, TWO ODD CYCLES MEETING IN ONE POINT: THAT POINT IS NEVER USED.**

Let `D`, `E` be odd cycles of `G` with `(D ∩ E).card = 1`, and let `S ⊆ D ∪ E` be an independent set
carrying `2 * |S| + 1 ≥ |D ∪ E|` (such an `S` exists by `LocIndep 1 G`).  Then `S` avoids the
unique vertex of `D ∩ E`.

This is the *only* thing the budget says about a one-point overlap, and it is the reason the
petal-overlap bound of Part 4 cannot be recovered from counting: the point is not *forbidden* in
`G`, it is only unavailable to an independent set. -/
theorem not_mem_inter_of_locIndep_one {D E : Finset V} (hG : LocIndep 1 G) (hD : IsOddCycle G D)
    (hE : IsOddCycle G E) (hone : (D ∩ E).card = 1) {v : V} (hv : v ∈ D ∩ E) {S : Finset V}
    (hSsub : S ⊆ D ∪ E) (hSi : G.IsIndepSet S) (hSlo : 2 * S.card + 1 ≥ (D ∪ E).card) : v ∉ S := by
  have h1 := two_mul_card_add_two_card_inter_add_one_le_card_add_card_of_isOddCycle hD hE hSsub hSi
  have h2 : (D ∪ E).card = D.card + E.card - 1 := by
    have h := Finset.card_union_add_card_inter D E
    rw [hone] at h
    omega
  have hz : (S ∩ D ∩ E).card = 0 := by omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
  have hxv : v = x := by
    have hv' := hv
    rw [hx] at hv'
    exact Finset.mem_singleton.mp hv'
  have hz2 : (S ∩ {x} : Finset V).card = 0 := by
    rw [← hx, ← Finset.inter_assoc]
    exact hz
  have hempty : S ∩ {x} = ∅ := Finset.card_eq_zero.mp hz2
  rw [hxv]
  intro hxs
  exact absurd (Finset.mem_inter.mpr ⟨hxs, Finset.mem_singleton_self x⟩) (by rw [hempty]; simp)

/-- The form of `JSP90.not_mem_inter_of_locIndep_one` with `S` produced by Erdős's hypothesis. -/
theorem exists_indepSet_avoiding_inter_of_locIndep_one {D E : Finset V} (hG : LocIndep 1 G)
    (hD : IsOddCycle G D) (hE : IsOddCycle G E) (hone : (D ∩ E).card = 1) :
    ∃ S : Finset V, S ⊆ D ∪ E ∧ G.IsIndepSet S ∧ 2 * S.card + 1 ≥ (D ∪ E).card ∧
      ∀ v ∈ D ∩ E, v ∉ S := by
  obtain ⟨S, hSsub, hSi, hSlo⟩ := hG (D ∪ E)
  refine ⟨S, hSsub, hSi, hSlo, fun v hv => ?_⟩
  exact not_mem_inter_of_locIndep_one hG hD hE hone hv hSsub hSi hSlo

end Budget

/-! ## Part 2 — A VERTEX OF AN ODD CYCLE HAS TWO NEIGHBOURS ON IT -/

section Neigh

/-- **A VERTEX OF AN ODD CYCLE HAS TWO DISTINCT NEIGHBOURS INSIDE THE CYCLE.**  These are its two
cycle-neighbours; `JSP90.two_le_innerDeg_of_mem_oddCycle` is the version for a vertex *avoiding* `S`,
and this one is for the cycle itself. -/
theorem two_le_card_inter_neigh_of_mem_isOddCycle {C : Finset V} (hC : IsOddCycle G C) {v : V}
    (hv : v ∈ C) : 2 ≤ (Neigh G v ∩ C).card := by
  classical
  obtain ⟨o, -⟩ := hC.cycleOrder
  obtain ⟨i, hi⟩ := (o.hmem v).mp hv
  have hsub : ({o.f (cycSucc i), o.f (o.prev i)} : Finset V) ⊆ Neigh G v ∩ C := by
    intro w hw
    rcases Finset.mem_insert.mp hw with hw | hw
    · rw [hw, Finset.mem_inter]
      exact ⟨by rw [← hi]; exact mem_neigh.mpr (o.hcyc i), (o.hmem _).mpr ⟨cycSucc i, rfl⟩⟩
    · rw [(Finset.mem_singleton.mp hw), Finset.mem_inter]
      exact ⟨by rw [← hi]; exact mem_neigh.mpr (o.adj_prev i), (o.hmem _).mpr ⟨o.prev i, rfl⟩⟩
  have hcard : ({o.f (cycSucc i), o.f (o.prev i)} : Finset V).card = 2 := by
    simp [Finset.card_insert_of_notMem, o.step_prev_ne i]
  have hle := Finset.card_le_card hsub
  omega

/-- **A VERTEX OF AN ODD CYCLE WITH EXACTLY TWO NEIGHBOURS CARRIES BOTH OF THEM ON EVERY ODD CYCLE
THROUGH IT.**  If `N(v)` has two elements and `v ∈ C` with `C` an odd cycle, then `N(v) ⊆ C`. -/
theorem subset_inter_neigh_of_card_neigh_eq_two {C : Finset V} (hC : IsOddCycle G C) {v : V}
    (hv : v ∈ C) {X : Finset V} (hX : Neigh G v = X) (hX2 : X.card = 2) : X ⊆ C := by
  have h1 : 2 ≤ (X ∩ C).card := by
    have h := two_le_card_inter_neigh_of_mem_isOddCycle hC hv
    rwa [hX] at h
  have h2 : (X \ C).card = X.card - (X ∩ C).card := by
    have h := Finset.card_sdiff (s := C) (t := X)
    rw [Finset.inter_comm] at h
    exact h
  have h4 : X \ C = ∅ := Finset.card_eq_zero.mp (by omega)
  intro x hx
  by_contra hxc
  have hne : x ∉ X \ C := by rw [h4]; simp
  exact absurd (Finset.mem_sdiff.mpr ⟨hx, hxc⟩) hne

end Neigh

/-! ## Part 3 — `sun3`, THE 3-SUN: TWO PETALS OF A TRIANGLE MEETING IN ONE POINT -/

section Sun3

local instance instDecidableRelSun3 : DecidableRel sun3.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ sun3Edge))

/-- **THE MEMBERSHIP TESTS FOR THE FOUR TRIANGLES OF `sun3`**. -/
theorem mem_T1' : ∀ x : Fin 6, x ∈ T1 ↔ x = 0 ∨ x = 1 ∨ x = 2 := by
  intro x
  simp [T1]

theorem mem_T2' : ∀ x : Fin 6, x ∈ T2 ↔ x = 2 ∨ x = 3 ∨ x = 5 := by
  intro x
  simp [T2]

theorem mem_T3' : ∀ x : Fin 6, x ∈ T3 ↔ x = 0 ∨ x = 4 ∨ x = 5 := by
  intro x
  simp [T3]

/-- **THE PETAL OF `T₁ = {0, 1, 2}` AT `0` IS `T₃ = {0, 4, 5}`.** -/
theorem inter_sun3_petal_zero : T3 ∩ T1 = ({0} : Finset (Fin 6)) := by decide

/-- **THE PETAL OF `T₁` AT `2` IS `T₂ = {2, 3, 5}`.** -/
theorem inter_sun3_petal_two : T2 ∩ T1 = ({2} : Finset (Fin 6)) := by decide

/-- **THE TWO PETALS OF `T₁` MEET IN THE SINGLE VERTEX `5`.**

`T₃ = {0, 4, 5}` is a petal of `T₁ = {0, 1, 2}` at `0`, `T₂ = {2, 3, 5}` is a petal at `2`, and
`|T₃ ∩ T₂| = 1`.  **This is the whole content of Part 4: the petal-overlap bound is false at
`k = 1`**, even though `sun3` satisfies `LocIndep 1` (`JSP90.locIndep_one_sun3`) and needs exactly
two vertices to become bipartite (`JSP90.not_closeToBipartite_one_sun3`).  It also says the
attachment set of `T₁` has (at least) two elements, so `JSP90.PetalSetLeTwoOfOne` — if it is a
theorem — is *sharp* at `sun3`. -/
theorem card_inter_sun3_petals_eq_one : (T3 ∩ T2).card = 1 := by decide

/-- **EVERY POINT OF `T₃` THAT LIES IN `T₁` IS `0`**: `T₃ ∩ T₁ = {0}`, elementwise. -/
theorem sun3_petal_zero_dir1 : ∀ x ∈ T3, x ∈ T1 → x = 0 := by
  intro x hxD hxT
  rcases (mem_T3' x).mp hxD with h | h | h <;> rcases (mem_T1' x).mp hxT with h' | h' | h' <;> simp_all

/-- **EVERY POINT OF `T₁` THAT LIES IN `T₃` IS `0`**. -/
theorem sun3_petal_zero_dir2 : ∀ x ∈ T1, x ∈ T3 → x = 0 := by
  intro x hxD hxT
  rcases (mem_T1' x).mp hxD with h | h | h <;> rcases (mem_T3' x).mp hxT with h' | h' | h' <;> simp_all

/-- **EVERY POINT OF `T₂` THAT LIES IN `T₁` IS `2`**: `T₂ ∩ T₁ = {2}`, elementwise. -/
theorem sun3_petal_two_dir1 : ∀ x ∈ T2, x ∈ T1 → x = 2 := by
  intro x hxD hxT
  rcases (mem_T2' x).mp hxD with h | h | h <;> rcases (mem_T1' x).mp hxT with h' | h' | h' <;> simp_all

/-- **EVERY POINT OF `T₁` THAT LIES IN `T₂` IS `2`**. -/
theorem sun3_petal_two_dir2 : ∀ x ∈ T1, x ∈ T2 → x = 2 := by
  intro x hxD hxT
  rcases (mem_T1' x).mp hxD with h | h | h <;> rcases (mem_T2' x).mp hxT with h' | h' | h' <;> simp_all

/-- **THE WITNESS OF THE `k = 1` REFUTATION, IN ONE STATEMENT.**  In `sun3`, which satisfies
`LocIndep 1`, the triangle `T₁ = {0, 1, 2}` has two *distinct* attachment points `0` and `2` with
petals `T₃` and `T₂` meeting in a single vertex. -/
theorem sun3_three_petals_data :
    IsOddCycle sun3 T1 ∧ T1.card = 3 ∧ IsOddCycle sun3 T3 ∧ IsOddCycle sun3 T2 ∧
      T3 ∩ T1 = ({0} : Finset (Fin 6)) ∧ T2 ∩ T1 = ({2} : Finset (Fin 6)) ∧ 0 ≠ 2 ∧
      (T3 ∩ T2).card = 1 :=
  ⟨isOddCycle_T1, by decide, isOddCycle_T3, isOddCycle_T2, inter_sun3_petal_zero,
    inter_sun3_petal_two, by decide, card_inter_sun3_petals_eq_one⟩

end Sun3

/-! ## Part 4 — THE PETAL-OVERLAP BOUND, AND ITS COMPLETE CLASSIFICATION -/

/-- **THE PETAL-OVERLAP BOUND**: if `T` is a triangle of `G` and `D`, `E` are petals of `T` at the
*distinct* attachment points `a` and `b` (so `D ∩ T = {a}` and `E ∩ T = {b}`), then `D` and `E` have
a common sub-finset of size `3 - k`.

This is the statement a *counting* proof of `JSP90.PetalSetLeTwoOfOne` would want, and it is
**false**: `JSP90.petalOverlapGe_iff` classifies it exactly.  The definition is phrased without any
`Finset` operation (the two petal conditions are given elementwise, the conclusion through a common
sub-finset) so that it does not depend on a `DecidableEq` instance. -/
def PetalOverlapGe (k : ℕ) : Prop :=
  ∀ (W : Type) (_ : Fintype W) (H : SimpleGraph W) (T D E : Finset W) (a b : W),
    LocIndep k H → IsOddCycle H T → T.card = 3 → IsOddCycle H D → IsOddCycle H E →
      (∀ x ∈ D, x ∈ T → x = a) → (∀ x ∈ T, x ∈ D → x = a) →
      (∀ x ∈ E, x ∈ T → x = b) → (∀ x ∈ T, x ∈ E → x = b) → a ≠ b →
      ∃ S : Finset W, S ⊆ D ∧ S ⊆ E ∧ 3 - k ≤ S.card

/-- **`PetalOverlapGe k` holds as soon as `3 ≤ k`**, trivially: `3 - k = 0`, and `∅` is a common
sub-finset. -/
theorem petalOverlapGe_of_ge_three {k : ℕ} (hk : 3 ≤ k) : PetalOverlapGe k := by
  intro W _ H T D E a b _ hT _ hD hE hDa1 hDa2 hEb1 hEb2 hab
  refine ⟨∅, fun _ h => by simp at h, fun _ h => by simp at h, ?_⟩
  have : 3 - k = 0 := by omega
  rw [this]
  exact Nat.zero_le (∅ : Finset W).card

/-- **`PetalOverlapGe 1` IS FALSE**, witnessed by `sun3` (`= g6` up to relabelling): the triangle
`T₁ = {0, 1, 2}`, the petals `T₃ = {0, 4, 5}` (at `0`) and `T₂ = {2, 3, 5}` (at `2`), which meet in
the single vertex `5`.

So at `LocIndep 1` two petals of a triangle at *distinct* attachment points may meet in **one**
vertex: no statement of the shape `2 ≤ |D ∩ E|` may be used in an argument about attachment sets,
and the counting of Part 1 is exhausted. -/
theorem not_petalOverlapGe_one : ¬ PetalOverlapGe 1 := by
  rintro h
  obtain ⟨S, hSD, hSE, hcard⟩ := h (Fin 6) inferInstance sun3 T1 T3 T2 0 2 locIndep_one_sun3
    isOddCycle_T1 (by decide) isOddCycle_T3 isOddCycle_T2 (sun3_petal_zero_dir1) (sun3_petal_zero_dir2)
    (sun3_petal_two_dir1) (sun3_petal_two_dir2) (by decide)
  have h1 : S ⊆ T3 ∩ T2 := fun _ h => Finset.mem_inter.mpr ⟨hSD h, hSE h⟩
  have h2 : S.card ≤ (T3 ∩ T2).card := Finset.card_le_card h1
  rw [card_inter_sun3_petals_eq_one] at h2
  omega

/-! ### The witness at `k = 2`: `pinch`, a triangle with a pendant triangle at two of its vertices -/

/-- A cyclic ordering of three vertices of `Fin n`. -/
def cyc3n (n : ℕ) (a b c : Fin n) : Fin 3 → Fin n := fun j =>
  match j.val with
  | 0 => a
  | 1 => b
  | _ => c

/-- The edges of `pinch`: the triangle `{0, 1, 2}`, the triangle `{0, 3, 4}` at `0` and the triangle
`{1, 5, 6}` at `1`. -/
def pinchEdge : Finset (Fin 7 × Fin 7) :=
  (Finset.univ : Finset (Fin 7 × Fin 7)).filter fun p =>
    (p.1 = 0 ∧ p.2 = 1) ∨ (p.1 = 1 ∧ p.2 = 0) ∨ (p.1 = 0 ∧ p.2 = 2) ∨ (p.1 = 2 ∧ p.2 = 0) ∨
      (p.1 = 1 ∧ p.2 = 2) ∨ (p.1 = 2 ∧ p.2 = 1) ∨ (p.1 = 0 ∧ p.2 = 3) ∨ (p.1 = 3 ∧ p.2 = 0) ∨
      (p.1 = 0 ∧ p.2 = 4) ∨ (p.1 = 4 ∧ p.2 = 0) ∨ (p.1 = 3 ∧ p.2 = 4) ∨ (p.1 = 4 ∧ p.2 = 3) ∨
      (p.1 = 1 ∧ p.2 = 5) ∨ (p.1 = 5 ∧ p.2 = 1) ∨ (p.1 = 1 ∧ p.2 = 6) ∨ (p.1 = 6 ∧ p.2 = 1) ∨
      (p.1 = 5 ∧ p.2 = 6) ∨ (p.1 = 6 ∧ p.2 = 5)

theorem pinchEdge_symm : ∀ v w : Fin 7, (v, w) ∈ pinchEdge ↔ (w, v) ∈ pinchEdge := by decide

theorem pinchEdge_irrefl : ∀ v : Fin 7, (v, v) ∉ pinchEdge := by decide

/-- **`pinch`**: the triangle `{0, 1, 2}` with a pendant triangle at each of `0` and `1`. -/
def pinch : SimpleGraph (Fin 7) where
  Adj v w := (v, w) ∈ pinchEdge
  symm := ⟨fun _ _ h => (pinchEdge_symm _ _).mp h⟩
  loopless := ⟨fun v h => pinchEdge_irrefl _ h⟩

@[simp] theorem pinch_adj {v w : Fin 7} : pinch.Adj v w ↔ (v, w) ∈ pinchEdge := Iff.rfl

local instance instDecidableRelPinch : DecidableRel pinch.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ pinchEdge))

set_option maxRecDepth 100000 in
/-- **`LocIndep 2 pinch`**: the deficiency of `pinch` is exactly `2`, witnessed by the two
vertex-disjoint pendant triangles `{0, 3, 4}` and `{1, 5, 6}`. -/
theorem locIndep_two_pinch : LocIndep 2 pinch := by
  unfold LocIndep
  decide

/-- The central triangle of `pinch`. -/
theorem isOddCycle_pinch_t₀ : IsOddCycle pinch ({0, 1, 2} : Finset (Fin 7)) :=
  ⟨3, cyc3n 7 0 1 2, by decide, by decide, by decide, by decide, by decide⟩

/-- The pendant triangle at `0`. -/
theorem isOddCycle_pinch_t₁ : IsOddCycle pinch ({0, 3, 4} : Finset (Fin 7)) :=
  ⟨3, cyc3n 7 0 3 4, by decide, by decide, by decide, by decide, by decide⟩

/-- The pendant triangle at `1`. -/
theorem isOddCycle_pinch_t₂ : IsOddCycle pinch ({1, 5, 6} : Finset (Fin 7)) :=
  ⟨3, cyc3n 7 1 5 6, by decide, by decide, by decide, by decide, by decide⟩

/-- The petal of the central triangle of `pinch` at `0` is `{0, 3, 4}`. -/
theorem inter_pinch_petal_zero : ({0, 3, 4} : Finset (Fin 7)) ∩ {0, 1, 2} = {0} := by decide

/-- The petal of the central triangle of `pinch` at `1` is `{1, 5, 6}`. -/
theorem inter_pinch_petal_one : ({1, 5, 6} : Finset (Fin 7)) ∩ {0, 1, 2} = {1} := by decide

/-- **THE TWO PETALS OF THE CENTRAL TRIANGLE OF `pinch` ARE DISJOINT.** -/
theorem inter_pinch_petals : ({0, 3, 4} : Finset (Fin 7)) ∩ {1, 5, 6} = ∅ := by decide

theorem mem_pinch_T0' : ∀ x : Fin 7, x ∈ ({0, 1, 2} : Finset (Fin 7)) ↔ x = 0 ∨ x = 1 ∨ x = 2 := by
  intro x
  simp

theorem mem_pinch_D' : ∀ x : Fin 7, x ∈ ({0, 3, 4} : Finset (Fin 7)) ↔ x = 0 ∨ x = 3 ∨ x = 4 := by
  intro x
  simp

theorem mem_pinch_E' : ∀ x : Fin 7, x ∈ ({1, 5, 6} : Finset (Fin 7)) ↔ x = 1 ∨ x = 5 ∨ x = 6 := by
  intro x
  simp

theorem pinch_petal_zero_dir1 : ∀ x ∈ ({0, 3, 4} : Finset (Fin 7)), x ∈ ({0, 1, 2} : Finset (Fin 7)) →
    x = 0 := by
  intro x hxD hxT
  rcases (mem_pinch_D' x).mp hxD with h | h | h <;> rcases (mem_pinch_T0' x).mp hxT with h' | h' | h' <;> simp_all

theorem pinch_petal_zero_dir2 : ∀ x ∈ ({0, 1, 2} : Finset (Fin 7)), x ∈ ({0, 3, 4} : Finset (Fin 7)) →
    x = 0 := by
  intro x hxD hxT
  rcases (mem_pinch_T0' x).mp hxD with h | h | h <;> rcases (mem_pinch_D' x).mp hxT with h' | h' | h' <;> simp_all

theorem pinch_petal_one_dir1 : ∀ x ∈ ({1, 5, 6} : Finset (Fin 7)), x ∈ ({0, 1, 2} : Finset (Fin 7)) →
    x = 1 := by
  intro x hxD hxT
  rcases (mem_pinch_E' x).mp hxD with h | h | h <;> rcases (mem_pinch_T0' x).mp hxT with h' | h' | h' <;> simp_all

theorem pinch_petal_one_dir2 : ∀ x ∈ ({0, 1, 2} : Finset (Fin 7)), x ∈ ({1, 5, 6} : Finset (Fin 7)) →
    x = 1 := by
  intro x hxD hxT
  rcases (mem_pinch_T0' x).mp hxD with h | h | h <;> rcases (mem_pinch_E' x).mp hxT with h' | h' | h' <;> simp_all

/-- **`PetalOverlapGe 2` IS FALSE**, witnessed by `pinch`: its two petals of the central triangle,
attached at `0` and `1`, are *disjoint*. -/
theorem not_petalOverlapGe_two : ¬ PetalOverlapGe 2 := by
  rintro h
  obtain ⟨S, hSD, hSE, hcard⟩ :=
    h (Fin 7) inferInstance pinch ({0, 1, 2} : Finset (Fin 7)) ({0, 3, 4} : Finset (Fin 7))
      ({1, 5, 6} : Finset (Fin 7)) 0 1 locIndep_two_pinch isOddCycle_pinch_t₀ (by decide)
      isOddCycle_pinch_t₁ isOddCycle_pinch_t₂ pinch_petal_zero_dir1 pinch_petal_zero_dir2
      pinch_petal_one_dir1 pinch_petal_one_dir2 (by decide)
  have h1 : S ⊆ ({0, 3, 4} : Finset (Fin 7)) ∩ {1, 5, 6} :=
    fun _ h => Finset.mem_inter.mpr ⟨hSD h, hSE h⟩
  have h2 : S.card ≤ (({0, 3, 4} : Finset (Fin 7)) ∩ {1, 5, 6}).card := Finset.card_le_card h1
  have h3 : (({0, 3, 4} : Finset (Fin 7)) ∩ {1, 5, 6}).card = 0 := by
    rw [inter_pinch_petals]
    simp
  omega

/-- **THE COMPLETE CLASSIFICATION OF THE PETAL-OVERLAP BOUND**: it holds exactly for `k = 0` (where
Erdős's hypothesis forces `G` to be bipartite, so the statement is vacuous) and for `k ≥ 3` (where it
is trivial), and it is **false** for `k = 1` (`sun3`) and `k = 2` (`pinch`).

So the bound `3 - k` on the intersection of two petals at distinct attachment points is not a theorem
at any `k` at which it is not trivial. -/
theorem petalOverlapGe_iff {k : ℕ} : PetalOverlapGe k ↔ k = 0 ∨ 3 ≤ k := by
  constructor
  · intro h
    rcases Nat.lt_or_ge k 3 with hlt | hge
    · by_cases hk0 : k = 0
      · exact Or.inl hk0
      · have hk12 : k = 1 ∨ k = 2 := by omega
        rcases hk12 with hk1 | hk2
        · rw [hk1] at h
          exact absurd h not_petalOverlapGe_one
        · rw [hk2] at h
          exact absurd h not_petalOverlapGe_two
    · exact Or.inr hge
  · rintro (rfl | hge)
    · intro W _ H T D E a b hH hT _ hD hE _ _ _ _ _
      have hb : H.IsBipartite := locIndep_zero_isBipartite hH
      exact absurd ⟨D, hD⟩ (not_isOddCycle_of_isBipartite hb)
    · exact petalOverlapGe_of_ge_three hge


/-! ## Part 5 — A NEW INSTANCE OF THE HEADLINE THEOREM: EVERY ODD CYCLE MEETS A TRIANGLE TWICE -/

section MeetTwo

/-- **TWO VERTICES SUFFICE IF EVERY ODD CYCLE MEETS A TRIANGLE IN AT LEAST TWO VERTICES.**

Two subsets of a three-element set, each of size at least two, meet; so every odd cycle meets every
two-element subset of the triangle `C`. -/
theorem closeToBipartite_two_of_oddCycles_meet_two {C : Finset V} (hC : IsOddCycle G C)
    (hC3 : C.card = 3) (hmeet : ∀ D : Finset V, IsOddCycle G D → 2 ≤ (D ∩ C).card) :
    CloseToBipartite 2 G := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hC3]; omega)
  refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2)).mpr
    ⟨C.erase a, by rw [Finset.card_erase_of_mem ha, hC3], ?_⟩
  intro D hD
  have htwo := hmeet D hD
  by_contra hc
  have hdis : Disjoint (D ∩ C) (C.erase a : Finset V) :=
    Finset.disjoint_left.mpr fun _ hx1 hx2 => by
      have hx : _ ∈ D ∩ C.erase a :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx1).1, hx2⟩
      rw [hc] at hx
      simp at hx
  have hcard := Finset.card_union_of_disjoint hdis
  have hce : (C.erase a : Finset V).card = 2 := by rw [Finset.card_erase_of_mem ha, hC3]
  have hle : ((D ∩ C) ∪ C.erase a).card ≤ C.card :=
    Finset.card_le_card (Finset.union_subset Finset.inter_subset_right (Finset.erase_subset a C))
  rw [hC3] at hle
  omega

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, FOR EVERY `k`, WITH THE CONSTANT `2`.**  If every odd
cycle of `G` meets a fixed triangle `C` in at least two vertices, then `G` is `2`-close to bipartite.

The hypothesis is structural — it counts nothing and bounds no size, no degree and no girth — and,
exactly as in `JSP90.erdos73On_of_edgeCount`, Erdős's hypothesis is not needed for the conclusion;
`LocIndep k G` is carried only so that the statement has the shape of an instance. -/
theorem erdos73On_of_triangle_of_oddCycles_meet_two {k : ℕ} (hG : LocIndep k G) {C : Finset V}
    (hC : IsOddCycle G C) (hC3 : C.card = 3)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → 2 ≤ (D ∩ C).card) : CloseToBipartite 2 G :=
  closeToBipartite_two_of_oddCycles_meet_two hC hC3 hmeet

end MeetTwo

end
end JSP90
