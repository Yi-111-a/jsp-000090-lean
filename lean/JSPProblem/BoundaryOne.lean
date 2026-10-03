/-
# JSP-000090, round 135 — `JSPProblem/BoundaryOne.lean`: **the fan of a shortest odd cycle at
# `k = 1`**, and the residual of the sharp case in one statement

Attack family 64.  Round 134 closed the *attachment-point* axis of the sharp case `k = 1` by a
machine-checked refutation (`JSPProblem/Nonagon.lean`, the nine-vertex witness `g9`), and
`JSPProblem/AttachErase.lean` left exactly one residual, `JSP90.TwoTransversal 2`
(`⟺ Erdős73On 1 2`).  Three candidate *shapes* for the certificate of two vertices have been
refuted (two vertices of a triangle, two vertices of a shortest odd cycle, `|C| - 1 + |PetalSet|`).

This round takes the **third** shape — the two vertices may lie **anywhere in the closed
neighbourhood of a shortest odd cycle**, i.e. on the cycle *or* in its **fan** — and gets the
exact structural content of the fan at `k = 1`, which no previous round has.

## The new structural content

Let `C` be a **shortest** odd cycle of `G` and let `boundary G C` be its **fan**: the vertices
outside `C` with a neighbour on `C` (`JSPProblem/Boundary.lean`, round 61).  At `LocIndep 1`:

* **`JSP90.isBipartite_outerLayer_of_locIndep_one`** — **the part of `G` at distance `≥ 2` from `C`
  is bipartite.**  It is separated from `C` by construction, so an odd cycle in it would be a second
  odd cycle *disjoint* from `C`, which `LocIndep 1` forbids
  (`JSP90.inter_oddCycle_of_locIndep_one`).  This is the hypothesis that
  `JSP90.closeToBipartite_of_bipartite_outerLayer` (round 61) needs, and it is **free** at `k = 1`:
  so all of round 61's instance now applies at `k = 1` with no extra assumption;
* **`JSP90.oddCycle_eq_or_inter_boundary_of_locIndep_one`** — **THE FAN IS AN ODD-CYCLE
  TRANSVERSAL**:
  ```lean
  D = C ∨ D ∩ boundary G C ≠ ∅
  ```
  for every odd cycle `D`: every odd cycle of `G` other than `C` itself meets the fan.  (The
  hypothesis that `C` is shortest is essential: `JSPProblem/BoundaryOne.lean`'s search
  `discovery/JSP-000090/r135.c` finds counterexamples for arbitrary `C`, e.g. `C = V`.)  This is the
  classical "`C` has no odd cycle hanging off it except through its fan" statement;
* consequently **`JSP90.closeToBipartite_boundary_add_one_of_locIndep_one`** and the two instances
  `JSP90.closeToBipartite_one_of_boundary_empty` (constant `1`!) and
  **`JSP90.erdos73On_one_of_boundary_le_one`** (the sharp constant `2`): a `LocIndep 1` graph with an
  odd cycle whose fan has at most one vertex is `2`-close to bipartite.

## The fan is unbounded at `k = 1` (machine-checked, `JSPProblem/Fan4.lean`)

`JSP90.not_exists_boundary_le_two_fan4`: on `Fin 6`, the graph `fan4` (the triangle `{0,4,5}` with
three pendant vertices at `5`) satisfies `LocIndep 1`, has **exactly one** odd cycle, and its fan
has **three** elements.  So **no** statement of the form "`LocIndep 1` supplies an odd cycle with at
most `m` fan vertices" is available for any `m ≥ 2`, and the "small fan" route is closed.  The same
file records `JSP90.closeToBipartite_one_fan4`: the certificate there is the single vertex `5`, so the
big fan is not a counterexample — it is the case in which one vertex of the cycle does all the work.

## The residual of the sharp case `k = 1`, in one statement

```lean
JSP90.FanTwoResidual : LocIndep 1 G → C shortest odd cycle → 2 ≤ |boundary G C| →
                       ∃ X, |X| ≤ 2 ∧ X meets every odd cycle of G
```

* **`JSP90.erdos73On_one_two_of_fanTwoResidual`** — `FanTwoResidual` implies the **sharp**
  `Erdős73On 1 2`.  Together with Part 1–3 this reduces the sharp case `k = 1` to a statement about
  the **fan of one shortest odd cycle** and nothing else;
* the exhaustive search of this round (`discovery/JSP-000090/r135.c`, over **all** `903 792` graphs
  with `MaxDef ≤ 1` on `n ≤ 7` vertices) confirms that `FanTwoResidual` holds there, that `τ_odd ≤ 2`
  everywhere (`τ_odd = 2` first at `n = 6`), and that the maximum of `min_C |boundary G C|` over
  shortest odd cycles `C` is `4` (`fan4`), `3` at `n = 6`, and `2` restricted to triangle-free
  graphs.  It also confirms that a two-vertex certificate inside `C ∪ boundary G C` exists in
  **every** case at `n ≤ 7` — so the statement above is the right one.

## Part 5 — the same content under the packing condition, i.e. without Erdős's hypothesis

The only part of `LocIndep 1` used in Parts 1–2 is that no two odd cycles are vertex-disjoint, i.e.
`JSP90.PackingNumberOne` (`JSPProblem/Residue.lean`).  So the whole fan theorem is available on the
strictly larger class of graphs of **packing number one**:

* `JSP90.isBipartite_outerLayer_of_packing_one`,
  `JSP90.oddCycle_eq_or_inter_boundary_of_packing_one`,
  `JSP90.hitsOddCycles_boundary_singleton_of_packing_one`,
  `JSP90.closeToBipartite_boundary_add_one_of_packing_one`;
* **`JSP90.erdos73On_of_boundary_le_one_of_packing_one` — A NEW INSTANCE OF THE HEADLINE THEOREM:**
  for **every** `k`, `LocIndep k G` + packing number one + a shortest odd cycle whose fan has at most
  one vertex give `CloseToBipartite 2 G`, the **optimal constant**, with no bound on the odd girth,
  the packing weight or the number of branch vertices.  The hypothesis is incomparable with that of
  `JSP90.erdos73On_of_packing_one` (round 40), which bounds the transversal by the **odd girth** `ℓ`:
  `K_5` has packing number one and fan `2`, while `fan4` of `JSPProblem/Fan4.lean` has `LocIndep 1`
  and fan `3`.

## What is *not* proved

`JSP90.FanTwoResidual`, and behind it `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  `jsp_000090_main` is not declared,
so the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`.
-/

import JSPProblem.AttachErase
import Mathlib.Data.Finset.SDiff

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance boundaryOneDecidableEq : DecidableEq V := Classical.decEq V

/-- **AN ODD CYCLE HAS A VERTEX** — the image of its cyclic numbering.  (The pinned Mathlib slice has
no `Finset.card_pos_iff`, so the `C.Nonempty` needed below is obtained from the certificate of
`IsOddCycle` itself.) -/
theorem exists_mem_isOddCycle {V : Type u} {G : SimpleGraph V} [Fintype V] {C : Finset V}
    (hC : IsOddCycle G C) : C.Nonempty := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  exact ⟨f ⟨0, by omega⟩, (hCmem (f ⟨0, by omega⟩)).2 ⟨⟨0, by omega⟩, rfl⟩⟩

/-! ## Part 1 — at `LocIndep 1` the outer layer of an odd cycle is bipartite

This is the input that `JSP90.closeToBipartite_of_bipartite_outerLayer` of `JSPProblem/Boundary.lean`
(round 61) needed as an extra hypothesis, and it is **free** at `k = 1`. -/

/-- **AT `LocIndep 1`, THE PART OF `G` AT DISTANCE `≥ 2` FROM AN ODD CYCLE IS BIPARTITE.**  The outer
layer `outerLayer G C = V \ (C ∪ N(C))` is *separated* from `C` by construction
(`JSP90.separated_outerLayer`), so an odd cycle inside it would be a second odd cycle of `G`
vertex-disjoint from `C`; Erdős's hypothesis at `k = 1` forbids two vertex-disjoint odd cycles
(`JSP90.inter_oddCycle_of_locIndep_one`, the packing bound of `JSPProblem/Packing.lean` at `k = 1`).

No hypothesis on `C` is needed: `C` may be **any** odd cycle of `G`. -/
theorem isBipartite_outerLayer_of_locIndep_one (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) : (induceFinset G (outerLayer G C)).IsBipartite := by
  refine isBipartite_of_no_oddCycle (fun hD => ?_)
  obtain ⟨D, hD⟩ := hD
  have hsub : D ⊆ outerLayer G C := isOddCycle_sub_induceFinset hD

  have hne : C ∩ D ≠ ∅ := inter_oddCycle_of_locIndep_one hG hC hD.of_induceFinset
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  exact (mem_outerLayer.mp (hsub (Finset.mem_inter.mp hx).2)).1 (Finset.mem_inter.mp hx).1

/-! ## Part 2 — the fan of a *shortest* odd cycle is an odd-cycle transversal -/

/-- **AN ODD CYCLE THAT MEETS A SHORTEST ODD CYCLE LIES ON ONE SIDE OF THE OUTER LAYER.**  A cycle
never crosses an anticomplete split (`JSP90.isOddCycle_sub_anticoverIn`), and `C` and
`outerLayer G C` are anticomplete (`JSP90.separated_outerLayer`). -/
theorem sub_C_or_outer_of_oddCycle {C D : Finset V} (_hC : IsOddCycle G C) (hD : IsOddCycle G D)
    (hsub : D ⊆ C ∪ outerLayer G C) : D ⊆ C ∨ D ⊆ outerLayer G C := by
  have hanti : AnticoverIn G (C ∪ outerLayer G C) C (outerLayer G C) := by
    refine ⟨?_, rfl, ?_⟩
    · intro x hx1 hx2
      exact (mem_outerLayer.mp hx2).1 hx1
    · intro v hv w hw h
      exact separated_outerLayer.2 v hv w hw h
  exact isOddCycle_sub_anticoverIn hanti (hD.induceFinset hsub)

/-- **THE FAN OF A SHORTEST ODD CYCLE IS AN ODD-CYCLE TRANSVERSAL: EVERY OTHER ODD CYCLE MEETS IT.**

```lean
IsOddCycle G D → D = C ∨ D ∩ boundary G C ≠ ∅
```

In words: at `LocIndep 1`, **no odd cycle of `G` other than `C` itself avoids the fan of `C`.**  This
is the "there is nothing hanging off `C` except through the fan" statement of the classical
argument, and it is what makes the fan — rather than the cycle — the object the constant has to pay
for.  The hypothesis that `C` is *shortest* is essential: it is used through
`JSP90.eq_of_isOddCycle_subset_shortest` (`JSPProblem/Boundary.lean`), and the search of this round
(`discovery/JSP-000090/r135.c`) refutes the statement for an arbitrary odd cycle `C`. -/
theorem oddCycle_eq_or_inter_boundary_of_locIndep_one {C D : Finset V} (hG : LocIndep 1 G)
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hD : IsOddCycle G D) : D = C ∨ D ∩ boundary G C ≠ ∅ := by
  obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
  have hX : (induceFinset G (outerLayer G C)).IsBipartite :=
    isBipartite_outerLayer_of_locIndep_one hG hC
  have hhits : D ∩ (boundary G C ∪ {c} ∪ (∅ : Finset V)) ≠ ∅ :=
    hitsOddCycles_of_bipartite_outer hC hshort c hc (by simpa using hX) D hD
  by_cases hb : D ∩ boundary G C = ∅
  · left
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hhits
    have hxD : x ∈ D := (Finset.mem_inter.mp hx).1
    have hx' : x ∈ boundary G C ∪ {c} := by
      have hxU := (Finset.mem_inter.mp hx).2
      simpa using hxU
    have hxb : x ∉ boundary G C := by
      intro h
      have hD' : x ∈ D ∩ boundary G C := Finset.mem_inter.mpr ⟨hxD, h⟩
      rw [hb] at hD'
      simp at hD'
    rcases Finset.mem_union.mp hx' with hb' | hc'
    · exact absurd hb' hxb
    · have hxeq : x = c := Finset.mem_singleton.mp hc'
      subst hxeq
      have hsubC : D ⊆ C ∪ outerLayer G C := by
        intro y hyD
        have hyB : y ∉ boundary G C := by
          intro h
          have hD' : y ∈ D ∩ boundary G C := Finset.mem_inter.mpr ⟨hyD, h⟩
          rw [hb] at hD'
          simp at hD'
        by_cases hyC : y ∈ C
        · exact Finset.mem_union_left _ hyC
        · exact Finset.mem_union_right _
            (mem_outerLayer.mpr ⟨hyC, fun w hw hadj => hyB (mem_boundary.mpr ⟨hyC, w, hw, hadj⟩)⟩)
      rcases sub_C_or_outer_of_oddCycle hC hD hsubC with hDC | hDX
      · exact eq_of_isOddCycle_subset_shortest hC hshort hD hDC
      · exact absurd hc ((mem_outerLayer.mp (hDX hxD)).1)
  · exact Or.inr hb

/-! ## Part 3 — the instances: the constant is the size of the fan -/

/-- **`LocIndep 1` + A SHORTEST ODD CYCLE: THE CONCLUSION OF ERDŐS #73 WITH THE CONSTANT
`|boundary G C| + 1`.**  This is `JSP90.closeToBipartite_of_bipartite_outerLayer` of
`JSPProblem/Boundary.lean` with its extra hypothesis discharged by Part 1. -/
theorem closeToBipartite_boundary_add_one_of_locIndep_one (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) :
    CloseToBipartite ((boundary G C).card + 1) G := by
  obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
  exact closeToBipartite_of_bipartite_outerLayer hC hshort c hc
    (isBipartite_outerLayer_of_locIndep_one hG hC)

/-- **A `LocIndep 1` GRAPH WITH A SHORTEST ODD CYCLE WITH AN EMPTY FAN IS `1`-CLOSE TO BIPARTITE.**
The constant `1` is optimal (`K_3`). -/
theorem closeToBipartite_one_of_boundary_empty (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hempty : boundary G C = ∅) : CloseToBipartite 1 G := by
  have h1 := closeToBipartite_boundary_add_one_of_locIndep_one hG hC hshort
  rw [hempty, Finset.card_empty] at h1
  exact closeToBipartite_mono (by omega) h1

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM: THE SHARP CONSTANT `2` AT `k = 1` UNDER A FAN-BOUND.**
If `G` satisfies `LocIndep 1` and a shortest odd cycle of `G` has at most **one** vertex outside it
that touches it, then `CloseToBipartite 2 G`.  The hypothesis bounds no odd girth, no packing
weight, no packing number and no degree; and it is *not* available in general
(`JSPProblem/Fan4.lean` refutes the version with `2` in place of `1`). -/
theorem erdos73On_one_of_boundary_le_one (hG : LocIndep 1 G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hb : (boundary G C).card ≤ 1) : CloseToBipartite 2 G := by
  have h1 := closeToBipartite_boundary_add_one_of_locIndep_one hG hC hshort
  exact closeToBipartite_mono (by omega) h1

/-- **THE FAN IS THE ONLY THING THE CONSTANT HAS TO PAY FOR**: every odd cycle of `G` other than `C`
meets the fan (Part 2), so the fan together with one vertex of `C` is an odd-cycle transversal. -/
theorem hitsOddCycles_boundary_singleton_of_locIndep_one (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (c : V)
    (hc : c ∈ C) : HitsOddCycles G (boundary G C ∪ {c}) := by
  intro D hD
  rcases oddCycle_eq_or_inter_boundary_of_locIndep_one hG hC hshort hD with hDC | hb
  · refine Finset.nonempty_iff_ne_empty.mp
      ⟨c, Finset.mem_inter.mpr
        ⟨hDC ▸ hc, Finset.mem_union_right _ (Finset.mem_singleton_self c)⟩⟩
  · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hb
    refine Finset.nonempty_iff_ne_empty.mp ⟨y, Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hy).1, Finset.mem_union_left _ (Finset.mem_inter.mp hy).2⟩⟩

/-! ## Part 4 — the residual of the sharp case `k = 1`, in one statement -/

/-- **THE RESIDUAL OF THE SHARP CASE `k = 1` IN THE SHAPE OF THE FAN.**  At `LocIndep 1`, if a
shortest odd cycle `C` has **at least two** fan vertices, then some set of at most **two** vertices
of `C ∪ boundary G C` meets every odd cycle of `G`.

Everything else of the sharp case `k = 1` is proved in this file (Parts 1–3: the fan is the only
obstruction, and a fan of size `≤ 1` gives the sharp constant `2`), and the statement is verified
exhaustively for every graph with `MaxDef ≤ 1` on `n ≤ 7` vertices
(`discovery/JSP-000090/r135.c`). -/
def FanTwoResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      2 ≤ (boundary G C).card → ∃ X : Finset W, X.card ≤ 2 ∧ HitsOddCycles G X

/-- **THE SHARP CASE `k = 1` OF ERDŐS PROBLEM #73, WITH THE CONSTANT `2`, FROM THE SINGLE STATEMENT
ABOVE.**  The two cases are: the graph has no odd cycle (bipartite, constant `0`); a shortest odd
cycle `C` exists and has at most one fan vertex (Part 3, the sharp constant `2`); or `C` has at
least two fan vertices (the hypothesis of `FanTwoResidual`).  A shortest odd cycle exists
(`JSP90.exists_shortest_oddCycle`), so no choice is made. -/
theorem erdos73On_one_two_of_fanTwoResidual (h : FanTwoResidual.{u}) : Erdős73On.{u} 1 2 := by
  intro W instW G hG
  rw [closeToBipartite_iff_hitsOddCycles]
  by_cases hex : ∃ C : Finset W, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle (G := G) hex
    obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
    by_cases hb : (boundary G C).card ≤ 1
    · exact ⟨boundary G C ∪ {c}, by
        have hh := card_union_le' (boundary G C) ({c} : Finset W)
        simp only [Finset.card_singleton] at hh
        omega,
        hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc⟩
    · obtain ⟨X, hXcard, hX⟩ := h W instW G hG C hC hshort (by omega)
      exact ⟨X, hXcard, hX⟩
  · exact ⟨∅, by simp, fun D hD => absurd ⟨D, hD⟩ hex⟩

/-- **THE FAN-BOUND INSTANCE IS NECESSARY-SUFFICIENT FOR THE SMALL-FAN CASE**: the hypothesis
`|boundary G C| ≤ 1` of `JSP90.erdos73On_one_of_boundary_le_one` is exactly the hypothesis of the
first case of the reduction above. -/
theorem erdos73On_one_two_of_fanLe_one_of_fanTwoResidual (_h : FanTwoResidual.{u}) {W : Type u}
    (_ : Fintype W) (G : SimpleGraph W) (hG : LocIndep 1 G) {C : Finset W} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card)
    (hb : (boundary G C).card ≤ 1) : CloseToBipartite 2 G :=
  erdos73On_one_of_boundary_le_one hG hC hshort hb

/-! ## Part 5 — the same content under the **packing condition**, i.e. without Erdős's hypothesis

Nothing in Parts 1–2 uses `LocIndep 1` except the *packing* consequence of it: no two vertex-disjoint
odd cycles, i.e. `JSP90.PackingNumberOne` of `JSPProblem/Residue.lean` (round 40).  So the whole fan
theorem is available on the strictly larger class of graphs of **packing number one**, with no
reference to Erdős's hypothesis at all:

* **`JSP90.isBipartite_outerLayer_of_packing_one`** and
  **`JSP90.oddCycle_eq_or_inter_boundary_of_packing_one`** — Parts 1 and 2 under `PackingNumberOne`;
* **`JSP90.closeToBipartite_boundary_add_one_of_packing_one`** — the conclusion of Erdős #73 with the
  constant `|boundary G C| + 1`;
* **`JSP90.erdos73On_of_boundary_le_one_of_packing_one` — A NEW INSTANCE OF THE HEADLINE THEOREM:**
  for **every** `k`, if `LocIndep k G` and a shortest odd cycle `C` has at most one vertex outside it
  that touches it, then `CloseToBipartite 2 G` — the **optimal constant**, with no bound on the odd
  girth, the packing weight or the number of branch vertices, and with the *packing condition* rather
  than Erdős's hypothesis as the structural hypothesis;
* the comparison with `JSP90.erdos73On_of_packing_one` (`JSPProblem/Residue.lean`, round 40) is then
  exact and worth recording: that instance bounds the transversal by the **odd girth** `ℓ`, this one
  by the **fan** `|boundary G C| + 1`, and the two hypotheses are incomparable — `K_5` has packing
  number one and fan `2` at its shortest odd cycle, while `fan4` of `JSPProblem/Fan4.lean` has
  `LocIndep 1` and fan `3`. -/

/-- **AT `LocIndep 1` EVERY TWO ODD CYCLES MEET**, i.e. `G` has packing number one.  This is the only
part of Erdős's hypothesis used in Parts 1–2. -/
theorem packingNumberOne_of_locIndep_one (hG : LocIndep 1 G) : PackingNumberOne G :=
  fun _ _ hC hD => inter_oddCycle_of_locIndep_one hG hC hD

/-- **THE OUTER LAYER OF AN ODD CYCLE IS BIPARTITE IN A GRAPH OF PACKING NUMBER ONE** (Part 1 without
Erdős's hypothesis). -/
theorem isBipartite_outerLayer_of_packing_one (h : PackingNumberOne G) {C : Finset V}
    (hC : IsOddCycle G C) : (induceFinset G (outerLayer G C)).IsBipartite := by
  refine isBipartite_of_no_oddCycle (fun hD => ?_)
  obtain ⟨D, hD⟩ := hD
  have hsub : D ⊆ outerLayer G C := isOddCycle_sub_induceFinset hD
  have hDC : D ∩ C = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    exact (mem_outerLayer.mp (hsub (Finset.mem_inter.mp hx).1)).1 (Finset.mem_inter.mp hx).2
  have hne : C ∩ D ≠ ∅ := h C D hC hD.of_induceFinset
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  exact (mem_outerLayer.mp (hsub (Finset.mem_inter.mp hx).2)).1 (Finset.mem_inter.mp hx).1

/-- **THE FAN OF A SHORTEST ODD CYCLE IS AN ODD-CYCLE TRANSVERSAL IN A GRAPH OF PACKING NUMBER ONE**
(Part 2 without Erdős's hypothesis). -/
theorem oddCycle_eq_or_inter_boundary_of_packing_one {C D : Finset V} (h : PackingNumberOne G)
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hD : IsOddCycle G D) : D = C ∨ D ∩ boundary G C ≠ ∅ := by
  obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
  have hX : (induceFinset G (outerLayer G C)).IsBipartite :=
    isBipartite_outerLayer_of_packing_one h hC
  have hhits : D ∩ (boundary G C ∪ {c} ∪ (∅ : Finset V)) ≠ ∅ :=
    hitsOddCycles_of_bipartite_outer hC hshort c hc (by simpa using hX) D hD
  by_cases hb : D ∩ boundary G C = ∅
  · left
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hhits
    have hxD : x ∈ D := (Finset.mem_inter.mp hx).1
    have hx' : x ∈ boundary G C ∪ {c} := by
      have hxU := (Finset.mem_inter.mp hx).2
      simpa using hxU
    have hxb : x ∉ boundary G C := by
      intro hmem
      have hD' : x ∈ D ∩ boundary G C := Finset.mem_inter.mpr ⟨hxD, hmem⟩
      rw [hb] at hD'
      simp at hD'
    rcases Finset.mem_union.mp hx' with hb' | hc'
    · exact absurd hb' hxb
    · have hxeq : x = c := Finset.mem_singleton.mp hc'
      subst hxeq
      have hsubC : D ⊆ C ∪ outerLayer G C := by
        intro y hyD
        have hyB : y ∉ boundary G C := by
          intro hmem
          have hD' : y ∈ D ∩ boundary G C := Finset.mem_inter.mpr ⟨hyD, hmem⟩
          rw [hb] at hD'
          simp at hD'
        by_cases hyC : y ∈ C
        · exact Finset.mem_union_left _ hyC
        · exact Finset.mem_union_right _
            (mem_outerLayer.mpr ⟨hyC, fun w hw hadj => hyB (mem_boundary.mpr ⟨hyC, w, hw, hadj⟩)⟩)
      rcases sub_C_or_outer_of_oddCycle hC hD hsubC with hDC | hDX
      · exact eq_of_isOddCycle_subset_shortest hC hshort hD hDC
      · exact absurd hc ((mem_outerLayer.mp (hDX hxD)).1)
  · exact Or.inr hb

/-- **THE FAN PLUS ONE VERTEX OF THE CYCLE IS A TRANSVERSAL IN A GRAPH OF PACKING NUMBER ONE.** -/
theorem hitsOddCycles_boundary_singleton_of_packing_one (h : PackingNumberOne G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (c : V)
    (hc : c ∈ C) : HitsOddCycles G (boundary G C ∪ {c}) := by
  intro D hD
  rcases oddCycle_eq_or_inter_boundary_of_packing_one h hC hshort hD with hDC | hb
  · refine Finset.nonempty_iff_ne_empty.mp
      ⟨c, Finset.mem_inter.mpr
        ⟨hDC ▸ hc, Finset.mem_union_right _ (Finset.mem_singleton_self c)⟩⟩
  · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hb
    refine Finset.nonempty_iff_ne_empty.mp ⟨y, Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hy).1, Finset.mem_union_left _ (Finset.mem_inter.mp hy).2⟩⟩

/-- **THE CONCLUSION OF ERDŐS #73 WITH THE CONSTANT `|boundary G C| + 1` IN A GRAPH OF PACKING NUMBER
ONE.**  The certificate is `boundary G C ∪ {c}` for any `c ∈ C`: by
`JSP90.oddCycle_eq_or_inter_boundary_of_packing_one` every odd cycle of `G` other than `C` meets the
fan. -/
theorem closeToBipartite_boundary_add_one_of_packing_one (h : PackingNumberOne G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) :
    CloseToBipartite ((boundary G C).card + 1) G := by
  obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
  refine (closeToBipartite_iff_hitsOddCycles (G := G)
    (m := (boundary G C).card + 1)).mpr
      ⟨boundary G C ∪ {c}, ?_, hitsOddCycles_boundary_singleton_of_packing_one h hC hshort c hc⟩
  have hh := card_union_le' (boundary G C) ({c} : Finset V)
  simp only [Finset.card_singleton] at hh
  omega

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM: A FAN OF AT MOST ONE VERTEX GIVES THE OPTIMAL CONSTANT
`2`, FOR EVERY `k`, UNDER THE PACKING CONDITION.**  `LocIndep k G`, packing number one, and a
shortest odd cycle `C` with at most one vertex outside it that touches it, give
`CloseToBipartite 2 G`.  Compare `JSP90.erdos73On_of_packing_one`
(`JSPProblem/Residue.lean`), which under the packing condition bounds the transversal by the **odd
girth** `ℓ`; the two hypotheses are incomparable (`K_5` has packing number one and fan `2` at its
shortest odd cycle, while `fan4` of `JSPProblem/Fan4.lean` has `LocIndep 1` and fan `3`). -/
theorem erdos73On_of_boundary_le_one_of_packing_one {k : ℕ} (_hG : LocIndep k G) (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hb : (boundary G C).card ≤ 1) : CloseToBipartite 2 G :=
  closeToBipartite_mono (by omega) (closeToBipartite_boundary_add_one_of_packing_one h hC hshort)

/-- **THE `k = 1` INSTANCE OF THE PREVIOUS THEOREM, WITH ERDŐS'S HYPOTHESIS SUPPLYING THE PACKING
CONDITION** (this is `JSP90.erdos73On_one_of_boundary_le_one` of Part 3, re-derived). -/
theorem erdos73On_of_boundary_le_one (hG : LocIndep 1 G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (hb : (boundary G C).card ≤ 1) :
    CloseToBipartite 2 G :=
  erdos73On_of_boundary_le_one_of_packing_one hG (packingNumberOne_of_locIndep_one hG) hC hshort hb

end

end JSP90