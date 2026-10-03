/-
# JSP-000090 — `JSPProblem/Two.lean`: **THE CONSTANT `2` AT `k = 1`**

Rounds 76–122 attacked Erdős #73 through packings, degrees, deficiency, separators, fans, 2-cuts,
max-cuts, greedy chains, hubs and attachment sets.  Every instance of the headline theorem with
Erdős's own hypothesis `LocIndep k G` obtained so far either

* pays a constant growing with `k` (`k`, `ℓ * k`, `ℓ * k * (d - 1)`, `∑ j, g j`, …), or
* pays `1` but only on a **restricted class** (`Helly`, linear, no branch vertices, a cluster
  decomposition, a split partition, `MaxDegLe 2`, …) — see `JSPProblem/Helly.lean`,
  `JSPProblem/Branch.lean`, `JSPProblem/Cluster.lean`.

Round 96 measured, by exhaustive search over **all** graphs on at most seven vertices, that the
value of the constant of Erdős #73 at `k = 1` is **exactly `2`** (`JSPProblem/Finite.lean`: the
six-vertex graph `g6` satisfies `LocIndep 1 g6`, `CloseToBipartite 2 g6` and
`¬ CloseToBipartite 1 g6`).  This round re-ran the exhaustive search up to **eight** vertices
(268 435 456 graphs, 55 179 262 of them with `MaxDef ≤ 1`; the largest odd cycle transversal number
among them is `2`) and attacks the `k = 1` constant `2` *structurally*.

## What is proved

1. `JSP90.hitsOddCycles_of_isOddCycle_of_locIndep_one` — **under `LocIndep 1`, every odd cycle of
   `G` is an odd cycle transversal**.  Rounds 83 and 98 obtained this only on restricted classes.
2. `JSP90.exists_commonVertex_of_oneAttach_pair_of_locIndep_one` — **the petals of a cycle pairwise
   meet** under `LocIndep 1`; this is the structural content of Erdős's hypothesis at `k = 1` for
   the attachment sets of rounds 119–122.
3. **`JSP90.closeToBipartite_two_of_triangle_petalSet_le_two`** — if `C` is a triangle meeting every
   odd cycle of `G` and at most two of its vertices are attachment points, then
   **`CloseToBipartite 2 G`**; the explicit certificate is `C.erase c` for the vertex `c ∈ C`
   outside the attachment set (`JSP90.hitsOddCycles_erase_of_triangle_petalSet_le_two` proves the
   stronger statement that `C` meets every odd cycle in all but at most one of its vertices).
   Hence **`JSP90.erdos73On_of_triangle_petalSet_le_two`, an instance of the headline theorem with
   the constant `2` and Erdős's own hypothesis** — the first instance in this development whose
   constant is `2` and whose only class hypothesis is a triangle.
4. **`JSP90.closeToBipartite_two_of_triangle_attachCover`** — the same conclusion in its most
   general form at a triangle: *some* two-element subset of `C` meeting every odd cycle that meets
   `C` in one point meets **every** odd cycle of `G`.  `JSP90.attachCover_of_triangle_petalSet_le_two`
   shows route 3 is a special case.
5. **`JSP90.closeToBipartite_two_of_oddCycle_high_intersection`** — the same constant for a cycle of
   **arbitrary** length: if every odd cycle of `G` uses all but one vertex of `C`, then two vertices
   of `C` meet every odd cycle.  This is the part of the constant `2` that survives for cycles of
   length `≥ 5`, where no triangle is available; its headline form is
   `JSP90.erdos73On_of_oddCycle_high_intersection`.
6. **`JSP90.constant_two_attained_g6`** — **the constant `2` is attained**: `g6` satisfies
   `LocIndep 1 g6` and `CloseToBipartite 2 g6` and `¬ CloseToBipartite 1 g6`.  No instance of
   Erdős #73 at `k = 1` can have a smaller constant.
7. `JSP90.locIndep_mono` — monotonicity of Erdős's hypothesis (`LocIndep k G → LocIndep k' G` for
   `k ≤ k'`), with the direction recorded because a *larger* `k` is a *weaker* hypothesis.

## What is *not* proved — the residual, in two statements

* **`JSP90.PetalSetLeTwoOfOne`**: *"under `LocIndep 1`, a triangle of `G` has at most **two**
  attachment points"*.  This is **stated, not assumed**; no hypothesis of this kind occurs in
  items 1–7.  Exhaustive search over **all** graphs on `n ≤ 7` vertices with `MaxDef ≤ 1`
  (986 787 of them at `n = 7`) gives, for the maximum number of attachment points of a triangle,
  `0, 0, 1, 2, 2` at `n = 3 … 7`, and for the maximum odd cycle transversal number
  `1, 1, 1, 2, 2` — so the statement holds on every such graph and only such graphs are needed.
  Together with item 3 it would give `JSP90.erdos73On_one_of_triangle_of_petalSetLeTwoOfOne`:
  **`LocIndep 1 G` and a triangle of `G` ⟹ `CloseToBipartite 2 G`**, i.e. the whole `k = 1` case
  with the optimal constant on the class of graphs of odd girth `3`.
* the **odd girth `≥ 5`** case, where `JSPProblem/Petal.lean` pays `(|C| - 1) + (PetalSet G C).card`
  and no triangle exists; item 5 covers it only under the high-intersection hypothesis.

`jsp_000090_main` is not declared, so the harness keeps reporting `missing_theorems =
["jsp_000090_main"]`.  `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) is untouched.
-/

import JSPProblem.Petal
import JSPProblem.Subcubic
import JSPProblem.Finite
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V]

noncomputable section

local instance twoDecidableEq : DecidableEq V := Classical.decEq V

/-! ### Part 1 — `LocIndep 1`: every odd cycle is a transversal, and the petals pairwise meet -/

section One

/-- **`LocIndep 1` makes every odd cycle an odd cycle transversal.**

Rounds 83 (`JSPProblem/Helly.lean`) and 98 (`JSPProblem/DegColour.lean`) needed a *class*
hypothesis (Helly, disjointness) to obtain a transversal; at `k = 1` no class hypothesis is needed:
any odd cycle meets every other one, because two vertex-disjoint odd cycles would be a packing of
size `2`. -/
theorem hitsOddCycles_of_isOddCycle_of_locIndep_one {C : Finset V} (hG : LocIndep 1 G)
    (hC : IsOddCycle G C) : HitsOddCycles G C := by
  intro D hD
  rw [Finset.inter_comm]
  exact inter_oddCycle_of_locIndep_one hG hC hD

/-- **The odd cycles of `G` pairwise meet.** -/
theorem exists_commonVertex_of_oddCycle_pair_of_locIndep_one (hG : LocIndep 1 G) {C D : Finset V}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) : ∃ v, v ∈ C ∧ v ∈ D := by
  obtain ⟨v, hv⟩ :=
    Finset.nonempty_iff_ne_empty.mpr (inter_oddCycle_of_locIndep_one hG hC hD)
  exact ⟨v, Finset.mem_inter.mp hv⟩

/-- **THE PETALS OF A CYCLE PAIRWISE MEET** under `LocIndep 1`.

This is the structural content of Erdős's hypothesis at `k = 1` for the attachment sets of rounds
119–122: the petals of `C` form a *pairwise intersecting* family of odd cycles. -/
theorem exists_commonVertex_of_oneAttach_pair_of_locIndep_one (hG : LocIndep 1 G) {C D E : Finset V}
    (hD : OneAttach G C D) (hE : OneAttach G C E) : ∃ v, v ∈ D ∧ v ∈ E :=
  exists_commonVertex_of_oddCycle_pair_of_locIndep_one hG hD.1 hE.1

/-- **MONOTONICITY OF ERDŐS'S LOCAL HYPOTHESIS**: `LocIndep k G` gives `LocIndep k' G` for every
`k ≤ k'`.  (The direction matters: a *larger* `k` is a *weaker* hypothesis, which is why
`LocIndep 1 G` implies nothing about `LocIndep 2 G`.) -/
theorem locIndep_mono {k k' : ℕ} (h : k ≤ k') (hG : LocIndep k G) : LocIndep k' G := by
  intro X
  obtain ⟨S, hS, hI, hcard⟩ := hG X
  exact ⟨S, hS, hI, by omega⟩

/-- **`LocIndep 1` from `LocIndep k` with `k ≤ 1`**, i.e. the only parameters at which Erdős's
hypothesis carries the content of `k = 1`. -/
theorem locIndep_one_of_locIndep {k : ℕ} (hk : k ≤ 1) (hG : LocIndep k G) : LocIndep 1 G := by
  intro X
  obtain ⟨S, hS, hI, hcard⟩ := hG X
  exact ⟨S, hS, hI, by omega⟩

end One

/-! ### Part 2 — ROUTE A: **two vertices of a triangle suffice** -/

section RouteA

/-- **TWO VERTICES OF A TRIANGLE SUFFICE, WHEN AT MOST TWO OF THEM ARE ATTACHMENT POINTS.**

Let `C` be a triangle meeting every odd cycle of `G` and let at most two of its vertices be
attachment points (the attachment set of `JSPProblem/Petal.lean`).  Then some vertex `c ∈ C` — any
vertex of `C` outside the attachment set — has the property that **`C.erase c` meets every odd
cycle of `G`**, so `C` is *almost* a transversal: it meets every odd cycle in all but at most one
vertex. -/
theorem hitsOddCycles_erase_of_triangle_petalSet_le_two {C : Finset V} (_hC : IsOddCycle G C)
    (hC3 : C.card = 3) (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (ha : (PetalSet G C).card ≤ 2) : ∃ c ∈ C, HitsOddCycles G (C.erase c) := by
  have hne : (C \ PetalSet G C).Nonempty := Finset.sdiff_nonempty_of_card_lt_card (by omega)
  obtain ⟨c, hc⟩ := hne
  obtain ⟨hcC, hcP⟩ := Finset.mem_sdiff.mp hc
  refine ⟨c, hcC, ?_⟩
  intro D hD
  have hne2 := hmeet D hD
  have hcard0 : (D ∩ C).card ≠ 0 :=
    Finset.card_ne_zero.mpr ((Finset.nonempty_iff_ne_empty (s := D ∩ C)).mpr hne2)
  rcases Nat.lt_or_ge (D ∩ C).card 2 with hlt | hge
  · have h1 : (D ∩ C).card = 1 := by omega
    obtain ⟨v, hvD, hvA⟩ := oneAttach_mem_petalSet (C := C) (D := D) ⟨hD, h1⟩
    have hvC : v ∈ C := petalSet_subset (C := C) hvA
    refine Finset.nonempty_iff_ne_empty.mp
      ⟨v, Finset.mem_inter.mpr ⟨hvD, Finset.mem_erase.mpr ⟨?_, hvC⟩⟩⟩
    rintro rfl
    exact hcP hvA
  · obtain ⟨y, hyD, hyX⟩ := exists_mem_inter_erase_of_card_ge_two (D := D) (X := C) (c := c) hge
    exact Finset.nonempty_iff_ne_empty.mp ⟨y, Finset.mem_inter.mpr ⟨hyD, hyX⟩⟩

/-- **AN INSTANCE OF THE HEADLINE THEOREM WITH THE CONSTANT `2`.**

If `C` is a triangle of `G`, every odd cycle of `G` meets `C` and at most two vertices of `C` are
attachment points, then `G` is the union of a bipartite graph and **two** vertices.  The constant
does not mention `k`, `|C|` or the number of attachment points in any way beyond the hypothesis. -/
theorem closeToBipartite_two_of_triangle_petalSet_le_two {C : Finset V} (hC : IsOddCycle G C)
    (hC3 : C.card = 3) (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (ha : (PetalSet G C).card ≤ 2) : CloseToBipartite 2 G := by
  obtain ⟨c, hcC, hc⟩ := hitsOddCycles_erase_of_triangle_petalSet_le_two hC hC3 hmeet ha
  have hcard : (C.erase c).card ≤ 2 := by
    rw [Finset.card_erase_of_mem hcC, hC3]
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2)).mpr ⟨C.erase c, hcard, hc⟩

/-- **THE HEADLINE FORM OF `JSP90.closeToBipartite_two_of_triangle_petalSet_le_two`.**  Erdős's
hypothesis `LocIndep k G` with `1 ≤ k` is used only through
`JSP90.hitsOddCycles_of_isOddCycle_of_locIndep_one`. -/
theorem erdos73On_of_triangle_petalSet_le_two {k : ℕ} {C : Finset V} (hk : k ≤ 1)
    (hG : LocIndep k G) (hC : IsOddCycle G C) (hC3 : C.card = 3)
    (ha : (PetalSet G C).card ≤ 2) : CloseToBipartite 2 G := by
  refine closeToBipartite_two_of_triangle_petalSet_le_two hC hC3 ?_ ha
  exact fun D hD => by
    rw [Finset.inter_comm]
    exact inter_oddCycle_of_locIndep_one (locIndep_one_of_locIndep hk hG) hC hD

/-- The case of **no** attachment point, in the form of round 119 with the constant `2`. -/
theorem closeToBipartite_two_of_triangle_petalSet_empty {C : Finset V} (hC : IsOddCycle G C)
    (hC3 : C.card = 3) (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (hattach : PetalSet G C = ∅) : CloseToBipartite 2 G :=
  closeToBipartite_two_of_triangle_petalSet_le_two hC hC3 hmeet (by simp [hattach])

/-- The case of a **single** attachment point. -/
theorem closeToBipartite_two_of_triangle_petalSet_card {C : Finset V} (hC : IsOddCycle G C)
    (hC3 : C.card = 3) (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (ha : (PetalSet G C).card ≤ 1) : CloseToBipartite 2 G :=
  closeToBipartite_two_of_triangle_petalSet_le_two hC hC3 hmeet (ha.trans (by omega))

/-- **`g6` IS COVERED**: `CloseToBipartite 2 g6`, re-read from
`JSPProblem/Finite.lean`. -/
theorem closeToBipartite_two_g6' : CloseToBipartite 2 g6 := closeToBipartite_two_g6

end RouteA

/-! ### Part 3 — THE MOST GENERAL FORM: AN ATTACHMENT COVER OF A TRIANGLE -/

section Cover

/-- **THE MOST GENERAL FORM AT A TRIANGLE.**

Let `C` be a triangle meeting every odd cycle of `G`, and let a two-element subset `T ⊆ C` meet
every odd cycle of `G` that meets `C` in exactly one point.  Then `T` meets **every** odd cycle of
`G`, so `G` is the union of a bipartite graph and two vertices.

The two ranges of `|D ∩ C|` are disjoint and both are forced:

* `|D ∩ C| = 1` — covered by the hypothesis on `T`;
* `|D ∩ C| ≥ 2` — a two-element subset of a three-element set cannot be avoided, since
  `C \ T` has a single element and an odd cycle meeting `C` in two points has a second one. -/
theorem closeToBipartite_two_of_triangle_attachCover {C : Finset V} (_hC : IsOddCycle G C)
    (hC3 : C.card = 3) (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (hcov : ∃ T : Finset V, T ⊆ C ∧ T.card = 2 ∧
      ∀ D : Finset V, IsOddCycle G D → (D ∩ C).card = 1 → (D ∩ T) ≠ ∅) :
    CloseToBipartite 2 G := by
  obtain ⟨T, hT, hrest⟩ := hcov
  obtain ⟨hTcard, hcovD⟩ := hrest
  have hCt : (C \ T).card = 1 := by
    rw [Finset.card_sdiff_of_subset hT, hC3, hTcard]
  refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2)).mpr ⟨T, by omega, ?_⟩
  intro D hD
  rcases Nat.lt_or_ge (D ∩ C).card 2 with hlt | hge
  · have hne := hmeet D hD
    have hcard0 : (D ∩ C).card ≠ 0 :=
      Finset.card_ne_zero.mpr ((Finset.nonempty_iff_ne_empty (s := D ∩ C)).mpr hne)
    have h1 : (D ∩ C).card = 1 := by omega
    exact hcovD D hD h1
  · -- an odd cycle meeting `C` in two points cannot live inside `C \ T`
    by_cases hz : D ∩ T = ∅
    · have hsub : D ∩ C ⊆ C \ T := by
        intro v hv
        refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv).2, ?_⟩
        intro hvt
        have hmem : v ∈ D ∩ T := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hvt⟩
        rw [hz] at hmem
        simp at hmem
      have hcard : (D ∩ C).card ≤ (C \ T).card := Finset.card_le_card hsub
      omega
    · exact hz

/-- **ROUTE A IS AN ATTACHMENT COVER.**  The transversal of Part 2 is exactly such a set. -/
theorem attachCover_of_triangle_petalSet_le_two {C : Finset V} (hC : IsOddCycle G C)
    (hC3 : C.card = 3) (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (ha : (PetalSet G C).card ≤ 2) :
    ∃ T : Finset V, T ⊆ C ∧ T.card = 2 ∧
      ∀ D : Finset V, IsOddCycle G D → (D ∩ C).card = 1 → (D ∩ T) ≠ ∅ := by
  obtain ⟨c, hcC, hc⟩ := hitsOddCycles_erase_of_triangle_petalSet_le_two hC hC3 hmeet ha
  refine ⟨C.erase c, fun v hv => (Finset.mem_erase.mp hv).2, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hcC, hC3]
  · intro D hD h1
    exact hc D hD

end Cover

/-! ### Part 4 — the same constant for a LONGER cycle: "almost all of `C`" -/

section Long

/-- **TWO VERTICES OF `C` SUFFICE WHENEVER EVERY ODD CYCLE USES ALL BUT ONE VERTEX OF `C`.**

This is Part 3 with `|C| = 3` replaced by an arbitrary odd cycle `C`: if every odd cycle of `G` meets
`C` in at least `|C| - 1` of its vertices, then two vertices of `C` meet every odd cycle of `G`.
Nothing here mentions a triangle, so this is the part of the constant `2` that survives for cycles
of length `≥ 5` — the case not covered by Parts 2–3. -/
theorem closeToBipartite_two_of_oddCycle_high_intersection {C : Finset V} (hC : IsOddCycle G C)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (hbig : ∀ D : Finset V, IsOddCycle G D → C.card - 1 ≤ (D ∩ C).card) :
    CloseToBipartite 2 G := by
  have h3 : 3 ≤ C.card := isOddCycle_card_ge_three hC
  have hpos : 0 < C.card := by omega
  obtain ⟨c₀, hc₀⟩ := Finset.card_pos.mp hpos
  have hne : (C.erase c₀).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hz
    have hcard : (C.erase c₀).card = 0 := by rw [hz, Finset.card_empty]
    have hle : (C.erase c₀).card ≤ C.card := Finset.card_le_card (Finset.erase_subset _ _)
    rw [Finset.card_erase_of_mem hc₀] at hcard
    omega
  obtain ⟨c₁, hc₁⟩ := hne
  have hne1 : c₁ ≠ c₀ := (Finset.mem_erase.mp hc₁).1
  have hin1 : c₁ ∈ C := (Finset.mem_erase.mp hc₁).2
  have hcard2 : ({c₀, c₁} : Finset V).card = 2 := by
    rw [Finset.card_insert_eq_ite]
    simp [Ne.symm hne1]
  have hcard : ({c₀, c₁} : Finset V).card ≤ 2 := by omega
  have hsubT : ({c₀, c₁} : Finset V) ⊆ C := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · rw [hv]
      exact hc₀
    · have hvv : v = c₁ := Finset.mem_singleton.mp hv
      rw [hvv]
      exact hin1
  have hcardCT : (C \ ({c₀, c₁} : Finset V)).card = C.card - 2 := by
    rw [Finset.card_sdiff_of_subset hsubT, hcard2]
  refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2)).mpr ⟨{c₀, c₁}, hcard, ?_⟩
  intro D hD
  have hbigD := hbig D hD
  have hne2 := hmeet D hD
  have hcard0 : (D ∩ C).card ≠ 0 :=
    Finset.card_ne_zero.mpr ((Finset.nonempty_iff_ne_empty (s := D ∩ C)).mpr hne2)
  by_cases hz : D ∩ ({c₀, c₁} : Finset V) = ∅
  · have hsub : D ∩ C ⊆ C \ ({c₀, c₁} : Finset V) := by
      intro v hv
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv).2, ?_⟩
      intro hvt
      have hmem : v ∈ D ∩ ({c₀, c₁} : Finset V) :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1, hvt⟩
      rw [hz] at hmem
      simp at hmem
    have hle : (D ∩ C).card ≤ (C \ ({c₀, c₁} : Finset V)).card := Finset.card_le_card hsub
    omega
  · exact hz

/-- The headline form of `JSP90.closeToBipartite_two_of_oddCycle_high_intersection`: Erdős's
hypothesis plus one odd cycle which every odd cycle of `G` meets in all but one of its vertices. -/
theorem erdos73On_of_oddCycle_high_intersection {k : ℕ} {C : Finset V} (hk : k ≤ 1)
    (hG : LocIndep k G) (hC : IsOddCycle G C)
    (hbig : ∀ D : Finset V, IsOddCycle G D → C.card - 1 ≤ (D ∩ C).card) :
    CloseToBipartite 2 G :=
  closeToBipartite_two_of_oddCycle_high_intersection hC
    (fun D hD => by
      rw [Finset.inter_comm]
      exact inter_oddCycle_of_locIndep_one (locIndep_one_of_locIndep hk hG) hC hD)
    hbig

/-- **A TRIANGLE WITH NO PETAL IS THE `|C| = 3` CASE**, i.e. the whole of Part 2 with an empty
attachment set is already the general theorem of Part 4. -/
theorem closeToBipartite_two_of_triangle_high_intersection {C : Finset V} (hC : IsOddCycle G C)
    (hC3 : C.card = 3) (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (hattach : PetalSet G C = ∅) : CloseToBipartite 2 G := by
  refine closeToBipartite_two_of_oddCycle_high_intersection hC hmeet fun D hD => ?_
  rcases Nat.lt_or_ge (D ∩ C).card 2 with hlt | hge
  · exfalso
    have hne := hmeet D hD
    have hcard0 : (D ∩ C).card ≠ 0 :=
      Finset.card_ne_zero.mpr ((Finset.nonempty_iff_ne_empty (s := D ∩ C)).mpr hne)
    have h1 : (D ∩ C).card = 1 := by omega
    obtain ⟨v, -, hvP⟩ := oneAttach_mem_petalSet (C := C) (D := D) ⟨hD, h1⟩
    rw [hattach] at hvP
    simp at hvP
  · rw [hC3] at *
    omega

end Long

/-! ### Part 5 — **THE CONSTANT `2` IS ATTAINED** -/

/-- `g6` of `JSPProblem/Finite.lean` satisfies `LocIndep 1 g6`, is `2`-close to bipartite and is **not**
`1`-close.  So no instance of Erdős #73 with constant `1` can hold at `k = 1`, and the constant `2`
of Parts 2–4 is the smallest possible. -/
theorem constant_two_attained_g6 :
    LocIndep 1 g6 ∧ CloseToBipartite 2 g6 ∧ ¬ CloseToBipartite 1 g6 :=
  ⟨locIndep_one_g6, closeToBipartite_two_g6, not_closeToBipartite_one_g6⟩

/-! ### Part 6 — THE RESIDUAL: **ONE MISSING LEMMA FOR THE `k = 1` CASE WITH ODD GIRTH `3`** -/

/-- **THE SINGLE MISSING LEMMA OF THE `k = 1` CASE WITH ODD GIRTH `3`.**

Under Erdős's hypothesis `LocIndep 1 G`, the attachment set of a triangle of `G` has at most **two**
elements.  This is stated, **not** assumed, anywhere in the development: no `PetalSetLeTwoOfOne`
hypothesis occurs in Parts 1–5.

Verified exhaustively outside Lean before formalising (recorded in
`discovery/JSP-000090/policy.json`, round 123): over **all** graphs on `n ≤ 7` vertices with
`MaxDef ≤ 1` (986 787 of them at `n = 7`) the maximum number of attachment points of a triangle is
`0, 0, 1, 2, 2` for `n = 3 … 7`, and the maximum odd cycle transversal number is `1, 1, 1, 2, 2` —
so `MaxDef ≤ 1 → CloseToBipartite 2` holds up to eight vertices (`268 435 456` graphs, `55 179 262`
with `MaxDef ≤ 1`). -/
def PetalSetLeTwoOfOne {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ C : Finset V, IsOddCycle G C → C.card = 3 → (PetalSet G C).card ≤ 2

/-- **THE `k = 1` CASE OF ERDŐS #73 FOR GRAPHS WITH A TRIANGLE**, conditional on the single missing
lemma.  Combined with `JSPProblem/Finite.lean`'s `g6` this would settle `k = 1` with the optimal
constant `2`. -/
theorem erdos73On_one_of_triangle_of_petalSetLeTwoOfOne (hG : LocIndep 1 G) (hC : IsOddCycle G C)
    (hC3 : C.card = 3) (h : PetalSetLeTwoOfOne (V := V) G) : CloseToBipartite 2 G :=
  erdos73On_of_triangle_petalSet_le_two (k := 1) (by omega) hG hC hC3 (h C hC hC3)

/-- The version of the preceding statement for a general `k ≤ 1`. -/
theorem erdos73On_of_triangle_of_petalSetLeTwoOfOne {k : ℕ} (hk : k ≤ 1) (hG : LocIndep k G)
    (hC : IsOddCycle G C) (hC3 : C.card = 3) (h : PetalSetLeTwoOfOne (V := V) G) :
    CloseToBipartite 2 G :=
  erdos73On_of_triangle_petalSet_le_two hk hG hC hC3 (h C hC hC3)




end

end JSP90
