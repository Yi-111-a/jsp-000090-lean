/-
# JSP-000090 — the ODD CACTUS axis: sharpness, and the necessity of the two-Helly hypothesis

Attack family 28, companion to `JSPProblem/Cactus.lean` (round 81).  This file is the **finite**
half: the witnesses that make the statements of `JSPProblem/Cactus.lean` sharp, and the
machine-checked obstruction showing that its hypothesis cannot be weakened.

## What is proved

1. **THE CONSTANT `1` OF `JSP90.closeToBipartite_one_of_oddCactus_of_locIndep_one` IS ATTAINED.**
   `K₃` is an `OddCactus` graph (`JSP90.oddCactus_completeGraph_three`; every odd cycle of `K₃` is
   the whole vertex set, so the class conditions are vacuous there), it satisfies
   `LocIndep 1` (`JSP90.locIndep_one_completeGraph_three` = `JSP90.completeGraph_locIndep 1`), and it
   is **not** bipartite (`JSP90.not_closeToBipartite_zero_completeGraph_three`).  So the `k = 1` value
   of `f` on the class `OddCactus` is exactly `1` — the smallest value possible for a graph with an
   odd cycle.  (By contrast the constant `2` of `JSPProblem/Cover.lean`, whose class
   `ShareCycleEdge` is a different one, is attained by the nine-vertex graph `p9`.)

2. **THE CLASS IS NON-TRIVIAL AND CONTAINS ROUND 39's SHARP WITNESS.**
   `JSP90.oddCactus_kTriangles : ∀ k, OddCactus (kTriangles k)`, from the already-proved
   `JSP90.oddCyclesDisjoint_kTriangles`; and `kTriangles k` has odd cycle transversal number exactly
   `k` (`JSPProblem/Sharp.lean`), so the class is attained.

3. **THE TWO-HELLY HYPOTHESIS IS NECESSARY: THE 3-SUN.**  `sun3` is the graph on six vertices
   consisting of a triangle `0 – 2 – 5` with a degree-2 vertex hung on each of its three edges
   (`1` on `0 – 2`, `3` on `2 – 5`, `4` on `0 – 5`).  It satisfies `LocIndep 1`
   (`JSP90.locIndep_one_sun3`, exhaustive decision over the `64` vertex sets), and it is **not** one
   vertex away from bipartite (`JSP90.not_closeToBipartite_one_sun3`: for every vertex there is one
   of the four triangles avoiding it).  Yet its three "peripheral" triangles `T₁ = {0,1,2}`,
   `T₂ = {2,3,5}`, `T₃ = {0,4,5}` pairwise meet in three distinct vertices with empty triple
   intersection — a **ring** — so `sun3` is neither two-Helly nor even linear
   (`JSP90.not_oddCactus_sun3`, `JSP90.not_linear_sun3`).  This is the machine-checked justification
   for cutting the class of `JSPProblem/Cactus.lean` exactly where it is cut, and it is the
   computational reason the naive "`LocIndep 1` implies one vertex from bipartite" statement is
   false.

`#print axioms` on all of these shows only `[propext, Classical.choice, Quot.sound]`.
-/
import JSPProblem.Cactus

namespace JSP90

open Finset Fintype Set

noncomputable section

/-! ## Part 1 — `K₃` attains the constant `1` -/

/-- **Every odd cycle of `K₃` is the whole vertex set.**  An odd cycle of `K₃` has odd length `≥ 3`
and at most `|V| = 3` vertices, so it has exactly three, and there is only one three-element set. -/
theorem eq_univ_of_oddCycle_completeGraph_three {D : Finset (Fin 3)}
    (hD : IsOddCycle (SimpleGraph.completeGraph (Fin 3)) D) :
    D = (Finset.univ : Finset (Fin 3)) := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  have hcard : D.card = m := card_eq_cyclicOrder f hinj hmem
  have hle : D.card ≤ 3 := by
    refine le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
  rw [hcard] at hle
  have hm3' : m = 3 := by omega
  exact Finset.eq_univ_of_card D (hcard.trans hm3')

/-- **`K₃` IS AN ODD CACTUS.**  Both halves are vacuous there: there is only one odd cycle, namely the
whole vertex set, so no two *distinct* odd cycles meet at all, and three pairwise meeting odd cycles
must be that one cycle. -/
theorem oddCactus_completeGraph_three : OddCactus (SimpleGraph.completeGraph (Fin 3)) := by
  refine ⟨?_, ?_⟩
  · intro C D hC hD hne
    have h1 := eq_univ_of_oddCycle_completeGraph_three hC
    have h2 := eq_univ_of_oddCycle_completeGraph_three hD
    rw [h1, h2] at hne
    exfalso
    exact hne rfl
  · intro C D E hC hD hE hCD hDE hEC
    have h1 : C = (Finset.univ : Finset (Fin 3)) := eq_univ_of_oddCycle_completeGraph_three hC
    have h2 : D = (Finset.univ : Finset (Fin 3)) := eq_univ_of_oddCycle_completeGraph_three hD
    have h3 : E = (Finset.univ : Finset (Fin 3)) := eq_univ_of_oddCycle_completeGraph_three hE
    subst h1
    subst h2
    subst h3
    obtain ⟨v, hv⟩ := hC.nonempty
    exact exists_mem_inter3 (Finset.mem_univ v) (Finset.mem_univ v) (Finset.mem_univ v)

/-- **`LocIndep 1 (K₃)`**: the sharp witness of Part 1 is inside the range of the theorem. -/
theorem locIndep_one_completeGraph_three :
    LocIndep 1 (SimpleGraph.completeGraph (Fin 3)) :=
  completeGraph_locIndep 1

/-- **THE CONSTANT `1` IS ATTAINED: `K₃` IS AN ODD CACTUS, SATISFIES `LocIndep 1`, AND IS NOT
BIPARTITE.**  So on the class of `JSPProblem/Cactus.lean` the value of `f(1)` is exactly `1`. -/
theorem not_closeToBipartite_zero_completeGraph_three :
    ¬ CloseToBipartite 0 (SimpleGraph.completeGraph (Fin 3)) := by
  rw [closeToBipartite_iff_completeGraph_add_two 0 3]
  omega

/-! ## Part 2 — the class contains round 39's sharp witness -/

/-- **`kTriangles k` IS AN ODD CACTUS.**  Its odd cycles are the `k` disjoint triangles of
`JSPProblem/Sharp.lean`, which are pairwise vertex-disjoint
(`JSP90.oddCyclesDisjoint_kTriangles`), so both halves of the class are automatic.  Since the least
odd cycle transversal of `kTriangles k` is exactly `k`, the class is attained. -/
theorem oddCactus_kTriangles (k : ℕ) : OddCactus (kTriangles k) :=
  OddCactus.of_oddCyclesDisjoint (oddCyclesDisjoint_kTriangles (k := k))

/-! ## Part 3 — the 3-sun: the two-Helly hypothesis is necessary

Here a **computable** `DecidableEq` is needed, so this part is outside the classical section of
`JSPProblem/Cactus.lean`; the statements only mention `⊆`, element membership and `card`, so they
are the same statements in both. -/

/-- **The edge set of `sun3`, the 3-sun**: a triangle `0 – 2 – 5` with a degree-two vertex hung on
each of its three edges. -/
def sun3Edge : Finset (Fin 6 × Fin 6) :=
  {(0, 2), (2, 0), (2, 5), (5, 2), (0, 5), (5, 0), (0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2),
    (3, 5), (5, 3), (0, 4), (4, 0), (4, 5), (5, 4)}

theorem sun3Edge_symm : ∀ v w : Fin 6, (v, w) ∈ sun3Edge ↔ (w, v) ∈ sun3Edge := by decide

theorem sun3Edge_irrefl : ∀ v : Fin 6, (v, v) ∉ sun3Edge := by decide

/-- **`sun3`, the 3-sun.** -/
def sun3 : SimpleGraph (Fin 6) where
  Adj v w := (v, w) ∈ sun3Edge
  symm := ⟨fun _ _ h => (sun3Edge_symm _ _).mp h⟩
  loopless := ⟨fun _ h => (sun3Edge_irrefl _ h)⟩

@[simp] theorem sun3_adj {v w : Fin 6} : sun3.Adj v w ↔ (v, w) ∈ sun3Edge := Iff.rfl

/-- Adjacency of `sun3` is decidable: this is what makes the finite checks below kernel
computations. -/
local instance : DecidableRel sun3.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ sun3Edge))

/-- A cyclic ordering of three vertices. -/
def cyc3 (a b c : Fin 6) : Fin 3 → Fin 6 := fun j =>
  match j.val with
  | 0 => a | 1 => b | _ => c

/-- The central triangle `0 – 2 – 5`. -/
def T0 : Finset (Fin 6) := {0, 2, 5}
/-- The triangle on the edge `0 – 2`. -/
def T1 : Finset (Fin 6) := {0, 1, 2}
/-- The triangle on the edge `2 – 5`. -/
def T2 : Finset (Fin 6) := {2, 3, 5}
/-- The triangle on the edge `0 – 5`. -/
def T3 : Finset (Fin 6) := {0, 4, 5}

theorem mem_T0 : ∀ x : Fin 6, x ∈ T0 ↔ ∃ j : Fin 3, cyc3 0 2 5 j = x := by decide
theorem mem_T1 : ∀ x : Fin 6, x ∈ T1 ↔ ∃ j : Fin 3, cyc3 0 1 2 j = x := by decide
theorem mem_T2 : ∀ x : Fin 6, x ∈ T2 ↔ ∃ j : Fin 3, cyc3 2 3 5 j = x := by decide
theorem mem_T3 : ∀ x : Fin 6, x ∈ T3 ↔ ∃ j : Fin 3, cyc3 0 4 5 j = x := by decide

theorem isOddCycle_T0 : IsOddCycle sun3 T0 := ⟨3, cyc3 0 2 5, by decide, by decide, by decide,
  by decide, mem_T0⟩

theorem isOddCycle_T1 : IsOddCycle sun3 T1 := ⟨3, cyc3 0 1 2, by decide, by decide, by decide,
  by decide, mem_T1⟩

theorem isOddCycle_T2 : IsOddCycle sun3 T2 := ⟨3, cyc3 2 3 5, by decide, by decide, by decide,
  by decide, mem_T2⟩

theorem isOddCycle_T3 : IsOddCycle sun3 T3 := ⟨3, cyc3 0 4 5, by decide, by decide, by decide,
  by decide, mem_T3⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- **`LocIndep 1 sun3`**: the maximum deficiency of the 3-sun is at most one, by exhaustive decision
over its `64` vertex sets. -/
theorem locIndep_one_sun3 : LocIndep 1 sun3 := by
  unfold LocIndep
  decide

/-- Every vertex of `sun3` is avoided by one of the four triangles. -/
theorem sun3_oddCycle_av (v : Fin 6) : ∃ C : Finset (Fin 6), IsOddCycle sun3 C ∧ v ∉ C := by
  fin_cases v
  · exact ⟨T2, isOddCycle_T2, by decide⟩
  · exact ⟨T0, isOddCycle_T0, by decide⟩
  · exact ⟨T3, isOddCycle_T3, by decide⟩
  · exact ⟨T0, isOddCycle_T0, by decide⟩
  · exact ⟨T0, isOddCycle_T0, by decide⟩
  · exact ⟨T1, isOddCycle_T1, by decide⟩

/-- **THE RESIDUE OF `sun3` AT ANY SINGLE VERTEX STILL CARRIES AN ODD CYCLE** — the witness behind
`JSP90.not_closeToBipartite_one_sun3`. -/
theorem sun3_oddCycle_delete_av (v : Fin 6) :
    ∃ C : Finset (Fin 6), IsOddCycle (deleteFinset sun3 {v}) C := by
  obtain ⟨C, hC, hnot⟩ := sun3_oddCycle_av v
  exact exists_oddCycle_deleteFinset hC hnot

/-- **THE LEAST ODD CYCLE TRANSVERSAL OF THE 3-SUN IS EXACTLY `2`.**  So `LocIndep 1` does *not* by
itself imply one vertex from bipartite, and the 3-sun is a six-vertex witness for the lower bound
`f(1) ≥ 2` of `JSPProblem/Petersen.lean` (which uses the nine-vertex graph `p9`). -/
theorem not_closeToBipartite_one_sun3 : ¬ CloseToBipartite 1 sun3 := by
  rintro ⟨X, hX, hb⟩
  by_cases hX0 : X = ∅
  · rw [hX0, deleteFinset_empty] at hb
    exact not_isOddCycle_of_isBipartite hb ⟨T0, isOddCycle_T0⟩
  · have hXne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hX0
    have hXpos : 0 < X.card := Finset.card_pos.mpr hXne
    have hXeq : X.card = 1 := Nat.le_antisymm hX (by omega)
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hXeq
    obtain ⟨C, hC⟩ := sun3_oddCycle_delete_av a
    exact not_isOddCycle_of_isBipartite hb ⟨C, hC⟩

/-- **NO VERTEX LIES IN ALL THREE PERIPHERAL TRIANGLES** — the statement of the ring of the 3-sun,
phrased with element memberships only. -/
theorem not_common_T1_T2_T3 : ¬ ∃ v : Fin 6, v ∈ T1 ∧ v ∈ T2 ∧ v ∈ T3 := by decide

/-- **THE THREE PERIPHERAL TRIANGLES OF THE 3-SUN ARE A RING**: they pairwise meet in three distinct
vertices (`2`, `5`, `0`) and have empty triple intersection.  This is the obstruction to the class of
`JSPProblem/Cactus.lean`, and it is exactly the configuration the missing ring lemma
(`JSP90.LinearRing`) rules out in a linear graph. -/
theorem not_twoHelly_sun3 : ¬ TwoHellyOddCycles sun3 := by
  rintro h
  obtain ⟨v, hv⟩ := twoHelly_of_three_ne h isOddCycle_T1 isOddCycle_T2 isOddCycle_T3
    (show (2 : Fin 6) ∈ T1 by decide) (show (2 : Fin 6) ∈ T2 by decide)
    (show (5 : Fin 6) ∈ T2 by decide) (show (5 : Fin 6) ∈ T3 by decide)
    (show (0 : Fin 6) ∈ T3 by decide) (show (0 : Fin 6) ∈ T1 by decide)
  obtain ⟨h1, h2, h3⟩ := mem_of_mem_inter3 hv
  exact absurd ⟨v, h1, h2, h3⟩ not_common_T1_T2_T3

/-- **THE 3-SUN IS NOT EVEN LINEAR**: the peripheral triangle `T₁` and the central triangle `T₀` meet
in the two vertices `0` and `2`. -/
theorem not_linear_sun3 : ¬ LinearOddCycles sun3 := by
  rintro h
  exact not_linear_of_two_mem h isOddCycle_T1 isOddCycle_T0 (by decide)
    (show (0 : Fin 6) ∈ T1 by decide) (show (0 : Fin 6) ∈ T0 by decide)
    (show (2 : Fin 6) ∈ T1 by decide) (show (2 : Fin 6) ∈ T0 by decide) (by decide)

/-- **THE 3-SUN IS NOT AN ODD CACTUS.**  Together with `JSP90.locIndep_one_sun3` and
`JSP90.not_closeToBipartite_one_sun3` this says the two-Helly hypothesis of
`JSP90.closeToBipartite_one_of_oddCactus_of_locIndep_one` cannot be dropped: it is satisfied by every
graph of `LocIndep 1` **except** for those containing a ring of three odd cycles. -/
theorem not_oddCactus_sun3 : ¬ OddCactus sun3 := fun h => not_twoHelly_sun3 h.2

end

end JSP90
