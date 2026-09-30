import JSPProblem.Subcubic
import JSPProblem.Petersen
import Mathlib.Tactic.FinCases

/-!
# JSP-000090, round 80 — the **SHARED-EDGE axis**: the odd-girth bound with no degree bound, the
# packing-number-one case of it, and a machine-checked refutation of the "two active edges suffice"
# plan of round 78

This is the **twenty-seventh attack family**.  Round 78 (`JSPProblem/Subcubic.lean`) proved that two
odd cycles of a graph of maximum degree `≤ 3` that meet **share a cycle edge** of the first
(`CycleOrder.exists_adj_mem_inter`), and used it to prove a new instance of the headline theorem,

> `closeToBipartite_of_subcubic_of_shortOddCycles : MaxDegLe G 3 → LocIndep k G → (odd girth ≤ ℓ) →
>   CloseToBipartite (k * ((ℓ + 1) / 2)) G`.

That instance carries a **degree** hypothesis.  Round 78's policy closed with a *plan* — "for a
shortest odd cycle `C` of a subcubic graph, the **active edges** (the edges of `C` lying in another odd
cycle) are covered by two vertices" — and **Part 4 of this file shows that plan to be false** by
machine check, and replaces it by the hypothesis the argument actually needs.

## Part 1 — the degree-free hypothesis `ShareCycleEdge`

`JSP90.ShareCycleEdge` says: *two odd cycles of `G` that meet share a cycle edge of the first*, in
every cyclic ordering of the first.  It is a purely **local intersection property**: no degree, no
girth, no packing.  `ShareCycleEdge.lemma_of_maxDegLe_three` derives it from subcubicity (round 78),
so the instances of Parts 2 and 3 **strictly generalise** round 78's: the degree bound is replaced by a
local property, and graphs of unbounded maximum degree enter the class.

## Part 2 — a NEW INSTANCE of the headline theorem, with no degree bound

> **`erdos73On_of_shareCycleEdge_of_shortOddCycles`**: `ShareCycleEdge G → LocIndep k G → (every odd
> cycle of `G` has at most `ℓ` vertices) → CloseToBipartite (k * ((ℓ + 1) / 2)) G`

with the constant of round 78 — itself better than the general `ℓ * k` of
`erdos73On_of_bounded_odd_girth` — under a strictly weaker hypothesis, and
`erdos73On_shareCycleEdge_of_three`, the `ℓ = 3` level `CloseToBipartite (2 * k) G`.

## Part 3 — the PACKING-NUMBER-ONE case, with **no local hypothesis at all**

> **`closeToBipartite_of_shareCycleEdge_of_packingOne`**: if **every two odd cycles of `G` meet**, then
> `CloseToBipartite ((ℓ + 1) / 2) G`, where `ℓ` bounds the length of the odd cycles.

Here Erdős's hypothesis does not occur: `LocIndep 1` enters, when it occurs at all, only through the
packing statement it implies (`inter_oddCycle_of_locIndep_one`).  The `ℓ = 3` level,

> **`closeToBipartite_of_shareCycleEdge_of_packingOne_of_three`**:

> *a graph whose odd cycles are all triangles, pairwise meet, and share a cycle edge whenever they
> meet, is `2`-close to bipartite*,

is a **new instance of the headline theorem on a class carrying no degree bound and no local
hypothesis**.  Its constant `2` is **sharp**: `K₄` satisfies the hypotheses and is not one vertex away
from bipartite (`not_closeToBipartite_one_K4`), and so is `p9` (`not_shareEdgePackingOne_one`).

## Part 4 — the ACTIVE EDGES of an odd cycle, and the refutation of round 78's plan

`ActiveEdges o` is the finset of **cycle edges** of `C` (in the cyclic ordering `o`) that lie in
another odd cycle of `G`.  By Part 1 every odd cycle of `G` meeting `C` contains one of them, so
`closeToBipartite_of_activeEdgeCover_of_shareCycleEdge` is the criterion round 78's plan aimed at:
*a vertex cover of the active edges of `C`, sitting inside `C`, is a transversal of the whole graph.*

In the Petersen graph with one vertex deleted (`JSP90.p9`: subcubic by `JSP90.maxDegLe_p9`, odd girth
`5` by `JSP90.card_ge_five_of_oddCycle_p9`, so `Cb` is a shortest odd cycle):

* **every** edge of `Cb` is active (`each_activeCb_active`: the five edges lie in `Ca`, `Ca`, `Cc`,
  `Cd`, `Cd`; and `ActiveEdges_oCb : ActiveEdges oCb = activeCb` puts the computation in the language
  of the definition);
* **no** set of at most two vertices of `Cb` covers them (`no_two_cover_activeCb`, a `decide` over all
  `3 ^ 9` subsets of the nine vertices), three are needed (`card_vertexCover_activeCb`) and three
  suffice (`exists_cover_activeCb_three`).

So **the vertex-cover number of the active edges of a shortest odd cycle of a subcubic graph is three,
not two** (`not_vertexCover_two_of_activeCb`): round 78's closing plan is refuted.  The `k = 1`
subcubic constant `2`, which *is* attained by `p9` (`closeToBipartite_two_p9`), therefore cannot be
obtained by covering the active edges of one odd cycle.

## Part 5 — the remaining statement, isolated and pinned down

`JSP90.ShareEdgePackingOne r`: *a graph in which two odd cycles that meet share a cycle edge, and whose
odd cycles pairwise meet, is `r`-close to bipartite.*  This drops **both** hypotheses that remain in
the `k = 1` subcubic case — the degree bound `MaxDegLe G 3` and the odd-girth bound — so it is a
**generalisation** of round 78's `JSP90.SubcubicPackingOne`, which is the special case of it on
subcubic graphs (`subcubicPackingOne_of_shareEdgePackingOne_two` is that special case, read in the
other direction).  Part 3 proves its base level for the graphs whose odd cycles are triangles, and
Part 4 pins the constant down:

> **`not_shareEdgePackingOne_one` — `¬ JSP90.ShareEdgePackingOne 1`, by machine check**: `p9` satisfies
> the hypotheses (`maxDegLe_p9`, hence `shareCycleEdge_p9`; `locIndep_one_p9`, hence every two of its
> odd cycles meet by `inter_oddCycle_of_locIndep_one`) and is not one vertex away from bipartite.

So `r = 2` is the sharp candidate, `p9` shows it cannot be lowered, and the statement is **not
assumed**: the only reduction out of it, `erdos73On_shareEdgePackingOne_one`, consumes it in the
direction that makes it the weaker target.

Nothing is assumed: `#print axioms` on the results below shows only `[propext, Classical.choice,
Quot.sound]`.
-/

namespace JSP90

open Finset Fintype Set

noncomputable section

universe u

/-! ## Parts 1–3 and 5 — the general statements

A *classical* `DecidableEq V` is installed in this section only: `Finset.inter` needs it, and the
finite checks of Part 4 need a *computable* one, so Part 4 lives outside this section. -/

section General

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

local instance instDecidableEqCover : DecidableEq V := Classical.decEq V

local instance instDecidableAdjCover : ∀ v w : V, Decidable (G.Adj v w) :=
  fun _ _ => Classical.propDecidable _

local instance instDecidableIsOddCycleCover {D : Finset V} : Decidable (IsOddCycle G D) :=
  Classical.propDecidable _

/-! ### Part 1 — the hypothesis: two meeting odd cycles share a cycle edge -/

/-- **TWO ODD CYCLES THAT MEET SHARE A CYCLE EDGE.**  In *every* cyclic ordering `o` of the odd cycle
`C`, two odd cycles `C`, `D` of `G` with `C ∩ D ≠ ∅` have two **consecutive** vertices of `o` inside
`D`.

This is a purely local property of the intersection pattern of the odd cycles of `G`: it mentions no
degree, no girth and no packing.  `JSP90.ShareCycleEdge.lemma_of_maxDegLe_three` below derives it from
subcubicity, so Parts 2 and 3 strictly generalise `JSP90.closeToBipartite_of_subcubic_of_shortOddCycles`
from a degree hypothesis to a local intersection hypothesis. -/
noncomputable def ShareCycleEdge (G : SimpleGraph V) : Prop :=
  ∀ C D : Finset V, IsOddCycle G C → IsOddCycle G D → C ∩ D ≠ ∅ →
    ∀ o : CycleOrder G C, ∃ i : Fin o.m, o.f i ∈ D ∧ o.f (cycSucc i) ∈ D

/-- **EVERY GRAPH OF MAXIMUM DEGREE `≤ 3` SATISFIES `ShareCycleEdge`.**  This is round 78's
`CycleOrder.exists_adj_mem_inter`, read as a statement about the graph rather than about one odd
cycle, so the hypothesis of Parts 2–5 is *weaker* than subcubicity. -/
theorem ShareCycleEdge.lemma_of_maxDegLe_three (hdeg : MaxDegLe G 3) : ShareCycleEdge G := by
  intro C D hC hD hmeet o
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hmeet
  obtain ⟨i, -, h1, h2⟩ := o.exists_adj_mem_inter hdeg hD hu
  exact ⟨i, h1, h2⟩

/-- **THE STRUCTURAL CONTENT OF THE HYPOTHESIS: two meeting odd cycles share at least two
vertices** — the degree-free version of round 78's `exists_ne_two_mem_inter_oddCycle`. -/
theorem exists_ne_two_mem_inter_of_shareCycleEdge (h : ShareCycleEdge G) {C D : Finset V}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) (hmeet : C ∩ D ≠ ∅) :
    ∃ a b : V, a ∈ C ∩ D ∧ b ∈ C ∩ D ∧ a ≠ b := by
  obtain ⟨o, _⟩ := hC.cycleOrder
  obtain ⟨i, h1, h2⟩ := h C D hC hD hmeet o
  refine ⟨o.f i, o.f (cycSucc i), Finset.mem_inter.mpr ⟨(o.hmem _).mpr ⟨i, rfl⟩, h1⟩,
    Finset.mem_inter.mpr ⟨(o.hmem _).mpr ⟨cycSucc i, rfl⟩, h2⟩, o.step_ne i⟩

/-! ### Part 2 — the even cover works under a local hypothesis: a new instance -/

/-- **THE EVEN COVER OF AN ODD CYCLE MEETS EVERY ODD CYCLE THAT MEETS IT** — under the hypothesis
`ShareCycleEdge`, in place of round 78's subcubicity.  This is the single lemma the rest of the file
rests on. -/
theorem inter_evenCover_of_shareCycleEdge (h : ShareCycleEdge G) {C D : Finset V}
    (hC : IsOddCycle G C) {o : CycleOrder G C} (hm : o.m % 2 = 1) (hD : IsOddCycle G D)
    (hmeet : C ∩ D ≠ ∅) : D ∩ evenCover o hm ≠ ∅ := by
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hmeet
  obtain ⟨i, h1, h2⟩ := h C D hC hD (Finset.ne_empty_of_mem hu) o
  rcases exists_mem_evenCover_of_cycleEdge (o := o) (hm := hm) i with hc | hc
  · exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨h1, hc⟩)
  · exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨h2, hc⟩)

/-- **THE EVEN COVER OF AN ODD CYCLE MEETS EVERY ODD CYCLE THAT MEETS IT**, phrased with
`JSP90.oddEvenCover` (the even cover of the *chosen* cyclic order of an odd cycle, `∅` otherwise). -/
theorem inter_oddEvenCover_of_shareCycleEdge (h : ShareCycleEdge G) {C D : Finset V}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) (hmeet : C ∩ D ≠ ∅) :
    D ∩ oddEvenCover G C ≠ ∅ := by
  rw [oddEvenCover, dif_pos hC]
  exact inter_evenCover_of_shareCycleEdge h hC (o := (hC.cycleOrder).choose)
    (hm := (hC.cycleOrder).choose_spec) hD hmeet

/-- **THE LOCAL VERSION OF ROUND 78'S SUBCUBIC TRANSVERSAL.**  If every odd cycle of `G` meets the odd
cycle `C`, then some subset of `C` of at most `(C.card + 1) / 2` vertices meets every odd cycle of
`G`. -/
theorem hitsOddCycles_of_inter_of_shareCycleEdge (h : ShareCycleEdge G) {C : Finset V}
    (hC : IsOddCycle G C) (hmeet : ∀ D, IsOddCycle G D → C ∩ D ≠ ∅) :
    ∃ Z : Finset V, Z.card ≤ (C.card + 1) / 2 ∧ HitsOddCycles G Z := by
  obtain ⟨o, hm⟩ := hC.cycleOrder
  refine ⟨evenCover o hm, card_evenCover (hm := hm), ?_⟩
  intro D hD
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr (hmeet D hD)
  exact inter_evenCover_of_shareCycleEdge h hC (o := o) (hm := hm) hD (Finset.ne_empty_of_mem hu)

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM: THE ODD-GIRTH BOUND WITHOUT A DEGREE BOUND.**

`ShareCycleEdge G`, `LocIndep k G` and *every odd cycle of `G` has at most `ℓ` vertices* give
`CloseToBipartite (k * ((ℓ + 1) / 2)) G`.

The constant is the one of round 78's `closeToBipartite_of_subcubic_of_shortOddCycles` — itself better
than the general `ℓ * k` of `JSP90.erdos73On_of_bounded_odd_girth` — while the hypothesis is strictly
weaker: `MaxDegLe G 3` is replaced by the local property `ShareCycleEdge G`, which graphs of unbounded
maximum degree may satisfy.  This is `JSP90.erdős73On k m` for the class "graphs whose odd cycles share
a cycle edge whenever they meet, of bounded odd girth". -/
theorem closeToBipartite_of_shareCycleEdge_of_shortOddCycles (k ℓ : ℕ) (hsh : ShareCycleEdge G)
    (hG : LocIndep k G) (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ) :
    CloseToBipartite (k * ((ℓ + 1) / 2)) G := by
  classical
  obtain ⟨P, hP, hmax⟩ := exists_maxCard_oddCycleFamily (G := G)
  have hPC : P.card ≤ k := hG.oddCycleFamily_card_le hP
  have htrans : HitsOddCycles G (P.biUnion (oddEvenCover G)) := by
    intro D hD
    have h1 : D ∩ (P.biUnion id) ≠ ∅ := hitsOddCycles_of_maxCardFamily hP hmax D hD
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr h1
    obtain ⟨hxD, hxU⟩ := Finset.mem_inter.mp hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxU
    have hne2 : D ∩ oddEvenCover G i ≠ ∅ :=
      inter_oddEvenCover_of_shareCycleEdge hsh (hP.2 i hi) hD
        (Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨hxi, hxD⟩))
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hne2
    obtain ⟨hyD, hycov⟩ := Finset.mem_inter.mp hy
    exact Finset.ne_empty_of_mem
      (Finset.mem_inter.mpr ⟨hyD, Finset.mem_biUnion.mpr ⟨i, hi, hycov⟩⟩)
  refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := k * ((ℓ + 1) / 2))).mpr
    ⟨P.biUnion (oddEvenCover G), ?_, htrans⟩
  calc (P.biUnion (oddEvenCover G)).card ≤ ∑ D ∈ P, (oddEvenCover G D).card := by
        exact Finset.card_biUnion_le (s := P) (t := oddEvenCover G)
    _ ≤ ∑ D ∈ P, (D.card + 1) / 2 := Finset.sum_le_sum fun D hD =>
        card_oddEvenCover_of_isOddCycle (hP.2 D hD)
    _ ≤ ∑ _D ∈ P, ((ℓ + 1) / 2) := Finset.sum_le_sum fun D hD =>
        div_add_one_mono (hlen D (hP.2 D hD))
    _ ≤ P.card * ((ℓ + 1) / 2) := sum_le_card_mul P ((ℓ + 1) / 2)
    _ ≤ k * ((ℓ + 1) / 2) := Nat.mul_le_mul_right _ hPC

/-- **THE SAME INSTANCE, WRITTEN AS AN INSTANCE OF ERDŐS #73.** -/
theorem erdos73On_of_shareCycleEdge_of_shortOddCycles (k ℓ : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W), ShareCycleEdge G → LocIndep k G →
      (∀ D, IsOddCycle G D → D.card ≤ ℓ) → CloseToBipartite (k * ((ℓ + 1) / 2)) G :=
  fun W instW G hsh hG hlen =>
    closeToBipartite_of_shareCycleEdge_of_shortOddCycles k ℓ hsh hG hlen

/-- **THE `k = 1` LEVEL OF THE NEW INSTANCE, AND THE CONSTANT DOES NOT MENTION `k`.** -/
theorem closeToBipartite_of_shareCycleEdge_of_shortOddCycle_one (ℓ : ℕ) (hsh : ShareCycleEdge G)
    (hG : LocIndep 1 G) (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ) :
    CloseToBipartite ((ℓ + 1) / 2) G := by
  have h := closeToBipartite_of_shareCycleEdge_of_shortOddCycles 1 ℓ hsh hG hlen
  simpa using h

/-- **THE `ℓ = 3` LEVEL: A GRAPH WHOSE ODD CYCLES ARE ALL TRIANGLES IS `2 k`-CLOSE TO BIPARTITE**,
under the degree-free hypothesis `ShareCycleEdge`. -/
theorem closeToBipartite_of_shareCycleEdge_of_three (k : ℕ) (hsh : ShareCycleEdge G)
    (hG : LocIndep k G) (hlen : ∀ D, IsOddCycle G D → D.card ≤ 3) :
    CloseToBipartite (2 * k) G := by
  have h := closeToBipartite_of_shareCycleEdge_of_shortOddCycles k 3 hsh hG hlen
  simpa [Nat.mul_comm] using h

/-- **ROUND 78'S INSTANCE IS THE SPECIAL CASE OF THE NEW ONE WITH `MaxDegLe G 3` REINSTATED** —
recorded so that the generalisation is machine-checked in both directions. -/
theorem closeToBipartite_of_maxDegLe_three_of_shortOddCycles (k ℓ : ℕ) (hdeg : MaxDegLe G 3)
    (hG : LocIndep k G) (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ) :
    CloseToBipartite (k * ((ℓ + 1) / 2)) G :=
  closeToBipartite_of_shareCycleEdge_of_shortOddCycles k ℓ
    (ShareCycleEdge.lemma_of_maxDegLe_three hdeg) hG hlen

/-- **THE `ℓ = 3` LEVEL AS AN INSTANCE OF ERDŐS #73.** -/
theorem erdos73On_shareCycleEdge_of_three (k : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W), ShareCycleEdge G → LocIndep k G →
      (∀ D, IsOddCycle G D → D.card ≤ 3) → CloseToBipartite (2 * k) G :=
  fun W instW G hsh hG hlen => closeToBipartite_of_shareCycleEdge_of_three k hsh hG hlen

/-! ### Part 3 — the packing-number-one level, with **no** local hypothesis -/

/-- **THE PACKING-ONE LEVEL, WITH NO LOCAL HYPOTHESIS AT ALL: IF EVERY TWO ODD CYCLES OF `G` MEET, THEN
SOME SET OF AT MOST `(ℓ + 1) / 2` VERTICES MEETS EVERY ODD CYCLE OF `G`.**

Erdős's hypothesis does not occur in the statement: `LocIndep 1` enters, when it occurs at all, only
through the packing statement it implies (`JSP90.inter_oddCycle_of_locIndep_one`).  This is the form in
which an Erdős–Pósa induction on the packing number needs the `k = 1` case. -/
theorem closeToBipartite_of_shareCycleEdge_of_packingOne (ℓ : ℕ) (hsh : ShareCycleEdge G)
    (hmeet : ∀ C D, IsOddCycle G C → IsOddCycle G D → C ∩ D ≠ ∅)
    (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ) : CloseToBipartite ((ℓ + 1) / 2) G := by
  classical
  by_cases hex : (∃ D : Finset V, IsOddCycle G D)
  · obtain ⟨C, hC⟩ := hex
    obtain ⟨Z, hZ, hZhits⟩ :=
      hitsOddCycles_of_inter_of_shareCycleEdge hsh hC (fun D hD => hmeet C D hC hD)
    have hCcard : C.card = (hC.cycleOrder).choose.m :=
      card_eq_cyclicOrder (hC.cycleOrder).choose.f (hC.cycleOrder).choose.hinj
        (hC.cycleOrder).choose.hmem
    have hmle : (hC.cycleOrder).choose.m ≤ ℓ := by
      have h := hlen C hC
      rwa [hCcard] at h
    refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := (ℓ + 1) / 2)).mpr ⟨Z, ?_, hZhits⟩
    rw [hCcard] at hZ
    exact hZ.trans (div_add_one_mono hmle)
  · have hb : G.IsBipartite := isBipartite_of_no_oddCycle (G := G) hex
    exact ⟨∅, by simp, isBipartite_delete hb⟩

/-- **THE TRIANGLE LEVEL OF THE PRECEDING STATEMENT: A GRAPH WHOSE ODD CYCLES ARE TRIANGLES, PAIRWISE
MEET, AND SHARE A CYCLE EDGE WHENEVER THEY MEET, IS `2`-CLOSE TO BIPARTITE.**

This is a new instance of the headline theorem on a class carrying **no degree bound and no local
hypothesis**.  The constant `2` is sharp: `JSP90.not_closeToBipartite_one_K4` below, and
`JSP90.not_shareEdgePackingOne_one`. -/
theorem closeToBipartite_of_shareCycleEdge_of_packingOne_of_three (hsh : ShareCycleEdge G)
    (hmeet : ∀ C D, IsOddCycle G C → IsOddCycle G D → C ∩ D ≠ ∅)
    (hlen : ∀ D, IsOddCycle G D → D.card ≤ 3) : CloseToBipartite 2 G := by
  have h := closeToBipartite_of_shareCycleEdge_of_packingOne 3 hsh hmeet hlen
  simpa using h

/-- **`K₄` HAS MAXIMUM DEGREE `3`.** -/
theorem maxDegLe_completeGraph_four : MaxDegLe (SimpleGraph.completeGraph (Fin 4)) 3 := by
  intro v
  have hneigh : Neigh (SimpleGraph.completeGraph (Fin 4)) v
      = (Finset.univ : Finset (Fin 4)) \ {v} := by
    ext w
    simp [Neigh, SimpleGraph.completeGraph, eq_comm]
  rw [MaxDeg, hneigh]
  simp [Finset.card_sdiff]

/-- **`K₄` SATISFIES THE HYPOTHESIS OF PARTS 1–5.** -/
theorem shareCycleEdge_completeGraph_four :
    ShareCycleEdge (SimpleGraph.completeGraph (Fin 4)) :=
  ShareCycleEdge.lemma_of_maxDegLe_three maxDegLe_completeGraph_four

/-- **EVERY ODD CYCLE OF `K₄` HAS AT MOST THREE VERTICES.**  An odd cycle of `K₄` is a triangle: its
length is odd, at least three, and at most `|V| = 4`. -/
theorem card_le_three_of_oddCycle_completeGraph_four {D : Finset (Fin 4)}
    (hD : IsOddCycle (SimpleGraph.completeGraph (Fin 4)) D) : D.card ≤ 3 := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  have hcard : D.card = m := card_eq_cyclicOrder f hinj hmem
  have hle : D.card ≤ 4 := by
    refine le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
  rw [hcard] at hle
  omega

/-- **EVERY TWO ODD CYCLES OF `K₄` MEET.**  They have three vertices each, out of four. -/
theorem inter_oddCycle_completeGraph_four {C D : Finset (Fin 4)}
    (hC : IsOddCycle (SimpleGraph.completeGraph (Fin 4)) C)
    (hD : IsOddCycle (SimpleGraph.completeGraph (Fin 4)) D) : C ∩ D ≠ ∅ := by
  have h3C : C.card = 3 := by
    have h1 := card_le_three_of_oddCycle_completeGraph_four hC
    obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
    have h3 : 3 ≤ C.card := by rw [card_eq_cyclicOrder f hinj hmem]; omega
    omega
  have h3D : D.card = 3 := by
    have h1 := card_le_three_of_oddCycle_completeGraph_four hD
    obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
    have h3 : 3 ≤ D.card := by rw [card_eq_cyclicOrder f hinj hmem]; omega
    omega
  by_contra hne
  have hdisj : Disjoint C D := Finset.disjoint_iff_inter_eq_empty.mpr hne
  have hcardle : C.card + D.card ≤ 4 := by
    calc C.card + D.card = (C ∪ D).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_le_univ _
      _ = 4 := Finset.card_fin 4
  omega

/-- **THE CONSTANT `2` OF `closeToBipartite_of_shareCycleEdge_of_packingOne_of_three` IS SHARP:
`K₄` SATISFIES ALL ITS HYPOTHESES AND IS NOT ONE VERTEX AWAY FROM BIPARTITE.**

The hypotheses are machine-checked: `shareCycleEdge_completeGraph_four` (the local intersection
property, from `MaxDegLe K₄ 3`), `card_le_three_of_oddCycle_completeGraph_four` (every odd cycle is a
triangle) and `inter_oddCycle_completeGraph_four` (any two odd cycles meet). -/
theorem not_closeToBipartite_one_K4 : ¬ CloseToBipartite 1 (SimpleGraph.completeGraph (Fin 4)) := by
  rw [closeToBipartite_iff_completeGraph_add_two 1 4]
  omega

/-- **`K₄` IS A `LocIndep 2` GRAPH**, so the constant `2` of
`closeToBipartite_of_shareCycleEdge_of_three` is attained inside the range of the theorem. -/
theorem locIndep_two_K4 : LocIndep 2 (SimpleGraph.completeGraph (Fin 4)) :=
  completeGraph_locIndep 2

/-! ### Part 4 — the active edges of an odd cycle, and the cover criterion -/

/-- **THE ACTIVE EDGES OF AN ODD CYCLE.**  In the cyclic ordering `o` of `C`, the **active edges** are
the **cycle edges** of `C` — the pairs `{o.f i, o.f (cycSucc i)}` for `i < o.m` — that lie in another
odd cycle of `G`.  By Part 1, every odd cycle of `G` meeting `C` contains one of them. -/
noncomputable def ActiveEdges {C : Finset V} (o : CycleOrder G C) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (fun e : Finset V =>
    e.card = 2 ∧ (∃ i : Fin o.m, e = ({o.f i, o.f (cycSucc i)} : Finset V)) ∧
      ∃ D : Finset V, IsOddCycle G D ∧ e ⊆ D)

theorem mem_ActiveEdges {C : Finset V} {o : CycleOrder G C} {e : Finset V} :
    e ∈ ActiveEdges o ↔ e.card = 2 ∧ (∃ i : Fin o.m, e = ({o.f i, o.f (cycSucc i)} : Finset V)) ∧
      ∃ D : Finset V, IsOddCycle G D ∧ e ⊆ D := by
  simp [ActiveEdges]

/-- **THE EVEN COVER OF AN ODD CYCLE COVERS THE ACTIVE EDGES OF THAT CYCLE** — under subcubicity,
which is how `ActiveEdges` is meant to be used, and the reason the even cover is the right object to
look at. -/
theorem evenCover_cover_activeEdges (hdeg : MaxDegLe G 3) {C : Finset V} (hC : IsOddCycle G C)
    {o : CycleOrder G C} (hm : o.m % 2 = 1) :
    ∀ e, e ∈ ActiveEdges o → e ∩ evenCover o hm ≠ ∅ := by
  intro e he
  rcases mem_ActiveEdges.mp he with ⟨_, ⟨i, hi⟩, _, _⟩
  rw [hi]
  rcases exists_mem_evenCover_of_cycleEdge (o := o) (hm := hm) i with hc | hc
  · exact Finset.ne_empty_of_mem
      (Finset.mem_inter.mpr ⟨Finset.mem_insert.mpr (Or.inl rfl), hc⟩)
  · exact Finset.ne_empty_of_mem
      (Finset.mem_inter.mpr
        ⟨Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)), hc⟩)

/-- **THE COVER CRITERION: A VERTEX COVER OF THE ACTIVE EDGES OF `C`, SITTING INSIDE `C`, IS A
TRANSVERSAL OF THE WHOLE GRAPH** — provided every odd cycle of `G` meets `C`.  This is the criterion
that round 78's closing plan aimed at. -/
theorem hitsOddCycles_of_activeEdgeCover_of_shareCycleEdge (h : ShareCycleEdge G)
    {C : Finset V} (hC : IsOddCycle G C) {o : CycleOrder G C} {Z : Finset V} (hsub : Z ⊆ C)
    (hne : Z ≠ ∅) (hmeet : ∀ D, IsOddCycle G D → D ≠ C → C ∩ D ≠ ∅)
    (hcover : ∀ e, e ∈ ActiveEdges o → e ∩ Z ≠ ∅) : HitsOddCycles G Z := by
  intro D hD
  by_cases hDC : D = C
  · have hsubD : Z ⊆ D := by rw [hDC]; exact hsub
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨hsubD hz, hz⟩)
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr (hmeet D hD hDC)
  obtain ⟨i, h1, h2⟩ := h C D hC hD (Finset.ne_empty_of_mem hu) o
  have he : ({o.f i, o.f (cycSucc i)} : Finset V) ∈ ActiveEdges o := by
    refine mem_ActiveEdges.mpr ⟨?_, ⟨i, rfl⟩, D, hD, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simp [o.step_ne i]), Finset.card_singleton]
    · intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with hx | hx
      · rw [hx]; exact h1
      · rw [Finset.mem_singleton] at hx
        rw [hx]; exact h2
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr (hcover _ he)
  obtain ⟨hze, hzZ⟩ := Finset.mem_inter.mp hz
  have hzD : z ∈ D := by
    rw [Finset.mem_insert] at hze
    rcases hze with hze | hze
    · rw [hze]; exact h1
    · rw [Finset.mem_singleton] at hze
      rw [hze]; exact h2
  exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨hzD, hzZ⟩)

/-- **THE COVER CRITERION, PACKAGED AS AN INSTANCE OF THE CONCLUSION OF ERDŐS #73.** -/
theorem closeToBipartite_of_activeEdgeCover_of_shareCycleEdge {r : ℕ} {C : Finset V}
    (hC : IsOddCycle G C) (h : ShareCycleEdge G) {o : CycleOrder G C} {Z : Finset V}
    (hsub : Z ⊆ C) (hne : Z ≠ ∅) (hZ : Z.card ≤ r)
    (hmeet : ∀ D, IsOddCycle G D → D ≠ C → C ∩ D ≠ ∅)
    (hcover : ∀ e, e ∈ ActiveEdges o → e ∩ Z ≠ ∅) : CloseToBipartite r G :=
  (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨Z, hZ,
    hitsOddCycles_of_activeEdgeCover_of_shareCycleEdge h hC hsub hne hmeet hcover⟩

/-- **THE COVER CRITERION AT THE EVEN COVER: FOR A SUBCUBIC GRAPH IN WHICH EVERY ODD CYCLE MEETS `C`,
THE EVEN COVER OF `C` IS A TRANSVERSAL OF SIZE AT MOST `(C.card + 1) / 2`.**  This is round 78's
`hitsOddCycles_of_inter` routed through the active edges. -/
theorem hitsOddCycles_of_activeEdgeCover_evenCover (hdeg : MaxDegLe G 3) {C : Finset V}
    (hC : IsOddCycle G C) (hmeet : ∀ D, IsOddCycle G D → D ≠ C → C ∩ D ≠ ∅) :
    ∃ Z : Finset V, Z.card ≤ (C.card + 1) / 2 ∧ HitsOddCycles G Z := by
  obtain ⟨o, hm⟩ := hC.cycleOrder
  have hsub : evenCover o hm ⊆ C := by
    intro x hx
    obtain ⟨i, hi, hfx⟩ := Finset.mem_image.mp hx
    exact (o.hmem x).mpr ⟨i, hfx⟩
  have hne : evenCover o hm ≠ ∅ :=
    Finset.ne_empty_of_mem (mem_evenCover_even_index (hm := hm) (i := ⟨0, by omega⟩) ⟨0, rfl⟩)
  refine ⟨evenCover o hm, card_evenCover (hm := hm), ?_⟩
  intro D hD
  by_cases hDC : D = C
  · have hsubD : evenCover o hm ⊆ D := by rw [hDC]; exact hsub
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨hsubD hz, hz⟩)
  · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr (hmeet D hD hDC)
    exact inter_evenCover_of_shareCycleEdge (ShareCycleEdge.lemma_of_maxDegLe_three hdeg) hC
      (o := o) (hm := hm) hD (Finset.ne_empty_of_mem hu)

/-- **`p9` HAS ODD GIRTH `5`**: every odd cycle of `p9` has at least five vertices.  This is what
makes the pentagon `Cb` a *shortest* odd cycle of `p9`, which is the hypothesis round 78's refuted plan
was stated for. -/
theorem card_ge_five_of_oddCycle_p9 {D : Finset (Fin 9)} (hD : IsOddCycle p9 D) : 5 ≤ D.card := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  have hcard : D.card = m := card_eq_cyclicOrder f hinj hmem
  rw [hcard]
  by_cases h3 : m = 3
  · subst h3
    exfalso
    have hA : p9.Adj (f (0 : Fin 3)) (f (1 : Fin 3)) := by
      have h := hcyc (0 : Fin 3)
      have h0 : cycSucc (0 : Fin 3) = (1 : Fin 3) := by decide
      rw [h0] at h
      exact h
    have hB : p9.Adj (f (1 : Fin 3)) (f (2 : Fin 3)) := by
      have h := hcyc (1 : Fin 3)
      have h1 : cycSucc (1 : Fin 3) = (2 : Fin 3) := by decide
      rw [h1] at h
      exact h
    have hC : p9.Adj (f (2 : Fin 3)) (f (0 : Fin 3)) := by
      have h := hcyc (2 : Fin 3)
      have h2 : cycSucc (2 : Fin 3) = (0 : Fin 3) := by decide
      rw [h2] at h
      exact h
    exact triangleFree_p9 (f (0 : Fin 3)) (f (1 : Fin 3)) hA
      ⟨f (2 : Fin 3), hC.symm, hB.symm⟩
  omega

/-- **THE CONJECTURE OF ROUND 78, STATED PRECISELY AND IN AN INSTANCE-FREE VOCABULARY.**

*For every odd cycle `C` of `G` and every cyclic ordering `o` of it, some set of at most **two**
vertices of `C` covers the **active cycle edges** of `C`: for every odd cycle `D ≠ C` meeting `C`, the
pair `{o.f i, o.f (cycSucc i)}` of consecutive vertices lying in `D` is met by the set.*

`JSP90.not_two_cover_of_Cb` below refutes this for the pentagon `Cb` of the subcubic graph `p9` — i.e.
at a **shortest** odd cycle, which is what the conjecture was stated for.  The statement uses only
`⊆` and element membership, so the two occurrences of the same finite vertex set below are the same
finset, whichever `DecidableEq` is in scope. -/
noncomputable def TwoCoverCycleEdges (G : SimpleGraph V) : Prop :=
  ∀ C : Finset V, IsOddCycle G C → ∀ o : CycleOrder G C,
    ∃ Z : Finset V, Z ⊆ C ∧ Z.card ≤ 2 ∧
      ∀ i : Fin o.m, ∀ D : Finset V, IsOddCycle G D → D ≠ C →
        o.f i ∈ D → o.f (cycSucc i) ∈ D → o.f i ∈ Z ∨ o.f (cycSucc i) ∈ Z

/-! ### Part 5 — the remaining statement, isolated and pinned down -/

/-- **`p9` SATISFIES THE HYPOTHESIS OF PARTS 1–5.** -/
theorem shareCycleEdge_p9 : ShareCycleEdge p9 :=
  ShareCycleEdge.lemma_of_maxDegLe_three maxDegLe_p9

/-- **THE REMAINING STATEMENT.**

A graph in which two odd cycles that meet share a cycle edge, and whose odd cycles pairwise meet, is
`r`-close to bipartite.

This drops **both** hypotheses that remain in the `k = 1` subcubic case — the degree bound
(`MaxDegLe G 3`) and the odd-girth bound (every odd cycle a triangle) — and it is *strictly weaker*
than round 78's `JSP90.SubcubicPackingOne`, which is a special case of it.

It is **stated, not assumed**: the only reductions touching it are
`subcubicPackingOne_of_shareEdgePackingOne_two` (round 78's statement is *implied* by it, so it
subsumes that statement) and `erdos73On_shareEdgePackingOne_one` (it implies the `k = 1` level of the
headline theorem on the class of Part 1).  Neither is used elsewhere. -/
noncomputable def ShareEdgePackingOne.{w} (r : ℕ) : Prop :=
  ∀ (W : Type w) (_ : Fintype W) (G : SimpleGraph W), ShareCycleEdge G →
    (∀ C D, IsOddCycle G C → IsOddCycle G D → C ∩ D ≠ ∅) → CloseToBipartite r G

/-- **THE STATEMENT IS NOT ASSUMED, AND `r = 1` IS IMPOSSIBLE: `¬ ShareEdgePackingOne 1`, BY MACHINE
CHECK.**  `p9` satisfies the hypotheses (`maxDegLe_p9`, hence `shareCycleEdge_p9`; `locIndep_one_p9`,
hence every two of its odd cycles meet by `inter_oddCycle_of_locIndep_one`) and
`JSP90.not_closeToBipartite_one_p9` says it is not one vertex away from bipartite.

So `r = 2` is the sharp candidate for `ShareEdgePackingOne`, `p9` is the witness that it cannot be
lowered, and `JSP90.closeToBipartite_of_shareCycleEdge_of_packingOne_of_three` is the proved base
level for the graphs whose odd cycles are triangles. -/
theorem not_shareEdgePackingOne_one : ¬ ShareEdgePackingOne.{0} 1 :=
  fun h => not_closeToBipartite_one_p9
    (h (Fin 9) inferInstance p9 shareCycleEdge_p9
      (fun C D hC hD => inter_oddCycle_of_locIndep_one locIndep_one_p9 hC hD))

/-- **THE NEW TARGET IS STRICTLY WEAKER THAN ROUND 78'S: `ShareEdgePackingOne 2` IMPLIES
`JSP90.SubcubicPackingOne`.**  The degree bound `MaxDegLe G 3` implies the hypothesis of Part 1
(`ShareCycleEdge.lemma_of_maxDegLe_three`), so the statement of round 78 — a *special case* of
`ShareEdgePackingOne 2` — follows from it. -/
theorem subcubicPackingOne_of_shareEdgePackingOne_two (h : ShareEdgePackingOne.{u} 2) :
    SubcubicPackingOne.{u} :=
  fun W instW G hdeg hmeet =>
    h W instW G (ShareCycleEdge.lemma_of_maxDegLe_three hdeg) hmeet

/-- **THE CONSUMER: `ShareEdgePackingOne r` IMPLIES THE `k = 1` LEVEL OF THE HEADLINE THEOREM ON THE
CLASS OF PART 1.**  Erdős's hypothesis enters only through the packing statement it implies. -/
theorem erdos73On_shareEdgePackingOne_one (h : ShareEdgePackingOne.{u} r) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G → ShareCycleEdge G →
      CloseToBipartite r G :=
  fun W instW G hG hsh =>
    h W instW G hsh (fun C D hC hD => inter_oddCycle_of_locIndep_one hG hC hD)

end General

/-! ## Part 4 — the finite computations on `p9`

Here a **computable** `DecidableEq (Fin n)` is installed, so that the checks below are kernel
computations.  `JSPProblem/Petersen.lean` installs the same instance, but locally to that file; the
classical instance of the previous section must *not* be in scope here, or `decide` would no longer
compute. -/

section Finite

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- A computable `DecidableEq` on `Fin n`. -/
local instance instDecidableEqCoverFin (n : ℕ) : DecidableEq (Fin n) := instDecidableEqFin n

/-- Adjacency of `p9` is decidable: this is what makes the checks of this section kernel computations. -/
local instance instDecidableAdjP9 : DecidableRel p9.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ p9Edge))

/-- The cyclic ordering `2 – 3 – 8 – 5 – 7 – 2` of the pentagon `Cb` of `p9`. -/
def oCb : CycleOrder p9 Cb := ⟨5, cyc5 2 3 8 5 7, by decide, by decide, by decide, mem_Cb⟩

/-- The five **cycle edges** of `Cb`. -/
def activeCb : Finset (Finset (Fin 9)) :=
  {{2, 3}, {3, 8}, {8, 5}, {5, 7}, {7, 2}}

theorem mem_activeCb : ∀ e : Finset (Fin 9), e ∈ activeCb ↔
    e = {2, 3} ∨ e = {3, 8} ∨ e = {8, 5} ∨ e = {5, 7} ∨ e = {7, 2} := by decide

theorem card_activeCb : activeCb.card = 5 := by decide

/-- **`activeCb` IS EXACTLY THE SET OF CYCLE EDGES OF `Cb`** — the finite computation of this section
and the definition of Part 4 speak the same language. -/
theorem activeCb_eq_cycleEdges : ∀ e : Finset (Fin 9),
    e ∈ activeCb ↔ ∃ i : Fin 5, e = ({oCb.f i, oCb.f (cycSucc i)} : Finset (Fin 9)) := by
  intro e
  rw [mem_activeCb]
  constructor
  · rintro (h | h | h | h | h)
    · rw [h]; exact ⟨⟨0, by omega⟩, rfl⟩
    · rw [h]; exact ⟨⟨1, by omega⟩, rfl⟩
    · rw [h]; exact ⟨⟨2, by omega⟩, rfl⟩
    · rw [h]; exact ⟨⟨3, by omega⟩, rfl⟩
    · rw [h]; exact ⟨⟨4, by omega⟩, rfl⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> rw [hi] <;> decide

/-- **EVERY EDGE OF THE PENTAGON `Cb` OF `p9` IS ACTIVE**: the five cycle edges of `Cb` lie in the odd
cycles `Ca`, `Ca`, `Cc`, `Cd`, `Cd` respectively. -/
theorem each_activeCb_active : ∀ e, e ∈ activeCb → ∃ C, IsOddCycle p9 C ∧ C ≠ Cb ∧ e ⊆ C := by
  intro e he
  rcases (mem_activeCb e).mp he with h | h | h | h | h
  · subst h
    exact ⟨Ca, isOddCycle_Ca, by decide, by decide⟩
  · subst h
    exact ⟨Ca, isOddCycle_Ca, by decide, by decide⟩
  · subst h
    exact ⟨Cc, isOddCycle_Cc, by decide, by decide⟩
  · subst h
    exact ⟨Cd, isOddCycle_Cd, by decide, by decide⟩
  · subst h
    exact ⟨Cd, isOddCycle_Cd, by decide, by decide⟩

/-- **NO SET OF AT MOST TWO VERTICES OF `Cb` COVERS THE ACTIVE CYCLE EDGES OF `Cb`.**  The
verification is a `decide` over all `3 ^ 9 = 19 683` vertex subsets of the nine vertices of `p9`; it is
a kernel computation. -/
theorem no_two_cover_activeCb : ∀ Z : Finset (Fin 9), Z ⊆ Cb → Z.card ≤ 2 →
    ∃ e, e ∈ activeCb ∧ e ∩ Z = ∅ := by decide

/-- **AND THREE VERTICES COVER THEM** — e.g. `{2, 7, 8}`, the even positions of the cycle. -/
theorem exists_cover_activeCb_three : ∃ Z : Finset (Fin 9), Z ⊆ Cb ∧ Z.card = 3 ∧
    ∀ e, e ∈ activeCb → e ∩ Z ≠ ∅ := by decide

/-- **THE VERTEX-COVER NUMBER OF THE ACTIVE EDGES OF `Cb` IS EXACTLY THREE.** -/
theorem card_vertexCover_activeCb : ∀ Z : Finset (Fin 9), Z ⊆ Cb →
    (∀ e, e ∈ activeCb → e ∩ Z ≠ ∅) → 3 ≤ Z.card := by decide

/-- **THE CONJECTURE OF ROUND 78 IS FALSE AT THE SHORTEST ODD CYCLE `Cb` OF `p9`, IN THE
CONJECTURE'S OWN (ORDER-BASED) VOCABULARY.** -/
theorem not_two_cover_of_Cb :
    ¬ (∃ Z : Finset (Fin 9), Z ⊆ Cb ∧ Z.card ≤ 2 ∧
      ∀ i : Fin 5, ∀ D : Finset (Fin 9), IsOddCycle p9 D → D ≠ Cb →
        oCb.f i ∈ D → oCb.f (cycSucc i) ∈ D → oCb.f i ∈ Z ∨ oCb.f (cycSucc i) ∈ Z) := by
  rintro ⟨Z, hsub, hcard, h⟩
  unfold oCb at h
  obtain ⟨e, he, hemp⟩ := no_two_cover_activeCb Z hsub hcard
  obtain ⟨i, hi⟩ := (activeCb_eq_cycleEdges e).mp he
  obtain ⟨D, hD, hDC, hDsub⟩ := each_activeCb_active e he
  rw [hi] at hemp hDsub
  have hxf : oCb.f i ∈ D := hDsub (Finset.mem_insert.mpr (Or.inl rfl))
  have hyf : oCb.f (cycSucc i) ∈ D :=
    hDsub (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
  rcases h i D hD hDC hxf hyf with hz | hz
  · have hmem : oCb.f i ∈ ({oCb.f i, oCb.f (cycSucc i)} : Finset (Fin 9)) ∩ Z :=
      Finset.mem_inter.mpr ⟨Finset.mem_insert.mpr (Or.inl rfl), hz⟩
    rw [hemp] at hmem
    exact Finset.not_nonempty_empty ⟨_, hmem⟩
  · have hmem : oCb.f (cycSucc i) ∈ ({oCb.f i, oCb.f (cycSucc i)} : Finset (Fin 9)) ∩ Z :=
      Finset.mem_inter.mpr
        ⟨Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)), hz⟩
    rw [hemp] at hmem
    exact Finset.not_nonempty_empty ⟨_, hmem⟩

/-- **ROUND 78'S CONCRETE NEXT LEMMA IS FALSE, BY MACHINE CHECK.**

Round 78 closed its policy with the plan: *"for a shortest odd cycle `C` of a subcubic graph, the edges
of `C` that lie in another odd cycle are covered by two vertices of `C`"*.  `p9` is subcubic
(`JSP90.maxDegLe_p9`), `Cb` is a shortest odd cycle of `p9` (`JSP90.card_ge_five_of_oddCycle_p9`,
`JSP90.isOddCycle_Cb`), all five of its cycle edges are active (`JSP90.each_activeCb_active`,
`JSP90.activeCb_eq_cycleEdges`), and no two vertices cover them (`JSP90.not_two_cover_of_Cb`).  Three
are needed (`JSP90.card_vertexCover_activeCb`) and three are what the even cover of `Cb` provides. -/
theorem not_vertexCover_two_of_activeCb :
    ¬ (∃ Z : Finset (Fin 9), Z ⊆ Cb ∧ Z.card ≤ 2 ∧ ∀ e, e ∈ activeCb → e ∩ Z ≠ ∅) := by
  rintro ⟨Z, hsub, hcard, h⟩
  obtain ⟨e, he, hemp⟩ := no_two_cover_activeCb Z hsub hcard
  exact (h e he) hemp

end Finite

end
end JSP90