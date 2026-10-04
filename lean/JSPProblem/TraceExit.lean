import JSPProblem.TraceComplex

/-!
# JSP-000090, round 145 — `JSPProblem/TraceExit.lean`: **the sharp case is ONE statement, one-point
cross-overs are singleton traces, and the exit step**

Attack family 73.  Round 144 introduced the **trace complex** `JSP90.traceFamily G C` and reduced the
sharp case `Erdős73On 1 2` to *two* named statements (`JSP90.AllCrossResidual` of round 141 for the
`|attachPoints| = 3` half, and `JSP90.TraceCoverResidual` for `|attachPoints| ≥ 3`).  This round
removes one of the two, bridges the two vocabularies, and adds the **exit step** — the missing
structural lemma of the trace complex.  16 declarations, no placeholders, `lake build` OK (1296 jobs).

## Part 1 — **the residual is ONE statement**

`JSP90.TraceCoverResidual` is stated for `3 ≤ |attachPoints G C|`, so it *already* contains the three
attachment point case; round 144 nevertheless used round 141's machinery there, because it reused the
`|attachPoints| ≤ 3` branch of the older reduction.  Reorganising the case analysis gives

* **`JSP90.erdos73On_one_two_of_traceCoverResidual` — THE SHARP CASE `Erdős73On 1 2` FROM
  `JSP90.TraceCoverResidual` ALONE.**

So the sharp case of Erdős #73 — the optimal constant `f(1) = 2` — is *equivalent to a single
statement*: the trace complex of a shortest odd cycle with at least three attachment points has a
cover of size `≤ 2` inside the attachment points.  Round 144's `AllCrossResidual` hypothesis is
redundant and is not needed.

## Part 2 — **a one-point cross-over is a singleton trace**

* **`JSP90.mem_traceFamily_of_onePointCrossOver`** — if an odd cycle `D` meets `C$ in the single point
  `a`, then `{a}` is a trace of `C$:

  ```lean
  OnePointCrossOver G C D → a ∈ C ∩ D → ({a} : Finset V) ∈ traceFamily G C
  ```

  Indeed `attachPoints G C ⊆ C` gives `D ∩ attachPoints G C ⊆ D ∩ C = {a}`, and `a` is an attachment
  point by round 139's `JSP90.mem_attachPoints_of_onePointCrossOver`.  **No hypothesis at all** — not
  packing number one, not minimality of `C$;
* `JSP90.singletonTrace_of_crossOverPoint`, `JSP90.singletonTrace_of_mem_crossOverSet`,
  **`JSP90.threeSingletonTraces_of_subset_crossOverSet`** and
  `JSP90.threeSingletonTraces_of_eq_crossOverSet`: round 141's cross-over configuration
  `attachPoints G C = crossOverSet G C` **forces** round 144's `JSP90.ThreeSingletonTraces`, so the
  configuration compared by round 141 is contained in the configuration compared by round 144.

## Part 3 — **no cross-over is a positive instance of the sharp case**

* **`JSP90.eq_empty_crossOverSet_of_noCrossOver`** and `JSP90.not_crossOverPoint_of_noCrossOver`:
  under `JSP90.NoCrossOver G C` there are **no** cross-over points at all, so round 139's erasure
  lemma applies with **no exception**:
  **`JSP90.hitsOddCycles_attachPoints_sdiff_of_noCrossOver`** — `attachPoints G C \ {b}` is an odd
  cycle transversal for **every** attachment point `b`;
* **`JSP90.exists_cover_le_two_of_card_attachPoints_eq_three_of_noCrossOver`** — at three attachment
  points and no cross-over the sharp case holds with the **optimal** constant `2`;
* **`JSP90.SmallAttachNoCrossOver` + `JSP90.closeToBipartite_two_of_smallAttach_noCrossOver` +
  `JSP90.erdos73On_one_two_of_smallAttach_noCrossOver` — A NEW INSTANCE OF THE HEADLINE THEOREM**:
  graphs in which every shortest odd cycle has at most three attachment points *and* no odd cycle
  meets a shortest odd cycle in exactly one vertex satisfy `Erdős73On 1 2` with the **optimal**
  constant `2` — no bound on the odd girth, the packing weight or the number of branch vertices, and
  **no residual statement at all** (rounds 141 and 144 each needed one on this class:
  `JSP90.AllCrossResidual` resp. `JSP90.TraceCoverResidual`).

## Part 5 — **the exit step**

* **`JSP90.attachPoints_inter_D_nonempty_of_not_subset_C`** — **a cycle that meets `C$ but is not
  contained in it leaves it**:

  ```lean
  IsOddCycle G D → (C ∩ D).Nonempty → ¬ D ⊆ C → (attachPoints G C ∩ D).Nonempty
  ```

  If the nonempty set of positions of the cyclic numbering which lie on `C$ were closed under
  `cycSucc`, then by induction every `cycSucc^[d] j` would lie on `C$, and since every position is a
  `cycSucc^[d]` of any other (`JSP90.exists_arc`) the whole cycle would lie in `C$ — a
  contradiction.  So some `j` has `f j ∈ C$ and `f (cycSucc j) ∉ C$, and `f j$ is an attachment point
  lying on `D$.  This is the classical *exit step* of the fan argument: it is the reason every trace
  `D ∩ attachPoints G C$ contains the points at which `D$ leaves `C$, and the first step of the
  classical proof that the two ends of a maximal `C$-chain along `D$ are attachment points.

## A mathematical finding recorded here

**The converse of Part 2 is FALSE, and the reason is instructive.**  A *singleton trace* does **not**
imply a *one-point cross-over*: take `C$ = ` a 5-cycle `1-2-3-4-5`, `D$ = the triangle `1-2-3` inside
it, and a pendant vertex `6` adjacent to `1` (this graph satisfies `LocIndep 1`).  Then
`attachPoints G C = {1}` and `D ∩ attachPoints G C = {1}` is a singleton trace, but
`C ∩ D = {1,2,3}`.  The reason is that `attachPoints` records where a cycle **leaves** `C$, while a
trace only records the attachment points met; a cycle can enter `C$ at a point which is *not* an
attachment point (it has no neighbour outside `C$) and travel inside `C$`.  So
`ThreeSingletonTraces` is **weaker** than round 141's cross-over configuration
`attachPoints G C = crossOverSet G C`, which is exactly what Part 2 proves.

## What is *not* proved

`JSP90.TraceCoverResidual`, and behind it `JSP90.NoTraceK4`, `JSP90.OneTracePair`,
`JSP90.NoThreeSingletonTraces` and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the
unchanged primary blocker.  `jsp_000090_main` is deliberately **not** declared, so the harness keeps
reporting `missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 800000

local instance traceExitDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Part 1 — **the sharp case is one statement** -/

/-- **ERDŐS PROBLEM #73 AT `k = 1` WITH THE OPTIMAL CONSTANT `2` FROM THE TRACE-COVER RESIDUAL
ALONE.**

```lean
TraceCoverResidual → Erdős73On 1 2
```

`TraceCoverResidual` is stated for `3 ≤ |attachPoints G C|`, so the three attachment point case is
*included*: at a shortest odd cycle with two attachment points at most the attachment set itself is a
transversal (`JSP90.hitsOddCycles_attachPoints_of_packing_one`), and a shortest odd cycle with an
empty fan is hit by a single vertex
(`JSP90.hitsOddCycles_boundary_singleton_of_locIndep_one`).  Hence round 144's extra hypothesis
`JSP90.AllCrossResidual` is *redundant*, and the residual of the sharp case is a **single** statement. -/
theorem erdos73On_one_two_of_traceCoverResidual (hT : TraceCoverResidual.{u}) : Erdős73On.{u} 1 2 := by
  intro W instW G hG
  rw [closeToBipartite_iff_hitsOddCycles]
  by_cases hex : ∃ C : Finset W, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle (G := G) hex
    obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
    by_cases hne : (boundary G C).Nonempty
    · by_cases hb : (attachPoints G C).card ≤ 2
      · exact ⟨attachPoints G C, hb,
          hitsOddCycles_attachPoints_of_packing_one (packingNumberOne_of_locIndep_one hG)
            hC hshort hne⟩
      · obtain ⟨X, hX, hX2, hh⟩ := hT W instW G hG C hC hshort (by omega)
        exact ⟨X, hX2, fun D hD => hh D hD⟩
    · have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hh : HitsOddCycles G ({c} : Finset W) := by
        simpa [h0] using hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc
      exact ⟨{c}, by simp, hh⟩
  · exact ⟨∅, by simp, fun D hD => absurd ⟨D, hD⟩ hex⟩

/-! ## Part 2 — **a one-point cross-over is a singleton trace** -/

/-- **A ONE-POINT CROSS-OVER IS A SINGLETON TRACE.**  If an odd cycle `D` meets `C$ in the single
vertex `a`, then `D ∩ attachPoints G C = {a}` is a trace of `C$:

```lean
OnePointCrossOver G C D → a ∈ C ∩ D → ({a} : Finset V) ∈ traceFamily G C
```

Indeed `attachPoints G C ⊆ C` gives `D ∩ attachPoints G C ⊆ D ∩ C = {a}`, and `a` is an attachment
point by round 139's `JSP90.mem_attachPoints_of_onePointCrossOver` (which needs no hypothesis).  No
packing-number-one hypothesis and no minimality of `C$ are needed: this is pure set theory. -/
theorem mem_traceFamily_of_onePointCrossOver {C D : Finset V} (h : OnePointCrossOver G C D)
    {a : V} (ha : a ∈ C ∩ D) : ({a} : Finset V) ∈ traceFamily G C := by
  have haA : a ∈ attachPoints G C := mem_attachPoints_of_onePointCrossOver h ha
  have hsing : C ∩ D = {a} := inter_eq_singleton_of_onePointCrossOver h ha
  refine ⟨D, h.1, Finset.Subset.antisymm ?_ ?_⟩
  · intro z hz
    have hzD : z ∈ D := (Finset.mem_inter.mp hz).1
    have hzA : z ∈ attachPoints G C := (Finset.mem_inter.mp hz).2
    have hzCD : z ∈ C ∩ D := Finset.mem_inter.mpr ⟨subset_attachPoints_C C hzA, hzD⟩
    rw [hsing] at hzCD
    exact hzCD
  · intro z hz
    have hza : z = a := Finset.mem_singleton.mp hz
    subst hza
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).2, haA⟩

/-- **A CROSS-OVER POINT WHICH IS AN ATTACHMENT POINT IS A SINGLETON TRACE.** -/
theorem singletonTrace_of_crossOverPoint {C : Finset V} {a : V} (ha : a ∈ attachPoints G C)
    (h : CrossOverPoint G C a) : ({a} : Finset V) ∈ traceFamily G C := by
  obtain ⟨D, hD, haCD⟩ := h
  exact mem_traceFamily_of_onePointCrossOver hD haCD

/-- **A CROSS-OVER POINT OF THE CROSS-OVER SET IS A SINGLETON TRACE.** -/
theorem singletonTrace_of_mem_crossOverSet {C : Finset V} {a : V} (ha : a ∈ crossOverSet G C) :
    ({a} : Finset V) ∈ traceFamily G C :=
  singletonTrace_of_crossOverPoint (mem_crossOverSet.mp ha).2 (mem_crossOverSet.mp ha).1

/-- **ROUND 141's CROSS-OVER CONFIGURATION FORCES ROUND 144's SINGLETON TRACES.**  Every attachment
point of `C$ being a cross-over point makes every attachment point a trace, so
`attachPoints G C = crossOverSet G C` forces `JSP90.ThreeSingletonTraces G C`: the two
configurations compared by rounds 141 and 144 are *not* independent. -/
theorem threeSingletonTraces_of_subset_crossOverSet {C : Finset V}
    (h : attachPoints G C ⊆ crossOverSet G C) : ThreeSingletonTraces G C :=
  fun a haA => singletonTrace_of_mem_crossOverSet (h haA)

/-- **THE CROSS-OVER CONFIGURATION IMPLIES THE SINGLETON TRACES.** -/
theorem threeSingletonTraces_of_eq_crossOverSet {C : Finset V}
    (h : attachPoints G C = crossOverSet G C) : ThreeSingletonTraces G C :=
  threeSingletonTraces_of_subset_crossOverSet (fun _ ha => h ▸ ha)

/-! ## Part 3 — **no cross-over is a positive instance of the sharp case** -/

/-- **UNDER NO CROSS-OVER THERE ARE NO CROSS-OVER POINTS.**  `JSP90.NoCrossOver G C` says that no odd
cycle other than `C$ meets `C$ in exactly one vertex, which is precisely what
`JSP90.CrossOverPoint G C a` asserts for every `a`; so the cross-over set is empty.  **No hypothesis
on `C$ at all** (it does not even have to be an odd cycle or shortest). -/
theorem eq_empty_crossOverSet_of_noCrossOver {C : Finset V} (hnc : NoCrossOver G C) :
    crossOverSet G C = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun a ha => ?_
  obtain ⟨D, hD, haCD⟩ := (mem_crossOverSet.mp ha).1
  exact hnc D hD.1 hD.2.1 hD.2.2

/-- **NO POINT IS A CROSS-OVER POINT UNDER `NoCrossOver`.** -/
theorem not_mem_crossOverSet_of_noCrossOver {C : Finset V} (hnc : NoCrossOver G C) {a : V} :
    a ∉ crossOverSet G C := by
  intro ha
  have h0 : crossOverSet G C = ∅ := eq_empty_crossOverSet_of_noCrossOver hnc
  rw [h0] at ha
  exact absurd ha (by simp)

/-- **NO ATTACHMENT POINT IS A CROSS-OVER POINT UNDER `NoCrossOver`.**  In pointwise form; the
`Finset` form is `JSP90.not_mem_crossOverSet_of_noCrossOver` below. -/
theorem not_crossOverPoint_of_noCrossOver {C : Finset V} (hnc : NoCrossOver G C) {a : V} :
    ¬ CrossOverPoint G C a := by
  rintro ⟨D, hD, haCD⟩
  exact hnc D hD.1 hD.2.1 hD.2.2

/-- **UNDER NO CROSS-OVER, ERASING ANY ATTACHMENT POINT LEAVES A TRANSVERSAL.**  Round 139's erasure
lemma `JSP90.hitsOddCycles_attachPoints_sdiff_of_not_crossOver` with **no exception**: under
`NoCrossOver G C` there is no attachment point which is not a cross-over point. -/
theorem hitsOddCycles_attachPoints_sdiff_of_noCrossOver (h : PackingNumberOne G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) {b : V} (hbA : b ∈ attachPoints G C) (h2 : 2 ≤ (attachPoints G C).card) :
    HitsOddCycles G (attachPoints G C \ {b}) :=
  hitsOddCycles_attachPoints_sdiff_of_not_crossOver h hC hshort hbA
    (not_crossOverPoint_of_noCrossOver hnc) h2

/-- **AT THREE ATTACHMENT POINTS AND NO CROSS-OVER THE SHARP CASE IS PROVED.**  The residual of
rounds 137–144 is *not* needed on this class: erasing any attachment point leaves a two-element
transversal. -/
theorem exists_cover_le_two_of_card_attachPoints_eq_three_of_noCrossOver (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) (h3 : (attachPoints G C).card = 3) :
    ∃ X : Finset V, X ⊆ attachPoints G C ∧ X.card ≤ 2 ∧ HitsOddCycles G X := by
  have hneA : (attachPoints G C).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (by
      intro h0
      have hh := congrArg Finset.card h0
      rw [Finset.card_empty, h3] at hh
      omega)
  obtain ⟨b, hbA⟩ := hneA
  have hcard : (attachPoints G C \ {b}).card = 2 := by
    rw [card_sdiff_singleton_of_mem_attachPoints hbA, h3]
  exact ⟨attachPoints G C \ {b}, Finset.sdiff_subset, hcard.le,
    hitsOddCycles_attachPoints_sdiff_of_noCrossOver h hC hshort hnc hbA (by rw [h3]; omega)⟩

/-! ## Part 4 — **A NEW INSTANCE OF THE HEADLINE THEOREM** -/

/-- **THE NO-CROSS-OVER CLASS**: no shortest odd cycle of `G` is met by another odd cycle in exactly
one vertex.  A property of the odd cycles of `G` alone — no bound on the odd girth, on the packing
weight or on the number of branch vertices. -/
def SmallAttachNoCrossOver (G : SimpleGraph V) : Prop :=
  ∀ C : Finset V, IsOddCycle G C → (∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) →
    NoCrossOver G C

/-- **ERDŐS PROBLEM #73 WITH THE OPTIMAL CONSTANT `2` ON THE NO-CROSS-OVER CLASS WITH SMALL
ATTACHMENT SETS** — per graph. -/
theorem closeToBipartite_two_of_smallAttach_noCrossOver {W : Type u} (instW : Fintype W)
    (G : SimpleGraph W) (hG : LocIndep 1 G)
    (hall : ∀ C : Finset W, IsOddCycle G C →
      (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) → (attachPoints G C).card ≤ 3)
    (hnc : SmallAttachNoCrossOver.{u} G) : CloseToBipartite 2 G := by
  rw [closeToBipartite_iff_hitsOddCycles]
  by_cases hex : ∃ C : Finset W, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle (G := G) hex
    have hpack : PackingNumberOne G := packingNumberOne_of_locIndep_one hG
    by_cases hne : (boundary G C).Nonempty
    · by_cases hb : (attachPoints G C).card ≤ 2
      · exact ⟨attachPoints G C, hb, hitsOddCycles_attachPoints_of_packing_one hpack hC hshort hne⟩
      · have hle3 : (attachPoints G C).card ≤ 3 := hall C hC hshort
        obtain ⟨X, hX, hX2, hh⟩ :=
          exists_cover_le_two_of_card_attachPoints_eq_three_of_noCrossOver hpack hC hshort
            (hnc C hC hshort) (by omega)
        exact ⟨X, hX2, fun D hD => hh D hD⟩
    · obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
      have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hh : HitsOddCycles G ({c} : Finset W) := by
        simpa [h0] using hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc
      exact ⟨{c}, by simp, hh⟩
  · exact ⟨∅, by simp, fun D hD => absurd ⟨D, hD⟩ hex⟩

/-- **A CLASS INSTANCE OF ERDŐS PROBLEM #73 WITH THE OPTIMAL CONSTANT `2`: `Erdős73On 1 2` follows
from "every shortest odd cycle has at most three attachment points" together with "no shortest odd
cycle is met by another odd cycle in exactly one vertex".**

Both are properties of the odd cycles of `G` alone — no bound on the odd girth, on the packing weight
or on the number of branch vertices — and **no residual hypothesis of rounds 137–144 is needed on this
class**: at two attachment points the attachment set itself is a transversal
(`JSP90.hitsOddCycles_attachPoints_of_packing_one`), at three the erasure of any attachment point is
(Part 3), and a shortest odd cycle with an empty fan is hit by a single vertex.  Compare
`JSP90.erdos73On_one_two_of_maxCardAttach_three`, which needs round 141's
`JSP90.AllCrossResidual` on the same bounded-attachment class. -/
theorem erdos73On_one_two_of_smallAttach_noCrossOver
    (hbound : ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), ∀ C : Finset W, IsOddCycle G C →
      (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) → (attachPoints G C).card ≤ 3)
    (hnc : ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), ∀ C : Finset W, IsOddCycle G C →
      (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) → NoCrossOver G C) :
    Erdős73On.{u} 1 2 := by
  intro W instW G hG
  exact closeToBipartite_two_of_smallAttach_noCrossOver instW G hG (hbound W instW G) (hnc W instW G)

/-! ## Part 5 — **the exit step: where a cycle leaves `C`** -/

/-- **A CYCLE THAT MEETS `C$ BUT IS NOT CONTAINED IN IT LEAVES IT.**

```lean
IsOddCycle G D → (C ∩ D).Nonempty → ¬ D ⊆ C → (attachPoints G C ∩ D).Nonempty
```

If the nonempty set of positions of the cyclic numbering which lie on `C$ were closed under
`cycSucc`, then by induction every `cycSucc^[d] j` would lie on `C$, and since every position is a
`cycSucc^[d]` of any other (`JSP90.exists_arc`) the whole cycle would lie in `C$ — a contradiction.
So there is a position `j` with `f j ∈ C$ and `f (cycSucc j) ∉ C$`: the vertex `f j$ lies on `C$,
has the neighbour `f (cycSucc j)$ outside `C$` — so it is an attachment point of `C$ — and lies on
`D$.  This is the classical *exit step* of the fan argument, and the reason why every trace
`D ∩ attachPoints G C` contains the points at which `D$ leaves `C$. -/
theorem attachPoints_inter_D_nonempty_of_not_subset_C {C D : Finset V} (hD : IsOddCycle G D)
    (hne : (C ∩ D).Nonempty) (hnsub : ¬ D ⊆ C) : (attachPoints G C ∩ D).Nonempty := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  have hmemD : ∀ x : V, x ∈ D ↔ ∃ j : Fin m, f j = x := hmem
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hxC, hxD⟩ := Finset.mem_inter.mp hx
  obtain ⟨j0, hj0⟩ := (hmemD x).mp hxD
  have hj0C : f j0 ∈ C := hj0 ▸ hxC
  set S : Finset (Fin m) := Finset.univ.filter (fun j : Fin m => f j ∈ C) with hSdef
  have hmem' : ∀ j : Fin m, j ∈ S ↔ f j ∈ C := by
    intro j
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
  have hj0S : j0 ∈ S := (hmem' j0).mpr hj0C
  by_cases hcl : ∀ j ∈ S, cycSucc j ∈ S
  · have horbit : ∀ k : ℕ, ((cycSucc^[k] : Fin m → Fin m) j0) ∈ S := by
      intro k
      induction k with
      | zero => exact hj0S
      | succ k ih =>
        rw [cycSucc_succ_pow]
        exact hcl _ ih
    have hall : ∀ i : Fin m, i ∈ S := by
      intro i
      by_cases hji : i = j0
      · rw [hji]
        exact hj0S
      · obtain ⟨d, hd0, hdm, hid⟩ := exists_arc (m := m) (by omega) (Ne.symm hji)
        rw [← hid]
        exact horbit d
    exact False.elim (hnsub (fun z hz => by
      obtain ⟨k, hk⟩ := (hmemD z).mp hz
      rw [← hk]
      exact (hmem' k).mp (hall k)))
  · have hcl' : ∃ j : Fin m, j ∈ S ∧ cycSucc j ∉ S := by
      by_cases he : ∃ j : Fin m, j ∈ S ∧ cycSucc j ∉ S
      · exact he
      · exfalso
        have hP : ∀ j : Fin m, j ∈ S → cycSucc j ∈ S := by
          intro j hjS
          by_contra hn
          exact he ⟨j, hjS, hn⟩
        exact hcl hP
    obtain ⟨j, hjS, hjnc⟩ := hcl'
    have hjC : f j ∈ C := (hmem' j).mp hjS
    exact ⟨f j, Finset.mem_inter.mpr ⟨mem_attachPoints.mpr ⟨hjC, f (cycSucc j),
      mem_boundary.mpr ⟨(hmem' (cycSucc j)).not.mp hjnc, f j, hjC, (hcyc j).symm⟩, hcyc j⟩,
      (hmem (f j)).mpr ⟨j, rfl⟩⟩⟩

#print axioms JSP90.attachPoints_inter_D_nonempty_of_not_subset_C
#print axioms JSP90.erdos73On_one_two_of_traceCoverResidual
#print axioms JSP90.mem_traceFamily_of_onePointCrossOver
#print axioms JSP90.singletonTrace_of_crossOverPoint
#print axioms JSP90.singletonTrace_of_mem_crossOverSet
#print axioms JSP90.threeSingletonTraces_of_subset_crossOverSet
#print axioms JSP90.threeSingletonTraces_of_eq_crossOverSet
#print axioms JSP90.eq_empty_crossOverSet_of_noCrossOver
#print axioms JSP90.not_mem_crossOverSet_of_noCrossOver
#print axioms JSP90.not_crossOverPoint_of_noCrossOver
#print axioms JSP90.hitsOddCycles_attachPoints_sdiff_of_noCrossOver
#print axioms JSP90.exists_cover_le_two_of_card_attachPoints_eq_three_of_noCrossOver
#print axioms JSP90.closeToBipartite_two_of_smallAttach_noCrossOver
#print axioms JSP90.erdos73On_one_two_of_smallAttach_noCrossOver

/-! ## What is *not* proved

`JSP90.TraceCoverResidual`, and behind it `JSP90.NoTraceK4`, `JSP90.OneTracePair`,
`JSP90.NoThreeSingletonTraces` and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas).
`jsp_000090_main` is deliberately not declared. -/

end

end JSP90
