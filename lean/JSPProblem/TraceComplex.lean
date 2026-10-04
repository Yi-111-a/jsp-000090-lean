import JSPProblem.FanCount

/-!
# JSP-000090, round 144 — `JSPProblem/TraceComplex.lean`: **the TRACE COMPLEX of a shortest odd cycle,
and the classification of the failure of the sharp case `k = 1` at three and four attachment points**

Attack family 72.  Rounds 136–143 attacked the sharp case `Erdős73On 1 2` through the *attachment
points* `attachPoints G C` and the *fan* `boundary G C`; round 142 introduced the "traces"
`D ∩ attachPoints G C` one at a time and needed `NoCrossOver G C` for its six-traces theorem.  This
round replaces that ad-hoc language by **one object**, the TRACE COMPLEX of `C`,

```
JSP90.traceFamily G C  =  { D ∩ attachPoints G C  :  D  an odd cycle of G },
```

and proves that every question the development has been asking about transversals at a shortest odd
cycle is a question about this family.  The centre of the round is **the cover–transversal duality**
(`JSP90.hitsOddCycles_iff_covers_traceFamily`): a set of attachment points is an odd-cycle transversal
exactly when it is a **cover of the trace complex**.

## What this buys

* **`JSP90.hitsOddCycles_iff_covers_traceFamily`** — the cover–transversal duality: for
  `X ⊆ attachPoints G C`, `X ≠ ∅`, and every odd cycle other than `C` meeting the attachment points,
  `X` is an odd-cycle transversal **iff** it meets every trace of `C`.  Every question the
  development asks about transversals is a question about one object.

* **`JSP90.not_hitsOddCycles_iff_exists_trace_subset_complement`** — the general form, for any number
  of attachment points: a pair `Q ⊆ attachPoints G C` fails to be a transversal **iff some trace lies
  inside `attachPoints G C \ Q`**.  Two lines: packing number one makes the trace nonempty.

* **`JSP90.not_hitsOddCycles_iff_exists_trace_eq_complement_of_card_attachPoints_eq_three`** — at three
  attachment points the complement has ONE element, so the trace **is** the complementary singleton,
  with **no `NoCrossOver` hypothesis**.  This is the trace-complex form of round 141's cross-over
  configuration, and it gives the `|A| = 3` half of the residual as an `iff`:

  **`JSP90.not_cover_le_two_iff_threeSingletons_of_card_attachPoints_eq_three`** — the sharp case fails
  at `|attachPoints G C| = 3` **iff all three attachment points are singleton traces**.

* **`JSP90.not_hitsOddCycles_iff_mem_tracePair_of_card_attachPoints_eq_four_of_noCrossOver`** — at four
  attachment points and no cross-over, a failing pair is exactly the complementary **two-element
  trace**, giving **`JSP90.not_cover_le_two_iff_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver`**:
  the sharp case fails at `|attachPoints G C| = 4` **iff** the six-traces configuration
  `JSP90.TraceK4` occurs (round 142's theorem, re-derived in the trace language).  The `NoCrossOver`
  hypothesis **is** needed here, and round 144's measurement `r144c` `U2` says why: at `LocIndep 1` two
  odd cycles may meet in **three or four** points (55 800 cases), so the trace of an odd cycle need
  not be small and the counting `|attachPoints G C \ Q| = 2` alone does not give the two-element
  trace — round 142's segment lemma does.  (Round 142's result is thus *not* superseded; it is
  re-proved here through `JSP90.two_le_card_attachPoints_inter_of_noCrossOver_of_packing_one`.)

* **`JSP90.TraceCoverResidual`** — the whole `3 ≤ |attachPoints G C|` half of the sharp case as ONE
  statement ("the trace complex of `C` has a cover of size `≤ 2` inside `attachPoints G C`"), and
  **`JSP90.erdos73On_one_two_of_allCrossResidual_and_traceCoverResidual`**: the sharp case
  `Erdős73On 1 2` follows from round 141's `AllCrossResidual` together with this one statement.  The
  residual is **two** named statements instead of round 142's three, one of them in negative form;
  `JSP90.attachFourResidual_of_traceCoverResidual` shows the new statement is strictly stronger than
  round 142's `AttachFourResidual`, and `JSP90.traceCoverResidual_of_attachThreeResidualRefined` shows
  it is implied by round 137's refined residual.

* **`JSP90.exists_cover_le_two_of_card_attachPoints_eq_four_of_oneTracePair`** — a *sharper* target
  than `JSP90.NoTraceK4`: at four attachment points it suffices that the trace graph has at most
  **one** edge, which is what the search measures (2 520 cases with no edge, 2 520 with exactly one,
  none with two or more).

## Measurements (`discovery/JSP-000090/r144.c`, `r144b.c`, `r144c.c`)

| question | result |
|---|---|
| `T1` are the traces of size `≤ 2`? | **no**: 27 720 traces of size 3 occur |
| `T3` `\|A\| = 4`: "no transversal pair" `↔` "trace graph `= K₄`" | 0 violations in 5 040 cases |
| `T4` `\|A\| = 4`: number of edges of the trace graph | **only 0 or 1** (2 520 each) |
| `T5` is there always a cover of size `≤ 2` inside `A`? | **0 failures** in 1 268 520 cases with `\|A\| ≥ 3` |
| `T6` `\|A\| ≥ 4`: number of transversal pairs of `A` | **5 or 6**, never fewer |
| `T7` does the trace graph ever equal `K₄`? | **never**, 0 occurrences |
| `U1` edges of the trace graph by `\|A\|` | `\|A\|=2`: always 1; `\|A\|=3`: `0,1,2,3`; `\|A\|=4`: `0,1` |
| `U2` can two odd cycles of a `LocIndep`-1 graph meet in `≥ 3` points? | **yes**, 55 800 cases |
| `U7` `\|A\| ≥ 4`, no one-point cross-over: minimum cover size | **always 1** (5 040 cases) |
| `B` is there a `LocIndep`-1 graph with `τ_odd ≥ 3`? | **no**: `r144b.c` searches **all** 55 179 262 `LocIndep`-1 graphs on 8 vertices.  (Round 143's `r143.c` pruned every branch at the root — `τ_odd < 3` is not a sound pruning rule — and was vacuous.) |

## What is *not* proved

`JSP90.TraceCoverResidual` (in particular `JSP90.NoTraceK4` and `JSP90.OneTracePair`), and behind them
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas).  `jsp_000090_main` is deliberately **not**
declared, so the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 800000

local instance traceComplexDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Part 0 — three elementary `Finset` helpers

The pinned Mathlib slice of this development has `Finset.disjoint_iff_inter_eq_empty` but not the
`inter_eq_empty_iff` / `inter_eq_self` family, so the two facts used throughout are recorded here
once. -/

/-- **NO COMMON ELEMENT.** -/
theorem traceComplex_inter_eq_empty {s t : Finset V} (h : ∀ x, x ∈ s → x ∉ t) : s ∩ t = ∅ :=
  Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_left.mpr h)

/-- **A COMMON ELEMENT.** -/
theorem traceComplex_inter_ne_empty {s t : Finset V} {x : V} (hx : x ∈ s) (hxt : x ∈ t) :
    s ∩ t ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp ⟨x, Finset.mem_inter.mpr ⟨hx, hxt⟩⟩

/-- **A SUBSET ON THE RIGHT IS ITS OWN INTERSECTION.** -/
theorem traceComplex_inter_eq_right {s t : Finset V} (h : t ⊆ s) : s ∩ t = t :=
  Finset.Subset.antisymm Finset.inter_subset_right fun x hx => Finset.mem_inter.mpr ⟨h hx, hx⟩

/-- **EMPTY INTERSECTION, SYMMETRIC FORM.** -/
theorem traceComplex_inter_eq_empty_of_comm {s t : Finset V} (h : t ∩ s = ∅) : s ∩ t = ∅ := by
  rw [Finset.inter_comm, h]

/-- **EMPTY INTERSECTION, RESTRICTED TO A SUBSET.** -/
theorem traceComplex_inter_eq_empty_of_subset_inter {s t w : Finset V} (hst : s ⊆ t)
    (h : t ∩ w = ∅) : s ∩ w = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hmem := Finset.mem_inter.mp hx
  exact ((Finset.eq_empty_iff_forall_notMem.mp h) x) (Finset.mem_inter.mpr ⟨hst hmem.1, hmem.2⟩)

/-- **EMPTY INTERSECTION, FURTHER INTERSECTED.** -/
theorem traceComplex_inter_eq_empty_of_inter_inter {s t w : Finset V} (h : s ∩ t = ∅) :
    s ∩ (t ∩ w) = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hmem := Finset.mem_inter.mp hx
  have hmem2 := Finset.mem_inter.mp hmem.2
  exact ((Finset.eq_empty_iff_forall_notMem.mp h) x) (Finset.mem_inter.mpr ⟨hmem.1, hmem2.1⟩)

/-- **A NONEMPTY SET HAS AT LEAST ONE ELEMENT.** -/
theorem traceComplex_card_pos_of_ne {s : Finset V} (h : s ≠ ∅) : 1 ≤ s.card :=
  Finset.card_pos.mpr (Finset.nonempty_of_ne_empty h)

/-- **AN EMPTY INTERSECTION WITH A COMPLEMENT.** -/
theorem traceComplex_inter_eq_empty_of_sdiff {s t : Finset V} : s \ t ∩ t = ∅ := by
  rw [Finset.inter_comm]
  exact Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_sdiff (s := t) (t := s))

/-! ## Part 1 — the trace complex

The trace of an odd cycle `D` on the attachment points of `C` is `D ∩ attachPoints G C`.  A `Set` is
used rather than a `Finset` because `IsOddCycle` is not decidable; the two-element traces are
collected separately, as a `Finset`, in Part 3. -/

/-- **THE TRACE COMPLEX OF `C`**: the traces `D ∩ attachPoints G C` of the odd cycles `D` of `G`, a
family of subsets of the attachment points. -/
noncomputable def traceFamily (G : SimpleGraph V) (C : Finset V) : Set (Finset V) :=
  { T | ∃ D : Finset V, IsOddCycle G D ∧ D ∩ attachPoints G C = T }

/-- **MEMBERSHIP IN THE TRACE COMPLEX.** -/
theorem mem_traceFamily {C T : Finset V} :
    T ∈ traceFamily G C ↔ ∃ D : Finset V, IsOddCycle G D ∧ D ∩ attachPoints G C = T := Iff.rfl

/-- **EVERY TRACE LIES IN THE ATTACHMENT POINTS.** -/
theorem subset_traceFamily_attachPoints {C T : Finset V} (hT : T ∈ traceFamily G C) :
    T ⊆ attachPoints G C := by
  obtain ⟨D, hD, rfl⟩ := hT
  exact Finset.inter_subset_right

/-- **THE TRACE OF AN ODD CYCLE IS A TRACE.** -/
theorem inter_attachPoints_mem_traceFamily {C D : Finset V} (hD : IsOddCycle G D) :
    D ∩ attachPoints G C ∈ traceFamily G C :=
  ⟨D, hD, rfl⟩

/-- **THE TRACE OF `C` ITSELF IS THE WHOLE ATTACHMENT SET.** -/
theorem attachPoints_mem_traceFamily {C : Finset V} (hC : IsOddCycle G C) :
    attachPoints G C ∈ traceFamily G C :=
  ⟨C, hC, traceComplex_inter_eq_right (subset_attachPoints_C C)⟩

/-- **AT PACKING NUMBER ONE EVERY TRACE OF AN ODD CYCLE DIFFERENT FROM `C` IS NONEMPTY.**  This is
`JSP90.inter_attachPoints_of_isOddCycle_ne_of_packing_one` in trace language; it is what rules out the
singleton traces of Part 4. -/
theorem ne_empty_of_inter_attachPoints_of_packing_one (h : PackingNumberOne G) {C D : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hD : IsOddCycle G D) (hne : D ≠ C) : D ∩ attachPoints G C ≠ ∅ :=
  inter_attachPoints_of_isOddCycle_ne_of_packing_one h hC hshort hD hne

/-- **AN ODD CYCLE AVOIDING A GIVEN SET** (the negation of `HitsOddCycles`). -/
theorem exists_oddCycle_avoid_of_not_hitsOddCycles {X : Finset V} (hf : ¬ HitsOddCycles G X) :
    ∃ D : Finset V, IsOddCycle G D ∧ D ∩ X = ∅ := by
  have hnot : ¬ (∀ D : Finset V, IsOddCycle G D → D ∩ X ≠ ∅) := hf
  push Not at hnot
  obtain ⟨D, hD, hDcap⟩ := hnot
  exact ⟨D, hD, hDcap⟩

/-- **A TRANSVERSAL MEETS EVERY ODD CYCLE.**  The trivial form, spelled out because Part 4 uses it
in the form "a set meeting every odd cycle cannot be avoided by one of them". -/
theorem hitsOddCycles_of_inter_empty {X : Finset V} (hX : HitsOddCycles G X) {D : Finset V}
    (hD : IsOddCycle G D) (hDcap : D ∩ X = ∅) : False :=
  hX D hD hDcap

/-- **A TRACE DISJOINT FROM `X` IS WITNESSED BY AN ODD CYCLE AVOIDING `X`.**  This is the whole
content of the trace language: the odd cycles of `G` are accounted for by their traces. -/
theorem exists_oddCycle_avoid_of_inter_traceFamily {X T : Finset V}
    (hX : X ⊆ attachPoints G C) (hT : T ∈ traceFamily G C) (hempty : X ∩ T = ∅) :
    ∃ D : Finset V, IsOddCycle G D ∧ D ∩ X = ∅ := by
  obtain ⟨D, hD, hTD⟩ := hT
  have h2 : T ∩ X = ∅ := by rw [Finset.inter_comm]; exact hempty
  have h3 : D ∩ X = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    have hzT : z ∈ T := by
      rw [← hTD]
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1, hX (Finset.mem_inter.mp hz).2⟩
    exact ((Finset.eq_empty_iff_forall_notMem.mp h2) z)
      (Finset.mem_inter.mpr ⟨hzT, (Finset.mem_inter.mp hz).2⟩)
  exact ⟨D, hD, h3⟩

/-! ## Part 2 — the cover–transversal duality

**THE MAIN STRUCTURAL STATEMENT OF THE ROUND.** -/

/-- **THE COVER–TRANSVERSAL DUALITY.**  If every odd cycle other than `C` meets the attachment points
— which is exactly what `PackingNumberOne` gives for a shortest odd cycle — then

```lean
X ⊆ attachPoints G C → X ≠ ∅ → (X meets every odd cycle of G) ↔ (X meets every trace of C)
```

because `X ⊆ attachPoints G C ⊆ C` gives `C ∩ X = X ≠ ∅`, and for every odd cycle `D`
`D ∩ X = (D ∩ attachPoints G C) ∩ X`.  So a set of attachment points is an odd-cycle transversal
exactly when it is a cover of the trace complex, and rounds 136–143 become a study of one object. -/
theorem hitsOddCycles_iff_covers_traceFamily {X : Finset V} (hX : X ⊆ attachPoints G C)
    (hne : X ≠ ∅)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ≠ C → (D ∩ attachPoints G C).Nonempty) :
    HitsOddCycles G X ↔ ∀ T ∈ traceFamily G C, X ∩ T ≠ ∅ := by
  constructor
  · -- a transversal meets every trace
    intro hh T hT
    obtain ⟨D, hD, hTD⟩ := hT
    rw [← hTD]
    obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty (hh D hD)
    have hmem : x ∈ D ∧ x ∈ X := Finset.mem_inter.mp hx
    exact traceComplex_inter_ne_empty hmem.2 (Finset.mem_inter.mpr ⟨hmem.1, hX hmem.2⟩)
  · -- a cover of the traces is a transversal
    intro hh D hD
    by_cases hDC : D = C
    · have hXC : X ⊆ C := hX.trans (subset_attachPoints_C C)
      rw [hDC, traceComplex_inter_eq_right hXC]
      exact hne
    · have hTfam : D ∩ attachPoints G C ∈ traceFamily G C :=
        inter_attachPoints_mem_traceFamily hD
      obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty (hh _ hTfam)
      have hmem := Finset.mem_inter.mp hx
      have hmemX : x ∈ X := (Finset.mem_inter.mp hx).left
      have hmemD : x ∈ D := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).right).left
      exact Finset.nonempty_iff_ne_empty.mp ⟨x, Finset.mem_inter.mpr ⟨hmemD, hmemX⟩⟩

/-- **THE COVER–TRANSVERSAL DUALITY AT PACKING NUMBER ONE** — the form in which the development uses
it. -/
theorem hitsOddCycles_iff_covers_traceFamily_of_packing_one (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    {X : Finset V} (hX : X ⊆ attachPoints G C) (hne : X ≠ ∅) :
    HitsOddCycles G X ↔ ∀ T ∈ traceFamily G C, X ∩ T ≠ ∅ :=
  hitsOddCycles_iff_covers_traceFamily hX hne (fun D hD hne =>
    Finset.nonempty_of_ne_empty (ne_empty_of_inter_attachPoints_of_packing_one h hC hshort hD hne))

/-- **A FAILING PAIR IS WITNESSED BY A TRACE DISJOINT FROM IT.**  This is the exact form of "no pair
of attachment points is a transversal" that Part 4 classifies. -/
theorem not_hitsOddCycles_pair_iff_exists_trace_disjoint (h : PackingNumberOne G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    {p q : V} (hne : p ≠ q) (hp : p ∈ attachPoints G C) (hq : q ∈ attachPoints G C) :
    (¬ HitsOddCycles G ({p, q} : Finset V))
      ↔ ∃ T ∈ traceFamily G C, ({p, q} : Finset V) ∩ T = ∅ := by
  constructor
  · intro hf
    obtain ⟨D, hD, hDcap⟩ := exists_oddCycle_avoid_of_not_hitsOddCycles hf
    have hDne : D ≠ C := by
      intro hDC
      have hmem : p ∈ D ∩ ({p, q} : Finset V) :=
        Finset.mem_inter.mpr ⟨by rw [hDC]; exact (mem_attachPoints.mp hp).1, by simp⟩
      rw [hDcap] at hmem
      exact absurd hmem (by simp)
    have hneT : D ∩ attachPoints G C ≠ ∅ :=
      ne_empty_of_inter_attachPoints_of_packing_one h hC hshort hD hDne
    refine ⟨D ∩ attachPoints G C, inter_attachPoints_mem_traceFamily hD, ?_⟩
    exact traceComplex_inter_eq_empty_of_inter_inter
      (s := ({p, q} : Finset V)) (t := D) (w := attachPoints G C)
      (traceComplex_inter_eq_empty_of_comm hDcap)
  · rintro ⟨T, hT, hTcap⟩ hh
    obtain ⟨D, hD, hDT⟩ := hT
    have h2 : T ∩ ({p, q} : Finset V) = ∅ := by rw [Finset.inter_comm]; exact hTcap
    have h3 : D ∩ ({p, q} : Finset V) = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have hzmem := Finset.mem_inter.mp hz
      have hzT : z ∈ T := by
        rw [← hDT]
        refine Finset.mem_inter.mpr ⟨hzmem.1, ?_⟩
        rcases mem_pair_iff.mp hzmem.2 with rfl | rfl
        · exact hp
        · exact hq
      exact ((Finset.eq_empty_iff_forall_notMem.mp h2) z) (Finset.mem_inter.mpr ⟨hzT, hzmem.2⟩)
    exact hh D hD h3

/-! ## Part 3 — the two-element traces, i.e. the edges of the trace graph -/

local instance traceComplexDecidableMem (Q : Finset V) :
    Decidable (Q ∈ traceFamily G C) := Classical.propDecidable _

/-- **THE TWO-ELEMENT TRACES.** -/
noncomputable def tracePairs (G : SimpleGraph V) (C : Finset V) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter fun Q : Finset V =>
    decide (Q.card = 2 ∧ Q ⊆ attachPoints G C ∧ Q ∈ traceFamily G C)

/-- **MEMBERSHIP IN THE TWO-ELEMENT TRACES.** -/
theorem mem_tracePairs {C Q : Finset V} :
    Q ∈ tracePairs G C ↔ Q.card = 2 ∧ Q ⊆ attachPoints G C ∧ Q ∈ traceFamily G C := by
  constructor
  · intro hQ
    exact of_decide_eq_true (Finset.mem_filter.mp hQ).2
  · rintro ⟨h1, h2, h3⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true ⟨h1, h2, h3⟩⟩

/-! ## Part 4 — **the failure of the sharp case at three or four attachment points is a NAMED
configuration** -/

/-- **A FAILING PAIR IS WITNESSED BY A TRACE INSIDE ITS COMPLEMENT.**  The general form, valid for
**any** number of attachment points: a pair `Q` of attachment points fails to be a transversal iff
some trace lies in `attachPoints G C \ Q`.

```lean
PackingNumberOne G → C a shortest odd cycle → Q ⊆ attachPoints G C → Q.card = 2 →
  (¬ HitsOddCycles G Q) ↔ ∃ T ∈ traceFamily G C, T ⊆ attachPoints G C \ Q
```

The forward direction is the trace language of "some odd cycle avoids `Q`" together with packing
number one, which makes the trace nonempty; the backward direction is
`JSP90.exists_oddCycle_avoid_of_inter_traceFamily`. -/
theorem not_hitsOddCycles_iff_exists_trace_subset_complement (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : 3 ≤ (attachPoints G C).card) {Q : Finset V} (hQ : Q.card = 2)
    (hQA : Q ⊆ attachPoints G C) :
    (¬ HitsOddCycles G Q) ↔ ∃ T ∈ traceFamily G C, T ⊆ attachPoints G C \ Q := by
  obtain ⟨p, q, hpq, hcard⟩ := Finset.card_eq_two.mp hQ
  have hsubPQ : ({p, q} : Finset V) ⊆ attachPoints G C := by rw [← hcard]; exact hQA
  have hp : p ∈ attachPoints G C := hsubPQ (mem_pair_iff.mpr (Or.inl rfl))
  have hq : q ∈ attachPoints G C := hsubPQ (mem_pair_iff.mpr (Or.inr rfl))
  constructor
  · intro hf
    have hPQ : ¬ HitsOddCycles G ({p, q} : Finset V) := fun hh => hf (hcard ▸ hh)
    obtain ⟨T, hT, hTcap⟩ :=
      (not_hitsOddCycles_pair_iff_exists_trace_disjoint h hC hshort hpq hp hq).mp hPQ
    have hQT : Q ∩ T = ∅ := by rw [hcard]; exact hTcap
    have hneT : T ≠ ∅ := by
      obtain ⟨D, hD, hTD⟩ := hT
      by_cases hDC : D = C
      · have hself : T = attachPoints G C := by
          rw [← hTD, hDC, traceComplex_inter_eq_right (subset_attachPoints_C C)]
        rw [hself]
        exact fun h0 => by
          have hh := Finset.card_eq_zero.mpr h0
          omega
      · rw [← hTD]
        exact ne_empty_of_inter_attachPoints_of_packing_one h hC hshort hD hDC
    refine ⟨T, hT, fun z hz => ?_⟩
    have hzA : z ∈ attachPoints G C := subset_traceFamily_attachPoints hT hz
    exact Finset.mem_sdiff.mpr ⟨hzA, by
      intro hz3
      exact ((Finset.eq_empty_iff_forall_notMem.mp hQT) z (Finset.mem_inter.mpr ⟨hz3, hz⟩))⟩
  · rintro ⟨T, hT, hTsub⟩ hh
    obtain ⟨D, hD, hDT⟩ := hT
    have h3 : D ∩ Q = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have hzmem := Finset.mem_inter.mp hz
      have hzT : z ∈ T := by
        rw [← hDT]
        exact Finset.mem_inter.mpr ⟨hzmem.1, hQA hzmem.2⟩
      exact absurd hzmem.2 (Finset.mem_sdiff.mp (hTsub hzT)).2
    exact hh D hD h3

/-- **AT THREE ATTACHMENT POINTS A FAILING PAIR IS EXACTLY THE SINGLETON COMPLEMENT.**  Here
`attachPoints G C \ Q` has exactly **one** element and the trace is nonempty, so it *is* the
complementary singleton — no cross-over hypothesis needed.  This is the trace-complex form of round
141's cross-over configuration `A = crossOverSet G C`. -/
theorem not_hitsOddCycles_iff_exists_trace_eq_complement_of_card_attachPoints_eq_three
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : (attachPoints G C).card = 3) {Q : Finset V} (hQ : Q.card = 2) (hQA : Q ⊆ attachPoints G C) :
    (¬ HitsOddCycles G Q) ↔ ∃ T ∈ traceFamily G C, T = attachPoints G C \ Q := by
  rw [not_hitsOddCycles_iff_exists_trace_subset_complement h hC hshort (by omega) hQ hQA]
  constructor
  · rintro ⟨T, hT, hTsub⟩
    have hcardAQ : (attachPoints G C \ Q).card = 1 := by
      have hh := Finset.card_sdiff_of_subset hQA
      rw [h3] at hh
      omega
    have hle : T.card ≤ (attachPoints G C \ Q).card := by
      refine Finset.card_le_card (s := T) (t := attachPoints G C \ Q) ?_
      intro z hz
      exact hTsub hz
    have hT' : T ∈ traceFamily G C := hT
    obtain ⟨D, hD, hTD⟩ := hT
    have hTne : T ≠ ∅ := by
      by_cases hDC : D = C
      · have hself : T = attachPoints G C := by
          rw [← hTD, hDC, traceComplex_inter_eq_right (subset_attachPoints_C C)]
        rw [hself]
        exact fun h0 => by
          have hh := Finset.card_eq_zero.mpr h0
          rw [h3] at hh
          omega
      · rw [← hTD]
        exact ne_empty_of_inter_attachPoints_of_packing_one h hC hshort hD hDC
    have hpos : 1 ≤ T.card := Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hTne)
    refine ⟨T, hT', Finset.eq_of_subset_of_card_le hTsub (by omega)⟩
  · rintro ⟨T, hT, hTcomp⟩
    exact ⟨T, hT, fun z hz => by rw [← hTcomp]; exact hz⟩

/-- **AT FOUR ATTACHMENT POINTS AND NO CROSS-OVER, A FAILING PAIR IS EXACTLY THE COMPLEMENTARY
TWO-ELEMENT TRACE** — the content of round 142's six-traces theorem, now derived from the trace
complex: `attachPoints G C \ Q` has two elements, and `JSP90.two_le_card_attachPoints_inter_of_noCrossOver_of_packing_one`
(`r144c` `U2`: the bound really is needed, since two odd cycles of a `LocIndep`-1 graph may meet in
three or four points) makes the trace have two elements as well, so it *is* the complement. -/
theorem not_hitsOddCycles_iff_mem_tracePair_of_card_attachPoints_eq_four_of_noCrossOver
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hnc : NoCrossOver G C)
    (h4 : (attachPoints G C).card = 4) {Q : Finset V} (hQ : Q.card = 2) (hQA : Q ⊆ attachPoints G C) :
    (¬ HitsOddCycles G Q) ↔ attachPoints G C \ Q ∈ tracePairs G C := by
  have hcardAQ : (attachPoints G C \ Q).card = 2 := by
    have hh := Finset.card_sdiff_of_subset hQA
    rw [h4] at hh
    omega
  constructor
  · intro hf
    obtain ⟨T, hT, hTsub⟩ :=
      (not_hitsOddCycles_iff_exists_trace_subset_complement h hC hshort (by omega) hQ hQA).mp hf
    have hT' : T ∈ traceFamily G C := hT
    obtain ⟨D, hD, hTD⟩ := hT
    have hDne : D ≠ C := by
      intro hDC
      have hself : T = attachPoints G C := by
        rw [← hTD, hDC, traceComplex_inter_eq_right (subset_attachPoints_C C)]
      have hbad : attachPoints G C ⊆ attachPoints G C \ Q := hself ▸ hTsub
      have hQ0 : Q = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
        exact absurd hz (Finset.mem_sdiff.mp (hbad (hQA hz))).2
      have hne : Q.card = 0 := Finset.card_eq_zero.mpr hQ0
      omega
    have h2le : 2 ≤ T.card := by
      have hh := two_le_card_attachPoints_inter_of_noCrossOver_of_packing_one h hC hshort hnc hD hDne
      rw [Finset.inter_comm] at hh
      rw [hTD] at hh
      exact hh
    have hle' : (attachPoints G C \ Q).card ≤ T.card := by omega
    have hTcomp : T = attachPoints G C \ Q :=
      (Finset.subset_iff_eq_of_card_le (s := T) (t := attachPoints G C \ Q) hle').mp hTsub
    refine mem_tracePairs.mpr ⟨hcardAQ, Finset.sdiff_subset, ?_⟩
    rw [← hTcomp]
    exact hT'
  · intro hTc
    obtain ⟨hTcard, hTsub, hT⟩ := mem_tracePairs.mp hTc
    obtain ⟨D', hD', hDTcap⟩ := exists_oddCycle_avoid_of_inter_traceFamily hQA hT
      (traceComplex_inter_eq_empty_of_comm
        (traceComplex_inter_eq_empty_of_sdiff (s := attachPoints G C) (t := Q)))
    exact fun hh => hh D' hD' hDTcap

/-! ### The classification of the failure, as an `iff` -/

/-- **THE SIX-TRACES CONFIGURATION**, in trace language: at four attachment points, every pair of
`attachPoints G C` occurs as a trace. -/
def TraceK4 (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ Q : Finset V, Q.card = 2 → Q ⊆ attachPoints G C → Q ∈ tracePairs G C

/-- **THE THREE SINGLETON TRACES**, in trace language: at three attachment points, every attachment
point occurs as a trace. -/
def ThreeSingletonTraces (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ a ∈ attachPoints G C, ({a} : Finset V) ∈ traceFamily G C

/-- **AN ODD CYCLE IS NONEMPTY.** -/
theorem ne_empty_of_isOddCycle {C : Finset V} (hC : IsOddCycle G C) : C ≠ ∅ := by
  rintro h0
  obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
  rw [h0] at hc
  exact absurd hc (by simp)

/-- **AT FOUR ATTACHMENT POINTS THE SHARP CASE FAILS `iff` THE SIX-TRACES CONFIGURATION OCCURS.**

```lean
PackingNumberOne G → C a shortest odd cycle → |attachPoints G C| = 4 →
  ¬ ∃ X ⊆ attachPoints G C, X.card ≤ 2 ∧ HitsOddCycles G X  ↔  TraceK4 G C
```

No `NoCrossOver` hypothesis and no cross-over analysis; see
`JSP90.not_hitsOddCycles_iff_exists_trace_complement`. -/
theorem not_cover_le_two_iff_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver
    (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) (h4 : (attachPoints G C).card = 4) :
    (¬ ∃ X : Finset V, X ⊆ attachPoints G C ∧ X.card ≤ 2 ∧ HitsOddCycles G X) ↔ TraceK4 G C := by
  constructor
  · -- no small cover: every pair fails, hence every pair is a trace
    intro hf Q hQ hQA
    have hcardAQ : (attachPoints G C \ Q).card = 2 := by
      have hh := Finset.card_sdiff_of_subset hQA
      rw [h4] at hh
      omega
    have hAeq : attachPoints G C \ (attachPoints G C \ Q) = Q := by
      ext z
      simp [hQA]
    exact hAeq ▸
      (not_hitsOddCycles_iff_mem_tracePair_of_card_attachPoints_eq_four_of_noCrossOver
        h hC hshort hnc h4 hcardAQ Finset.sdiff_subset).mp
          (fun hh => hf ⟨attachPoints G C \ Q, Finset.sdiff_subset, hcardAQ.le, hh⟩)
  · -- all six pairs are traces: no small cover
    rintro hK4 ⟨X, hXA, hX2, hXhits⟩
    by_cases hX0 : X = ∅
    · have hXempty : X = ∅ := hX0
      subst hXempty
      have hCne : C ≠ ∅ := ne_empty_of_isOddCycle hC
      exact hXhits C hC (by rw [Finset.inter_empty])
    · have hXcard : X.card = 1 ∨ X.card = 2 := by
        have hpos : 1 ≤ X.card := traceComplex_card_pos_of_ne hX0
        by_cases h1 : X.card = 1
        · exact Or.inl h1
        · exact Or.inr (by omega)
      rcases hXcard with hX1 | hX2'
      · -- a singleton cover: the edge between two other attachment points avoids it
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hX1
        have haX : a ∈ X := by rw [ha]; simp
        have haA : a ∈ attachPoints G C := hXA haX
        have hcard1 : ({a} : Finset V).card = 1 := Finset.card_singleton a
        obtain ⟨b, c, d, hbc, hbd, hcd, hsub⟩ := Finset.card_eq_three.mp (by
          have hh := Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr haA)
          rw [h4] at hh
          simp only [Finset.card_singleton] at hh
          omega)
        have hbA' : b ∈ attachPoints G C \ {a} := by rw [hsub]; simp
        have hcA' : c ∈ attachPoints G C \ {a} := by rw [hsub]; simp
        have hsubA : attachPoints G C \ {a} ⊆ attachPoints G C := Finset.sdiff_subset
        have hbA : b ∈ attachPoints G C := hsubA hbA'
        have hcA : c ∈ attachPoints G C := hsubA hcA'
        have hba : b ≠ a := by
          intro h
          exact (Finset.mem_sdiff.mp hbA').2 (Finset.mem_singleton.mpr h)
        have hca : c ≠ a := by
          intro h
          exact (Finset.mem_sdiff.mp hcA').2 (Finset.mem_singleton.mpr h)
        obtain ⟨hTcard, hTsub, hT⟩ := mem_tracePairs.mp
          (hK4 ({b, c} : Finset V) (Finset.card_eq_two.mpr ⟨b, c, hbc, rfl⟩) (by
            intro z hz
            rcases mem_pair_iff.mp hz with rfl | rfl
            · exact hbA
            · exact hcA))
        obtain ⟨D, hD, hDC⟩ := exists_oddCycle_avoid_of_inter_traceFamily (X := X) hXA hT (by
          refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
          have hzX : z ∈ X := (Finset.mem_inter.mp hz).1
          have hza : z = a := by rw [ha] at hzX; exact Finset.mem_singleton.mp hzX
          rcases mem_pair_iff.mp (Finset.mem_inter.mp hz).2 with h | h
          · exact hba (h.symm.trans hza)
          · exact hca (h.symm.trans hza))
        exact hXhits D hD hDC
      · -- a two-element cover: its complement is a trace, which avoids it
        have hcardAX : (attachPoints G C \ X).card = 2 := by
          have hh := Finset.card_sdiff_of_subset hXA
          rw [h4] at hh
          omega
        obtain ⟨hTc, hTsubc, hTc⟩ := mem_tracePairs.mp
          (hK4 (attachPoints G C \ X) hcardAX Finset.sdiff_subset)
        obtain ⟨D, hD, hDC⟩ := exists_oddCycle_avoid_of_inter_traceFamily (X := X) hXA hTc
          (traceComplex_inter_eq_empty_of_comm
            (traceComplex_inter_eq_empty_of_sdiff (s := attachPoints G C) (t := X)))
        exact hXhits D hD hDC

/-- **AT THREE ATTACHMENT POINTS THE SHARP CASE FAILS `iff` ALL THREE SINGLETON TRACES OCCUR.** -/
theorem not_cover_le_two_iff_threeSingletons_of_card_attachPoints_eq_three
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : (attachPoints G C).card = 3) :
    (¬ ∃ X : Finset V, X ⊆ attachPoints G C ∧ X.card ≤ 2 ∧ HitsOddCycles G X)
      ↔ ThreeSingletonTraces G C := by
  constructor
  · -- no small cover: the pair `A \ {a}` fails, so `{a}` is a trace
    intro hf a haA
    have hcard1 : ({a} : Finset V).card = 1 := Finset.card_singleton a
    have hcardQ : (attachPoints G C \ {a}).card = 2 := by
      have hh := Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr haA)
      rw [h3] at hh
      simp only [Finset.card_singleton] at hh
      omega
    have hsubQ : attachPoints G C \ {a} ⊆ attachPoints G C := Finset.sdiff_subset
    have hnot : ¬ HitsOddCycles G (attachPoints G C \ {a}) :=
      fun hh => hf ⟨attachPoints G C \ {a}, hsubQ, hcardQ.le, hh⟩
    obtain ⟨T, hT, hcomp⟩ :=
      (not_hitsOddCycles_iff_exists_trace_eq_complement_of_card_attachPoints_eq_three
        h hC hshort h3 hcardQ hsubQ).mp hnot
    have hAeq : attachPoints G C \ (attachPoints G C \ ({a} : Finset V)) = {a} :=
      Finset.ext fun z => by simp [haA]
    have hTa : T = {a} := by rw [hcomp]; exact hAeq
    exact hTa ▸ hT
  · -- all three singleton traces: no small cover
    rintro hS ⟨X, hXA, hX2, hXhits⟩
    by_cases hX0 : X = ∅
    · have hXempty : X = ∅ := hX0
      subst hXempty
      have hCne : C ≠ ∅ := ne_empty_of_isOddCycle hC
      exact hXhits C hC (by rw [Finset.inter_empty])
    · have hXcard : X.card = 1 ∨ X.card = 2 := by
        have hpos : 1 ≤ X.card := traceComplex_card_pos_of_ne hX0
        by_cases h1 : X.card = 1
        · exact Or.inl h1
        · exact Or.inr (by omega)
      rcases hXcard with hX1 | hX2'
      · -- a singleton cover: another attachment point gives a trace avoiding it
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hX1
        have haX : a ∈ X := by rw [ha]; simp
        have haA : a ∈ attachPoints G C := hXA haX
        have hcard1 : ({a} : Finset V).card = 1 := Finset.card_singleton a
        obtain ⟨b, hb⟩ := exists_mem_sdiff_singleton_of_card_ge_two
          (S := attachPoints G C) (by omega) (a := a)
        have hbA : b ∈ attachPoints G C := (Finset.mem_sdiff.mp hb).1
        have hba : b ≠ a := by
          intro h
          exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_singleton.mpr h)
        obtain ⟨D, hD, hDC⟩ := exists_oddCycle_avoid_of_inter_traceFamily (X := X) hXA
          (hS b hbA) (by
            refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
            have hzX : z ∈ X := (Finset.mem_inter.mp hz).1
            have hza : z = a := by rw [ha] at hzX; exact Finset.mem_singleton.mp hzX
            exact hba (Finset.mem_singleton.mp (Finset.mem_inter.mp hz).2 ▸ hza))
        exact hXhits D hD hDC
      · -- a two-element cover: the third attachment point gives a trace avoiding it
        obtain ⟨p, q, hpq, hsub⟩ := Finset.card_eq_two.mp hX2'
        have hsubA : X ⊆ attachPoints G C := hsub ▸ hXA
        have hcardAX : (attachPoints G C \ X).card = 1 := by
          have hh := Finset.card_sdiff_of_subset hsubA
          rw [h3] at hh
          omega
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcardAX
        have hcAX : c ∈ attachPoints G C \ X := by
          have hcs : c ∈ ({c} : Finset V) := by simp
          exact hc.symm ▸ hcs
        have hcA : c ∈ attachPoints G C := (Finset.mem_sdiff.mp hcAX).1
        have hcX : c ∉ X := (Finset.mem_sdiff.mp hcAX).2
        have hcp : c ∉ ({p, q} : Finset V) := hsub ▸ hcX
        obtain ⟨D, hD, hDC⟩ := exists_oddCycle_avoid_of_inter_traceFamily (X := X) hXA
          (hS c hcA) (by
            refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
            have hzc : z = c := Finset.mem_singleton.mp (Finset.mem_inter.mp hz).2
            exact hcX (hzc ▸ (Finset.mem_inter.mp hz).1))
        exact hXhits D hD hDC

/-- **THE `|A| = 4` HALF FOLLOWS FROM THE ABSENCE OF THE SIX-TRACES CONFIGURATION.** -/
theorem exists_cover_le_two_of_card_attachPoints_eq_four_of_noTraceK4 (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) (h4 : (attachPoints G C).card = 4) (hnK4 : ¬ TraceK4 G C) :
    ∃ X : Finset V, X ⊆ attachPoints G C ∧ X.card ≤ 2 ∧ HitsOddCycles G X :=
  not_not.mp (((not_cover_le_two_iff_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver
    h hC hshort hnc h4).not).mpr hnK4)

/-- **THE `|A| = 3` HALF FOLLOWS FROM THE ABSENCE OF THE THREE SINGLETON TRACES.** -/
theorem exists_cover_le_two_of_card_attachPoints_eq_three_of_noSingletonTraces
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (h3 : (attachPoints G C).card = 3)
    (hns : ¬ ThreeSingletonTraces G C) :
    ∃ X : Finset V, X ⊆ attachPoints G C ∧ X.card ≤ 2 ∧ HitsOddCycles G X :=
  not_not.mp (((not_cover_le_two_iff_threeSingletons_of_card_attachPoints_eq_three
    h hC hshort h3).not).mpr hns)

/-- **AT THREE ATTACHMENT POINTS WITH NO SINGLETON TRACE, EVERY PAIR OF ATTACHMENT POINTS IS A
TRANSVERSAL** (round 141 proved only the existence of one pair). -/
theorem hitsOddCycles_pair_of_card_attachPoints_eq_three_of_noSingletonTraces
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (h3 : (attachPoints G C).card = 3)
    (hs : ∀ a ∈ attachPoints G C, ({a} : Finset V) ∉ traceFamily G C) {Q : Finset V}
    (hQ : Q.card = 2) (hQA : Q ⊆ attachPoints G C) : HitsOddCycles G Q := by
  by_contra hf
  obtain ⟨T, hT, hcomp⟩ :=
    (not_hitsOddCycles_iff_exists_trace_eq_complement_of_card_attachPoints_eq_three
      h hC hshort h3 hQ hQA).mp hf
  have hcardT : T.card = 1 := by
    rw [hcomp]
    have hh := Finset.card_sdiff_of_subset hQA
    rw [h3] at hh
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcardT
  have haA : a ∈ attachPoints G C := subset_traceFamily_attachPoints (ha ▸ hT) (by simp)
  exact hs a haA (ha ▸ hT)

/-- **AT MOST TWO ATTACHMENT POINTS: THE ATTACHMENT SET ITSELF IS A TRANSVERSAL**, i.e. the
`|X| ≤ 2` case of the trace-cover statement. -/
theorem exists_cover_le_two_of_card_attachPoints_le_two (h : PackingNumberOne G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h2 : (attachPoints G C).card ≤ 2) (hne : (boundary G C).Nonempty) :
    ∃ X : Finset V, X ⊆ attachPoints G C ∧ X.card ≤ 2 ∧ HitsOddCycles G X :=
  ⟨attachPoints G C, Finset.Subset.rfl, h2,
    hitsOddCycles_attachPoints_of_packing_one h hC hshort hne⟩

/-! ## Part 5 — the trace-cover residual, and the sharp case from two named statements -/

/-- **THE TRACE-COVER RESIDUAL**: at `LocIndep 1`, a shortest odd cycle with at least three attachment
points has an odd-cycle transversal of size `≤ 2` *inside its attachment points*; by Part 2 this says
that the trace complex of `C` has a cover of size `≤ 2`.  This single statement replaces
`JSP90.AttachFourResidual` (which started at `4 ≤ |A|`) and absorbs the `|A| = 3` half. -/
def TraceCoverResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      3 ≤ (attachPoints G C).card →
      ∃ X : Finset W, X ⊆ attachPoints G C ∧ X.card ≤ 2 ∧ HitsOddCycles G X

/-- **THE NEGATIVE FORM OF THE `|A| = 4` HALF**: the six-traces configuration of
`JSP90.not_cover_le_two_iff_sixTraces_of_card_attachPoints_eq_four` never occurs at `LocIndep 1`.
Measured: 0 occurrences (`r144.c` `T7`); at `|A| = 4` the trace graph has at most **one** edge. -/
def NoTraceK4 : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    (∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      (attachPoints G C).card = 4 → NoCrossOver G C → ¬ TraceK4 G C) →
    CloseToBipartite 2 G

/-- **A SHARPER TARGET THAN `JSP90.NoTraceK4`**: at `LocIndep 1` the trace graph of a shortest odd
cycle with four attachment points has **at most one edge**.  Measured (`r144.c` `T4`, `r144c` `U1`):
2 520 instances with no edge and 2 520 with exactly one, none with two or more. -/
def OneTracePair : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    (∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      (attachPoints G C).card = 4 → NoCrossOver G C → (tracePairs G C).card ≤ 1) →
    CloseToBipartite 2 G

/-- **THE NEGATIVE FORM OF THE `|A| = 3` HALF**: the three singleton traces never occur at
`LocIndep 1`.  Measured `r144.c` `T2`: a singleton trace occurs exactly when there is a one-point
cross-over, so this configuration is contained in round 141's `AllCrossResidual`. -/
def NoThreeSingletonTraces : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    (∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      (attachPoints G C).card = 3 → ¬ ThreeSingletonTraces G C) →
    CloseToBipartite 2 G

/-- **THE `|A| = 4` HALF FROM `OneTracePair`** (measured as `T4`; the hypothesis is strictly weaker
than the one of `NoTraceK4`, since a trace graph with two or three edges is not excluded). -/
theorem exists_cover_le_two_of_card_attachPoints_eq_four_of_oneTracePair (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) (h4 : (attachPoints G C).card = 4) (hone : (tracePairs G C).card ≤ 1) :
    ∃ X : Finset V, X ⊆ attachPoints G C ∧ X.card ≤ 2 ∧ HitsOddCycles G X := by
  have hnK4 : ¬ TraceK4 G C := by
    rintro hK4
    obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hsub⟩ := Finset.card_eq_four.mp h4
    have hpA : p ∈ attachPoints G C := by rw [hsub]; simp
    have hqA : q ∈ attachPoints G C := by rw [hsub]; simp
    have hrA : r ∈ attachPoints G C := by rw [hsub]; simp
    have hsA : s ∈ attachPoints G C := by rw [hsub]; simp
    have hsubPQ : ({p, q} : Finset V) ⊆ attachPoints G C := by
      intro z hz
      rcases mem_pair_iff.mp hz with rfl | rfl
      · exact hpA
      · exact hqA
    have hsubRS : ({r, s} : Finset V) ⊆ attachPoints G C := by
      intro z hz
      rcases mem_pair_iff.mp hz with rfl | rfl
      · exact hrA
      · exact hsA
    have hne : ({p, q} : Finset V) ≠ ({r, s} : Finset V) := by
      intro hcon
      have hpq' : p ∈ ({r, s} : Finset V) := by rw [← hcon]; simp
      rcases mem_pair_iff.mp hpq' with h | h
      · exact hpr h
      · exact hps h
    have h1 : ({p, q} : Finset V) ∈ tracePairs G C :=
      hK4 _ (Finset.card_eq_two.mpr ⟨p, q, hpq, rfl⟩) hsubPQ
    have h2 : ({r, s} : Finset V) ∈ tracePairs G C :=
      hK4 _ (Finset.card_eq_two.mpr ⟨r, s, hrs, rfl⟩) hsubRS
    have h2le : 2 ≤ (tracePairs G C).card := two_le_card_of_mem_pair hne h1 h2
    omega
  exact exists_cover_le_two_of_card_attachPoints_eq_four_of_noTraceK4 h hC hshort hnc h4 hnK4

/-- **THE SHARP CASE `Erdős73On 1 2` FROM ROUND 141's `|A| = 3` HALF AND THE TRACE-COVER RESIDUAL.**
This is the reduction of the round: **two** named statements, instead of round 142's three. -/
theorem erdos73On_one_two_of_allCrossResidual_and_traceCoverResidual
    (hA : AllCrossResidual.{u}) (hT : TraceCoverResidual.{u}) : Erdős73On.{u} 1 2 := by
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
      · by_cases h3 : (attachPoints G C).card ≤ 3
        · by_cases heq : attachPoints G C = crossOverSet G C
          · exact hA W instW G hG C hC hshort (by omega) heq
          · exact (closeToBipartite_iff_hitsOddCycles (V := W) (G := G) (m := 2)).mp
              (erdos73On_one_two_of_card_attachPoints_le_three_of_ne_crossOverSet hG hC hshort
                h3 heq)
        · obtain ⟨X, hX, hX2, hh⟩ := hT W instW G hG C hC hshort (by omega)
          exact ⟨X, hX2, fun D hD => hh D hD⟩
    · have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hh : HitsOddCycles G ({c} : Finset W) := by
        simpa [h0] using hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc
      exact ⟨{c}, by simp, hh⟩
  · exact ⟨∅, by simp, fun D hD => absurd ⟨D, hD⟩ hex⟩

/-- **THE TRACE-COVER RESIDUAL IS IMPLIED BY ROUND 137's REFINED RESIDUAL.** -/
theorem traceCoverResidual_of_attachThreeResidualRefined (h : AttachThreeResidualRefined.{u}) :
    TraceCoverResidual.{u} := by
  intro W instW G hG C hC hshort h3
  obtain ⟨a, b, hab, ha, hb, hh⟩ := h W instW G hG C hC hshort h3
  have hab' : ({a, b} : Finset W).card = 2 := Finset.card_eq_two.mpr ⟨a, b, hab, rfl⟩
  refine ⟨{a, b}, ?_, hab'.le, hh⟩
  intro z hz
  rcases mem_pair_iff.mp hz with rfl | rfl
  · exact ha
  · exact hb

/-- **THE TRACE-COVER RESIDUAL IMPLIES ROUND 142's `AttachFourResidual`.**  So the new statement is
strictly stronger (it also settles `|A| = 3`), and still unproved; it is the sharpest single
formulation of the residual. -/
theorem attachFourResidual_of_traceCoverResidual (h : TraceCoverResidual.{u}) :
    AttachFourResidual.{u} := by
  intro W instW G hG C hC hshort h4
  obtain ⟨X, hX, hX2, hh⟩ := h W instW G hG C hC hshort (by omega)
  by_cases hX0 : X = ∅
  · have hXempty : X = ∅ := hX0
    subst hXempty
    have hfalse : False := hh C hC (by rw [Finset.inter_empty])
    exact hfalse.elim
  · by_cases hX1 : X.card = 1
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hX1
      have haX : a ∈ X := by rw [ha]; simp
      have haA : a ∈ attachPoints G C := hX haX
      obtain ⟨b, hb⟩ := exists_mem_sdiff_singleton_of_card_ge_two
        (S := attachPoints G C) (by omega) (a := a)
      have hab : a ≠ b := by
        intro h
        exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_singleton.mpr h.symm)
      have hbA : b ∈ attachPoints G C := (Finset.mem_sdiff.mp hb).1
      have haab : a ∈ ({a, b} : Finset W) := mem_pair_iff.mpr (Or.inl rfl)
      refine ⟨a, b, hab, haA, hbA, fun D hD => ?_⟩
      have hne : D ∩ X ≠ ∅ := hh D hD
      obtain ⟨z, hz⟩ := Finset.nonempty_of_ne_empty hne
      have hzX : z ∈ X := (Finset.mem_inter.mp hz).2
      have hza : z = a := by rw [ha] at hzX; exact Finset.mem_singleton.mp hzX
      have hzD : a ∈ D := by rw [← hza]; exact (Finset.mem_inter.mp hz).1
      exact Finset.nonempty_iff_ne_empty.mp ⟨a, Finset.mem_inter.mpr ⟨hzD, haab⟩⟩
    · have hpos : 1 ≤ X.card := traceComplex_card_pos_of_ne hX0
      have hcard2 : X.card = 2 := by omega
      obtain ⟨a, b, hab, hXeq⟩ := Finset.card_eq_two.mp hcard2
      have haX : a ∈ X := by rw [hXeq]; simp
      have hbX : b ∈ X := by rw [hXeq]; simp
      refine ⟨a, b, hab, hX haX, hX hbX, fun D hD => ?_⟩
      rw [hXeq.symm]
      exact hh D hD

#print axioms JSP90.traceComplex_inter_eq_empty
#print axioms JSP90.traceComplex_inter_ne_empty
#print axioms JSP90.mem_traceFamily
#print axioms JSP90.subset_traceFamily_attachPoints
#print axioms JSP90.inter_attachPoints_mem_traceFamily
#print axioms JSP90.attachPoints_mem_traceFamily
#print axioms JSP90.ne_empty_of_inter_attachPoints_of_packing_one
#print axioms JSP90.exists_oddCycle_avoid_of_not_hitsOddCycles
#print axioms JSP90.hitsOddCycles_of_inter_empty
#print axioms JSP90.exists_oddCycle_avoid_of_inter_traceFamily
#print axioms JSP90.hitsOddCycles_iff_covers_traceFamily
#print axioms JSP90.hitsOddCycles_iff_covers_traceFamily_of_packing_one
#print axioms JSP90.not_hitsOddCycles_pair_iff_exists_trace_disjoint
#print axioms JSP90.mem_tracePairs
#print axioms JSP90.not_hitsOddCycles_iff_exists_trace_subset_complement
#print axioms JSP90.not_hitsOddCycles_iff_exists_trace_eq_complement_of_card_attachPoints_eq_three
#print axioms JSP90.not_hitsOddCycles_iff_mem_tracePair_of_card_attachPoints_eq_four_of_noCrossOver
#print axioms JSP90.ne_empty_of_isOddCycle
#print axioms JSP90.not_cover_le_two_iff_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver
#print axioms JSP90.not_cover_le_two_iff_threeSingletons_of_card_attachPoints_eq_three
#print axioms JSP90.exists_cover_le_two_of_card_attachPoints_eq_four_of_noTraceK4
#print axioms JSP90.exists_cover_le_two_of_card_attachPoints_eq_three_of_noSingletonTraces
#print axioms JSP90.hitsOddCycles_pair_of_card_attachPoints_eq_three_of_noSingletonTraces
#print axioms JSP90.exists_cover_le_two_of_card_attachPoints_le_two
#print axioms JSP90.exists_cover_le_two_of_card_attachPoints_eq_four_of_oneTracePair
#print axioms JSP90.erdos73On_one_two_of_allCrossResidual_and_traceCoverResidual
#print axioms JSP90.traceCoverResidual_of_attachThreeResidualRefined
#print axioms JSP90.attachFourResidual_of_traceCoverResidual

/-! ## What is *not* proved

`JSP90.TraceCoverResidual`, and behind it `JSP90.NoTraceK4`, `JSP90.OneTracePair`,
`JSP90.NoThreeSingletonTraces` and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas).
`jsp_000090_main` is deliberately not declared. -/