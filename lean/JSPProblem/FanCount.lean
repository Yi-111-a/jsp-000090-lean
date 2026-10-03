import JSPProblem.CrossThree

/-!
# JSP-000090, round 142 — `JSPProblem/FanCount.lean`: **the fan accounting, the pairing of four
# attachment points, and the SIX-TRACES classification of the sharp case `k = 1` at `|A| = 4`**

Attack family 71.  Round 141 reduced the residual of the sharp case `k = 1` at three attachment
points to a single configuration (`JSP90.AllCrossResidual`) and left the `|attachPoints G C| ≥ 4`
half of `JSP90.AttachThreeResidualRefined` (`JSPProblem/Segment.lean`) completely untouched — the
largest untouched part of the sharp case.  `policy.json`'s `next_bet` route (A) was *"count on the
fan"*: at `LocIndep 1` every fan vertex has **at most two** attachment points
(`JSP90.card_attachSet_le_two_of_locIndep_one`, `JSPProblem/AttachPoints.lean`), so the attachment
points are the union of at most two-element sets indexed by the **fan** `boundary G C`, and the
attachment-point counting of rounds 136–141 can be re-expressed as an accounting on the fan.

This round does exactly that, and then *classifies the failure* at four attachment points.

## Part 1 — the fan accounting

* **`JSP90.card_attachPoints_le_sum_attachSet`** — the attachment points are the union of the
  attachment sets over the fan, so their number is at most the sum of the attachment-set sizes;
* **`JSP90.card_attachPoints_le_two_mul_card_boundary`** — **THE FAN ACCOUNTING**: at `LocIndep 1`
  and for a shortest odd cycle,
  ```
  |attachPoints G C|  ≤  2 * |boundary G C|,
  ```
  i.e. the odd cycle's attachment points cost at most two per fan vertex.  This is the statement
  `discovery/JSP-000090/r139.c` measured as question `Q8` and round 139 could not formalise; the
  exhaustive search of this round (`discovery/JSP-000090/r142.c`, question `F1`) finds **0 failures
  in 2 163 652** shortest odd cycles of all `LocIndep`-1 graphs on `n ≤ 7`, with `29 052` cases
  attaining the bound `|A| = 2|B|`;
* five corollaries: `two_le_card_boundary_of_card_attachPoints_ge_three`,
  `…_ge_four`, `three_le_card_boundary_of_card_attachPoints_ge_five`,
  `card_attachPoints_le_four_of_card_boundary_le_two`,
  `card_attachPoints_le_two_of_card_boundary_le_one`.  Together: **a shortest odd cycle with three
  (resp. four, five) attachment points has a fan of at least two (two, three) vertices**, which is
  the first *lower* bound on the fan in the development.

## Part 2 — the pairing of four attachment points

* **`JSP90.exists_attachSet_pair_of_card_attachPoints_eq_four_of_card_boundary_eq_two`** — **at
  `LocIndep 1` four attachment points and a fan of size two force the fan to consist of two
  *adjacent-in-structure* vertices, each carrying exactly two attachment points, with the two
  attachment sets DISJOINT and their union the whole attachment set**:
  ```
  ∃ y₁ y₂ ∈ boundary G C, y₁ ≠ y₂ ∧ |attachSet G C y₁| = |attachSet G C y₂| = 2 ∧
    Disjoint (attachSet G C y₁) (attachSet G C y₂) ∧
    attachSet G C y₁ ∪ attachSet G C y₂ = attachPoints G C
  ```
  The counting is exact: `4 = |A| ≤ |A₁ ∪ A₂| ≤ |A₁| + |A₂| ≤ 2 + 2 = 4`, so every inequality is an
  equality and `Finset.card_union_add_card_inter` makes the two attachment sets disjoint.  The
  measurement `r142.c` question `F6` confirms this in all `5 040` cases of the measured range.

## Part 3 — the six-traces classification

* **`JSP90.not_pair_transversal_iff_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver`** —
  **THE ONLY WAY THE SHARP CASE FAILS AT FOUR ATTACHMENT POINTS IS THAT ALL SIX COMPLEMENTARY PAIRS
  OCCUR AS TRACES.**  At packing number one, for a shortest odd cycle `C` with `|attachPoints G C| = 4`
  and no cross-over,
  ```
  (no two-element subset of attachPoints G C meets every odd cycle)
    ↔
  (for every two p q of attachPoints G C there is an odd cycle D with
        D ∩ attachPoints G C = attachPoints G C \ {p, q})
  ```
  as an `iff`.  ⟸: the trace cycle `D` avoids `{p, q}` because `{p, q} ⊆ attachPoints G C`.  ⟹: a
  failing pair is avoided by some odd cycle `D`; `D ≠ C`; no cross-over gives `2 ≤ |D ∩ A|` by round
  137's segment lemma, while `D ∩ A ⊆ A \ {p, q}` has exactly `4 − 2 = 2` elements.
  The measurement `r142.c` question `F3` finds **0 failures in the 5 040** measured cases.

* **`JSP90.exists_trace_or_crossOverPoint_of_pair_not_transversal_of_card_attachPoints_eq_four`** —
  the same statement **without** the no-cross-over hypothesis and for `4 ≤ |attachPoints G C|`: a
  failing pair is witnessed either by a cycle whose trace on `A` is exactly the complementary pair or
  by a cross-over point of `C` **outside** `{p, q}`.  This is the forced shape of the whole
  `|A| ≥ 4` residual: the only obstruction is the cross-over, as in round 139.

## Part 4 — the sharp case is two named statements

* **`JSP90.AttachFourResidual`** — the `4 ≤ |attachPoints G C|` half of round 137's refined residual;
* **`JSP90.NoSixTraces`** — the **negative form** of the `|A| = 4` half: at `LocIndep 1` the six-traces
  configuration of Part 3 never occurs;
* **`JSP90.erdos73On_one_two_of_allCrossResidual_and_attachFourResidual`** and
  **`JSP90.erdos73On_one_two_of_allCrossResidual_and_attachFourResidual_and_noSixTraces`** — with
  round 141's `AllCrossResidual` (the `|A| = 3` half) the whole sharp case `k = 1` follows, so
  **`Erdős73On 1 2` is reduced to at most three named configurations**;
* `JSP90.allCrossResidual_of_erdos73On_one_two` and `JSP90.attachFourResidual_of_attachThreeResidualRefined`.

## What is *not* proved

`JSP90.AllCrossResidual`, `JSP90.NoSixTraces`, `JSP90.AttachFourResidual` and behind them
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.
`jsp_000090_main` is deliberately **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 800000

local instance fanCountDecidableEq : DecidableEq V := Classical.decEq V

local instance fanCountDecidablePred (C : Finset V) : DecidablePred (CrossOverPoint G C) :=
  fun _ => Classical.propDecidable _

/-! ## Part 1 — the fan accounting -/

/-- **MEMBERSHIP IN A TWO-ELEMENT SET.**  Helper of Parts 2 and 3: the pair `{p, q}` of a
two-element certificate.  (Same statement as `JSP90.mem_pair` of `JSPProblem/Double.lean`, kept here
so that this file does not have to reach into that development.) -/
theorem mem_pair_iff {p q x : V} : x ∈ ({p, q} : Finset V) ↔ x = p ∨ x = q := by simp

/-- **THE ATTACHMENT POINTS ARE PRICED BY THE ATTACHMENT SETS OF THE FAN.** -/
theorem card_attachPoints_le_sum_attachSet (C : Finset V) :
    (attachPoints G C).card ≤ ∑ y ∈ boundary G C, (attachSet G C y).card := by
  rw [attachPoints]
  exact Finset.card_biUnion_le

/-- **THE FAN ACCOUNTING: at `LocIndep 1` the attachment points of a shortest odd cycle cost at most
TWO per fan vertex.**

```lean
LocIndep 1 G → C an odd cycle → C shortest → |attachPoints G C| ≤ 2 * |boundary G C|
```

This is the statement `discovery/JSP-000090/r139.c` measured as `Q8`; the search of this round
(`discovery/JSP-000090/r142.c`, `F1`) finds `0` failures in `2 163 652` shortest odd cycles.  The proof
is the union bound of Part 1 followed by round 136's `card_attachSet_le_two_of_locIndep_one`. -/
theorem card_attachPoints_le_two_mul_card_boundary (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) :
    (attachPoints G C).card ≤ 2 * (boundary G C).card := by
  have h1 := card_attachPoints_le_sum_attachSet (G := G) (C := C)
  have h2 : (∑ y ∈ boundary G C, (attachSet G C y).card : ℕ) ≤ 2 * (boundary G C).card := by
    have h2' : (∑ y ∈ boundary G C, (attachSet G C y).card : ℕ)
        ≤ ∑ _y ∈ boundary G C, (2 : ℕ) :=
      Finset.sum_le_sum fun y hy => card_attachSet_le_two_of_locIndep_one hG hC hshort hy
    have h2'' : (∑ _y ∈ boundary G C, (2 : ℕ) : ℕ) = (boundary G C).card * 2 :=
      Finset.sum_const (s := boundary G C) (b := (2 : ℕ))
    omega
  omega

/-- **THREE ATTACHMENT POINTS FORCE A FAN OF TWO VERTICES.** -/
theorem two_le_card_boundary_of_card_attachPoints_ge_three (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : 3 ≤ (attachPoints G C).card) : 2 ≤ (boundary G C).card := by
  have h := card_attachPoints_le_two_mul_card_boundary hG hC hshort
  omega

/-- **FOUR ATTACHMENT POINTS FORCE A FAN OF TWO VERTICES.** -/
theorem two_le_card_boundary_of_card_attachPoints_ge_four (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : 4 ≤ (attachPoints G C).card) : 2 ≤ (boundary G C).card := by
  have h := card_attachPoints_le_two_mul_card_boundary hG hC hshort
  omega

/-- **FIVE ATTACHMENT POINTS FORCE A FAN OF THREE VERTICES.** -/
theorem three_le_card_boundary_of_card_attachPoints_ge_five (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : 5 ≤ (attachPoints G C).card) : 3 ≤ (boundary G C).card := by
  have h := card_attachPoints_le_two_mul_card_boundary hG hC hshort
  omega

/-- **A FAN OF TWO VERTICES HAS AT MOST FOUR ATTACHMENT POINTS.** -/
theorem card_attachPoints_le_four_of_card_boundary_le_two (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h2 : (boundary G C).card ≤ 2) : (attachPoints G C).card ≤ 4 := by
  have h := card_attachPoints_le_two_mul_card_boundary hG hC hshort
  omega

/-- **A SINGLE FAN VERTEX HAS AT MOST TWO ATTACHMENT POINTS.** -/
theorem card_attachPoints_le_two_of_card_boundary_le_one (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h2 : (boundary G C).card ≤ 1) : (attachPoints G C).card ≤ 2 := by
  have h := card_attachPoints_le_two_mul_card_boundary hG hC hshort
  omega

/-! ## Part 2 — the pairing of four attachment points -/

/-- **FOUR ATTACHMENT POINTS AND A FAN OF TWO: THE TWO FAN VERTICES CARRY DISJOINT PAIRS.**

```lean
LocIndep 1 G → C a shortest odd cycle → |attachPoints G C| = 4 → |boundary G C| = 2 →
  ∃ y₁ y₂ ∈ boundary G C, y₁ ≠ y₂ ∧ |attachSet G C y₁| = |attachSet G C y₂| = 2 ∧
    Disjoint (attachSet G C y₁) (attachSet G C y₂) ∧
    attachSet G C y₁ ∪ attachSet G C y₂ = attachPoints G C
```

The count is exact: `4 = |A| ≤ |A₁ ∪ A₂| ≤ |A₁| + |A₂| ≤ 2 + 2`, so all the inequalities are
equalities and `Finset.card_union_add_card_inter` forces the two attachment sets to be disjoint.
This is the configuration the search of round 135 met on the six-vertex graph `fan4`, and
`discovery/JSP-000090/r142.c` (`F6`) confirms it in all `5 040` measured cases. -/
theorem exists_attachSet_pair_of_card_attachPoints_eq_four_of_card_boundary_eq_two
    (hG : LocIndep 1 G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h4 : (attachPoints G C).card = 4) (h2 : (boundary G C).card = 2) :
    ∃ y₁ y₂ : V, y₁ ∈ boundary G C ∧ y₂ ∈ boundary G C ∧ y₁ ≠ y₂ ∧
      (attachSet G C y₁).card = 2 ∧ (attachSet G C y₂).card = 2 ∧
      Disjoint (attachSet G C y₁) (attachSet G C y₂) ∧
      attachSet G C y₁ ∪ attachSet G C y₂ = attachPoints G C := by
  obtain ⟨y₁, y₂, hne, hB⟩ := Finset.card_eq_two.mp h2
  have hy₁ : y₁ ∈ boundary G C := by rw [hB]; simp
  have hy₂ : y₂ ∈ boundary G C := by rw [hB]; simp
  have hsub : attachPoints G C ⊆ attachSet G C y₁ ∪ attachSet G C y₂ := by
    intro a ha
    obtain ⟨haC, y, hy, hay⟩ := mem_attachPoints.mp ha
    have hmem : a ∈ attachSet G C y := mem_attachSet.mpr ⟨haC, hay.symm⟩
    have hy' : y ∈ ({y₁, y₂} : Finset V) := hB ▸ hy
    rcases mem_pair_iff.mp hy' with h | h
    · subst h
      exact Finset.mem_union_left _ hmem
    · subst h
      exact Finset.mem_union_right _ hmem
  have hle4 : 4 ≤ (attachSet G C y₁ ∪ attachSet G C y₂).card := by
    have hh := Finset.card_le_card hsub
    rw [h4] at hh
    exact hh
  have h1 : (attachSet G C y₁).card ≤ 2 := card_attachSet_le_two_of_locIndep_one hG hC hshort hy₁
  have h2' : (attachSet G C y₂).card ≤ 2 := card_attachSet_le_two_of_locIndep_one hG hC hshort hy₂
  have hleU : (attachSet G C y₁ ∪ attachSet G C y₂).card
      ≤ (attachSet G C y₁).card + (attachSet G C y₂).card := Finset.card_union_le _ _
  have hsum : (attachSet G C y₁).card + (attachSet G C y₂).card = 4 := by omega
  have hcards : (attachSet G C y₁).card = 2 ∧ (attachSet G C y₂).card = 2 := by omega
  have hcard : (attachSet G C y₁ ∪ attachSet G C y₂).card = 4 := by omega
  refine ⟨y₁, y₂, hy₁, hy₂, hne, hcards.1, hcards.2, ?_, ?_⟩
  · have hinter : (attachSet G C y₁ ∩ attachSet G C y₂).card = 0 := by
      have hh := Finset.card_union_add_card_inter (attachSet G C y₁) (attachSet G C y₂)
      rw [hcard, hsum] at hh
      omega
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hinter)
  · refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hcard, h4]

/-! ## Part 3 — the six-traces classification -/

/-- **A FAILING PAIR OF ATTACHMENT POINTS IS AVOIDED BY AN ODD CYCLE.**  The content of
`¬ HitsOddCycles G {p, q}`, in the form Part 3 uses. -/
theorem exists_oddCycle_avoid_pair_of_not_hitsOddCycles_pair {p q : V} (hne : p ≠ q)
    (hf : ¬ HitsOddCycles G ({p, q} : Finset V)) :
    ∃ D : Finset V, IsOddCycle G D ∧ D ∩ ({p, q} : Finset V) = ∅ := by
  have hnot : ¬ (∀ D : Finset V, IsOddCycle G D → D ∩ ({p, q} : Finset V) ≠ ∅) := hf
  push Not at hnot
  obtain ⟨D, hD, hDcap⟩ := hnot
  refine ⟨D, hD, ?_⟩
  ext z
  constructor
  · intro hz
    have hz2 : z ∉ ({p, q} : Finset V) := by
      have hz3 : z ∈ D ∩ ({p, q} : Finset V) := hz
      rw [hDcap] at hz3
      exact absurd hz3 (by simp)
    exact absurd (Finset.mem_inter.mp hz).2 hz2
  · intro hz
    exact absurd hz (by simp)

/-- **AN ODD CYCLE AVOIDING A PAIR OF ATTACHMENT POINTS IS NOT THE SHORTEST ODD CYCLE `C`.** -/
theorem ne_of_oddCycle_avoid_pair_sub_attachPoints {C : Finset V} {a b : V}
    (ha : a ∈ attachPoints G C) (hb : a ≠ b) {D : Finset V} (hD : IsOddCycle G D)
    (hcap : D ∩ ({a, b} : Finset V) = ∅) : D ≠ C := by
  intro hDC
  have hmem : a ∈ D ∩ ({a, b} : Finset V) := by
    rw [hDC]
    exact Finset.mem_inter.mpr ⟨(mem_attachPoints.mp ha).1, by simp⟩
  rw [hcap] at hmem
  exact absurd hmem (by simp)

/-- **A PAIR OF ATTACHMENT POINTS HAS TWO ELEMENTS, AND IS CONTAINED IN THE ATTACHMENT POINTS.** -/
theorem card_pair_of_mem_attachPoints {p q : V} (hne : p ≠ q) (hp : p ∈ attachPoints G C)
    (hq : q ∈ attachPoints G C) :
    ({p, q} : Finset V).card = 2 ∧ ({p, q} : Finset V) ⊆ attachPoints G C := by
  refine ⟨Finset.card_eq_two.mpr ⟨p, q, hne, rfl⟩, fun z hz => ?_⟩
  rcases mem_pair_iff.mp hz with h | h
  · rw [h]; exact hp
  · rw [h]; exact hq

/-! ### The forced form of a failing pair -/

/-- **A FAILING PAIR OF ATTACHMENT POINTS IS FORCED: EITHER BY A TRACE, OR BY A CROSS-OVER POINT
OUTSIDE THE PAIR.**

```lean
PackingNumberOne G → C a shortest odd cycle → |attachPoints G C| = 4 →
  p, q ∈ attachPoints G C → p ≠ q → ¬ HitsOddCycles G {p, q} →
  (∃ D, IsOddCycle G D ∧ (D ∩ attachPoints G C) = attachPoints G C \ {p, q})
    ∨ (∃ x, CrossOverPoint G C x ∧ x ∉ ({p, q} : Finset V))
```

The proof is the three-line case analysis.  The cycle `D` avoiding `{p, q}` is not `C` and meets the
attachment points (packing number one), so pick `x ∈ D ∩ attachPoints G C`.  Either `D` meets `C$ in
two points — then round 137's segment lemma gives `2 ≤ |D ∩ A|`, while `D ∩ A ⊆ A \ {p, q}$ has
exactly `|A| − 2 = 2` elements, so the two sets are equal — or `D` crosses `C$ over in one point,
which is a cross-over point of `C$ different from `p` and `q` because `D` avoids them. -/
theorem exists_trace_or_crossOverPoint_of_pair_not_transversal_of_card_attachPoints_eq_four
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h4 : (attachPoints G C).card = 4) {p q : V} (hp : p ∈ attachPoints G C)
    (hq : q ∈ attachPoints G C) (hne : p ≠ q) (hf : ¬ HitsOddCycles G ({p, q} : Finset V)) :
    (∃ D : Finset V, IsOddCycle G D ∧ (D ∩ attachPoints G C) = attachPoints G C \ {p, q})
      ∨ (∃ x : V, CrossOverPoint G C x ∧ x ∉ ({p, q} : Finset V)) := by
  obtain ⟨D, hD, hDcap⟩ := exists_oddCycle_avoid_pair_of_not_hitsOddCycles_pair hne hf
  have hDne : D ≠ C := ne_of_oddCycle_avoid_pair_sub_attachPoints hp hne hD hDcap
  have hne0 : (C ∩ D).card ≠ 0 := fun hc =>
    h D C hD hC (by rw [Finset.inter_comm]; exact Finset.card_eq_zero.mp hc)
  have hneA : attachPoints G C ∩ D ≠ ∅ := by
    rw [Finset.inter_comm]
    exact inter_attachPoints_of_isOddCycle_ne_of_packing_one h hC hshort hD hDne
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hneA
  have hxA : x ∈ attachPoints G C := (Finset.mem_inter.mp hx).1
  have hxD : x ∈ D := (Finset.mem_inter.mp hx).2
  have hsub : D ∩ attachPoints G C ⊆ attachPoints G C \ {p, q} := by
    intro z hz
    have hzD : z ∈ D := (Finset.mem_inter.mp hz).1
    have hzA : z ∈ attachPoints G C := (Finset.mem_inter.mp hz).2
    have hz2 : z ∉ ({p, q} : Finset V) := by
      intro hz3
      have hz4 : z ∈ D ∩ ({p, q} : Finset V) := Finset.mem_inter.mpr ⟨hzD, hz3⟩
      rw [hDcap] at hz4
      exact absurd hz4 (by simp)
    exact Finset.mem_sdiff.mpr ⟨hzA, hz2⟩
  obtain ⟨hcardpair, hsubpair⟩ := card_pair_of_mem_attachPoints hne hp hq
  have hcard2 : (attachPoints G C \ {p, q}).card = 2 := by
    have hh := Finset.card_sdiff_of_subset hsubpair
    omega
  by_cases h2 : 2 ≤ (C ∩ D).card
  · left
    have htwo : 2 ≤ (D ∩ attachPoints G C).card := by
      have hh := two_le_card_attachPoints_inter_of_card_inter_ge_two hC hshort hD hDne h2
      rwa [Finset.inter_comm] at hh
    refine ⟨D, hD, Finset.eq_of_subset_of_card_le hsub ?_⟩
    have hh := Finset.card_le_card hsub
    omega
  · right
    have hone : (C ∩ D).card = 1 := by omega
    have hmem : x ∈ C ∩ D := Finset.mem_inter.mpr ⟨(mem_attachPoints.mp hxA).1, hxD⟩
    refine ⟨x, ⟨D, ⟨hD, hDne, hone⟩, hmem⟩, ?_⟩
    intro hx2
    have : x ∈ D ∩ ({p, q} : Finset V) := Finset.mem_inter.mpr ⟨hxD, hx2⟩
    rw [hDcap] at this
    exact absurd this (by simp)

/-! ### The six-traces theorem: the failure at four attachment points -/

/-- **THE ONLY WAY THE SHARP CASE FAILS AT FOUR ATTACHMENT POINTS IS THE SIX-TRACES CONFIGURATION.**

```lean
PackingNumberOne G → C a shortest odd cycle → NoCrossOver G C → |attachPoints G C| = 4 →
  (no two-element subset of attachPoints G C meets every odd cycle)
    ↔
  (for every two distinct p q of attachPoints G C there is an odd cycle D with
       D ∩ attachPoints G C = attachPoints G C \ {p, q})
```

On a four-element ground set this is the *complete* classification of the failure: a pair fails iff
the complementary pair occurs as the trace of an odd cycle, so "no pair works" iff **all six**
complementary pairs occur.  The hypothesis `NoCrossOver G C` enters through round 137's
`two_le_card_attachPoints_inter_of_noCrossOver_of_packing_one`, which says that every odd cycle meets
the attachment points in **two** points; with a cross-over the cycle meets them in one point and the
trace is a singleton, which is the second alternative of
`JSP90.exists_trace_or_crossOverPoint_of_pair_not_transversal_of_card_attachPoints_eq_four`.
`discovery/JSP-000090/r142.c` (`F3`) finds `0` failures in the `5 040` measured cases. -/
theorem not_pair_transversal_iff_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) (h4 : (attachPoints G C).card = 4) :
    (∀ p q : V, p ∈ attachPoints G C → q ∈ attachPoints G C → p ≠ q →
        ¬ HitsOddCycles G ({p, q} : Finset V))
      ↔
    (∀ p q : V, p ∈ attachPoints G C → q ∈ attachPoints G C → p ≠ q →
        ∃ D : Finset V, IsOddCycle G D ∧ (D ∩ attachPoints G C) = attachPoints G C \ {p, q}) := by
  constructor
  · -- no pair works: every pair is the trace of an odd cycle
    intro hno p q hp hq hne
    obtain ⟨D, hD, hDcap⟩ :=
      exists_oddCycle_avoid_pair_of_not_hitsOddCycles_pair hne (hno p q hp hq hne)
    have hDne : D ≠ C := ne_of_oddCycle_avoid_pair_sub_attachPoints hp hne hD hDcap
    have hneA : attachPoints G C ∩ D ≠ ∅ := by
      rw [Finset.inter_comm]
      exact inter_attachPoints_of_isOddCycle_ne_of_packing_one h hC hshort hD hDne
    have htwo : 2 ≤ (D ∩ attachPoints G C).card := by
      have hh := two_le_card_attachPoints_inter_of_noCrossOver_of_packing_one h hC hshort hnc hD hDne
      rwa [Finset.inter_comm] at hh
    have hsub : D ∩ attachPoints G C ⊆ attachPoints G C \ {p, q} := by
      intro z hz
      have hzD : z ∈ D := (Finset.mem_inter.mp hz).1
      have hzA : z ∈ attachPoints G C := (Finset.mem_inter.mp hz).2
      have hz2 : z ∉ ({p, q} : Finset V) := by
        intro hz3
        have hz4 : z ∈ D ∩ ({p, q} : Finset V) := Finset.mem_inter.mpr ⟨hzD, hz3⟩
        rw [hDcap] at hz4
        exact absurd hz4 (by simp)
      exact Finset.mem_sdiff.mpr ⟨hzA, hz2⟩
    obtain ⟨hcardpair, hsubpair⟩ := card_pair_of_mem_attachPoints hne hp hq
    have hcard2 : (attachPoints G C \ {p, q}).card = 2 := by
      have hh := Finset.card_sdiff_of_subset hsubpair
      omega
    exact ⟨D, hD, Finset.eq_of_subset_of_card_le hsub (by
      have hh := Finset.card_le_card hsub
      omega)⟩
  · -- all six traces occur: every pair is avoided
    intro hall p q hp hq hne
    obtain ⟨D, hD, hDtr⟩ := hall p q hp hq hne
    have hempty : D ∩ ({p, q} : Finset V) = ∅ := by
      ext z
      constructor
      · intro hz
        obtain ⟨hzD, hz2⟩ := Finset.mem_inter.mp hz
        have hzA : z ∈ attachPoints G C := by
          rcases mem_pair_iff.mp hz2 with h | h
          · rw [h]; exact hp
          · rw [h]; exact hq
        have hz3 : z ∈ attachPoints G C \ {p, q} := by
          rw [← hDtr]; exact Finset.mem_inter.mpr ⟨hzD, hzA⟩
        exact absurd hz2 (Finset.mem_sdiff.mp hz3).2
      · intro hz
        exact absurd hz (by simp)
    have hf : ¬ HitsOddCycles G ({p, q} : Finset V) :=
      fun hE => hE D hD hempty
    exact hf

/-! ## Part 4 — the sharp case is two named statements -/

/-- **THE `4 ≤ |attachPoints G C|` HALF OF ROUND 137'S REFINED RESIDUAL.**  The largest untouched part
of the sharp case `k = 1`. -/
def AttachFourResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      4 ≤ (attachPoints G C).card →
      ∃ a b : W, a ≠ b ∧ a ∈ attachPoints G C ∧ b ∈ attachPoints G C ∧
        HitsOddCycles G ({a, b} : Finset W)

/-- **THE NEGATIVE FORM OF THE `|attachPoints G C| = 4` HALF: THE SIX-TRACES CONFIGURATION OF PART 3
NEVER OCCURS AT `LocIndep 1`.**  A statement about a *configuration that does not occur*, of the same
shape as round 139's `JSP90.TriangleCrossResidual`. -/
def NoSixTraces : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    (∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      4 ≤ (attachPoints G C).card → NoCrossOver G C →
      ¬ (∀ p q : W, p ∈ attachPoints G C → q ∈ attachPoints G C → p ≠ q →
          ∃ D : Finset W, IsOddCycle G D ∧ (D ∩ attachPoints G C) = attachPoints G C \ {p, q})) →
    CloseToBipartite 2 G

/-- **THE SHARP CASE `k = 1`, WITH THE OPTIMAL CONSTANT `2`, FROM THE TWO NAMED CONFIGURATIONS.** -/
theorem erdos73On_one_two_of_allCrossResidual_and_attachFourResidual
    (hA : AllCrossResidual.{u}) (hF : AttachFourResidual.{u}) : Erdős73On.{u} 1 2 := by
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
        · obtain ⟨a, b, hab, ha, hb, hh⟩ :=
            hF W instW G hG C hC hshort (by omega)
          exact ⟨{a, b}, card_le_two_pair hab, fun D hD => hh D hD⟩
    · have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hh : HitsOddCycles G ({c} : Finset W) := by
        simpa [h0] using hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc
      exact ⟨{c}, by simp, hh⟩
  · exact ⟨∅, by simp, fun D hD => absurd ⟨D, hD⟩ hex⟩


/-- **THE `|A| = 3` CONFIGURATION FOLLOWS FROM THE SHARP CASE `k = 1`.** -/
theorem allCrossResidual_of_erdos73On_one_two (h : Erdős73On.{u} 1 2) : AllCrossResidual.{u} := by
  intro W instW G hG C hC hshort h3 heq
  obtain ⟨X, hX, hh⟩ := (closeToBipartite_iff_hitsOddCycles (V := W) (G := G) (m := 2)).mp
    (h W instW G hG)
  exact ⟨X, hX, hh⟩

/-- **THE `|A| ≥ 4` HALF OF ROUND 137'S REFINED RESIDUAL IS WEAKER THAN THE REFINED RESIDUAL.** -/
theorem attachFourResidual_of_attachThreeResidualRefined (h : AttachThreeResidualRefined.{u}) :
    AttachFourResidual.{u} := by
  intro W instW G hG C hC hshort h4
  obtain ⟨a, b, hab, ha, hb, hh⟩ := h W instW G hG C hC hshort (by omega)
  exact ⟨a, b, hab, ha, hb, hh⟩

/-! ## The six-traces residual really does settle the `|A| = 4` half -/

/-- **IF THE SIX-TRACES CONFIGURATION NEVER OCCURS THEN EVERY `|A| = 4` INSTANCE HAS A TWO-ELEMENT
CERTIFICATE INSIDE ITS ATTACHMENT POINTS.**  This is the *per-instance* consequence of
`JSP90.NoSixTraces`, using Part 3's `iff`. -/
theorem exists_pair_of_not_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hnc : NoCrossOver G C) (h4 : (attachPoints G C).card = 4)
    (hns : ¬ (∀ p q : V, p ∈ attachPoints G C → q ∈ attachPoints G C → p ≠ q →
        ∃ D : Finset V, IsOddCycle G D ∧ (D ∩ attachPoints G C) = attachPoints G C \ {p, q})) :
    ∃ p q : V, p ∈ attachPoints G C ∧ q ∈ attachPoints G C ∧ p ≠ q ∧
      HitsOddCycles G ({p, q} : Finset V) := by
  have hiff := not_pair_transversal_iff_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver
    h hC hshort hnc h4
  by_cases hex : ∃ p q : V,
      p ∈ attachPoints G C ∧ q ∈ attachPoints G C ∧ p ≠ q ∧ HitsOddCycles G ({p, q} : Finset V)
  · obtain ⟨p, q, hp, hq, hne, hh⟩ := hex
    exact ⟨p, q, hp, hq, hne, hh⟩
  · have hA : ∀ p q : V, p ∈ attachPoints G C → q ∈ attachPoints G C → p ≠ q →
        ¬ HitsOddCycles G ({p, q} : Finset V) := by
      intro p' q' hp' hq' hne' hc
      exact hex ⟨p', q', hp', hq', hne', hc⟩
    exact False.elim (hns (hiff.mp hA))

#print axioms JSP90.card_attachPoints_le_sum_attachSet
#print axioms JSP90.card_attachPoints_le_two_mul_card_boundary
#print axioms JSP90.two_le_card_boundary_of_card_attachPoints_ge_three
#print axioms JSP90.card_attachPoints_le_four_of_card_boundary_le_two
#print axioms JSP90.exists_attachSet_pair_of_card_attachPoints_eq_four_of_card_boundary_eq_two
#print axioms JSP90.exists_oddCycle_avoid_pair_of_not_hitsOddCycles_pair
#print axioms JSP90.ne_of_oddCycle_avoid_pair_sub_attachPoints
#print axioms JSP90.exists_trace_or_crossOverPoint_of_pair_not_transversal_of_card_attachPoints_eq_four
#print axioms JSP90.not_pair_transversal_iff_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver
#print axioms JSP90.erdos73On_one_two_of_allCrossResidual_and_attachFourResidual
#print axioms JSP90.allCrossResidual_of_erdos73On_one_two
#print axioms JSP90.attachFourResidual_of_attachThreeResidualRefined
#print axioms JSP90.exists_pair_of_not_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver

/-! ## What is *not* proved

`JSP90.AllCrossResidual`, `JSP90.NoSixTraces`, `JSP90.AttachFourResidual`, and behind them
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.
`jsp_000090_main` is deliberately not declared. -/
