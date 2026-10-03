import JSPProblem.CrossPair

/-!
# JSP-000090, round 141 — `JSPProblem/CrossThree.lean`: **the complete classification of the sharp
# case `k = 1` at three attachment points, and the accounting at three cross-over points**

Attack family 70.  Rounds 136–139 built the attachment-point axis: the attachment points
`A = attachPoints G C` of a shortest odd cycle `C` are an odd-cycle transversal (round 136); an odd
cycle meets them in one point exactly when it crosses `C` over in one point, i.e. at a *cross-over
point*, and erasing one attachment point which is not a cross-over point leaves a transversal
(rounds 137/138); a two-element certificate lying on `C` is *forced* to contain the cross-over set
`X = crossOverSet G C` (round 139).  What round 139 could not do is decide the sharp case at
`|A| = 3`: there the certificate must be `{x, a}` with `x` a cross-over point, and when *every*
attachment point is a cross-over point no pair on `C$ works at all.

This round settles the bookkeeping: **at `|A| = 3` the refined residual of round 137 is equivalent to
"not every attachment point is a cross-over point"**, as an `iff`.  Everything else is a theorem, so
the residual of the sharp case `k = 1` is reduced to one configuration, named `JSP90.AllCrossResidual`.

## Part 1 — the counting lemma

`JSP90.two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle`: an independent set contained in an
odd cycle of length `m` satisfies `2 * |S| + 1 ≤ m`.  This is `JSP90.indep_card_le_of_odd_cycle`
(`JSPProblem/OddCycle.lean`, the bound `α(C_m) ≤ ⌊m / 2⌋`) with the "every element of `S` is a vertex
of the cycle" side condition discharged by `S ⊆ C`; the development previously only had the form in
which `S$ is presented as an intersection with the cycle.  `JSP90.card_le_one_of_isIndepSet_sub_of_card_C_eq_three`
is its `|C| = 3` case.

## Part 2 — the classification at `|A| = 3`

**`JSP90.attachThreeResidualRefined_iff_of_card_attachPoints_eq_three`**: at packing number one, for a
shortest odd cycle `C` with `|attachPoints G C| = 3`,

```
(∃ a b, a ≠ b ∧ a, b ∈ attachPoints G C ∧ HitsOddCycles G {a, b})  ↔  attachPoints G C ≠ crossOverSet G C
```

* `⇐`: pick `b ∈ attachPoints G C \ crossOverSet G C` — the set is nonempty because
  `crossOverSet ⊆ attachPoints` and the two finsets are different — erase it (round 138's
  `hitsOddCycles_attachPoints_sdiff_of_not_crossOver`); the residue has exactly `3 - 1 = 2` elements
  and is therefore the sharp certificate of round 137's residual, exhibited as a named pair;
* `⇒`: a two-element certificate of `C$ contains `X$ (round 139's
  `subset_pair_of_hitsOddCycles_pair_of_mem`), so `|X| ≤ 2 < 3 = |A|`.

**`JSP90.hitsOddCycles_crossOverSet_of_card_crossOverSet_eq_two_of_card_attachPoints_eq_three`** — in
the `|X| = 2` case the certificate is the cross-over set *itself*, i.e. round 139's
`JSP90.TwoCrossTransversal` under the (necessary) hypothesis `|attachPoints G C| = 3`: two cross-over
points leave one attachment point which is not a cross-over point, and erasing it leaves a
two-element transversal *contained in* the cross-over set.

## Part 3 — new instances of the headline theorem

* **`JSP90.erdos73On_one_two_of_card_attachPoints_le_three_of_ne_crossOverSet`** — Erdős #73 at `k = 1`
  with the **optimal** constant `2`, for every shortest odd cycle with at most three attachment points
  and not all of them cross-over points: no bound on `|C|`, no odd-girth hypothesis, no packing weight,
  no branch vertices.  This *strictly generalises* round 139's
  `erdos73On_one_two_of_triangleCrossResidual` (which required `|C| = 3`);
* **`JSP90.erdos73On_one_two_of_triangleCrossResidual'`** — the same conclusion from round 139's
  triangle residual, with the certificate **exhibited** as `attachPoints G C \ {x}`;
* **`JSP90.SmallAttachResidual` / `JSP90.erdos73On_one_two_of_maxCardAttach_three`** — a *class*
  instance: every graph all of whose shortest odd cycles have at most three attachment points is
  `2`-close to bipartite at `LocIndep 1`, under the residual `SmallAttachResidual`, which is exactly
  `¬ JSP90.AllCrossResidual`.

## Part 4 — the accounting at three cross-over points

`JSP90.le_card_add_two_mul_card_inter_of_three_crossOverPoints`: if `c₁, c₂, c₃` are cross-over points
of `C$ with witnesses `D₁, D₂, D₃` (so `C ∩ Dᵢ = {cᵢ}`) and `S` is an independent set contained in
`C ∪ ⋃ᵢ (Dᵢ \ C)`, then

```
2 * |S| + 2 * |S ∩ {c₁, c₂, c₃}|  ≤  |C| - 1 + (|D₁| - 1) + (|D₂| - 1) + (|D₃| - 1)
```

The mechanism is a three-line count: `Dᵢ = (Dᵢ \ C) ⊔ {cᵢ}`, so `S ∩ Dᵢ` splits as
`(S ∩ (Dᵢ \ C)) ⊔ (S ∩ {cᵢ})`; Part 1 prices `S ∩ Dᵢ` at `(|Dᵢ| - 1) / 2` and therefore
`S ∩ (Dᵢ \ C)` at `(|Dᵢ| - 1) / 2` **minus one** whenever `cᵢ ∈ S`.  The four pieces of `S$ — on `C$
and in each tail — are then counted separately.  No hypothesis on `LocIndep`, on the minimality of `C$
or on `|C|` is used, and the `cᵢ` need not be distinct.

`JSP90.le_card_union_tails_add_two_mul_card_inter_of_three_crossOverPoints` adds Erdős's hypothesis
(applied to `W = C ∪ ⋃ᵢ (Dᵢ \ C)`) and concludes that **the three tails must overlap by at least
`2 |S ∩ {c₁, c₂, c₃}|`**, which is the first quantitative constraint on three cross-over points.

## What is *not* proved

`JSP90.AllCrossResidual` (every attachment point of a shortest odd cycle with three attachment points
is a cross-over point), the cases `|attachPoints G C| ≥ 4` of `JSP90.AttachThreeResidualRefined`, and
behind them `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary
blocker.  `jsp_000090_main` is deliberately not declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 800000

local instance crossThreeDecidableEq : DecidableEq V := Classical.decEq V

local instance crossThreeDecidablePred (C : Finset V) : DecidablePred (CrossOverPoint G C) :=
  fun _ => Classical.propDecidable _

/-! ## Part 1 — the counting lemma: an independent set inside an odd cycle -/

/-- **AN INDEPENDENT SET CONTAINED IN AN ODD CYCLE HAS AT MOST `⌊m / 2⌋` ELEMENTS.**

`2 * |S| + 1 ≤ |C|` for every independent set `S` of `G` contained in the odd cycle `C`.  This is
`JSP90.indep_card_le_of_odd_cycle` (`JSPProblem/OddCycle.lean`: `α(C_m) ≤ ⌊m / 2⌋`) with the "every
element of `S` is a vertex of the cycle" side condition discharged by `S ⊆ C`. -/
theorem two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle {C S : Finset V}
    (hC : IsOddCycle G C) (hS : G.IsIndepSet S) (hsub : S ⊆ C) : 2 * S.card + 1 ≤ C.card := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  have hcard : C.card = m := card_eq_cyclicOrder f hinj hmem
  have hSin : ∀ ⦃x : V⦄, x ∈ S → ∃ j : Fin m, f j = x := by
    intro x hx
    exact hmem x |>.mp (hsub hx)
  have hle := indep_card_le_of_odd_cycle hm f hinj hcyc S hS hSin
  rw [← hcard] at hle
  exact hle

/-- **AN INDEPENDENT SET CONTAINED IN AN ODD TRIANGLE HAS AT MOST ONE ELEMENT.** -/
theorem card_le_one_of_isIndepSet_sub_of_card_C_eq_three {C S : Finset V} (hC : IsOddCycle G C)
    (hS : G.IsIndepSet S) (hsub : S ⊆ C) (h3 : C.card = 3) : S.card ≤ 1 := by
  have h := two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle hC hS hsub
  rw [h3] at h
  omega

/-- **A SINGLETON HAS AT MOST ONE ELEMENT.** -/
theorem card_le_one_singleton (c : V) : ({c} : Finset V).card ≤ 1 := by simp

/-- **A MEMBERSHIP AND ITS NEGATION ARE INCONSISTENT.**  At the pinned revision a `Finset`
membership is *not* applicable as a function (`a ∈ s` has type `Prop`, not `α → Prop`), so the idiom
`hz hz'` of the earlier files only works when `hz'` has the `¬` shape; this wrapper fixes the
direction once. -/
theorem mem_and_not_mem_false {W : Type u} {s : Finset W} {z : W} (h1 : z ∈ s) (h2 : z ∉ s) : False :=
  absurd h1 h2

/-- **A SET WHICH IS NOT CONTAINED IN ANOTHER HAS AN ELEMENT OUTSIDE IT.** -/
theorem exists_mem_notMem_of_not_subset' {s t : Finset V} (h : ¬ s ⊆ t) :
    ∃ b ∈ s, b ∉ t := by
  by_contra hc
  refine h ?_
  intro x hx
  by_contra hxt
  exact hc ⟨x, hx, hxt⟩

/-- **AN ATTACHMENT POINT WHICH IS NOT A CROSS-OVER POINT EXISTS AS SOON AS THE TWO SETS DIFFER AND
THERE ARE THREE ATTACHMENT POINTS.** -/
theorem exists_mem_attachPoints_notMem_crossOverSet_of_card_eq_three_of_ne {C : Finset V}
    (h3 : (attachPoints G C).card = 3) (hne : attachPoints G C ≠ crossOverSet G C) :
    ∃ b ∈ attachPoints G C, b ∉ crossOverSet G C := by
  by_cases hsub : attachPoints G C ⊆ crossOverSet G C
  · exfalso
    apply hne
    exact Finset.Subset.antisymm hsub (subset_crossOverSet_attachPoints C)
  · have hne2 : (attachPoints G C).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hc
      have hz := congrArg Finset.card hc
      rw [Finset.card_empty] at hz
      omega
    exact exists_mem_notMem_of_not_subset' hsub

/-! ## Part 2 — the classification at `|attachPoints G C| = 3` -/

/-- **THE SHARP CERTIFICATE AT THREE ATTACHMENT POINTS, ONE OF WHICH IS NOT A CROSS-OVER POINT.**

```lean
PackingNumberOne G → C a shortest odd cycle → |attachPoints G C| = 3 →
  attachPoints G C ≠ crossOverSet G C →
  ∃ a b, a ≠ b ∧ a, b ∈ attachPoints G C ∧ HitsOddCycles G {a, b}
```

Round 138 proved that erasing *one* attachment point which is not a cross-over point leaves a
transversal; at `|A| = 3` that transversal has exactly two elements, so it is the sharp certificate of
round 137's residual, exhibited here as a *named pair*. -/
theorem hitsOddCycles_pair_of_card_attachPoints_eq_three_of_ne_crossOverSet
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : (attachPoints G C).card = 3) (hne : attachPoints G C ≠ crossOverSet G C) :
    ∃ a b : V, a ≠ b ∧ a ∈ attachPoints G C ∧ b ∈ attachPoints G C ∧
      HitsOddCycles G ({a, b} : Finset V) := by
  obtain ⟨b, hbA, hbX⟩ :=
    exists_mem_attachPoints_notMem_crossOverSet_of_card_eq_three_of_ne h3 hne
  have hb : ¬ CrossOverPoint G C b := fun h => hbX (mem_crossOverSet.mpr ⟨h, hbA⟩)
  have hZ : HitsOddCycles G (attachPoints G C \ {b}) :=
    hitsOddCycles_attachPoints_sdiff_of_not_crossOver h hC hshort hbA hb (by rw [h3]; omega)
  have hcard : (attachPoints G C \ {b} : Finset V).card = 2 := by
    rw [card_sdiff_singleton_of_mem hbA, h3]
  obtain ⟨a, a', ha, ha', hne'⟩ :=
    exists_pair_ne_of_card_ge_two (S := attachPoints G C \ {b}) (by omega)
  have hsub : ({a, a'} : Finset V) ⊆ attachPoints G C \ {b} := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact ha
    · rw [hz]
      exact ha'
  have hcard2 : ({a, a'} : Finset V).card = 2 := Finset.card_eq_two.mpr ⟨a, a', hne', rfl⟩
  have heq : ({a, a'} : Finset V) = attachPoints G C \ {b} :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard2])
  refine ⟨a, a', hne', (Finset.mem_sdiff.mp ha).1, (Finset.mem_sdiff.mp ha').1, ?_⟩
  rw [heq]
  exact hZ

/-- **NO TWO-ELEMENT CERTIFICATE LIES ON `C$` WHEN EVERY ATTACHMENT POINT IS A CROSS-OVER POINT.**

Round 139's `JSP90.not_hitsOddCycles_pair_of_mem_of_three_crossOverPoint`, with the three cross-over
points named as the three attachment points: the certificate of a shortest odd cycle is forced to
contain the whole cross-over set, so three cross-over points are an obstruction. -/
theorem not_hitsOddCycles_pair_of_mem_of_card_attachPoints_eq_three_of_subset_crossOverSet
    {C : Finset V} (h3 : (attachPoints G C).card = 3)
    (hsub : attachPoints G C ⊆ crossOverSet G C) :
    ∀ a b : V, a ≠ b → a ∈ attachPoints G C → b ∈ attachPoints G C →
      ¬ HitsOddCycles G ({a, b} : Finset V) := by
  intro a b hab ha hb hH
  have heq : attachPoints G C = crossOverSet G C :=
    Finset.Subset.antisymm hsub (subset_crossOverSet_attachPoints C)
  obtain ⟨c, hcC, hca, hcb⟩ := exists_third_of_card_eq_three_mem_pair h3 hab ha hb
  have hsubC : ({a, b} : Finset V) ⊆ C := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact (mem_attachPoints.mp ha).1
    · rw [hz]
      exact (mem_attachPoints.mp hb).1
  exact not_hitsOddCycles_pair_of_mem_of_three_crossOverPoint
    (mem_crossOverSet.mp (heq ▸ ha)).1 (mem_crossOverSet.mp (heq ▸ hb)).1
    (mem_crossOverSet.mp (heq ▸ hcC)).1 hab (Ne.symm hcb) (Ne.symm hca) hsubC hab hH

/-- **IN THE LAST RESIDUAL NO TWO-ELEMENT SUBSET OF THE ATTACHMENT POINTS IS A TRANSVERSAL.**
The certificate of round 137, if it exists in the configuration `JSP90.AllCrossResidual`, cannot lie
among the attachment points (hence not on `C$): it must come from outside `C$. -/
theorem not_hitsOddCycles_pair_of_mem_of_card_attachPoints_eq_three_of_eq_crossOverSet
    {C : Finset V} (h3 : (attachPoints G C).card = 3) (heq : attachPoints G C = crossOverSet G C) :
    ∀ a b : V, a ≠ b → a ∈ attachPoints G C → b ∈ attachPoints G C →
      ¬ HitsOddCycles G ({a, b} : Finset V) := by
  have hsub : attachPoints G C ⊆ crossOverSet G C := fun _ hx => heq ▸ hx
  exact not_hitsOddCycles_pair_of_mem_of_card_attachPoints_eq_three_of_subset_crossOverSet h3 hsub

/-- **THE RESIDUAL OF THE SHARP CASE `k = 1` IS EQUIVALENT, AT THREE ATTACHMENT POINTS, TO "NOT EVERY
ATTACHMENT POINT IS A CROSS-OVER POINT".**

```lean
PackingNumberOne G → C a shortest odd cycle → |attachPoints G C| = 3 →
  ((∃ a b, a ≠ b ∧ a, b ∈ attachPoints G C ∧ HitsOddCycles G {a, b})
     ↔ attachPoints G C ≠ crossOverSet G C)
```

This is the exact statement of what is left of `JSP90.AttachThreeResidualRefined` (round 137): one
named configuration, rather than an existential to be searched. -/
theorem attachThreeResidualRefined_iff_of_card_attachPoints_eq_three (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : (attachPoints G C).card = 3) :
    ((∃ a b : V, a ≠ b ∧ a ∈ attachPoints G C ∧ b ∈ attachPoints G C ∧
        HitsOddCycles G ({a, b} : Finset V))
      ↔ attachPoints G C ≠ crossOverSet G C) := by
  constructor
  · rintro ⟨a, b, hab, ha, hb, hh⟩
    have hsubC : ({a, b} : Finset V) ⊆ C := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · rw [hz]
        exact (mem_attachPoints.mp ha).1
      · rw [hz]
        exact (mem_attachPoints.mp hb).1
    have hX : crossOverSet G C ⊆ ({a, b} : Finset V) :=
      subset_pair_of_hitsOddCycles_pair_of_mem hab (mem_attachPoints.mp ha).1
        (mem_attachPoints.mp hb).1 hh
    have hle : (crossOverSet G C).card ≤ 2 :=
      (Finset.card_le_card hX).trans (card_le_two_pair hab)
    intro heq
    have hX3 : (crossOverSet G C).card = 3 := heq ▸ h3
    omega
  · intro hne
    exact hitsOddCycles_pair_of_card_attachPoints_eq_three_of_ne_crossOverSet h hC hshort h3 hne

/-- **THE CERTIFICATE IN THE CASE OF TWO CROSS-OVER POINTS IS THE CROSS-OVER SET ITSELF.**

Round 139's `JSP90.TwoCrossTransversal`, under the necessary hypothesis `|attachPoints G C| = 3`:
`|crossOverSet G C| = 2` leaves one attachment point which is not a cross-over point, erasing it
leaves a two-element transversal *contained in* the cross-over set, and both have two elements. -/
theorem hitsOddCycles_crossOverSet_of_card_crossOverSet_eq_two_of_card_attachPoints_eq_three
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : (attachPoints G C).card = 3) (h2 : (crossOverSet G C).card = 2) :
    HitsOddCycles G (crossOverSet G C) := by
  have hle : (crossOverSet G C).card ≤ (attachPoints G C).card :=
    Finset.card_le_card (subset_crossOverSet_attachPoints C)
  have hne : attachPoints G C ≠ crossOverSet G C := by
    intro heq
    have h3' : (crossOverSet G C).card = 3 := heq ▸ h3
    omega
  obtain ⟨a, b, hab, ha, hb, hh⟩ :=
    hitsOddCycles_pair_of_card_attachPoints_eq_three_of_ne_crossOverSet h hC hshort h3 hne
  have hsubX : crossOverSet G C ⊆ ({a, b} : Finset V) :=
    subset_pair_of_hitsOddCycles_pair_of_mem hab (mem_attachPoints.mp ha).1
      (mem_attachPoints.mp hb).1 hh
  have hcard2 : ({a, b} : Finset V).card = 2 := Finset.card_eq_two.mpr ⟨a, b, hab, rfl⟩
  have heqX : crossOverSet G C = ({a, b} : Finset V) :=
    Finset.eq_of_subset_of_card_le hsubX (by rw [hcard2, h2])
  rw [heqX]
  exact hh

/-! ## Part 3 — new instances of the headline theorem -/

/-- **ERDŐS PROBLEM #73 AT `k = 1` WITH THE CONSTANT `2`, FOR A SHORTEST ODD CYCLE WITH AT MOST THREE
ATTACHMENT POINTS AND NOT ALL OF THEM CROSS-OVER POINTS.**

```lean
LocIndep 1 G → C a shortest odd cycle → |attachPoints G C| ≤ 3 →
  attachPoints G C ≠ crossOverSet G C → CloseToBipartite m G   (2 ≤ m)
```

A new instance of the headline theorem: the certificate is two vertices **of `C$**, and no hypothesis
on `|C|`, the odd girth, the packing weight or the number of branch vertices appears.  It strictly
generalises round 139's `JSP90.erdos73On_one_two_of_triangleCrossResidual`, which required `|C| = 3`.

The case analysis: `|A| ≤ 2` — `A` itself is a transversal (round 136); `|A| = 3` — Part 2 gives a
named pair; `C$ has no fan vertex — a single vertex of `C$ suffices (round 136). -/
theorem closeToBipartite_two_of_card_attachPoints_le_three_of_ne_crossOverSet
    {m : ℕ} (hG : LocIndep 1 G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : (attachPoints G C).card ≤ 3) (hne : attachPoints G C ≠ crossOverSet G C)
    (hm : 2 ≤ m) : CloseToBipartite m G := by
  have hp : PackingNumberOne G := packingNumberOne_of_locIndep_one hG
  rw [closeToBipartite_iff_hitsOddCycles]
  by_cases hnef : (boundary G C).Nonempty
  · by_cases hle : (attachPoints G C).card ≤ 2
    · exact ⟨attachPoints G C, hle.trans hm,
        hitsOddCycles_attachPoints_of_packing_one hp hC hshort hnef⟩
    · have h3' : (attachPoints G C).card = 3 := by omega
      obtain ⟨a, b, hab, ha, hb, hh⟩ :=
        hitsOddCycles_pair_of_card_attachPoints_eq_three_of_ne_crossOverSet hp hC hshort h3' hne
      exact ⟨{a, b}, card_le_two_pair hab |>.trans hm, hh⟩
  · obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
    have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnef
    have hh : HitsOddCycles G ({c} : Finset V) := by
      simpa [h0] using hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc
    exact ⟨{c}, card_le_one_singleton c |>.trans (by omega), hh⟩

/-- **THE INSTANCE OF Part 3 AS AN INSTANCE OF THE HEADLINE THEOREM.** -/
theorem erdos73On_one_two_of_card_attachPoints_le_three_of_ne_crossOverSet
    (hG : LocIndep 1 G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : (attachPoints G C).card ≤ 3) (hne : attachPoints G C ≠ crossOverSet G C) :
    CloseToBipartite 2 G :=
  closeToBipartite_two_of_card_attachPoints_le_three_of_ne_crossOverSet hG hC hshort h3 hne
    (by omega)

/-- **THE SAME, FROM ROUND 139'S TRIANGLE RESIDUAL, WITH THE CERTIFICATE EXHIBITED.** -/
theorem erdos73On_one_two_of_triangleCrossResidual' (h : TriangleCrossResidual.{u}) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
      (∀ C : Finset W, IsOddCycle G C → C.card = 3) → CloseToBipartite 2 G := by
  intro W instW G hG htri
  rw [closeToBipartite_iff_hitsOddCycles]
  by_cases hex : ∃ C : Finset W, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle (G := G) hex
    have hC3 : C.card = 3 := htri C hC
    by_cases hnef : (boundary G C).Nonempty
    · by_cases hle : (attachPoints G C).card ≤ 2
      · exact ⟨attachPoints G C, by omega,
          hitsOddCycles_attachPoints_of_packing_one (packingNumberOne_of_locIndep_one hG) hC hshort
            hnef⟩
      · have hleA : (attachPoints G C).card ≤ C.card :=
          Finset.card_le_card (subset_attachPoints_C C)
        have h3 : (attachPoints G C).card = 3 := by omega
        have hA : attachPoints G C = C := by
          refine Finset.eq_of_subset_of_card_le (s := attachPoints G C) (t := C)
            (subset_attachPoints_C C) ?_
          omega
        obtain ⟨x, hxC, hx⟩ := h W instW G hG C hC hshort hC3 (by omega)
        have hxA : x ∈ attachPoints G C := by rw [hA]; exact hxC
        have hcardX : (attachPoints G C \ {x} : Finset W).card ≤ 2 := by
          rw [card_sdiff_singleton_of_mem hxA, h3]
        refine ⟨attachPoints G C \ {x}, hcardX, ?_⟩
        exact hitsOddCycles_attachPoints_sdiff_of_not_crossOver
          (packingNumberOne_of_locIndep_one hG) hC hshort hxA hx (by omega)
    · obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
      have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnef
      have hh : HitsOddCycles G ({c} : Finset W) := by
        simpa [h0] using hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc
      exact ⟨{c}, by simp, hh⟩
  · exact ⟨∅, by simp, fun D hD => absurd ⟨D, hD⟩ hex⟩

/-- **THE LAST RESIDUAL OF THE SHARP CASE `k = 1` AT THREE ATTACHMENT POINTS: every attachment point
of `C$ is a cross-over point.**  By Part 2 this is the *only* configuration in which the certificate
of round 137 is not exhibited by this file, and it cannot lie among the attachment points (Part 2,
negative half), so it must come from outside `C$. -/
def AllCrossResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      3 ≤ (attachPoints G C).card → attachPoints G C = crossOverSet G C →
      ∃ X : Finset W, X.card ≤ 2 ∧ HitsOddCycles G X

/-- **ERDŐS PROBLEM #73 AT `k = 1` WITH THE CONSTANT `2`, FOR GRAPHS ALL OF WHOSE SHORTEST ODD CYCLES
HAVE AT MOST THREE ATTACHMENT POINTS.**  A class instance of the headline theorem: the hypothesis is
a property of the odd cycles alone. -/
def SmallAttachResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    (∀ (C : Finset W), IsOddCycle G C →
      (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) → (attachPoints G C).card ≤ 3) →
    CloseToBipartite 2 G

/-- **THE LAST RESIDUAL IMPLIES THE CLASS RESIDUAL.** -/
theorem smallAttachResidual_of_allCrossResidual (h : AllCrossResidual.{u}) :
    SmallAttachResidual.{u} := by
  intro W instW G hG hall
  rw [closeToBipartite_iff_hitsOddCycles]
  by_cases hex : ∃ C : Finset W, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle (G := G) hex
    have h3 : (attachPoints G C).card ≤ 3 := hall C hC hshort
    by_cases heq : attachPoints G C = crossOverSet G C
    · by_cases hle : (attachPoints G C).card ≤ 2
      · by_cases hnef : (boundary G C).Nonempty
        · exact ⟨attachPoints G C, by omega,
            hitsOddCycles_attachPoints_of_packing_one (packingNumberOne_of_locIndep_one hG) hC hshort
              hnef⟩
        · obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
          have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnef
          have hh : HitsOddCycles G ({c} : Finset W) := by
            simpa [h0] using hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc
          exact ⟨{c}, by simp, hh⟩
      · exact h W instW G hG C hC hshort (by omega) heq
    · exact (closeToBipartite_iff_hitsOddCycles (V := W) (G := G) (m := 2)).mp
        (erdos73On_one_two_of_card_attachPoints_le_three_of_ne_crossOverSet hG hC hshort h3 heq)
  · exact ⟨∅, by simp, fun D hD => absurd ⟨D, hD⟩ hex⟩

/-- **THE CLASS INSTANCE, AS A HYPOTHESIS ON THE GRAPH.** -/
theorem erdos73On_one_two_of_maxCardAttach_three (h : AllCrossResidual.{u})
    {W : Type u} (_ : Fintype W) (G : SimpleGraph W) (hG : LocIndep 1 G)
    (hall : ∀ C : Finset W, IsOddCycle G C →
      (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) → (attachPoints G C).card ≤ 3) :
    CloseToBipartite 2 G :=
  smallAttachResidual_of_allCrossResidual h W _ G hG hall

/-! ## Part 4 — the accounting at three cross-over points -/

/-- **THE ACCOUNTING AT THREE CROSS-OVER POINTS.**

```lean
OnePointCrossOver G C D₁ → OnePointCrossOver G C D₂ → OnePointCrossOver G C D₃ →
  c₁ ∈ C ∩ D₁ → c₂ ∈ C ∩ D₂ → c₃ ∈ C ∩ D₃ →
  S independent, S ⊆ C ∪ (D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C) →
  2 * |S| + 2 * |S ∩ {c₁, c₂, c₃}|  ≤  |C| - 1 + (|D₁| - 1) + (|D₂| - 1) + (|D₃| - 1)
```

The mechanism is a three-line count.  Since `C ∩ Dᵢ = {cᵢ}`, the odd cycle `Dᵢ$ is the disjoint union of
its tail `Tᵢ = Dᵢ \ C` and the single point `cᵢ`, so `S ∩ Dᵢ$ splits as
`(S ∩ (Dᵢ \ C)) ⊔ (S ∩ {cᵢ})`; Part 1 prices `S ∩ Dᵢ$ at `(|Dᵢ| - 1) / 2` and therefore
`S ∩ (Dᵢ \ C)` at `(|Dᵢ| - 1) / 2` **minus one** whenever `cᵢ ∈ S`.  The four pieces of `S$ — on `C$
and in each tail — are then counted separately.

No hypothesis on `LocIndep`, on the minimality of `C$ or on `|C|` is used, and the `cᵢ` need not be
distinct. -/
theorem le_card_add_two_mul_card_inter_of_three_crossOverPoints {C D₁ D₂ D₃ S : Finset V}
    {c₁ c₂ c₃ : V} (hC : IsOddCycle G C) (h₁ : OnePointCrossOver G C D₁)
    (h₂ : OnePointCrossOver G C D₂) (h₃ : OnePointCrossOver G C D₃) (hc₁ : c₁ ∈ C ∩ D₁)
    (hc₂ : c₂ ∈ C ∩ D₂) (hc₃ : c₃ ∈ C ∩ D₃) (hS : G.IsIndepSet S)
    (hsub : S ⊆ C ∪ (D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C)) :
    2 * S.card + 2 * ((S ∩ ({c₁, c₂, c₃} : Finset V)).card)
      ≤ (C.card - 1) + (D₁.card - 1) + (D₂.card - 1) + (D₃.card - 1) := by
  have hsing₁ : C ∩ D₁ = {c₁} := inter_eq_singleton_of_onePointCrossOver h₁ hc₁
  have hsing₂ : C ∩ D₂ = {c₂} := inter_eq_singleton_of_onePointCrossOver h₂ hc₂
  have hsing₃ : C ∩ D₃ = {c₃} := inter_eq_singleton_of_onePointCrossOver h₃ hc₃
  have hcC₁ : c₁ ∈ C := (Finset.mem_inter.mp hc₁).1
  have hcC₂ : c₂ ∈ C := (Finset.mem_inter.mp hc₂).1
  have hcC₃ : c₃ ∈ C := (Finset.mem_inter.mp hc₃).1
  -- `S ∩ Dᵢ` splits into the tail part and the single point `cᵢ`
  have hsplit : ∀ (D : Finset V) (c : V) (hcC : c ∈ C) (heq : C ∩ D = {c}),
      (S ∩ D).card = (S ∩ (D \ C)).card + (S ∩ {c}).card := by
    intro D c hcC heq
    have hcongr : S ∩ D = (S ∩ (D \ C)) ∪ (S ∩ (C ∩ D)) := by
      ext z
      have hsplitD : z ∈ D ↔ z ∈ D \ C ∨ z ∈ C ∩ D := by
        constructor
        · intro hz
          by_cases hzC : z ∈ C
          · exact Or.inr (Finset.mem_inter.mpr ⟨hzC, hz⟩)
          · exact Or.inl (Finset.mem_sdiff.mpr ⟨hz, hzC⟩)
        · rintro (h | h)
          · exact (Finset.mem_sdiff.mp h).1
          · exact (Finset.mem_inter.mp h).2
      constructor
      · intro hz
        rcases Finset.mem_inter.mp hz with ⟨hzS, hzD⟩
        rcases hsplitD.mp hzD with h | h
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hzS, h⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hzS, h⟩))
      · intro hz
        rcases Finset.mem_union.mp hz with h | h
        · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1,
            hsplitD.mpr (Or.inl (Finset.mem_inter.mp h).2)⟩
        · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1,
            hsplitD.mpr (Or.inr (Finset.mem_inter.mp h).2)⟩
    rw [hcongr, heq]
    have hdis : Disjoint ((S ∩ (D \ C) : Finset V)) (S ∩ ({c} : Finset V)) := by
      refine Finset.disjoint_left.mpr ?_
      intro z hz1 hz2
      have hz1' : z ∈ D ∧ z ∉ C := Finset.mem_sdiff.mp (Finset.mem_inter.mp hz1).2
      have hz2' : z = c := Finset.mem_singleton.mp (Finset.mem_inter.mp hz2).2
      simp only [hz2'] at hz1'
      exact hz1'.2 hcC
    exact Finset.card_union_of_disjoint hdis
  have hs1 : (S ∩ D₁).card = (S ∩ (D₁ \ C)).card + (S ∩ {c₁}).card :=
    hsplit D₁ c₁ hcC₁ hsing₁
  have hs2 : (S ∩ D₂).card = (S ∩ (D₂ \ C)).card + (S ∩ {c₂}).card :=
    hsplit D₂ c₂ hcC₂ hsing₂
  have hs3 : (S ∩ D₃).card = (S ∩ (D₃ \ C)).card + (S ∩ {c₃}).card :=
    hsplit D₃ c₃ hcC₃ hsing₃
  -- the counting inputs
  have hSc : 2 * (S ∩ C).card + 1 ≤ C.card :=
    two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle (C := C) (S := S ∩ C) hC
      (IsIndepSet.subset hS (Finset.inter_subset_left : S ∩ C ⊆ S))
      (Finset.inter_subset_right : S ∩ C ⊆ C)
  have hS1 : 2 * (S ∩ D₁).card + 1 ≤ D₁.card :=
    two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle (C := D₁) (S := S ∩ D₁) h₁.1
      (IsIndepSet.subset hS (Finset.inter_subset_left : S ∩ D₁ ⊆ S))
      (Finset.inter_subset_right : S ∩ D₁ ⊆ D₁)
  have hS2 : 2 * (S ∩ D₂).card + 1 ≤ D₂.card :=
    two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle (C := D₂) (S := S ∩ D₂) h₂.1
      (IsIndepSet.subset hS (Finset.inter_subset_left : S ∩ D₂ ⊆ S))
      (Finset.inter_subset_right : S ∩ D₂ ⊆ D₂)
  have hS3 : 2 * (S ∩ D₃).card + 1 ≤ D₃.card :=
    two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle (C := D₃) (S := S ∩ D₃) h₃.1
      (IsIndepSet.subset hS (Finset.inter_subset_left : S ∩ D₃ ⊆ S))
      (Finset.inter_subset_right : S ∩ D₃ ⊆ D₃)
  -- the three cross-over points are counted once
  have hJsub : ({c₁, c₂, c₃} : Finset V) ⊆ {c₁} ∪ {c₂} ∪ {c₃} := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with hz | hz | hz <;> rw [hz] <;> simp
  have hJ : ((S ∩ ({c₁, c₂, c₃} : Finset V)) : Finset V).card
      ≤ (S ∩ {c₁}).card + (S ∩ {c₂}).card + (S ∩ {c₃}).card := by
    have heq : S ∩ ({c₁, c₂, c₃} : Finset V)
        = ((S ∩ {c₁}) ∪ (S ∩ {c₂})) ∪ (S ∩ {c₃}) := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    calc card (S ∩ ({c₁, c₂, c₃} : Finset V))
        ≤ card (((S ∩ {c₁}) ∪ (S ∩ {c₂})) ∪ (S ∩ {c₃})) := Finset.card_le_card heq.le
      _ ≤ card ((S ∩ {c₁}) ∪ (S ∩ {c₂})) + card (S ∩ {c₃}) :=
          Finset.card_union_le ((S ∩ {c₁}) ∪ (S ∩ {c₂})) (S ∩ {c₃})
      _ ≤ card (S ∩ {c₁}) + card (S ∩ {c₂}) + card (S ∩ {c₃}) := by
        have e := Finset.card_union_le (S ∩ ({c₁} : Finset V)) (S ∩ {c₂})
        omega
  have hone1 : (S ∩ {c₁} : Finset V).card ≤ 1 :=
    (Finset.card_le_card
      (Finset.inter_subset_right : S ∩ ({c₁} : Finset V) ⊆ {c₁})).trans (card_le_one_singleton c₁)
  have hone2 : (S ∩ {c₂} : Finset V).card ≤ 1 :=
    (Finset.card_le_card
      (Finset.inter_subset_right : S ∩ ({c₂} : Finset V) ⊆ {c₂})).trans (card_le_one_singleton c₂)
  have hone3 : (S ∩ {c₃} : Finset V).card ≤ 1 :=
    (Finset.card_le_card
      (Finset.inter_subset_right : S ∩ ({c₃} : Finset V) ⊆ {c₃})).trans (card_le_one_singleton c₃)
  -- `S` splits into its part on `C$ and its three tail parts
  have hSW : S ∩ (C ∪ (D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C))
      = (S ∩ C) ∪ (S ∩ (D₁ \ C)) ∪ (S ∩ (D₂ \ C)) ∪ (S ∩ (D₃ \ C)) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have e1 : S.card = (S ∩ (C ∪ (D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C)) : Finset V).card :=
    congrArg Finset.card (show S = S ∩ (C ∪ (D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C)) by
      ext z
      simp only [Finset.mem_inter]
      constructor
      · exact fun h => ⟨h, hsub h⟩
      · exact fun h => h.1)
  have e0 : (S ∩ (C ∪ (D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C))).card
      = Finset.card ((((S ∩ C) ∪ (S ∩ (D₁ \ C))) ∪ (S ∩ (D₂ \ C))) ∪ (S ∩ (D₃ \ C))
          : Finset V) :=
    congrArg Finset.card hSW
  have e2 := Finset.card_union_le
    (((S ∩ C) ∪ (S ∩ (D₁ \ C))) ∪ (S ∩ (D₂ \ C))) (S ∩ (D₃ \ C))
  have e3 := Finset.card_union_le ((S ∩ C) ∪ (S ∩ (D₁ \ C))) (S ∩ (D₂ \ C))
  have e4 := Finset.card_union_le (S ∩ C) (S ∩ (D₁ \ C))
  omega

/-- **THE THREE TAILS OF THREE CROSS-OVER CYCLES MUST OVERLAP BY AT LEAST `2 |S ∩ {c₁, c₂, c₃}|`.**

With `LocIndep 1` applied to the vertex set `W = C ∪ (D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C)` — the independent
set `S ⊆ W$ supplied by Erdős's hypothesis — together with the accounting lemma:

```
|⋃ᵢ (Dᵢ \ C)| + 2 * |S ∩ {c₁, c₂, c₃}|  ≤  Σᵢ (|Dᵢ| - 1)
```

This is the first quantitative constraint on three cross-over points available in the development. -/
theorem le_card_union_tails_add_two_mul_card_inter_of_three_crossOverPoints
    {C D₁ D₂ D₃ S : Finset V} {c₁ c₂ c₃ : V} (hG : LocIndep 1 G) (hC : IsOddCycle G C)
    (h₁ : OnePointCrossOver G C D₁)
    (h₂ : OnePointCrossOver G C D₂) (h₃ : OnePointCrossOver G C D₃) (hc₁ : c₁ ∈ C ∩ D₁)
    (hc₂ : c₂ ∈ C ∩ D₂) (hc₃ : c₃ ∈ C ∩ D₃) (hS : G.IsIndepSet S)
    (hsub : S ⊆ C ∪ (D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C))
    (h2S : 2 * S.card + 1 ≥ (C ∪ (D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C)).card) :
    ((D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C)).card + 2 * ((S ∩ ({c₁, c₂, c₃} : Finset V)).card)
      ≤ (D₁.card - 1) + (D₂.card - 1) + (D₃.card - 1) := by
  have hle := le_card_add_two_mul_card_inter_of_three_crossOverPoints hC h₁ h₂ h₃ hc₁ hc₂ hc₃ hS hsub
  have hd : Disjoint (C : Finset V) ((D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C)) := by
    refine Finset.disjoint_left.mpr ?_
    intro z hzC hzU
    rcases Finset.mem_union.mp hzU with hz1 | hz1
    · rcases Finset.mem_union.mp hz1 with hz2 | hz2
      · exact (Finset.mem_sdiff.mp hz2).2 hzC
      · exact (Finset.mem_sdiff.mp hz2).2 hzC
    · exact (Finset.mem_sdiff.mp hz1).2 hzC
  have hCcard : (C ∪ ((D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C))).card
      = C.card + ((D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C)).card :=
    Finset.card_union_of_disjoint hd
  have hC3 : 3 ≤ C.card := by
    obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
    have hcard : C.card = m := card_eq_cyclicOrder f hinj hmem
    omega
  have he : C ∪ (D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C) = C ∪ ((D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C)) := by
    ext z
    simp only [Finset.mem_union]
    tauto
  have h2S' : 2 * S.card + 1 ≥ (C ∪ ((D₁ \ C) ∪ (D₂ \ C) ∪ (D₃ \ C))).card := by
    rw [← he]
    exact h2S
  omega

/-! ## What is *not* proved

`JSP90.AllCrossResidual`, the cases `|attachPoints G C| ≥ 4` of `JSP90.AttachThreeResidualRefined`, and
behind them `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary
blocker.  `jsp_000090_main` is deliberately not declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`. -/

end

end JSP90