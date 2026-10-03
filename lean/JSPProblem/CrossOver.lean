import JSPProblem.Segment
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Card

/-!
# JSP-000090, round 138 — `JSPProblem/CrossOver.lean`: **the one-point cross-over of a shortest odd
cycle**, and the exact reduction of the residual of the sharp case `k = 1`

Attack family 67.  Round 137 (`JSPProblem/Segment.lean`) proved the **segment lemma**

```lean
2 ≤ (C ∩ D).card  ⟹  2 ≤ (attachPoints G C ∩ D).card
```

for a shortest odd cycle `C` and an odd cycle `D ≠ C`, and closed the case of **no cross-over**
(`JSP90.NoCrossOver`, i.e. no odd cycle meets `C` in exactly one vertex) with the constants
`|attachPoints G C| - 1`, `1` and `2`.  A **one-point cross-over** `C ∩ D = {a}` was left as "the only
obstruction".

This round takes that obstruction seriously, measures it (`discovery/JSP-000090/r138.c`, questions `Q1`
to `Q11`), and shows that it is **not** an obstruction for the `|A| - 1` instance: the *right* hypothesis
is not the absence of cross-overs but the **absence of a cross-over at a given attachment point**.

## Part 1 — the new object

```lean
OnePointCrossOver G C D  :=  IsOddCycle G D ∧ D ≠ C ∧ (C ∩ D).card = 1
CrossOverPoint G C a    :=  ∃ D, OnePointCrossOver G C D ∧ a ∈ C ∩ D
```

* `JSP90.inter_eq_singleton_of_onePointCrossOver` — a cross-over is literally `C ∩ D = {a}`;
* **`JSP90.mem_attachPoints_of_onePointCrossOver`** — **THE CROSS-OVER POINT IS AN ATTACHMENT POINT**:
  the exit of the length-`0` segment.  Neither a packing hypothesis nor the minimality of `C` is
  needed;
* `JSP90.not_crossOverPoint_of_mem_boundary_of_noCrossOver` — `JSP90.NoCrossOver` of round 137 is
  exactly the *emptiness* of the set of cross-over points, so the two objects are formally comparable.

## Part 2 — the dichotomy

`JSP90.card_inter_attachPoints_eq_one_iff`:

```lean
|attachPoints G C ∩ D| = 1  ⟷  |C ∩ D| = 1
```

at packing number one, for `D ≠ C`.  So **every odd cycle meets the attachment points, and it meets
them in exactly one point exactly when it crosses `C` over** — and by Part 1 that point is then a
cross-over point.  Measured with no failures over the `986 787` graphs with `LocIndep 1` on
`n ≤ 7` vertices (`r138.c`, `Q1`).

## Part 3 — the main new theorem

`JSP90.hitsOddCycles_attachPoints_sdiff_of_not_crossOver`:

```lean
PackingNumberOne G → C shortest odd cycle → b ∈ attachPoints G C → 2 ≤ |attachPoints G C| →
  ¬ CrossOverPoint G C b → HitsOddCycles G (attachPoints G C \ {b})
```

**ERASING ONE ATTACHMENT POINT WHICH IS NOT A CROSS-OVER POINT LEAVES AN ODD-CYCLE
TRANSVERSAL.**  An odd cycle `D ≠ C` meets the attachment points (round 136); if it met them in `{b}`
alone, Part 2 would make `D` a cross-over at `b`, against the hypothesis; and `D = C` meets
`attachPoints G C \ {b}` because `|attachPoints G C| ≥ 2`.

So the constant-`|A| - 1` instance of round 137 **generalises**: `JSP90.NoCrossOver` is replaced by
"one attachment point is not a cross-over point", and cross-overs are then allowed.

## Part 4 — the instances (for every `k`, the constant is `|attachPoints G C| - 1`)

| statement | constant | hypothesis |
| --- | --- | --- |
| `JSP90.closeToBipartite_of_attachPoints_sdiff_of_not_crossOver` | `|A| - 1` | packing number one, `¬ CrossOverPoint G C b` |
| **`JSP90.closeToBipartite_one_of_card_attachPoints_eq_two_of_not_crossOver`** | **`1`** (optimal) | `|A| = 2` |
| **`JSP90.erdos73On_one_two_of_card_attachPoints_le_three_of_not_crossOver`** | **`2`** (optimal) | `|A| ≤ 3` |

The last two are **new instances of the headline theorem**: they hold even when one-point cross-overs
occur, which `JSP90.erdos73On_one_two_of_noCrossOver_of_card_attachPoints_le_three` explicitly forbids.
The optimality of the constant `2` at `k = 1` is machine-checked in `JSPProblem/SharpTwo.lean`.

## Part 5 — the *exact* form of what is left

Round 137's residual `JSP90.AttachThreeResidualRefined` asks for a two-element certificate **inside the
attachment points** when `3 ≤ |A|`.  Parts 3–4 answer it for every `|A| ≤ 3`, cross-overs included, so

```lean
JSP90.CrossOverResidual : … → 3 ≤ |attachPoints G C| →
  (4 ≤ |attachPoints G C| ∨ ∀ b ∈ attachPoints G C, CrossOverPoint G C b) →
  ∃ a b, a ≠ b ∧ a, b ∈ attachPoints G C ∧ HitsOddCycles G {a, b}
```

is **equivalent** to it: `JSP90.crossOverResidual_of_attachThreeResidualRefined` and
`JSP90.attachThreeResidualRefined_of_crossOverResidual` are both theorems of this file.  So the residual
is now read off exactly: *the case `4 ≤ |attachPoints G C|`, together with the case that every attachment
point is a cross-over point*.  The second disjunct is **measured to be empty** (`r138.c`, `Q9`: no graph
with `LocIndep 1` on `n ≤ 7` vertices has a shortest odd cycle all of whose attachment points are
cross-over points) and the first is **non-vacuous on seven vertices** (`r138.c`, `Q11`: `5 040`
shortest cycles with `4 ≤ |attachPoints G C|`, and in each of them a two-element certificate inside the
attachment points exists; smallest witness on `n = 7`, edges `0-3 0-5 0-6 1-2 1-4 1-6 2-3 2-5 3-4`).

## What is *not* proved

`JSP90.CrossOverResidual`, and behind it `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  `jsp_000090_main` is not declared, so
the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 400000

local instance crossOverDecidableEq : DecidableEq V := Classical.decEq V

/-! ### Part 0 — two small `Finset` lemmas, proved from scratch

The forms used below are not available verbatim in the pinned Mathlib revision. -/

/-- **A nonempty set which is not a singleton has an element different from a given one.** -/
theorem exists_mem_ne_of_nonempty_of_ne_singleton {s : Finset V} {a : V} (hne : s.Nonempty)
    (h : s ≠ {a}) : ∃ x ∈ s, x ≠ a := by
  obtain ⟨y, hy⟩ := hne
  by_cases hya : y = a
  · by_contra hc
    have hsub : s ⊆ {a} := by
      intro x hx
      have hxa : x = a := by
        by_contra hne'
        exact hc ⟨x, hx, hne'⟩
      exact hxa ▸ Finset.mem_singleton_self a
    have heq : s = {a} := by
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hx
        exact Finset.mem_singleton.mp (hsub hx)
      · intro hx
        rw [hx]
        exact hya ▸ hy
    exact h heq
  · exact ⟨y, hy, hya⟩

/-- **A set of one element containing `a` is `{a}`.** -/
theorem eq_singleton_of_card_eq_one_of_mem {s : Finset V} {a : V} (h1 : s.card = 1) (ha : a ∈ s) :
    s = {a} := by
  ext x
  simp only [Finset.mem_singleton]
  constructor
  · intro hx
    by_contra hne
    have hcard : ({a, x} : Finset V).card = 2 :=
      Finset.card_eq_two.mpr ⟨a, x, fun h => hne h.symm, rfl⟩
    have hle := Finset.card_le_card (show ({a, x} : Finset V) ⊆ s by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ha
      · exact hx)
    rw [hcard, h1] at hle
    omega
  · intro hx
    rw [hx]
    exact ha

/-! ## Part 1 — cross-over points

A **one-point cross-over** of `C` by `D` is an odd cycle `D ≠ C` meeting `C` in exactly one vertex: a
segment of length `0` of `C` along `D`.  Round 137's segment lemma says that this is the only way an odd
cycle can fail to meet the attachment points of `C` twice. -/

/-- **`D` CROSSES `C` OVER IN EXACTLY ONE POINT.** -/
def OnePointCrossOver (G : SimpleGraph V) (C D : Finset V) : Prop :=
  IsOddCycle G D ∧ D ≠ C ∧ (C ∩ D).card = 1

/-- **`a` IS A CROSS-OVER POINT OF `C`**: some odd cycle of `G` meets `C` in the single vertex `a`. -/
def CrossOverPoint (G : SimpleGraph V) (C : Finset V) (a : V) : Prop :=
  ∃ D : Finset V, OnePointCrossOver G C D ∧ a ∈ C ∩ D

/-- **A CROSS-OVER IS A SINGLETON INTERSECTION.** -/
theorem inter_eq_singleton_of_onePointCrossOver {C D : Finset V} (h : OnePointCrossOver G C D)
    {a : V} (ha : a ∈ C ∩ D) : C ∩ D = {a} :=
  eq_singleton_of_card_eq_one_of_mem h.2.2 ha

/-- **A CROSS-OVER POINT IS AN ATTACHMENT POINT.**

```lean
OnePointCrossOver G C D → a ∈ C ∩ D → a ∈ attachPoints G C
```

Round 137's exit lemma `JSP90.mem_attachPoints_exit` applied to the length-`0` segment: the successor of
`a` along `D` is a different vertex of `D` (`JSP90.CycleOrder.step_ne`), hence outside `C ∩ D = {a}`,
hence a fan vertex of `C` adjacent to `a`.  No packing hypothesis and no minimality of `C` are needed. -/
theorem mem_attachPoints_of_onePointCrossOver {C D : Finset V} (h : OnePointCrossOver G C D)
    {a : V} (ha : a ∈ C ∩ D) : a ∈ attachPoints G C := by
  have hsing : C ∩ D = {a} := inter_eq_singleton_of_onePointCrossOver h ha
  obtain ⟨o, -⟩ := h.1.cycleOrder
  obtain ⟨i, hi⟩ := (o.hmem a).mp (Finset.mem_inter.mp ha).2
  have hiC : o.f i ∈ C := by
    rw [hi]
    exact (Finset.mem_inter.mp ha).1
  have hsucc : o.f (cycSucc i) ∉ C := by
    intro hc
    have hmem : o.f (cycSucc i) ∈ C ∩ D :=
      Finset.mem_inter.mpr ⟨hc, (o.hmem _).mpr ⟨cycSucc i, rfl⟩⟩
    have hfa : o.f (cycSucc i) = a := by
      have hmem' : o.f (cycSucc i) ∈ ({a} : Finset V) := by
        rw [← hsing]
        exact hmem
      exact Finset.mem_singleton.mp hmem'
    exact o.step_ne i (hi.trans hfa.symm)
  rw [← hi]
  exact mem_attachPoints_exit hiC hsucc

/-- **THE CROSS-OVER POINTS LIE AMONG THE ATTACHMENT POINTS.** -/
theorem mem_attachPoints_of_crossOverPoint {C : Finset V} {a : V} (h : CrossOverPoint G C a) :
    a ∈ attachPoints G C := by
  obtain ⟨D, hD, ha⟩ := h
  exact mem_attachPoints_of_onePointCrossOver hD ha

/-- **NO CROSS-OVER MEANS NO CROSS-OVER POINT**: `JSP90.NoCrossOver` of round 137 is exactly the
emptiness of the set of cross-over points, so the two objects are formally comparable. -/
theorem not_crossOverPoint_of_mem_boundary_of_noCrossOver {C : Finset V} (hnc : NoCrossOver G C)
    {a : V} : ¬ CrossOverPoint G C a := by
  rintro ⟨D, hD, hmem⟩
  exact hnc D hD.1 hD.2.1 hD.2.2

/-! ## Part 2 — the dichotomy: an odd cycle meets the attachment points in one point exactly when it
crosses `C` over -/

/-- **AN ODD CYCLE MEETS THE ATTACHMENT POINTS IN EXACTLY ONE POINT EXACTLY WHEN IT CROSSES `C` OVER.**

```lean
PackingNumberOne G → C shortest odd cycle → D odd cycle → D ≠ C →
  (attachPoints G C ∩ D).card = 1 ↔ (C ∩ D).card = 1
```

* `⇐`: the attachment points lie on `C`, so `attachPoints G C ∩ D ⊆ C ∩ D`, and every odd cycle `≠ C`
  meets the attachment points (round 136) — hence the card is exactly `1`;
* `⇒`: the attachment points meet `C`, so `1 ≤ |C ∩ D|`, and two points of `C ∩ D` would give two
  attachment points by the segment lemma of round 137. -/
theorem card_inter_attachPoints_eq_one_iff (h : PackingNumberOne G) {C D : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hD : IsOddCycle G D) (hne : D ≠ C) :
    (attachPoints G C ∩ D).card = 1 ↔ (C ∩ D).card = 1 := by
  have hsub : attachPoints G C ∩ D ⊆ C ∩ D := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(mem_attachPoints.mp (Finset.mem_inter.mp hx).1).1,
      (Finset.mem_inter.mp hx).2⟩
  constructor
  · -- one attachment point ⟹ one point of `C ∩ D`
    intro h1
    have hle : (attachPoints G C ∩ D).card ≤ (C ∩ D).card := Finset.card_le_card hsub
    have hone : 1 ≤ (C ∩ D).card := by
      rw [h1] at hle
      omega
    by_contra hcon
    have h2 : 2 ≤ (C ∩ D).card := by omega
    have hseg := two_le_card_attachPoints_inter_of_card_inter_ge_two hC hshort hD hne h2
    omega
  · -- a cross-over meets the attachment points in exactly one point
    intro h1
    have hle : (attachPoints G C ∩ D).card ≤ (C ∩ D).card := Finset.card_le_card hsub
    have hle1 : (attachPoints G C ∩ D).card ≤ 1 := by
      rw [h1] at hle
      omega
    have hne0 : attachPoints G C ∩ D ≠ ∅ := by
      rw [Finset.inter_comm]
      exact inter_attachPoints_of_isOddCycle_ne_of_packing_one h hC hshort hD hne
    have hcardpos : 0 < (attachPoints G C ∩ D).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne0)
    omega

/-! ## Part 3 — erasing one attachment point which is not a cross-over point -/

/-- **ERASING ONE ATTACHMENT POINT WHICH IS NOT A CROSS-OVER POINT LEAVES AN ODD-CYCLE
TRANSVERSAL.**

```lean
PackingNumberOne G → C shortest odd cycle → b ∈ attachPoints G C → 2 ≤ |attachPoints G C| →
  ¬ CrossOverPoint G C b → HitsOddCycles G (attachPoints G C \ {b})
```

The main new theorem of the round.  Round 137 obtained the same conclusion under the stronger hypothesis
`JSP90.NoCrossOver G C` (no cross-over at all); here cross-overs are allowed at every attachment point but
`b`. -/
theorem hitsOddCycles_attachPoints_sdiff_of_not_crossOver (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    {b : V} (hbA : b ∈ attachPoints G C) (hb : ¬ CrossOverPoint G C b)
    (h2 : 2 ≤ (attachPoints G C).card) : HitsOddCycles G (attachPoints G C \ {b}) := by
  intro D hD
  by_cases hDC : D = C
  · -- `C` meets `attachPoints G C \ {b}`, because `|attachPoints G C| ≥ 2`
    obtain ⟨x, hx⟩ :=
      exists_mem_sdiff_singleton_of_card_ge_two (S := attachPoints G C) (a := b) h2
    have hxA : x ∈ attachPoints G C := (Finset.mem_sdiff.mp hx).1
    exact Finset.nonempty_iff_ne_empty.mp ⟨x, Finset.mem_inter.mpr
      ⟨hDC ▸ (mem_attachPoints.mp hxA).1, hx⟩⟩
  · -- `D` meets the attachment points; if in `{b}` alone, `D` crosses `C` over at `b`
    have hne0 : attachPoints G C ∩ D ≠ ∅ := by
      rw [Finset.inter_comm]
      exact inter_attachPoints_of_isOddCycle_ne_of_packing_one h hC hshort hD hDC
    have hne0' : (attachPoints G C ∩ D).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne0
    obtain ⟨x, hx⟩ := hne0'
    have hxA : x ∈ attachPoints G C := (Finset.mem_inter.mp hx).1
    have hxD : x ∈ D := (Finset.mem_inter.mp hx).2
    by_cases hxb : x = b
    · have hne : attachPoints G C ∩ D ≠ {b} := by
        intro heq
        refine hb ⟨D, ⟨hD, hDC, ?_⟩,
          Finset.mem_inter.mpr ⟨hxb ▸ (mem_attachPoints.mp hxA).1, hxb ▸ hxD⟩⟩
        exact (card_inter_attachPoints_eq_one_iff h hC hshort hD hDC).mp (by rw [heq]; simp)
      obtain ⟨y, hy, hyb⟩ := exists_mem_ne_of_nonempty_of_ne_singleton ⟨x, hx⟩ hne
      have hyA : y ∈ attachPoints G C := (Finset.mem_inter.mp hy).1
      have hyD : y ∈ D := (Finset.mem_inter.mp hy).2
      exact Finset.nonempty_iff_ne_empty.mp ⟨y, Finset.mem_inter.mpr
        ⟨hyD, Finset.mem_sdiff.mpr ⟨hyA, fun hc => hyb (Finset.mem_singleton.mp hc)⟩⟩⟩
    · exact Finset.nonempty_iff_ne_empty.mp ⟨x, Finset.mem_inter.mpr
        ⟨hxD, Finset.mem_sdiff.mpr ⟨hxA, fun hc => hxb (Finset.mem_singleton.mp hc)⟩⟩⟩

/-- **THE CARD OF THE ATTACHMENT POINTS WITH ONE OF THEM ERASED.** -/
theorem card_sdiff_singleton_of_mem_attachPoints {C : Finset V} {b : V}
    (hb : b ∈ attachPoints G C) : (attachPoints G C \ {b}).card = (attachPoints G C).card - 1 := by
  have hcard1 : ({b} : Finset V) ∩ attachPoints G C = {b} := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hb⟩⟩
  rw [Finset.card_sdiff, Finset.card_eq_one.mpr ⟨b, hcard1⟩]

/-! ## Part 4 — the instances, for every `k` -/

/-- **THE CONCLUSION OF ERDŐS #73 WITH THE CONSTANT `|attachPoints G C| - 1`, FOR EVERY `k`, ERASING AN
ATTACHMENT POINT WHICH IS NOT A CROSS-OVER POINT.**

This contains round 137's `JSP90.closeToBipartite_of_noCrossOver` (there, no cross-over point exists at
all, by `JSP90.not_crossOverPoint_of_mem_boundary_of_noCrossOver`), but it also applies when cross-overs
occur. -/
theorem closeToBipartite_of_attachPoints_sdiff_of_not_crossOver {m : ℕ} {k : ℕ} (_hG : LocIndep k G)
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) {b : V}
    (hbA : b ∈ attachPoints G C) (hb : ¬ CrossOverPoint G C b)
    (h2 : 2 ≤ (attachPoints G C).card) (hcard : (attachPoints G C \ {b}).card ≤ m) :
    CloseToBipartite m G :=
  (closeToBipartite_iff_hitsOddCycles (G := G) (m := m)).mpr
    ⟨attachPoints G C \ {b}, hcard,
      hitsOddCycles_attachPoints_sdiff_of_not_crossOver h hC hshort hbA hb h2⟩

/-- **THE CONSTANT `|attachPoints G C| - 1`, FOR EVERY `k`.** -/
theorem closeToBipartite_of_attachPoints_sdiff {m : ℕ} {k : ℕ} (hG : LocIndep k G)
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) {b : V}
    (hbA : b ∈ attachPoints G C) (hb : ¬ CrossOverPoint G C b)
    (h2 : 2 ≤ (attachPoints G C).card) (hcard : (attachPoints G C).card - 1 ≤ m) :
    CloseToBipartite m G :=
  closeToBipartite_of_attachPoints_sdiff_of_not_crossOver hG h hC hshort hbA hb h2 (by
    rw [card_sdiff_singleton_of_mem_attachPoints hbA]
    exact hcard)

/-- **THE OPTIMAL CONSTANT `1`, FOR EVERY `k`: TWO ATTACHMENT POINTS, ERASING ONE WHICH IS NOT A
CROSS-OVER POINT.**  The certificate is the single other attachment point, which lies on `C`. -/
theorem closeToBipartite_one_of_card_attachPoints_eq_two_of_not_crossOver {k : ℕ} (hG : LocIndep k G)
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) {b : V}
    (hbA : b ∈ attachPoints G C) (hb : ¬ CrossOverPoint G C b) (h2 : (attachPoints G C).card = 2) :
    CloseToBipartite 1 G :=
  closeToBipartite_of_attachPoints_sdiff_of_not_crossOver hG h hC hshort hbA hb (by rw [h2]) (by
    rw [card_sdiff_singleton_of_mem_attachPoints hbA]
    calc (attachPoints G C).card - 1 = 1 := by rw [h2]
      _ ≤ 1 := by omega)

/-- **THE OPTIMAL CONSTANT `2`, FOR EVERY `k`: AT MOST THREE ATTACHMENT POINTS, ONE OF WHICH IS NOT A
CROSS-OVER POINT.**  The certificate is the two attachment points other than it, and it lies on `C`.

Round 137's instance of the same constant needs `JSP90.NoCrossOver G C`, i.e. *no* cross-over at all;
here cross-overs are permitted at the other attachment points. -/
theorem erdos73On_one_two_of_card_attachPoints_le_three_of_not_crossOver {k : ℕ} (hG : LocIndep k G)
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) {b : V}
    (hbA : b ∈ attachPoints G C) (hb : ¬ CrossOverPoint G C b) (h3 : 3 ≤ (attachPoints G C).card)
    (hle : (attachPoints G C).card ≤ 3) : CloseToBipartite 2 G :=
  closeToBipartite_of_attachPoints_sdiff_of_not_crossOver hG h hC hshort hbA hb (by omega) (by
    rw [card_sdiff_singleton_of_mem_attachPoints hbA]
    omega)

/-- **THE SAME INSTANCE, WITH THE HYPOTHESIS "SOME ATTACHMENT POINT IS NOT A CROSS-OVER POINT".** -/
theorem erdos73On_one_two_of_card_attachPoints_le_three_of_exists_not_crossOver {k : ℕ}
    (hG : LocIndep k G) (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (h3 : 3 ≤ (attachPoints G C).card) (hle : (attachPoints G C).card ≤ 3)
    (hex : ∃ b, b ∈ attachPoints G C ∧ ¬ CrossOverPoint G C b) : CloseToBipartite 2 G := by
  obtain ⟨b, hbA, hb⟩ := hex
  exact erdos73On_one_two_of_card_attachPoints_le_three_of_not_crossOver hG h hC hshort hbA hb h3 hle

/-- **THE CONSTANT `1` INSTANCE, WITH THE HYPOTHESIS "SOME ATTACHMENT POINT IS NOT A CROSS-OVER
POINT".** -/
theorem closeToBipartite_one_of_card_attachPoints_eq_two_of_exists_not_crossOver {k : ℕ}
    (hG : LocIndep k G) (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (h2 : (attachPoints G C).card = 2)
    (hex : ∃ b, b ∈ attachPoints G C ∧ ¬ CrossOverPoint G C b) : CloseToBipartite 1 G := by
  obtain ⟨b, hbA, hb⟩ := hex
  exact closeToBipartite_one_of_card_attachPoints_eq_two_of_not_crossOver hG h hC hshort hbA hb h2

/-! ## Part 5 — the *exact* form of what is left

Round 137's residual `JSP90.AttachThreeResidualRefined` asks for a two-element certificate **inside the
attachment points** when `3 ≤ |A|`.  Parts 3–4 answer it for every `|A| ≤ 3`, cross-overs included, so
what is left is exactly the case `4 ≤ |A|`, together with the case that every attachment point is a
cross-over point. -/

/-- **THE RESIDUAL OF THE SHARP CASE `k = 1`, IN CROSS-OVER FORM.**

```lean
LocIndep 1 G → C shortest odd cycle → 3 ≤ |attachPoints G C| →
  (4 ≤ |attachPoints G C| ∨ ∀ b ∈ attachPoints G C, CrossOverPoint G C b) →
  ∃ a b, a ≠ b ∧ a, b ∈ attachPoints G C ∧ HitsOddCycles G {a, b}
```

The certificate is required to lie **on the shortest odd cycle `C`**, as in round 137. -/
def CrossOverResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      3 ≤ (attachPoints G C).card →
      (4 ≤ (attachPoints G C).card ∨ ∀ b ∈ attachPoints G C, CrossOverPoint G C b) →
      ∃ a b : W, a ≠ b ∧ a ∈ attachPoints G C ∧ b ∈ attachPoints G C ∧
        HitsOddCycles G ({a, b} : Finset W)

/-- **THE SHARP CASE `k = 1` OF ERDŐS PROBLEM #73, WITH THE CONSTANT `2`, FROM THE CROSS-OVER
RESIDUAL.**  The same four cases as in `JSP90.erdos73On_one_two_of_attachThreeResidualRefined`, with the
new instances of Part 4 added. -/
theorem erdos73On_one_two_of_crossOverResidual (h : CrossOverResidual.{u}) : Erdős73On.{u} 1 2 := by
  intro W instW G hG
  rw [closeToBipartite_iff_hitsOddCycles]
  by_cases hex : ∃ C : Finset W, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle (G := G) hex
    obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
    have hp1 : PackingNumberOne G := packingNumberOne_of_locIndep_one hG
    by_cases hne : (boundary G C).Nonempty
    · by_cases hb : (attachPoints G C).card ≤ 2
      · exact ⟨attachPoints G C, hb,
          hitsOddCycles_attachPoints_of_packing_one hp1 hC hshort hne⟩
      · by_cases hex2 : ∃ b, b ∈ attachPoints G C ∧ ¬ CrossOverPoint G C b
        · by_cases hle : (attachPoints G C).card ≤ 3
          · obtain ⟨b, hbA, hbnot⟩ := hex2
            have hX : HitsOddCycles G (attachPoints G C \ {b}) :=
              hitsOddCycles_attachPoints_sdiff_of_not_crossOver hp1 hC hshort hbA hbnot (by omega)
            obtain ⟨a, b', ha, hb', hab'⟩ :=
              exists_pair_ne_of_card_ge_two (by
                rw [card_sdiff_singleton_of_mem_attachPoints hbA]
                omega)
            have hcard2 : ({a, b'} : Finset W).card = 2 := Finset.card_eq_two.mpr ⟨a, b', hab', rfl⟩
            have heq : attachPoints G C \ {b} = {a, b'} := by
              refine (Finset.eq_of_subset_of_card_le (s := ({a, b'} : Finset W))
                (t := attachPoints G C \ {b}) (fun z hz => ?_) (by
                  rw [card_sdiff_singleton_of_mem_attachPoints hbA, hcard2]
                  omega)).symm
              rcases Finset.mem_insert.mp hz with rfl | hz
              · exact ha
              · exact (Finset.mem_singleton.mp hz) ▸ hb'
            refine ⟨{a, b'}, card_le_two_pair hab', fun D hD => heq ▸ hX D hD⟩
          · obtain ⟨a, b, hab, ha, hbA, hh⟩ :=
              h W instW G hG C hC hshort (by omega) (Or.inl (by omega))
            exact ⟨{a, b}, card_le_two_pair hab, fun D hD => hh D hD⟩
        · obtain ⟨a, b, hab, ha, hbA, hh⟩ := h W instW G hG C hC hshort (by omega) (by
            refine Or.inr ?_
            intro b' hb'
            by_contra hnb
            exact hex2 ⟨b', hb', hnb⟩)
          exact ⟨{a, b}, card_le_two_pair hab, fun D hD => hh D hD⟩
    · have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hh : HitsOddCycles G ({c} : Finset W) := by
        simpa [h0] using hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc
      exact ⟨{c}, by simp, hh⟩
  · exact ⟨∅, by simp, fun D hD => absurd ⟨D, hD⟩ hex⟩

/-- **ROUND 137'S RESIDUAL IS IMPLIED BY THE CROSS-OVER RESIDUAL.** -/
theorem attachThreeResidualRefined_of_crossOverResidual (h : CrossOverResidual.{u}) :
    AttachThreeResidualRefined.{u} := by
  intro W instW G hG C hC hshort h3
  have hp1 : PackingNumberOne G := packingNumberOne_of_locIndep_one hG
  by_cases hex2 : ∃ b, b ∈ attachPoints G C ∧ ¬ CrossOverPoint G C b
  · obtain ⟨b, hbA, hbnot⟩ := hex2
    by_cases hle : (attachPoints G C).card ≤ 3
    · have hX : HitsOddCycles G (attachPoints G C \ {b}) :=
        hitsOddCycles_attachPoints_sdiff_of_not_crossOver hp1 hC hshort hbA hbnot (by omega)
      obtain ⟨a, b', ha, hb', hab'⟩ :=
        exists_pair_ne_of_card_ge_two (by
          rw [card_sdiff_singleton_of_mem_attachPoints hbA]
          omega)
      have hcard2 : ({a, b'} : Finset W).card = 2 := Finset.card_eq_two.mpr ⟨a, b', hab', rfl⟩
      have heq : attachPoints G C \ {b} = {a, b'} := by
        refine (Finset.eq_of_subset_of_card_le (s := ({a, b'} : Finset W))
          (t := attachPoints G C \ {b}) (fun z hz => ?_) (by
            rw [card_sdiff_singleton_of_mem_attachPoints hbA, hcard2]
            omega)).symm
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact ha
        · exact (Finset.mem_singleton.mp hz) ▸ hb'
      refine ⟨a, b', hab', (Finset.mem_sdiff.mp ha).1, (Finset.mem_sdiff.mp hb').1, fun D hD => ?_⟩
      exact heq ▸ hX D hD
    · obtain ⟨a, b', hab', ha, hb', hh⟩ := h W instW G hG C hC hshort h3 (Or.inl (by omega))
      exact ⟨a, b', hab', ha, hb', hh⟩
  · obtain ⟨a, b', hab', ha, hb', hh⟩ := h W instW G hG C hC hshort h3 (by
      refine Or.inr ?_
      intro b hbA
      by_contra hnb
      exact hex2 ⟨b, hbA, hnb⟩)
    exact ⟨a, b', hab', ha, hb', hh⟩

/-- **THE CROSS-OVER RESIDUAL IS IMPLIED BY ROUND 137'S RESIDUAL: the two are equivalent.**

So the residual of the sharp case `k = 1` is now read off exactly: *either `4 ≤ |attachPoints G C|`,
or every attachment point of `C` is a cross-over point*. -/
theorem crossOverResidual_of_attachThreeResidualRefined (h : AttachThreeResidualRefined.{u}) :
    CrossOverResidual.{u} := by
  intro W instW G hG C hC hshort h3 _
  obtain ⟨a, b, hab, ha, hb, hh⟩ := h W instW G hG C hC hshort h3
  exact ⟨a, b, hab, ha, hb, hh⟩

/-! ## What is *not* proved

`JSP90.CrossOverResidual`, and behind it `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  `jsp_000090_main` is not declared, so the
harness keeps reporting `missing_theorems = ["jsp_000090_main"]`. -/

#print axioms JSP90.exists_mem_ne_of_nonempty_of_ne_singleton
#print axioms JSP90.eq_singleton_of_card_eq_one_of_mem
#print axioms JSP90.inter_eq_singleton_of_onePointCrossOver
#print axioms JSP90.mem_attachPoints_of_onePointCrossOver
#print axioms JSP90.mem_attachPoints_of_crossOverPoint
#print axioms JSP90.not_crossOverPoint_of_mem_boundary_of_noCrossOver
#print axioms JSP90.card_inter_attachPoints_eq_one_iff
#print axioms JSP90.hitsOddCycles_attachPoints_sdiff_of_not_crossOver
#print axioms JSP90.card_sdiff_singleton_of_mem_attachPoints
#print axioms JSP90.closeToBipartite_of_attachPoints_sdiff_of_not_crossOver
#print axioms JSP90.closeToBipartite_of_attachPoints_sdiff
#print axioms JSP90.closeToBipartite_one_of_card_attachPoints_eq_two_of_not_crossOver
#print axioms JSP90.erdos73On_one_two_of_card_attachPoints_le_three_of_not_crossOver
#print axioms JSP90.erdos73On_one_two_of_card_attachPoints_le_three_of_exists_not_crossOver
#print axioms JSP90.closeToBipartite_one_of_card_attachPoints_eq_two_of_exists_not_crossOver
#print axioms JSP90.erdos73On_one_two_of_crossOverResidual
#print axioms JSP90.attachThreeResidualRefined_of_crossOverResidual
#print axioms JSP90.crossOverResidual_of_attachThreeResidualRefined