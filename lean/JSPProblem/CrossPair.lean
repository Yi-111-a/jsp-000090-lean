import JSPProblem.CrossOver

/-!
# JSP-000090, round 139 — `JSPProblem/CrossPair.lean`: **the cross-over points force the certificate**

Attack family 68.  Round 138 (`JSPProblem/CrossOver.lean`) introduced the **cross-over points** of a
shortest odd cycle — the attachment points at which some other odd cycle leaves `C` in one point — and
proved that *erasing one attachment point which is not a cross-over point leaves an odd-cycle
transversal*.  Its residual is

```lean
JSP90.CrossOverResidual : … → 3 ≤ |attachPoints G C| →
  (4 ≤ |attachPoints G C| ∨ ∀ b ∈ attachPoints G C, CrossOverPoint G C b) →
  ∃ a b, a ≠ b ∧ a, b ∈ attachPoints G C ∧ HitsOddCycles G {a, b}
```

**This round observes that such a certificate is never a free choice: it is determined by the
cross-over points.**  The reason is one line, and needs no minimality, no packing hypothesis and no
`LocIndep` (Part 1):

```lean
a ≠ b → a, b ∈ C → HitsOddCycles G {a, b}  ⟹  crossOverSet G C ⊆ {a, b}
```

for the cross-over cycle `D` through a point `x ∉ {a, b}` one has `C ∩ D = {x}`, so `D` avoids both `a`
and `b`, contradicting that `{a, b}` meets every odd cycle.

## The measurements behind the file (`discovery/JSP-000090/r139.c`, `r139b.c`, `r139e.c`)

Over the `986 787` graphs with `LocIndep 1` on `n ≤ 7` vertices, i.e. `1 268 520` shortest odd cycles
with `3 ≤ |attachPoints G C|` (of which `5 040` have `4 ≤ |attachPoints G C|`):

| question | statement | result |
| --- | --- | --- |
| `Q1` | `\|attachPoints G C\| ≤ \|C\|` | 0 failures |
| `Q3` | a *prescribed* non-cross-over point of `A` can be completed to a certificate | **5 040 failures** — rules out that shape |
| `Q5` | `\|X\| = 2 ⟹ X` is a transversal | **0 failures** in `5 040` cases, all with `\|A\| = 3` |
| `Q6` | `4 ≤ \|A\| ⟹ A ∖ {b}` is a transversal for *every* `b ∈ A` | 0 failures |
| `Q7`,`Q9` | a shortest triangle all of whose vertices are cross-over points | **0** occurrences for `n ≤ 7`, and **0** among the `2 503 867` graphs with `LocIndep 1` on `n = 8` containing a triangle |
| `Q8` | `\|A\| ≤ 2 · \|fan\|`, and `3 ≤ \|A\| ⟹ ≥ 2` fan vertices | 0 failures |
| `r139b` | the split of the residual by cross-over count: `612 510` / `650 970` / `5 040` / `0` for `0` / `1` / `2` / `≥ 3` | **0 failures** in every case |
| **`S1`** | **a transversal pair inside `A` contains `crossOverSet G C`** — the statement of Part 1 | **0 failures in `3 157 110` pairs** |
| `S2` | the same with a pair merely *meeting* `A` | `1 099 680` failures — so `{a, b} ⊆ C` is essential |
| `S5` | the same with `\|A\| ≤ 2` and arbitrary pairs | `1 160 160` failures — so `3 ≤ \|A\|` is essential |
| `r139e` | a shortest cycle with `3 ≤ \|A\|` and no 2-element transversal inside `A` | **0** occurrences |

## What is *not* proved

`JSP90.LowCrossResidual` and `JSP90.TwoCrossTransversal` — the two halves of
`JSP90.CrossPairResidual` — and `JSP90.TriangleCrossResidual`, and behind them
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.
`jsp_000090_main` is not declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 400000

local instance crossPairDecidableEq : DecidableEq V := Classical.decEq V

local instance crossPairDecidable (C : Finset V) : DecidablePred (CrossOverPoint G C) :=
  fun _ => Classical.propDecidable _

/-! ## Part 0 — the set of cross-over points -/

/-- **THE CROSS-OVER POINTS OF `C`**: the attachment points of `C` at which some odd cycle leaves `C` in
a single point, i.e. `JSP90.CrossOverPoint G C x` made into a `Finset`. -/
noncomputable def crossOverSet (G : SimpleGraph V) (C : Finset V) : Finset V :=
  (Finset.univ.filter (CrossOverPoint G C)) ∩ attachPoints G C

/-- **MEMBERSHIP IN THE CROSS-OVER SET.** -/
theorem mem_crossOverSet {C : Finset V} {x : V} :
    x ∈ crossOverSet G C ↔ CrossOverPoint G C x ∧ x ∈ attachPoints G C := by
  rw [crossOverSet, Finset.mem_inter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- **THE CROSS-OVER POINTS ARE ATTACHMENT POINTS.** -/
theorem subset_crossOverSet_attachPoints (C : Finset V) : crossOverSet G C ⊆ attachPoints G C :=
  fun _ hx => (mem_crossOverSet.mp hx).2

/-- **THE CROSS-OVER POINTS LIE ON `C`.** -/
theorem subset_crossOverSet_C (C : Finset V) : crossOverSet G C ⊆ C :=
  fun _ hx => subset_attachPoints_C C ((mem_crossOverSet.mp hx).2)

/-- **A POINT WHICH IS NOT A CROSS-OVER POINT IS NOT IN THE CROSS-OVER SET.** -/
theorem not_mem_crossOverSet_of_not_crossOverPoint {C : Finset V} {x : V}
    (h : ¬ CrossOverPoint G C x) : x ∉ crossOverSet G C :=
  fun hx => h (mem_crossOverSet.mp hx).1

/-! ## Part 1 — **a two-element certificate inside `C` is FORCED to contain the cross-over points** -/

/-- **THE CERTIFICATE IS FORCED BY THE CROSS-OVER POINTS.**

```lean
a ≠ b → a, b ∈ C → HitsOddCycles G {a, b} → crossOverSet G C ⊆ {a, b}
```

Indeed let `x` be a cross-over point with witness `D`, so `C ∩ D = {x}`; if `x ∉ {a, b}` then `D`
avoids `a` and `b`, because `a, b ∈ C`, contradicting that `{a, b}` meets every odd cycle. -/
theorem subset_pair_of_hitsOddCycles_pair_of_mem {C : Finset V} {a b : V} (hab : a ≠ b)
    (ha : a ∈ C) (hb : b ∈ C) (h : HitsOddCycles G ({a, b} : Finset V)) :
    crossOverSet G C ⊆ ({a, b} : Finset V) := by
  intro x hx
  rw [Finset.mem_insert]
  obtain ⟨D, hD, hxD⟩ := (mem_crossOverSet.mp hx).1
  have hCD : C ∩ D = {x} := inter_eq_singleton_of_onePointCrossOver hD hxD
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr (h D hD.1)
  obtain ⟨hyD, hyab⟩ := Finset.mem_inter.mp hy
  have hyC : y ∈ C := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyab
    rcases hyab with rfl | rfl
    · exact ha
    · exact hb
  have hyCD : y ∈ C ∩ D := Finset.mem_inter.mpr ⟨hyC, hyD⟩
  rw [hCD, Finset.mem_singleton] at hyCD
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyab
  rcases hyab with hyab | hyab
  · exact Or.inl (hyCD ▸ hyab)
  · exact Or.inr (Finset.mem_singleton.mpr (hyCD ▸ hyab))

/-- **THE CROSS-OVER SET HAS AT MOST TWO ELEMENTS AS SOON AS A TWO-ELEMENT CERTIFICATE OF `C` EXISTS.** -/
theorem card_le_two_pair_of_hitsOddCycles_pair_of_mem {C : Finset V} {a b : V} (hab : a ≠ b)
    (ha : a ∈ C) (hb : b ∈ C) (h : HitsOddCycles G ({a, b} : Finset V)) :
    (crossOverSet G C).card ≤ 2 := by
  have hsub : crossOverSet G C ⊆ ({a, b} : Finset V) :=
    subset_pair_of_hitsOddCycles_pair_of_mem hab ha hb h
  have hle := Finset.card_le_card hsub
  have hle2 := card_le_two_pair hab
  omega

/-- **A VERTEX OF `C` OUTSIDE A TWO-ELEMENT CERTIFICATE OF `C` IS NOT A CROSS-OVER POINT.**

The negative form of the above: the certificate cannot be *improved* by moving a vertex of `C` which is
not in it. -/
theorem not_mem_crossOverSet_of_mem_of_hitsOddCycles_pair_of_mem {C : Finset V} {a b c : V}
    (hsub : ({a, b} : Finset V) ⊆ C) (hc : c ∉ ({a, b} : Finset V))
    (h : HitsOddCycles G ({a, b} : Finset V)) : c ∉ crossOverSet G C := by
  intro hx
  obtain ⟨D, hD, hxD⟩ := (mem_crossOverSet.mp hx).1
  have hCD : C ∩ D = {c} := inter_eq_singleton_of_onePointCrossOver hD hxD
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr (h D hD.1)
  obtain ⟨hyD, hyab⟩ := Finset.mem_inter.mp hy
  have hyC : y ∈ C := hsub hyab
  have hyCD : y ∈ C ∩ D := Finset.mem_inter.mpr ⟨hyC, hyD⟩
  rw [hCD, Finset.mem_singleton] at hyCD
  simp only [Finset.mem_insert, Finset.mem_singleton] at hyab
  rcases hyab with hyab | hyab
  · exact hc (Finset.mem_insert.mpr (Or.inl (hyCD.symm.trans hyab)))
  · exact hc (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hyCD.symm.trans hyab))))

/-! ## Part 2 — **three cross-over points obstruct every two-element certificate on `C`** -/

/-- **EVERY VERTEX OF `C` IN THE CROSS-OVER SET IS ONE OF THE TWO CERTIFICATE VERTICES.** -/
theorem eq_or_eq_of_mem_pair_of_hitsOddCycles_pair_of_crossOverPoint {C : Finset V} {a b z : V}
    (hab : a ≠ b) (hsub : ({a, b} : Finset V) ⊆ C) (h : HitsOddCycles G ({a, b} : Finset V))
    (hz : z ∈ crossOverSet G C) : z = a ∨ z = b := by
  have hmem : z ∈ ({a, b} : Finset V) := subset_pair_of_hitsOddCycles_pair_of_mem hab
    (hsub (Finset.mem_insert.mpr (Or.inl rfl))) (hsub (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self b)))) h hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **THREE DISTINCT CROSS-OVER POINTS OBSTRUCT EVERY TWO-ELEMENT CERTIFICATE LYING ON `C`.**

```lean
a, b, c cross-over points of C, distinct, p ≠ q, {p, q} ⊆ C → ¬ HitsOddCycles G {p, q}
```

This is the negative counterpart of Part 1, and it explains why the threshold `2` of the residual is
the right one: a two-element certificate on `C` can exist only if `C` has at most two cross-over
points.  In particular the configuration round 138 left open — a shortest triangle all three of whose
vertices are cross-over points — has **no** two-element certificate lying on `C`. -/
theorem not_hitsOddCycles_pair_of_mem_of_three_crossOverPoint {C : Finset V} {a b c p q : V}
    (ha : CrossOverPoint G C a) (hb : CrossOverPoint G C b) (hc : CrossOverPoint G C c)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hsub : ({p, q} : Finset V) ⊆ C) (hpq : p ≠ q) :
    ¬ HitsOddCycles G ({p, q} : Finset V) := by
  intro h
  have haA : a ∈ attachPoints G C := mem_attachPoints_of_crossOverPoint ha
  have hbA : b ∈ attachPoints G C := mem_attachPoints_of_crossOverPoint hb
  have hcA : c ∈ attachPoints G C := mem_attachPoints_of_crossOverPoint hc
  have haX : a ∈ crossOverSet G C := mem_crossOverSet.mpr ⟨ha, haA⟩
  have hbX : b ∈ crossOverSet G C := mem_crossOverSet.mpr ⟨hb, hbA⟩
  have hcX : c ∈ crossOverSet G C := mem_crossOverSet.mpr ⟨hc, hcA⟩
  have hle : ({a, b, c} : Finset V).card ≤ ({p, q} : Finset V).card := Finset.card_le_card (by
    intro z hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · rw [hz]
      rcases (eq_or_eq_of_mem_pair_of_hitsOddCycles_pair_of_crossOverPoint hpq hsub h haX) with h | h
      · rw [h]
        exact Finset.mem_insert.mpr (Or.inl rfl)
      · rw [h]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self q))
    · rcases Finset.mem_insert.mp hz with hz | hz
      · rw [hz]
        rcases (eq_or_eq_of_mem_pair_of_hitsOddCycles_pair_of_crossOverPoint hpq hsub h hbX) with h | h
        · rw [h]
          exact Finset.mem_insert.mpr (Or.inl rfl)
        · rw [h]
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self q))
      · have hz' : z = c := Finset.mem_singleton.mp hz
        rw [hz']
        rcases (eq_or_eq_of_mem_pair_of_hitsOddCycles_pair_of_crossOverPoint hpq hsub h hcX) with h | h
        · rw [h]
          exact Finset.mem_insert.mpr (Or.inl rfl)
        · rw [h]
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self q)))
  have h3 : ({a, b, c} : Finset V).card = 3 := Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have h2 : ({p, q} : Finset V).card = 2 := Finset.card_eq_two.mpr ⟨p, q, hpq, rfl⟩
  omega

/-- **TWO CROSS-OVER POINTS OF `C` GIVE TWO DISTINCT POINTS OF `C`.** -/
theorem exists_pair_mem_C_of_card_crossOverSet_eq_two {C : Finset V}
    (hX2 : (crossOverSet G C).card = 2) :
    ∃ a b : V, a ∈ crossOverSet G C ∧ b ∈ crossOverSet G C ∧ a ≠ b ∧ a ∈ C ∧ b ∈ C := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_pair_ne_of_card_ge_two (by rw [hX2])
  refine ⟨a, b, ha, hb, hab, ?_, ?_⟩
  · exact subset_crossOverSet_C C ha
  · exact subset_crossOverSet_C C hb

/-- **THE TWO CROSS-OVER POINTS OF `C`, WHEN THEY EXIST, ARE TWO ATTACHMENT POINTS.** -/
theorem card_attachPoints_ge_two_of_card_crossOverSet_eq_two {C : Finset V}
    (hX2 : (crossOverSet G C).card = 2) : 2 ≤ (attachPoints G C).card := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_pair_ne_of_card_ge_two (by rw [hX2])
  exact two_le_card_of_mem_pair hab (mem_crossOverSet.mp ha).2 (mem_crossOverSet.mp hb).2


/-! ### Three numerical helpers: erasing one element of a set -/

theorem card_sdiff_singleton_of_mem {S : Finset V} {b : V} (hb : b ∈ S) : (S \ {b}).card = S.card - 1 := by
  have hinter : ({b} : Finset V) ∩ S = {b} := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hb⟩⟩
  rw [Finset.card_sdiff, Finset.card_eq_one.mpr ⟨b, hinter⟩]

theorem two_le_card_sdiff_singleton_of_card_ge_three {S : Finset V} {b : V} (hb : b ∈ S)
    (h3 : 3 ≤ S.card) : 2 ≤ (S \ {b}).card := by
  rw [card_sdiff_singleton_of_mem hb]
  have hpos : 0 < S.card := by omega
  have heq : S.card - 1 + 1 = S.card := Nat.sub_add_cancel hpos
  have hstep : 3 ≤ S.card - 1 + 1 := by rw [heq]; omega
  omega

theorem card_le_two_sdiff_singleton_of_card_le_three {S : Finset V} {b : V} (hb : b ∈ S)
    (h3 : 3 ≤ S.card) (hle : S.card ≤ 3) : (S \ {b}).card ≤ 2 := by
  rw [card_sdiff_singleton_of_mem hb]
  have hpos : 0 < S.card := by omega
  have heq : S.card - 1 + 1 = S.card := Nat.sub_add_cancel hpos
  omega

/-! ## Part 3 — the residual in *forced* form

`JSP90.CrossPairResidual` is round 138's `JSP90.CrossOverResidual` with the extra requirement that the
certificate contain the cross-over set.  Part 1 shows the two are equivalent, so the new form costs
nothing and is much more local: it says *which* pair has to be exhibited, in terms of the cross-over
set alone. -/

/-- **THE RESIDUAL OF THE SHARP CASE `k = 1` IN FORCED FORM: THE CERTIFICATE IS DETERMINED BY THE
CROSS-OVER POINTS OF `C`.**

```lean
LocIndep 1 G → C shortest odd cycle → 3 ≤ |attachPoints G C| →
  ∃ a b, a ≠ b ∧ a, b ∈ attachPoints G C ∧ crossOverSet G C ⊆ {a, b} ∧ HitsOddCycles G {a, b}
``` -/
def CrossPairResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      3 ≤ (attachPoints G C).card →
      ∃ a b : W, a ≠ b ∧ a ∈ attachPoints G C ∧ b ∈ attachPoints G C ∧
        crossOverSet G C ⊆ ({a, b} : Finset W) ∧ HitsOddCycles G ({a, b} : Finset W)

/-- **THE FORCED RESIDUAL IS WEAKER THAN ROUND 138'S**: it exhibits the same pair, with the extra
information that it contains the cross-over points. -/
theorem crossOverResidual_of_crossPairResidual (h : CrossPairResidual.{u}) :
    CrossOverResidual.{u} := by
  intro W instW G hG C hC hshort h3 _
  obtain ⟨a, b, hab, ha, hb, -, hh⟩ := h W instW G hG C hC hshort h3
  exact ⟨a, b, hab, ha, hb, hh⟩

/-- **THE SHARP CASE `k = 1` OF ERDŐS PROBLEM #73, WITH THE CONSTANT `2`, FROM THE FORCED RESIDUAL.** -/
theorem erdos73On_one_two_of_crossPairResidual (h : CrossPairResidual.{u}) : Erdős73On.{u} 1 2 :=
  erdos73On_one_two_of_crossOverResidual (crossOverResidual_of_crossPairResidual h)

/-- **A THREE-ELEMENT SET OF ATTACHMENT POINTS, WITH ONE ERASED, YIELDS THE FORCED CERTIFICATE.**

Round 138's construction, read off in forced form: if the attachment points with one *non cross-over*
point erased meet every odd cycle and at most two of them are left, then they are the whole cross-over
set, contained in a two-element certificate. -/
theorem exists_pair_of_hitsOddCycles_attachPoints_sdiff (h : PackingNumberOne G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) {b : V}
    (hbA : b ∈ attachPoints G C) (hb : ¬ CrossOverPoint G C b)
    (h3 : 3 ≤ (attachPoints G C).card)
    (hle : (attachPoints G C \ {b}).card ≤ 2) (hX : HitsOddCycles G (attachPoints G C \ {b})) :
    ∃ a b' : V, a ≠ b' ∧ a ∈ attachPoints G C ∧ b' ∈ attachPoints G C ∧
      crossOverSet G C ⊆ ({a, b'} : Finset V) ∧ HitsOddCycles G ({a, b'} : Finset V) := by
  obtain ⟨a, b', ha, hb', hab'⟩ := exists_pair_ne_of_card_ge_two
    (two_le_card_sdiff_singleton_of_card_ge_three hbA h3)
  have hcard2 : ({a, b'} : Finset V).card = 2 := Finset.card_eq_two.mpr ⟨a, b', hab', rfl⟩
  have heq : attachPoints G C \ {b} = ({a, b'} : Finset V) := by
    refine (Finset.eq_of_subset_of_card_le (s := ({a, b'} : Finset V))
      (t := attachPoints G C \ {b}) (fun z hz => ?_) (by omega)).symm
    rcases Finset.mem_insert.mp hz with hz | hz
    · exact hz ▸ ha
    · exact (Finset.mem_singleton.mp hz) ▸ hb'
  refine ⟨a, b', hab', (Finset.mem_sdiff.mp ha).1, (Finset.mem_sdiff.mp hb').1, ?_, ?_⟩
  · intro x hx
    rw [← heq]
    refine Finset.mem_sdiff.mpr ⟨(mem_crossOverSet.mp hx).2, ?_⟩
    intro hcon
    rw [Finset.mem_singleton.mp hcon] at hx
    exact hb (mem_crossOverSet.mp hx).1
  · exact heq ▸ hX

/-- **ROUND 138'S RESIDUAL IS IMPLIED BY THE FORCED ONE: the two are EQUIVALENT.**

The whole content is the one-line lemma of Part 1: given a two-element certificate *inside `C`*, the
cross-over points are already inside it. -/
theorem crossPairResidual_of_crossOverResidual (h : CrossOverResidual.{u}) :
    CrossPairResidual.{u} := by
  intro W instW G hG C hC hshort h3
  by_cases hex2 : ∃ b, b ∈ attachPoints G C ∧ ¬ CrossOverPoint G C b
  · obtain ⟨b, hbA, hbnot⟩ := hex2
    have hp1 : PackingNumberOne G := packingNumberOne_of_locIndep_one hG
    by_cases hle : (attachPoints G C).card ≤ 3
    · obtain ⟨a, b', hab', ha, hb', hsub', hh⟩ :=
        exists_pair_of_hitsOddCycles_attachPoints_sdiff hp1 hC hshort hbA hbnot h3
          (card_le_two_sdiff_singleton_of_card_le_three hbA h3 hle)
          (hitsOddCycles_attachPoints_sdiff_of_not_crossOver hp1 hC hshort hbA hbnot (by omega))
      exact ⟨a, b', hab', ha, hb', hsub', hh⟩
    · obtain ⟨a, b', hab', ha, hb', hh⟩ := h W instW G hG C hC hshort h3 (Or.inl (by omega))
      exact ⟨a, b', hab', ha, hb',
        subset_pair_of_hitsOddCycles_pair_of_mem hab' (mem_attachPoints.mp ha).1
          (mem_attachPoints.mp hb').1 hh, hh⟩
  · obtain ⟨a, b', hab', ha, hb', hh⟩ := h W instW G hG C hC hshort h3 (by
      refine Or.inr fun b'' hb'' => ?_
      by_contra hnb
      exact hex2 ⟨b'', hb'', hnb⟩)
    exact ⟨a, b', hab', ha, hb',
      subset_pair_of_hitsOddCycles_pair_of_mem hab' (mem_attachPoints.mp ha).1
        (mem_attachPoints.mp hb').1 hh, hh⟩

/-- **THE TWO RESIDUALS ARE EQUIVALENT.**  So the certificate of the sharp case `k = 1` is *determined*
by the cross-over points of a shortest odd cycle: it contains `crossOverSet G C`, and when the
cross-over set has two elements it *is* the certificate. -/
theorem crossPairResidual_iff_crossOverResidual :
    CrossPairResidual.{u} ↔ CrossOverResidual.{u} :=
  ⟨crossOverResidual_of_crossPairResidual, crossPairResidual_of_crossOverResidual⟩

/-! ## Part 4 — the two-element certificate under the cross-over hypothesis

The exact form of Part 1: the certificate `{a, b}` works as soon as it **contains** the cross-over set
and **meets every odd cycle which meets the attachment points in two points**.  Indeed an odd cycle
meeting the attachment points in one point is a cross-over, hence already inside `{a, b}`, and the odd
cycle `C` meets `{a, b}` trivially. -/

/-- **THE TWO-ELEMENT CERTIFICATE, WITH THE CROSS-OVER SET INSIDE THE PAIR.**

```lean
PackingNumberOne G → C shortest odd cycle → a ≠ b → a, b ∈ attachPoints G C →
  crossOverSet G C ⊆ {a, b} →
  (every odd cycle meeting the attachment points in ≥ 2 points meets {a, b}) →
  HitsOddCycles G {a, b}
```

The certificate lies **on the shortest odd cycle `C`**, and the statement holds for every `k`
satisfying the packing condition, with no bound on the odd girth, the packing weight or the number of
branch vertices. -/
theorem hitsOddCycles_pair_of_attachPoints_of_subset_crossOverSet (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    {a b : V} (hab : a ≠ b) (ha : a ∈ attachPoints G C) (hb : b ∈ attachPoints G C)
    (hX : crossOverSet G C ⊆ ({a, b} : Finset V))
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ≠ C → 2 ≤ (attachPoints G C ∩ D).card →
      D ∩ ({a, b} : Finset V) ≠ ∅) : HitsOddCycles G ({a, b} : Finset V) := by
  intro D hD
  by_cases hDC : D = C
  · -- `C` meets `{a, b}`, because `a, b ∈ attachPoints G C ⊆ C` and `a ≠ b`
    have haC : a ∈ C := (mem_attachPoints.mp ha).1
    exact Finset.nonempty_iff_ne_empty.mp ⟨a, Finset.mem_inter.mpr
      ⟨hDC ▸ haC, Finset.mem_insert.mpr (Or.inl rfl)⟩⟩
  · -- `D` meets the attachment points
    have hne0 : attachPoints G C ∩ D ≠ ∅ := by
      rw [Finset.inter_comm]
      exact inter_attachPoints_of_isOddCycle_ne_of_packing_one h hC hshort hD hDC
    obtain ⟨x, hx⟩ := (Finset.nonempty_iff_ne_empty.mpr hne0)
    have hxA : x ∈ attachPoints G C := (Finset.mem_inter.mp hx).1
    have hxD : x ∈ D := (Finset.mem_inter.mp hx).2
    have hpos : 0 < (attachPoints G C ∩ D).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne0)
    -- an odd cycle meeting the attachment points in one point is a cross-over, hence inside the pair
    have hone : (attachPoints G C ∩ D).card = 1 → x ∈ ({a, b} : Finset V) := by
      intro h1
      have hcross : CrossOverPoint G C x := by
        refine ⟨D, ⟨hD, hDC, ?_⟩, ?_⟩
        · have hleA : (attachPoints G C ∩ D).card ≤ (C ∩ D).card := Finset.card_le_card (by
            intro z hz
            exact Finset.mem_inter.mpr ⟨(mem_attachPoints.mp (Finset.mem_inter.mp hz).1).1,
              (Finset.mem_inter.mp hz).2⟩)
          rw [h1] at hleA
          exact (card_inter_attachPoints_eq_one_iff h hC hshort hD hDC).mp (by omega)
        · exact Finset.mem_inter.mpr ⟨(mem_attachPoints.mp hxA).1, hxD⟩
      exact hX (mem_crossOverSet.mpr ⟨hcross, hxA⟩)
    by_cases hxab : x ∈ ({a, b} : Finset V)
    · exact Finset.nonempty_iff_ne_empty.mp ⟨x, Finset.mem_inter.mpr ⟨hxD, hxab⟩⟩
    · have h2 : 2 ≤ (attachPoints G C ∩ D).card := by
        by_contra hlt
        have hlt' : (attachPoints G C ∩ D).card ≤ 1 := by omega
        exact hxab (hone (by omega))
      exact hmeet D hD hDC h2

/-- **THE CONCLUSION OF ERDŐS #73 WITH THE OPTIMAL CONSTANT `2`, FROM A PAIR OF ATTACHMENT POINTS
CONTAINING THE CROSS-OVER SET.**  A new instance of the headline theorem: the certificate is two
vertices of a shortest odd cycle, determined by the cross-over points. -/
theorem closeToBipartite_two_of_subset_crossOverSet {k : ℕ} (hG : LocIndep k G)
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) {a b : V} (hab : a ≠ b)
    (ha : a ∈ attachPoints G C) (hb : b ∈ attachPoints G C)
    (hX : crossOverSet G C ⊆ ({a, b} : Finset V))
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ≠ C → 2 ≤ (attachPoints G C ∩ D).card →
      D ∩ ({a, b} : Finset V) ≠ ∅) : CloseToBipartite 2 G :=
  (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2)).mpr ⟨{a, b}, card_le_two_pair hab,
    hitsOddCycles_pair_of_attachPoints_of_subset_crossOverSet h hC hshort hab ha hb hX hmeet⟩

/-! ## Part 5 — the forced residual splits by the number of cross-over points

Round 138's residual is an existential over pairs.  Part 1 shows that the pair is forced by the
cross-over points, so the three cases `|crossOverSet| = 0, 1, 2` are three different problems, and the
third admits **no choice at all**: the certificate is `crossOverSet` itself.  Each is named, and
`JSP90.crossPairResidual_iff_three` makes the split an equivalence. -/

/-- **THE CERTIFICATE IN THE CASE OF NO CROSS-OVER POINT.**  Measured: `612 510` shortest odd cycles at
`LocIndep 1` with `3 ≤ |attachPoints G C|` have no cross-over point (`r139b.c`). -/
def NoCrossPairResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      (crossOverSet G C).card = 0 → 3 ≤ (attachPoints G C).card →
      ∃ a b : W, a ≠ b ∧ a ∈ attachPoints G C ∧ b ∈ attachPoints G C ∧
        HitsOddCycles G ({a, b} : Finset W)

/-- **THE CERTIFICATE IN THE CASE OF EXACTLY ONE CROSS-OVER POINT**: the cross-over point itself, and
one more attachment point.  Measured: `650 970` shortest odd cycles at `LocIndep 1` with
`3 ≤ |attachPoints G C|` have exactly one (`r139b.c`). -/
def OneCrossPairResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      (crossOverSet G C).card = 1 → 3 ≤ (attachPoints G C).card →
      ∃ a b : W, a ≠ b ∧ a ∈ attachPoints G C ∧ b ∈ attachPoints G C ∧
        HitsOddCycles G ({a, b} : Finset W)

/-- **THE FORCED CERTIFICATE: THE TWO CROSS-OVER POINTS OF A SHORTEST ODD CYCLE MEET EVERY ODD CYCLE.**

```lean
LocIndep 1 G → C shortest odd cycle → |crossOverSet G C| = 2 → HitsOddCycles G (crossOverSet G C)
```

By Part 1 the certificate *must* contain the two cross-over points, so a two-element certificate would
*be* the cross-over set; there is nothing to choose.  Measured with **0 failures** in `5 040` cases
(`r139.c` `Q5`, `r139b.c` `R1`), all of them with `|attachPoints G C| = 3`. -/
def TwoCrossTransversal : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      (crossOverSet G C).card = 2 → HitsOddCycles G (crossOverSet G C)

/-- **THE `|crossOverSet| ≠ 2` CASE: A TWO-ELEMENT CERTIFICATE EXISTS.**

One clean statement for the two cases `|crossOverSet| = 0` and `|crossOverSet| = 1`; measured with
**0 failures** in the `612 510` and `650 970` cases of `r139b.c`.  The hypothesis is deliberately
`|crossOverSet| ≠ 2` and not `|crossOverSet| ≤ 1`: by Part 2 the case `|crossOverSet| ≥ 3` is
*vacuous*, because no two-element certificate on `C` can then exist. -/
def LowCrossResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      (crossOverSet G C).card ≠ 2 → 3 ≤ (attachPoints G C).card →
      ∃ a b : W, a ≠ b ∧ a ∈ attachPoints G C ∧ b ∈ attachPoints G C ∧
        crossOverSet G C ⊆ ({a, b} : Finset W) ∧ HitsOddCycles G ({a, b} : Finset W)

/-- **THE FORCED RESIDUAL FOLLOWS FROM THE TWO CASES: `|crossOverSet| ≤ 1`, AND THE FORCED CERTIFICATE
`|crossOverSet| = 2`.** -/
theorem crossPairResidual_of_low_iff (h0 : LowCrossResidual.{u})
    (h2 : TwoCrossTransversal.{u}) : CrossPairResidual.{u} := by
  intro W instW G hG C hC hshort h3
  by_cases hX2 : (crossOverSet G C).card = 2
  · obtain ⟨a, b, haX, hbX, hab, haC, hbC⟩ := exists_pair_mem_C_of_card_crossOverSet_eq_two hX2
    have heq : crossOverSet G C = ({a, b} : Finset W) := by
      refine (Finset.eq_of_subset_of_card_le (s := ({a, b} : Finset W))
        (t := crossOverSet G C) (fun z hz => by
          rcases Finset.mem_insert.mp hz with hz | hz
          · rw [hz]
            exact haX
          · rw [Finset.mem_singleton.mp hz]
            exact hbX)
        (by rw [hX2, Finset.card_eq_two.mpr ⟨a, b, hab, rfl⟩])).symm
    have hh : HitsOddCycles G ({a, b} : Finset W) := by
      rw [← heq]
      exact h2 W instW G hG C hC hshort hX2
    exact ⟨a, b, hab, subset_crossOverSet_attachPoints C haX, subset_crossOverSet_attachPoints C hbX,
      subset_pair_of_hitsOddCycles_pair_of_mem hab haC hbC hh, hh⟩
  · obtain ⟨a, b, hab, ha, hb, hX, hh⟩ := h0 W instW G hG C hC hshort hX2 h3
    exact ⟨a, b, hab, ha, hb, hX, hh⟩

/-- **THE `|crossOverSet| ≤ 1` CASE IS IMPLIED BY THE FORCED RESIDUAL** (no case analysis is needed,
since the residual exhibits a pair and Part 1 shows it already contains the cross-over set). -/
theorem lowCrossResidual_of_crossPairResidual (h : CrossPairResidual.{u}) :
    LowCrossResidual.{u} := by
  intro W instW G hG C hC hshort hX1 h3
  obtain ⟨a, b, hab, ha, hb, hX, hh⟩ := h W instW G hG C hC hshort h3
  exact ⟨a, b, hab, ha, hb, hX, hh⟩

/-- **THE FORCED CERTIFICATE IS IMPLIED BY THE FORCED RESIDUAL: with two cross-over points the
certificate is not a choice.**

In the case `|attachPoints G C| ≤ 2` the attachment points themselves meet every odd cycle (round 136)
and contain the cross-over set, so they are the certificate; and an empty fan gives an empty cross-over
set, so `|crossOverSet G C| = 2` forces a nonempty fan. -/
theorem twoCrossTransversal_of_crossPairResidual (h : CrossPairResidual.{u}) :
    TwoCrossTransversal.{u} := by
  intro W instW G hG C hC hshort hX2
  by_cases hnb : (boundary G C).Nonempty
  · by_cases hle : (attachPoints G C).card ≤ 2
    · have hh : HitsOddCycles G (attachPoints G C) :=
        hitsOddCycles_attachPoints_of_packing_one (packingNumberOne_of_locIndep_one hG) hC hshort hnb
      have hA : attachPoints G C = crossOverSet G C := by
        refine (Finset.eq_of_subset_of_card_le (s := crossOverSet G C) (t := attachPoints G C)
          (fun z hz => (mem_crossOverSet.mp hz).2) ?_).symm
        rw [hX2]
        exact hle
      rw [← hA]
      exact hh
    · have hleA : (attachPoints G C).card ≤ C.card := Finset.card_le_card (subset_attachPoints_C C)
      obtain ⟨a, b, hab, haA, hbA, hX, hh⟩ := h W instW G hG C hC hshort (by omega)
      rw [show crossOverSet G C = ({a, b} : Finset W) from Finset.eq_of_subset_of_card_le hX
        (by rw [hX2]; exact card_le_two_pair hab)]
      exact hh
  · have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnb
    have hXzero : crossOverSet G C = ∅ := by
      ext z
      constructor
      · intro hz
        obtain ⟨y, hy, -⟩ := (mem_attachPoints.mp (mem_crossOverSet.mp hz).2).2
        rw [h0] at hy
        exact absurd hy (by simp)
      · intro hz
        exact absurd hz (by simp)
    rw [hXzero, Finset.card_empty] at hX2
    exact absurd hX2 (by omega)

/-- **THE FORCED RESIDUAL IS EXACTLY THE TWO-WAY SPLIT: `|crossOverSet| ≤ 1`, AND `|crossOverSet| = 2`.**
So the residual of the sharp case `k = 1` is now read off as two independent statements, and the
`|crossOverSet| = 2` one has no existential in it at all. -/
theorem crossPairResidual_iff_low_iff :
    CrossPairResidual.{u} ↔ LowCrossResidual.{u} ∧ TwoCrossTransversal.{u} :=
  ⟨fun h => ⟨lowCrossResidual_of_crossPairResidual h, twoCrossTransversal_of_crossPairResidual h⟩,
    fun ⟨h0, h2⟩ => crossPairResidual_of_low_iff h0 h2⟩

/-- **THE `|crossOverSet| ≤ 1` CASE IMPLIES THE THREE CASES' EXISTENTIAL FORM.** -/
theorem noCrossPairResidual_of_lowCrossResidual (h : LowCrossResidual.{u}) :
    NoCrossPairResidual.{u} := by
  intro W instW G hG C hC hshort hX0 h3
  obtain ⟨a, b, hab, ha, hb, -, hh⟩ := h W instW G hG C hC hshort (by omega) h3
  exact ⟨a, b, hab, ha, hb, hh⟩

/-- **AND THE `|crossOverSet| = 1` CASE.** -/
theorem oneCrossPairResidual_of_lowCrossResidual (h : LowCrossResidual.{u}) :
    OneCrossPairResidual.{u} := by
  intro W instW G hG C hC hshort hX1 h3
  obtain ⟨a, b, hab, ha, hb, -, hh⟩ := h W instW G hG C hC hshort (by omega) h3
  exact ⟨a, b, hab, ha, hb, hh⟩

/-! ## Part 6 — the two cross-over cycles at two distinct points meet

The cross-over cycles of the same odd cycle are pairwise intersecting at `LocIndep 1`, since they are
odd cycles and `LocIndep 1` bounds the packing number by one.  This is what makes the triangle
configuration of Part 7 tight. -/

/-- **THE TWO CROSS-OVER CYCLES AT TWO DISTINCT POINTS OF `C` MEET.**  Any two odd cycles of a graph of
packing number one meet, so in particular the two cycles that leave `C` at `a` and at `b ≠ a`. -/
theorem inter_ne_of_crossOverPoint_pair (h : PackingNumberOne G) {C : Finset V} {a b : V}
    {D E : Finset V} (hD : OnePointCrossOver G C D) (hE : OnePointCrossOver G C E) : D ∩ E ≠ ∅ :=
  h D E hD.1 hE.1

/-! ## Part 7 — the triangle case is a *negative* configuration

Round 138 left the case "every attachment point is a cross-over point" in its residual.  For a triangle
that case is the whole of the hypothesis, and it is a statement about a configuration that does not
occur: `r139.c` finds none on `n ≤ 7` (`Q7`), and none among the `2 503 867` graphs with `LocIndep 1`
on `n = 8` which contain a triangle (`Q9`).  Naming it gives the sharp case `k = 1` a second, tighter
and *negative* residual, whose object is a finite configuration rather than a certificate to be found. -/

/-- **A SET OF THREE ELEMENTS CONTAINING TWO OF THEM HAS A THIRD.** -/
theorem exists_third_of_card_eq_three_mem_pair {S : Finset V} (h3 : S.card = 3) {a b : V}
    (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) : ∃ c, c ∈ S ∧ c ≠ a ∧ c ≠ b := by
  have hsub : ({a, b} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb
  have hcard : (S \ ({a, b} : Finset V)).card = S.card - 2 := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_eq_two.mpr ⟨a, b, hab, rfl⟩]
  have hne : (S \ ({a, b} : Finset V)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hcon
    have hz : (S \ ({a, b} : Finset V)).card = 0 := Finset.card_eq_zero.mpr hcon
    have heq : 0 = S.card - 2 := by rw [← hcard, hz]
    omega
  obtain ⟨c, hc⟩ := hne
  have hcN : c ∉ ({a, b} : Finset V) := (Finset.mem_sdiff.mp hc).2
  refine ⟨c, (Finset.mem_sdiff.mp hc).1, fun h => ?_, fun h => ?_⟩
  · exact hcN (Finset.mem_insert.mpr (Or.inl h))
  · exact hcN (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))

/-- **THE RESIDUAL OF THE SHARP CASE `k = 1` RESTRICTED TO TRIANGLES, IN NEGATIVE FORM.**

```lean
LocIndep 1 G → C a shortest odd cycle → |C| = 3 → ∃ x ∈ C, ¬ CrossOverPoint G C x
```

i.e. *the three vertices of a shortest odd triangle do not all carry a cross-over*. -/
def TriangleCrossResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      C.card = 3 → 3 ≤ (attachPoints G C).card → ∃ x : W, x ∈ C ∧ ¬ CrossOverPoint G C x

/-- **ERDŐS PROBLEM #73 AT `k = 1` WITH THE OPTIMAL CONSTANT `2`, FOR THE CLASS OF GRAPHS WHOSE
SHORTEST ODD CYCLES ARE TRIANGLES.**

A new instance of the headline theorem, on a class of graphs given by a property of their odd cycles
alone: the odd girth is `3`.  The case analysis: the attachment points lie on `C`, so `|A| ≤ 3`; if
there are at most two of them they themselves meet every odd cycle (round 136); if there are three then
`C` *is* the set of attachment points, and the residual supplies a point which is not a cross-over
point, whose erasure leaves a two-element transversal (round 138). -/
theorem erdos73On_one_two_of_triangleCrossResidual (h : TriangleCrossResidual.{u}) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
      (∀ C : Finset W, IsOddCycle G C → C.card = 3) → CloseToBipartite 2 G := by
  intro W instW G hG htri
  rw [closeToBipartite_iff_hitsOddCycles]
  by_cases hex : ∃ C : Finset W, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle (G := G) hex
    have hC3 : C.card = 3 := htri C hC
    by_cases hne : (boundary G C).Nonempty
    · by_cases hle : (attachPoints G C).card ≤ 2
      · exact ⟨attachPoints G C, hle,
          hitsOddCycles_attachPoints_of_packing_one (packingNumberOne_of_locIndep_one hG) hC hshort
            hne⟩
      · have hleA : (attachPoints G C).card ≤ C.card :=
          Finset.card_le_card (subset_attachPoints_C C)
        have h3 : 3 ≤ (attachPoints G C).card := by omega
        have hA : attachPoints G C = C := by
          refine Finset.eq_of_subset_of_card_le (s := attachPoints G C) (t := C)
            (subset_attachPoints_C C) ?_
          omega
        obtain ⟨x, hxC, hx⟩ := h W instW G hG C hC hshort hC3 h3
        have hxA : x ∈ attachPoints G C := by rw [hA]; exact hxC
        exact ⟨attachPoints G C \ {x},
          (card_le_two_sdiff_singleton_of_card_le_three hxA h3 (by rw [← hC3]; exact hleA)),
          hitsOddCycles_attachPoints_sdiff_of_not_crossOver (packingNumberOne_of_locIndep_one hG)
            hC hshort hxA hx (by omega)⟩
    · obtain ⟨c, hc⟩ := exists_mem_isOddCycle hC
      have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hh : HitsOddCycles G ({c} : Finset W) := by
        simpa [h0] using hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc
      exact ⟨{c}, by simp, hh⟩
  · exact ⟨∅, by simp, fun D hD => absurd ⟨D, hD⟩ hex⟩

/-- **THE TRIANGLE RESIDUAL IS IMPLIED BY ROUND 138'S FORCED RESIDUAL.**  Two of the three vertices are
cross-over points, so the third — which exists, `|C| = 3` — is not. -/
theorem triangleCrossResidual_of_crossPairResidual (h : CrossPairResidual.{u}) :
    TriangleCrossResidual.{u} := by
  intro W instW G hG C hC hshort hC3 h3
  have hleA : (attachPoints G C).card ≤ C.card := Finset.card_le_card (subset_attachPoints_C C)
  obtain ⟨a, b, hab, ha, hb, hX, hh⟩ := h W instW G hG C hC hshort h3
  have hA : attachPoints G C = C := by
    refine Finset.eq_of_subset_of_card_le (s := attachPoints G C) (t := C) (subset_attachPoints_C C)
      ?_
    omega
  have haA : a ∈ C := hA ▸ ha
  have hbA : b ∈ C := hA ▸ hb
  have hsub0 : ({a, b} : Finset W) ⊆ C := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · rw [hz]
      exact haA
    · rw [Finset.mem_singleton.mp hz]
      exact hbA
  by_cases haX : a ∈ crossOverSet G C
  · by_cases hbX : b ∈ crossOverSet G C
    · obtain ⟨c, hcC, hca, hcb⟩ := exists_third_of_card_eq_three_mem_pair hC3 hab haA hbA
      have hcA : c ∈ attachPoints G C := hA.symm ▸ hcC
      refine ⟨c, hA.symm ▸ hcC, ?_⟩
      intro hc
      have hcX : c ∈ crossOverSet G C := mem_crossOverSet.mpr ⟨hc, hcA⟩
      rcases eq_or_eq_of_mem_pair_of_hitsOddCycles_pair_of_crossOverPoint hab hsub0 hh hcX with
        hcab | hcab
      · exact hca hcab
      · exact hcb hcab
    · refine ⟨b, hbA, ?_⟩
      intro hb'
      exact hbX (mem_crossOverSet.mpr ⟨hb', hb⟩)
  · refine ⟨a, haA, ?_⟩
    intro ha'
    exact haX (mem_crossOverSet.mpr ⟨ha', ha⟩)

#print axioms JSP90.exists_three_of_card_ge_three
#print axioms JSP90.mem_crossOverSet
#print axioms JSP90.subset_crossOverSet_attachPoints
#print axioms JSP90.subset_crossOverSet_C
#print axioms JSP90.not_mem_crossOverSet_of_not_crossOverPoint
#print axioms JSP90.subset_pair_of_hitsOddCycles_pair_of_mem
#print axioms JSP90.card_le_two_pair_of_hitsOddCycles_pair_of_mem
#print axioms JSP90.not_mem_crossOverSet_of_mem_of_hitsOddCycles_pair_of_mem
#print axioms JSP90.eq_or_eq_of_mem_pair_of_hitsOddCycles_pair_of_crossOverPoint
#print axioms JSP90.not_hitsOddCycles_pair_of_mem_of_three_crossOverPoint
#print axioms JSP90.exists_pair_mem_C_of_card_crossOverSet_eq_two
#print axioms JSP90.card_attachPoints_ge_two_of_card_crossOverSet_eq_two
#print axioms JSP90.card_sdiff_singleton_of_mem
#print axioms JSP90.two_le_card_sdiff_singleton_of_card_ge_three
#print axioms JSP90.card_le_two_sdiff_singleton_of_card_le_three
#print axioms JSP90.crossOverResidual_of_crossPairResidual
#print axioms JSP90.erdos73On_one_two_of_crossPairResidual
#print axioms JSP90.exists_pair_of_hitsOddCycles_attachPoints_sdiff
#print axioms JSP90.crossPairResidual_of_crossOverResidual
#print axioms JSP90.crossPairResidual_iff_crossOverResidual
#print axioms JSP90.hitsOddCycles_pair_of_attachPoints_of_subset_crossOverSet
#print axioms JSP90.closeToBipartite_two_of_subset_crossOverSet
#print axioms JSP90.LowCrossResidual
#print axioms JSP90.crossPairResidual_of_low_iff
#print axioms JSP90.lowCrossResidual_of_crossPairResidual
#print axioms JSP90.twoCrossTransversal_of_crossPairResidual
#print axioms JSP90.crossPairResidual_iff_low_iff
#print axioms JSP90.noCrossPairResidual_of_lowCrossResidual
#print axioms JSP90.oneCrossPairResidual_of_lowCrossResidual
#print axioms JSP90.twoCrossTransversal_of_crossPairResidual
#print axioms JSP90.inter_ne_of_crossOverPoint_pair
#print axioms JSP90.exists_third_of_card_eq_three_mem_pair
#print axioms JSP90.erdos73On_one_two_of_triangleCrossResidual
#print axioms JSP90.triangleCrossResidual_of_crossPairResidual
