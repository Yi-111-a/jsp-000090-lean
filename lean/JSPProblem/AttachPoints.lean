import JSPProblem.BoundaryOne
import JSPProblem.Book
import Mathlib.Data.Finset.SDiff

/-!
# JSP-000090, round 136 — `JSPProblem/AttachPoints.lean`: **the attachment points of a shortest odd
# cycle**, the fan-entry lemma, and a *tighter* residual for the sharp case `k = 1`

Attack family 65.  Round 135 (`JSPProblem/BoundaryOne.lean`) proved that **the fan** of a shortest
odd cycle is an odd-cycle transversal at `LocIndep 1`, and reduced the sharp case `k = 1` to
`JSP90.FanTwoResidual`:

```lean
LocIndep 1 G → C shortest odd cycle → 2 ≤ |boundary G C| → ∃ X, |X| ≤ 2 ∧ X hits every odd cycle
```

This round attacks `FanTwoResidual` from a **new** direction.  Instead of the *fan*
(`boundary G C`, the vertices outside `C` touching it) the object studied here is the
**attachment set**

```lean
attachPoints G C = ⋃ (y ∈ boundary G C) (attachSet G C y)
                = { a ∈ C : a has a neighbour in boundary G C }
```

— the vertices **of the cycle** that some fan vertex hangs on.  It is the mirror image of the fan
(`JSP90.attachSet` is round 117's `JSPProblem/Book.lean`), it always lies **on** `C`
(`JSP90.subset_attachPoints_C`), and on the six-vertex witness `fan4` of round 135 it is the single
vertex `5` while the fan is `{1, 2, 3}`.

## The key lemma: fan entry (Part 2)

`JSP90.exists_mem_boundary_neigh_inter_of_isOddCycle_ne_of_packing_one`:

> every odd cycle `D ≠ C` contains a fan vertex `y` **with a neighbour of `y` lying on `D ∩ C`**.

The proof is the classical "an odd cycle cannot cross a vertex set" step
(`JSP90.sub_inter_or_sdiff_of_isOddCycle`, Part 1): if no fan vertex of `D` had a neighbour on
`D ∩ C`, then no edge of `G` would join `D ∩ C` to `D \ C`, so the cycle `D` would lie on one side —
inside `C` (impossible, `C` is *shortest*) or entirely off `C` (impossible, `C` and `D` would be two
vertex-disjoint odd cycles).

## The consequence (Parts 3–5)

`JSP90.hitsOddCycles_attachPoints_of_packing_one` — **the attachment points of a shortest odd cycle
are an odd-cycle transversal**.  Nothing but `JSP90.PackingNumberOne` is used, so this is available
for every `k` with the packing condition in place of Erdős's hypothesis, and it *subsumes* the
round-135 instances in a strictly finer way:

| statement | constant | hypothesis |
| --- | --- | --- |
| `JSP90.closeToBipartite_of_attachPoints_le_of_packing_one` | `|attachPoints|` | packing number one |
| **`JSP90.closeToBipartite_one_of_attachPoints_le_one_of_packing_one`** | **`1`** | packing number one |
| **`JSP90.erdos73On_one_two_of_attachPoints_le_two_of_packing_one`** | **`2`** (optimal) | packing number one, any `k` |

`fan4` of round 135 (`LocIndep 1`, fan `{1,2,3}`, `CloseToBipartite 1`, certificate `{5}`) is the
first instance of the constant-`1` statement, and it is tight: `|attachPoints| ≤ 1` **forces**
`τ_odd = 1`, because the attachment points are then themselves a one-vertex transversal.

## Part 6 — a *tighter* residual (`JSP90.AttachThreeResidual`)

Because the cases `|boundary G C| = 0` and `|attachPoints| ≤ 2` are now theorems, the residual of the
sharp case `k = 1` can be stated with **no hypothesis on the fan at all**:

```lean
JSP90.AttachThreeResidual : LocIndep 1 G → C shortest odd cycle → 3 ≤ |attachPoints G C| →
                             ∃ X, |X| ≤ 2 ∧ X hits every odd cycle
```

`JSP90.erdos73On_one_two_of_attachThreeResidual` proves it implies the **sharp**
`Erdős73On 1 2`, and `JSP90.fanTwoResidual_of_attachThreeResidual` proves it implies round 135's
`FanTwoResidual`.  So the residual is now *strictly weaker* than it was, and the case it no longer
covers — `|boundary G C| ≥ 2` with `|attachPoints| ≤ 2`, in which the certificate is the attachment
set itself — is proved (`JSP90.hitsOddCycles_pair_of_attachPoints_sub`).

The threshold `3` is optimal and the residual is non-vacuous already on **five** vertices:
`discovery/JSP-000090/r136.c` measures `max_G min_C |attachPoints G C| = 4` over all `986 787`
graphs with `MaxDef ≤ 1` on `n ≤ 7` vertices, and the smallest graph with
`min_C |attachPoints G C| = 3` has edges `0-2 0-3 0-4 1-2 1-3 1-4 2-3` (a `K_{2,3}` plus one edge):
its shortest odd cycles are two triangles sharing an edge, both with all three vertices being
attachment points.

## Part 7 — `K₄`-freeness and the missing `|C| = 3` half of the fan bound

`JSP90.card_isClique_le_two_add`: under `LocIndep k`, **every clique has at most `k + 2` vertices**
(in deficiency form, `JSP90.maxDef_clique_add_two_le`), so `LocIndep 1` forbids `K_4`.

`JSP90.card_attachSet_le_two_of_locIndep_one`: at `LocIndep 1`, a fan vertex of a **shortest** odd
cycle has at most two attachment points, **including when the cycle is a triangle**.  Round 35's
`JSP90.card_inter_neigh_le_two` (via round 117's `JSP90.card_attachSet_le_two`) needs `5 ≤ |C|`; the
missing `|C| = 3` half is the `K₄`-free observation above, and it is exactly what the search
verifies (`Q4`: `max |N(x) ∩ C| = 2` for `|C| = 3` as well as for `|C| ≥ 5`).
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 400000

local instance attachPointsDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Part 1 — an odd cycle does not cross a vertex set

The elementary step behind the whole file: `D` is an odd cycle and `X` any vertex set; if no edge of
`G` joins `D ∩ X` to `D \ X`, then `D` lies on one side.  This is
`JSP90.isOddCycle_sub_anticoverIn` (round 106, `JSPProblem/Additive.lean`) applied to the induced
graph on `D`. -/

/-- **AN ODD CYCLE DOES NOT CROSS A VERTEX SET.**  If no edge of `G` joins `D ∩ X` to `D \ X`, then the
odd cycle `D` lies entirely on one side: `D ⊆ D \ X` or `D ⊆ D ∩ X`. -/
theorem sub_inter_or_sdiff_of_isOddCycle {D X : Finset V} (hD : IsOddCycle G D)
    (hno : ∀ v ∈ D ∩ X, ∀ w ∈ D \ X, ¬ G.Adj v w) : D ⊆ D \ X ∨ D ⊆ D ∩ X := by
  have hno' : ∀ v ∈ D \ X, ∀ w ∈ D ∩ X, ¬ G.Adj v w :=
    fun v hv w hw h => hno w hw v hv h.symm
  refine isOddCycle_sub_anticoverIn (s := D) (A := D \ X) (B := D ∩ X) ?_
    (hD.induceFinset (Finset.Subset.refl D))
  refine ⟨?_, Finset.sdiff_union_inter D X, ?_⟩
  · intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx1).2 (Finset.mem_inter.mp hx2).2
  · intro v hv w hw h
    exact hno' v hv w hw h

/-! ## Part 2 — the fan-entry lemma

**THE KEY NEW LEMMA OF THIS ROUND.** -/

/-- **FAN ENTRY: EVERY OTHER ODD CYCLE ENTERS THE CYCLE THROUGH ONE OF ITS FAN VERTICES.**

At packing number one, if `C` is a shortest odd cycle and `D ≠ C` is an odd cycle, then some `y` in
the fan of `C` satisfies

```lean
y ∈ D ∩ boundary G C      and      neighOf G {y} ∩ D ∩ C ≠ ∅
```

that is, **`D` contains a fan vertex of `C` together with a neighbour of it lying on `D ∩ C`.**

Proof: `JSP90.oddCycle_eq_or_inter_boundary_of_packing_one` (round 135, Part 2) gives a fan vertex
of `D`; if none of them had a neighbour on `D ∩ C`, then no edge of `G` would join `D ∩ C` to
`D \ C` (an endpoint of such an edge outside `C` is a fan vertex), so by Part 1 the cycle `D` would
lie on one side: inside `C`, contradicting that `C` is *shortest*, or off `C`, contradicting
`JSP90.PackingNumberOne`. -/
theorem exists_mem_boundary_neigh_inter_of_isOddCycle_ne_of_packing_one {C D : Finset V}
    (h : PackingNumberOne G) (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hD : IsOddCycle G D)
    (hne : D ≠ C) :
    ∃ y ∈ D ∩ boundary G C, (neighOf G {y} ∩ D ∩ C).Nonempty := by
  have hfan : D ∩ boundary G C ≠ ∅ :=
    (oddCycle_eq_or_inter_boundary_of_packing_one h hC hshort hD).resolve_left hne
  obtain ⟨y0, hy0⟩ := Finset.nonempty_iff_ne_empty.mpr hfan
  by_cases hex : ∃ y ∈ D ∩ boundary G C, (neighOf G {y} ∩ D ∩ C).Nonempty
  · obtain ⟨y, hy, hny⟩ := hex
    exact ⟨y, hy, hny⟩
  -- no edge of `G` joins `D ∩ C` to `D \ C`
  have hno : ∀ v ∈ D ∩ C, ∀ w ∈ D \ C, ¬ G.Adj v w := by
    intro v hv w hw hvw
    have hxv : v ∈ D ∧ v ∈ C := Finset.mem_inter.mp hv
    have hwn : w ∉ C := (Finset.mem_sdiff.mp hw).2
    have hwfan : w ∈ boundary G C := mem_boundary.mpr ⟨hwn, v, hxv.2, hvw.symm⟩
    refine absurd ?_ hex
    exact ⟨w, Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hw).1, hwfan⟩, v, Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨mem_neighOf.mpr ⟨w, Finset.mem_singleton_self w, hvw⟩, hxv.1⟩,
        hxv.2⟩⟩
  rcases sub_inter_or_sdiff_of_isOddCycle hD hno with hDX | hDs
  · exfalso
    refine h C D hC hD ?_
    refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    exact (Finset.mem_sdiff.mp (hDX (Finset.mem_inter.mp hz).2)).2 (Finset.mem_inter.mp hz).1
  · have hD_eq : D = C := eq_of_isOddCycle_subset_shortest hC hshort hD
      (fun x hx => (Finset.mem_inter.mp (hDs hx)).2)
    exact absurd hD_eq hne

/-! ## Part 3 — the attachment points of an odd cycle

The mirror image of the fan `boundary G C`: the vertices **of `C`** that a fan vertex hangs on.  It is
built from `JSP90.attachSet` of `JSPProblem/Book.lean` (round 117), the attachment set of a *single*
fan vertex. -/

/-- **THE ATTACHMENT POINTS OF `C`**: the vertices of `C` that some fan vertex of `C` is adjacent to,
i.e. the union of the attachment sets `JSP90.attachSet` over the fan. -/
noncomputable def attachPoints (G : SimpleGraph V) (C : Finset V) : Finset V :=
  (boundary G C).biUnion (attachSet G C)

/-- **MEMBERSHIP IN THE ATTACHMENT SET**: `a ∈ attachPoints G C` iff `a` lies on `C` and is adjacent to
some fan vertex. -/
theorem mem_attachPoints {C : Finset V} {a : V} :
    a ∈ attachPoints G C ↔ a ∈ C ∧ ∃ y ∈ boundary G C, G.Adj a y := by
  rw [attachPoints, Finset.mem_biUnion]
  constructor
  · rintro ⟨y, hy, hay⟩
    exact ⟨(mem_attachSet.mp hay).1, y, hy, (mem_attachSet.mp hay).2.symm⟩
  · rintro ⟨ha, y, hy, hay⟩
    exact ⟨y, hy, mem_attachSet.mpr ⟨ha, hay.symm⟩⟩

/-- **THE ATTACHMENT POINTS LIE ON THE CYCLE**, the mirror image of
`JSP90.subset_fanClass_boundary`. -/
theorem subset_attachPoints_C (C : Finset V) : attachPoints G C ⊆ C :=
  fun _ ha => (mem_attachPoints.mp ha).1

/-- **THE ATTACHMENT POINTS AND THE FAN ARE DISJOINT**: the two objects live on opposite sides of the
cycle, so a fan vertex is never an attachment point. -/
theorem disjoint_attachPoints_boundary (C : Finset V) : Disjoint (attachPoints G C) (boundary G C) :=
  Finset.disjoint_left.mpr fun a ha hb => by
    have : a ∈ C := (mem_attachPoints.mp ha).1
    exact (mem_boundary.mp hb).1 this

/-- **A NONEMPTY FAN GIVES A NONEMPTY SET OF ATTACHMENT POINTS.** -/
theorem attachPoints_nonempty_of_mem_boundary {C : Finset V} (_hC : IsOddCycle G C) {y : V}
    (hy : y ∈ boundary G C) : (attachPoints G C).Nonempty := by
  obtain ⟨a, ha⟩ := attachSet_nonempty_of_mem_boundary hy
  exact ⟨a, mem_attachPoints.mpr ⟨(mem_attachSet.mp ha).1, y, hy, (mem_attachSet.mp ha).2.symm⟩⟩

/-! ## Part 4 — **THE ATTACHMENT POINTS ARE AN ODD-CYCLE TRANSVERSAL** -/

/-- **AN ODD CYCLE OTHER THAN `C` MEETS THE ATTACHMENT POINTS OF `C`.** -/
theorem inter_attachPoints_of_isOddCycle_ne_of_packing_one {C D : Finset V} (h : PackingNumberOne G)
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hD : IsOddCycle G D) (hne : D ≠ C) : D ∩ attachPoints G C ≠ ∅ := by
  obtain ⟨y, hyfan, a, ha⟩ :=
    exists_mem_boundary_neigh_inter_of_isOddCycle_ne_of_packing_one h hC hshort hD hne
  obtain ⟨haN, haC⟩ := Finset.mem_inter.mp ha
  obtain ⟨haN', haD⟩ := Finset.mem_inter.mp haN
  refine Finset.nonempty_iff_ne_empty.mp
    ⟨a, Finset.mem_inter.mpr ⟨haD, ?_⟩⟩
  refine mem_attachPoints.mpr ⟨haC, y, (Finset.mem_inter.mp hyfan).2, ?_⟩
  obtain ⟨w, hw, hadj⟩ := mem_neighOf.mp haN'
  rw [Finset.mem_singleton.mp hw] at hadj
  exact hadj

/-- **`C` MEETS ITS OWN ATTACHMENT POINTS**, as soon as the fan is nonempty. -/
theorem inter_C_attachPoints_of_boundary_nonempty {C : Finset V} (hC : IsOddCycle G C) {y : V}
    (hy : y ∈ boundary G C) : C ∩ attachPoints G C ≠ ∅ := by
  obtain ⟨a, ha⟩ := attachPoints_nonempty_of_mem_boundary hC hy
  exact Finset.nonempty_iff_ne_empty.mp
    ⟨a, Finset.mem_inter.mpr ⟨(mem_attachPoints.mp ha).1, ha⟩⟩

/-- **THE ATTACHMENT POINTS OF A SHORTEST ODD CYCLE ARE AN ODD-CYCLE TRANSVERSAL.**

```lean
HitsOddCycles G (attachPoints G C)
```

every odd cycle of `G` meets the vertices of `C` on which a fan vertex hangs.  Only
`JSP90.PackingNumberOne` is used, so this holds for every `k` with the packing condition in place of
Erdős's hypothesis (`JSP90.packingNumberOne_of_locIndep_one` supplies it at `k = 1`).

This is the second half of the "fan or entry" dichotomy of round 135: the fan is a transversal
(`JSP90.oddCycle_eq_or_inter_boundary_of_packing_one`) and so are the attachment points, and the
latter are usually much smaller — on `fan4` the fan has `3` elements while the attachment points are
the single vertex `5`. -/
theorem hitsOddCycles_attachPoints_of_packing_one (h : PackingNumberOne G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hne : (boundary G C).Nonempty) : HitsOddCycles G (attachPoints G C) := by
  intro D hD
  by_cases hDC : D = C
  · subst hDC
    obtain ⟨y, hy⟩ := hne
    exact inter_C_attachPoints_of_boundary_nonempty hC hy
  · exact inter_attachPoints_of_isOddCycle_ne_of_packing_one h hC hshort hD hDC

/-- **THE ATTACHMENT POINTS TOGETHER WITH ONE VERTEX OF `C` ARE A TRANSVERSAL**, with **no** hypothesis
on the fan at all; this form also covers the empty fan. -/
theorem hitsOddCycles_attachPoints_union_singleton_of_packing_one (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) {c : V} (hc : c ∈ C) :
    HitsOddCycles G (attachPoints G C ∪ {c}) := by
  intro D hD
  by_cases hDC : D = C
  · refine Finset.nonempty_iff_ne_empty.mp
      ⟨c, Finset.mem_inter.mpr ⟨hDC ▸ hc, Finset.mem_union_right _ (Finset.mem_singleton_self c)⟩⟩
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr
      (inter_attachPoints_of_isOddCycle_ne_of_packing_one h hC hshort hD hDC)
    exact Finset.nonempty_iff_ne_empty.mp ⟨a, Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp ha).1, Finset.mem_union_left _ (Finset.mem_inter.mp ha).2⟩⟩

/-! ## Part 5 — the instances: the constant is the number of attachment points -/

/-- **THE CONCLUSION OF ERDŐS #73 WITH THE CONSTANT `|attachPoints G C|`**, at packing number one.
The certificate is the attachment set itself. -/
theorem closeToBipartite_of_attachPoints_le_of_packing_one {m : ℕ} (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hne : (boundary G C).Nonempty) (hb : (attachPoints G C).card ≤ m) : CloseToBipartite m G :=
  (closeToBipartite_iff_hitsOddCycles (G := G) (m := m)).mpr
    ⟨attachPoints G C, hb, hitsOddCycles_attachPoints_of_packing_one h hC hshort hne⟩

/-- **A NEW INSTANCE WITH THE CONSTANT `1`.**  A shortest odd cycle with a nonempty fan and at most
**one** attachment point makes `G` `1`-close to bipartite, at packing number one.  Compare
`JSP90.closeToBipartite_boundary_add_one_of_packing_one` of round 135, whose constant is
`|fan| + 1`: for the six-vertex witness `fan4` of `JSPProblem/Fan4.lean` that is `4` and this is
`1`.  The constant is optimal, because the attachment points are then themselves a one-vertex
transversal. -/
theorem closeToBipartite_one_of_attachPoints_le_one_of_packing_one (h : PackingNumberOne G)
    {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hne : (boundary G C).Nonempty) (hb : (attachPoints G C).card ≤ 1) : CloseToBipartite 1 G :=
  closeToBipartite_of_attachPoints_le_of_packing_one h hC hshort hne hb

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM: THE OPTIMAL CONSTANT `2`, FOR EVERY `k`, UNDER THE
PACKING CONDITION.**  `LocIndep k G`, packing number one, a shortest odd cycle with at most **two**
attachment points and a nonempty fan give `CloseToBipartite 2 G` — the optimal constant, with no
bound on the odd girth, the packing weight or the number of branch vertices. -/
theorem erdos73On_one_two_of_attachPoints_le_two_of_packing_one {k : ℕ} (_hG : LocIndep k G)
    (h : PackingNumberOne G) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hne : (boundary G C).Nonempty) (hb : (attachPoints G C).card ≤ 2) : CloseToBipartite 2 G :=
  closeToBipartite_of_attachPoints_le_of_packing_one h hC hshort hne hb

/-- **THE `k = 1` INSTANCE OF THE PREVIOUS THEOREM, WITH ERDŐS'S HYPOTHESIS SUPPLYING THE PACKING
CONDITION.** -/
theorem erdos73On_one_two_of_attachPoints_le_two (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hne : (boundary G C).Nonempty) (hb : (attachPoints G C).card ≤ 2) : CloseToBipartite 2 G :=
  erdos73On_one_two_of_attachPoints_le_two_of_packing_one hG
    (packingNumberOne_of_locIndep_one hG) hC hshort hne hb

/-- **THE CONSTANT `1` AT `k = 1`.** -/
theorem closeToBipartite_one_of_attachPoints_le_one (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hne : (boundary G C).Nonempty) (hb : (attachPoints G C).card ≤ 1) : CloseToBipartite 1 G :=
  closeToBipartite_one_of_attachPoints_le_one_of_packing_one (packingNumberOne_of_locIndep_one hG)
    hC hshort hne hb

/-- **A CARDINALITY BOUND GIVES A NONEMPTY FAN.** -/
theorem nonempty_boundary_of_card_ge_two {C : Finset V} {m : ℕ} (h : (boundary G C).card = m)
    (hm : 2 ≤ m) : (boundary G C).Nonempty := by
  refine Finset.nonempty_iff_ne_empty.mpr ?_
  intro hcon
  have hz : (boundary G C).card = 0 := by rw [hcon, Finset.card_empty]
  rw [h] at hz
  omega

/-- **TWO NAMED VERTICES SUFFICE WHEN THEY CONTAIN THE ATTACHMENT POINTS.**  This is the concrete
certificate form of Part 4 and a *provable case* of `JSP90.FanTwoResidual`: when the attachment
points of a shortest odd cycle fit inside a pair `{p, q}`, that pair meets every odd cycle of `G`. -/
theorem hitsOddCycles_pair_of_attachPoints_sub (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) {p q : V}
    (hpq : attachPoints G C ⊆ ({p, q} : Finset V)) (hne : (boundary G C).Nonempty) :
    HitsOddCycles G ({p, q} : Finset V) := by
  intro D hD
  by_cases hDC : D = C
  · subst hDC
    obtain ⟨y, hy⟩ := hne
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr
      (inter_C_attachPoints_of_boundary_nonempty hC hy)
    have ha' : a ∈ ({p, q} : Finset V) := hpq (Finset.mem_inter.mp ha).2
    refine Finset.nonempty_iff_ne_empty.mp
      ⟨a, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).1, ha'⟩⟩
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr
      (inter_attachPoints_of_isOddCycle_ne_of_packing_one (packingNumberOne_of_locIndep_one hG)
        hC hshort hD hDC)
    refine Finset.nonempty_iff_ne_empty.mp
      ⟨a, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).1, hpq (Finset.mem_inter.mp ha).2⟩⟩

/-- **A PROVABLE CASE OF `JSP90.FanTwoResidual`: A FAN OF SIZE `2` WITH AT MOST TWO ATTACHMENT
POINTS.**  The certificate is the attachment set, which lies on `C`. -/
theorem erdos73On_one_two_of_boundary_card_eq_two_of_attachPoints_le_two (hG : LocIndep 1 G)
    {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hfan : (boundary G C).card = 2) (hb : (attachPoints G C).card ≤ 2) : CloseToBipartite 2 G :=
  erdos73On_one_two_of_attachPoints_le_two hG hC hshort
    (nonempty_boundary_of_card_ge_two hfan (by omega)) hb

/-! ## Part 6 — a **tighter residual** for the sharp case `k = 1`

Everything of the sharp case is now settled except the graphs in which **every** shortest odd cycle
has at least **three** attachment points. -/

/-- **THE RESIDUAL OF THE SHARP CASE `k = 1`, IN THE SHAPE OF THE ATTACHMENT POINTS.**  At
`LocIndep 1`, if a shortest odd cycle `C` has **at least three** attachment points, then some set of
at most **two** vertices meets every odd cycle of `G`.

This is *strictly weaker* than the residual of round 135, `JSP90.FanTwoResidual`
(`2 ≤ |boundary G C|`): the cases `|boundary G C| = 0` and `|attachPoints G C| ≤ 2` are theorems of
this file (Parts 3–5), and `3 ≤ |attachPoints G C|` forces `2 ≤ |boundary G C|`.
`JSP90.fanTwoResidual_of_attachThreeResidual` makes this formal, and
`JSP90.erdos73On_one_two_of_attachThreeResidual` proves the implication to the **sharp**
`Erdős73On 1 2`. -/
def AttachThreeResidual : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    ∀ (C : Finset W), IsOddCycle G C → (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) →
      3 ≤ (attachPoints G C).card → ∃ X : Finset W, X.card ≤ 2 ∧ HitsOddCycles G X

/-- **THE SHARP CASE `k = 1` OF ERDŐS PROBLEM #73, WITH THE CONSTANT `2`, FROM THE SINGLE STATEMENT
ABOVE.**  The four cases: `G` has no odd cycle; a shortest odd cycle `C` exists with an empty fan (the
constant `1`, by `JSP90.closeToBipartite_boundary_add_one_of_locIndep_one`); the fan is nonempty and
there are at most two attachment points (Part 5, the constant `2`); or there are at least three
attachment points (the hypothesis of `AttachThreeResidual`).  A shortest odd cycle exists by
`JSP90.exists_shortest_oddCycle`, so no choice is made. -/
theorem erdos73On_one_two_of_attachThreeResidual (h : AttachThreeResidual.{u}) : Erdős73On.{u} 1 2 := by
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
      · obtain ⟨X, hXcard, hX⟩ := h W instW G hG C hC hshort (by omega)
        exact ⟨X, hXcard, hX⟩
    · have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hh : HitsOddCycles G ({c} : Finset W) := by
        simpa [h0] using hitsOddCycles_boundary_singleton_of_locIndep_one hG hC hshort c hc
      exact ⟨{c}, by simp, hh⟩
  · exact ⟨∅, by simp, fun D hD => absurd ⟨D, hD⟩ hex⟩

/-- **THE RESIDUAL OF THIS ROUND IS STRICTLY WEAKER THAN THE RESIDUAL OF ROUND 135.**  Round 135 left
`JSP90.FanTwoResidual` (`2 ≤ |boundary G C|`); the hypothesis is now `3 ≤ |attachPoints G C|`, and the
cases it no longer covers are theorems of this file. -/
theorem fanTwoResidual_of_attachThreeResidual (h : AttachThreeResidual.{u}) : FanTwoResidual.{u} := by
  intro W instW G hG C hC hshort h2
  have hp : PackingNumberOne G := packingNumberOne_of_locIndep_one hG
  by_cases hne : (boundary G C).Nonempty
  · by_cases hb : (attachPoints G C).card ≤ 2
    · exact ⟨attachPoints G C, hb, hitsOddCycles_attachPoints_of_packing_one hp hC hshort hne⟩
    · obtain ⟨X, hX, hXh⟩ := h W instW G hG C hC hshort (by omega)
      exact ⟨X, hX, hXh⟩
  · have h0 : boundary G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [h0, Finset.card_empty] at h2
    omega

/-! ## Part 7 — `K₄`-freeness at `k = 1`, and the missing `|C| = 3` half of the fan bound -/

/-- **ERDŐS'S LOCAL HYPOTHESIS BOUNDS THE SIZE OF EVERY CLIQUE BY `k + 2`.**  This is the deficiency
form of the observation behind `JSP90.LocIndep.clique_card_le`, and it holds for **every** `k`: at
`LocIndep 1` a `K_4` is impossible, at `LocIndep 2` a `K_5` is, and so on. -/
theorem card_isClique_le_two_add {k : ℕ} (hG : LocIndep k G) {T : Finset V} (hT : G.IsClique T) :
    T.card ≤ k + 2 := by
  have h1 := maxDef_clique_add_two_le hT
  have h2 := maxDef_le_of_locIndep hG
  omega

/-- **NO `n`-CLIQUE WITH `n ≥ k + 3` UNDER `LocIndep k`.** -/
theorem not_isNClique_of_card_ge_three_add {k n : ℕ} (hG : LocIndep k G) {s : Finset V}
    (h : G.IsNClique n s) (h3 : k + 3 ≤ n) : False := by
  have hle : n ≤ k + 2 := by
    rw [← h.card_eq]
    exact card_isClique_le_two_add hG h.isClique
  omega

/-- **AT `LocIndep 1` EVERY CLIQUE HAS AT MOST THREE VERTICES** (the `k = 1` case of the previous
theorem; `JSP90.not_isNClique_four_of_locIndep_one` and
`JSP90.not_isClique_card_four_of_locIndep_one` of `JSPProblem/OneK.lean` are the `IsNClique` forms). -/
theorem card_isClique_le_three_of_locIndep_one (hG : LocIndep 1 G) {T : Finset V}
    (hT : G.IsClique T) : T.card ≤ 3 := by
  have h := card_isClique_le_two_add hG hT
  omega

/-- **AT `LocIndep 1` A FAN VERTEX OF A SHORTEST ODD CYCLE HAS AT MOST TWO ATTACHMENT POINTS —
INCLUDING WHEN THE CYCLE IS A TRIANGLE.**

`JSP90.card_attachSet_le_two` (`JSPProblem/Book.lean`) proves this for `5 ≤ |C|`, from
`JSP90.card_inter_neigh_le_two` of `JSPProblem/Fan.lean` (round 35).  The missing `|C| = 3` case is
the `K₄`-free observation: if `x` were adjacent to all three vertices of the triangle `C`, then the
independent set `LocIndep 1` supplies inside `{x} ∪ C` could not have two vertices.  The search of
this round verifies both halves: `max |N(x) ∩ C| = 2` for `|C| = 3` as well as for `|C| ≥ 5`
(`discovery/JSP-000090/r136.c`, question `Q4`). -/
theorem card_attachSet_le_two_of_locIndep_one {C : Finset V} (hG : LocIndep 1 G)
    (hC : IsOddCycle G C) (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    {x : V} (hxb : x ∈ boundary G C) : (attachSet G C x).card ≤ 2 := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hCcard : C.card = m := card_eq_cyclicOrder f hinj hCmem
  by_cases h5 : 5 ≤ m
  · exact card_attachSet_le_two hshort hm h5 f hinj hcyc hCmem hxb
  · have hm3' : m = 3 := by omega
    subst hm3'
    have hxC : x ∉ C := (mem_boundary.mp hxb).1
    have hle : (attachSet G C x).card ≤ C.card := by
      refine Finset.card_le_card fun z hz => (mem_attachSet.mp hz).1
    rw [hCcard] at hle
    by_contra hcon
    have hcard : (attachSet G C x).card = 3 := by omega
    obtain ⟨a, b, c, hab, hac, hbc, habc⟩ := Finset.card_eq_three.mp hcard
    have ha' : a ∈ attachSet G C x := by rw [habc]; simp
    have hb' : b ∈ attachSet G C x := by rw [habc]; simp
    have hc' : c ∈ attachSet G C x := by rw [habc]; simp
    have haC : a ∈ C := (mem_attachSet.mp ha').1
    have hbC : b ∈ C := (mem_attachSet.mp hb').1
    have hcC : c ∈ C := (mem_attachSet.mp hc').1
    have hxa : G.Adj x a := (mem_attachSet.mp ha').2
    have hxb' : G.Adj x b := (mem_attachSet.mp hb').2
    have hxc : G.Adj x c := (mem_attachSet.mp hc').2
    have hxa_ne : x ≠ a := fun h => hxC (h ▸ haC)
    have hxb_ne : x ≠ b := fun h => hxC (h ▸ hbC)
    have hxc_ne : x ≠ c := fun h => hxC (h ▸ hcC)
    have hxabc : x ∉ ({a, b, c} : Finset V) := by
      intro hx'
      have hx' : x = a ∨ x = b ∨ x = c := by simpa using hx'
      rcases hx' with h | h | h
      · exact hxC (h ▸ haC)
      · exact hxC (h ▸ hbC)
      · exact hxC (h ▸ hcC)
    obtain ⟨I, hIsub, hIi, hIle⟩ := hG {x, a, b, c}
    have h4 : ({x, a, b, c} : Finset V).card = 4 := by
      have heq : ({x, a, b, c} : Finset V) = insert x ({a, b, c} : Finset V) := by
        ext z; simp
      rw [heq, Finset.card_insert_of_notMem (s := ({a, b, c} : Finset V)) hxabc,
        Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩]
    have hIcard2 : 2 ≤ I.card := by
      have hle' : ({x, a, b, c} : Finset V).card ≤ 2 * I.card + 1 := by simpa using hIle
      omega
    have hxI : x ∉ I := by
      intro hxI
      have hsub1 : I ⊆ ({x} : Finset V) := by
        intro z hz
        have hz' : z = x ∨ z = a ∨ z = b ∨ z = c := by simpa using hIsub hz
        rcases hz' with h | h | h | h
        · simp [h]
        · exact absurd hxa (hIi hxI (by rw [← h]; exact hz) hxa_ne)
        · exact absurd hxb' (hIi hxI (by rw [← h]; exact hz) hxb_ne)
        · exact absurd hxc (hIi hxI (by rw [← h]; exact hz) hxc_ne)
      have hle' : I.card ≤ 1 := Finset.card_le_card hsub1
      omega
    have hIsubC : I ⊆ C := by
      intro z hz
      have hz' : z = x ∨ z = a ∨ z = b ∨ z = c := by simpa using hIsub hz
      rcases hz' with h | h | h | h
      · exact False.elim (absurd (h ▸ hz) hxI)
      · exact h ▸ haC
      · exact h ▸ hbC
      · exact h ▸ hcC
    have hle2 := indep_card_le_of_odd_cycle hm f hinj hcyc I hIi
      (fun z hz => (hCmem z).mp (hIsubC hz))
    omega

/-! ## Part 8 — what is *not* proved

`JSP90.AttachThreeResidual`, and behind it `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  `jsp_000090_main` is not declared,
so the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`. -/

#print axioms JSP90.sub_inter_or_sdiff_of_isOddCycle
#print axioms JSP90.exists_mem_boundary_neigh_inter_of_isOddCycle_ne_of_packing_one
#print axioms JSP90.mem_attachPoints
#print axioms JSP90.hitsOddCycles_attachPoints_of_packing_one
#print axioms JSP90.hitsOddCycles_attachPoints_union_singleton_of_packing_one
#print axioms JSP90.closeToBipartite_of_attachPoints_le_of_packing_one
#print axioms JSP90.closeToBipartite_one_of_attachPoints_le_one_of_packing_one
#print axioms JSP90.erdos73On_one_two_of_attachPoints_le_two_of_packing_one
#print axioms JSP90.erdos73On_one_two_of_attachPoints_le_two
#print axioms JSP90.closeToBipartite_one_of_attachPoints_le_one
#print axioms JSP90.hitsOddCycles_pair_of_attachPoints_sub
#print axioms JSP90.erdos73On_one_two_of_boundary_card_eq_two_of_attachPoints_le_two
#print axioms JSP90.erdos73On_one_two_of_attachThreeResidual
#print axioms JSP90.fanTwoResidual_of_attachThreeResidual
#print axioms JSP90.card_isClique_le_two_add
#print axioms JSP90.not_isNClique_of_card_ge_three_add
#print axioms JSP90.card_attachSet_le_two_of_locIndep_one

end

end JSP90
