/-
# JSP-000090 — `JSPProblem/Hub.lean`: the **HUB COVER** (pay for a vertex, not for an attachment
# point)

`discovery/JSP-000090/policy.json` (rounds 119 and 120) reduced the absorption step of the residue
induction to a **numerical** question about the attachment set `PetalSet G C` of an odd cycle `C`:
round 119 asked for a function `φ` with `|PetalSet G C| ≤ φ(k)` under `LocIndep k G`, and round 120
proved `|PetalSet G C| ≤ MaxDef G` under a packing cover (`JSP90.card_petalSet_le_maxDef_of_cover`)
while refuting it in general on the seven-vertex witness `g7`.

This file does **not** try to close that numerical question (see `JSPProblem/Wheel.lean` of the same
round, which *refutes the whole family* of bounds `|PetalSet G C| ≤ φ(MaxDef G)`).  Instead it
introduces the object the wheel forces one to introduce: the **hub**.

## The new object

* **`JSP90.HubCover G C Z`** — `C` is an odd cycle meeting every odd cycle of `G`, and **every odd
  cycle which meets `C` in exactly one vertex (every petal of `C`) passes through `Z`**.  Such a `Z`
  is a set of *hubs*: one vertex can carry the petals of many attachment points at once.

The wheel is the reason: in a wheel with an odd cycle of `n` vertices, a hub, and one leaf per cycle
vertex, *all* `n` vertices of `C` are attachment points (`PetalSet G C = C`) while a **single**
vertex — the hub — kills every petal, so the correct constant is one, not `n`.

## What is proved

1. **`JSP90.hitsOddCycles_of_hubCover`, `JSP90.closeToBipartite_of_hubCover`,
   `JSP90.erdos73On_of_hubCover` — A NEW INSTANCE OF THE HEADLINE THEOREM.**  `LocIndep k G`, an odd
   cycle `C`, a set `Z` and `HubCover G C Z` give `CloseToBipartite (|C| - 1 + |Z|) G`.  The
   certificate is `C.erase c ∪ Z`, and the proof is the two cases of an odd cycle `D`: meeting `C`
   in at least two vertices, or being a petal of `C`.

2. **`JSP90.hubCover_petalSet` — ROUND 119 RE-DERIVED.**  `HitsOddCycles G C` gives
   `HubCover G C (PetalSet G C)`, so round 119's transversal is the instance `Z = PetalSet G C` of
   the new theorem, with exactly the constant `|C| - 1 + |PetalSet G C|`.  The new instance is
   therefore never weaker, and `JSP90.hubCover_constant_lt` records the strict improvement
   `Z.card < (PetalSet G C).card`.

3. **`JSP90.HubByPacking r ℓ q`, `JSP90.closeToBipartite_of_hubByPacking`,
   `JSP90.erdos73On_of_hubByPacking`, `JSP90.erdos73On_of_hubByPacking_of_forall`,
   `JSP90.erdos73_of_hubByPacking_of_forall` — THE NEW CLASS-LEVEL RESIDUAL**, in the shape of round
   115's `TwoAttachCoverExists` and round 120's `OneCyclePetal`: for a bounded odd cycle packing
   number there is a short odd cycle `C` and a small hub set `Z`.  `HubsByPacking` for every packing
   bound implies `Erdős73 k` with the constant `ℓ + (q - 1)`, **independent of `k`**.

   `HubByPacking` is a `def` and is **not** assumed anywhere: it is the residual that replaces the
   refuted numerical route, and it is strictly more flexible than the two-attachment cover of round
   115 (whose members had to be odd cycles meeting every odd cycle twice, and which round 117
   refuted).

## What is *not* proved

`jsp_000090_main` is **not** declared, `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) is
untouched, and `HubsByPacking` is unproved.  The concrete instances of the new theorem are given on
the wheel family of `JSPProblem/Wheel.lean`.
-/

import JSPProblem.PetalBound
import JSPProblem.Pivot

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance hubDecidableEq : DecidableEq V := Classical.decEq V

/-! ### Part 1 — the hub cover -/

section HubCover

/-- **THE HUB COVER OF AN ODD CYCLE.**  `Z` is a set of **hubs** for the odd cycle `C`: every odd
cycle of `G` meets `C`, and every odd cycle which meets `C` in **exactly one** vertex — every *petal*
of `C`, in the sense of `JSP90.OneAttach` — passes through `Z`.

This is strictly more flexible than the two-attachment cover of `JSPProblem/TwoAttach.lean`: the
members are vertices rather than odd cycles, and only the *petals* of `C` have to meet `Z`. -/
def HubCover (G : SimpleGraph V) (C Z : Finset V) : Prop :=
  HitsOddCycles G C ∧ ∀ D : Finset V, IsOddCycle G D → (D ∩ C).card = 1 → D ∩ Z ≠ ∅

/-- The first half of a hub cover: `C` meets every odd cycle of `G`. -/
theorem hubCover_hitsOddCycles {C Z : Finset V} (h : HubCover G C Z) : HitsOddCycles G C := h.1

/-- The second half of a hub cover: every petal of `C` passes through `Z`. -/
theorem hubCover_petals {C Z : Finset V} (h : HubCover G C Z) {D : Finset V} (hD : IsOddCycle G D)
    (h1 : (D ∩ C).card = 1) : D ∩ Z ≠ ∅ := h.2 D hD h1

/-- More hubs still cover: `Z ⊆ Z'` and `HubCover G C Z` give `HubCover G C Z'`. -/
theorem hubCover_mono {C Z Z' : Finset V} (h : HubCover G C Z) (hZZ' : Z ⊆ Z') : HubCover G C Z' := by
  refine ⟨h.1, fun D hD h1 => ?_⟩
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty (s := D ∩ Z).mpr (h.2 D hD h1)
  obtain ⟨hxD, hxZ⟩ := Finset.mem_inter.mp hx
  exact Finset.nonempty_iff_ne_empty (s := D ∩ Z').mp
    ⟨x, Finset.mem_inter.mpr ⟨hxD, hZZ' hxZ⟩⟩

/-- **THE HUB TRANSVERSAL.**  If `Z` is a hub cover of the odd cycle `C` then, for **any**
`c ∈ C`, the set `C.erase c ∪ Z` meets every odd cycle of `G`. -/
theorem hitsOddCycles_of_hubCover {C Z : Finset V} {c : V} (hC : IsOddCycle G C) (hc : c ∈ C)
    (hZ : HubCover G C Z) : HitsOddCycles G ((C.erase c) ∪ Z) := by
  intro D hD
  have hne := hZ.1 D hD
  have hcard0 : (D ∩ C).card ≠ 0 :=
    Finset.card_ne_zero.mpr ((Finset.nonempty_iff_ne_empty (s := D ∩ C)).mpr hne)
  rcases Nat.lt_or_ge (D ∩ C).card 2 with hlt | hge
  · have h1 : (D ∩ C).card = 1 := by omega
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty (s := D ∩ Z).mpr (hZ.2 D hD h1)
    obtain ⟨hxD, hxZ⟩ := Finset.mem_inter.mp hx
    exact Finset.nonempty_iff_ne_empty (s := D ∩ ((C.erase c) ∪ Z)).mp
      ⟨x, Finset.mem_inter.mpr ⟨hxD, mem_union_of_right' (s := C.erase c) (t := Z) hxZ⟩⟩
  · obtain ⟨y, hyD, hyX⟩ := exists_mem_inter_erase_of_card_ge_two (D := D) (X := C) hge
    exact Finset.nonempty_iff_ne_empty (s := D ∩ ((C.erase c) ∪ Z)).mp
      ⟨y, Finset.mem_inter.mpr ⟨hyD, mem_union_of_left' (s := C.erase c) (t := Z) hyX⟩⟩

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, PAID FOR BY HUBS.**  If `Z` is a hub cover of the odd
cycle `C` then `G` is the union of a bipartite graph and at most `|C| - 1 + |Z|` vertices. -/
theorem closeToBipartite_of_hubCover {C Z : Finset V} {c : V} (hC : IsOddCycle G C) (hc : c ∈ C)
    (hZ : HubCover G C Z) : CloseToBipartite ((C.card - 1) + Z.card) G := by
  refine closeToBipartite_iff_hitsOddCycles.mpr
    ⟨(C.erase c) ∪ Z, ?_, hitsOddCycles_of_hubCover hC hc hZ⟩
  calc (C.erase c ∪ Z).card ≤ (C.erase c).card + Z.card := Finset.card_union_le _ _
    _ = (C.card - 1) + Z.card := by rw [Finset.card_erase_of_mem hc]

/-- The headline-theorem form of `closeToBipartite_of_hubCover`.  Erdős's hypothesis is *not* used
by the step itself; the constant `|C| - 1 + |Z|` does not grow with `k`. -/
theorem erdos73On_of_hubCover {k : ℕ} {C Z : Finset V} {c : V} (hC : IsOddCycle G C) (hc : c ∈ C)
    (hZ : HubCover G C Z) (hG : LocIndep k G) : CloseToBipartite ((C.card - 1) + Z.card) G :=
  closeToBipartite_of_hubCover hC hc hZ

/-- **ROUND 119'S PETAL SET *IS* A HUB COVER.**  Every petal of `C` meets `PetalSet G C` at its
attachment point (`JSP90.oneAttach_mem_petalSet`), so `HitsOddCycles G C` gives
`HubCover G C (PetalSet G C)`; the instance `closeToBipartite_of_hubCover` is then exactly round
119's `closeToBipartite_of_petalSet` with `a = |PetalSet G C|`. -/
theorem hubCover_petalSet {C : Finset V} (hC : IsOddCycle G C) (hmeet : HitsOddCycles G C) :
    HubCover G C (PetalSet G C) := by
  refine ⟨hmeet, fun D hD h1 => ?_⟩
  obtain ⟨v, hvD, hvA⟩ := oneAttach_mem_petalSet (C := C) (D := D) ⟨hD, h1⟩
  exact Finset.nonempty_iff_ne_empty (s := D ∩ PetalSet G C).mp ⟨v, Finset.mem_inter.mpr ⟨hvD, hvA⟩⟩

/-- **THE NEW INSTANCE, RECOVERED.**  `HubCover G C (PetalSet G C)` gives
`CloseToBipartite ((C.card - 1) + (PetalSet G C).card) G`. -/
theorem closeToBipartite_of_hubCover_petalSet {C : Finset V} {c : V} (hC : IsOddCycle G C) (hc : c ∈ C)
    (hmeet : HitsOddCycles G C) : CloseToBipartite ((C.card - 1) + (PetalSet G C).card) G :=
  closeToBipartite_of_hubCover hC hc (hubCover_petalSet hC hmeet)

/-- **AND THE HUB COVER IS STRICTLY BETTER WHENEVER THE HUB SET IS SMALLER THAN THE ATTACHMENT
SET.**  This is the quantitative reason for preferring hubs to attachment points. -/
theorem hubCover_constant_lt {C Z : Finset V} (hlt : Z.card < (PetalSet G C).card) :
    (C.card - 1) + Z.card < (C.card - 1) + (PetalSet G C).card :=
  Nat.add_lt_add_left hlt (C.card - 1)

end HubCover

/-! ### Part 2 — the class-level statement, and the reduction -/

section HubByPacking

universe u

/-- **THE CLASS-LEVEL STATEMENT**, in the shape of `JSP90.TwoAttachCoverExists` (round 115) and
`JSP90.OneCyclePetal` (round 120): for every finite graph of odd cycle packing number at most `r`
there is an odd cycle `C` of at most `q` vertices and a set `Z` of at most `ℓ` vertices such that
**every petal of `C` passes through `Z`**.

This is a `def`, and it is **not** assumed anywhere.  It replaces the *numerical* residual of rounds
119–120 (`|PetalSet G C| ≤ φ(k)`), which `JSPProblem/Wheel.lean` of this round refutes: a hub set
is a structural object, and it is not a function of the deficiency. -/
def HubByPacking (r ℓ q : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] (G : SimpleGraph W), OddCyclePackingLe r G →
    ∃ C Z : Finset W, IsOddCycle G C ∧ C.card ≤ q ∧ HubCover G C Z ∧ Z.card ≤ ℓ

/-- **THE REDUCTION**: a packing bound `r` together with `HubByPacking r ℓ q` gives Erdős's conclusion
with the constant `ℓ + (q - 1)`. -/
theorem closeToBipartite_of_hubByPacking {r ℓ q : ℕ} (h : HubByPacking.{u} r ℓ q)
    {W : Type u} [Fintype W] {G : SimpleGraph W} (hp : OddCyclePackingLe r G) :
    CloseToBipartite (ℓ + (q - 1)) G := by
  classical
  obtain ⟨C, Z, hC, hCcard, hZ, hZcard⟩ := h W G hp
  have h3 := isOddCycle_card_ge_three hC
  have hpos : 0 < C.card := by omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  have h1 := closeToBipartite_of_hubCover hC hc hZ
  refine closeToBipartite_mono ?_ h1
  omega

/-- The headline-theorem form: Erdős's hypothesis `LocIndep k G` gives the packing bound `k`, and if
`k ≤ r` then `HubByPacking r ℓ q` applies; the constant `ℓ + (q - 1)` is **independent of `k`**. -/
theorem erdos73On_of_hubByPacking {r ℓ q k : ℕ} (h : HubByPacking.{u} r ℓ q)
    {W : Type u} [Fintype W] {G : SimpleGraph W} (hG : LocIndep k G) (hr : k ≤ r) :
    CloseToBipartite (ℓ + (q - 1)) G := by
  exact closeToBipartite_of_hubByPacking h (fun P hP =>
    (locIndep_oddCyclePackingLe hG P hP).trans hr)

/-- **THE HEADLINE SHAPE**: if `HubByPacking r ℓ q` holds for *every* packing bound `r`, then every
graph satisfying Erdős's hypothesis with parameter `k` is the union of a bipartite graph and at most
`ℓ + (q - 1)` vertices. -/
theorem erdos73On_of_hubByPacking_of_forall {k ℓ q : ℕ} (h : ∀ r, HubByPacking.{u} r ℓ q)
    {W : Type u} [Fintype W] {G : SimpleGraph W} (hG : LocIndep k G) :
    CloseToBipartite (ℓ + (q - 1)) G :=
  erdos73On_of_hubByPacking (h k) hG (Nat.le_refl k)

/-- **AND THEREFORE ERDŐS #73 ITSELF.**  `HubByPacking` for every packing bound implies
`Erdős73 k` for every `k`, i.e. `jsp_000090_main`, with the constant `ℓ + (q - 1)` — again
independent of `k`. -/
theorem erdos73_of_hubByPacking_of_forall {k ℓ q : ℕ} (h : ∀ r, HubByPacking.{u} r ℓ q) :
    Erdős73.{u} k := by
  refine ⟨ℓ + (q - 1), ?_⟩
  intro W _ G hG
  exact erdos73On_of_hubByPacking_of_forall h hG

end HubByPacking

end

end JSP90
