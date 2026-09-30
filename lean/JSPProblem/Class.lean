/-
# JSP-000090, round 70 — **the classes of the fan, the parity of two classes, and the two-vertex
arc (the "no short cut" lemma)**

## Where the development stands

Rounds 64–69 reduced Erdős Problem #73 to **one** statement: `JSP90.FanErdős73 f` of
`JSPProblem/Free.lean` — for every triangle-free `G` with `LocIndep k G` and every odd cycle `C`
of `G`, a set `Z` of at most `f k` vertices meeting **every odd cycle of `G` that meets the
boundary of `C`**.  Round 69 proved `JSP90.erdos73_iff_fanErdős73`, so that statement is
*equivalent* to the whole problem, and round 68 proved it is equivalent to
`JSP90.TriangleFreeOnly`.

So the remaining content is the pure combinatorics of the **fan** of one odd cycle in a
triangle-free graph.  Round 69 established the local structure of the fan
(`JSP90.card_inter_neigh_le_two`, `JSP90.shortArc_of_shortest`, `JSP90.not_adj_cycSucc_of_adj`,
`JSP90.pairwise_not_adj_fan_of_cliqueFree3`) but had no *name* for the classes of the fan and no
statement about them.  This file supplies both, and then extracts the following: a parity lemma
for two classes, a counting lemma for the far part of the fan, a new instance of the headline
theorem along the class axis, and the two-vertex analogue of the arc constructor of
`JSPProblem/Fan.lean` together with the classical **"no short cut" lemma** of the fan argument.
29 declarations, 0 placeholders.
-/

import JSPProblem.Free
import Mathlib.Data.Finset.SDiff

namespace JSP90

universe u

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqClass : DecidableEq V := Classical.decEq V

local instance instDecidableAdjClass (G : SimpleGraph V) : ∀ (v w : V), Decidable (G.Adj v w) :=
  fun _ _ => Classical.propDecidable _

/-! ## Part 1 — the classes of the fan

`JSP90.fanClass G C a = (boundary G C).filter (G.Adj a)` is the set of fan vertices attached to
`a`.  Proved: `JSP90.mem_fanClass`, `JSP90.subset_fanClass_boundary`, `JSP90.mem_fanClass_of_adj`,
`JSP90.subset_fanClass_of_subset_boundary`, **`JSP90.isIndepSet_fanClass`** (a class is
independent, being contained in the independent neighbourhood of `a`) and
`JSP90.exists_mem_fanClass_of_mem_boundary` (**every vertex of the fan lies in some class**).

## Part 2 — the parity of two classes

`JSP90.fanColour G a x = if G.Adj x a then 0 else 1` is a **proper 2-colouring of any vertex set
covered by two classes**: two vertices of the same colour are either both attached to `a` (hence
non-adjacent, `a`'s class is independent) or both attached to `b` (likewise, because they are in
the fan, so not being attached to `a` puts them in `b`'s class).  Proved:

* **`JSP90.isBipartite_of_subset_fanClass_union`**, and hence
* **`JSP90.not_isOddCycle_of_subset_fanClass_union`: AN ODD CYCLE OF `G` IS NEVER CONTAINED IN
  TWO CLASSES** (an odd cycle cannot run through only two attachment points of `C`; the parity is
  read off by `JSP90.even_of_cycle_in_bipartition` of round 40), and
* `JSP90.not_subset_two_fanClass_of_isOddCycle` together with
  `JSP90.card_ge_three_of_isOddCycle_of_subset_boundary`.

## Part 3 — the far part of the fan, and the counting lemma

`JSP90.farFan G C a b = (boundary G C) \ (fanClass G C a ∪ fanClass G C b)` is the part of the fan
attached to *neither* `a` nor `b`.  Proved:

* **`JSP90.hitsOddCycles_farFan`: the far part of the fan meets every odd cycle of `G` contained
  in the fan** (by Part 2);
* `JSP90.card_le_biUnion_of_disjoint_ne` — a disjoint family of nonempty sets is counted by its
  union — and hence
* **`JSP90.card_farFan_ge_of_disjoint_oddCycles`: a packing of `j` odd cycles of `G` inside the
  fan of `C` needs `j` vertices of the far part, for *every* pair `a, b ∈ C`.**  This is the first
  *counting* statement about the fan, and the shape of the classical half-integral argument: the
  far part is a transversal for every pair, so a transversal of the fan is forced to spread out
  over the classes;
* **`JSP90.fanErdős73_of_fan_twoClass` and `JSP90.erdos73On_of_fan_twoClass` — a new instance of
  the headline theorem along a new axis**: if every odd cycle of a triangle-free graph with
  `LocIndep k G` has two vertices `a, b ∈ C` such that (i) the fan of `C` is covered by the two
  classes of `a` and `b` and (ii) `{a, b}` meets every odd cycle of `G`, then `LocIndep k G`
  forces `CloseToBipartite (fanBound (fun _ => 2) k) G`.  The class structure is used only to say
  that the two vertices hit the fan, so the statement is proved with no packing number, no odd
  girth, no packing weight and no bound on the number of branch vertices.

## Part 4 — the two-vertex arc, and the "no short cut" lemma

The parity core of the fan argument so far was `JSP90.arc_isOddCycle` of `JSPProblem/Fan.lean`,
which closes an **arc of the cycle through ONE outside vertex**.  A fan edge needs **two**: the
cycle `x — y — a — (arc) — b — x`, and that is a *simple* cycle, so a shortest odd cycle forbids
short such cycles.  The file supplies the missing constructor:

* `JSP90.arcFun2` — the closed walk `x → y → f i → f (cycSucc i) → … → f (cycSucc^[e] i) → x`, as
  a map `Fin (e + 3) → V`, with `JSP90.arcFun2_zero`, `JSP90.arcFun2_one`, `JSP90.arcFun2_two`
  and `JSP90.arcFun2_last` for its four distinguished entries;
* `JSP90.arcFun2_ne` — **the walk is simple** (no vertex repeated) when `e < m` and the two outside
  vertices are distinct and off the cycle;
* `JSP90.arcFun2_adj` — **consecutive entries are adjacent**;
* `JSP90.arc_card2` — the cycle has exactly `e + 3` vertices; and
* **`JSP90.arc2_isOddCycle`: CLOSING AN EVEN ARC THROUGH TWO ADJACENT OUTSIDE VERTICES GIVES A
  SIMPLE ODD CYCLE OF EXACTLY `e + 3` VERTICES** — the two-vertex analogue of
  `JSP90.arc_isOddCycle`, and the second parity core of the classical fan argument;
* **`JSP90.not_adj_fan_of_far_attach` — THE "NO SHORT CUT" LEMMA**: if `x` and `y` are two
  distinct vertices outside a shortest odd cycle, adjacent to each other, with `x` adjacent to
  `f i` and `y` adjacent to `f (cycSucc^[d] i)`, then the arc between their attachment points has
  length `d ≤ 3` **or** `d ≥ m - 3`.  Equivalently (**`JSP90.not_adj_of_attach_far`**): **two
  fan vertices whose attachment points are `4` to `m - 5` steps apart around the cycle are never
  adjacent.**  No triangle-free hypothesis occurs — the lemma is a statement about shortest odd
  cycles in *any* graph; the "book, not web" picture of the fan needs
  `JSP90.not_adj_cycSucc_of_adj` (round 69) and `JSP90.shortArc_of_shortest` (round 35) on top of
  it.

## What is *not* proved

`JSP90.FanErdős73 f` for any `f`, and hence `jsp_000090_main`.  The counting lemma of Part 3 is
the *shape* of the classical half-integral argument ("a transversal of size `t` of the fan forces
a packing of `≳ t / |C|` odd cycles"), but the quantitative half — turning "the far part is a
transversal for every pair `a, b`" into a bound `t ≤ O_k(1)` on the least transversal of the fan
— is not proved.  `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) stands behind it.
-/

/-! ## Part 1 — the classes of the fan -/

section Classes

/-- **THE CLASS OF `a`.**  The vertices of the fan of `C` attached to `a`.  Round 69 proved
(`JSP90.pairwise_not_adj_fan_of_cliqueFree3`) that fan vertices attached to one and the same
vertex of the cycle are pairwise non-adjacent, so each class is an independent set; the content of
Part 2 is what *two* classes give. -/
noncomputable def fanClass (G : SimpleGraph V) (C : Finset V) (a : V) : Finset V :=
  (boundary G C).filter (G.Adj a)

theorem mem_fanClass {C : Finset V} {a x : V} :
    x ∈ fanClass G C a ↔ x ∈ boundary G C ∧ G.Adj a x := by
  simp [fanClass]

/-- A class lies in the fan. -/
theorem subset_fanClass_boundary (C : Finset V) (a : V) : fanClass G C a ⊆ boundary G C :=
  fun _ hx => (mem_fanClass.mp hx).1

/-- **A CLASS IS AN INDEPENDENT SET**: two fan vertices attached to the same vertex of the cycle
are not adjacent.  (The local form of "the neighbourhood of a vertex is independent".) -/
theorem isIndepSet_fanClass (hG3 : G.CliqueFree 3) (C : Finset V) (a : V) :
    G.IsIndepSet (fanClass G C a) := by
  intro x hx y hy hxy
  exact not_adj_of_common_neigh_of_cliqueFree3 hG3 (mem_fanClass.mp hx).2 (mem_fanClass.mp hy).2

/-- **A CLASS CONTAINS EVERYTHING OF THE FAN ATTACHED TO `a`.** -/
theorem mem_fanClass_of_adj {C : Finset V} {a x : V} (hxb : x ∈ boundary G C) (hax : G.Adj a x) :
    x ∈ fanClass G C a := mem_fanClass.mpr ⟨hxb, hax⟩

/-- **A CLASS CONTAINS A SET OF FAN VERTICES ALL ADJACENT TO `a`.** -/
theorem subset_fanClass_of_subset_boundary {C : Finset V} {a : V} {X : Finset V}
    (hX : X ⊆ boundary G C)
    (hXa : ∀ x ∈ X, G.Adj a x) : X ⊆ fanClass G C a :=
  fun x hx => mem_fanClass_of_adj (hX hx) (hXa x hx)

/-- **EVERY VERTEX OF THE FAN LIES IN AT LEAST ONE CLASS.** -/
theorem exists_mem_fanClass_of_mem_boundary {C : Finset V} {x : V} (hx : x ∈ boundary G C) :
    ∃ a ∈ C, x ∈ fanClass G C a := by
  obtain ⟨a, haC, hax⟩ := (mem_boundary.mp hx).2
  exact ⟨a, haC, mem_fanClass_of_adj hx (hax.symm)⟩

end Classes

/-! ## Part 2 — the parity of two classes -/

section TwoClasses

/-- **THE CLASS-COLOURING.**  `0` on the class of `a`, `1` off it. -/
noncomputable def fanColour (G : SimpleGraph V) (a : V) (x : V) : Fin 2 :=
  if G.Adj x a then 0 else 1

/-- **A VERTEX SET COVERED BY TWO CLASSES IS BIPARTITE.**  Two vertices of the same colour are
either both attached to `a`, or both attached to `b` (because they are in the fan, so not being
attached to `a` puts them in `b`'s class); in both cases they are not adjacent, because a class
is independent. -/
theorem isBipartite_of_subset_fanClass_union (hG3 : G.CliqueFree 3) (C : Finset V) (a b : V)
    {X : Finset V} (hX : X ⊆ fanClass G C a ∪ fanClass G C b) : (induceFinset G X).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun x => fanColour G a x) ?_⟩
  intro x y h
  rw [induce_adj] at h
  rcases h with ⟨hxX, hyX, hxy⟩
  by_cases hxa : G.Adj x a <;> by_cases hya : G.Adj y a
  · exact absurd hxy (not_adj_of_common_neigh_of_cliqueFree3 hG3 hxa.symm hya.symm)
  · simp [fanColour, hxa, hya]
  · simp [fanColour, hxa, hya]
  · have hxmem : x ∈ fanClass G C b := by
      rcases Finset.mem_union.mp (hX hxX) with h | h
      · exact absurd h (fun hx => hxa (mem_fanClass.mp hx).2.symm)
      · exact h
    have hymem : y ∈ fanClass G C b := by
      rcases Finset.mem_union.mp (hX hyX) with h | h
      · exact absurd h (fun hy => hya (mem_fanClass.mp hy).2.symm)
      · exact h
    exact absurd hxy
      (not_adj_of_common_neigh_of_cliqueFree3 hG3 (mem_fanClass.mp hxmem).2
        (mem_fanClass.mp hymem).2)

/-- **AN ODD CYCLE OF `G` IS NEVER CONTAINED IN TWO CLASSES.**  The parity core of the class
structure: an odd cycle cannot run through only two attachment points of `C`. -/
theorem not_isOddCycle_of_subset_fanClass_union (hG3 : G.CliqueFree 3) {C D : Finset V} {a b : V}
    (hsub : D ⊆ fanClass G C a ∪ fanClass G C b) (hD : IsOddCycle G D) : False := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hDmem⟩ := hD
  have hB : (induceFinset G D).IsBipartite :=
    isBipartite_of_subset_fanClass_union hG3 C a b hsub
  obtain ⟨c, hc⟩ := hB
  have hfin (u : Fin 2) : u = 0 ∨ u = 1 := by
    rcases Nat.lt_or_ge u.1 1 with h | h
    · exact Or.inl (Fin.ext (by omega))
    · exact Or.inr (Fin.ext (by omega))
  have hst : (induceFinset G D).IsBipartiteWith ({x : V | c x = 0} : Set V)
      ({x : V | c x = 1} : Set V) := by
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro v hv1 hv2
      rw [Set.mem_setOf_eq] at hv1 hv2
      have hbad : (0 : Fin 2) = 1 := hv1.symm.trans hv2
      exact absurd hbad (by decide)
    · intro v w hvw
      by_cases h0v : c v = 0
      · by_cases h0w : c w = 0
        · exfalso
          have h2v : (c v).1 < 2 := (c v).isLt
          exact absurd (Fin.ext (by omega)) (hc hvw)
        · exact Or.inl ⟨Set.mem_setOf_eq.mpr h0v, Set.mem_setOf_eq.mpr (by
            rcases hfin (c w) with h | h
            · exact absurd h h0w
            · exact h)⟩
      · have h1v : c v = 1 := by
          rcases hfin (c v) with h | h
          · exact absurd h h0v
          · exact h
        exact Or.inr ⟨Set.mem_setOf_eq.mpr h1v, Set.mem_setOf_eq.mpr (by
          rcases hfin (c w) with h | h
          · exact h
          · exact absurd (hc hvw) (by simp [h1v, h]))⟩
  have hall : ∀ j : Fin m, f j ∈ ({x : V | c x = 0} : Set V) ∪ {x : V | c x = 1} := by
    intro j
    rcases hfin (c (f j)) with h | h
    · exact Or.inl (Set.mem_setOf_eq.mpr h)
    · exact Or.inr (Set.mem_setOf_eq.mpr h)
  have hadj : ∀ j : Fin m, (induceFinset G D).Adj (f j) (f (cycSucc j)) := by
    intro j
    exact induce_adj.mpr
      ⟨(hDmem (f j)).mpr ⟨j, rfl⟩, (hDmem (f (cycSucc j))).mpr ⟨cycSucc j, rfl⟩, hcyc j⟩
  have hall : ∀ j : Fin m, f j ∈ ({x : V | c x = 0} : Set V) ∪ {x : V | c x = 1} := by
    intro j
    rcases hfin (c (f j)) with h | h
    · exact Or.inl (Set.mem_setOf_eq.mpr h)
    · exact Or.inr (Set.mem_setOf_eq.mpr h)
  exact absurd (even_of_cycle_in_bipartition (bip := hst) hm3 f hadj hall) (by omega)

/-- **AN ODD CYCLE CONTAINED IN THE FAN IS NOT COVERED BY THE CLASSES OF TWO VERTICES OF `C`.** -/
theorem not_subset_two_fanClass_of_isOddCycle (hG3 : G.CliqueFree 3) {C D : Finset V}
    (hD : IsOddCycle G D) (_hsub : D ⊆ boundary G C) {a b : V} :
    ¬ (D ⊆ fanClass G C a ∪ fanClass G C b) :=
  fun h => not_isOddCycle_of_subset_fanClass_union hG3 h hD

/-- **AN ODD CYCLE CONTAINED IN THE FAN HAS AT LEAST THREE VERTICES.** -/
theorem card_ge_three_of_isOddCycle_of_subset_boundary {C D : Finset V} (hD : IsOddCycle G D)
    (_hsub : D ⊆ boundary G C) : 3 ≤ D.card := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hDmem⟩ := hD
  rw [card_eq_cyclicOrder f hinj hDmem]
  exact hm3

end TwoClasses

/-! ## Part 3 — the far part of the fan, and the counting lemma -/

section FarFan

/-- **THE FAR PART OF THE FAN**: the vertices of the fan attached to neither `a` nor `b`. -/
noncomputable def farFan (G : SimpleGraph V) (C : Finset V) (a b : V) : Finset V :=
  (boundary G C) \ (fanClass G C a ∪ fanClass G C b)

theorem mem_farFan {C : Finset V} {a b x : V} :
    x ∈ farFan G C a b ↔ x ∈ boundary G C ∧ ¬ G.Adj x a ∧ ¬ G.Adj x b := by
  rw [farFan, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    refine ⟨h1, fun ha => h2 (Or.inl (mem_fanClass.mpr ⟨h1, ha.symm⟩)),
      fun hb => h2 (Or.inr (mem_fanClass.mpr ⟨h1, hb.symm⟩))⟩
  · rintro ⟨h1, h2a, h2b⟩
    refine ⟨h1, fun h => ?_⟩
    rcases h with h | h
    · exact h2a (mem_fanClass.mp h).2.symm
    · exact h2b (mem_fanClass.mp h).2.symm

/-- **THE FAR PART OF THE FAN MEETS EVERY ODD CYCLE CONTAINED IN THE FAN.**  By Part 2 an odd
cycle of the fan is not covered by two classes. -/
theorem hitsOddCycles_farFan (hG3 : G.CliqueFree 3) {C : Finset V} {a b : V} (_hab : a ∈ C)
    (_hbb : b ∈ C) {D : Finset V} (hD : IsOddCycle G D) (hsub : D ⊆ boundary G C) :
    D ∩ farFan G C a b ≠ ∅ := by
  by_contra hcon
  have hne : D ∩ farFan G C a b = ∅ := hcon
  refine not_isOddCycle_of_subset_fanClass_union hG3 (C := C) (a := a) (b := b) ?_ hD
  intro y hy
  by_cases hyf : y ∈ farFan G C a b
  · exfalso
    have hmem : y ∈ D ∩ farFan G C a b := Finset.mem_inter.mpr ⟨hy, hyf⟩
    have hmem' : y ∈ (∅ : Finset V) := hne ▸ hmem
    simp at hmem'
  · by_cases hyb : y ∈ boundary G C
    · by_cases hya : G.Adj y a
      · exact Finset.mem_union.mpr (Or.inl (mem_fanClass.mpr ⟨hyb, hya.symm⟩))
      · by_cases hyb2 : G.Adj y b
        · exact Finset.mem_union.mpr (Or.inr (mem_fanClass.mpr ⟨hyb, hyb2.symm⟩))
        · exact absurd (mem_farFan.mpr ⟨hyb, hya, hyb2⟩) hyf
    · exact absurd (hsub hy) hyb

/-- **COUNTING A DISJOINT FAMILY OF NONEMPTY SETS.**  If `g D` is nonempty for every `D ∈ T` and
the sets `g D` are pairwise disjoint, then `T` has at most as many members as the union of the
`g D`.  Induction on `T`; the point is that the new piece `g X` is disjoint from the union of the
rest, so the union gains at least one element. -/
theorem card_le_biUnion_of_disjoint_ne {T : Finset (Finset V)} (g : Finset V → Finset V)
    (hne : ∀ D ∈ T, (g D).Nonempty)
    (hdis : ∀ (X : Finset V), X ∈ T → ∀ (Y : Finset V), Y ∈ T → X ≠ Y →
      ∀ (x : V), x ∈ g X → x ∉ g Y) : T.card ≤ (T.biUnion g).card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert X t hX ih =>
      have h1 : 0 < (g X).card := Finset.card_pos.mpr (hne X (Finset.mem_insert_self X t))
      have hne' : ∀ D ∈ t, (g D).Nonempty :=
        fun D hD => hne D (Finset.mem_insert_of_mem hD)
      have hdis' : ∀ (X' : Finset V), X' ∈ t → ∀ (Y : Finset V), Y ∈ t → X' ≠ Y →
          ∀ (z : V), z ∈ g X' → z ∉ g Y :=
        fun X' hX' Y hY hX'Y z hz => hdis X' (Finset.mem_insert_of_mem hX') Y
          (Finset.mem_insert_of_mem hY) hX'Y z hz
      have h2 : (g X) ∩ t.biUnion g = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr ?_
        intro z hz
        rcases Finset.mem_inter.mp hz with ⟨h1z, hzz⟩
        rcases Finset.mem_biUnion.mp hzz with ⟨Y, hY, hz2⟩
        have hXY : X ≠ Y := fun hXY => hX (hXY ▸ hY)
        exact absurd hz2 (hdis X (Finset.mem_insert_self X t) Y (Finset.mem_insert_of_mem hY)
          hXY z h1z)
      calc (insert X t).card = t.card + 1 := Finset.card_insert_of_notMem hX
        _ ≤ (t.biUnion g).card + 1 := Nat.add_le_add_right
            (ih hne' hdis') 1
        _ ≤ ((insert X t).biUnion g).card := by
            rw [Finset.biUnion_insert, Finset.card_union_of_disjoint
              (Finset.disjoint_left.mpr fun z hz1 hz2 => by
                have hz : z ∈ (∅ : Finset V) := h2 ▸ Finset.mem_inter.mpr ⟨hz1, hz2⟩
                simp at hz)]
            omega

/-- **THE COUNTING LEMMA OF THE FAN: a packing of `j` odd cycles of `G` inside the fan of `C`
needs `j` vertices of the far part, for *every* pair `a, b` of vertices of `C`.**  This is the
shape of the classical half-integral argument: the far part is a transversal for every pair, so a
transversal of the fan is forced to spread out over the classes. -/
theorem card_farFan_ge_of_disjoint_oddCycles (hG3 : G.CliqueFree 3) {C : Finset V} {a b : V}
    (hab : a ∈ C) (hbb : b ∈ C) {𝒟 : Finset (Finset V)} (hD : IsOddCycleFamily (G := G) 𝒟)
    (hsub : ∀ D ∈ 𝒟, D ⊆ boundary G C) : 𝒟.card ≤ (farFan G C a b).card := by
  classical
  have hne : ∀ D ∈ 𝒟, (D ∩ farFan G C a b).Nonempty := by
    intro D hX
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    exact hitsOddCycles_farFan hG3 hab hbb (hD.2 D hX) (hsub D hX)
  have hdis : ∀ (X : Finset V), X ∈ 𝒟 → ∀ (Y : Finset V), Y ∈ 𝒟 → X ≠ Y →
      ∀ (x : V), x ∈ X ∩ farFan G C a b → x ∉ Y ∩ farFan G C a b := by
    intro X hX Y hY hXY x hx
    rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
    intro hxY
    rcases Finset.mem_inter.mp hxY with ⟨hxY1, hxY2⟩
    have hz : x ∈ (∅ : Finset V) := hD.left X hX Y hY hXY ▸ Finset.mem_inter.mpr ⟨hx1, hxY1⟩
    simp at hz
  have hsub2 : 𝒟.biUnion (fun D : Finset V => D ∩ farFan G C a b) ⊆ farFan G C a b := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨D, hD, hzD⟩
    exact Finset.mem_inter.mp hzD |>.2
  exact (card_le_biUnion_of_disjoint_ne (fun D : Finset V => D ∩ farFan G C a b) hne hdis).trans
    (Finset.card_le_card hsub2)

/-- **THE FAN STATEMENT FOR A GRAPH WHOSE FANS ARE TWO-CLASS COVERED AND WHOSE ODD CYCLES ARE
HIT BY TWO VERTICES.**  A new instance of the fan statement — and hence, by
`JSP90.erdos73On_of_fanErdős73`, a new instance of the headline theorem.  The class structure
here is used only to say that the two vertices hit the fan, so the statement is proved with no
packing number, no odd girth, no packing weight and no bound on the number of branch vertices. -/
theorem fanErdős73_of_fan_twoClass
    (hP : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
      ∀ C : Finset W, IsOddCycle G C →
        ∃ a b : W, a ∈ C ∧ b ∈ C ∧
          (boundary G C ⊆ fanClass G C a ∪ fanClass G C b) ∧ HitsOddCycles G {a, b}) :
    FanErdős73.{u} (fun _ => 2) := by
  intro k W instW G hG hG3 C hC
  obtain ⟨a, b, haC, hbC, hsub, hhits⟩ := hP k W instW G hG hG3 C hC
  exact ⟨{a, b}, Finset.card_le_two, fun D hD _ => hhits D hD⟩

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, ALONG THE CLASS STRUCTURE OF THE FAN.** -/
theorem erdos73On_of_fan_twoClass
    (hP : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
      ∀ C : Finset W, IsOddCycle G C →
        ∃ a b : W, a ∈ C ∧ b ∈ C ∧
          (boundary G C ⊆ fanClass G C a ∪ fanClass G C b) ∧ HitsOddCycles G {a, b})
    (k : ℕ) : Erdős73On.{u} k (fanBound (fun _ => 2) k) :=
  erdos73On_of_fanErdős73 (fun k W instW G hG hG3 C hC => by
    obtain ⟨a, b, haC, hbC, hsub, hhits⟩ := hP k W instW G hG hG3 C hC
    exact ⟨{a, b}, Finset.card_le_two, fun D hD _ => hhits D hD⟩) k

end FarFan

/-! ## Part 4 — the two-vertex arc, and the "no short cut" lemma -/

section TwoVertexArc

/-- **THE TWO-VERTEX CLOSED WALK** `x → y → f i → f (cycSucc i) → … → f (cycSucc^[e] i) → x`,
as a map `Fin (e + 3) → V`: entry `0` is `x`, entry `1` is `y`, entry `k + 2` is
`f (cycSucc^[k] i)`.  The two-vertex analogue of `JSP90.arcFun`: a fan edge `x — y` closes the arc
of the cycle between the attachment points of `x` and `y`. -/
noncomputable def arcFun2 (m e : ℕ) (f : Fin m → V) (i : Fin m) (x y : V) (j : Fin (e + 3)) : V :=
  if j.val = 0 then x
  else if j.val = 1 then y
  else f ((cycSucc^[j.val - 2] : Fin m → Fin m) i)

@[simp] theorem arcFun2_zero {m e : ℕ} (f : Fin m → V) (i : Fin m) (x y : V) :
    arcFun2 m e f i x y (0 : Fin (e + 3)) = x := by
  simp [arcFun2]

theorem arcFun2_one {m e : ℕ} (h : 1 < e + 3) (f : Fin m → V) (i : Fin m) (x y : V) :
    arcFun2 m e f i x y ⟨1, h⟩ = y := by
  simp [arcFun2]

theorem arcFun2_two {m e : ℕ} (h : 2 < e + 3) (f : Fin m → V) (i : Fin m) (x y : V) :
    arcFun2 m e f i x y ⟨2, h⟩ = f i := by
  simp [arcFun2]

theorem arcFun2_last {m e : ℕ} (f : Fin m → V) (i : Fin m) (x y : V) :
    arcFun2 m e f i x y ⟨e + 2, by omega⟩ = f ((cycSucc^[e] : Fin m → Fin m) i) := by
  simp [arcFun2]

/-- **THE TWO-VERTEX CLOSED WALK IS SIMPLE**, provided the arc is shorter than the cycle and the
two outside vertices are distinct and outside the image of the cyclic ordering. -/
theorem arcFun2_ne {m e : ℕ} (he : e < m) (f : Fin m → V) (hinj : Function.Injective f)
    (i : Fin m) (x y : V) (hxy : x ≠ y) (hximg : ∀ j : Fin m, f j ≠ x)
    (hyimg : ∀ j : Fin m, f j ≠ y) {a b : Fin (e + 3)} (hne : a ≠ b) :
    arcFun2 m e f i x y a ≠ arcFun2 m e f i x y b := by
  intro hab
  have hstep2 {a b : Fin (e + 3)} (h2a : 2 ≤ a.val) (h2b : 2 ≤ b.val)
      (hf : f ((cycSucc^[a.val - 2] : Fin m → Fin m) i) = f ((cycSucc^[b.val - 2] : Fin m → Fin m) i)) :
      a.val = b.val := by
    have hstep : ((cycSucc^[a.val - 2] : Fin m → Fin m) i)
        = ((cycSucc^[b.val - 2] : Fin m → Fin m) i) := hinj hf
    have hv : (i.val + (a.val - 2)) % m = (i.val + (b.val - 2)) % m := by
      have h := congrArg Fin.val hstep
      simpa only [cycSucc_pow_val] using h
    have hla : a.val - 2 < m := by
      have hsub : a.val - 2 ≤ (e + 2 : ℕ) - 2 :=
        Nat.sub_le_sub_right (show a.val ≤ e + 2 by omega) 2
      have : a.val - 2 ≤ e := by simpa using hsub
      exact lt_of_le_of_lt this he
    have hlb : b.val - 2 < m := by
      have hsub : b.val - 2 ≤ (e + 2 : ℕ) - 2 :=
        Nat.sub_le_sub_right (show b.val ≤ e + 2 by omega) 2
      have : b.val - 2 ≤ e := by simpa using hsub
      exact lt_of_le_of_lt this he
    have hsub : a.val - 2 = b.val - 2 :=
      mod_inj_add (m := m) (a := i.val) (b := a.val - 2) (b' := b.val - 2) hla hlb hv
    have h2 : 2 ≤ a.val := by omega
    have h2b : 2 ≤ b.val := by omega
    calc a.val = (a.val - 2) + 2 := (Nat.sub_add_cancel h2).symm
      _ = (b.val - 2) + 2 := by rw [hsub]
      _ = b.val := Nat.sub_add_cancel h2b
  by_cases ha0 : a.val = 0
  · by_cases hb0 : b.val = 0
    · exact hne (Fin.ext (ha0.trans hb0.symm))
    · by_cases hb1 : b.val = 1
      · exact hxy (by simpa [arcFun2, ha0, hb1] using hab)
      · exact (hximg _ (by simpa [arcFun2, ha0, hb0, hb1] using hab.symm)).elim
  · by_cases hb0 : b.val = 0
    · by_cases ha1 : a.val = 1
      · exact hxy (by simpa [arcFun2, ha1, hb0] using hab.symm)
      · exact (hximg _ (by simpa [arcFun2, ha0, ha1, hb0] using hab)).elim
    · by_cases ha1 : a.val = 1
      · by_cases hb1 : b.val = 1
        · exact hne (Fin.ext (ha1.trans hb1.symm))
        · exact (hyimg _ (by simpa [arcFun2, ha1, hb0, hb1] using hab.symm)).elim
      · by_cases hb1 : b.val = 1
        · exact (hyimg _ (by simpa [arcFun2, ha0, ha1, hb0, hb1] using hab)).elim
        · exact hne (Fin.ext (hstep2 (by omega) (by omega) (by
              simpa [arcFun2, ha0, ha1, hb0, hb1] using hab)))

/-- **CONSECUTIVE ENTRIES OF THE TWO-VERTEX CLOSED WALK ARE ADJACENT.**  In the bulk of the walk this
is the adjacency of the cycle; at the three joints it is the three given edges. -/
theorem arcFun2_adj {m e : ℕ} (_he : e < m) (f : Fin m → V) (i : Fin m) (x y : V)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hxy : G.Adj x y) (hYi : G.Adj y (f i))
    (hXe : G.Adj (f ((cycSucc^[e] : Fin m → Fin m) i)) x) :
    ∀ j : Fin (e + 3),
      G.Adj (arcFun2 m e f i x y j) (arcFun2 m e f i x y (cycSucc j)) := by
  intro j
  have hcs : (cycSucc j).val = (j.val + 1) % (e + 3) := cycSucc_val j
  by_cases hj0 : j.val = 0
  · have hsucc : cycSucc j = ⟨1, by omega⟩ :=
      Fin.ext (by rw [hcs, hj0, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega))
    have hj : j = (0 : Fin (e + 3)) := Fin.ext hj0
    rw [hsucc, hj]
    rw [arcFun2_zero (m := m) (e := e) (f := f) (i := i) (x := x) (y := y),
      arcFun2_one (m := m) (e := e) (f := f) (i := i) (x := x) (y := y) (by omega)]
    exact hxy
  · by_cases hj1 : j.val = 1
    · have hsucc : cycSucc j = ⟨2, by omega⟩ :=
        Fin.ext (by rw [hcs, hj1]; exact Nat.mod_eq_of_lt (by omega))
      have hj : j = (⟨1, by omega⟩ : Fin (e + 3)) := Fin.ext hj1
      rw [hsucc, hj]
      rw [show arcFun2 m e f i x y ⟨1, _⟩ = y by simp [arcFun2]]
      rw [show arcFun2 m e f i x y ⟨2, _⟩ = f i by simp [arcFun2]]
      exact hYi
    · by_cases hjl : j.val + 1 = e + 3
      · have hsucc : cycSucc j = (0 : Fin (e + 3)) :=
          Fin.ext (by rw [hcs, hjl, Nat.mod_self]; rfl)
        have hkey : j.val - 2 = e := by omega
        rw [show arcFun2 m e f i x y j = f ((cycSucc^[e] : Fin m → Fin m) i) by
          simp [arcFun2, hj0, hj1, hkey]]
        rw [hsucc]
        rw [show arcFun2 m e f i x y 0 = x by simp [arcFun2]]
        exact hXe
      · have hjlt : j.val + 1 < e + 3 := by omega
        have hsuccv : (cycSucc j).val = j.val + 1 := by rw [hcs, Nat.mod_eq_of_lt hjlt]
        have hkey : j.val + 1 - 2 = j.val - 1 := by
          calc j.val + 1 - 2 = (j.val + 1 - 1) - 1 :=
              (Nat.sub_succ (n := j.val + 1) (m := 1)).symm
            _ = j.val - 1 := by rw [Nat.succ_sub_one j.val]
        rw [show arcFun2 m e f i x y j = f ((cycSucc^[j.val - 2] : Fin m → Fin m) i) by
          simp [arcFun2, hj0, hj1]]
        have hmod : (j.val + 1) % (e + 3) = j.val + 1 := Nat.mod_eq_of_lt hjlt
        rw [show arcFun2 m e f i x y (cycSucc j)
            = f ((cycSucc^[j.val - 1] : Fin m → Fin m) i) by
          simp [arcFun2, hmod, hkey, hj0]]
        have hstep : ((cycSucc^[j.val - 1] : Fin m → Fin m) i)
            = cycSucc ((cycSucc^[j.val - 2] : Fin m → Fin m) i) := by
          have h := Function.iterate_succ_apply' cycSucc (j.val - 2) i
          have hpos : 2 ≤ j.val := by omega
          have heq : ((j.val - 2 : ℕ).succ) = j.val - 1 := by
            have h1 : j.val = (j.val - 2) + 2 := (Nat.sub_add_cancel hpos).symm
            rw [h1, Nat.add_sub_cancel]
            omega
          rw [heq] at h
          exact h
        rw [hstep]
        exact hcyc ((cycSucc^[j.val - 2] : Fin m → Fin m) i)

/-- **CARDINALITY OF THE TWO-VERTEX CYCLE.** -/
theorem arc_card2 {m e : ℕ} (he : e < m) (f : Fin m → V) (hinj : Function.Injective f)
    (i : Fin m) (x y : V) (hxy : x ≠ y) (hximg : ∀ j : Fin m, f j ≠ x)
    (hyimg : ∀ j : Fin m, f j ≠ y) :
    ((Finset.univ : Finset (Fin (e + 3))).image (arcFun2 m e f i x y)).card = e + 3 := by
  have hinjarc : Function.Injective (arcFun2 m e f i x y) := by
    intro a b hab
    by_contra hne
    exact False.elim (arcFun2_ne he f hinj i x y hxy hximg hyimg hne hab)
  rw [Finset.card_image_of_injective _ hinjarc]
  simp

/-- **CLOSING AN EVEN ARC THROUGH TWO ADJACENT OUTSIDE VERTICES GIVES A SIMPLE ODD CYCLE OF
EXACTLY `e + 3` VERTICES** — the two-vertex analogue of `JSP90.arc_isOddCycle`, and the second
parity core of the classical fan argument. -/
theorem arc2_isOddCycle {m e : ℕ} {C : Finset V} (hm : m % 2 = 1) (hm3 : 3 ≤ m)
    (he : e < m) (he0 : 0 < e) (heven : e % 2 = 0)
    (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {i : Fin m} {x y : V} (hxy : x ≠ y)
    (hxC : x ∉ C) (hyC : y ∉ C) (hxy' : G.Adj x y) (hYi : G.Adj y (f i))
    (hXe : G.Adj (f ((cycSucc^[e] : Fin m → Fin m) i)) x) :
    IsOddCycle G ((Finset.univ : Finset (Fin (e + 3))).image (arcFun2 m e f i x y)) := by
  have hmod : (e + 3) % 2 = 1 := by
    rw [← Nat.mod_add_mod e 2 3, heven]
  have hximg : ∀ j : Fin m, f j ≠ x := by
    intro j hj
    have hfj : f j ∈ C := (hCmem (f j)).mpr ⟨j, rfl⟩
    rw [hj] at hfj
    exact hxC hfj
  have hyimg : ∀ j : Fin m, f j ≠ y := by
    intro j hj
    have hfj : f j ∈ C := (hCmem (f j)).mpr ⟨j, rfl⟩
    rw [hj] at hfj
    exact hyC hfj
  have hinjarc : Function.Injective (arcFun2 m e f i x y) := by
    intro a b hab
    by_contra hne
    exact False.elim (arcFun2_ne he f hinj i x y hxy hximg hyimg hne hab)
  refine ⟨e + 3, arcFun2 m e f i x y, hmod, by omega, hinjarc, ?_, ?_⟩
  · exact arcFun2_adj he f i x y hcyc hxy' hYi hXe
  · intro y
    constructor
    · intro hy
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hy
      exact ⟨j, hj⟩
    · rintro ⟨j, rfl⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- **THE "NO SHORT CUT" LEMMA.**  Two distinct vertices outside a *shortest* odd cycle, adjacent to
each other, with attachment points `f i` and `f (cycSucc^[d] i)`: the arc between their attachment
points has length `d ≤ 3` or `d ≥ m - 3`.  Equivalently: **two fan vertices whose attachment
points are far apart around the cycle are never adjacent.** -/
theorem not_adj_fan_of_far_attach {m d : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {i j : Fin m} (hdm : d < m) (hd0 : 0 < d)
    (hdij : ((cycSucc^[d] : Fin m → Fin m) i = j)) {x y : V} (hxy : x ≠ y) (hxC : x ∉ C)
    (hyC : y ∉ C) (hxy' : G.Adj x y) (hxi : G.Adj x (f i)) (hyj : G.Adj y (f j)) :
    d ≤ 3 ∨ m - 3 ≤ d := by
  have hcard : C.card = m := card_eq_cyclicOrder f hinj hCmem
  have hximg : ∀ k : Fin m, f k ≠ x := by
    intro k hk
    have hfk : f k ∈ C := (hCmem (f k)).mpr ⟨k, rfl⟩
    rw [hk] at hfk
    exact hxC hfk
  have hyimg : ∀ k : Fin m, f k ≠ y := by
    intro k hk
    have hfk : f k ∈ C := (hCmem (f k)).mpr ⟨k, rfl⟩
    rw [hk] at hfk
    exact hyC hfk
  by_cases hdodd : d % 2 = 1
  · -- the complement arc, of even length `m - d`, closed through `x` and `y`
    obtain ⟨heven, h2le⟩ := even_compl_of_odd hm hdodd hdm
    have hrev : ((cycSucc^[m - d] : Fin m → Fin m) j = i) := arc_rev hdm hdij
    have hXe' : G.Adj (f ((cycSucc^[m - d] : Fin m → Fin m) j)) x := by
      rw [hrev]
      exact hxi.symm
    have hD : IsOddCycle G ((Finset.univ : Finset (Fin (m - d + 3))).image
        (arcFun2 m (m - d) f j x y)) :=
      arc2_isOddCycle hm (by omega) (e := m - d) (by omega) (by omega) heven f hinj hcyc hCmem hxy
        hxC hyC hxy' hyj hXe'
    have hDcard : ((Finset.univ : Finset (Fin (m - d + 3))).image
        (arcFun2 m (m - d) f j x y)).card = m - d + 3 :=
      arc_card2 (by omega) f hinj j x y hxy hximg hyimg
    have hle' : C.card ≤ m - d + 3 := (hshort _ hD).trans_eq hDcard
    omega
  · -- the arc of length `d`, closed through `x` and `y`
    have hd_even : d % 2 = 0 := Nat.mod_two_eq_zero_or_one d |>.resolve_right hdodd
    have hXe' : G.Adj (f ((cycSucc^[d] : Fin m → Fin m) i)) y := by
      rw [hdij]
      exact hyj.symm
    have hD : IsOddCycle G ((Finset.univ : Finset (Fin (d + 3))).image
        (arcFun2 m d f i y x)) :=
      arc2_isOddCycle hm (by omega) (e := d) hdm hd0 hd_even f hinj hcyc hCmem hxy.symm hyC
        hxC hxy'.symm hxi hXe'
    have hDcard : ((Finset.univ : Finset (Fin (d + 3))).image
        (arcFun2 m d f i y x)).card = d + 3 :=
      arc_card2 hdm f hinj i y x hxy.symm hyimg hximg
    have hle' : C.card ≤ d + 3 := (hshort _ hD).trans_eq hDcard
    omega

/-- **THE "FAR FAN" FORM OF THE NO-SHORT-CUT LEMMA: two vertices outside a shortest odd cycle, each
adjacent to a vertex of the cycle, whose two attachment points are `4` to `m - 5` steps apart
along the cycle, are NOT adjacent.**  In words: at a shortest odd cycle, two fan vertices conflict
only if they are attached within three steps of each other.

Notice that no triangle-free hypothesis occurs: the lemma is a statement about shortest odd cycles
in *any* graph, and the "book, not web" picture of the fan needs `JSP90.not_adj_cycSucc_of_adj`
(round 69) on top of it. -/
theorem not_adj_of_attach_far {m d : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {i j : Fin m} (hdm : d < m) (hd0 : 0 < d)
    (hd4 : 4 ≤ d) (hd5 : d ≤ m - 5)
    (hdij : ((cycSucc^[d] : Fin m → Fin m) i = j)) {x y : V} (hxy : x ≠ y) (hxC : x ∉ C)
    (hyC : y ∉ C) (hxy' : G.Adj x y) (hxi : G.Adj x (f i)) (hyj : G.Adj y (f j)) : False := by
  have h := not_adj_fan_of_far_attach hshort hm hm3 f hinj hcyc hCmem hdm hd0 hdij hxy hxC hyC
    hxy' hxi hyj
  omega

end TwoVertexArc

end

end JSP90
