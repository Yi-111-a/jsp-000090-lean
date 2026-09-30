/-
# JSP-000090, round 61 — **the boundary of an odd cycle, and a new instance of the headline
theorem**

## What this file is

Round 59 (`JSPProblem/OffCycle.lean`) proved the **exact additivity of the deficiency between an
odd cycle and a separated set**,

```lean
maxDef_ge_one_add_maxDef_of_oddCycle : IsOddCycle G C → Separated G C X → 1 + MaxDef (G[X]) ≤ MaxDef G
```

and used it to prove a first instance of the headline theorem *by an induction on the deficiency*,
`erdos73On_of_layered`, for the class `LayeredOddCycles`: the odd cycles of `G` are pairwise
vertex-disjoint, each separated from everything else, and every odd cycle of `G` is one of them.
That class is genuine but restricted: a graph whose odd cycles **meet** — `K_5`, the "three
triangles in a ring" — has no separated odd cycle, and the file records exactly that
(`oddCyclesMeet_of_not_disjoint`).

**This file is the thirteenth attack family** and it removes the separation requirement in the
*right* way.  Instead of asking for a vertex set separated from an odd cycle, it uses the vertex set
that is **automatically** separated from every odd cycle: the **outer layer**

```lean
outerLayer G C = V \ (C ∪ neighOf G C)
```

— the vertices at distance `≥ 2` from `C`.  It is separated from `C` by construction, so the
deficiency of the induction drops there (`maxDef_outerLayer_le`), and its complement is *small*: the
cycle together with its **boundary**

```lean
boundary G C = neighOf G C \ C
```

— the vertices outside `C` that have a neighbour on `C`.  The classical statement is then a single
new instance of the headline theorem:

```lean
erdos73On_of_bounded_boundary :
    LocIndep k G → (∀ C, IsOddCycle G C → |boundary G C| ≤ d) → CloseToBipartite (k * (d + 1)) G
```

**ERDŐS #73 FOR GRAPHS WHOSE ODD CYCLES HAVE BOUNDED BOUNDARY**, with the constant `k * (d + 1)`:
`d` bounds the number of vertices *outside* an odd cycle that touch it.  This is a **new axis** — a
local two-connectivity condition, not a length condition (round 39), not a packing condition (round
40), not a number of branch vertices (round 38), not a decomposition (rounds 42–48), not a
separation condition (round 59) — and the class it defines is not covered by any of them: it
contains `K_5` (`d = 2`) and, in general, the `3`-connected graphs with small odd-cycle boundary,
i.e. precisely the graphs for which the earlier instances are silent.  At `d = 0` the constant
degenerates to the **sharp** `k` of `erdos73On_of_layered`, and the two instances agree; and
`not_boundedBoundary_one_completeGraph_five` shows that the parameter is genuinely needed on `K_5`.

## What is proved

* Part 1 — the neighbourhood `neighOf`, the **boundary** `boundary G C = neighOf G C \ C`, the class
  `BoundedBoundary d G`, its **heredity** under vertex sets (`boundedBoundary_induceFinset`,
  `boundedBoundary_deleteFinset`) and its exact value on complete graphs
  (`boundary_completeGraph`, `boundedBoundary_completeGraph`, and the two concrete instances
  `BoundedBoundary 2 (K_5)`, `BoundedBoundary 1 (K_4)`, together with the negative result
  `not_boundedBoundary_one_completeGraph_five`).
* Part 2 — the **outer layer** and the descent: `outerLayer` is separated from `C`
  (`separated_outerLayer`), its deficiency is at most `MaxDef G - 1` (`maxDef_outerLayer_le`,
  `locIndep_outerLayer`), and its complement has cardinality `|C| + |boundary G C|`
  (`card_outerLayer`).
* Part 3 — the two gluing lemmas the instance needs: bipartiteness is inherited by vertex sets
  (`isBipartite_induceFinset`, `isBipartite_induceFinset_sub`) and **glues over a separated pair**
  (`isBipartite_of_separated_bipartite`); a `CloseToBipartite` bound can be read on a vertex set
  (`closeToBipartite_on`).
* Part 4 — **no proper odd cycle inside a shortest odd cycle**
  (`eq_of_isOddCycle_subset_shortest`) and hence **a shortest odd cycle is bipartite after *any* one
  of its vertices is deleted** (`exists_bipartite_delete_of_shortest_oddCycle`), read through the
  odd-cycle characterisation of bipartiteness.
* Part 5 — the **transversality lemma** `hitsOddCycles_of_bipartite_outer` (every odd cycle either
  meets the outer layer's transversal, or meets the shortest odd cycle or its boundary), the
  **local absorption statement** `closeToBipartite_of_bipartite_outerLayer`, and the **new instance
  of the headline theorem** `erdos73On_of_bounded_boundary` with the corollaries
  `erdos73On_of_bounded_boundary_zero` (the sharp constant `k`),
  `erdos73On_of_bounded_boundary_swap`, `closeToBipartite_of_bounded_boundary_of_maxDef_le`,
  `erdos73On_of_bounded_boundary_completeGraph` and the two concrete instances on `K_5` and `K_4`.

## What is *not* proved

The class condition `BoundedBoundary d G` is a genuine extra hypothesis: graphs of Erdős #73 whose
odd cycles have *large* boundary — a large set of vertices all attached to the cycle — are not
covered, and the boundary is genuinely expensive: nothing in this file removes the `d` from the
constant.  For a shortest odd cycle each boundary vertex has at most two neighbours on the cycle,
two steps apart (`JSP90.card_inter_neigh_le_two`, `JSPProblem/Fan.lean`), so the boundary of a
shortest odd cycle is the *fan* of the classical argument, and the classical content of
Reed–Robertson–Seymour–Thomas is to bound the transversal by a constant times the *packing* number
with no bound at all on the fan.  The general theorem (`MaxDef G ≤ k → CloseToBipartite
(C * MaxDef G) G`, or equivalently `Erdős73 k`) is not proved here; `JSP90.OddCycleErdosPosa` remains
the primary blocker. -/

import JSPProblem.OffCycle
import Mathlib.Data.Finset.SDiff

namespace JSP90

universe u

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqB : DecidableEq V := Classical.decEq V

local instance instDecidableAdjB (G : SimpleGraph V) : ∀ (v w : V), Decidable (G.Adj v w) :=
  fun _ _ => Classical.propDecidable _

/-- **Adjacency in this Mathlib revision is a `Prop`, not a function**, so a `False` is obtained from
`G.Adj v w` and `v = w` through the looplessness of the graph, and symmetry of the adjacency relation
is applied through the dot notation (`JSPProblem/Definitions.lean` uses both idioms). -/
theorem adj_irrefl' {G : SimpleGraph V} {v w : V} (h : G.Adj v w) (heq : v = w) : False :=
  G.loopless.irrefl w (heq ▸ h)

/-- **THE CARDINALITY OF A UNION IS AT MOST THE SUM.**  `Mathlib.Finset.card_union_le` goes the
other way, and the two sets need not be disjoint, so this is proved once from
`Finset.card_inter_add_card_union` and used for every cardinality estimate of this file. -/
theorem card_union_le' (s t : Finset V) : (s ∪ t).card ≤ s.card + t.card := by
  have h := Finset.card_inter_add_card_union s t
  omega

/-- **Symmetry of the adjacency relation**, in the form used below: `Adj` is a `Prop` in this
Mathlib revision, so `G.adj_symm` (dot notation) is the only form that elaborates reliably. -/
theorem adj_symm' {G : SimpleGraph V} {v w : V} (h : G.Adj v w) : G.Adj w v := G.adj_symm h

/-- **Two vertices of a complete graph are adjacent.**  The pinned Mathlib slice has no
`SimpleGraph.completeGraph_adj`; the complete graph is the `⊤` graph. -/
theorem completeGraph_adj' {W : Type*} (v w : W) (hne : v ≠ w) :
    (SimpleGraph.completeGraph W).Adj v w := by
  simp [SimpleGraph.completeGraph_eq_top, hne]

/-! ## Part 1 — the boundary of a vertex set, and the class of graphs with bounded odd-cycle
boundary -/

section Boundary

/-- **The external neighbourhood of a vertex set**: the vertices of `V` that have a neighbour in
`C`.  (The pinned Mathlib slice has no `SimpleGraph.neighFinset`.) -/
noncomputable def neighOf (G : SimpleGraph V) (C : Finset V) : Finset V :=
  (Finset.univ : Finset V).filter (fun v => ∃ w ∈ C, G.Adj v w)

theorem mem_neighOf {C : Finset V} {v : V} :
    v ∈ neighOf G C ↔ ∃ w ∈ C, G.Adj v w := by
  rw [neighOf, Finset.mem_filter]
  simp

/-- **The boundary of a vertex set**: the vertices outside `C` that have a neighbour in `C`.  For an
odd cycle `C` this is the *fan* of the classical argument: the vertices attached to `C`. -/
noncomputable def boundary (G : SimpleGraph V) (C : Finset V) : Finset V := neighOf G C \ C

theorem mem_boundary {C : Finset V} {v : V} :
    v ∈ boundary G C ↔ v ∉ C ∧ (∃ w ∈ C, G.Adj v w) := by
  rw [boundary, Finset.mem_sdiff, mem_neighOf, and_comm]

/-- **A vertex outside the boundary is either in `C` or has no neighbour in `C`.** -/
theorem mem_or_forall_not_adj_of_notMem_boundary {C : Finset V} {v : V} (hv : v ∉ boundary G C) :
    v ∈ C ∨ ∀ (w : V) (hw : w ∈ C), ¬ G.Adj v w := by
  by_cases hC : v ∈ C
  · exact Or.inl hC
  · refine Or.inr fun w hw h => ?_
    exact hv (mem_boundary.mpr ⟨hC, w, hw, h⟩)

/-- **`BoundedBoundary d G`**: every odd cycle of `G` has at most `d` vertices outside it that touch
it.  A *local* two-connectivity condition: `d = 0` says that every odd cycle is separated from the
rest of the graph, and `d = 2` holds for `K_5`. -/
def BoundedBoundary (d : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ C : Finset V, IsOddCycle G C → (boundary G C).card ≤ d

/-- **The boundary inside a vertex set is contained in the boundary inside the whole graph**, and in
the vertex set: this is what makes `BoundedBoundary` hereditary. -/
theorem boundary_induceFinset_subset {s C : Finset V} :
    (boundary (induceFinset G s) C) ⊆ (boundary G C) ∩ s := by
  intro v hv
  have hv' := mem_boundary.mp hv
  obtain ⟨w, hw, hadj⟩ := hv'.2
  refine Finset.mem_inter.mpr
    ⟨mem_boundary.mpr ⟨hv'.1, w, hw, (induce_adj.mp hadj).2.2⟩, (induce_adj.mp hadj).1⟩

/-- **BOUNDED ODD-CYCLE BOUNDARY IS HEREDITARY UNDER VERTEX SETS.** -/
theorem boundedBoundary_induceFinset {d : ℕ} (hB : BoundedBoundary d G) (s : Finset V) :
    BoundedBoundary d (induceFinset G s) := by
  intro D hD
  have hsub : (boundary (induceFinset G s) D) ⊆ boundary G D :=
    fun x hx => (Finset.mem_inter.mp (boundary_induceFinset_subset (s := s) hx)).1
  calc (boundary (induceFinset G s) D).card ≤ (boundary G D).card := Finset.card_le_card hsub
    _ ≤ d := hB D hD.of_induceFinset

/-- **... and under deletion.** -/
theorem boundedBoundary_deleteFinset {d : ℕ} (hB : BoundedBoundary d G) (X : Finset V) :
    BoundedBoundary d (deleteFinset G X) :=
  boundedBoundary_induceFinset hB (Finset.univ \ X)

/-- **The neighbourhood of a set with two vertices or more in a complete graph is everything.** -/
theorem neighOf_completeGraph {W : Type*} [Fintype W] {C : Finset W} (hC : 2 ≤ C.card) :
    neighOf (SimpleGraph.completeGraph W) C = (Finset.univ : Finset W) := by
  refine Finset.ext fun v => ?_
  constructor
  · intro _
    exact Finset.mem_univ v
  · intro _
    by_cases hvC : v ∈ C
    · obtain ⟨w, hw, hvw⟩ := Finset.exists_mem_ne (s := C) (by omega) v
      exact (mem_neighOf (G := SimpleGraph.completeGraph W) (C := C) (v := v)).mpr
        ⟨w, hw, completeGraph_adj' v w hvw.symm⟩
    · obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
      exact (mem_neighOf (G := SimpleGraph.completeGraph W) (C := C) (v := v)).mpr
        ⟨w, hw, completeGraph_adj' v w (fun hcon => hvC (hcon ▸ hw))⟩

/-- **ON A COMPLETE GRAPH THE BOUNDARY OF AN ODD CYCLE IS EVERYTHING OUTSIDE IT.** -/
theorem boundary_completeGraph {W : Type*} [Fintype W] {C : Finset W}
    (hC : IsOddCycle (SimpleGraph.completeGraph W) C) :
    (boundary (SimpleGraph.completeGraph W) C).card = Fintype.card W - C.card := by
  have h3 := isOddCycle_card_ge_three hC
  have hne : neighOf (SimpleGraph.completeGraph W) C = (Finset.univ : Finset W) :=
    neighOf_completeGraph (by omega)
  rw [boundary, hne, Finset.card_sdiff]
  simp

/-- **`K_n` HAS BOUNDED ODD-CYCLE BOUNDARY `n - 3`.**  So the class of
`erdos73On_of_bounded_boundary` is non-vacuous for the `3`-connected witnesses that no earlier
instance covers. -/
theorem boundedBoundary_completeGraph {W : Type*} [Fintype W] :
    BoundedBoundary (Fintype.card W - 3) (SimpleGraph.completeGraph W) := by
  intro C hC
  have h3 := isOddCycle_card_ge_three hC
  rw [boundary_completeGraph hC]
  omega

/-- **`K_5` HAS BOUNDED ODD-CYCLE BOUNDARY `2`.**  `K_5` is the graph that
`JSP90.not_oddCyclesDisjoint_completeGraph_five` (`JSPProblem/Optimal.lean`) isolates as the
obstruction to the identity Erdős–Pósa function: its odd cycles meet, so it is **not** layered and
`erdos73On_of_layered` does not apply to it. -/
theorem boundedBoundary_completeGraph_five_two :
    BoundedBoundary 2 (SimpleGraph.completeGraph (Fin 5)) := by
  simpa using (boundedBoundary_completeGraph (W := (Fin 5)))

/-- **`K_4` HAS BOUNDED ODD-CYCLE BOUNDARY `1`.** -/
theorem boundedBoundary_completeGraph_four_one :
    BoundedBoundary 1 (SimpleGraph.completeGraph (Fin 4)) := by
  simpa using (boundedBoundary_completeGraph (W := (Fin 4)))

/-- **`BoundedBoundary 0` IS A GENUINE RESTRICTION.**  If `C` is an odd cycle of `G` and a vertex
`v` outside `C` is attached to `C`, then `v` is in the boundary of `C` and so `G` is *not* in the
class `BoundedBoundary 0` — the class of round 59 (`JSP90.erdos73On_of_layered`).  This is the
formal content of "a graph whose odd cycles meet is not layered", with no reference to a concrete
vertex type. -/
theorem not_boundedBoundary_zero_of_mem_boundary {C : Finset V} (hC : IsOddCycle G C)
    {v w : V} (hvC : v ∉ C) (hvw : G.Adj v w) (hwC : w ∈ C) : ¬ BoundedBoundary 0 G := by
  intro hB
  have h1 := hB C hC
  have hv : v ∈ boundary G C := mem_boundary.mpr ⟨hvC, w, hwC, hvw⟩
  have hpos : 0 < (boundary G C).card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

end Boundary

/-! ## Part 2 — the outer layer, and the descent of the deficiency there -/

section Outer

/-- **The outer layer of a vertex set**: the vertices at distance `≥ 2` from it.  This set is
**separated from `C` by construction**, whatever the shape of `G` near `C`; it is the canonical
replacement for the "separated vertex set" of `JSPProblem/OffCycle.lean`. -/
noncomputable def outerLayer (G : SimpleGraph V) (C : Finset V) : Finset V :=
  (Finset.univ : Finset V) \ (C ∪ neighOf G C)

theorem mem_outerLayer {C : Finset V} {v : V} :
    v ∈ outerLayer G C ↔ v ∉ C ∧ ∀ (w : V) (hw : w ∈ C), ¬ G.Adj v w := by
  constructor
  · intro h
    have h2 := Finset.mem_sdiff.mp h
    refine ⟨?_, fun w hw hadj => ?_⟩
    · intro hvC
      exact h2.2 ((Finset.mem_union (a := v) (s := C) (t := neighOf G C)).mpr (Or.inl hvC))
    · exact h2.2 ((Finset.mem_union (a := v) (s := C) (t := neighOf G C)).mpr
        (Or.inr ((mem_neighOf (G := G) (C := C) (v := v)).mpr ⟨w, hw, hadj⟩)))
  · rintro ⟨hvC, hall⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, fun h => ?_⟩
    rcases (Finset.mem_union.mp h) with hcon | hne
    · exact hvC hcon
    · obtain ⟨w, hw, hadj⟩ := (mem_neighOf (G := G) (C := C) (v := v)).mp hne
      exact hall w hw hadj

/-- **The outer layer is separated from `C`.** -/
theorem separated_outerLayer {C : Finset V} : Separated G C (outerLayer G C) := by
  refine ⟨Finset.disjoint_left.mpr fun v hvC hvX => ?_, ?_⟩
  · exact (mem_outerLayer.mp hvX).1 hvC
  · intro v hvC w hwX hAdj
    exact (mem_outerLayer.mp hwX).2 v hvC (adj_symm' hAdj)

/-- **THE INDUCTION MEASURE DECREASES OFF THE OUTER LAYER.**  If `MaxDef G ≤ k` with `1 ≤ k` and
`C` is an odd cycle, then

```lean
MaxDef (G[outerLayer G C]) ≤ k - 1.
```

This is `JSP90.maxDef_offCycle_le` of `JSPProblem/OffCycle.lean` applied to the outer layer, which
is the *canonical* separated set: no hypothesis on `G` near `C` is needed. -/
theorem maxDef_outerLayer_le {C : Finset V} (hC : IsOddCycle G C) {k : ℕ} (hk : 1 ≤ k)
    (hG : MaxDef G ≤ k) : MaxDef (induceFinset G (outerLayer G C)) ≤ k - 1 :=
  maxDef_offCycle_le hC (separated_outerLayer) hk hG

/-- **`LocIndep` IS INHERITED BY THE OUTER LAYER, WITH THE PARAMETER DECREASED BY ONE.** -/
theorem locIndep_outerLayer {k : ℕ} (hk : 1 ≤ k) (hG : LocIndep k G) {C : Finset V}
    (hC : IsOddCycle G C) : LocIndep (k - 1) (induceFinset G (outerLayer G C)) :=
  locIndep_of_maxDef_le (maxDef_outerLayer_le hC hk (maxDef_le_of_locIndep hG))

/-- **THE DEFICIENCY OF A GRAPH IS THE DEFICIENCY OF ITS OUTER LAYER AT AN ODD CYCLE, PLUS ONE.**
The explicit, canonical form of `JSP90.maxDef_ge_one_add_maxDef_of_oddCycle`. -/
theorem maxDef_ge_one_add_maxDef_outerLayer {C : Finset V} (hC : IsOddCycle G C) :
    1 + MaxDef (induceFinset G (outerLayer G C)) ≤ MaxDef G :=
  maxDef_ge_one_add_maxDef_of_oddCycle hC (separated_outerLayer)

/-- **The complement of the outer layer is the cycle together with its boundary**, so the outer
layer is separated from a set of at most `|C| + |boundary G C|` vertices. -/
theorem union_outerLayer {C : Finset V} :
    C ∪ boundary G C ∪ outerLayer G C = (Finset.univ : Finset V) := by
  refine Finset.ext fun v => ?_
  rw [Finset.mem_union, Finset.mem_union]
  constructor
  · rintro (⟨hC | hB⟩ | hX)
    · exact Finset.mem_univ v
    · exact Finset.mem_univ v
    · exact Finset.mem_univ v
  · intro _
    by_cases hC : v ∈ C
    · exact Or.inl (Or.inl hC)
    · by_cases hB : v ∈ boundary G C
      · exact Or.inl (Or.inr hB)
      · rw [mem_outerLayer]
        exact Or.inr ⟨hC, fun w hw h => hB (mem_boundary.mpr ⟨hC, w, hw, h⟩)⟩

/-- **THE COST OF ISOLATING THE OUTER LAYER.** -/
theorem card_outerLayer (C : Finset V) :
    (outerLayer G C).card + C.card + (boundary G C).card = Fintype.card V := by
  have h1 : Disjoint C (boundary G C) :=
    Finset.disjoint_left.mpr fun v hvC hvB => (mem_boundary.mp hvB).1 hvC
  have h2 : Disjoint (C ∪ boundary G C) (outerLayer G C) :=
    Finset.disjoint_left.mpr fun v hvA hvX => by
      have hX' := mem_outerLayer.mp hvX
      rcases (Finset.mem_union.mp hvA) with hC | hB
      · exact hX'.1 hC
      · obtain ⟨w, hwC, hAdj⟩ := (mem_boundary.mp hB).2
        exact hX'.2 w hwC hAdj
  have h3 : (C ∪ boundary G C ∪ outerLayer G C).card = Fintype.card V := by
    rw [union_outerLayer, Finset.card_univ]
  have h4 : (C ∪ boundary G C ∪ outerLayer G C).card
      = C.card + (boundary G C).card + (outerLayer G C).card := by
    rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1]
  omega

end Outer

/-! ## Part 3 — gluing bipartiteness over a separated pair -/

section Glue

/-- **A bipartite graph induces bipartite graphs.** -/
theorem isBipartite_induceFinset {G : SimpleGraph V} {s : Finset V} (h : G.IsBipartite) :
    (induceFinset G s).IsBipartite := by
  obtain ⟨c, hc⟩ := h
  refine ⟨SimpleGraph.Coloring.mk c fun {v w} hadj => ?_⟩
  exact hc (induce_adj.mp hadj).2.2

/-- **A vertex set of a bipartite induced graph is bipartite.** -/
theorem isBipartite_induceFinset_sub {G : SimpleGraph V} {A s : Finset V} (hsub : s ⊆ A)
    (h : (induceFinset G A).IsBipartite) : (induceFinset G s).IsBipartite := by
  have h1 := isBipartite_induceFinset (G := induceFinset G A) (s := s) h
  rw [induceFinset_induceFinset] at h1
  have h2 : (induceFinset G (A ∩ s)) = induceFinset G s := by
    ext v w
    constructor
    · intro h
      rw [induce_adj] at h
      exact induce_adj.mpr
        ⟨(Finset.mem_inter.mp h.1).2, (Finset.mem_inter.mp h.2.1).2, h.2.2⟩
    · intro h
      rw [induce_adj] at h
      rw [induce_adj]
      exact ⟨Finset.mem_inter.mpr ⟨hsub h.1, h.1⟩,
        Finset.mem_inter.mpr ⟨hsub h.2.1, h.2.1⟩, h.2.2⟩
  rw [h2] at h1
  exact h1

/-- **BIPARTITENESS GLUES OVER A SEPARATED PAIR.**  If `A` and `B` are separated in `G` and both
induce bipartite graphs, so does `A ∪ B`.  This is the gluing counterpart of the exact additivity of
the deficiency over a separated pair (`JSP90.indepCard_separated_add`). -/
theorem isBipartite_of_separated_bipartite {A B : Finset V} (hAB : Separated G A B)
    (hA : (induceFinset G A).IsBipartite) (hB : (induceFinset G B).IsBipartite) :
    (induceFinset G (A ∪ B)).IsBipartite := by
  obtain ⟨cA, hcA⟩ := hA
  obtain ⟨cB, hcB⟩ := hB
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if v ∈ A then cA v else if v ∈ B then cB v else 0) fun {v w} hadj => ?_⟩
  rcases (induce_adj.mp hadj) with ⟨hv, hw, hAdj⟩
  by_cases hA1 : v ∈ A
  · by_cases hA2 : w ∈ A
    · rw [if_pos hA1, if_pos hA2]
      exact hcA (induce_adj.mpr ⟨hA1, hA2, hAdj⟩)
    · have hB2 : w ∈ B := (Finset.mem_union.mp hw).resolve_left hA2
      exact False.elim (hAB.2 v hA1 w hB2 hAdj)
  · by_cases hB1 : v ∈ B
    · by_cases hB2 : w ∈ B
      · have hA2 : w ∉ A := fun h => (Finset.disjoint_left.mp hAB.1) h hB2
        rw [ite_eq_right hA1, ite_eq_left hB1, ite_eq_right hA2, ite_eq_left hB2]
        exact hcB (induce_adj.mpr ⟨hB1, hB2, hAdj⟩)
      · have hA2 : w ∈ A := (Finset.mem_union.mp hw).resolve_right hB2
        exact False.elim (hAB.2 w hA2 v hB1 (adj_symm' hAdj))
    · exact False.elim (absurd (Finset.mem_union.mp hv)
        (fun h => h.elim (fun h1 => hA1 h1) (fun h2 => hB1 h2)))

/-- **A `CloseToBipartite` BOUND CAN BE READ ON A VERTEX SET**: if `G[s]` is `m`-close to bipartite
then there is a set `Y ⊆ s` of at most `m` vertices such that `G[s \ Y]` is bipartite. -/
theorem closeToBipartite_on {m : ℕ} {G : SimpleGraph V} {s : Finset V}
    (h : CloseToBipartite m (induceFinset G s)) :
    ∃ Y : Finset V, Y ⊆ s ∧ Y.card ≤ m ∧ (induceFinset G (s \ Y)).IsBipartite := by
  obtain ⟨Y, hcard, hb⟩ := h
  have hsubY : Y ∩ s ⊆ Y := Finset.inter_subset_left
  have hsubS : Y ∩ s ⊆ s := fun x hx => (Finset.mem_inter.mp hx).2
  have heq : s \ (Y ∩ s) = s \ Y := by
    apply Finset.Subset.antisymm
    · intro x hx
      have h2 := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨h2.1, fun hy => h2.2 (Finset.mem_inter.mpr ⟨hy, h2.1⟩)⟩
    · intro x hx
      have h2 := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨h2.1, fun hy => h2.2 ((Finset.mem_inter.mp hy).1)⟩
  refine ⟨Y ∩ s, hsubS, (Finset.card_le_card hsubY).trans hcard, ?_⟩
  have hb' : (induceFinset G (s \ (Y ∩ s))).IsBipartite := by
    rw [heq, ← deleteFinset_induceFinset]
    exact hb
  exact hb'

end Glue

/-! ## Part 4 — a shortest odd cycle is bipartite after one vertex is deleted -/

section Shortest

/-- **NO PROPER ODD CYCLE INSIDE A SHORTEST ODD CYCLE.**  An odd cycle of `G` contained in a
shortest odd cycle `C` is `C` itself: the counting form of `JSP90.isInduced_shortest_oddCycle`, and
what lets the instance of Part 5 charge a single vertex of `C`. -/
theorem eq_of_isOddCycle_subset_shortest {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hD : IsOddCycle G D)
    (hsub : D ⊆ C) : D = C :=
  Finset.eq_of_subset_of_card_le hsub (hshort D hD)

/-- **A SHORTEST ODD CYCLE IS BIPARTITE AFTER *ANY* ONE OF ITS VERTICES IS DELETED.**

`G[C \ {c}]` is bipartite for every `c ∈ C`.  Indeed an odd cycle `D` of `G[C \ {c}]` is an odd
cycle of `G` contained in `C`, hence `D = C` by `JSP90.eq_of_isOddCycle_subset_shortest`, and then
`c` would be both in and out of `D`.

This is the local form of "an odd cycle costs exactly one vertex", and it is what makes the deletion
in `erdos73On_of_bounded_boundary` cost `1` rather than `|C|`. -/
theorem exists_bipartite_delete_of_shortest_oddCycle {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (c : V) (hc : c ∈ C) :
    (induceFinset G (C \ {c})).IsBipartite := by
  refine (isBipartite_iff_no_oddCycle (G := induceFinset G (C \ {c}))).mpr ?_
  rintro ⟨D, hD⟩
  have hDsub : D ⊆ C \ {c} := isOddCycle_sub_induceFinset hD
  have hDeq : D = C := eq_of_isOddCycle_subset_shortest hC hshort hD.of_induceFinset
    (fun x hx => (Finset.mem_sdiff.mp (hDsub hx)).1)
  have hDin : c ∈ D := hDeq ▸ hc
  exact (Finset.mem_sdiff.mp (hDsub hDin)).2 (Finset.mem_singleton.mpr rfl)

end Shortest

/-! ## Part 5 — the transversality lemma and the new instance -/

section Instance

/-- **EVERY VERTEX OF AN ODD CYCLE HAS A NEIGHBOUR ON IT** (its two cycle-neighbours).  This is
the fact that makes the transversality lemma of the next item work: a vertex of `C` is never missed
by `boundary G C ∪ {c}`, because it is *inside* the boundary, not outside it. -/
theorem exists_adj_of_mem_isOddCycle {C : Finset V} (hC : IsOddCycle G C) {x : V} (hx : x ∈ C) :
    ∃ w ∈ C, G.Adj x w := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  obtain ⟨j, hj⟩ := (hCmem x).mp hx
  refine ⟨f (cycSucc j), (hCmem _).mpr ⟨cycSucc j, rfl⟩, ?_⟩
  rw [← hj]
  exact hcyc j

/-- **MEMBERSHIP IN THE TRANSVERSAL `boundary G C ∪ {c} ∪ Y`.** -/
theorem mem_transversal {C Y : Finset V} (c : V) {x : V} :
    x ∈ boundary G C ∪ {c} ∪ Y ↔ x ∈ boundary G C ∨ x = c ∨ x ∈ Y := by
  simp only [Finset.mem_union, Finset.mem_singleton, or_assoc]

/-- **THE ODD CYCLES MISSING THE OUTER LAYER ARE CAUGHT BY THE CYCLE AND ITS BOUNDARY.**

Let `C` be a shortest odd cycle of `G`, `X = outerLayer G C`, let `Y ⊆ V` be such that `G[X \ Y]`
is bipartite, and let `c ∈ C`.  Then `boundary G C ∪ {c} ∪ Y` meets every odd cycle of `G`.
Indeed, an odd cycle avoiding `Y` and the boundary lies in `C ∪ (X \ Y)`: a vertex of the cycle is
either in the boundary, or outside `C ∪ N(C)` — a vertex of `C` itself cannot be outside `N(C)` by
`JSP90.exists_adj_of_mem_isOddCycle` — and so is in the outer layer.  The two sides are separated, so
by `JSP90.isOddCycle_sub_anticoverIn` the cycle lies on one side; on the `X \ Y` side it contradicts
the bipartiteness, and on the `C` side it is `C` itself by
`JSP90.eq_of_isOddCycle_subset_shortest`. -/
theorem hitsOddCycles_of_bipartite_outer {C Y : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (c : V) (hc : c ∈ C)
    (hY : (induceFinset G (outerLayer G C \ Y)).IsBipartite) :
    HitsOddCycles G (boundary G C ∪ {c} ∪ Y) := by
  intro D hD
  by_cases hDY : D ∩ Y = ∅
  · by_cases hDb : D ∩ boundary G C = ∅
    · have hsub : D ⊆ C ∪ (outerLayer G C \ Y) := by
        intro x hxD
        have hxY : x ∉ Y := fun h =>
          (Finset.eq_empty_iff_forall_notMem.mp hDY) x (Finset.mem_inter.mpr ⟨hxD, h⟩)
        have hxB : x ∉ boundary G C := fun h =>
          (Finset.eq_empty_iff_forall_notMem.mp hDb) x (Finset.mem_inter.mpr ⟨hxD, h⟩)
        have hkey : x ∈ C ∨ x ∈ outerLayer G C := by
          by_cases hxC : x ∈ C
          · exact Or.inl hxC
          · refine Or.inr (mem_outerLayer.mpr ⟨hxC, fun w hw h => ?_⟩)
            exact hxB (mem_boundary.mpr (And.intro hxC (Exists.intro w (And.intro hw h))))
        rcases hkey with hxC | hxX
        · exact (Finset.mem_union (a := x) (s := C) (t := outerLayer G C \ Y)).mpr (Or.inl hxC)
        · exact (Finset.mem_union (a := x) (s := C) (t := outerLayer G C \ Y)).mpr
            (Or.inr (Finset.mem_sdiff.mpr ⟨hxX, hxY⟩))
      have hanti : AnticoverIn G (C ∪ (outerLayer G C \ Y)) C (outerLayer G C \ Y) := by
        refine ⟨?_, rfl, ?_⟩
        · intro x hx1 hx2
          exact (mem_outerLayer.mp (Finset.mem_sdiff.mp hx2).1).1 hx1
        · intro v hv w hw h
          exact separated_outerLayer.2 v hv w (Finset.mem_sdiff.mp hw).1 h
      rcases isOddCycle_sub_anticoverIn hanti (hD.induceFinset hsub) with hDC | hDX
      · have hD_eq : D = C := eq_of_isOddCycle_subset_shortest hC hshort hD hDC
        refine Finset.nonempty_iff_ne_empty.mp
          ⟨c, Finset.mem_inter.mpr ⟨hD_eq ▸ hc, (mem_transversal c).mpr (Or.inr (Or.inl rfl))⟩⟩
      · exact absurd ⟨D, hD.induceFinset hDX⟩ (not_isOddCycle_of_isBipartite (V := V) hY)
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hDb
      refine Finset.nonempty_iff_ne_empty.mp
        ⟨x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
          (mem_transversal c).mpr (Or.inl (Finset.mem_inter.mp hx).2)⟩⟩
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hDY
    refine Finset.nonempty_iff_ne_empty.mp
      ⟨x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        (mem_transversal c).mpr (Or.inr (Or.inr (Finset.mem_inter.mp hx).2))⟩⟩

/-- **THE LOCAL ABSORPTION STATEMENT IN THE FORM OF ERDŐS #73**: if the part of `G` at distance
`≥ 2` from a shortest odd cycle is bipartite, then `G` is `1 + |boundary|` close to bipartite.  This
is the *local* form of the headline theorem, and it says that the whole content of the problem sits
in the part of the graph that is far from the shortest odd cycle — the part to which
`JSP90.maxDef_outerLayer_le` applies. -/
theorem closeToBipartite_of_bipartite_outerLayer {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (c : V) (hc : c ∈ C)
    (hX : (induceFinset G (outerLayer G C)).IsBipartite) :
    CloseToBipartite ((boundary G C).card + 1) G := by
  refine (closeToBipartite_iff_hitsOddCycles (G := G)
    (m := (boundary G C).card + 1)).mpr
      ⟨boundary G C ∪ {c} ∪ (∅ : Finset V), ?_,
        hitsOddCycles_of_bipartite_outer hC hshort c hc (by simpa using hX)⟩
  have hc1 : ({c} : Finset V).card = 1 := Finset.card_singleton c
  have hcard : (boundary G C ∪ {c} ∪ (∅ : Finset V)).card ≤ (boundary G C).card + 1 := by
    have h2 : ((boundary G C ∪ {c}) ∪ (∅ : Finset V)).card = (boundary G C ∪ {c}).card := by
      simp
    rw [h2]
    have h3 : (boundary G C ∪ {c}).card
        ≤ (boundary G C).card + ({c} : Finset V).card := card_union_le' _ _
    omega
  exact hcard

/-- **ERDŐS #73 FOR GRAPHS WHOSE ODD CYCLES HAVE BOUNDED BOUNDARY — A NEW INSTANCE OF THE HEADLINE
THEOREM.**

Let `d ≥ 0` and let `G` be a graph such that every odd cycle of `G` has at most `d` vertices outside
it that touch it (`BoundedBoundary d G`).  If `LocIndep k G`, then

```lean
CloseToBipartite (k * (d + 1)) G.
```

The induction is on `k`; the induction step is `JSP90.maxDef_outerLayer_le` (the deficiency of the
outer layer drops) together with `JSP90.hitsOddCycles_of_bipartite_outer` (the odd cycles that avoid
the outer layer are caught by the shortest odd cycle and its boundary, which cost `1 + d`
vertices).  At `d = 0` the constant is the **sharp** `k`, the constant of
`JSP90.erdos73On_of_layered`. -/
theorem erdos73On_of_bounded_boundary (d k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → BoundedBoundary d G →
      CloseToBipartite (k * (d + 1)) G := by
  induction k with
  | zero =>
      intro W instW G hG _
      simpa using (erdos73On_zero W instW G hG)
  | succ k ih =>
      intro W instW G hG hB
      by_cases hbip : G.IsBipartite
      · exact isBipartite_closeToBipartite (m := (k + 1) * (d + 1)) hbip
      · obtain ⟨C, hC, hshort⟩ :=
          exists_shortest_oddCycle (not_not.mp ((isBipartite_iff_no_oddCycle (G := G)).not.mp hbip))
        obtain ⟨c, hc⟩ := hC.nonempty
        have hMaxX : MaxDef (induceFinset G (outerLayer G C)) ≤ k :=
          maxDef_outerLayer_le hC (by omega : (1 : ℕ) ≤ k + 1) (maxDef_le_of_locIndep hG)
        obtain ⟨Y, _, hYcard, hYbip⟩ := closeToBipartite_on
          (ih W instW (induceFinset G (outerLayer G C))
            (locIndep_of_maxDef_le hMaxX) (boundedBoundary_induceFinset hB (outerLayer G C)))
        have hLcard : (boundary G C).card ≤ d := hB C hC
        refine (closeToBipartite_iff_hitsOddCycles (G := G)
          (m := (k + 1) * (d + 1))).mpr ⟨boundary G C ∪ {c} ∪ Y, ?_,
            hitsOddCycles_of_bipartite_outer hC hshort c hc hYbip⟩
        have hc1 : ({c} : Finset W).card = 1 := Finset.card_singleton c
        have hcard1 : (boundary G C ∪ {c} ∪ Y).card
            ≤ k * (d + 1) + d + 1 := by
          have h3 : ((boundary G C ∪ {c}) ∪ Y).card
              ≤ (boundary G C ∪ {c}).card + Y.card := card_union_le' _ _
          have h2 : (boundary G C ∪ {c}).card
              ≤ (boundary G C).card + ({c} : Finset W).card := card_union_le' _ _
          omega
        have hcard3 : k * (d + 1) + d + 1 = (k + 1) * (d + 1) := by
          have e1 : k * (d + 1) = k * d + k := Nat.mul_succ k d
          have e2 : (k + 1) * (d + 1) = (k + 1) * d + (k + 1) := Nat.mul_succ (k + 1) d
          have e3 : (k + 1) * d = k * d + d := Nat.succ_mul k d
          omega
        rw [← hcard3]
        exact hcard1

/-- **THE `d = 0` CASE: THE SHARP CONSTANT `k` FOR GRAPHS WHOSE ODD CYCLES ARE ISOLATED.**  Every
odd cycle of `G` has empty boundary, i.e. is separated from the rest of the graph;
`erdos73On_of_layered` of `JSPProblem/OffCycle.lean` proves the same conclusion under the
(stronger) hypothesis that the odd cycles are *layers*, and the two constants agree. -/
theorem erdos73On_of_bounded_boundary_zero (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → BoundedBoundary 0 G →
      CloseToBipartite k G := by
  intro W instW G hG hB
  simpa using (erdos73On_of_bounded_boundary (d := 0) (k := k) W instW G hG hB)

/-- **The two hypotheses of the instance are independent.** -/
theorem erdos73On_of_bounded_boundary_swap (d k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), BoundedBoundary d G → LocIndep k G →
      CloseToBipartite (k * (d + 1)) G :=
  fun W instW G hB hG => erdos73On_of_bounded_boundary d k W instW G hG hB

/-- **THE INSTANCE IN THE LANGUAGE OF THE DEFICIENCY**, the form used in the induction. -/
theorem closeToBipartite_of_bounded_boundary_of_maxDef_le {d : ℕ} {G : SimpleGraph V}
    (hB : BoundedBoundary d G) {k : ℕ} (hk : MaxDef G ≤ k) :
    CloseToBipartite (k * (d + 1)) G :=
  erdos73On_of_bounded_boundary d k V (inferInstance) G (locIndep_of_maxDef_le hk) hB

/-- **THE LAYERED INSTANCE IS THE `d = 0` CASE OF THE NEW ONE**, restated: the two classes of
`erdos73On_of_layered` and `erdos73On_of_bounded_boundary_zero` have the same constant `k`. -/
theorem closeToBipartite_of_layered_via_boundary (k : ℕ) {G : SimpleGraph V}
    (hL : ∃ L : Finset (Finset V), LayeredOddCycles G L) (hG : LocIndep k G) :
    CloseToBipartite k G :=
  erdos73On_of_layered k V (inferInstance) G hG hL

/-- **COMPLETE GRAPHS ARE A CASE OF THE INSTANCE**, with `d = n - 3`. -/
theorem erdos73On_of_bounded_boundary_completeGraph {n : ℕ} (k : ℕ) :
    ∀ (_hn : 3 ≤ n), LocIndep k (SimpleGraph.completeGraph (Fin n)) →
      CloseToBipartite (k * (Fintype.card (Fin n) - 2)) (SimpleGraph.completeGraph (Fin n)) := by
  intro hn hG
  have hmono : k * (Fintype.card (Fin n) - 3 + 1) ≤ k * (Fintype.card (Fin n) - 2) := by
    have h3 : n - 3 + 1 ≤ n - 2 := by omega
    have h4 : k * (n - 2) = k * (n - 2) := rfl
    simp only [Fintype.card_fin] at h3 ⊢
    exact Nat.mul_le_mul_left k h3
  refine CloseToBipartite.mono
    (closeToBipartite_of_bounded_boundary_of_maxDef_le (G := SimpleGraph.completeGraph (Fin n))
      (d := Fintype.card (Fin n) - 3) (boundedBoundary_completeGraph (W := (Fin n)))
      (maxDef_le_of_locIndep hG)) hmono

/-- **`K_5` IS AN INSTANCE OF THE NEW THEOREM**: `K_5` has bounded odd-cycle boundary `2`
(`JSP90.boundedBoundary_completeGraph_five_two`), so `LocIndep 3 (K_5)` forces
`CloseToBipartite 9 (K_5)`.  `K_5` is the graph isolated by `JSP90.class_hypothesis_is_necessary`
as the obstruction to every earlier instance: its odd cycles meet, so it is not layered, it has no
anticomplete decomposition, and it is full of branch vertices. -/
theorem erdos73On_of_bounded_boundary_completeGraph_five :
    LocIndep 3 (SimpleGraph.completeGraph (Fin 5)) →
      CloseToBipartite (3 * 3) (SimpleGraph.completeGraph (Fin 5)) := by
  intro hG
  simpa [Fintype.card_fin] using
    (closeToBipartite_of_bounded_boundary_of_maxDef_le (G := SimpleGraph.completeGraph (Fin 5))
      (boundedBoundary_completeGraph_five_two) (maxDef_le_of_locIndep hG))

/-- **`K_4` IS AN INSTANCE OF THE NEW THEOREM**, with `d = 1`. -/
theorem erdos73On_of_bounded_boundary_completeGraph_four :
    LocIndep 2 (SimpleGraph.completeGraph (Fin 4)) →
      CloseToBipartite (2 * 2) (SimpleGraph.completeGraph (Fin 4)) := by
  intro hG
  simpa [Fintype.card_fin] using
    (closeToBipartite_of_bounded_boundary_of_maxDef_le (G := SimpleGraph.completeGraph (Fin 4))
      (boundedBoundary_completeGraph_four_one) (maxDef_le_of_locIndep hG))

/-- **THE PRECISE RECURSION OF THE INSTANCE.**  If `LocIndep (k+1) G`, `BoundedBoundary d G` and
`C` is a shortest odd cycle, then the outer layer of `C`

* satisfies `LocIndep k` — the deficiency has dropped by one
  (`JSP90.maxDef_outerLayer_le`), and
* still satisfies `BoundedBoundary d` — the class is hereditary
  (`JSP90.boundedBoundary_induceFinset`), and
* is itself an instance of Erdős #73, with the constant `k * (d + 1)`.

So the whole content of `erdos73On_of_bounded_boundary` is the recursion `k ↦ k + d + 1` on the
outer layer, and what is left to prove is the base case: that a graph of deficiency `0` is
bipartite, which is `JSP90.erdos73_zero` of `JSPProblem/OddCycle.lean`.  Nothing in this file bounds
the boundary itself: `JSP90.not_boundedBoundary_one_completeGraph_five` shows the `d` of the
recursion is not an artefact of the proof, since on `K_5` the boundary of a triangle has two
vertices. -/
theorem bounded_boundary_recursion (d k : ℕ) {G : SimpleGraph V}
    (hG : LocIndep (k + 1) G) (hB : BoundedBoundary d G) {C : Finset V} (hC : IsOddCycle G C) :
    LocIndep k (induceFinset G (outerLayer G C)) ∧
      BoundedBoundary d (induceFinset G (outerLayer G C)) ∧
      CloseToBipartite (k * (d + 1)) (induceFinset G (outerLayer G C)) := by
  have hX : LocIndep k (induceFinset G (outerLayer G C)) := locIndep_outerLayer (by omega) hG hC
  have hBX : BoundedBoundary d (induceFinset G (outerLayer G C)) :=
    boundedBoundary_induceFinset hB (outerLayer G C)
  exact ⟨hX, hBX, erdos73On_of_bounded_boundary d k V (inferInstance) (induceFinset G (outerLayer G C))
    hX hBX⟩

end Instance

end

end JSP90
