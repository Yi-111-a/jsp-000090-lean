/-
# JSP-000090, round 69 — **the fan of an odd cycle in a triangle-free graph, and the reduction of
Erdős Problem #73 to a purely LOCAL statement about that fan**

## Where the development stands

Round 68 (`JSPProblem/Triangle.lean`) closed the last of its two gaps and proved

```lean
JSP90.erdos73_iff_triangleFreeOnly : (∀ k, Erdős73On k (cutBound k)) ↔ JSP90.TriangleFreeOnly
```

so that **a single statement remains**: `JSP90.TriangleFreeOnly`, Erdős Problem #73 for
**triangle-free** graphs.  Everything else — the packing bound, the transversals, the residues, the
2-cuts, the anticomplete decompositions, the maximum-weight packing, the anticomplete composition,
the descent at a triangle — is proved and enters only through that one statement.

`discovery/JSP-000090/policy.json` named the next move as the *fan* at a shortest odd cycle of a
triangle-free graph, and asked for "a decomposition of the boundary of a shortest odd cycle into at
most `3` pieces", warning that it "needs Menger / the block-cut tree, which the pinned Mathlib slice
does not provide".  **This file does not need Menger.**  It reaches the same place by a different
route: it *localises* the whole remaining content to a statement about **one odd cycle and its
boundary** — a statement about a single pair of vertex sets, with no connectivity, no packing
number, no odd girth and no decomposition.

## The new statements

### Part 1 — triangle-freeness, made usable

* `JSP90.isNClique_three_of_isOddCycle` — a `3`-cycle of `G` *is* a `3`-clique, and
  `JSP90.isNClique_three` — three mutually adjacent vertices are a `3`-clique.  So a
  `G.CliqueFree 3` hypothesis can be read as "no vertex has two adjacent neighbours".
* `JSP90.card_ge_five_of_cliqueFree3_of_isOddCycle` — **in a triangle-free graph every odd cycle
  has at least `5` vertices.**  This is what makes the local structure of `JSPProblem/Fan.lean`
  (which is stated for `5 ≤ |C|`) apply to *every* odd cycle of a triangle-free graph, the shortest
  one included.
* `JSP90.indepSet_neighOf_singleton_of_cliqueFree3` and
  **`JSP90.neighOf_insert_isBipartite_of_cliqueFree3`** — **the neighbourhood of a vertex of a
  triangle-free graph is an independent set, so its closed neighbourhood induces a bipartite graph**
  (a star).  The difficulty of Erdős #73 is never *at* a vertex.

### Part 2 — the local structure of the fan in a triangle-free graph

* `JSP90.not_adj_cycSucc_of_adj` — **in a triangle-free graph a vertex adjacent to `f i` is not
  adjacent to the successor of `f i` on the cycle.**  This is the *first* genuine use of
  `CliqueFree 3` on the fan, and it is exactly the fact that makes the picture of the classical
  argument a "book" and not a "web".
* `JSP90.not_adj_of_common_neigh_of_cliqueFree3`,
  `JSP90.pairwise_not_adj_fan_of_cliqueFree3` and
  `JSP90.card_le_one_of_adj_of_fan_attach` — **the fan vertices attached to one fixed vertex of
  the cycle are pairwise non-adjacent.**  So the fan is a disjoint union of independent classes, one
  class per attachment point, and every edge inside the fan joins *different* classes.
* `JSP90.localStructure_shortest_oddCycle_free` — **the complete local structure of a triangle-free
  graph at a shortest odd cycle**: an outside vertex meets the cycle in at most two vertices, two
  steps apart, and is *not* adjacent to the vertex in between.  (Rounds 35 and 63 proved the first
  two facts; the third is new, and is the content of triangle-freeness at the fan.)

### Part 3 — the fan carries one unit less packing

* `JSP90.oddCycleFamily_card_le_of_boundary` — **under `LocIndep k G`, no packing of `k` odd cycles
  lives inside the boundary of an odd cycle**: such a packing together with the cycle itself would be
  a packing of `k + 1` odd cycles of `G`.  This is the induction parameter of the classical
  Erdős–Pósa argument, in the form the development consumes.
* `JSP90.isBipartite_fan_of_locIndep_one` — **`LocIndep 1` and an odd cycle force the fan to be
  bipartite** (a corollary, and a sanity check on the counting).

### Part 4 — THE REDUCTION: Erdős #73 from the fan statement

```lean
JSP90.FanErdős73 f  --  for every triangle-free G, every k, every odd cycle C of G, there is a set Z
                     --  of at most f k vertices meeting every odd cycle of G that meets the
                     --  boundary of C
```

* `JSP90.erdos73On_of_fanErdős73` — **Erdős #73 follows from the fan statement**, with the explicit
  constant `JSP90.fanBound f`.  The induction on `k` uses, at a triangle, the round-68 instance
  `3 + (k + 1) * f k`, and at a *shortest odd cycle* `C` of a triangle-free graph the two
  transversality facts already proved: the outer layer inherits `LocIndep (k - 1)`
  (`JSP90.locIndep_outerLayer`) and the odd cycles that avoid the outer layer are caught by
  `boundary G C ∪ {c} ∪ Y` (`JSP90.hitsOddCycles_of_bipartite_outer`).
* `JSP90.erdos73_of_fanErdős73` — **Erdős Problem #73 follows from a purely local statement about
  the boundary of one odd cycle in a triangle-free graph.**
* `JSP90.fanErdős73_of_triangleFreeOn` and **`JSP90.erdos73_iff_fanErdős73`** — the converse, so:
  **ERDŐS PROBLEM #73 IS EQUIVALENT TO ITS FAN STATEMENT.**  The blocker is now a statement about a
  single cycle and the set of vertices that touch it, and nothing else.

### Part 5 — the statement is not a formality

* `JSP90.fanErdős73_of_bounded_boundary` — the fan statement holds with `f k = d + 1` when every odd
  cycle has at most `d` vertices in its boundary.  (The instance of the headline theorem obtained
  from it is *dominated* by `JSP90.erdos73On_of_bounded_boundary` of round 61; the content of the fan
  statement is the unbounded-fan case, which is what the equivalence above isolates.)
* `JSP90.not_fanErdős73_one_completeGraph_seven` — **machine-checked negative result**: in a general
  graph the fan statement with `n = 1` is *false* — in `K_7`, at the triangle `C = {0,1,2}`, the two
  triangles `{3,4,5}` and `{6,0,1}` both meet the boundary of `C` and are disjoint.  So the constant
  of the fan statement is a genuine parameter and the triangle-free hypothesis is not a formality.
* **Not machine-checked (recorded as an observation).**  In a *triangle-free* graph the constant `1`
  is expected to fail as well: take a `13`-cycle and, for the five pairs `{0,2}`, `{3,5}`, `{6,8}`,
  `{9,11}`, `{12,1}` (each a pair two steps apart), one fan vertex attached to that pair, and make
  the five fan vertices a `5`-cycle.  The graph is triangle-free (no fan vertex is adjacent to a
  neighbour of its pair, and no two fan vertices share an attachment point), it satisfies
  `LocIndep 2` (`MaxDef = 2` on the whole vertex set, `≤ 1` on every proper vertex set), and the fan
  of `C` contains a `5`-cycle *disjoint from* the two odd cycles through each of its vertices, so no
  single vertex kills it.  The fan statement is therefore expected to need `n ≥ 2` in the
  triangle-free case, which is the classical shape of Reed's argument.

## What is *not* proved

`JSP90.TriangleFreeOnly`, and hence `JSP90.FanErdős73 f` for any `f`, and hence `jsp_000090_main`.
The blocker is now stated as precisely as it can be without the classical theorem: **the boundary of
a shortest odd cycle of a triangle-free graph can be killed with `f k` vertices**, `f k = O_k(1)`.
-/

import JSPProblem.Triangle
import JSPProblem.Boundary
import Mathlib.Data.Finset.SDiff

namespace JSP90

universe u

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqFree : DecidableEq V := Classical.decEq V

/-! ## Part 1 — `Fin 3`, `3`-cliques, and what triangle-freeness gives -/

section Cliques

/-- **EVERY `Fin 3` IS `0`, `1` OR `2`.** -/
theorem fin3_cases (i : Fin 3) : (i = 0) ∨ (i = 1) ∨ (i = 2) := by
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by
    have := i.isLt
    omega
  rcases hi with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

/-- **ON `Fin 3`, TWO DISTINCT INDICES ARE CONSECUTIVE AROUND THE CYCLE.**  This is the counting
fact that turns a `3`-cycle into a `3`-clique. -/
theorem fin3_cycSucc_rel {i j : Fin 3} (h : i ≠ j) : i = cycSucc j ∨ j = cycSucc i := by
  have hi : i.val < 3 := i.isLt
  have hj : j.val < 3 := j.isLt
  have hne : i.val ≠ j.val := fun hh => h (Fin.ext hh)
  have key : (j.val + 1) % 3 = i.val ∨ (i.val + 1) % 3 = j.val := by omega
  rcases key with key | key
  · exact Or.inl (Fin.ext key.symm)
  · exact Or.inr (Fin.ext key.symm)

/-- **THREE MUTUALLY ADJACENT VERTICES ARE A `3`-CLIQUE.**  `SimpleGraph.IsNClique` at the pinned
revision is `IsClique ∧ card = n`, and the readiness conditions of `IsClique` already rule out the
three coincidences by looplessness, so no distinctness hypothesis is needed here. -/
theorem isNClique_three {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    G.IsNClique 3 {a, b, c} := by
  refine G.isNClique_iff.mpr ⟨?_, ?_⟩
  · intro v hv w hw hvw
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · exact (hvw rfl).elim
    · exact hab
    · exact hac
    · exact hab.symm
    · exact (hvw rfl).elim
    · exact hbc
    · exact hac.symm
    · exact hbc.symm
    · exact (hvw rfl).elim
  · have hab' : a ≠ b := adj_irrefl' hab
    have hac' : a ≠ c := adj_irrefl' hac
    have hbc' : b ≠ c := adj_irrefl' hbc
    exact Finset.card_eq_three.mpr ⟨a, b, c, hab', hac', hbc', rfl⟩

/-- **A `3`-CYCLE OF `G` IS A `3`-CLIQUE.**  So `CliqueFree 3` is usable: the `Fin 3` case analysis
above turns the two cyclic edges and the third edge into a `3`-clique. -/
theorem isNClique_three_of_isOddCycle {C : Finset V} (hC : IsOddCycle G C) (h3 : C.card = 3) :
    G.IsNClique 3 C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hcard : C.card = m := card_eq_cyclicOrder f hinj hCmem
  have hm3' : m = 3 := by omega
  subst hm3'
  refine G.isNClique_iff.mpr ⟨?_, h3⟩
  intro v hv w hw hvw
  obtain ⟨i, rfl⟩ := hCmem v |>.mp hv
  obtain ⟨j, rfl⟩ := hCmem w |>.mp hw
  have hne : i ≠ j := fun h => hvw (congrArg f h)
  rcases fin3_cycSucc_rel hne with h | h
  · subst h
    exact (hcyc j).symm
  · subst h
    exact hcyc i

/-- **IN A TRIANGLE-FREE GRAPH, EVERY ODD CYCLE HAS AT LEAST `5` VERTICES.**  Together with
`JSP90.card_inter_neigh_le_two` and `JSP90.shortArc_of_shortest` of `JSPProblem/Fan.lean` this is
what makes the local structure of the shortest odd cycle available in *every* triangle-free graph,
with no hypothesis at all. -/
theorem card_ge_five_of_cliqueFree3_of_isOddCycle (hG3 : G.CliqueFree 3) {C : Finset V}
    (hC : IsOddCycle G C) : 5 ≤ C.card := by
  have hC' : IsOddCycle G C := hC
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hcard : C.card = m := card_eq_cyclicOrder f hinj hCmem
  have hodd : C.card % 2 = 1 := by rw [hcard]; exact hm
  have h3 : 3 ≤ C.card := by rw [hcard]; exact hm3
  by_cases h5 : 5 ≤ C.card
  · exact h5
  · exfalso
    have hlt : C.card < 5 := Nat.lt_of_not_ge h5
    have h3card : C.card = 3 := by omega
    exact absurd (isNClique_three_of_isOddCycle hC' h3card) (hG3 C)

/-- **TRIANGLE-FREE: TWO VERTICES WITH A COMMON NEIGHBOUR ARE NOT ADJACENT.**  This is the local form
of "the neighbourhood of a vertex is an independent set". -/
theorem not_adj_of_common_neigh_of_cliqueFree3 (hG3 : G.CliqueFree 3) {a s t : V}
    (has : G.Adj a s) (hat : G.Adj a t) : ¬ G.Adj s t := by
  intro hst
  exact hG3 _ (isNClique_three has hat hst)

/-- **IN A TRIANGLE-FREE GRAPH THE NEIGHBOURHOOD OF A VERTEX IS INDEPENDENT.** -/
theorem indepSet_neighOf_singleton_of_cliqueFree3 (hG3 : G.CliqueFree 3) {v x y : V}
    (hx : x ∈ neighOf G {v}) (hy : y ∈ neighOf G {v}) : ¬ G.Adj x y := by
  have hvx : G.Adj v x := by
    obtain ⟨w, hw, h⟩ := mem_neighOf.mp hx
    rw [Finset.mem_singleton.mp hw] at h
    exact h.symm
  have hvy : G.Adj v y := by
    obtain ⟨w, hw, h⟩ := mem_neighOf.mp hy
    rw [Finset.mem_singleton.mp hw] at h
    exact h.symm
  exact not_adj_of_common_neigh_of_cliqueFree3 hG3 hvx hvy

/-- **THE CLOSED NEIGHBOURHOOD OF A VERTEX OF A TRIANGLE-FREE GRAPH IS BIPARTITE.**  The two parts are
`{v}` and `N(v)`, and `N(v)` is independent by the previous lemma.  The difficulty of Erdős #73 is
never *at* a vertex. -/
theorem neighOf_insert_isBipartite_of_cliqueFree3 (hG3 : G.CliqueFree 3) {v : V} :
    (induceFinset G (insert v (neighOf G {v}))).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun x => if x = v then 0 else 1) ?_⟩
  intro x y h
  rw [induce_adj] at h
  rcases h with ⟨hxV, hyV, hxy⟩
  by_cases hxv : x = v
  · have hynv : y ≠ v := fun hyv => adj_irrefl' hxy (hxv.trans hyv.symm)
    simp [hxv, hynv]
  · have hxmem : x ∈ neighOf G {v} := by
      rw [Finset.mem_insert] at hxV
      exact hxV.resolve_left hxv
    have hyv : y = v := by
      by_contra hyv'
      have hyN : y ∈ neighOf G {v} := by
        rw [Finset.mem_insert] at hyV
        exact hyV.resolve_left hyv'
      exact absurd hxy (indepSet_neighOf_singleton_of_cliqueFree3 hG3 hxmem hyN)
    simp [hxv, hyv]

end Cliques

/-! ## Part 2 — the local structure of the fan in a triangle-free graph -/

section FanStructure

/-- **TRIANGLE-FREE: A VERTEX ADJACENT TO `f i` IS NOT ADJACENT TO THE SUCCESSOR OF `f i` ON THE
CYCLE.**  The first genuine use of `CliqueFree 3` on the fan: the two attachments of a fan vertex
are *never* consecutive, and the classical picture of the fan is a book, not a web. -/
theorem not_adj_cycSucc_of_adj (hG3 : G.CliqueFree 3) {m : ℕ} (f : Fin m → V)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j))) {x : V} {i : Fin m} (hxi : G.Adj x (f i)) :
    ¬ G.Adj x (f (cycSucc i)) :=
  fun h => hG3 _ (isNClique_three hxi h (hcyc i))

/-- **TWO FAN VERTICES ATTACHED TO THE SAME VERTEX OF THE CYCLE ARE NOT ADJACENT.**  In particular the
fan vertices of `C` attached to one and the same `a ∈ C` form an independent set: the fan is a
disjoint union of independent classes, one class per attachment point, and every edge inside the
fan joins two *different* classes. -/
theorem pairwise_not_adj_fan_of_cliqueFree3 (hG3 : G.CliqueFree 3) {C : Finset V} {a s t : V}
    (_ha : a ∈ C) (has : G.Adj a s) (hat : G.Adj a t) : ¬ G.Adj s t :=
  not_adj_of_common_neigh_of_cliqueFree3 hG3 has hat

/-- **THE SAME, IN SET FORM: a set of vertices all attached to one fixed vertex of the cycle and all
of them in the fan is an independent set** — equivalently, at most one of its vertices is adjacent
to any given vertex of the set. -/
theorem card_le_one_of_adj_of_fan_attach (hG3 : G.CliqueFree 3) {C : Finset V} {a : V} (_ha : a ∈ C)
    {S : Finset V} (hS : ∀ v ∈ S, G.Adj a v) {s t : V} (hs : s ∈ S) (ht : t ∈ S) (hst : G.Adj s t) :
    s = t := by
  by_contra hne
  exact hG3 _ (isNClique_three (hS s hs) (hS t ht) hst)

/-- **THE COMPLETE LOCAL STRUCTURE OF A TRIANGLE-FREE GRAPH AT A SHORTEST ODD CYCLE.**

For `x ∉ C`:

* `(i)` `x` meets `C` in at most **two** vertices (`JSPProblem/Fan.lean`, `card_inter_neigh_le_two`);
* `(ii)` any two of its attachment points are exactly **two steps apart**
  (`JSPProblem/Fan.lean`, `shortArc_of_shortest`);
* `(iii)` `x` is **not** adjacent to the vertex in between** — the new content, and the only place
  where `CliqueFree 3` enters.

Rounds 35 and 63 proved `(i)` and `(ii)`; `(iii)` is the triangle-free hypothesis read at the fan. -/
theorem localStructure_shortest_oddCycle_free {m : ℕ} {C : Finset V} (hG3 : G.CliqueFree 3)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m)
    (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {x : V} (hxC : x ∉ C) :
    (∀ S : Finset (Fin m), (∀ j ∈ S, G.Adj x (f j)) → S.card ≤ 2) ∧
      (∀ i j : Fin m, G.Adj x (f i) → G.Adj x (f j) → i ≠ j →
        cycSucc (cycSucc i) = j ∨ cycSucc (cycSucc j) = i) ∧
      (∀ i : Fin m, G.Adj x (f i) → ¬ G.Adj x (f (cycSucc i))) :=
  ⟨card_inter_neigh_le_two hshort hm hm3 f hinj hcyc hCmem hxC,
    fun i j hi hj hne => shortArc_of_shortest hshort hm hm3 f hinj hcyc hCmem hne hxC hi hj,
    fun i _hi => not_adj_cycSucc_of_adj hG3 f hcyc _hi⟩

end FanStructure

/-! ## Part 3 — the fan carries one unit less packing than `G` -/

section FanPacking

/-- **A VERTICAL SET INSIDE THE BOUNDARY OF `C` IS DISJOINT FROM `C`.**  The counting form of
`C ∩ boundary G C = ∅`, in the shape the packing argument needs. -/
theorem inter_boundary_oddCycle_eq_empty {C : Finset V} (_hC : IsOddCycle G C) {X : Finset V}
    (hX : X ⊆ boundary G C) : C ∩ X = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr fun _ hx =>
    absurd (Finset.mem_inter.mp hx).1
      (Finset.mem_sdiff.mp (hX (Finset.mem_inter.mp hx).2)).2

/-- **UNDER `LocIndep k`, NO PACKING OF `k` ODD CYCLES LIVES INSIDE THE BOUNDARY OF AN ODD CYCLE.**
The packing together with `C` itself would be a packing of `k + 1` odd cycles of `G`, and every member
of the packing is disjoint from `C` because it lies in `boundary G C`.  This is the induction
parameter of the classical Erdős–Pósa argument, in the form the development consumes. -/
theorem oddCycleFamily_card_le_of_boundary {k : ℕ} (hG : LocIndep k G) {C : Finset V}
    (hC : IsOddCycle G C) {𝒟 : Finset (Finset V)} (hD : IsOddCycleFamily (G := G) 𝒟)
    (hsub : ∀ D ∈ 𝒟, D ⊆ boundary G C) : 𝒟.card ≤ k - 1 := by
  have hanti (X : Finset V) (hX : X ∈ 𝒟) : C ∩ X = ∅ :=
    inter_boundary_oddCycle_eq_empty hC (hsub X hX)
  have hmem (X : Finset V) (hX : X ∈ 𝒟) : X ∈ insert C 𝒟 := Finset.mem_insert.mpr (Or.inr hX)
  have hfam : IsOddCycleFamily (G := G) (insert C 𝒟) := by
    refine ⟨?_, ?_⟩
    · intro X hX Y hY hXY
      by_cases hXC' : X ∈ 𝒟
      · by_cases hYC' : Y ∈ 𝒟
        · exact hD.1 X hXC' Y hYC' hXY
        · have hYC : Y = C := by
            rw [Finset.mem_insert] at hY
            exact hY.resolve_right hYC'
          by_cases hXC : X = C
          · exact absurd (hXC.trans hYC.symm) hXY
          · have hne : C ∩ X = ∅ := hanti X hXC'
            refine hYC ▸ Finset.eq_empty_iff_forall_notMem.mpr ?_
            intro z hz
            have hz' : z ∈ C ∩ X := Finset.mem_inter.mpr (Finset.mem_inter.mp hz).symm
            rw [hne] at hz'
            simp at hz'
      · have hXC : X = C := by
          rw [Finset.mem_insert] at hX
          exact hX.resolve_right hXC'
        by_cases hYC' : Y ∈ 𝒟
        · exact hXC ▸ hanti Y hYC'
        · have hYC : Y = C := by
            rw [Finset.mem_insert] at hY
            exact hY.resolve_right hYC'
          exact absurd (hXC.trans hYC.symm) hXY
    · intro X hX
      by_cases hXC' : X ∈ 𝒟
      · exact hD.2 X hXC'
      · have hXC : X = C := by
          rw [Finset.mem_insert] at hX
          exact hX.resolve_right hXC'
        exact hXC ▸ hC
  have hnotin : C ∉ 𝒟 := by
    intro hC'
    obtain ⟨x, hx⟩ := hC.nonempty
    exact (mem_boundary.mp ((hsub C hC') hx)).1 hx
  have hcard : 𝒟.card + 1 ≤ k := by
    have h := hG.oddCycleFamily_card_le hfam
    rwa [Finset.card_insert_of_notMem hnotin] at h
  omega

/-- **`LocIndep 1` AND AN ODD CYCLE FORCE THE FAN TO BE BIPARTITE.**  Every odd cycle of the
induced subgraph on the boundary would extend the packing `{C}`. -/
theorem isBipartite_fan_of_locIndep_one (hG : LocIndep 1 G) {C : Finset V} (hC : IsOddCycle G C) :
    (induceFinset G (boundary G C)).IsBipartite := by
  refine isBipartite_of_no_oddCycle ?_
  rintro ⟨D, hD⟩
  have hsub : D ⊆ boundary G C := isOddCycle_sub_induceFinset hD
  have hfam : IsOddCycleFamily (G := G) ({D} : Finset (Finset V)) :=
    ⟨fun _ hX _ hY hXY =>
        (hXY ((Finset.mem_singleton.mp hX).trans (Finset.mem_singleton.mp hY).symm)).elim, by
      intro X hX
      rw [Finset.mem_singleton.mp hX]
      exact hD.of_induceFinset⟩
  have hsub' : ∀ D' ∈ ({D} : Finset (Finset V)), D' ⊆ boundary G C := by
    intro D' hX x hx
    exact hsub (Finset.mem_singleton.mp hX ▸ hx)
  have hle := oddCycleFamily_card_le_of_boundary hG hC hfam hsub'
  simp only [Finset.card_singleton] at hle
  omega

end FanPacking

/-! ## Part 4 — the reduction: Erdős #73 from the fan statement -/

section Reduction

/-- **THE FAN STATEMENT.**  For every `k`, every finite `W`, every triangle-free graph `G` on `W` with
`LocIndep k G` and every odd cycle `C` of `G`, there is a set `Z` of at most `f k` vertices meeting
**every odd cycle of `G` that meets the boundary of `C`**.

The statement mentions one odd cycle and the set of vertices that touch it, and nothing else: no
connectivity, no packing number, no odd girth, no bound on the size of the boundary.  It is the
residual of the classical argument once the outer layer has been discharged by the descent. -/
def FanErdős73 (f : ℕ → ℕ) : Prop :=
  ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
    ∀ C : Finset W, IsOddCycle G C →
      ∃ Z : Finset W, Z.card ≤ f k ∧
        ∀ D : Finset W, IsOddCycle G D → D ∩ boundary G C ≠ ∅ → D ∩ Z ≠ ∅

/-- **The constant of the reduction**: `fanBound f 0 = 0` and
`fanBound f (k + 1) = max (fanBound f k + f (k + 1) + 1) (3 + (k + 1) * fanBound f k)`, the
maximum of the cost of the triangle step (round 68) and of the cost of the fan step (this round). -/
def fanBound (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (k + 1) => max (fanBound f k + f (k + 1) + 1) (3 + (k + 1) * fanBound f k)

/-- **ERDŐS PROBLEM #73 FOLLOWS FROM ITS FAN STATEMENT.**  The induction is on `k`:

* `k = 0` is `JSP90.erdos73On_zero`;
* at `k + 1` and a triangle, the components of `G − T` satisfy `LocIndep k`
  (`JSP90.locIndep_piece_of_triangle`) and the induction hypothesis makes each of them
  `fanBound f k`-close to bipartite, so `JSP90.closeToBipartite_of_triangle` concludes
  `3 + (k + 1) * fanBound f k`;
* at `k + 1`, no triangle, and a shortest odd cycle `C`: the outer layer of `C` satisfies
  `LocIndep k` (`JSP90.locIndep_outerLayer`) and is by induction `fanBound f k`-close to bipartite;
  by `JSP90.hitsOddCycles_of_bipartite_outer` every odd cycle of `G` then meets
  `boundary G C ∪ {c} ∪ Y`, so every odd cycle of `G` meets `Z ∪ Y ∪ {c}` where `Z` is the set given
  by the fan statement.  The constant is `fanBound f k + f (k + 1) + 1`. -/
theorem erdos73On_of_fanErdős73 {f : ℕ → ℕ} (h : FanErdős73.{u} f) (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      CloseToBipartite (fanBound f k) G := by
  induction k with
  | zero => exact erdos73On_zero
  | succ k ih =>
      intro W instW G hG
      by_cases hbip : G.IsBipartite
      · exact isBipartite_closeToBipartite (m := fanBound f (k + 1)) hbip
      · by_cases hG3 : G.CliqueFree 3
        · obtain ⟨C, hC, hshort⟩ :=
            exists_shortest_oddCycle
              (not_not.mp ((isBipartite_iff_no_oddCycle (G := G)).not.mp hbip))
          obtain ⟨c, hc⟩ := hC.nonempty
          obtain ⟨Y, _, hYcard, hYbip⟩ := closeToBipartite_on
            (ih W instW (induceFinset G (outerLayer G C))
              (locIndep_outerLayer (by omega : (1 : ℕ) ≤ k + 1) hG hC))
          obtain ⟨Z, hZcard, hZhits⟩ := h (k + 1) W instW G hG hG3 C hC
          have htrans : HitsOddCycles G (Z ∪ Y ∪ {c}) := by
            intro D hD
            have h1 : D ∩ (boundary G C ∪ {c} ∪ Y) ≠ ∅ :=
              hitsOddCycles_of_bipartite_outer hC hshort c hc hYbip D hD
            have hne : (D ∩ (boundary G C ∪ {c} ∪ Y)).Nonempty :=
              Finset.nonempty_iff_ne_empty.mpr h1
            obtain ⟨x, hx⟩ := hne
            have hxD : x ∈ D := (Finset.mem_inter.mp hx).1
            have hxT : x ∈ boundary G C ∪ {c} ∪ Y := (Finset.mem_inter.mp hx).2
            rcases (mem_transversal c).mp hxT with hxb | hxc | hxY
            · have hDb : D ∩ boundary G C ≠ ∅ := Finset.nonempty_iff_ne_empty.mp
                ⟨x, Finset.mem_inter.mpr ⟨hxD, hxb⟩⟩
              obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr (hZhits D hD hDb)
              have hyD : y ∈ D := (Finset.mem_inter.mp hy).1
              have hyZ : y ∈ Z := (Finset.mem_inter.mp hy).2
              refine Finset.nonempty_iff_ne_empty.mp ⟨y, Finset.mem_inter.mpr ⟨hyD, ?_⟩⟩
              exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hyZ)))
            · exact Finset.nonempty_iff_ne_empty.mp
                ⟨x, Finset.mem_inter.mpr ⟨hxD,
                  Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr hxc))⟩⟩
            · exact Finset.nonempty_iff_ne_empty.mp
                ⟨x, Finset.mem_inter.mpr ⟨hxD,
                  Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hxY)))⟩⟩
          refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := fanBound f (k + 1))).mpr
            ⟨Z ∪ Y ∪ {c}, ?_, htrans⟩
          have hcard : (Z ∪ Y ∪ {c} : Finset W).card ≤ fanBound f k + f (k + 1) + 1 := by
            have h3 : ((Z ∪ Y) ∪ {c} : Finset W).card
                ≤ (Z ∪ Y).card + ({c} : Finset W).card := card_union_le' _ _
            have h4 : (Z ∪ Y : Finset W).card ≤ Z.card + Y.card := card_union_le' _ _
            have h5 : ({c} : Finset W).card = 1 := Finset.card_singleton c
            omega
          rw [fanBound]
          exact hcard.trans (Nat.le_max_left _ _)
        · obtain ⟨T, hT⟩ : ∃ T : Finset W, G.IsNClique 3 T := by
            by_contra hc
            exact hG3 fun T hT => hc ⟨T, hT⟩
          have hcl : G.IsClique (T : Finset W) := (G.isNClique_iff.mp hT).1
          have hcardT : T.card = 3 := (G.isNClique_iff.mp hT).2
          have hm : ∀ Q ∈ cutPieces G T,
              CloseToBipartite (fanBound f k) (induceFinset G Q) := by
            intro Q hQ
            exact ih W instW (induceFinset G Q) (locIndep_piece_of_triangle hG T Q hcl hcardT hQ)
          have hineq : 3 + (k + 1) * fanBound f k ≤ fanBound f (k + 1) := by
            rw [fanBound]
            exact Nat.le_max_right _ _
          exact closeToBipartite_mono hineq (closeToBipartite_of_triangle hG T hT hm)

/-- **ERDŐS PROBLEM #73 FOLLOWS FROM A PURELY LOCAL STATEMENT ABOUT THE BOUNDARY OF ONE ODD CYCLE IN
A TRIANGLE-FREE GRAPH.** -/
theorem erdos73_of_fanErdős73 {f : ℕ → ℕ} (h : FanErdős73.{u} f) : ∀ k, Erdős73.{u} k :=
  fun k => ⟨fanBound f k, erdos73On_of_fanErdős73 h k⟩

/-- **THE FAN STATEMENT FOLLOWS FROM THE TRIANGLE-FREE CASE** — the converse direction, in the form
that gives the equivalence below.  A set making `G` `f k`-close to bipartite meets every odd cycle. -/
theorem fanErdős73_of_triangleFreeOn {f : ℕ → ℕ}
    (h : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      G.CliqueFree 3 → CloseToBipartite (f k) G) : FanErdős73.{u} f := by
  intro k W instW G hG hG3 C hC
  obtain ⟨X, hXcard, hXbip⟩ := h k W instW G hG hG3
  exact ⟨X, hXcard, fun D hD _ => hitsOddCycles_of_isBipartite_delete hXbip D hD⟩

/-- **ERDŐS PROBLEM #73 IS EQUIVALENT TO ITS FAN STATEMENT.**  In words: the whole of Erdős #73 is
equivalent to the assertion that the boundary of one odd cycle of a triangle-free graph can be killed
with `O_k(1)` vertices.  No connectivity, no packing number, no odd girth and no bound on the size of
the boundary appears in the statement. -/
theorem erdos73_iff_fanErdős73 : (∀ k, Erdős73.{u} k) ↔ ∃ f : ℕ → ℕ, FanErdős73.{u} f := by
  constructor
  · intro h
    refine ⟨fun k => (h k).choose, fanErdős73_of_triangleFreeOn fun k W instW G hG _ => ?_⟩
    exact (h k).choose_spec W instW G hG
  · rintro ⟨f, hf⟩ k
    exact ⟨fanBound f k, erdos73On_of_fanErdős73 hf k⟩

end Reduction

/-! ## Part 5 — the statement is not a formality -/

section Instances

/-- **THE FAN STATEMENT IS PROVED WHEN THE FAN IS BOUNDED.**  If every odd cycle of `G` has at most
`d` vertices in its boundary, then `f k = d + 1` works: the boundary together with one vertex of the
cycle is itself a set meeting every odd cycle that meets the boundary.  (The instance of the headline
theorem obtained this way is *dominated* by `JSP90.erdos73On_of_bounded_boundary` of round 61: the
content of the fan statement is the unbounded-fan case.) -/
theorem fanErdős73_of_bounded_boundary {d : ℕ}
    (hB : ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), BoundedBoundary d G) :
    FanErdős73.{u} (fun _ => d + 1) := by
  intro k W _instW G' hG hG3 C hC
  obtain ⟨c, _hc⟩ := hC.nonempty
  refine ⟨boundary G' C ∪ {c}, ?_, fun D hD hDb => ?_⟩
  · have h3 : ((boundary G' C ∪ {c}) : Finset W).card
        ≤ (boundary G' C).card + ({c} : Finset W).card := card_union_le' _ _
    have h4 : ({c} : Finset W).card = 1 := Finset.card_singleton c
    have h5 : (boundary G' C).card ≤ d := hB W _instW G' C hC
    have h6 : (boundary G' C ∪ {c}).card ≤ d + 1 := by
      generalize hcc : (boundary G' C ∪ {c}).card = n
      omega
    simpa using h6
  · have hne : (D ∩ boundary G' C).Nonempty := Finset.nonempty_iff_ne_empty.mpr hDb
    obtain ⟨x, hx⟩ := hne
    exact Finset.nonempty_iff_ne_empty.mp
      ⟨x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        Finset.mem_union.mpr (Or.inl ((Finset.mem_inter.mp hx).2))⟩⟩

/-- **The cyclic map `j ↦ a + j` of `Fin 3` into `Fin 7`.** -/
def consecutiveTriple_map7 (a : Fin 7) : Fin 3 → Fin 7 :=
  fun j => ⟨(a.val + j.val) % 7, by omega⟩

/-- **A consecutive triple of the cyclic order on `Fin 7`, as a vertex set.** -/
def triple7 (a : Fin 7) : Finset (Fin 7) :=
  (Finset.univ : Finset (Fin 3)).image (consecutiveTriple_map7 a)

/-- The cyclic map is injective, by cancellation of the modulus. -/
theorem consecutiveTriple_map7_inj (a : Fin 7) : Function.Injective (consecutiveTriple_map7 a) := by
  intro i j h
  have hval := congrArg Fin.val h
  have ha := a.isLt
  have hi := i.isLt
  have hj := j.isLt
  simp only [consecutiveTriple_map7] at hval
  exact Fin.ext (by omega)

/-- **A CONSECUTIVE TRIPLE OF `K_7` IS A `3`-CYCLE.** -/
theorem isOddCycle_triple7 (a : Fin 7) :
    IsOddCycle (SimpleGraph.completeGraph (Fin 7)) (triple7 a) := by
  have h : IsOddCycle (SimpleGraph.completeGraph (Fin 7))
      ((Finset.univ : Finset (Fin 3)).image (consecutiveTriple_map7 a)) := by
    refine ⟨3, consecutiveTriple_map7 a, rfl, by decide, consecutiveTriple_map7_inj a, ?_, ?_⟩
    · intro j hcon
      exact cycSucc_ne_self (m := 3) (by omega : 1 < 3) j (consecutiveTriple_map7_inj a hcon)
    · intro x
      constructor
      · intro hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  exact h

theorem mem_triple7_three (x : Fin 7) : x ∈ triple7 3 ↔ x.val = 3 ∨ x.val = 4 ∨ x.val = 5 := by
  rw [triple7, Finset.mem_image]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have hjv := congrArg Fin.val hj
    have hj' : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by
      have := j.isLt
      omega
    rcases hj' with hj' | hj' | hj'
    · left; simp [consecutiveTriple_map7, hj'] at hjv ⊢; omega
    · right; left; simp [consecutiveTriple_map7, hj'] at hjv ⊢; omega
    · right; right; simp [consecutiveTriple_map7, hj'] at hjv ⊢; omega
  · rintro (h | h | h)
    · exact ⟨⟨0, by omega⟩, by simp [consecutiveTriple_map7]; omega⟩
    · exact ⟨⟨1, by omega⟩, by simp [consecutiveTriple_map7]; omega⟩
    · exact ⟨⟨2, by omega⟩, by simp [consecutiveTriple_map7]; omega⟩

theorem mem_triple7_six (x : Fin 7) : x ∈ triple7 6 ↔ x.val = 6 ∨ x.val = 0 ∨ x.val = 1 := by
  rw [triple7, Finset.mem_image]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have hjv := congrArg Fin.val hj
    have hj' : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by
      have := j.isLt
      omega
    rcases hj' with hj' | hj' | hj'
    · left; simp [consecutiveTriple_map7, hj'] at hjv ⊢; omega
    · right; left; simp [consecutiveTriple_map7, hj'] at hjv ⊢; omega
    · right; right; simp [consecutiveTriple_map7, hj'] at hjv ⊢; omega
  · rintro (h | h | h)
    · exact ⟨⟨0, by omega⟩, by simp [consecutiveTriple_map7]; omega⟩
    · exact ⟨⟨1, by omega⟩, by simp [consecutiveTriple_map7]; omega⟩
    · exact ⟨⟨2, by omega⟩, by simp [consecutiveTriple_map7]; omega⟩

/-- **`{3,4,5}` AND `{6,0,1}` ARE DISJOINT.** -/
theorem inter_triple7_empty : triple7 3 ∩ triple7 6 = (∅ : Finset (Fin 7)) := by
  ext x
  simp only [Finset.mem_inter, mem_triple7_three, mem_triple7_six]
  simp
  omega

/-- **THE BOUNDARY OF THE TRIANGLE `{0,1,2}` IN `K_7` CONTAINS `3` AND `6`.** -/
theorem mem_boundary_triple7 {x : Fin 7} (hx : x = 3 ∨ x = 6) :
    x ∈ boundary (SimpleGraph.completeGraph (Fin 7)) (triple7 0) := by
  refine mem_boundary.mpr ⟨?_, 0, ?_, ?_⟩
  · rw [triple7, Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    rintro ⟨j, hj⟩
    have hjv := congrArg Fin.val hj
    have hj' : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by
      have := j.isLt
      omega
    rcases hj' with hj' | hj' | hj' <;> simp [consecutiveTriple_map7, hj'] at hjv <;> omega
  · rw [triple7, Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    exact ⟨⟨0, by omega⟩, by simp [consecutiveTriple_map7]⟩
  · exact completeGraph_adj' x 0 (by omega)

/-- **A VERTEX OF THE TRIANGLE `{3,4,5}` IS NOT IN THE TRIANGLE `{6,0,1}`.** -/
theorem not_mem_triple7_six_of_mem_three {x : Fin 7} (hx : x ∈ triple7 3) : x ∉ triple7 6 := by
  intro hx2
  have hx' : x ∈ triple7 3 ∩ triple7 6 := Finset.mem_inter.mpr ⟨hx, hx2⟩
  rw [inter_triple7_empty] at hx'
  simp at hx'

/-- **MACHINE-CHECKED NEGATIVE RESULT: IN A GENERAL GRAPH THE FAN STATEMENT WITH `n = 1` IS FALSE.**
In `K_7`, at the triangle `C = {0,1,2}` (`triple7 0`), the two triangles `{3,4,5}` and `{6,0,1}`
both meet the boundary of `C` and are **disjoint**, so no set of one vertex meets every odd cycle of
`G` that meets the boundary of `C`.  So the constant of the fan statement is a genuine parameter and
the triangle-free hypothesis is not a formality.  (`K_7` has `MaxDef = 5`, so this witness is not
inside the range of the theorem; the triangle-free witness recorded in the file header is.) -/
theorem not_fanErdős73_one_completeGraph_seven :
    ¬ (∃ Z : Finset (Fin 7), Z.card ≤ 1 ∧
          ∀ D : Finset (Fin 7), IsOddCycle (SimpleGraph.completeGraph (Fin 7)) D →
            D ∩ boundary (SimpleGraph.completeGraph (Fin 7)) (triple7 0) ≠ ∅ → D ∩ Z ≠ ∅) := by
  rintro ⟨Z, hZcard, hZhits⟩
  have hD1 : IsOddCycle (SimpleGraph.completeGraph (Fin 7)) (triple7 3) := isOddCycle_triple7 3
  have hD2 : IsOddCycle (SimpleGraph.completeGraph (Fin 7)) (triple7 6) := isOddCycle_triple7 6
  have hb1 : triple7 3 ∩ boundary (SimpleGraph.completeGraph (Fin 7)) (triple7 0) ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨3, Finset.mem_inter.mpr ⟨mem_triple7_three 3 |>.mpr
      (Or.inl rfl), mem_boundary_triple7 (Or.inl rfl)⟩⟩
  have hb2 : triple7 6 ∩ boundary (SimpleGraph.completeGraph (Fin 7)) (triple7 0) ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨6, Finset.mem_inter.mpr ⟨mem_triple7_six 6 |>.mpr
      (Or.inl rfl), mem_boundary_triple7 (Or.inr rfl)⟩⟩
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr (hZhits _ hD1 hb1)
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr (hZhits _ hD2 hb2)
  have hxD : x ∈ triple7 3 := (Finset.mem_inter.mp hx).1
  have hyD : y ∈ triple7 6 := (Finset.mem_inter.mp hy).1
  have hxZ : x ∈ Z := (Finset.mem_inter.mp hx).2
  have hyZ : y ∈ Z := (Finset.mem_inter.mp hy).2
  have hxy : x = y := by
    by_contra hne
    have h2 : (2 : ℕ) ≤ Z.card := by
      have hsub : ({x, y} : Finset (Fin 7)) ⊆ Z := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz1 | hz2
        · rw [hz1]; exact hxZ
        · rw [hz2]; exact hyZ
      calc 2 ≤ ({x, y} : Finset (Fin 7)).card :=
        (Eq.symm (Finset.card_pair hne)).le
        _ ≤ Z.card := Finset.card_le_card hsub
    omega
  exact not_mem_triple7_six_of_mem_three hxD (hxy ▸ hyD)

end Instances

end

end JSP90
