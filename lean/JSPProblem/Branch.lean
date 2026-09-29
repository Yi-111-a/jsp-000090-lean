/-
# JSP-000090 — the branch-vertex attack on the odd cycle transversal

`JSPProblem/Transversal.lean` reduced the whole of Erdős Problem #73 (Reed 1999, *Mangoes and
Blueberries*, Combinatorica 19 (1999) 267–296) to the single research statement
`OddCycleErdosPosa r`: a bound on the odd cycle **packing** number is a bound on the odd cycle
**transversal** number.  `JSPProblem/Fan.lean` (round 35) developed the *local* half of the
classical fan argument; the *global* half is still open.

This file is a **third attack family**, completely independent of the fan argument and of
connectivity, and it is the simplest possible way of seeing *where* the difficulty of
Erdős–Pósa for odd cycles lies.

The idea.  Call `v` a **branch vertex** of `G` if it has three pairwise distinct neighbours, and
delete them all.  What is left has maximum degree `≤ 2`, and in a graph of maximum degree `≤ 2`

* every vertex of a cycle has its two cycle-neighbours as *all* its neighbours
  (`CycleOrder.adj_iff_cycle_neigh`),
* hence two odd cycles meeting at a vertex are *equal* (`eq_of_mem_inter_of_no_branch`): the two
  cycles agree on the two neighbours of the common vertex and the agreement propagates around
  both cycles (`key`),
* hence the odd cycles of the graph are **pairwise disjoint**, so a packing of `r` odd cycles
  bounds the transversal by `r` — no gap at all
  (`maxCardFamily_eq_all_oddCycles`, `hitsOddCycles_onePerCycle`).

So for graphs of maximum degree `≤ 2` the Erdős–Pósa function for odd cycles is the **identity**,
`r ↦ r` (`closeToBipartite_of_no_branch`).  Deleting the branch vertices and then applying Erdős's
local hypothesis to the residue gives, for the first time in this development, a proved instance
of the headline theorem for a *non-trivial* class of graphs with unbounded odd girth:

* `erdos73On_of_bounded_branch` — if all branch vertices of `G` lie in a set `B` of at most `m`
  vertices, then `LocIndep k G` forces `CloseToBipartite (m + k) G`.  (Compare with
  `erdos73On_of_bounded_odd_girth`, which needs the odd girth to be bounded; this instance puts
  *no* bound on the odd girth.)
* `erdos73On_of_no_branch` — the case `m = 0` of the same statement.

The gap that remains is exactly the one of the research statement: branch vertices are the
obstruction, and no argument here controls how many of them a graph with bounded odd cycle packing
can have.  Turning the local 2-cut structure of `JSPProblem/Fan.lean` into that control is the
global half of the classical argument and remains open (see
`discovery/JSP-000090/policy.json`).
-/

import JSPProblem.Fan
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance : DecidableEq V := Classical.decEq V

/-! ### Branch vertices -/

section BranchVertex

/-- **`v` is a branch vertex of `G`**: it has three pairwise distinct neighbours.  Deleting all
branch vertices leaves a graph of maximum degree `≤ 2`. -/
def BranchVertex (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b c : V, G.Adj v a ∧ G.Adj v b ∧ G.Adj v c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c

theorem branchVertex_three {v : V} (a b c : V) (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : BranchVertex G v :=
  ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩

/-- **A vertex which is not a branch vertex has at most two neighbours.**  This is the whole
content of "no branch vertex" for the arguments below. -/
theorem two_of_three {v : V} (hv : ¬ BranchVertex G v) {a b c : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) : a = b ∨ a = c ∨ b = c := by
  by_contra h
  refine hv (branchVertex_three a b c ha hb hc ?_ ?_ ?_) <;> intro he
  · exact h (Or.inl he)
  · exact h (Or.inr (Or.inl he))
  · exact h (Or.inr (Or.inr he))

end BranchVertex

/-! ### The cyclic order of a cycle -/

/-- The **cyclic order carried by a cycle `C` of `G`**: a numbering `f` of the vertices of `C` by
consecutive adjacency, injective, whose image is `C`.  (`IsOddCycle` is this together with "`m` is
odd and `m ≥ 3`".) -/
structure CycleOrder (G : SimpleGraph V) (C : Finset V) where
  /-- the number of vertices of the cycle -/
  m : ℕ
  /-- the cyclic numbering of the vertices of `C` -/
  f : Fin m → V
  /-- a cycle has at least three vertices -/
  hm3 : 3 ≤ m
  /-- the numbering does not repeat a vertex -/
  hinj : Function.Injective f
  /-- consecutive vertices are adjacent -/
  hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j))
  /-- the image of the numbering is exactly the cycle -/
  hmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x

/-- Every odd cycle carries such a cyclic order, and its length is odd. -/
theorem IsOddCycle.cycleOrder {C : Finset V} (hC : IsOddCycle G C) :
    ∃ o : CycleOrder G C, o.m % 2 = 1 := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  exact ⟨⟨m, f, hm3, hinj, hcyc, hmem⟩, hm⟩

/-- An odd cycle is a nonempty set of vertices. -/
theorem IsOddCycle.nonempty {C : Finset V} (hC : IsOddCycle G C) : C.Nonempty := by
  obtain ⟨m, f, -, hm3, -, -, hmem⟩ := hC
  exact ⟨f ⟨0, by omega⟩, (hmem _).mpr ⟨⟨0, by omega⟩, rfl⟩⟩

/-- **The predecessor of a vertex of the cycle**: `m - 1` steps back. -/
def CycleOrder.prev {G : SimpleGraph V} {C : Finset V} (o : CycleOrder G C) (i : Fin o.m) :
    Fin o.m := (cycSucc^[o.m - 1] : Fin o.m → Fin o.m) i

namespace CycleOrder

variable {C : Finset V} (o : CycleOrder G C)

/-- The predecessor of the successor of `i` is `i` itself. -/
theorem prev_succ (o : CycleOrder G C) (i : Fin o.m) : o.prev (cycSucc i) = i := by
  have hm := o.hm3
  refine arc_rev (i := i) (j := cycSucc i) (d := 1) (by omega) ?_
  rw [Function.iterate_one]

/-- The successor of the predecessor of `i` is `i` itself. -/
theorem succ_prev (o : CycleOrder G C) (i : Fin o.m) : cycSucc (o.prev i) = i := by
  have h : ((cycSucc^[1 + (o.m - 1)] : Fin o.m → Fin o.m) i)
      = cycSucc ((cycSucc^[o.m - 1] : Fin o.m → Fin o.m) i) := by
    rw [Function.iterate_add_apply, Function.iterate_one]
  calc cycSucc (o.prev i)
      = ((cycSucc^[1] : Fin o.m → Fin o.m) ((cycSucc^[o.m - 1] : Fin o.m → Fin o.m) i)) := rfl
    _ = ((cycSucc^[1 + (o.m - 1)] : Fin o.m → Fin o.m) i) := h.symm
    _ = ((cycSucc^[o.m] : Fin o.m → Fin o.m) i) := by rw [show 1 + (o.m - 1) = o.m by omega]
    _ = i := cycSucc_pow i

/-- `t + 1` steps around the cycle are one step after `t` steps. -/
theorem iter_succ (o : CycleOrder G C) (i : Fin o.m) (t : ℕ) :
    ((cycSucc^[t + 1] : Fin o.m → Fin o.m) i) = cycSucc ((cycSucc^[t] : Fin o.m → Fin o.m) i) := by
  rw [Function.iterate_succ_apply']

/-- `t + m` steps around the cycle are the same vertex as `t` steps. -/
theorem iter_add_m (o : CycleOrder G C) (i : Fin o.m) (t : ℕ) :
    ((cycSucc^[t + o.m] : Fin o.m → Fin o.m) i) = ((cycSucc^[t] : Fin o.m → Fin o.m) i) := by
  rw [Function.iterate_add_apply, cycSucc_pow]

/-- **Consecutive vertices of the cycle are distinct.** -/
theorem step_ne (o : CycleOrder G C) (i : Fin o.m) : o.f i ≠ o.f (cycSucc i) := by
  have hm := o.hm3
  intro h
  have h2 : i = cycSucc i := o.hinj h
  have h3 := cycSucc_pow_inj i (p := 1) (q := 0) (by omega) (by omega) (by decide)
  rw [Function.iterate_one, Function.iterate_zero] at h3
  exact h3 h2.symm

/-- **The predecessor of a vertex of the cycle is different from it.** -/
theorem prev_ne (o : CycleOrder G C) (i : Fin o.m) : o.f i ≠ o.f (o.prev i) := by
  have hm := o.hm3
  intro h
  have h2 : i = o.prev i := o.hinj h
  have h3 := cycSucc_pow_inj i (p := 0) (q := o.m - 1) (by omega) (by omega) (by omega)
  rw [Function.iterate_zero] at h3
  exact h3 h2

/-- **The successor and the predecessor of a vertex of the cycle are different** (the cycle has
at least three vertices). -/
theorem step_prev_ne (o : CycleOrder G C) (i : Fin o.m) : o.f (cycSucc i) ≠ o.f (o.prev i) := by
  have hm := o.hm3
  intro h
  have h2 : cycSucc i = o.prev i := o.hinj h
  have h3 := cycSucc_pow_inj i (p := 1) (q := o.m - 1) (by omega) (by omega) (by omega)
  rw [Function.iterate_one] at h3
  exact h3 h2

/-- A vertex of the cycle is adjacent to its predecessor. -/
theorem adj_prev (o : CycleOrder G C) (i : Fin o.m) : G.Adj (o.f i) (o.f (o.prev i)) := by
  have h := o.hcyc (o.prev i)
  rw [o.succ_prev i] at h
  exact h.symm

/-- **The predecessor of the vertex `t` steps after `i` is the vertex `t - 1` steps after `i`**
(for `t ≥ 1`). -/
theorem prev_iter (o : CycleOrder G C) (i : Fin o.m) {t : ℕ} (ht : 1 ≤ t) :
    o.prev ((cycSucc^[t] : Fin o.m → Fin o.m) i) = ((cycSucc^[t - 1] : Fin o.m → Fin o.m) i) := by
  have hm := o.hm3
  rw [CycleOrder.prev]
  calc (cycSucc^[o.m - 1] : Fin o.m → Fin o.m) ((cycSucc^[t] : Fin o.m → Fin o.m) i)
      = (cycSucc^[o.m - 1 + t] : Fin o.m → Fin o.m) i :=
        (Function.iterate_add_apply cycSucc (o.m - 1) t i).symm
    _ = (cycSucc^[t + (o.m - 1)] : Fin o.m → Fin o.m) i := by rw [Nat.add_comm]
    _ = (cycSucc^[(t - 1) + o.m] : Fin o.m → Fin o.m) i :=
        congrArg (fun z : ℕ => (cycSucc^[z] : Fin o.m → Fin o.m) i)
          ((Nat.add_sub_assoc (k := 1) (m := o.m) (by omega) t).symm.trans
            (Nat.sub_add_comm (n := t) (m := o.m) (k := 1) (by omega)))
    _ = (cycSucc^[t - 1] : Fin o.m → Fin o.m) i := by
        rw [Function.iterate_add_apply, cycSucc_pow]

/-- **Every vertex of the cycle is reached from `i` in fewer than `m` steps.** -/
theorem exists_iter (o : CycleOrder G C) (i s : Fin o.m) :
    ∃ t : ℕ, t < o.m ∧ ((cycSucc^[t] : Fin o.m → Fin o.m) i = s) := by
  classical
  set S : Finset (Fin o.m) := (Finset.univ : Finset (Fin o.m)).image
    (fun t : Fin o.m => ((cycSucc^[t.val] : Fin o.m → Fin o.m) i)) with hSdef
  have hcard : S.card = o.m := by
    rw [hSdef, Finset.card_image_of_injective]
    · simp
    · intro a b hab
      by_cases h : a.val = b.val
      · exact Fin.ext h
      · exact absurd hab (cycSucc_pow_inj i a.isLt b.isLt h)
  have hSall : S = (Finset.univ : Finset (Fin o.m)) :=
    Finset.eq_univ_of_card S (hcard.trans (Fintype.card_fin o.m).symm)
  have hsmem : s ∈ S := by rw [hSall]; exact Finset.mem_univ s
  obtain ⟨t, -, he⟩ := Finset.mem_image.mp hsmem
  exact ⟨t.val, t.isLt, he⟩

/-- **The two neighbours of a vertex of a cycle are its two cycle-neighbours.**  In a graph
without branch vertices a vertex of a cycle has no neighbour outside the cycle and no third
neighbour: this is the key structural fact of the whole file. -/
theorem neigh_two_of_not_branch (o : CycleOrder G C) (hnb : ∀ v, ¬ BranchVertex G v)
    (i : Fin o.m) {w : V} (hw : G.Adj (o.f i) w) (hne : w ≠ o.f i) :
    w = o.f (cycSucc i) ∨ w = o.f (o.prev i) := by
  by_cases h1 : w = o.f i
  · exact False.elim (absurd h1 hne)
  by_cases h2 : w = o.f (cycSucc i)
  · exact Or.inl h2
  by_cases h3 : w = o.f (o.prev i)
  · exact Or.inr h3
  exact (hnb (o.f i)
    (branchVertex_three (o.f (cycSucc i)) (o.f (o.prev i)) w (o.hcyc i) (o.adj_prev i) hw
      (o.step_prev_ne i) (fun he => h2 he.symm) (fun he => h3 he.symm))).elim

/-- **The neighbours of a vertex of a cycle are exactly the three points `i`, the successor of `i`
and the predecessor of `i`** (the vertex itself cannot be a neighbour, so the useful form is
`neigh_two_of_not_branch`). -/
theorem adj_iff_cycle_neigh (o : CycleOrder G C) (hnb : ∀ v, ¬ BranchVertex G v) (i : Fin o.m)
    {w : V} (hw : G.Adj (o.f i) w) :
    w = o.f i ∨ w = o.f (cycSucc i) ∨ w = o.f (o.prev i) := by
  by_cases h1 : w = o.f i
  · exact Or.inl h1
  exact Or.inr (o.neigh_two_of_not_branch hnb i hw h1)

end CycleOrder

/-! ### Two odd cycles meeting at a vertex are equal -/

section Meeting

variable {C D : Finset V}

/-- **A vertex of an odd cycle of a graph without branch vertices has no neighbour outside the
cycle.**  Indeed its two cycle-neighbours are already two distinct neighbours, and a third one
would make it a branch vertex. -/
theorem IsOddCycle.neigh_subset (hnb : ∀ v, ¬ BranchVertex G v) {C : Finset V}
    (hC : IsOddCycle G C) {v w : V} (hv : v ∈ C) (hw : G.Adj v w) : w ∈ C := by
  by_contra h
  obtain ⟨o, -⟩ := hC.cycleOrder
  obtain ⟨i, hi⟩ := (o.hmem v).mp hv
  have hv' : v = o.f i := hi.symm
  refine hnb v (branchVertex_three (o.f (cycSucc i)) (o.f (o.prev i)) w ?_ ?_ hw
    (o.step_prev_ne i) ?_ ?_)
  · rw [hv']
    exact o.hcyc i
  · rw [hv']
    exact o.adj_prev i
  · intro he
    exact h ((o.hmem w).mpr ⟨cycSucc i, he⟩)
  · intro he
    exact h ((o.hmem w).mpr ⟨o.prev i, he⟩)

/-- **In a graph without branch vertices, every vertex of an odd cycle which also lies on another
odd cycle lies on that other cycle.**  The proof walks around the first cycle from the common
vertex: the successor of a vertex of the first cycle which lies on the second is adjacent to it,
hence on the second cycle as well. -/
theorem subset_of_mem_inter_of_no_branch (hnb : ∀ v, ¬ BranchVertex G v) {C D : Finset V}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) {x : V} (hx : x ∈ C ∩ D) : C ⊆ D := by
  obtain ⟨o, -⟩ := hC.cycleOrder
  obtain ⟨p, -⟩ := hD.cycleOrder
  obtain ⟨i, hi⟩ := (o.hmem x).mp (Finset.mem_inter.mp hx).1
  obtain ⟨j, hj⟩ := (p.hmem x).mp (Finset.mem_inter.mp hx).2
  have key : ∀ t : ℕ, ∃ s : Fin p.m, o.f ((cycSucc^[t] : Fin o.m → Fin o.m) i) = p.f s := by
    intro t
    induction t with
    | zero =>
        exact ⟨j, by rw [Function.iterate_zero]; exact hi.trans hj.symm⟩
    | succ t ih =>
        obtain ⟨s, hs⟩ := ih
        have hnext : G.Adj (o.f ((cycSucc^[t] : Fin o.m → Fin o.m) i))
            (o.f ((cycSucc^[t + 1] : Fin o.m → Fin o.m) i)) := by
          rw [o.iter_succ i t]
          exact o.hcyc ((cycSucc^[t] : Fin o.m → Fin o.m) i)
        have hmem : o.f ((cycSucc^[t + 1] : Fin o.m → Fin o.m) i) ∈ D :=
          hD.neigh_subset hnb ((p.hmem _).mpr ⟨s, hs.symm⟩) hnext
        have hex : ∃ u : Fin p.m, p.f u = o.f ((cycSucc^[t + 1] : Fin o.m → Fin o.m) i) :=
          (p.hmem _).mp hmem
        obtain ⟨u, hu⟩ := hex
        exact ⟨u, hu.symm⟩
  intro y hy
  obtain ⟨s, hs⟩ := (o.hmem y).mp hy
  obtain ⟨t, ht, hst⟩ := o.exists_iter i s
  obtain ⟨u, hu⟩ := key t
  rw [hst] at hu
  exact (p.hmem y).mpr ⟨u, hu.symm.trans hs⟩

/-- **In a graph without branch vertices, two odd cycles that meet are equal.** -/
theorem eq_of_mem_inter_of_no_branch (hnb : ∀ v, ¬ BranchVertex G v) {C D : Finset V}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) {x : V} (hx : x ∈ C ∩ D) : C = D := by
  obtain ⟨hxC, hxD⟩ := Finset.mem_inter.mp hx
  exact Finset.Subset.antisymm
    (subset_of_mem_inter_of_no_branch hnb hC hD (x := x) (Finset.mem_inter.mpr ⟨hxC, hxD⟩))
    (subset_of_mem_inter_of_no_branch hnb hD hC (x := x) (Finset.mem_inter.mpr ⟨hxD, hxC⟩))

/-- **In a graph without branch vertices, two *distinct* odd cycles are disjoint.** -/
theorem disjoint_of_no_branch (hnb : ∀ v, ¬ BranchVertex G v) (hC : IsOddCycle G C)
    (hD : IsOddCycle G D) (hne : C ≠ D) : C ∩ D = ∅ := by
  rw [← Finset.disjoint_iff_inter_eq_empty]
  exact Finset.disjoint_left.mpr fun _ hx1 hx2 =>
    hne (eq_of_mem_inter_of_no_branch hnb hC hD (Finset.mem_inter.mpr ⟨hx1, hx2⟩))

end Meeting

/-- **A set meeting both sides of a pair of finsets witnesses that their intersection is not
empty.** -/
theorem ne_inter_of_mem {s t : Finset V} {x : V} (h1 : x ∈ s) (h2 : x ∈ t) : s ∩ t ≠ ∅ :=
  fun hz => (Finset.disjoint_left.mp (Finset.disjoint_iff_inter_eq_empty.mpr hz)) h1 h2

/-! ### A packing bound is a transversal bound when there are no branch vertices -/

section Transversal

variable {H : SimpleGraph V}

/-- **A maximum packing of odd cycles of `H` contains all the odd cycles of `H`**, provided `H` has
no branch vertex: a maximum packing meets every odd cycle, and an odd cycle meeting a packed
cycle *is* that packed cycle. -/
theorem maxCardFamily_eq_all_oddCycles (hnb : ∀ v, ¬ BranchVertex H v) {𝒞 : Finset (Finset V)}
    (hfam : IsOddCycleFamily (G := H) 𝒞)
    (hmax : ∀ D, IsOddCycleFamily (G := H) D → D.card ≤ 𝒞.card) :
    ∀ D, IsOddCycle H D → D ∈ 𝒞 := by
  intro D hD
  by_contra hDmem
  have hne' : ∃ x, x ∈ D ∩ 𝒞.biUnion id :=
    Finset.nonempty_iff_ne_empty.mpr (hitsOddCycles_of_maxCardFamily hfam hmax D hD)
  obtain ⟨x, hx⟩ := hne'
  obtain ⟨hxD, hx⟩ := Finset.mem_inter.mp hx
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  have heq : C = D := eq_of_mem_inter_of_no_branch hnb (hfam.2 C hC) hD
    (Finset.mem_inter.mpr ⟨hxC, hxD⟩)
  exact hDmem (heq ▸ hC)

/-- **One vertex per odd cycle is a transversal**: in a graph without branch vertices the odd
cycles are pairwise disjoint, so choosing one vertex in each of them meets all of them and costs
one vertex per cycle.  The construction is by induction on the family. -/
theorem hitsOddCycles_onePerCycle {𝒞 : Finset (Finset V)}
    (hall : ∀ D, IsOddCycle H D → D ∈ 𝒞) (hfam : IsOddCycleFamily (G := H) 𝒞) :
    ∃ X : Finset V, X.card ≤ 𝒞.card ∧ HitsOddCycles H X := by
  classical
  have hne : ∀ D ∈ 𝒞, D.Nonempty := fun D hD => (hfam.2 D hD).nonempty
  refine ⟨(𝒞.attach).image (fun D : {D // D ∈ 𝒞} => Classical.choose (hne D.1 D.2)),
    (Finset.card_image_le).trans (by rw [Finset.card_attach]), ?_⟩
  intro D hD
  have hDmem : D ∈ 𝒞 := hall D hD
  have hch : Classical.choose (hne D hDmem) ∈ D := (hne D hDmem).choose_spec
  have hchX : Classical.choose (hne D hDmem)
      ∈ (𝒞.attach).image (fun E : {E // E ∈ 𝒞} => Classical.choose (hne E.1 E.2)) := by
    refine Finset.mem_image.mpr ⟨⟨D, hDmem⟩, Finset.mem_attach 𝒞 ⟨D, hDmem⟩, rfl⟩
  exact ne_inter_of_mem hch hchX

/-- **Erdős–Pósa for odd cycles in graphs without branch vertices, with the optimal function
`r ↦ r`.**  In a graph whose vertices all have at most two neighbours, the odd cycles are
pairwise disjoint, so `r` disjoint odd cycles bound the odd cycle transversal by `r`.  This is the
`k = 0`-like instance of `OddCycleErdosPosa` which the deletion of the branch vertices leaves
behind, and it is the reason the branch vertices are the whole difficulty of the research
statement. -/
theorem closeToBipartite_of_no_branch (r : ℕ) [Fintype V] (hnb : ∀ v, ¬ BranchVertex H v)
    (hpack : ∀ 𝒞, IsOddCycleFamily (G := H) 𝒞 → 𝒞.card ≤ r) : CloseToBipartite r H := by
  obtain ⟨𝒞, hfam, hmax⟩ := exists_maxCard_oddCycleFamily (G := H)
  have hall : ∀ D, IsOddCycle H D → D ∈ 𝒞 := maxCardFamily_eq_all_oddCycles hnb hfam hmax
  obtain ⟨X, hX, hhits⟩ := hitsOddCycles_onePerCycle hall hfam
  exact (closeToBipartite_iff_hitsOddCycles (G := H) (m := r)).mpr
    ⟨X, hX.trans (hpack 𝒞 hfam), hhits⟩

/-- **Odd cycles of a deletion are odd cycles of the original graph.** -/
theorem IsOddCycle.of_deleteFinset [Fintype V] {B : Finset V} {C : Finset V}
    (hC : IsOddCycle (deleteFinset G B) C) : IsOddCycle G C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  refine ⟨m, f, hm, hm3, hinj, fun j => (deleteFinset_adj.mp (hcyc j)).2.2, hmem⟩

/-- **Deleting `B` and then `X` is the same as deleting `B ∪ X` at once.** -/
theorem deleteFinset_deleteFinset [Fintype V] (B X : Finset V) :
    deleteFinset (deleteFinset G B) X = deleteFinset G (B ∪ X) := by
  ext v w
  simp [deleteFinset_adj, Finset.mem_union, and_left_comm, and_assoc]

end Transversal

/-! ### A proved instance of the headline theorem: graphs with few branch vertices -/

section Bounded

universe u

/-- **Erdős Problem #73 for graphs with few branch vertices.**  If every vertex of `G` with three
distinct neighbours lies in a set `B` of at most `m` vertices, and every subgraph of `G` has an
independent set of size at least `(|H| - k) / 2`, then `G` is the union of a bipartite graph and
at most `m + k` vertices.

This is a new instance of the headline theorem, and unlike `erdos73On_of_bounded_odd_girth` it
puts **no bound on the odd girth**: the hypothesis is about the branch vertices only.  The proof
deletes `B` — after which the graph has maximum degree `≤ 2` and hence pairwise disjoint odd
cycles, so the transversal of the residue is bounded by the *packing* bound `k` of Erdős's local
hypothesis (`LocIndep.oddCycleFamily_card_le`). -/
theorem erdos73On_of_bounded_branch (k m : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      ∀ B : Finset W, (∀ v : W, BranchVertex (deleteFinset G B) v → v ∈ B) → B.card ≤ m →
        CloseToBipartite (m + k) G := by
  intro W instW G hG B hB hBm
  have hnb : ∀ v : W, ¬ BranchVertex (deleteFinset G B) v := by
    intro v hv
    by_cases hmem : v ∈ B
    · obtain ⟨a, b, c, ha, -, -, -⟩ := hv
      exact (deleteFinset_adj.mp ha).1 hmem
    · exact absurd (hB v hv) hmem
  have hpack : ∀ 𝒞 : Finset (Finset W), IsOddCycleFamily (G := deleteFinset G B) 𝒞 →
      𝒞.card ≤ k := by
    intro 𝒞 h𝒞
    exact hG.oddCycleFamily_card_le
      ⟨h𝒞.1, fun D hD => (h𝒞.2 D hD).of_deleteFinset⟩
  obtain ⟨X, hX, hhits⟩ :=
    (closeToBipartite_iff_hitsOddCycles (G := deleteFinset G B) (m := k)).mp
      (closeToBipartite_of_no_branch k (hnb := hnb) hpack)
  refine ⟨B ∪ X, (Finset.card_union_le _ _).trans (Nat.add_le_add hBm hX), ?_⟩
  rw [← deleteFinset_deleteFinset]
  exact isBipartite_delete_of_hitsOddCycles hhits

/-- **Erdős Problem #73 for graphs with few high-degree vertices**: if all vertices of `G` with
three distinct neighbours lie in a set `B` of at most `m` vertices, then `LocIndep k G` forces
`CloseToBipartite (m + k) G`.

This is the same statement as `erdos73On_of_bounded_branch` with the hypothesis read directly on
`G` (rather than on the deletion), i.e. the classical form "the set of vertices of degree `≥ 3` is
small": it covers, for instance, every subdivision of a graph with `m` vertices of degree `≥ 3`, and
it puts **no bound on the odd girth**. -/
theorem erdos73On_of_few_high_degree (k m : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      ∀ B : Finset W, (∀ v : W, BranchVertex G v → v ∈ B) → B.card ≤ m →
        CloseToBipartite (m + k) G := by
  intro W instW G hG B hB hBm
  refine erdos73On_of_bounded_branch (k := k) (m := m) W instW G hG B (fun v hv => ?_) hBm
  by_cases hmem : v ∈ B
  · exact hmem
  · exfalso
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hv
    exact absurd (hB v (branchVertex_three a b c (deleteFinset_adj.mp ha).2.2
      (deleteFinset_adj.mp hb).2.2 (deleteFinset_adj.mp hc).2.2 hab hac hbc)) hmem

/-- **Erdős Problem #73 for graphs without branch vertices**: if `LocIndep k G` and every vertex
of `G` has at most two neighbours, then `G` is the union of a bipartite graph and at most `k`
vertices.  (The case `m = 0` of `erdos73On_of_bounded_branch`; for such a graph the odd cycles
are pairwise disjoint, so `k` is the *exact* transversal bound whenever the odd cycles exist.) -/
theorem erdos73On_of_no_branch (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      (∀ v : W, ¬ BranchVertex G v) → CloseToBipartite k G := by
  intro W instW G hG hnb
  have hB : ∀ v : W, BranchVertex (deleteFinset G ∅) v → v ∈ (∅ : Finset W) := by
    intro v hv
    rw [deleteFinset_empty] at hv
    exact absurd (hnb v hv) (by simp)
  simpa using erdos73On_of_bounded_branch (k := k) (m := 0) W instW G hG ∅ hB (by simp)

end Bounded

end

end JSP90
