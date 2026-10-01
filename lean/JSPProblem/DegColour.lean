/-
# JSP-000090 — the DISJOINT-ODD-CYCLE and the DEGREE–COLOURING axes (round 98)

This file is round 98 of the `JSP-000090` Lean harness and it opens **two new attack families**,
both of them untouched by rounds 35–97.

Rounds 38–97 attacked the statement through *local* patterns of the graph: branch vertices, fans,
odd girth, 2-cuts, max cuts, intersection patterns of the odd cycles.  The class
`BranchVertex`-free of `JSPProblem/Branch.lean` is the extreme case of the first family: it says
**no vertex of `G` has three neighbours**, and round 38 read off of it the sharp instance
`JSP90.erdos73On_of_no_branch : LocIndep k G → (every vertex has ≤ 2 neighbours) → CloseToBipartite
k G`.  What that instance really uses is much weaker, and this round isolates it.

## 1. The DISJOINT-ODD-CYCLE axis: the *optimal* instance with the weakest structural hypothesis

`JSP90.OddCycles G` is **the family of all the odd cycles of `G`**, and

> **`JSP90.erdos73On_of_disjointOddCycles : LocIndep k G → DisjointFamily (OddCycles G) →
>   CloseToBipartite k G`**

is a **new instance of the headline theorem with the optimal constant `k`**, whose hypothesis is
*only* that **any two distinct odd cycles of `G` are vertex-disjoint** — no degree bound, no odd
girth bound, no connectivity, no decomposition.  The point is that the hypothesis of round 38
(`∀ v, ¬ BranchVertex G v`) is used in `JSPProblem/Branch.lean` for exactly one thing, namely
`eq_of_mem_inter_of_no_branch` ("two odd cycles through a common vertex are equal"), and that is
replaced here by the conclusion it is used to derive: `JSP90.disjointFamily_oddCycles_of_no_branch`
shows round 38's instance is a special case of this one, so the new instance is **strictly
weaker in hypothesis and equal in constant**.  The class is settled *exactly*:

> **`JSP90.erdos73On_disjointOddCycles_exact`** — for every `k ≥ 1` the constant is `k` and not
> `k - 1`: the witness `kTriangles k` of `JSPProblem/Sharp.lean` satisfies `LocIndep k`, its odd
> cycles are pairwise vertex-disjoint (`JSP90.oddCycles_kTriangles`, proved here by analysing the
> cyclic order), and it is not `(k - 1)`-close to bipartite.

## 2. The DEGREE–COLOURING axis: the greedy colouring theorem, and a colour-class certificate

The pinned Mathlib slice has no degeneracy and no greedy-colouring API at all (this is recorded in
the header of `JSPProblem/Layer.lean`, which defines `Neigh` and `MaxDeg` by hand), so the classical
first lemma of graph colouring is proved here from scratch:

* `JSP90.exists_colouringOn_of_degLe` — the greedy step, by strong induction on the size of the
  vertex set (this is the load-bearing proof of the round: a fresh `Nat.strong_induction_on` over
  `Finset`s, with the "there is a free colour" step);
* `JSP90.coloring_of_degLe`, `JSP90.degLe_of_coloring`, `JSP90.coloring_of_maxDegLe` — a graph all
  of whose vertices have at most `d` neighbours is `Fin (d + 1)`-colourable, and conversely;
* `JSP90.OddColorClass` and `JSP90.erdos73On_of_oddColorClass` — **a colour class of a proper
  colouring is a certificate for the conclusion of Erdős #73**: if one colour class meets every odd
  cycle of `G` and has at most `q` vertices, then `CloseToBipartite q G`.  This is a *new
  hypothesis form* of the headline theorem, and it is the form in which a colouring argument can
  ever be used: a proper colouring alone is **not** enough (and `JSP90.g6` of
  `JSPProblem/Finite.lean` is the machine-checked counterexample: it is `2`-close to bipartite and
  every colour class of every proper colouring of it that is an odd cycle transversal has size `2`,
  never `1`).

## 3. The exact value of the constant on the class, and where the degree axis stops

`JSP90.erdos73On_disjointOddCycles_exact` settles the class *exactly* (constant `k`, not `k - 1`, for
every `k >= 1`, the lower bound being the witness `kTriangles k` of `JSPProblem/Sharp.lean`), and
`JSP90.closeToBipartite_iff_card_oddCycles_of_disjoint` goes further: the class is *decided* by a
single count.  The **degree** part of the axis stops here: the greedy theorem bounds **cliques**
(`JSP90.card_clique_le_of_coloring`), not colour classes, and a `(d + 1)`-colouring of a
`d`-degenerate graph does **not** bound the size of a colour class, so it gives no transversal bound
and hence no instance of Erdős #73 by itself.  The first unproved statement of the axis is
`JSP90.SubcubicErdosPosa` (`LocIndep k G -> MaxDegLe G 3 -> CloseToBipartite g k G`), still
*assumed* in `JSPProblem/Subcubic.lean`.

## What is not proved here

`jsp_000090_main` is still not declared, and `JSP90.OddCycleErdosPosa r` for arbitrary `r` is still
the primary blocker.  This round does not touch the 3-connected case (which needs Mader's structure
theorem, absent from the pinned Mathlib slice) and it does not touch the `k`-independent constant
for bounded degree greater than two, which is `JSPProblem/Subcubic.lean`'s assumed
`JSP90.SubcubicErdős73`.

Three further statements were *considered and refuted by analysis* before being formalised, and are
recorded here so that no later round re-tries them: a `(d + 1)`-colouring does not bound the size of
a colour class (so the greedy theorem yields no transversal bound); a colour class of a proper
colouring need not meet every odd cycle (a 5-cycle can avoid one colour of a 4-colouring), which is
why `JSP90.OddColorClass` is a separate hypothesis; and no graph with at most five vertices satisfies
`LocIndep 1` and fails `CloseToBipartite 1` (two vertex-disjoint odd cycles need six vertices, and
two of them force deficiency `2`), so the smallest `LocIndep 1` graph of maximum degree `3` that is
not `1`-close to bipartite is the nine-vertex `p9` of `JSPProblem/Petersen.lean`.
-/

import JSPProblem.Branch
import JSPProblem.Layer
import JSPProblem.Sharp
import JSPProblem.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace JSP90

open Finset Fintype Set

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqDegCol : DecidableEq V := Classical.decEq V

local instance instDecidableAdjDegCol : ∀ v w : V, Decidable (G.Adj v w) :=
  fun _ _ => Classical.propDecidable _

local instance instDecidableIsOddCycleDegCol {D : Finset V} : Decidable (IsOddCycle G D) :=
  Classical.propDecidable _

local instance instDecidableEqFinProdDegCol (k : ℕ) : DecidableEq (Fin 3 × Fin k) := Classical.decEq _

local instance instDecidableEqFinProdFinsetDegCol (k : ℕ) :
    DecidableEq (Finset (Fin 3 × Fin k)) := Classical.decEq _

/-! ### Part 1 — the family of *all* the odd cycles of `G` -/

section OddCyclesAll

/-- **`OddCycles G`** is the family of the odd cycles of `G` — the whole set of them, as a finset of
vertex sets.  The hypothesis `DisjointFamily (OddCycles G)` of the instance below says exactly that
**two distinct odd cycles of `G` are vertex-disjoint**. -/
def OddCycles (G : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (IsOddCycle G)

theorem mem_oddCycles {C : Finset V} : C ∈ OddCycles G ↔ IsOddCycle G C := by
  unfold OddCycles
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_oddCycles_univ {C : Finset V} (hC : IsOddCycle G C) : C ∈ OddCycles G :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩

/-- Every member of `OddCycles G` is an odd cycle of `G`. -/
theorem oddCycles_all_odd : ∀ C ∈ OddCycles G, IsOddCycle G C :=
  fun _ hC => (Finset.mem_filter.mp hC).2

/-- `OddCycles G` is a family of odd cycles, and a packing as soon as its members are disjoint. -/
theorem isOddCycleFamily_oddCycles (hd : DisjointFamily (OddCycles G)) :
    IsOddCycleFamily (G := G) (OddCycles G) :=
  ⟨hd, oddCycles_all_odd⟩

/-- **A transversal of a graph whose odd cycles are pairwise vertex-disjoint has at least as many
vertices as there are odd cycles**: it must meet each of them, in a *different* vertex.  This is
the lower half of the exact value computed by `closeToBipartite_iff_card_oddCycles_of_disjoint`
(the counting half of the identity Erdős–Pósa function, `JSPProblem/Optimal.lean`). -/
theorem card_le_of_hitsOddCycles_disjoint (X : Finset V) (hX : HitsOddCycles G X)
    (hd : DisjointFamily (OddCycles G)) : (OddCycles G).card ≤ X.card :=
  card_le_of_hitsOddCycles_of_disjointFamily hd
    (fun i hi => (oddCycles_all_odd i hi).nonempty) (fun i hi => hX i (oddCycles_all_odd i hi))

/-- **THE EXACT VALUE OF THE ODD CYCLE TRANSVERSAL ON THE DISJOINT-ODD-CYCLE CLASS: it is the
number of odd cycles.**  `CloseToBipartite m G` holds exactly when `G` has at most `m` odd cycles,
for every graph whose odd cycles are pairwise vertex-disjoint — no hypothesis of Erdős #73
involved.  So the class is *decided* by a single count, and `erdos73On_of_disjointOddCycles` is the
upper bound `m = k` of that count. -/
theorem closeToBipartite_iff_card_oddCycles_of_disjoint (m : ℕ)
    (hd : DisjointFamily (OddCycles G)) : CloseToBipartite m G ↔ (OddCycles G).card ≤ m := by
  constructor
  · rintro ⟨X, hX, hb⟩
    exact le_trans
      (card_le_of_hitsOddCycles_disjoint X (hitsOddCycles_of_isBipartite_delete hb) hd) hX
  · intro h
    obtain ⟨X, hX, hhits⟩ :=
      hitsOddCycles_onePerCycle (fun D hD => mem_oddCycles_univ hD) (isOddCycleFamily_oddCycles hd)
    exact (closeToBipartite_iff_hitsOddCycles (m := m)).mpr ⟨X, hX.trans h, hhits⟩

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, with the optimal constant `k` and a strictly weaker
hypothesis than `JSPProblem/Branch.lean`'s `erdos73On_of_no_branch`.**

`LocIndep k G` bounds the size of a packing of odd cycles by `k`
(`JSPProblem.LocIndep.oddCycleFamily_card_le`), and if the odd cycles are pairwise vertex-disjoint
then *all* of them together form a packing, so there are at most `k` of them; choosing one vertex in
each of them gives an odd cycle transversal of size at most `k`
(`JSPProblem/Branch.lean`, `hitsOddCycles_onePerCycle`), and the residue is bipartite.

The hypothesis is only "**any two distinct odd cycles of `G` are vertex-disjoint**": no degree
bound, no odd-girth bound, no connectivity, no decomposition, and no condition on the vertices
outside the odd cycles. -/
theorem erdos73On_of_disjointOddCycles (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      DisjointFamily (OddCycles G) → CloseToBipartite k G := by
  intro W instW G' hG hd
  have hfam : IsOddCycleFamily (G := G') (OddCycles G') := isOddCycleFamily_oddCycles hd
  have hcard : (OddCycles G').card ≤ k := hG.oddCycleFamily_card_le hfam
  obtain ⟨X, hX, hhits⟩ :=
    hitsOddCycles_onePerCycle (fun D hD => mem_oddCycles_univ hD) hfam
  exact (closeToBipartite_iff_hitsOddCycles (G := G') (m := k)).mpr
    ⟨X, hX.trans hcard, hhits⟩

/-- **ROUND 38'S INSTANCE IS A SPECIAL CASE OF THIS ROUND'S**: a graph without branch vertices has
pairwise vertex-disjoint odd cycles (`JSPProblem/Branch.lean`,
`eq_of_mem_inter_of_no_branch`: two odd cycles through a common vertex are *equal*).  So
`JSPProblem/Branch.lean`'s hypothesis "every vertex has at most two neighbours" is used, in
`erdos73On_of_no_branch`, for this one conclusion and for nothing else. -/
theorem disjointFamily_oddCycles_of_no_branch (hnb : ∀ v, ¬ BranchVertex G v) :
    DisjointFamily (OddCycles G) :=
  fun _ hC _ hD hne =>
    disjoint_of_no_branch hnb (oddCycles_all_odd _ hC) (oddCycles_all_odd _ hD) hne

/-- **Consequently `JSPProblem/Branch.lean`'s `erdos73On_of_no_branch` follows from the new
instance** (it is re-proved here, with the constant `k` unchanged). -/
theorem erdos73On_of_no_branch' (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      (∀ v : W, ¬ BranchVertex G v) → CloseToBipartite k G := by
  intro W instW G' hG hnb
  exact erdos73On_of_disjointOddCycles k W instW G' hG
    (disjointFamily_oddCycles_of_no_branch hnb)

end OddCyclesAll

/-! ### Part 2 — the exact value of the constant on the disjoint-odd-cycle class -/

section Sharp

/-- **Every odd cycle of `kTriangles k` is a whole fibre.**  Each edge of `kTriangles k` joins two
vertices of one fibre, so all the vertices of a cycle share one fibre index. -/
theorem eq_fibre_of_cyc_kTriangles {k m : ℕ} {f : Fin m → Fin 3 × Fin k}
    (hcyc : ∀ j : Fin m, (kTriangles k).Adj (f j) (f (cycSucc j))) :
    ∀ j : Fin m, ∀ t : ℕ, (f ((cycSucc^[t] : Fin m → Fin m) j)).2 = (f j).2 := by
  intro j t
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨h2, -⟩ := kTriangles_adj.mp (hcyc ((cycSucc^[t] : Fin m → Fin m) j))
    rw [Function.iterate_succ_apply']
    exact h2.symm.trans ih

/-- **Every odd cycle of `kTriangles k` is one of its `k` fibres.**  All the edges of `kTriangles k`
join two vertices of one fibre, so all the vertices of a cycle lie in a single fibre; the fibre has
three vertices, and the cycle has at least three distinct ones, so the cycle *is* the fibre. -/
theorem exists_eq_tri_of_isOddCycle_kTriangles {k : ℕ} {C : Finset (Fin 3 × Fin k)}
    (hC : IsOddCycle (kTriangles k) C) : ∃ i : Fin k, C = tri i := by
  obtain ⟨o, hodd⟩ := hC.cycleOrder
  have hm3 := o.hm3
  have hfibre : ∀ j : Fin o.m, (o.f j).2 = (o.f ⟨0, by omega⟩).2 := by
    intro j
    obtain ⟨t, -, ht⟩ := o.exists_iter ⟨0, by omega⟩ j
    rw [← ht]
    exact eq_fibre_of_cyc_kTriangles o.hcyc ⟨0, by omega⟩ t
  set i : Fin k := (o.f ⟨0, by omega⟩).2
  have hCsub : C ⊆ tri i := by
    intro x hx
    obtain ⟨j, hj⟩ := (o.hmem x).mp hx
    obtain rfl := hj
    exact mem_tri.mpr (hfibre j)
  have htri : (tri i).card = 3 := card_tri i
  have himg : C = ((Finset.univ : Finset (Fin o.m)).image o.f) := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := (o.hmem x).mp hx
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
    · intro hx
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hx
      exact (o.hmem x).mpr ⟨j, hj⟩
  have himgcard : ((Finset.univ : Finset (Fin o.m)).image o.f).card = o.m := by
    rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin o.m)) o.hinj]
    simp
  have hcardC : C.card = o.m := by
    have h := congrArg Finset.card himg
    omega
  have hle : o.m ≤ 3 := by
    have h := Finset.card_le_card hCsub
    rw [htri] at h
    omega
  have hm : o.m = 3 := by omega
  refine ⟨i, Finset.eq_of_subset_of_card_le hCsub ?_⟩
  rw [hcardC, hm, htri]

/-- **Each fibre of `kTriangles k` is a member of `OddCycles`.** -/
theorem mem_oddCycles_tri (k : ℕ) (i : Fin k) : tri i ∈ OddCycles (kTriangles k) :=
  mem_oddCycles_univ (isOddCycle_tri i)

/-- **The odd cycles of `kTriangles k` are pairwise vertex-disjoint**, so the witness of the lower
bound `f(k) ≥ k` of `JSPProblem/Sharp.lean` lives in the class of the new instance: the `k` fibres
are pairwise disjoint odd cycles, so this is the *pointwise* version of
"`OddCycles (kTriangles k)` is the family of the `k` fibres". -/
theorem disjointFamily_oddCycles_kTriangles (k : ℕ) : DisjointFamily (OddCycles (kTriangles k)) := by
  intro C hC D hD hne
  obtain ⟨i, rfl⟩ := exists_eq_tri_of_isOddCycle_kTriangles (oddCycles_all_odd C hC)
  obtain ⟨j, hj⟩ := exists_eq_tri_of_isOddCycle_kTriangles (oddCycles_all_odd D hD)
  subst hj
  exact (Finset.disjoint_iff_inter_eq_empty).mp (tri_disjoint (fun h => hne (congrArg tri h)))

/-- **THE EXACT VALUE OF THE CONSTANT OF ERDŐS #73 ON THE DISJOINT-ODD-CYCLE CLASS IS `k`.**

The upper bound is `JSP90.erdos73On_of_disjointOddCycles`; the lower bound is the witness
`kTriangles k` of `JSPProblem/Sharp.lean`, whose `k` fibres are pairwise vertex-disjoint odd cycles
and which is not `(k - 1)`-close to bipartite.  So no constant below `k` works on this class, for
any `k ≥ 1`. -/
theorem erdos73On_disjointOddCycles_exact (k : ℕ) (hk : 1 ≤ k) :
    (∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
        DisjointFamily (OddCycles G) → CloseToBipartite k G) ∧
      ¬ (∀ (W : Type 0) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
        DisjointFamily (OddCycles G) → CloseToBipartite (k - 1) G) := by
  refine ⟨fun W instW G' hG hd => erdos73On_of_disjointOddCycles k W instW G' hG hd, fun h => ?_⟩
  have hloc := locIndep_kTriangles (k := k)
  have hfam : DisjointFamily (OddCycles (kTriangles k)) := disjointFamily_oddCycles_kTriangles k
  have hnot : ¬ CloseToBipartite (k - 1) (kTriangles k) := by
    rw [closeToBipartite_iff]
    omega
  exact hnot (h (Fin 3 × Fin k) inferInstance (kTriangles k) hloc hfam)

end Sharp

/-! ### Part 3 — the greedy colouring theorem -/

section Greedy

/-- `c` is a **proper colouring of the subgraph induced by `S`**: the ends of every edge inside `S`
get different colours. -/
def ColouringOn {α : Type*} (G : SimpleGraph V) (c : V → α) (S : Finset V) : Prop :=
  ∀ ⦃u v⦄, u ∈ S → v ∈ S → G.Adj u v → c u ≠ c v

/-- **A finite set is not the whole of a finite type**: an ambient finite type with more elements
than `s` has an element outside `s`.  This is the "there is a free colour" step of the greedy
argument. -/
theorem exists_not_mem_of_card_lt {α : Type*} [Fintype α] (s : Finset α)
    (h : s.card < Fintype.card α) : ∃ a, a ∉ s := by
  by_contra hcon
  have hall : ∀ a, a ∈ s := by
    intro a
    by_contra hn
    exact hcon ⟨a, hn⟩
  have hss : s = (Finset.univ : Finset α) :=
    Finset.ext fun a => ⟨fun _ => Finset.mem_univ _, fun _ => hall a⟩
  rw [hss, Finset.card_univ] at h
  exact (Nat.lt_irrefl _ h)

/-- **THE GREEDY COLOURING THEOREM, step by step (the load-bearing proof of this round).**

If every vertex of `G` has at most `d` neighbours, then every vertex set carries a colouring with
`d + 1` colours which is proper on it.  The induction is on the size of the vertex set: peel off a
vertex of degree `< d` inside the set, colour the rest by induction, and extend — the vertex sees
fewer than `d` neighbours, so fewer than `d` of the `d + 1` colours are forbidden. -/
theorem exists_colouringOn_of_degLe (d : ℕ) (hdeg : ∀ v : V, (Neigh G v).card ≤ d) :
    ∀ n : ℕ, ∀ S : Finset V, S.card ≤ n → ∃ c : V → Fin (d + 1), ColouringOn G c S := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hS
    rcases Finset.eq_empty_or_nonempty S with rfl | hne
    · exact ⟨fun _ => 0, by simp [ColouringOn]⟩
    obtain ⟨v, hv⟩ := hne
    have hlt : (S.erase v).card < n := by
      have herase : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hv
      have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hv⟩
      omega
    obtain ⟨c, hc⟩ := ih (S.erase v).card hlt (S.erase v) (le_refl _)
    -- the colours forbidden at `v` are the colours of its neighbours inside `S \ {v}`
    set U : Finset (Fin (d + 1)) := ((Neigh G v) ∩ S.erase v).image c with hUdef
    have hUcard : U.card ≤ ((Neigh G v) ∩ S.erase v).card := Finset.card_image_le
    have hUle : ((Neigh G v) ∩ S.erase v).card ≤ ((Neigh G v) ∩ S).card :=
      Finset.card_le_card fun x hx => Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_erase.mp (Finset.mem_inter.mp hx).2).2⟩
    have hle' : ((Neigh G v) ∩ S).card ≤ (Neigh G v).card :=
      Finset.card_le_card fun x hx => (Finset.mem_inter.mp hx).1
    have hUlt : U.card < Fintype.card (Fin (d + 1)) := by
      have hle := hdeg v
      rw [Fintype.card_fin]
      simp only [hUdef] at hUcard hUle ⊢
      omega
    obtain ⟨a, ha⟩ := exists_not_mem_of_card_lt U hUlt
    have key : ∀ w : V, w ∈ S → G.Adj v w → a ≠ c w := by
      intro w hw hwv
      have hwv' : w ≠ v := by
        intro hcon
        subst hcon
        exact G.irrefl hwv
      have hmem : c w ∈ ((Neigh G v) ∩ S.erase v).image c := by
        refine Finset.mem_image.mpr ⟨w, ?_, rfl⟩
        exact Finset.mem_inter.mpr ⟨(mem_neigh).mpr hwv, Finset.mem_erase.mpr ⟨hwv', hw⟩⟩
      exact fun hcon => ha (hUdef.symm ▸ hcon ▸ hmem)
    set c' : V → Fin (d + 1) := fun x => if x = v then a else c x
    refine ⟨c', fun u w hu hw huw => ?_⟩
    simp only [c']
    by_cases huv : u = v
    · rw [if_pos huv]
      have hAdj : G.Adj v w := by rw [← huv]; exact huw
      by_cases hww : w = v
      · rw [if_pos hww]
        exact (G.irrefl (hww ▸ hAdj)).elim
      · rw [if_neg hww]
        exact fun hcon => key w hw hAdj hcon
    · by_cases hww : w = v
      · rw [if_pos hww]
        have hAdj : G.Adj v u := G.adj_symm (by rw [← hww]; exact huw)
        by_cases huv' : u = v
        · rw [if_pos huv']
          exact (G.irrefl (huv' ▸ hAdj)).elim
        · rw [if_neg huv']
          exact fun hcon => key u hu hAdj hcon.symm
      · rw [if_neg huv, if_neg hww]
        exact hc (u := u) (v := w) (Finset.mem_erase.mpr ⟨huv, hu⟩)
          (Finset.mem_erase.mpr ⟨hww, hw⟩) huw

theorem coloring_of_degLe (d : ℕ) (hdeg : ∀ v : V, (Neigh G v).card ≤ d) :
    Nonempty (G.Coloring (Fin (d + 1))) := by
  obtain ⟨c, hc⟩ :=
    exists_colouringOn_of_degLe d hdeg _ Finset.univ (le_trans (le_refl _) le_rfl)
  exact ⟨⟨c, fun {u v} huw => hc (Finset.mem_univ _) (Finset.mem_univ _) huw⟩⟩

omit [Fintype V] in
/-- **The converse of the greedy theorem, in the only form in which it is true**: a
`(d + 1)`-colouring bounds the size of a **clique** by `d + 1`.  (A *degree* bound would be false —
a 3-regular bipartite graph is 2-colourable and has vertices of degree 3 — and this is why
`coloring_of_degLe` is the contentful direction.) -/
theorem card_clique_le_of_coloring {d : ℕ} (hcol : Nonempty (G.Coloring (Fin (d + 1))))
    {C : Finset V} (hC : G.IsClique C) : C.card ≤ d + 1 := by
  obtain ⟨⟨c, hc⟩⟩ := hcol
  have hinjOn : Set.InjOn c C := by
    intro x hxC y hyC hxy
    by_contra hne
    exact hc (hC hxC hyC hne) hxy
  calc C.card ≤ (Finset.univ : Finset (Fin (d + 1))).card :=
      Finset.card_le_card_of_injOn (s := C) c (fun x _ => Finset.mem_univ (c x)) hinjOn
    _ = d + 1 := by rw [Finset.card_univ, Fintype.card_fin]

/-- The greedy theorem for the **degree** form of `JSPProblem/Layer.lean`. -/
theorem coloring_of_maxDegLe {d : ℕ} (hdeg : MaxDegLe G d) : Nonempty (G.Coloring (Fin (d + 1))) :=
  coloring_of_degLe d hdeg

end Greedy

/-! ### Part 4 — a colour class is a certificate for the conclusion -/

section ColorClass

/-- **`OddColorClass G c i`**: the set of the vertices of colour `i` meets every odd cycle of `G`.
Together with a bound on its size this is a certificate for the conclusion of Erdős #73. -/
def OddColorClass (G : SimpleGraph V) {α : Type*} (c : V → α) (i : α) : Prop :=
  ∀ C, IsOddCycle G C → ∃ v ∈ C, c v = i

theorem mem_colorClass {α : Type*} (c : V → α) (i : α) :
    ∀ v : V, v ∈ (Finset.univ : Finset V).filter (fun w => c w = i) ↔ c v = i := by
  intro v
  simp [Finset.mem_filter]

/-- **A COLOUR-CLASS CERTIFICATE FOR ERDŐS #73.**  If `c` is a proper colouring of `G`, the set of
the vertices of one colour meets every odd cycle of `G` and has at most `q` elements, then `G` is
the union of a bipartite graph and at most `q` vertices.  This is the only form in which a
colouring argument can be used to conclude Erdős #73, and it is *not* implied by properness alone:
on `JSP90.g6` of `JSPProblem/Finite.lean` (which is `2`-close and not `1`-close to bipartite) every
proper colouring whose colour class meets all odd cycles has a class of size `2`.  (Only the
certificate is used: the *properness* of `c` is not needed for the implication, and it is kept in
the statement because the content of the lemma is that a colour class of a proper colouring is a
certificate.) -/
theorem closeToBipartite_of_oddColorClass {n i : ℕ} (c : V → Fin (n + 1)) (hi : i < n + 1)
    (_hproper : ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) (hcert : OddColorClass G c (⟨i, hi⟩))
    {q : ℕ} (hcard : ((Finset.univ : Finset V).filter
      (fun v => c v = (⟨i, hi⟩ : Fin (n + 1)))).card ≤ q) : CloseToBipartite q G := by
  let Z : Finset V := (Finset.univ : Finset V).filter
    (fun v => c v = (⟨i, hi⟩ : Fin (n + 1)))
  have hZcard : Z.card ≤ q := by
    exact hcard
  have hhits : HitsOddCycles G Z := by
    intro C hC
    refine Finset.nonempty_iff_ne_empty.mp ?_
    obtain ⟨v, hv, hcv⟩ := hcert C hC
    exact ⟨v, Finset.mem_inter.mpr
      ⟨hv, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hcv⟩⟩⟩
  exact (closeToBipartite_iff_hitsOddCycles (m := q)).mpr ⟨Z, hZcard, hhits⟩

theorem erdos73On_of_oddColorClass (k q : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      (∃ (n i : ℕ) (c : W → Fin (n + 1)) (hi : i < n + 1),
        (∀ ⦃u v : W⦄, G.Adj u v → c u ≠ c v) ∧
        OddColorClass G c (⟨i, hi⟩) ∧
        ((Finset.univ : Finset (W)).filter
          (fun v => c v = (⟨i, hi⟩ : Fin (n + 1)))).card ≤ q) → CloseToBipartite q G := by
  intro W instW G' hG h
  obtain ⟨n, i, c, hi, hproper, hcert, hcard⟩ := h
  exact closeToBipartite_of_oddColorClass c hi hproper hcert hcard

/-- **Properness alone is not a certificate**: the odd cycle `C` of `G` is missed by the colour
class of `i` as soon as `C` is long enough, but a proper colouring may well fail to hit it.  The
machine-checked example is `JSP90.g6`, which needs two deletions: no proper colouring of `g6` has a
colour class of size `1` that meets all its odd cycles (`JSP90.not_closeToBipartite_one_g6`). -/
theorem not_closeToBipartite_one_g6' : ¬ CloseToBipartite 1 g6 :=
  not_closeToBipartite_one_g6

end ColorClass

end

end JSP90
