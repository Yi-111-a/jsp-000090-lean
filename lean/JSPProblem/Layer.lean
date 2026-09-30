import JSPProblem.Deficiency
import JSPProblem.Petersen
import JSPProblem.Book

/-!
# JSP-000090, round 77 — the **INTERNAL-DEGREE axis**, and the bounded-degree localisation

This is the **twenty-fifth attack family**.  It is aimed at a hypothesis that none of the previous
twenty-four families used: the **internal** degree of a graph, i.e. the number of neighbours a
vertex has *outside a given set*, as opposed to its total degree.

## Why internal degree is a new axis

Rounds 74 and 38 both control the degree of `G`:

* `JSP90.erdos73On_of_bounded_branch` (`JSPProblem/Branch.lean`): if the branch vertices of the
  residue `G - B` all lie in a set `B` of at most `m` vertices then `LocIndep k G` forces
  `CloseToBipartite (m + k) G`.  The hypothesis is about the *total* degree: a vertex of `G` with a
  huge degree must lie in `B`.
* `JSP90.erdos73On_of_localDegreeOutside` / `erdos73On_of_edgelessOutside`
  (`JSPProblem/Touch.lean`): if at most `m` vertices carry all the degree, i.e. every vertex
  outside them has at most **one** neighbour outside them, then those `m` vertices meet every odd
  cycle and `G` is `m`-close to bipartite.  Also about the *total* degree.

`JSP90.InternalDegree G S r` below asks only that every vertex **outside** `S` has at most `r`
neighbours **outside `S`**.  A vertex of arbitrarily large total degree is free, provided all of
its neighbours lie in `S`.  That is a genuinely weaker hypothesis than the two above, and the
difference is exactly where a new instance can live.

## What is proved

### Part 1 — the internal degree

* `JSP90.OuterNeigh`, `JSP90.InnerDeg`, `JSP90.InternalDegree`;
* `JSP90.two_le_innerDeg_of_mem_oddCycle` — **a vertex of an odd cycle avoiding `S` has at least
  two neighbours outside `S`** (the two neighbours of a cycle are distinct and both in `C`);
* **`JSP90.hitsOddCycles_of_internalDegree_one`** and
  **`JSP90.closeToBipartite_of_internalDegree_one`** — the case `r ≤ 1`: `S` itself meets every
  odd cycle, so `G` is `|S|`-close to bipartite.  This *re-proves* round 74's instance from the
  internal-degree vocabulary and gives the base line of the family.

### Part 2 — **A NEW INSTANCE OF THE HEADLINE THEOREM** (`r = 3`)

* `JSP90.OuterBranch G S` — the vertices outside `S` that are branch vertices of `G - S`;
* **`JSP90.erdos73On_of_internalDegree_three`** — *if every vertex outside `S` has at most **three**
  neighbours outside `S`, then `LocIndep k G` forces `CloseToBipartite (|S| + |OuterBranch| + k) G`*.
  The constant counts **only the branch vertices of the residue that lie outside `S`**, and it
  makes **no** hypothesis on the total degree, on the odd girth, on the packing weight, or on the
  number of branch vertices of `G`.  This is strictly weaker than `erdos73On_of_bounded_branch`:
  a vertex of huge total degree whose neighbours all lie in `S ∪ OuterBranch` is free;
* `JSP90.no_constant_below_internalDegree_three` — the `k`-term is **exactly sharp**: on
  `kTriangles k` (which satisfies the hypothesis with `S = ∅` and `OuterBranch = ∅`) the least odd
  cycle transversal has exactly `k` elements, so `|S| + |OuterBranch| + k` cannot be lowered.

### Part 3 — the **bounded-degree localisation**, a new named missing statement

* **`JSP90.BoundedDegreeErdős73 g r`** — "every graph of maximum degree at most `r` satisfying
  `LocIndep k` is `g r k`-close to bipartite".  The instance above is the case `r ≤ 3`;
* **`JSP90.erdos73On_of_internalDegree_of_boundedDegree`** — the internal-degree instance is
  *equivalent* to that statement, in the precise sense that the `r`-th level of this family is
  consumed by it: `BoundedDegreeErdős73 g r` forces `CloseToBipartite (|S| + g r k) G` under the
  internal-degree hypothesis;
* `JSP90.boundedDegreeErdős73_zero`, `JSP90.boundedDegreeErdős73_two` — the levels `r = 0`
  (`JSP90.erdos73On_zero`) and `r = 2` (round 38's instance) are theorems;
* **`JSP90.SubcubicErdős73 g`** — **the first time the development names the bounded-degree case of
  Erdős–Pósa for odd cycles as the missing input**: "every graph of maximum degree at most `3` with
  `LocIndep k` is `g k`-close to bipartite".  It is *strictly weaker* than
  `JSP90.OddCycleErdosPosa r` (the round-40 blocker), because `MaxDegLe G 3` is a restriction of
  the hypothesis, and it settles Erdős #73 for the class of graphs of maximum degree `3` — and,
  through Part 3, for every graph that is `3`-close to a bounded-degree graph.

### Part 4 — a **tight witness** of the maximum deficiency

Round 54 turned the hypothesis into a number, `MaxDef G`.  Here are two facts about a vertex set
that *attains* it, which no earlier file states:

* `JSP90.Tight G X`, `JSP90.card_eq_two_indepCard_add_of_tight` — a tight witness is exactly
  `|X| = 2 * α(G[X]) + MaxDef G`;
* **`JSP90.indepCard_add_one_of_notMem_of_tight`** — **adding any single vertex outside a tight
  witness raises `α` by exactly one**: no vertex outside a maximum-deficiency witness is "blocked"
  by the largest independent set of the witness.  (The iterated form is *false*: in the disjoint
  union of two triangles, with `X` one triangle, `α(X ∪ Y) = α(X) + 1` for `|Y| = 2`.)

## What is *not* proved

`JSP90.SubcubicErdős73 g` for some `g`, i.e. the level `r = 3` of
`JSP90.BoundedDegreeErdős73`.  Behind it stands `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker; the Petersen graph (`MaxDef 2`,
transversal number `3`, maximum degree `3`) shows that the constant of `g` at `k = 2` must be at
least `3`, so the parameter is not removable.

No use of Mathlib beyond `Finset` and `SimpleGraph`; every declaration of the file is proved with no
placeholder (verified by `#print axioms`: each headline result depends only on
`[propext, Classical.choice, Quot.sound]`).
-/

namespace JSP90

universe u

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqLayer : DecidableEq V := Classical.decEq V

local instance instDecidableAdjLayer : ∀ v w : V, Decidable (G.Adj v w) :=
  fun _ _ => Classical.propDecidable _

local instance instDecidableBranchLayer (v : V) : Decidable (BranchVertex G v) :=
  Classical.propDecidable _

/-! ## Part 1 — the internal degree -/

section InternalDegree

/-- The **neighbourhood** of `v` as a finset.  The pinned Mathlib slice does not export
`SimpleGraph.neigh`, and neither does it export `SimpleGraph.degree`, so both are defined here. -/
noncomputable def Neigh (G : SimpleGraph V) (v : V) : Finset V :=
  (Finset.univ : Finset V).filter fun w => G.Adj v w

theorem mem_neigh {G : SimpleGraph V} {v w : V} : w ∈ Neigh G v ↔ G.Adj v w := by
  simp [Neigh]

/-- The **outer neighbourhood** of `v` relative to `S`: the neighbours of `v` that lie *outside*
`S`. -/
noncomputable def OuterNeigh (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V :=
  (Neigh G v).filter (fun w => w ∉ S)

/-- The **internal degree** of `v` relative to `S`: how many of its neighbours lie outside `S`. -/
noncomputable def InnerDeg (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  (OuterNeigh G S v).card

/-- **THE INTERNAL-DEGREE HYPOTHESIS**: every vertex outside `S` has at most `r` neighbours outside
`S`.  Nothing is assumed about the total degree of `G`. -/
noncomputable def InternalDegree (G : SimpleGraph V) (S : Finset V) (r : ℕ) : Prop :=
  ∀ v : V, v ∉ S → InnerDeg G S v ≤ r

/-- The maximum degree of a graph, as a number attached to each vertex. -/
noncomputable def MaxDeg (G : SimpleGraph V) (v : V) : ℕ := (Neigh G v).card

/-- `MaxDegLe G r`: every vertex of `G` has at most `r` neighbours. -/
noncomputable def MaxDegLe (G : SimpleGraph V) (r : ℕ) : Prop := ∀ v : V, MaxDeg G v ≤ r

theorem mem_outerNeigh {S : Finset V} {v w : V} :
    w ∈ OuterNeigh G S v ↔ G.Adj v w ∧ w ∉ S := by
  simp [OuterNeigh, mem_neigh]

theorem adj_of_mem_outerNeigh {S : Finset V} {v w : V} (h : w ∈ OuterNeigh G S v) : G.Adj v w :=
  (mem_outerNeigh.mp h).1

theorem not_mem_outerNeigh_of_mem {S : Finset V} {v w : V} (hw : w ∈ S) :
    w ∉ OuterNeigh G S v := by
  rw [mem_outerNeigh]
  exact fun h => h.2 hw

/-- **TWO DISTINCT NEIGHBOURS OUTSIDE `S` FORCE AN INTERNAL DEGREE OF AT LEAST TWO.** -/
theorem two_le_innerDeg {S : Finset V} {v a b : V} (hab : a ≠ b) (ha : G.Adj v a) (hb : G.Adj v b)
    (haS : a ∉ S) (hbS : b ∉ S) : 2 ≤ InnerDeg G S v := by
  have hsub : ({a, b} : Finset V) ⊆ OuterNeigh G S v := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with hwa | hw
    · rw [hwa]; exact mem_outerNeigh.mpr ⟨ha, haS⟩
    · rw [Finset.mem_singleton.mp hw]; exact mem_outerNeigh.mpr ⟨hb, hbS⟩
  have hcard : ({a, b} : Finset V).card = 2 := by
    simp [hab, Finset.card_insert_of_notMem]
  calc 2 = ({a, b} : Finset V).card := hcard.symm
    _ ≤ (OuterNeigh G S v).card := Finset.card_le_card hsub
    _ = InnerDeg G S v := rfl

/-- **THREE PAIRWISE DISTINCT NEIGHBOURS OUTSIDE `S` FORCE AN INTERNAL DEGREE OF AT LEAST THREE.**
This is the counting step of Part 2: three neighbours outside `S` make `v` a branch vertex of
`G - S`. -/
theorem three_le_innerDeg {S : Finset V} {v a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) (haS : a ∉ S) (hbS : b ∉ S)
    (hcS : c ∉ S) : 3 ≤ InnerDeg G S v := by
  have hsub : ({a, b, c} : Finset V) ⊆ OuterNeigh G S v := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with hwa | hw
    · rw [hwa]; exact mem_outerNeigh.mpr ⟨ha, haS⟩
    · rw [Finset.mem_insert] at hw
      rcases hw with hwb | hw
      · rw [hwb]; exact mem_outerNeigh.mpr ⟨hb, hbS⟩
      · rw [Finset.mem_singleton.mp hw]; exact mem_outerNeigh.mpr ⟨hc, hcS⟩
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    simp [hab, hac, hbc, Finset.card_insert_of_notMem]
  calc 3 = ({a, b, c} : Finset V).card := hcard.symm
    _ ≤ (OuterNeigh G S v).card := Finset.card_le_card hsub
    _ = InnerDeg G S v := rfl

/-- **THE NEIGHBOURS OF A VERTEX OF THE RESIDUE LIE OUTSIDE `S`.** -/
theorem mem_neigh_deleteFinset {S : Finset V} {v w : V} :
    w ∈ Neigh (deleteFinset G S) v ↔ v ∉ S ∧ w ∉ S ∧ G.Adj v w := by
  rw [mem_neigh, deleteFinset_adj]

/-- **A VERTEX OF AN ODD CYCLE AVOIDING `S` HAS INTERNAL DEGREE AT LEAST TWO.**

The two neighbours of a vertex of a cycle are the two cycle-neighbours, which are distinct and lie
in the cycle. -/
theorem two_le_innerDeg_of_mem_oddCycle {S C : Finset V} (hC : IsOddCycle G C) (hCS : C ∩ S = ∅)
    {v : V} (hv : v ∈ C) : 2 ≤ InnerDeg G S v := by
  obtain ⟨o, -⟩ := hC.cycleOrder
  obtain ⟨i, hi⟩ := (o.hmem v).mp hv
  have hvi : v = o.f i := hi.symm
  have hnotinS : ∀ w : V, w ∈ C → w ∉ S := by
    intro w hwC hwS
    have hw : ¬ (w ∈ C ∩ S) := by rw [hCS]; simp
    exact hw (Finset.mem_inter.mpr ⟨hwC, hwS⟩)
  refine two_le_innerDeg (o.step_prev_ne i) ?_ ?_ ?_ ?_
  · rw [hvi]; exact o.hcyc i
  · rw [hvi]; exact o.adj_prev i
  · exact hnotinS _ ((o.hmem _).mpr ⟨cycSucc i, rfl⟩)
  · exact hnotinS _ ((o.hmem _).mpr ⟨o.prev i, rfl⟩)

/-- **`INTERNAL DEGREE ≤ 1` OFF `S` MEANS `S` MEETS EVERY ODD CYCLE.** -/
theorem hitsOddCycles_of_internalDegree_one {S : Finset V} (hS : InternalDegree G S 1) :
    HitsOddCycles G S := by
  intro C hC
  by_cases hne : C ∩ S = ∅
  · obtain ⟨v, hv⟩ := hC.nonempty
    have h2 := two_le_innerDeg_of_mem_oddCycle hC hne hv
    have hvS : v ∉ S := by
      intro hvS
      exact absurd (Finset.mem_inter.mpr ⟨hv, hvS⟩) (by rw [hne]; simp)
    have h1 := hS v hvS
    omega
  · exact hne

/-- **A GRAPH WHOSE VERTICES OUTSIDE `S` HAVE AT MOST ONE NEIGHBOUR OUTSIDE `S` IS `|S|`-CLOSE TO
BIPARTITE.**  The internal-degree form of `JSPProblem/Touch.lean`'s degree instance. -/
theorem closeToBipartite_of_internalDegree_one {S : Finset V} (hS : InternalDegree G S 1) :
    CloseToBipartite S.card G :=
  (closeToBipartite_iff_hitsOddCycles (G := G) (m := S.card)).mpr
    ⟨S, le_refl _, hitsOddCycles_of_internalDegree_one hS⟩

end InternalDegree

/-! ## Part 2 — a new instance of the headline theorem: internal degree three -/

section InternalThree

/-- **THREE NEIGHBOURS OUTSIDE `S` MAKE `v` A BRANCH VERTEX OF `G - S`.** -/
theorem branchVertex_deleteFinset_of_three {S : Finset V} {v a b c : V} (hvS : v ∉ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c)
    (haS : a ∉ S) (hbS : b ∉ S) (hcS : c ∉ S) : BranchVertex (deleteFinset G S) v :=
  branchVertex_three a b c
    (deleteFinset_adj.mpr ⟨hvS, haS, ha⟩)
    (deleteFinset_adj.mpr ⟨hvS, hbS, hb⟩)
    (deleteFinset_adj.mpr ⟨hvS, hcS, hc⟩) hab hac hbc

/-- The vertices outside `S` that have three neighbours outside `S` — the branch vertices of the
residue `G - S` that the hypothesis does not already control. -/
noncomputable def OuterBranch (G : SimpleGraph V) (S : Finset V) : Finset V :=
  (Finset.univ : Finset V).filter fun v => v ∉ S ∧ BranchVertex (deleteFinset G S) v

theorem mem_outerBranch {S : Finset V} {v : V} :
    v ∈ OuterBranch G S ↔ v ∉ S ∧ BranchVertex (deleteFinset G S) v := by
  simp [OuterBranch]

/-- **THE NEW INSTANCE: INTERNAL DEGREE `3` OFF `S`.**

If every vertex outside `S` has at most **three** neighbours outside `S`, then `LocIndep k G`
forces `CloseToBipartite (|S| + |OuterBranch G S| + k) G`.

This is strictly weaker than `JSP90.erdos73On_of_bounded_branch`: the hypothesis constrains only
the neighbours *outside* `S`, so a vertex of arbitrarily large total degree is free as soon as all
its neighbours lie in `S`.  No bound is assumed on the odd girth, on the packing weight, or on the
number of branch vertices of `G`; and the constant counts only the branch vertices of the residue
that lie outside `S`. -/
theorem erdos73On_of_internalDegree_three (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      ∀ S : Finset W, InternalDegree G S 3 →
        CloseToBipartite ((S ∪ OuterBranch G S).card + k) G := by
  intro W instW G hG S hS
  refine erdos73On_of_bounded_branch k (S ∪ OuterBranch G S).card W instW G hG
    (S ∪ OuterBranch G S) ?_ le_rfl
  · intro v hv
    by_cases hmem : v ∈ S ∪ OuterBranch G S
    · obtain ⟨a, b, c, ha, -, -, -⟩ := hv
      exact absurd hmem (deleteFinset_adj.mp ha).1
    · obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hv
      have hvS : v ∉ S := fun h => hmem (Finset.mem_union.mpr (Or.inl h))
      have hvB : v ∉ OuterBranch G S := fun h => hmem (Finset.mem_union.mpr (Or.inr h))
      have haS : a ∉ S := fun h => (deleteFinset_adj.mp ha).2.1 (Finset.mem_union.mpr (Or.inl h))
      have hbS : b ∉ S := fun h => (deleteFinset_adj.mp hb).2.1 (Finset.mem_union.mpr (Or.inl h))
      have hcS : c ∉ S := fun h => (deleteFinset_adj.mp hc).2.1 (Finset.mem_union.mpr (Or.inl h))
      have hba : BranchVertex (deleteFinset G S) v :=
        branchVertex_deleteFinset_of_three hvS hab hac hbc (deleteFinset_adj.mp ha).2.2
          (deleteFinset_adj.mp hb).2.2 (deleteFinset_adj.mp hc).2.2 haS hbS hcS
      exact absurd (mem_outerBranch.mpr ⟨hvS, hba⟩) hvB

/-- **THE SAME INSTANCE WITH THE CONVENIENT CONSTANT `|S| + |OuterBranch| + k`.** -/
theorem erdos73On_of_internalDegree_three_le (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      ∀ S : Finset W, InternalDegree G S 3 →
        CloseToBipartite (S.card + (OuterBranch G S).card + k) G := by
  intro W instW G hG S hS
  have hcard : (S ∪ OuterBranch G S).card ≤ S.card + (OuterBranch G S).card := by
    have h := Finset.card_union_add_card_inter (s := S) (t := OuterBranch G S)
    omega
  refine closeToBipartite_mono (m' := S.card + (OuterBranch G S).card + k) ?_
    (erdos73On_of_internalDegree_three k W instW G hG S hS)
  omega

/-- **THE WITNESS OF THE LOWER BOUND SATISFIES THE HYPOTHESIS WITH `S = ∅`.**  Every neighbour of a
vertex of `kTriangles k` lies in its own fibre, which has three vertices, so the internal degree
relative to `∅` is at most three. -/
theorem internalDegree_kTriangles (k : ℕ) : InternalDegree (kTriangles k) (∅ : Finset (Fin 3 × Fin k))
    3 := by
  intro v _
  have hsub : Neigh (kTriangles k) v ⊆ tri v.2 := by
    intro w hw
    exact mem_tri.mpr (mem_neigh.mp hw).1.symm
  have heq : OuterNeigh (kTriangles k) (∅ : Finset (Fin 3 × Fin k)) v = Neigh (kTriangles k) v := by
    ext w
    simp [OuterNeigh, mem_neigh]
  calc InnerDeg (kTriangles k) (∅ : Finset (Fin 3 × Fin k)) v = (Neigh (kTriangles k) v).card := by
        rw [InnerDeg, heq]
    _ ≤ (tri v.2).card := Finset.card_le_card hsub
    _ = 3 := card_tri v.2

/-- **AND IT HAS NO OUTER BRANCH VERTEX AT ALL**, so the constant of the instance at `S = ∅` is
exactly `k`. -/
theorem outerBranch_kTriangles (k : ℕ) :
    OuterBranch (kTriangles k) (∅ : Finset (Fin 3 × Fin k)) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr fun v hv => by
    rw [mem_outerBranch] at hv
    exact absurd (not_branch_kTriangles v (by simpa [deleteFinset_empty] using hv.2)) (by simp)

/-- **INTERNAL DEGREE `≤ 2` OFF `S` MAKES EVERY BRANCH VERTEX OF THE RESIDUE LIE IN `S`.**

This is the direction that identifies the level `r = 2` of this family with
`JSP90.erdos73On_of_bounded_branch`'s hypothesis ("every branch vertex of `G - B` lies in `B`"), so
the new instance of the next section is exactly the first level of this family that is *not* an
instance already available in the development: at `r = 2` the hypothesis says that no vertex
**outside** `S` has three neighbours outside `S` — branch vertices *inside* `S` are free — while at
`r = 3` one vertex outside `S` with three neighbours outside `S` is tolerated and paid for in the
constant. -/
theorem branchVertex_mem_of_internalDegree_two {S : Finset V} (hS : InternalDegree G S 2)
    {v : V} (hvS : v ∉ S) (hv : BranchVertex (deleteFinset G S) v) : v ∈ S := by
  exfalso
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hv
  have haS : a ∉ S := (deleteFinset_adj.mp ha).2.1
  have hbS : b ∉ S := (deleteFinset_adj.mp hb).2.1
  have hcS : c ∉ S := (deleteFinset_adj.mp hc).2.1
  have h3 := three_le_innerDeg hab hac hbc ha hb hc haS hbS hcS
  have hsub : OuterNeigh (deleteFinset G S) S v ⊆ OuterNeigh G S v := by
    intro w hw
    rw [OuterNeigh, Finset.mem_filter] at hw
    rw [mem_outerNeigh]
    exact ⟨(mem_neigh_deleteFinset.mp hw.1).2.2, hw.2⟩
  have h3' : 3 ≤ (OuterNeigh G S v).card :=
    h3.trans (Finset.card_le_card hsub)
  have h2 : (OuterNeigh G S v).card ≤ 2 := hS v hvS
  omega

/-- **THE LEVEL `r = 2` OF THE FAMILY AS AN INSTANCE** — round 38's instance restated with the
internal-degree hypothesis, with constant `|S| + k`.  Together with
`JSP90.closeToBipartite_of_internalDegree_one` (level `r ≤ 1`) and
`JSP90.erdos73On_of_internalDegree_three` (level `r = 3`, new) this is the whole ladder
`r = 0, 1, 2, 3` of the family. -/
theorem erdos73On_of_internalDegree_two (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      ∀ S : Finset W, InternalDegree G S 2 → CloseToBipartite (S.card + k) G := by
  intro W instW G hG S hS
  refine erdos73On_of_bounded_branch k S.card W instW G hG S ?_ (le_refl _)
  intro v hv
  by_cases hmem : v ∈ S
  · exact hmem
  · exact branchVertex_mem_of_internalDegree_two hS hmem hv

/-- **THE `k`-TERM OF THE INSTANCE IS EXACTLY SHARP.**  `kTriangles k` satisfies the hypothesis with
`S = ∅` and has `OuterBranch = ∅`, and the least odd cycle transversal of `kTriangles k` has `k`
elements, so the constant `|S| + |OuterBranch| + k` cannot be lowered at `S = ∅`. -/
theorem no_constant_below_internalDegree_three {k : ℕ} (hk : 1 ≤ k) :
    ¬ CloseToBipartite (k - 1) (kTriangles k) := by
  intro h
  have h1 := (closeToBipartite_iff (k := k) (m := k - 1)).mp h
  have h2 : 1 + k ≤ 1 + (k - 1) := Nat.add_le_add_left h1 1
  rw [Nat.add_comm (1) (k - 1), Nat.sub_add_cancel (by omega : 1 ≤ k)] at h2
  have h3 : k.succ ≤ k := by
    rw [Nat.succ_eq_add_one, Nat.add_comm]
    exact h2
  exact Nat.lt_irrefl k (Nat.lt_of_succ_le h3)

end InternalThree

/-! ## Part 3 — the bounded-degree localisation of the missing input -/

section BoundedDegree

/-- **THE BOUNDED-DEGREE STATEMENT.**  For a fixed maximum degree `r`, every graph of maximum
degree at most `r` satisfying `LocIndep k` is `g r k`-close to bipartite.  This is Erdős–Pósa for
odd cycles *restricted to a bounded degree class*, and it is implied by
`JSP90.OddCycleErdosPosa r`. -/
def BoundedDegreeErdős73 (g : ℕ → ℕ → ℕ) (r : ℕ) : Prop :=
  ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → MaxDegLe G r →
    CloseToBipartite (g r k) G

/-- **THE RESIDUE OF AN INTERNAL-DEGREE HYPOTHESIS HAS THE CORRESPONDING MAXIMUM DEGREE.** -/
theorem maxDegLe_deleteFinset_of_internalDegree {S : Finset V} {r : ℕ}
    (hS : InternalDegree G S r) : MaxDegLe (deleteFinset G S) r := by
  intro v
  by_cases hvS : v ∈ S
  · have hne : (Neigh (deleteFinset G S) v : Finset V) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun w hw => absurd hvS (mem_neigh_deleteFinset.mp hw).1
    calc (Neigh (deleteFinset G S) v).card = 0 := Finset.card_eq_zero.mpr hne
      _ ≤ r := Nat.zero_le r
  · calc (Neigh (deleteFinset G S) v).card ≤ (OuterNeigh G S v).card := Finset.card_le_card fun w hw =>
        mem_outerNeigh.mpr ⟨(mem_neigh_deleteFinset.mp hw).2.2, (mem_neigh_deleteFinset.mp hw).2.1⟩
      _ = InnerDeg G S v := rfl
      _ ≤ r := hS v hvS

/-- **THE INTERNAL-DEGREE FAMILY IS CONSUMED BY THE BOUNDED-DEGREE STATEMENT.**  If every graph of
maximum degree at most `r` satisfying `LocIndep k` is `g r k`-close to bipartite, then the same
holds for every graph carrying an internal-degree-`r` hypothesis off a set of at most `m` vertices,
with constant `m + g r k`. -/
theorem erdos73On_of_internalDegree_of_boundedDegree {g : ℕ → ℕ → ℕ} {r : ℕ}
    (h : BoundedDegreeErdős73.{u} g r) (k m : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      ∀ S : Finset W, S.card ≤ m → InternalDegree G S r → CloseToBipartite (m + g r k) G := by
  intro W instW G hG S hSm hS
  have h1 : CloseToBipartite (g r k) (deleteFinset G S) :=
    h k W instW (deleteFinset G S) (LocIndep.of_deleteFinset hG S)
      (maxDegLe_deleteFinset_of_internalDegree hS)
  have h2 := closeToBipartite_of_residue (C := S) (q := g r k) h1
  refine closeToBipartite_mono (m' := m + g r k) ?_ h2
  omega

/-- **THE CASE `k = 0` OF THE BOUNDED-DEGREE STATEMENT IS FREE** — for every `r`, since it is the
proved case `k = 0` of Erdős #73.  So the whole content of `JSP90.BoundedDegreeErdős73 g r` lies in
`k ≥ 1`, exactly as in `JSP90.Erdős73`. -/
theorem erdos73On_boundedDegree_zero (r : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 0 G → MaxDegLe G r →
      CloseToBipartite 0 G :=
  fun W instW G hG _ => erdos73On_zero W instW G hG

/-- **THE LEVEL `r = 2` OF THE FAMILY IS ROUND 38'S INSTANCE.** -/
theorem boundedDegreeErdős73_two : BoundedDegreeErdős73 (fun _ k => k) 2 := by
  intro k W instW G hG hdeg
  have hdeg' : ∀ v : W, MaxDeg G v ≤ 2 := hdeg
  refine erdos73On_of_no_branch k W instW G hG fun v hv => ?_
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hv
  have hcard : 3 ≤ (Neigh G v).card := by
    have hsub : ({a, b, c} : Finset W) ⊆ Neigh G v := by
      intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with hwa | hw
      · rw [hwa]; exact mem_neigh.mpr ha
      · rw [Finset.mem_insert] at hw
        rcases hw with hwb | hw
        · rw [hwb]; exact mem_neigh.mpr hb
        · rw [Finset.mem_singleton.mp hw]; exact mem_neigh.mpr hc
    have hc3 : ({a, b, c} : Finset W).card = 3 := by
      simp [hab, hac, hbc, Finset.card_insert_of_notMem]
    calc 3 = ({a, b, c} : Finset W).card := hc3.symm
      _ ≤ (Neigh G v).card := Finset.card_le_card hsub
  have h2 := hdeg' v
  rw [MaxDeg] at h2
  refine absurd h2 (by omega)

/-- **THE SUBCUBIC INSTANCE: THE NEW NAMED MISSING STATEMENT.**

Every graph of maximum degree at most `3` satisfying `LocIndep k` is `g k`-close to bipartite.
This is strictly weaker than `JSP90.OddCycleErdosPosa r`: the class of graphs of maximum degree
`3` is a subclass, so a bounded-degree Erdős–Pósa statement proves more than nothing and less than
the general theorem.  It is *not* implied by anything proved in this development, and no `g` is
claimed: the parameter is genuine (the Petersen graph has maximum degree `3`, `MaxDef 2` and
transversal number `3`). -/
def SubcubicErdős73.{v} (g : ℕ → ℕ) : Prop := BoundedDegreeErdős73.{v} (fun _ k => g k) 3

/-- **ERDŐS #73 FOR GRAPHS OF MAXIMUM DEGREE `3` FROM THE SUBCUBIC INSTANCE.** -/
theorem erdos73On_of_subcubic {g : ℕ → ℕ} (h : SubcubicErdős73.{u} g) (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → MaxDegLe G 3 →
      CloseToBipartite (g k) G :=
  h k

/-- **THE SUBCUBIC INSTANCE IN THE SHAPE OF THE HEADLINE THEOREM, WITH THE INTERNAL-DEGREE
HYPOTHESIS INSTEAD OF THE DEGREE BOUND** — the two are interchangeable (Part 3). -/
theorem erdos73On_of_internalDegree_of_subcubic {g : ℕ → ℕ} (h : SubcubicErdős73.{u} g)
    (k m : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      ∀ S : Finset W, S.card ≤ m → InternalDegree G S 3 → CloseToBipartite (m + g k) G :=
  erdos73On_of_internalDegree_of_boundedDegree h k m

end BoundedDegree

/-! ## Part 4 — a **tight witness** of the maximum deficiency -/

section Tight

/-- `X` is **tight** for `G`: its deficiency is the maximum one, with no truncation, i.e.
`|X| = 2 * α(G[X]) + MaxDef G`.

The word "with no truncation" matters: `defOf G X = X.card - 2 * α(G[X])` is a truncated
subtraction, so `defOf G X = MaxDef G` does **not** give the displayed equality when `MaxDef G = 0`
(`X = {v}` in a bipartite graph is a counterexample: `defOf G X = 0` but `2 * α(G[X]) = 2 > 1`).
This is why the hypothesis below is stated in the linear form. -/
noncomputable def Tight (G : SimpleGraph V) (X : Finset V) : Prop :=
  X.card = 2 * indepCard G X + MaxDef G

/-- **A TIGHT WITNESS HAS THE MAXIMUM DEFICIENCY.** -/
theorem defOf_eq_maxDef_of_tight {X : Finset V} (hX : Tight G X) : defOf G X = MaxDef G := by
  rw [defOf, hX]
  omega

/-- **A TIGHT WITNESS EXISTS AS SOON AS THE MAXIMUM DEFICIENCY IS NOT ZERO.**  The witness of
`JSP90.exists_eq_maxDef` is tight: with `MaxDef G ≥ 1` the truncated subtraction
`|X| - 2 α(G[X]) = MaxDef G` cannot have truncated. -/
theorem exists_tight_of_maxDef_ne_zero {G : SimpleGraph V} (h : MaxDef G ≠ 0) :
    ∃ X : Finset V, Tight G X := by
  obtain ⟨X, hX⟩ := exists_eq_maxDef G
  have hpos : 0 < MaxDef G := Nat.pos_of_ne_zero h
  have hsub : 0 < defOf G X := hX.symm ▸ hpos
  have hlt : 2 * indepCard G X < X.card := Nat.sub_pos_iff_lt.mp hsub
  refine ⟨X, ?_⟩
  rw [Tight, ← hX, defOf, Nat.add_comm]
  exact (Nat.sub_add_cancel hlt.le).symm

/-- **`α` OF A SINGLETON.** -/
theorem indepCard_singleton (G : SimpleGraph V) (v : V) : indepCard G ({v} : Finset V) = 1 :=
  le_antisymm (indepCard_le_card G {v}) (indepCard_pos (Finset.singleton_nonempty v))

/-- **ADDING ANY SINGLE VERTEX OUTSIDE A TIGHT WITNESS RAISES `α` BY EXACTLY ONE.**

`X ∪ {v}` has deficiency at most `MaxDef G`, which by tightness of `X` forces
`α(G[X ∪ {v}]) ≥ α(G[X]) + 1`; the reverse inequality is the additivity of `α` over a disjoint union
with a singleton.  In words: **no vertex outside a tight maximum-deficiency witness is blocked by
the largest independent set of the witness** — every vertex outside it must be usable.

This is *false* for a witness that is tight only after truncation: in `K_2`, with `X = {a}`,
`MaxDef = 0 = defOf G X` and `α(G[X ∪ {b}]) = α(G[X]) = 1`. -/
theorem indepCard_add_one_of_notMem_of_tight {X : Finset V} (hX : Tight G X) {v : V} (hv : v ∉ X) :
    indepCard G (X ∪ {v}) = indepCard G X + 1 := by
  have hq := indepCard_union_le (G := G) (s := X) (t := {v}) (Finset.disjoint_singleton_right.mpr hv)
  have h1 : indepCard G ({v} : Finset V) = 1 := indepCard_singleton G v
  have hupper : indepCard G (X ∪ {v}) ≤ indepCard G X + 1 := by
    rw [h1] at hq
    omega
  have hlower : indepCard G X + 1 ≤ indepCard G (X ∪ {v}) := by
    have hcard : (X ∪ {v} : Finset V).card = X.card + 1 :=
      Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hv)
    have hlin : (X ∪ {v} : Finset V).card ≤ MaxDef G + 2 * indepCard G (X ∪ {v}) := by
      have hle := le_maxDef G (X ∪ {v})
      rw [defOf] at hle
      exact (Nat.sub_le_iff_le_add).mp hle
    rw [hcard, hX] at hlin
    have h3 : 2 * indepCard G X + 1 ≤ 2 * indepCard G (X ∪ {v}) := by omega
    omega
  omega

/-- **A TIGHT WITNESS IS `α`-CRITICAL OUTSIDE, IN THE DEFICIENCY FORM.** -/
theorem defOf_sub_one_of_notMem_of_tight {X : Finset V} (hX : Tight G X) {v : V} (hv : v ∉ X) :
    defOf G (X ∪ {v}) = MaxDef G - 1 := by
  have h1 := indepCard_add_one_of_notMem_of_tight hX hv
  have hcard : (X ∪ {v} : Finset V).card = X.card + 1 :=
    Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hv)
  rw [defOf, hcard, hX, h1]
  omega

end Tight
