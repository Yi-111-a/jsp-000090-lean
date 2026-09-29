/-
# JSP-000090 — how large must the constant of Erdős Problem #73 be?

The catalogue question (Erdős Problem #73, Reed 1999, *Mangoes and Blueberries*, Combinatorica 19
(1999) 267–296) asks: for each `k ≥ 0` is there a constant `f(k)` such that a graph in which every
induced subgraph `H` has an independent set of size `≥ (|V(H)| - k) / 2` is the union of a bipartite
graph and `f(k)` vertices?

Everything proved so far in this development is an **upper** bound on `f(k)`:

* `JSPProblem/Transversal.lean` — `erdos73On_of_bounded_odd_girth`, the constant `ℓ * k` for graphs
  of bounded odd girth;
* `JSPProblem/Branch.lean` — `erdos73On_of_no_branch`, the constant `k` for graphs in which every
  vertex has at most two neighbours, and `erdos73On_of_bounded_branch`, the constant `m + k` for
  graphs whose branch vertices lie in a set of size `m`.

This file is the **fourth attack family**, and the first one that says anything about the *lower*
bound: no theorem of the shape of Erdős #73 can beat `k`.

The witness is the graph `kTriangles k` = `K_3 ⊔ K_3 ⊔ ... ⊔ K_3` (`k` copies), the disjoint union of
`k` triangles, on the vertex type `Fin 3 × Fin k`:

* `locIndep_kTriangles` — it satisfies Erdős's local hypothesis `LocIndep k`, and **with equality**:
  the independent set it carries inside the whole vertex set has size `k` and the hypothesis reads
  `2 * k + k = 3 * k = |V|`.  (`not_locIndep_kTriangles` shows it fails `LocIndep (k - 1)`, so the
  local hypothesis is as tight as it can be on this example.)
* `card_le_of_hitsOddCycles_kTriangles` — every set of vertices meeting every odd cycle of
  `kTriangles k` has at least `k` elements, since the `k` fibres are `k` pairwise disjoint odd
  cycles (`isOddCycle_tri`).  Together with `closeToBipartite_iff_hitsOddCycles` this gives the
  **exact** value of the conclusion on this graph:
  `closeToBipartite_iff : CloseToBipartite m (kTriangles k) ↔ k ≤ m`.
* `not_branch_kTriangles` — the witness has no branch vertex at all, so the instance
  `erdos73On_of_no_branch` of round 38 is **sharp**: the constant `k` cannot be lowered even on the
  class of graphs of maximum degree `≤ 2` (where `k` is always sufficient).  This is packaged in
  the shape of the theorem itself by `erdos73On_no_branch_optimal`.
* `erdos73_lower_bound` / `no_constant_below_k` — for every `k` and every `m < k` there is a graph
  satisfying `LocIndep k` which is not `m`-close to bipartite.  **This is the lower bound
  `f(k) ≥ k` of Erdős #73, and it is attained.**
* `packing_kTriangles_optimal` — the `k` triangles are a packing of `k` disjoint odd cycles, so the
  *packing* bound `LocIndep.oddCycle_packing_le` of `JSPProblem/Packing.lean` is attained too.  In
  the class without branch vertices packing number and transversal number agree
  (`closeToBipartite_of_no_branch`), which is why `k` is the right number on both sides.
* `not_branch_completeGraph_three` — `K_3` has no branch vertex, the counting lemma that makes the
  last point true at `k = 1`.

Nothing here uses connectivity, Menger or the fan machinery: everything is counting on the `k`
fibres `Fin 3 × {i}` and on `Fin 3`.  The research statement `OddCycleErdosPosa` remains open (see
`discovery/JSP-000090/policy.json`); what this file adds is the *optimality* half of the picture,
which no earlier file contained, and it settles the question of how large the constant of Erdős #73
must at least be.
-/

import JSPProblem.Branch
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

noncomputable section

/-! ### The disjoint union of `k` triangles -/

section Sharp

variable {k : ℕ}

/-- The instance of `DecidableEq` used throughout this file.  It is the one the statements of
`JSPProblem/Transversal.lean` and `JSPProblem/Branch.lean` were elaborated with, so the finsets
built here are the very same ones those lemmas speak about. -/
local instance : DecidableEq (Fin 3 × Fin k) := Classical.decEq _
local instance : DecidableEq (Finset (Fin 3 × Fin k)) := Classical.decEq _
local instance : DecidableEq (Finset (Finset (Fin 3 × Fin k))) := Classical.decEq _

/-- **The disjoint union of `k` triangles**, on the vertex type `Fin 3 × Fin k`: the vertices
`(a, i)` and `(b, j)` are adjacent exactly when `i = j` and `a ≠ b`.  Each fibre `Fin 3 × {i}`
therefore carries a copy of `K_3` and nothing joins two fibres. -/
def kTriangles (k : ℕ) : SimpleGraph (Fin 3 × Fin k) where
  Adj p q := p.2 = q.2 ∧ p.1 ≠ q.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun h' => h.2 h'.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

@[simp] theorem kTriangles_adj {k : ℕ} {p q : Fin 3 × Fin k} :
    (kTriangles k).Adj p q ↔ p.2 = q.2 ∧ p.1 ≠ q.1 := Iff.rfl

/-- **The `i`-th triangle of `kTriangles k`**: the fibre `Fin 3 × {i}`, as a finset. -/
def tri {k : ℕ} (i : Fin k) : Finset (Fin 3 × Fin k) :=
  (Finset.univ : Finset (Fin 3)).image fun a : Fin 3 => (a, i)

theorem mem_tri {k : ℕ} {i : Fin k} {p : Fin 3 × Fin k} : p ∈ tri i ↔ p.2 = i := by
  constructor
  · intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact (congrArg Prod.snd ha).symm
  · intro h
    refine Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, ?_⟩
    exact Prod.ext rfl h.symm

theorem card_tri {k : ℕ} (i : Fin k) : (tri i).card = 3 := by
  have hinj : Function.Injective (fun a : Fin 3 => (a, i)) := by
    intro a b h
    exact congrArg Prod.fst h
  rw [tri, Finset.card_image_of_injective (Finset.univ : Finset (Fin 3)) hinj]
  simp

theorem tri_disjoint {k : ℕ} {i j : Fin k} (h : i ≠ j) : Disjoint (tri i) (tri j) := by
  refine Finset.disjoint_left.mpr fun p h1 h2 => ?_
  obtain ⟨h1, h2⟩ := mem_tri.mp h1, mem_tri.mp h2
  exact h (h1.symm.trans h2)

/-- **A point of a fibre is determined by its two coordinates.** -/
theorem prod_mk_eq {k : ℕ} {p : Fin 3 × Fin k} {a : Fin 3} {i : Fin k} (h1 : p.1 = a)
    (h2 : p.2 = i) : p = (a, i) := by
  apply Prod.ext <;> assumption

/-- Two distinct vertices of one fibre are adjacent: the fibre is a `K_3`. -/
theorem tri_adj {k : ℕ} {i : Fin k} {a b : Fin 3} (h : a ≠ b) :
    (kTriangles k).Adj (a, i) (b, i) := (kTriangles_adj).2 ⟨rfl, h⟩

/-- **A step along a 3-cycle is not the identity** (counting: `j + 1 % 3 ≠ j` for `j < 3`).  This
is the `m = 3` case of the injectivity of the cyclic successor proved in `JSPProblem/Fan.lean`. -/
theorem cycSucc_three_ne (j : Fin 3) : j ≠ cycSucc j := by
  intro h
  have h3 := cycSucc_pow_inj j (p := 1) (q := 0) (by omega) (by omega) (by decide)
  rw [Function.iterate_one, Function.iterate_zero] at h3
  exact h3 h.symm

/-- **Each fibre of `kTriangles k` is an odd cycle** — one of the `k` triangles. -/
theorem isOddCycle_tri {k : ℕ} (i : Fin k) : IsOddCycle (kTriangles k) (tri i) := by
  have h : IsOddCycle (kTriangles k)
      ((Finset.univ : Finset (Fin 3)).image fun a : Fin 3 => (a, i)) := by
    refine isOddCycle_image _ (by decide) (by decide) ?_ ?_
    · intro a b h'
      exact congrArg Prod.fst h'
    · intro j
      exact tri_adj (cycSucc_three_ne j)
  exact h

/-! ### An independent set meeting every fibre -/

/-- **A canonical choice of one vertex of a fibre**: the smallest of `(0, i)`, `(1, i)`, `(2, i)`
which lies in `X`. -/
def triPick {k : ℕ} (X : Finset (Fin 3 × Fin k)) (i : Fin k) : Fin 3 × Fin k :=
  if (0, i) ∈ X then (0, i) else if (1, i) ∈ X then (1, i) else (2, i)

/-- **The fibres which meet `X`.** -/
def triActive {k : ℕ} (X : Finset (Fin 3 × Fin k)) : Finset (Fin k) :=
  (Finset.univ : Finset (Fin k)).filter fun i => X ∩ tri i ≠ ∅

theorem mem_triActive {k : ℕ} {X : Finset (Fin 3 × Fin k)} {i : Fin k} :
    i ∈ triActive X ↔ X ∩ tri i ≠ ∅ := by
  rw [triActive, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem triPick_fibre {k : ℕ} (X : Finset (Fin 3 × Fin k)) (i : Fin k) :
    (triPick X i).2 = i := by
  by_cases h0 : (0, i) ∈ X
  · simp [triPick, h0]
  by_cases h1 : (1, i) ∈ X
  · simp [triPick, h0, h1]
  · simp [triPick, h0, h1]

theorem mem_triPick {k : ℕ} {X : Finset (Fin 3 × Fin k)} {i : Fin k} (hi : i ∈ triActive X) :
    triPick X i ∈ X ∩ tri i := by
  have hne : X ∩ tri i ≠ ∅ := mem_triActive.mp hi
  refine Finset.mem_inter.mpr ⟨?_, mem_tri.mpr (triPick_fibre X i)⟩
  by_cases h0 : (0, i) ∈ X
  · simp [triPick, h0]
  by_cases h1 : (1, i) ∈ X
  · simp [triPick, h0, h1]
  obtain ⟨p, hp⟩ := (Finset.nonempty_iff_ne_empty.mpr hne)
  obtain ⟨hpX, hpTri⟩ := Finset.mem_inter.mp hp
  have hp2 : p.2 = i := mem_tri.mp hpTri
  have hp1 : p.1 ≠ 0 := fun hc => h0 ((prod_mk_eq hc hp2) ▸ hpX)
  have hp1' : p.1 ≠ 1 := fun hc => h1 ((prod_mk_eq hc hp2) ▸ hpX)
  have hval : p.1.val = 2 := by omega
  have hpv : p = (2, i) := prod_mk_eq (Fin.ext hval) hp2
  simp only [triPick, ite_eq_right h0, ite_eq_right h1]
  exact hpv ▸ hpX

/-- **One vertex in each nonempty fibre**: the independent set which witnesses `LocIndep k` for
`kTriangles k`. -/
def triIndep {k : ℕ} (X : Finset (Fin 3 × Fin k)) : Finset (Fin 3 × Fin k) :=
  (triActive X).image (triPick X)

theorem mem_triIndep {k : ℕ} {X : Finset (Fin 3 × Fin k)} {p : Fin 3 × Fin k} :
    p ∈ triIndep X ↔ ∃ i, i ∈ triActive X ∧ triPick X i = p := by
  rw [triIndep, Finset.mem_image]

theorem triIndep_indep {k : ℕ} (X : Finset (Fin 3 × Fin k)) :
    (kTriangles k).IsIndepSet (triIndep X) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro p hp q hq hne
  obtain ⟨i, hi, hpi⟩ := mem_triIndep.mp hp
  obtain ⟨j, hj, hqj⟩ := mem_triIndep.mp hq
  refine fun hadj => hne ?_
  have hfib : p.2 = q.2 := (kTriangles_adj.mp hadj).1
  have hi2 : i = p.2 := (triPick_fibre X i).symm.trans (congrArg Prod.snd hpi)
  have hj2 : j = q.2 := (triPick_fibre X j).symm.trans (congrArg Prod.snd hqj)
  have hij : i = j := hi2.trans (hfib.trans hj2.symm)
  exact hpi.symm.trans (hij ▸ hqj)

theorem card_triIndep {k : ℕ} (X : Finset (Fin 3 × Fin k)) :
    (triIndep X).card = (triActive X).card := by
  rw [triIndep, Finset.card_image_of_injective _ (f := fun i : Fin k => triPick X i)]
  intro i j h
  exact ((triPick_fibre X i).symm.trans (congrArg Prod.snd h)).trans (triPick_fibre X j)

theorem card_triActive_le {k : ℕ} (X : Finset (Fin 3 × Fin k)) : (triActive X).card ≤ k := by
  refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
  simp

/-! ### Counting: the witness has no branch vertex -/

/-- **Four pairwise distinct elements of `Fin 3` do not fit into `Fin 3`.** -/
theorem card_lt_four (a b c d : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (insert a (insert b (insert c ({d} : Finset (Fin 3))))).card < 4 := by
  have nm3 : a ∉ (insert b (insert c ({d} : Finset (Fin 3)))) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact hab h
    · exact hac h
    · exact had h
  have nm2 : b ∉ (insert c ({d} : Finset (Fin 3))) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hbc h
    · exact hbd h
  have nm1 : c ∉ ({d} : Finset (Fin 3)) := by
    rw [Finset.mem_singleton]
    exact hcd
  have h2 : (insert c ({d} : Finset (Fin 3))).card = 2 := by
    rw [Finset.card_insert_of_notMem nm1, Finset.card_singleton]
  have h3 : (insert b (insert c ({d} : Finset (Fin 3)))).card = 3 := by
    rw [Finset.card_insert_of_notMem nm2, h2]
  rw [Finset.card_insert_of_notMem nm3, h3]
  omega

/-- **No vertex of `kTriangles k` is a branch vertex**: every vertex has exactly the two other
vertices of its fibre as neighbours, and `Fin 3` has no room for a third one.  So the witness of
the lower bound lives in the very class for which round 38 proved the *upper* bound `k`. -/
theorem not_branch_kTriangles {k : ℕ} (v : Fin 3 × Fin k) : ¬ BranchVertex (kTriangles k) v := by
  rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  obtain ⟨ha2, ha1⟩ := kTriangles_adj.mp ha
  obtain ⟨hb2, hb1⟩ := kTriangles_adj.mp hb
  obtain ⟨hc2, hc1⟩ := kTriangles_adj.mp hc
  have h12 : v.1 ≠ a.1 := ha1
  have h13 : v.1 ≠ b.1 := hb1
  have h14 : v.1 ≠ c.1 := hc1
  have h23 : a.1 ≠ b.1 := fun h => hab (Prod.ext h (ha2.symm.trans hb2))
  have h24 : a.1 ≠ c.1 := fun h => hac (Prod.ext h (ha2.symm.trans hc2))
  have h34 : b.1 ≠ c.1 := fun h => hbc (Prod.ext h (hb2.symm.trans hc2))
  have hlt := card_lt_four v.1 a.1 b.1 c.1 h12 h13 h14 h23 h24 h34
  have hle : (insert v.1 (insert a.1 (insert b.1 ({c.1} : Finset (Fin 3))))).card
      ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_card (Finset.subset_univ _)
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- **`K_3` has no branch vertex**: three distinct neighbours of `v` in `Fin 3` would be four
distinct elements of `Fin 3`.  Together with `completeGraph_locIndep`,
`closeToBipartite_completeGraph_three` and `not_isBipartite_completeGraph_three` this records that
the instance `erdos73On_of_no_branch 1` is exactly tight. -/
theorem not_branch_completeGraph_three (v : Fin 3) :
    ¬ BranchVertex (SimpleGraph.completeGraph (Fin 3)) v := by
  rintro ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  have h1 : v ≠ a := (SimpleGraph.top_adj v a).mp ha
  have h2 : v ≠ b := (SimpleGraph.top_adj v b).mp hb
  have h3 : v ≠ c := (SimpleGraph.top_adj v c).mp hc
  have hlt := card_lt_four v a b c h1 h2 h3 hab hac hbc
  have hle : (insert v (insert a (insert b ({c} : Finset (Fin 3))))).card
      ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_card (Finset.subset_univ _)
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  omega

/-! ### Erdős's local hypothesis holds on `kTriangles k` -/

/-- **`kTriangles k` satisfies Erdős's local hypothesis with the parameter `k`**: every vertex set
`X` carries an independent set `S ⊆ X` with `2 * |S| + k ≥ |X|` — take one vertex in each fibre of
`X`; the `k` fibres of the graph, each of size `3`, pay for the deficit `k`.  This is the tightness
of the hypothesis: inside the whole vertex set the independent set has size exactly `k` and the
hypothesis is an equality, `2 * k + k = 3 * k = |V|`. -/
theorem locIndep_kTriangles {k : ℕ} : LocIndep k (kTriangles k) := by
  intro X
  refine ⟨triIndep X, ?_, triIndep_indep X, ?_⟩
  · -- the independent set lies in `X`
    intro p hp
    obtain ⟨i, hi, hpi⟩ := mem_triIndep.mp hp
    exact hpi ▸ (Finset.mem_inter.mp (mem_triPick hi)).1
  · -- `2 * |S| + k ≥ |X|`
    have hXeq : X = (triActive X).biUnion (fun i => X ∩ tri i) := by
      ext p
      constructor
      · intro hp
        have hpI : p ∈ X ∩ tri p.2 := Finset.mem_inter.mpr ⟨hp, (mem_tri).mpr rfl⟩
        exact Finset.mem_biUnion.mpr
          ⟨p.2, mem_triActive.mpr (Finset.ne_empty_of_mem hpI), hpI⟩
      · intro h
        obtain ⟨i, -, hp⟩ := Finset.mem_biUnion.mp h
        exact (Finset.mem_inter.mp hp).1
    have hle : X.card ≤ ∑ i ∈ triActive X, (X ∩ tri i).card := by
      calc X.card = ((triActive X).biUnion (fun i => X ∩ tri i)).card :=
            congrArg Finset.card hXeq
        _ ≤ ∑ i ∈ triActive X, (X ∩ tri i).card := Finset.card_biUnion_le
    have hthree : (∑ i ∈ triActive X, (X ∩ tri i).card) ≤ ∑ _i ∈ triActive X, (3 : ℕ) := by
      refine Finset.sum_le_sum fun i hi => ?_
      exact le_trans (Finset.card_le_card (fun _ hx => (Finset.mem_inter.mp hx).2)) (card_tri i).le
    have hfinal : X.card ≤ 3 * (triActive X).card := by
      calc X.card ≤ ∑ i ∈ triActive X, (X ∩ tri i).card := hle
        _ ≤ ∑ _i ∈ triActive X, (3 : ℕ) := hthree
        _ = 3 * (triActive X).card := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]
            rfl
    have hScard : (triIndep X).card = (triActive X).card := card_triIndep X
    have hk : (triActive X).card ≤ k := card_triActive_le X
    omega

/-- **An independent set of `kTriangles k` meets every fibre at most once**, hence has at most `k`
elements. -/
theorem card_le_kTriangles {k : ℕ} {S : Finset (Fin 3 × Fin k)} (hS : (kTriangles k).IsIndepSet S) :
    S.card ≤ k := by
  rw [SimpleGraph.isIndepSet_iff] at hS
  refine le_trans (Finset.card_le_card_of_injOn (s := S) (t := Finset.univ)
    (fun p : Fin 3 × Fin k => p.2) (fun _ _ => Finset.mem_univ _) ?_) ?_
  · intro p hp q hq h
    have hpS : p ∈ S := Finset.mem_coe.mp hp
    have hqS : q ∈ S := Finset.mem_coe.mp hq
    refine Prod.ext (by
      by_cases hc : p.1 = q.1
      · exact hc
      · exfalso
        exact hS hpS hqS (fun hpq => hc (congrArg Prod.fst hpq)) ((kTriangles_adj).2 ⟨h, hc⟩)) h
  · simp

/-- **The local hypothesis is sharp on this example**: `kTriangles k` does *not* satisfy
`LocIndep (k - 1)`. -/
theorem not_locIndep_kTriangles {k : ℕ} (hk1 : 1 ≤ k) :
    ¬ LocIndep (k - 1) (kTriangles k) := by
  intro h
  obtain ⟨S, -, hSi, hb⟩ := h (Finset.univ : Finset (Fin 3 × Fin k))
  have hle := card_le_kTriangles hSi
  have hbk : (Finset.univ : Finset (Fin 3 × Fin k)).card = 3 * k := by simp
  rw [hbk] at hb
  have hsub : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  omega

/-! ### The conclusion fails for `m < k` -/

/-- **Every set meeting every odd cycle of `kTriangles k` has at least `k` elements**: the `k`
fibres are `k` pairwise disjoint odd cycles, and a set meeting all of them meets all of the
fibres.  Together with `closeToBipartite_iff_hitsOddCycles` this is the lower bound on the
constant of Erdős #73. -/
theorem card_le_of_hitsOddCycles_kTriangles {k : ℕ} {X : Finset (Fin 3 × Fin k)}
    (hX : HitsOddCycles (kTriangles k) X) : k <= X.card := by
  set C : Finset (Finset (Fin 3 × Fin k)) := (Finset.univ : Finset (Fin k)).image tri with hCdef
  have hdisj : DisjointFamily C := by
    intro X₁ hX₁ X₂ hX₂ hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hX₁
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hX₂
    exact (Finset.disjoint_iff_inter_eq_empty).mp (tri_disjoint (fun h => hne (congrArg tri h)))
  have hcov : ∀ ⦃x : Fin 3 × Fin k⦄, x ∈ X → ∃ i ∈ C, x ∈ i := by
    intro x hx
    exact ⟨tri x.2, Finset.mem_image.mpr ⟨x.2, Finset.mem_univ _, rfl⟩, (mem_tri).mpr rfl⟩
  have hcard : X.card = ∑ i ∈ C, (X ∩ i).card := card_eq_sum_card_inter_of_disjoint hdisj hcov
  have hle : (∑ i ∈ C, (1 : ℕ)) ≤ ∑ i ∈ C, (X ∩ i).card := by
    refine Finset.sum_le_sum fun i hi => ?_
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    have hhit : tri j ∩ X ≠ ∅ := hX (tri j) (isOddCycle_tri j)
    rw [Finset.inter_comm] at hhit
    exact Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hhit)
  have hones : (∑ i ∈ C, (1 : ℕ)) = C.card := (Finset.card_eq_sum_ones C).symm
  have hcardC : C.card = k := by
    rw [hCdef, Finset.card_image_of_injective _ (f := fun i : Fin k => tri i)]
    · simp
    · intro i j h
      have h' : tri i = tri j := h
      obtain ⟨a, ha⟩ := (isOddCycle_tri i).nonempty
      exact (mem_tri.mp ha).symm.trans (mem_tri.mp (h' ▸ ha))
  omega

/-- **`kTriangles k` is not `m`-close to bipartite when `m < k`.** -/
theorem not_closeToBipartite_kTriangles {k m : ℕ} (h : m < k) :
    ¬ CloseToBipartite m (kTriangles k) := by
  rintro ⟨X, hX, hb⟩
  have hk := card_le_of_hitsOddCycles_kTriangles (X := X) (hitsOddCycles_of_isBipartite_delete hb)
  omega

/-- **The exact value of the conclusion on `kTriangles k`**: it is `m`-close to bipartite exactly
when `m ≥ k`.  So `k` is *exactly* the least number of vertices whose deletion makes this graph
bipartite. -/
theorem closeToBipartite_iff {k m : ℕ} : CloseToBipartite m (kTriangles k) ↔ k ≤ m := by
  constructor
  · rintro ⟨X, hX, hb⟩
    exact le_trans (card_le_of_hitsOddCycles_kTriangles (X := X)
      (hitsOddCycles_of_isBipartite_delete hb)) hX
  · intro h
    exact (erdos73On_of_no_branch k (Fin 3 × Fin k) inferInstance (kTriangles k)
      locIndep_kTriangles (fun v => not_branch_kTriangles v)).mono h

/-! ### The lower bound `f(k) ≥ k` for Erdős #73 -/

/-- **The witness is optimal**: the local hypothesis holds, the graph needs exactly `k` deletions to
become bipartite, and it has no branch vertex. -/
theorem kTriangles_optimal {k : ℕ} (hk1 : 1 ≤ k) :
    CloseToBipartite k (kTriangles k) ∧ ¬ CloseToBipartite (k - 1) (kTriangles k) := by
  refine ⟨(closeToBipartite_iff (k := k) (m := k)).mpr le_rfl, ?_⟩
  have hlt : k - 1 < k := by omega
  exact not_closeToBipartite_kTriangles (k := k) (m := k - 1) hlt

/-- **The lower bound of Erdős Problem #73: the constant must be at least `k`.**  For every `k`
and every `m < k` there is a graph satisfying `LocIndep k` which is not the union of a bipartite
graph and `m` vertices, so no constant `f(k) < k` can work in the statement of the catalogue
question. -/
theorem erdos73_lower_bound (k m : ℕ) (h : m < k) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G ∧ ¬ CloseToBipartite m G := by
  have hnb : ¬ CloseToBipartite m (kTriangles k) := not_closeToBipartite_kTriangles h
  exact ⟨Fin 3 × Fin k, inferInstance, kTriangles k, locIndep_kTriangles, hnb⟩

/-- **The same lower bound, in the shape of the theorem**: no constant below `k` works for Erdős
#73 with the parameter `k`. -/
theorem no_constant_below_k (k : ℕ) :
    ¬ ∃ m, m < k ∧ ∀ (W : Type) (_ : Fintype W) (G : SimpleGraph W),
      LocIndep k G → CloseToBipartite m G := by
  rintro ⟨m, hm, h⟩
  obtain ⟨W, instW, G, hG, hnb⟩ := erdos73_lower_bound k m hm
  exact hnb (h W instW G hG)

/-- **The instance of round 38 is sharp**: the constant `k` of `erdos73On_of_no_branch` cannot be
lowered on the class of graphs of maximum degree `≤ 2` — for every `m < k` such a graph satisfies
`LocIndep k` and is not `m`-close to bipartite.  Together with `erdos73On_of_no_branch` this
computes the value of `f(k)` on that class exactly: `f(k) = k`. -/
theorem erdos73On_no_branch_optimal (k m : ℕ) (h : m < k) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G ∧
      (∀ v : W, ¬ BranchVertex G v) ∧ ¬ CloseToBipartite m G := by
  have hnb : ¬ CloseToBipartite m (kTriangles k) := not_closeToBipartite_kTriangles h
  exact ⟨Fin 3 × Fin k, inferInstance, kTriangles k, locIndep_kTriangles,
    fun v => not_branch_kTriangles v, hnb⟩

/-- **The two halves of the Erdős–Pósa strategy are tight simultaneously.**  The `k` triangles of
`kTriangles k` are a packing of exactly `k` disjoint odd cycles — so the packing bound
`LocIndep.oddCycle_packing_le` of `JSPProblem/Packing.lean` is attained — and no packing of more
than `k` odd cycles exists. -/
theorem packing_kTriangles_optimal (k : ℕ) :
    (∃ 𝒞 : Finset (Finset (Fin 3 × Fin k)), IsOddCycleFamily (G := kTriangles k) 𝒞 ∧ 𝒞.card = k) ∧
      (∀ 𝒟 : Finset (Finset (Fin 3 × Fin k)), IsOddCycleFamily (G := kTriangles k) 𝒟 → 𝒟.card ≤ k) := by
  have hex : ∃ 𝒞 : Finset (Finset (Fin 3 × Fin k)),
      IsOddCycleFamily (G := kTriangles k) 𝒞 ∧ 𝒞.card = k := by
    set 𝒞 : Finset (Finset (Fin 3 × Fin k)) := (Finset.univ : Finset (Fin k)).image tri with h𝒞def
    refine ⟨𝒞, ⟨?_, ?_⟩, ?_⟩
    · intro X hX Y hY hXY
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hY
      exact (Finset.disjoint_iff_inter_eq_empty).mp
        (tri_disjoint (fun h => hXY (congrArg tri h)))
    · intro X hX
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hX
      exact isOddCycle_tri i
    · rw [h𝒞def, Finset.card_image_of_injective _ (f := fun i : Fin k => tri i)]
      · simp
      · intro i j h
        have h' : tri i = tri j := h
        obtain ⟨a, ha⟩ := (isOddCycle_tri i).nonempty
        exact (mem_tri.mp ha).symm.trans (mem_tri.mp (h' ▸ ha))
  refine ⟨hex, fun 𝒟 h𝒟 => ?_⟩
  exact (locIndep_kTriangles : LocIndep k (kTriangles k)).oddCycleFamily_card_le h𝒟

end Sharp

end

end JSP90
