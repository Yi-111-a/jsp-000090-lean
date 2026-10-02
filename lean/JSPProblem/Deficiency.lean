/-
# JSP-000090, round 54 — **the maximum deficiency: the numerical form of Erdős's hypothesis**

## What this file is

Rounds 40–48 attacked Erdős Problem #73 through **decompositions** (residues, 2-cuts, connected
components, 1-cuts) and rounds 46/53 attacked the **Erdős–Pósa function itself** (the identity
function on the class of graphs with pairwise disjoint odd cycles; minimal transversals and their
critical intersection graph).  Every one of those attacks needs the hypothesis of the problem,
`LocIndep k G`, and every one of them uses it in exactly one way: to bound the number of
vertex-disjoint odd cycles (`JSP90.LocIndep.oddCycle_packing_le`).

`LocIndep k G` is, however, a statement with a *universal quantifier over all vertex sets*:

```lean
LocIndep k G = ∀ X ⊆ V, ∃ S ⊆ X, G.IsIndepSet S ∧ 2 * |S| + k ≥ |X|
```

This file is the **eleventh attack family**: it replaces that universal statement by a single
**natural number attached to `G`** — the *maximum deficiency*

```lean
MaxDef G = max { |X| - 2 * α(G[X]) : X ⊆ V }
```

i.e. the largest amount by which a subgraph of `G` fails to be "half independent".  The classical
name for `|H| - 2 * α(H)` is the *deficiency* of `H`; Reed's condition "every subgraph `H` has
`α(H) ≥ (|H| - k) / 2`" says precisely that `G` has deficiency at most `k`.

Why this is worth having:

* **`LocIndep k G ↔ MaxDef G ≤ k`** (`locIndep_iff_maxDef_le`, Part 2).  The hypothesis of
  JSP-000090 becomes a *numerical* bound on a *function of `G`*, which is what an induction on `|V|`,
  a minimal-counterexample argument or any "pass the bound on" step needs.  The already-proved
  witnesses transfer by one line (Part 4: `MaxDef (kTriangles k) = k`; Part 5:
  `MaxDef (K_n) = n - 2` for `n ≥ 2`).
* **The sandwich `ν(G) ≤ MaxDef G ≤ τ(G)`** (`packing_le_maxDef_le_transversal`, Part 3): every
  packing of odd cycles is at most as large as the maximum deficiency, which is at most every odd
  cycle transversal.  The left inequality is the packing bound in numerical form; the right
  inequality is *new* and is proved here combinatorially.  This is precisely the chain along which
  the Erdős–Pósa theorem would prove Erdős #73, with `MaxDef` in place of the packing number.
* **`MaxDef G = 0 ↔ G.IsBipartite`** (`maxDef_eq_zero_iff`, Part 3): the whole of the proved case
  `k = 0` of Erdős #73 (`JSP90.erdos73_zero`) is the statement "deficiency `0` means bipartite".
* **Arithmetic** (Part 6): the deficiency is *additive over an anticomplete decomposition*
  (`maxDef_anticover_add`), it *never increases under taking an induced subgraph or a residue*
  (`maxDef_induceFinset_le`, `maxDef_deleteFinset_le`), and it is *bounded by a piece together with
  the number of outside vertices* (`maxDef_le_maxDef_induceFinset_add_card`) — the local-to-global
  step that the decomposition families of rounds 43–48 use in the other direction.
* **A reduction to a linear statement** (Part 7): `LinearErdős73` — the odd cycle transversal
  number of `G` is at most `C` times `MaxDef G` for a universal `C` — implies all of Erdős #73
  (`erdos73Of_linearErdős73`), and `C = 0` is refuted with the witness `K_3`.

## What is *not* proved

`MaxDef G ≤ k → CloseToBipartite (C * k) G` is exactly Erdős Problem #73 in the language of this
file and is not proved here; neither is the Erdős–Pósa theorem for odd cycles
(`JSP90.OddCycleErdosPosa`), the unchanged primary blocker.  What is new is that the *hypothesis* is
now a number, the sandwich that would finish the Erdős–Pósa route is proved on both sides, the
`k = 0` case is re-derived in the new language, and the arithmetic of the new quantity is available
to the decomposition families of the earlier rounds.

No Mathlib API beyond `Finset` and `SimpleGraph` (bipartiteness, independent sets) is used. -/

import JSPProblem.Critical
import Mathlib.Data.Finset.Max

namespace JSP90

universe u

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqDef : DecidableEq V := Classical.decEq V
local instance instDecidableEqFinDef (n : ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

/-- The decider used for "is `S` an independent set of `G`?".  Naming it makes the terms of
`indepSets` below match the terms the proofs speak about. -/
local instance instDecidablePredIsIndepSet (G : SimpleGraph V) :
    DecidablePred fun S : Finset V => G.IsIndepSet S := fun _ => Classical.propDecidable _

/-! ### Independent sets: the conversions used throughout -/

/-- **Finset-membership form of the definition of an independent set.** -/
theorem IsIndepSet.apply' {G : SimpleGraph V} {S : Finset V} (h : G.IsIndepSet S) {v w : V}
    (hv : v ∈ S) (hw : w ∈ S) (hne : v ≠ w) (hadj : G.Adj v w) : False := by
  rw [SimpleGraph.isIndepSet_iff] at h
  exact h (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hw) hne hadj

/-- **The constructor form of the definition of an independent set.** -/
theorem isIndepSet_of_intro {G : SimpleGraph V} {S : Finset V}
    (h : ∀ v w : V, v ∈ (S : Set V) → w ∈ (S : Set V) → v ≠ w → ¬ G.Adj v w) :
    G.IsIndepSet S := by
  rw [SimpleGraph.isIndepSet_iff]
  intro v hv w hw hne
  exact h v w hv hw hne

/-- **A single vertex is an independent set.** -/
theorem isIndepSet_singleton (G : SimpleGraph V) (a : V) : G.IsIndepSet ({a} : Finset V) := by
  refine isIndepSet_of_intro fun v w hv hw hne hadj => ?_
  have hva : v = a := Finset.mem_singleton.mp (Finset.mem_coe.mp hv)
  have hwa : w = a := Finset.mem_singleton.mp (Finset.mem_coe.mp hw)
  have hvw : v = w := hva.trans hwa.symm
  exact G.loopless.irrefl w (hvw ▸ hadj)

/-- **`∅` is an independent set.** -/
theorem isIndepSet_empty (G : SimpleGraph V) : G.IsIndepSet (∅ : Finset V) := by
  refine isIndepSet_of_intro fun v w hv => ?_
  simp

/-- **Restricting to the vertices of `s` does not create edges**: an independent set of `G` lying in
`s` is one of `G[s]`. -/
theorem IsIndepSet.induceFinset' {G : SimpleGraph V} {S s : Finset V} (hS : G.IsIndepSet S)
    (hsub : S ⊆ s) : (induceFinset G s).IsIndepSet S :=
  isIndepSet_of_intro fun v w hv hw hne hadj => IsIndepSet.apply' hS hv hw hne
    (induce_adj.mp hadj).2.2

/-- **An induced subgraph has no extra adjacencies**: an independent set of `G[s]` lying in `s` is
one of `G`. -/
theorem IsIndepSet.of_induceFinset {G : SimpleGraph V} {S s : Finset V}
    (hS : (induceFinset G s).IsIndepSet S) (hsub : S ⊆ s) : G.IsIndepSet S :=
  isIndepSet_of_intro fun v w hv hw hne hadj => IsIndepSet.apply' hS hv hw hne
    ⟨hsub (Finset.mem_coe.mp hv), hsub (Finset.mem_coe.mp hw), hadj⟩

/-- **The independent sets of `G` inside `s` and of `G[s]` inside `s` coincide.** -/
theorem isIndepSet_induceFinset_iff {G : SimpleGraph V} {S s : Finset V} (hsub : S ⊆ s) :
    (induceFinset G s).IsIndepSet S ↔ G.IsIndepSet S :=
  ⟨fun h => IsIndepSet.of_induceFinset h hsub, fun h => IsIndepSet.induceFinset' h hsub⟩

/-! ## Part 1 — the independence number `α(G[X])` as a number -/

section IndepCard

/-- **The independent subsets of `X` in `G`**, as a finset of finsets. -/
noncomputable def indepSets (G : SimpleGraph V) (X : Finset V) : Finset (Finset V) :=
  X.powerset.filter (fun S : Finset V => G.IsIndepSet S)

/-- **`∅` is independent**, so `indepSets G X` is never empty and the supremum below is attained. -/
theorem indepSets_nonempty (G : SimpleGraph V) (X : Finset V) : (indepSets G X).Nonempty :=
  ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), isIndepSet_empty G⟩⟩

/-- Every member of `indepSets G X` is a subset of `X`. -/
theorem sub_of_mem_indepSets {G : SimpleGraph V} {X S : Finset V} (hS : S ∈ indepSets G X) :
    S ⊆ X :=
  Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1

/-- **A member of `indepSets G X` is an independent set of `G`.**

Outside this file the statement `(Finset.mem_filter.mp hS).2` cannot be applied to `hS` directly:
`indepSets` is not unfolded, so the filter predicate and its `DecidablePred` stay metavariables and
instance search fails.  This lemma is the form to use from another module. -/
theorem isIndepSet_of_mem_indepSets {G : SimpleGraph V} {X S : Finset V}
    (hS : S ∈ indepSets G X) : G.IsIndepSet S := by
  rw [indepSets] at hS
  exact (Finset.mem_filter.mp hS).2

/-- **`indepCard G X = α(G[X])`**, the size of a largest independent subset of `X`.  This is the
`α` of Erdős's hypothesis, as a natural number. -/
noncomputable def indepCard (G : SimpleGraph V) (X : Finset V) : ℕ :=
  (indepSets G X).sup Finset.card

/-- Every independent subset of `X` is bounded by `α(G[X])`. -/
theorem le_indepCard {G : SimpleGraph V} {X S : Finset V} (hS : S ∈ indepSets G X) :
    S.card ≤ indepCard G X :=
  Finset.le_sup hS

/-- An independent subset of `X` is bounded by `α(G[X])`. -/
theorem le_indepCard_of_isIndepSet {G : SimpleGraph V} {X S : Finset V} (hS : S ⊆ X)
    (hSi : G.IsIndepSet S) : S.card ≤ indepCard G X :=
  le_indepCard (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hSi⟩)

/-- `α(G[X]) ≤ |X|`, for the trivial reason that an independent set is a subset. -/
theorem indepCard_le_card (G : SimpleGraph V) (X : Finset V) : indepCard G X ≤ X.card := by
  refine Finset.sup_le_iff.mpr fun S hS => Finset.card_le_card (sub_of_mem_indepSets hS)

/-- A nonempty `X` has `α(G[X]) ≥ 1`. -/
theorem indepCard_pos {G : SimpleGraph V} {X : Finset V} (hX : X.Nonempty) :
    0 < indepCard G X := by
  have hmem : ({Classical.choose hX} : Finset V) ∈ indepSets G X :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hX.choose_spec),
        isIndepSet_singleton G _⟩
  have hle := le_indepCard hmem
  have hcard : ({Classical.choose hX} : Finset V).card = 1 := Finset.card_singleton _
  omega

/-- **The independence number of the empty set is `0`.** -/
theorem indepCard_empty (G : SimpleGraph V) : indepCard G (∅ : Finset V) = 0 :=
  le_antisymm (by have hle := indepCard_le_card G ∅; simp at hle ⊢; omega) (Nat.zero_le _)

/-- **`α(G[X])` is attained**: there is an independent `S ⊆ X` of size exactly `indepCard G X`.
This is the step that turns the hypothesis of JSP-000090 from a `∀ ∃` statement into a number. -/
theorem exists_indepCard (G : SimpleGraph V) (X : Finset V) :
    ∃ S : Finset V, S ⊆ X ∧ G.IsIndepSet S ∧ S.card = indepCard G X := by
  by_cases hX : X.Nonempty
  · have hpos : 0 < indepCard G X := indepCard_pos hX
    have hmax : ∃ S ∈ indepSets G X, indepCard G X ≤ S.card :=
      (Finset.le_sup_iff (s := indepSets G X) (f := Finset.card) (a := indepCard G X) hpos).mp
        (Nat.le_refl _)
    obtain ⟨S, hS, hle⟩ := hmax
    exact ⟨S, sub_of_mem_indepSets hS, (Finset.mem_filter.mp hS).2,
      le_antisymm (le_indepCard hS) hle⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hX]
    exact ⟨∅, Finset.empty_subset _, isIndepSet_empty G, (indepCard_empty G).symm⟩

/-- **Adding edges cannot increase `α`**: if `H ≤ G` then every independent set of `G` is one of
`H`, so `α(G[X]) ≤ α(H[X])`. -/
theorem indepCard_mono {G H : SimpleGraph V} (hGH : H ≤ G) (X : Finset V) :
    indepCard G X ≤ indepCard H X := by
  refine Finset.sup_le_iff.mpr fun S hS => ?_
  exact le_indepCard_of_isIndepSet (sub_of_mem_indepSets hS)
    (IsIndepSet.mono_le hGH (Finset.mem_filter.mp hS).2)

/-- **A bipartite induced subgraph has a large independent set**: `|X| ≤ 2 * α(G[X])`, i.e. `X` is
`0`-deficient.  This is `JSP90.isBipartite_indepSet_card_half` with the two halves of Erdős's bound
made explicit. -/
theorem indepCard_le_of_isBipartite {G : SimpleGraph V} {X : Finset V}
    (h : (induceFinset G X).IsBipartite) : X.card ≤ 2 * indepCard G X := by
  obtain ⟨S, hSsub, hSi, hb⟩ := isBipartite_indepSet_card_half h X
  have hle : S.card ≤ indepCard G X :=
    le_indepCard_of_isIndepSet hSsub (IsIndepSet.of_induceFinset hSi hSsub)
  omega

/-- The independence number of a complete graph on a nonempty set is `1`. -/
theorem indepCard_completeGraph {W : Type*} [Fintype W] {X : Finset W} (hX : X.Nonempty) :
    indepCard (SimpleGraph.completeGraph W) X = 1 := by
  refine le_antisymm ?_ (Nat.succ_le_of_lt (indepCard_pos hX))
  refine Finset.sup_le_iff.mpr fun S hS => ?_
  have hSi : (SimpleGraph.completeGraph W).IsIndepSet S := (Finset.mem_filter.mp hS).2
  have hclique : (SimpleGraph.completeGraph W).IsClique X :=
    fun v _ w _ hne => SimpleGraph.top_adj v w |>.mpr hne
  exact indep_card_le_one_of_clique hclique hSi (sub_of_mem_indepSets hS)


/-- **An independent subset of `X ⊆ s` is a member of `indepSets (G[s]) X` exactly when it is
independent in `G`.** -/
theorem mem_indepSets_induceFinset {G : SimpleGraph V} {X Y s : Finset V} (hY : Y ⊆ s)
    (hX : X ⊆ Y) : X ∈ indepSets (induceFinset G s) Y ↔ G.IsIndepSet X :=
  ⟨fun h => (isIndepSet_induceFinset_iff (G := G) (S := X) (s := s)
        (Finset.Subset.trans hX hY)).mp (Finset.mem_filter.mp h).2,
   fun h => Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hX,
        (isIndepSet_induceFinset_iff (G := G) (S := X) (s := s)
          (Finset.Subset.trans hX hY)).mpr h⟩ ⟩

/-- **`α` is monotone under subsets**: a vertex set contains no larger an independent set than any
set containing it. -/
theorem indepCard_le_of_subset {G : SimpleGraph V} {X Y : Finset V} (hXY : X ⊆ Y) :
    indepCard G X ≤ indepCard G Y := by
  refine Finset.sup_le_iff.mpr fun S hS => ?_
  exact le_indepCard_of_isIndepSet (Finset.Subset.trans (sub_of_mem_indepSets hS) hXY)
    (Finset.mem_filter.mp hS).2

end IndepCard

/-! ## Part 2 — the deficiency of a vertex set, and the maximum deficiency of a graph -/

section Deficiency

/-- **The deficiency of the vertex set `X` in `G`**, `|X| - 2 * α(G[X])`: twice the number of
vertices of `X` that the largest independent set of `X` fails to cover.  It is `0` on a bipartite
`X`, `1` on an odd cycle, and `|X| - 2` on a clique. -/
noncomputable def defOf (G : SimpleGraph V) (X : Finset V) : ℕ :=
  X.card - 2 * indepCard G X

/-- The vertex sets of `G`, as a finset of finsets; the domain of the maximum below. -/
noncomputable def defSets (G : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ : Finset V).powerset

theorem mem_defSets (G : SimpleGraph V) (X : Finset V) : X ∈ defSets G :=
  Finset.mem_powerset.mpr (Finset.subset_univ X)

/-- **`MaxDef G`, the maximum deficiency of `G`**: the largest value of `|X| - 2 * α(G[X])` over all
vertex sets `X ⊆ V`.  Erdős's hypothesis `LocIndep k G` is exactly `MaxDef G ≤ k`. -/
noncomputable def MaxDef (G : SimpleGraph V) : ℕ := (defSets G).sup (defOf G)

/-- The deficiency of any vertex set is at most `MaxDef G`. -/
theorem le_maxDef (G : SimpleGraph V) (X : Finset V) : defOf G X ≤ MaxDef G :=
  Finset.le_sup (mem_defSets G X)

/-- A uniform bound on the deficiency of every vertex set bounds `MaxDef G`. -/
theorem maxDef_le {G : SimpleGraph V} {k : ℕ} (h : ∀ X : Finset V, defOf G X ≤ k) :
    MaxDef G ≤ k := by
  refine Finset.sup_le_iff.mpr fun Y _ => ?_
  exact h Y

/-- **`MaxDef G` is attained**: some vertex set of `G` has deficiency exactly `MaxDef G`. -/
theorem exists_eq_maxDef (G : SimpleGraph V) : ∃ X : Finset V, defOf G X = MaxDef G := by
  by_cases hpos : 0 < MaxDef G
  · have hmax : ∃ X ∈ defSets G, MaxDef G ≤ defOf G X :=
      (Finset.le_sup_iff (s := defSets G) (f := defOf G) (a := MaxDef G) hpos).mp (Nat.le_refl _)
    obtain ⟨X, hX, hle⟩ := hmax
    exact ⟨X, le_antisymm (le_maxDef G X) hle⟩
  · exact ⟨∅, le_antisymm (le_maxDef G ∅) (by omega)⟩

/-- **THE REFORMULATION OF ERDŐS'S HYPOTHESIS.**
`LocIndep k G` — "every vertex set `X` of `G` carries an independent set `S ⊆ X` with
`2 * |S| + k ≥ |X|`" — holds **if and only if** the maximum deficiency of `G` is at most `k`.

The forward direction is easy (a witness for `X` bounds the deficiency of `X`); the reverse one
uses that `α(G[X])` is attained.  This is the reduction that turns the hypothesis of JSP-000090
into a numerical bound on a function of `G`. -/
theorem locIndep_iff_maxDef_le {G : SimpleGraph V} {k : ℕ} : LocIndep k G ↔ MaxDef G ≤ k := by
  constructor
  · intro h
    refine maxDef_le fun X => ?_
    obtain ⟨S, hSsub, hSi, hb⟩ := h X
    have hle : S.card ≤ indepCard G X := le_indepCard_of_isIndepSet hSsub hSi
    rw [show defOf G X = X.card - 2 * indepCard G X from rfl, Nat.sub_le_iff_le_add]
    omega
  · intro h
    intro X
    obtain ⟨S, hSsub, hSi, hScard⟩ := exists_indepCard G X
    refine ⟨S, hSsub, hSi, ?_⟩
    have h1 := le_maxDef G X
    rw [hScard]
    have h1' : X.card - 2 * indepCard G X ≤ MaxDef G := by
      simp only [defOf] at h1
      exact h1
    rw [Nat.sub_le_iff_le_add] at h1'
    omega

theorem locIndep_of_maxDef_le {G : SimpleGraph V} {k : ℕ} (h : MaxDef G ≤ k) : LocIndep k G :=
  (locIndep_iff_maxDef_le).mpr h

theorem maxDef_le_of_locIndep {G : SimpleGraph V} {k : ℕ} (h : LocIndep k G) : MaxDef G ≤ k :=
  (locIndep_iff_maxDef_le).mp h

/-- **ERDŐS PROBLEM #73 IN THE LANGUAGE OF THE DEFICIENCY.**  The theorem is unaffected by the
reformulation: the hypothesis may be taken to be a single number attached to `G`. -/
theorem erdos73_iff_maxDef {k : ℕ} :
    Erdős73.{u} k ↔
      ∃ m : ℕ, ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
        MaxDef G ≤ k → CloseToBipartite m G := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h
    exact ⟨m, fun W instW G hG => hm W instW G (locIndep_of_maxDef_le hG)⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, fun W instW G hG => hm W instW G (maxDef_le_of_locIndep hG)⟩

end Deficiency

/-! ## Part 3 — the sandwich: packings ≤ deficiency ≤ transversals -/

section Sandwich

/-- **A vertex set splits into its two parts**: `|Y| = |Y ∩ s| + |Y \ s|`. -/
theorem card_inter_add_card_sdiff (Y s : Finset V) :
    (Y ∩ s).card + (Y \ s).card = Y.card := by
  have heq : Y = (Y ∩ s) ∪ (Y \ s) := by
    ext v
    constructor
    · intro hv
      by_cases hs : v ∈ s
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv, hs⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hs⟩)
    · intro hv
      rcases Finset.mem_union.mp hv with h | h
      · exact Finset.mem_inter.mp h |>.1
      · exact Finset.mem_sdiff.mp h |>.1
  have hdisj : Disjoint (Y ∩ s) (Y \ s) := by
    refine Finset.disjoint_left.2 ?_
    intro v hv1 hv2
    exact (Finset.mem_sdiff.mp hv2).2 (Finset.mem_inter.mp hv1).2
  calc (Y ∩ s).card + (Y \ s).card = ((Y ∩ s) ∪ (Y \ s)).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = Y.card := (congrArg Finset.card heq).symm

/-- **`MaxDef G ≤ |X|` for every odd cycle transversal `X`.**  The combinatorial content: if `G` is
bipartite off `X`, then the vertices of a vertex set `Y` outside `X` are covered, two by two, by
independent sets, so `|Y| - 2 * α(Y) ≤ |Y ∩ X| ≤ |X|`.

So a transversal has to be at least as large as the maximum deficiency: **the deficiency is a lower
bound for the number of vertices one must delete.** -/
theorem maxDef_le_of_hitsOddCycles {G : SimpleGraph V} {X : Finset V} (hX : HitsOddCycles G X) :
    MaxDef G ≤ X.card := by
  refine maxDef_le fun Y => ?_
  classical
  set Z : Finset V := Y \ X with hZdef
  have hsub : induceFinset (deleteFinset G X) Z = induceFinset G Z := by
    ext v w
    simp only [induce_adj, deleteFinset, hZdef, Finset.mem_sdiff, Finset.mem_univ]
    tauto
  have hres : (induceFinset G Z).IsBipartite := by
    rw [← hsub]
    obtain ⟨c, hc⟩ := isBipartite_delete_of_hitsOddCycles hX
    refine ⟨SimpleGraph.Coloring.mk c fun {v w} hadj => ?_⟩
    have hvmem : v ∈ Y \ X := hZdef ▸ (induce_adj.mp hadj).1
    have hwmem : w ∈ Y \ X := hZdef ▸ (induce_adj.mp hadj).2.1
    have hmem1 : v ∉ X := (Finset.mem_sdiff.mp hvmem).2
    have hmem2 : w ∉ X := (Finset.mem_sdiff.mp hwmem).2
    have hadjG : G.Adj v w := (deleteFinset_adj.mp (induce_adj.mp hadj).2.2).2.2
    exact hc (deleteFinset_adj.mpr ⟨hmem1, hmem2, hadjG⟩)
  obtain ⟨S, hSsub, hSi, hb⟩ := isBipartite_indepSet_card_half hres Z
  have hSiG : G.IsIndepSet S := IsIndepSet.of_induceFinset hSi hSsub
  have hle : S.card ≤ indepCard G Y :=
    le_indepCard_of_isIndepSet
      (Finset.Subset.trans hSsub (by rw [hZdef]; exact Finset.sdiff_subset)) hSiG
  have hcard : (Y ∩ X).card + (Y \ X).card = Y.card := card_inter_add_card_sdiff Y X
  have hb' : (Y \ X).card ≤ 2 * S.card := by rw [← hZdef]; exact hb
  have hinter : (Y ∩ X).card ≤ X.card := by
    refine Finset.card_le_card ?_
    intro v hv
    exact (Finset.mem_inter.mp hv).2
  simp only [defOf]
  omega

/-- **A transversal is a lower bound for `MaxDef`**: deleting at most `m` vertices leaves a bipartite
graph, so `MaxDef G ≤ m`.  This is the quantitative form of "one cannot do better than the
deficiency", and it is the reason the constant of Erdős #73 is bounded below by the deficiency of
the extremal witnesses. -/
theorem maxDef_le_closeToBipartite {G : SimpleGraph V} {m : ℕ} (h : CloseToBipartite m G) :
    MaxDef G ≤ m := by
  obtain ⟨X, hX, hhit⟩ := (closeToBipartite_iff_hitsOddCycles (G := G)).mp h
  have hle := maxDef_le_of_hitsOddCycles hhit
  omega

/-- **THE PACKING HALF OF THE SANDWICH**: a deficiency bound bounds every packing of odd cycles.
This is `JSP90.LocIndep.oddCycle_packing_le` in numerical form. -/
theorem card_le_of_maxDef_le {G : SimpleGraph V} {r : ℕ} (h : MaxDef G ≤ r)
    {C : Finset (Finset V)} (hC : IsOddCycleFamily (G := G) C) : C.card ≤ r :=
  (locIndep_of_maxDef_le h).oddCycleFamily_card_le hC

/-- **`ν(G) ≤ MaxDef G ≤ τ(G)`**: THE CHAIN ALONG WHICH ERDŐS–PÓSA WOULD PROVE JSP-000090.**  Any
packing of odd cycles of `G` has at most `MaxDef G` members, and any odd cycle transversal of `G`
has at least `MaxDef G` vertices.  So a bound on the maximum deficiency bounds the packing number,
and the Erdős–Pósa theorem for odd cycles would then bound the transversal number by a function of
`MaxDef G`, i.e. by a function of `k` — which is `JSP90.erdos73_of_erdosPosa`, in the numerical
language of this file. -/
theorem packing_le_maxDef_le_transversal {G : SimpleGraph V} {C : Finset (Finset V)}
    (hC : IsOddCycleFamily (G := G) C) {X : Finset V} (hX : HitsOddCycles G X) :
    C.card ≤ MaxDef G ∧ MaxDef G ≤ X.card :=
  ⟨card_le_of_maxDef_le (Nat.le_refl (MaxDef G)) hC, maxDef_le_of_hitsOddCycles hX⟩

/-- **DEFICIENCY `0` IS BIPARTITENESS.**  The proved case `k = 0` of Erdős #73
(`JSP90.erdos73_zero`) is exactly this equivalence: the maximum deficiency vanishes if and only if
the graph is bipartite, i.e. iff it is the union of a bipartite graph and *zero* vertices. -/
theorem maxDef_eq_zero_iff {G : SimpleGraph V} : MaxDef G = 0 ↔ G.IsBipartite := by
  constructor
  · intro h
    have h0 : LocIndep (0 : ℕ) G := locIndep_of_maxDef_le (G := G) (k := 0) (by omega)
    exact locIndep_zero_isBipartite (V := V) (G := G) h0
  · intro h
    have hle : MaxDef G ≤ 0 := by
      refine maxDef_le fun X => ?_
      obtain ⟨S, hSsub, hSi, hb⟩ := isBipartite_indepSet_card_half h X
      have hle : S.card ≤ indepCard G X := le_indepCard_of_isIndepSet hSsub hSi
      rw [show defOf G X = X.card - 2 * indepCard G X from rfl, Nat.sub_le_iff_le_add]
      omega
    exact le_antisymm hle (Nat.zero_le _)

/-- A non-bipartite graph has positive deficiency: it cannot be made bipartite for free. -/
theorem maxDef_pos_of_not_isBipartite {G : SimpleGraph V} (h : ¬ G.IsBipartite) :
    0 < MaxDef G := by
  have h0 : MaxDef G = 0 ↔ G.IsBipartite := maxDef_eq_zero_iff (G := G)
  rw [Nat.pos_iff_ne_zero]
  exact fun hz => h (h0.mp hz)

end Sandwich

/-! ## Part 4 — the deficiency of the sharp witness `kTriangles k` -/

section Sharp

/-- **THE SHARP WITNESS HAS DEFICIENCY EXACTLY `k`.**  `kTriangles k` is `K_3 ⊔ … ⊔ K_3` (`k`
copies), the graph on which Erdős #73 is sharp: it satisfies `LocIndep k`, and its largest
deficiency is `k`.

Both directions are one-liners on the reformulation: the upper bound is `locIndep_kTriangles` read
numerically, and the lower bound is the deficiency of the whole vertex set, `3 * k - 2 * k = k`. -/
theorem maxDef_kTriangles (k : ℕ) : MaxDef (kTriangles k) = k := by
  have h1 : MaxDef (kTriangles k) ≤ k := maxDef_le_of_locIndep (locIndep_kTriangles (k := k))
  have h2 : k ≤ MaxDef (kTriangles k) := by
    have hle := le_maxDef (kTriangles k) (Finset.univ : Finset (Fin 3 × Fin k))
    have hcard : ((Finset.univ : Finset (Fin 3 × Fin k))).card = 3 * k := by simp
    have hαle : indepCard (kTriangles k) (Finset.univ : Finset (Fin 3 × Fin k)) ≤ k := by
      refine Finset.sup_le_iff.mpr fun S hS => ?_
      exact card_le_kTriangles (Finset.mem_filter.mp hS).2
    have hαge : (k : ℕ) ≤ indepCard (kTriangles k) (Finset.univ : Finset (Fin 3 × Fin k)) := by
      -- the independent set `onePerFibre := (univ : Finset (Fin k)).image (fun i => (0, i))`
      -- picks one vertex in each of the `k` fibres, so it has `k` elements
      have hmem : ((Finset.univ : Finset (Fin k)).image
          fun i : Fin k => (⟨(0 : Fin 3), i⟩ : Fin 3 × Fin k))
          ∈ indepSets (kTriangles k) (Finset.univ : Finset (Fin 3 × Fin k)) := by
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_powerset.mpr ?_
          intro p hp
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
          exact Finset.mem_univ _
        · refine isIndepSet_of_intro fun v w hv hw hne hadj => ?_
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
          exact (kTriangles_adj.mp hadj).2 rfl
      have hcardS : ((Finset.univ : Finset (Fin k)).image
          fun i : Fin k => (⟨(0 : Fin 3), i⟩ : Fin 3 × Fin k)).card = k := by
        rw [Finset.card_image_of_injective _ (f := fun i : Fin k =>
          (⟨(0 : Fin 3), i⟩ : Fin 3 × Fin k))]
        · simp
        · intro i j h
          exact congrArg Prod.snd h
      have hle := le_indepCard hmem
      omega
    simp only [defOf] at hle
    omega
  omega

/-- **ON THE SHARP WITNESS THE EXACT VALUE OF THE CONCLUSION IS THE DEFICIENCY**: the least number
of vertices to delete to make `kTriangles k` bipartite is `k = MaxDef (kTriangles k)`. -/
theorem closeToBipartite_kTriangles_iff_maxDef (k m : ℕ) :
    CloseToBipartite m (kTriangles k) ↔ m ≥ MaxDef (kTriangles k) := by
  constructor
  · intro h
    exact maxDef_le_closeToBipartite h
  · intro h
    have hle : k ≤ m := by rw [← maxDef_kTriangles k]; exact h
    exact closeToBipartite_iff.mpr hle

/-- **NO CONSTANT BELOW THE DEFICIENCY WORKS.**  On `kTriangles k` the deficiency is `k` and the
conclusion needs `k` deletions, so `m < MaxDef` is never enough.  This is the lower bound
`f(k) ≥ k` of `JSPProblem/Sharp.lean`, in the language of this file. -/
theorem no_closeToBipartite_of_maxDef_kTriangles {k m : ℕ} (h : m < k) :
    ¬ CloseToBipartite m (kTriangles k) := by
  intro hc
  have hle : MaxDef (kTriangles k) ≤ m := maxDef_le_closeToBipartite hc
  rw [maxDef_kTriangles k] at hle
  omega

end Sharp

/-! ## Part 5 — the deficiency of a complete graph -/

section Complete

/-- **`MaxDef (K_n) = n - 2` for `n ≥ 2`**: on a complete graph an independent set has one vertex,
so the deficiency of a vertex set `X` is `|X| - 2`, largest at `X = V`.  Together with
`JSP90.closeToBipartite_iff_completeGraph_add_two` — "on complete graphs the conclusion of Erdős #73
is exact" — this says that on complete graphs the deficiency is *the* function which measures the
number of vertices to delete. -/
theorem maxDef_completeGraph {n : ℕ} (hn : 2 ≤ n) :
    MaxDef (SimpleGraph.completeGraph (Fin n)) = n - 2 := by
  have hle : MaxDef (SimpleGraph.completeGraph (Fin n)) ≤ n - 2 := by
    refine maxDef_le fun X => ?_
    by_cases hX : X.Nonempty
    · have hα : indepCard (SimpleGraph.completeGraph (Fin n)) X = 1 := indepCard_completeGraph hX
      have hXcard : X.card ≤ n :=
        le_trans (Finset.card_le_card (Finset.subset_univ X)) (by simp)
      rw [show defOf (SimpleGraph.completeGraph (Fin n)) X = X.card - 2 * indepCard _ X from rfl,
        Nat.sub_le_iff_le_add]
      omega
    · have hzero : defOf (SimpleGraph.completeGraph (Fin n)) X = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp hX, defOf, Finset.card_empty, indepCard_empty]
      omega
  refine le_antisymm hle ?_
  have hle' := le_maxDef (SimpleGraph.completeGraph (Fin n)) (Finset.univ : Finset (Fin n))
  have hα : indepCard (SimpleGraph.completeGraph (Fin n)) (Finset.univ : Finset (Fin n)) = 1 :=
    indepCard_completeGraph
      ((Finset.card_pos.mp (by rw [Finset.card_fin]; omega
        : (0 : ℕ) < (Finset.univ : Finset (Fin n)).card)))
  have hcard : ((Finset.univ : Finset (Fin n))).card = n := Finset.card_fin n
  simp only [defOf] at hle'
  omega

/-- **A COMPLETE GRAPH IS `n - 2` DELETIONS AWAY FROM BIPARTITE, AND THAT IS ITS DEFICIENCY.**
Combining the two halves: the value of the conclusion of Erdős #73 on `K_n` is exactly
`MaxDef (K_n)` for `n ≥ 2`; for `n ≤ 2` the graph is already bipartite and needs no deletion. -/
theorem closeToBipartite_completeGraph_iff_maxDef {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    CloseToBipartite m (SimpleGraph.completeGraph (Fin n))
      ↔ m ≥ MaxDef (SimpleGraph.completeGraph (Fin n)) := by
  constructor
  · intro h
    exact maxDef_le_closeToBipartite h
  · intro h
    have hle : n - 2 ≤ m := by rw [← maxDef_completeGraph hn]; exact h
    have hn2 : (n : ℕ) ≤ m + 2 := by omega
    exact closeToBipartite_iff_completeGraph_add_two m n |>.mpr hn2

/-- **THE SMALL COMPLETE GRAPHS HAVE DEFICIENCY `0`**: for `n ≤ 2` the graph `K_n` is already
bipartite, so its maximum deficiency vanishes and no deletion is needed. -/
theorem maxDef_completeGraph_small {n : ℕ} (hn : n ≤ 2) :
    MaxDef (SimpleGraph.completeGraph (Fin n)) = 0 := by
  have hle : MaxDef (SimpleGraph.completeGraph (Fin n)) ≤ 0 := by
    refine maxDef_le fun X => ?_
    by_cases hX : X.Nonempty
    · have hα : indepCard (SimpleGraph.completeGraph (Fin n)) X = 1 := indepCard_completeGraph hX
      have hXcard : X.card ≤ n := le_trans (Finset.card_le_card (Finset.subset_univ X)) (by simp)
      rw [show defOf (SimpleGraph.completeGraph (Fin n)) X = X.card - 2 * indepCard _ X from rfl,
        Nat.sub_le_iff_le_add]
      omega
    · have hzero : defOf (SimpleGraph.completeGraph (Fin n)) X = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty.mp hX, defOf, Finset.card_empty, indepCard_empty]
      omega
  exact le_antisymm hle (Nat.zero_le _)

end Complete

/-! ## Part 6 — arithmetic of the deficiency -/

section Arithmetic

/-- **ONE HALF OF THE DEFICIENCY BOUND.**  If `a ≤ c`, then subtracting `c + d` from `a + b` leaves
at most `b - d`: the part `a` is too small to pay anything. -/
theorem sub_le_sub_of_le (a b c d : ℕ) (h : a ≤ c) : a + b - (c + d) ≤ b - d := by
  rw [(Nat.sub_sub _ _ _).symm]
  refine Nat.sub_le_sub_right ?_ d
  exact (Nat.sub_le_iff_le_add).mpr (by omega)

/-- ... and symmetrically, if `b ≤ d` then `a + b - (c + d) ≤ a - c`. -/
theorem sub_le_sub_of_le' (a b c d : ℕ) (h : b ≤ d) : a + b - (c + d) ≤ a - c := by
  have h' := sub_le_sub_of_le b a d c h
  omega

/-- **THE DEFICIENCY IS SUBADDITIVE IN ARITHMETIC.**  Subtracting a sum from a sum is at most the
sum of the two differences: the truncation at zero can only lose, never gain.  This is the ℕ-arithmetic
behind the subadditivity of the deficiency over an anticomplete decomposition. -/
theorem sub_le_add_sub (a b c d : ℕ) : a + b - (c + d) ≤ (a - c) + (b - d) := by
  by_cases h1 : a ≤ c
  · rw [Nat.sub_eq_zero_of_le h1, Nat.zero_add]
    exact sub_le_sub_of_le a b c d h1
  · by_cases h2 : b ≤ d
    · rw [Nat.sub_eq_zero_of_le h2, Nat.add_zero]
      exact sub_le_sub_of_le' a b c d h2
    · -- both parts are large enough to pay, so there is no truncation at all
      have hlt1 : c < a := by omega
      have hlt2 : d < b := by omega
      have h1 : a - c + c = a := Nat.sub_add_cancel (Nat.le_of_lt hlt1)
      have h2 : b - d + d = b := Nat.sub_add_cancel (Nat.le_of_lt hlt2)
      have h3 : a + b = ((a - c) + (b - d)) + (c + d) := by omega
      rw [h3, Nat.add_sub_cancel]

/-- **Adding edges does not decrease the deficiency.** -/
theorem maxDef_mono {G H : SimpleGraph V} (hGH : H ≤ G) : MaxDef H ≤ MaxDef G := by
  refine maxDef_le fun X => ?_
  have h1 := le_maxDef H X
  have h2 := le_maxDef G X
  have h3 : 2 * indepCard G X ≤ 2 * indepCard H X :=
    Nat.mul_le_mul_left 2 (indepCard_mono hGH X)
  simp only [defOf] at h1 h2
  rw [Nat.sub_le_iff_le_add] at h1 h2
    <;> simp only [defOf]
  rw [Nat.sub_le_iff_le_add]
  omega

/-- **A piece of `G` has deficiency at most `MaxDef G`**: restricting to the vertices of `s` cannot
increase the maximum deficiency. -/
theorem maxDef_induceFinset_le {G : SimpleGraph V} (s : Finset V) :
    MaxDef (induceFinset G s) ≤ MaxDef G :=
  maxDef_mono (fun _ _ hadj => (induce_adj.mp hadj).2.2)

/-- **THE RESIDUE INHERITS THE BOUND.**  Deleting vertices cannot increase the maximum deficiency —
the numerical form of `JSP90.LocIndep.of_deleteFinset` and of the residue induction of
`JSPProblem/Residue.lean`, which is what makes an induction on `MaxDef G` (rather than on `|V|`)
possible. -/
theorem maxDef_deleteFinset_le {G : SimpleGraph V} (X : Finset V) :
    MaxDef (deleteFinset G X) ≤ MaxDef G :=
  maxDef_induceFinset_le (Finset.univ \ X)

/-- **The deficiency of a local hypothesis is inherited by every induced subgraph**, numerically. -/
theorem locIndep_induceFinset_of_maxDef_le {G : SimpleGraph V} {k : ℕ} (h : MaxDef G ≤ k)
    (s : Finset V) : LocIndep k (induceFinset G s) :=
  locIndep_of_maxDef_le (le_trans (maxDef_induceFinset_le s) h)

/-- **LOCAL-TO-GLOBAL: A PIECE PLUS THE VERTICES OUTSIDE IT.**  If the vertices of `s` have
deficiency at most `k`, the whole graph has deficiency at most `k + |V \ s|`: only the vertices
outside `s` are unaccounted for, since an independent set of a vertex set contains an independent set
of any of its subsets.  This is the inequality in the direction that the decomposition families of
rounds 43–48 need. -/
theorem maxDef_le_maxDef_induceFinset_add_card {G : SimpleGraph V} (s : Finset V) :
    MaxDef G ≤ MaxDef (induceFinset G s) + ((Finset.univ : Finset V) \ s).card := by
  refine maxDef_le fun Y => ?_
  have hα : indepCard (induceFinset G s) (Y ∩ s) ≤ indepCard G Y := by
    refine Finset.sup_le_iff.mpr fun S hS => ?_
    have hSs : S ⊆ s := Finset.Subset.trans (sub_of_mem_indepSets hS)
      (fun v hv => (Finset.mem_inter.mp hv).2)
    exact le_indepCard_of_isIndepSet
      (Finset.Subset.trans (sub_of_mem_indepSets hS) (fun v hv => (Finset.mem_inter.mp hv).1))
      ((isIndepSet_induceFinset_iff (G := G) (S := S) (s := s) hSs).mp
        (Finset.mem_filter.mp hS).2)
  have h1 := le_maxDef (induceFinset G s) (Y ∩ s)
  have h2 : (Y \ s).card ≤ ((Finset.univ : Finset V) \ s).card := by
    refine Finset.card_le_card ?_
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hv).2⟩
  have h3 := card_inter_add_card_sdiff Y s
  simp only [defOf] at h1 ⊢
  omega

/-- **THE DEFICIENCY SPLITS IN TWO UNDER AN ANTICOMPLETE DECOMPOSITION, in linear form.**  If
`A ∪ B` covers the vertices of `Y` and no edge joins `A` to `B`, then

* the vertices of `Y` split into `Y ∩ A` and `Y ∩ B`, and
* the independent sets of `Y` split into those of `Y ∩ A` in `G[A]` and those of `Y ∩ B` in `G[B]`.

These are the two linear facts from which the additivity of the deficiency follows. -/
theorem card_indepCard_anticover_add {G : SimpleGraph V} {A B Y : Finset V} (h : Anticover G A B)
    (hY : Y ⊆ A ∪ B) :
    Y.card = (Y ∩ A).card + (Y ∩ B).card ∧
      indepCard G Y = indepCard (induceFinset G A) (Y ∩ A)
        + indepCard (induceFinset G B) (Y ∩ B) := by
  have hcard : Y.card = (Y ∩ A).card + (Y ∩ B).card := by
    have heq : Y = (Y ∩ A) ∪ (Y ∩ B) := by
      ext v
      constructor
      · intro hv
        by_cases hA : v ∈ A
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv, hA⟩)
        · have hB : v ∈ B := by
            rcases Finset.mem_union.mp (hY hv) with hmem | hmem
            · exact absurd hmem hA
            · exact hmem
          exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hv, hB⟩)
      · intro hmem
        rcases Finset.mem_union.mp hmem with h | h
        · exact Finset.mem_inter.mp h |>.1
        · exact Finset.mem_inter.mp h |>.1
    have hdisj : Disjoint (Y ∩ A) (Y ∩ B) := by
      refine Finset.disjoint_left.2 ?_
      intro v hv1 hv2
      exact h.disjoint (Finset.mem_inter.mp hv1).2 (Finset.mem_inter.mp hv2).2
    calc Y.card = ((Y ∩ A) ∪ (Y ∩ B)).card := congrArg Finset.card heq
      _ = (Y ∩ A).card + (Y ∩ B).card := Finset.card_union_of_disjoint hdisj
  have hα : indepCard G Y = indepCard (induceFinset G A) (Y ∩ A)
      + indepCard (induceFinset G B) (Y ∩ B) := by
    refine le_antisymm ?_ ?_
    · refine Finset.sup_le_iff.mpr fun S hS => ?_
      have hSi : G.IsIndepSet S := (Finset.mem_filter.mp hS).2
      have hSA : S ∩ A ∈ indepSets (induceFinset G A) (Y ∩ A) :=
        (mem_indepSets_induceFinset (G := G) (Y := Y ∩ A) (s := A) (X := S ∩ A)
          (fun v hv => (Finset.mem_inter.mp hv).2) (fun v hv => by
            have hvI := Finset.mem_inter.mp hv
            exact Finset.mem_inter.mpr
              ⟨Finset.mem_of_subset (sub_of_mem_indepSets hS) hvI.1, hvI.2⟩)).mpr
            (IsIndepSet.subset hSi fun v hv => (Finset.mem_inter.mp hv).1)
      have hSB : S ∩ B ∈ indepSets (induceFinset G B) (Y ∩ B) :=
        (mem_indepSets_induceFinset (G := G) (Y := Y ∩ B) (s := B) (X := S ∩ B)
          (fun v hv => (Finset.mem_inter.mp hv).2) (fun v hv => by
            have hvI := Finset.mem_inter.mp hv
            exact Finset.mem_inter.mpr
              ⟨Finset.mem_of_subset (sub_of_mem_indepSets hS) hvI.1, hvI.2⟩)).mpr
            (IsIndepSet.subset hSi fun v hv => (Finset.mem_inter.mp hv).1)
      have h1 := le_indepCard hSA
      have h2 := le_indepCard hSB
      have h3 := card_inter_add_card_sdiff S A
      -- `S ⊆ A ∪ B`, so the two halves of `S` are `S ∩ A` and `S ∩ B`
      have h4 : S \ A = S ∩ B := by
        ext v
        constructor
        · intro hv
          have hvA := Finset.mem_sdiff.mp hv
          have hmem := hY (sub_of_mem_indepSets hS hvA.1)
          rcases Finset.mem_union.mp hmem with h | h
          · exact absurd h hvA.2
          · exact Finset.mem_inter.mpr ⟨hvA.1, h⟩
        · intro hv
          have hvI := Finset.mem_inter.mp hv
          refine Finset.mem_sdiff.mpr ⟨hvI.1, ?_⟩
          intro hnA
          exact h.disjoint hnA hvI.2
      have h3' : S.card = (S ∩ A).card + (S ∩ B).card := by
        rw [← h4]
        exact h3.symm
      omega
    · obtain ⟨SA, hSAsub, hSAi, hSAcard⟩ := exists_indepCard (induceFinset G A) (Y ∩ A)
      obtain ⟨SB, hSBsub, hSBi, hSBcard⟩ := exists_indepCard (induceFinset G B) (Y ∩ B)
      have hmem : SA ∪ SB ∈ indepSets G Y :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.Subset.trans
              (show SA ∪ SB ⊆ (Y ∩ A) ∪ (Y ∩ B) by
                intro v hv
                rcases Finset.mem_union.mp hv with hv' | hv'
                · exact Finset.mem_union_left _ (Finset.mem_of_subset hSAsub hv')
                · exact Finset.mem_union_right _ (Finset.mem_of_subset hSBsub hv'))
              (fun v hv => by
                rcases Finset.mem_union.mp hv with hv' | hv'
                · exact (Finset.mem_inter.mp hv').1
                · exact (Finset.mem_inter.mp hv').1)), ?_⟩
      · refine le_trans ?_ (le_indepCard hmem)
        have hdisjSA : Disjoint SA SB := by
          refine Finset.disjoint_left.2 ?_
          intro v hv1 hv2
          have hh1 := Finset.mem_of_subset hSAsub hv1
          have hh2 := Finset.mem_of_subset hSBsub hv2
          exact h.disjoint (Finset.mem_inter.mp hh1).2 (Finset.mem_inter.mp hh2).2
        rw [Finset.card_union_of_disjoint hdisjSA, hSAcard, hSBcard]
      · refine isIndepSet_of_intro fun v w hv hw hne hadj => ?_
        have hv' : v ∈ SA ∪ SB := Finset.mem_coe.mp hv
        have hw' : w ∈ SA ∪ SB := Finset.mem_coe.mp hw
        have inA : ∀ v ∈ SA, v ∈ A := fun v hv => by
          have hh := Finset.mem_of_subset hSAsub hv
          exact Finset.mem_inter.mp hh |>.2
        have inB : ∀ v ∈ SB, v ∈ B := fun v hv => by
          have hh := Finset.mem_of_subset hSBsub hv
          exact Finset.mem_inter.mp hh |>.2
        rcases Finset.mem_union.mp hv' with hvA | hvB <;> rcases Finset.mem_union.mp hw' with hwA | hwB
        · exact IsIndepSet.apply' hSAi hvA hwA hne (induce_adj.mpr ⟨inA _ hvA, inA _ hwA, hadj⟩)
        · exact (h.anticomplete (inA _ hvA) (inB _ hwB)) hadj
        · exact absurd hadj
            (fun hAdj => h.anticomplete (inA _ hwA) (inB _ hvB) hAdj.symm)
        · exact IsIndepSet.apply' hSBi hvB hwB hne (induce_adj.mpr ⟨inB _ hvB, inB _ hwB, hadj⟩)
  exact ⟨hcard, hα⟩

/-- **THE DEFICIENCY OF A VERTEX SET SPLITS (UP TO THE ZERO TRUNCATION) OVER AN ANTICOMPLETE
DECOMPOSITION OF IT.**  If `A ∪ B` covers the vertices of `Y` and no edge joins `A` to `B`, then the
deficiency of `Y` in `G` is **at most** the sum of the deficiencies of `Y ∩ A` in `G[A]` and of
`Y ∩ B` in `G[B]`.

Note that *equality* fails, and this is a genuine feature of the deficiency rather than an artefact:
for `Y` = a triangle disjoint from one isolated vertex, split into the two parts, the deficiency of
`Y` is `0` while the sum of the deficiencies of the parts is `1 + 0 = 1`.  The obstruction is the
truncation at zero, which is why the counting statement `card_indepCard_anticover_add` above is the
exact (linear) form. -/
theorem defOf_le_add_of_anticover {G : SimpleGraph V} {A B Y : Finset V} (h : Anticover G A B)
    (hY : Y ⊆ A ∪ B) :
    defOf G Y ≤ defOf (induceFinset G A) (Y ∩ A) + defOf (induceFinset G B) (Y ∩ B) := by
  obtain ⟨hcard, hα⟩ := card_indepCard_anticover_add h hY
  simp only [defOf, hcard, hα, Nat.mul_add]
  exact sub_le_add_sub _ _ _ _

/-- **THE DEFICIENCY OF A GRAPH IS AT MOST THE SUM OF THE DEFICIENCIES OF THE PIECES OF AN
ANTICOMPLETE DECOMPOSITION** — the arithmetic companion of
`JSP90.closeToBipartite_of_anticover` (`JSPProblem/Optimal.lean`), which is the additive companion for
the *conclusion*.  Together they say: the number of vertices one must delete from an anticomplete
decomposition is the sum of what the pieces require, and the deficiency — a lower bound for that
number — is at most the sum of the deficiencies of the pieces.

The *converse* (equality for `MaxDef`) is not proved here: it needs the additional fact that a vertex
of `X \ s` is isolated in `G[s]`, so that adding it to `X` raises `|X|` and `α(G[s][X])` by the same
amount and leaves `defOf` unchanged.  The per-vertex-set statement, which is what the decomposition
families of rounds 43–48 use, is `defOf_anticover_add` above. -/
theorem maxDef_le_add_of_anticover {G : SimpleGraph V} {A B : Finset V} (h : Anticover G A B) :
    MaxDef G ≤ MaxDef (induceFinset G A) + MaxDef (induceFinset G B) := by
  obtain ⟨Y, hY⟩ := exists_eq_maxDef G
  obtain ⟨hcard, hα⟩ := card_indepCard_anticover_add h
    (by simpa only [h.cover] using (Finset.subset_univ (Y : Finset V)))
  have h1 := le_maxDef (induceFinset G A) (Y ∩ A)
  have h2 := le_maxDef (induceFinset G B) (Y ∩ B)
  have hgoal : defOf G Y ≤ MaxDef (induceFinset G A) + MaxDef (induceFinset G B) :=
    le_trans (defOf_le_add_of_anticover h
      (by simpa only [h.cover] using (Finset.subset_univ (Y : Finset V))))
      (add_le_add h1 h2)
  exact hY ▸ hgoal

end Arithmetic

/-! ## Part 7 — what a linear statement about the deficiency would give -/

section Linear

/-- **A LINEAR STATEMENT ABOUT THE DEFICIENCY WOULD PROVE THE WHOLE OF ERDŐS #73.**  If there is a
single constant `C` such that *every* graph is the union of a bipartite graph and `C * MaxDef G`
vertices, then `jsp_000090_main` follows, with the explicit constant `C * k` for the parameter `k`.
This is a statement about the *function* `τ / MaxDef` rather than about the family `k ↦ f(k)`, and
it is a strictly weaker input than the Erdős–Pósa theorem of `JSPProblem/Transversal.lean`. -/
def LinearErdős73 (C : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), CloseToBipartite (C * MaxDef G) G

/-- **ERDŐS #73 FOLLOWS FROM ANY `LinearErdős73 C`.**  The constant for the parameter `k` is then
`C * k`. -/
theorem erdos73Of_linearErdős73 (hC : LinearErdős73.{u} C) : ∀ k, Erdős73.{u} k := by
  intro k
  refine ⟨C * k, fun W instW G hG => ?_⟩
  have hle : MaxDef G ≤ k := maxDef_le_of_locIndep hG
  exact closeToBipartite_mono (Nat.mul_le_mul_left C hle) (hC W instW G)

/-- **THE LINEAR STATEMENT WITH `C = 0` IS FALSE**, and the witness is the triangle `K_3`, which has
deficiency `1` and is not bipartite.  So the constant `C` of `LinearErdős73` is a genuine parameter
and not a formality. -/
theorem not_linearErdős73_zero : ¬ LinearErdős73.{0} 0 := by
  intro h
  obtain ⟨X, hX, hb⟩ := h (Fin 3) inferInstance (SimpleGraph.completeGraph (Fin 3))
  rw [Nat.zero_mul] at hX
  have hXempty : X = (∅ : Finset (Fin 3)) := Finset.card_eq_zero.mp (Nat.le_zero.mp hX)
  rw [hXempty, deleteFinset_empty] at hb
  exact not_isBipartite_completeGraph_three hb

/-- **A BOUNDED DEFICIENCY IS A BOUNDED PACKING NUMBER, IN NUMERICAL FORM.**  This is the whole of
the packing half of the strategy, restated: `MaxDef G ≤ r` gives `ν(G) ≤ r`, so the *only* input
the Erdős–Pósa route still needs is a bound on the transversal number in terms of `MaxDef`. -/
theorem oddCycle_packing_le_of_maxDef_le {G : SimpleGraph V} {r : ℕ} (h : MaxDef G ≤ r) :
    ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r := by
  intro C hC
  exact card_le_of_maxDef_le h hC

end Linear

end

end JSP90
