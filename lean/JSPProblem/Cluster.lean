/-
# JSP-000090, round 104 — **cluster graphs: Erdős's hypothesis and his conclusion coincide**

This file is a **new attack family** (the forty-fifth).  Every earlier family attacks the
statement of Erdős Problem #73 by *decomposing* the graph — components, 1-cuts, 2-cuts, residues,
fans, packings, colourings, deficiency, edge counts — and every one of them ends with the same
statement, "a bounded odd cycle packing number forces a bounded odd cycle transversal"
(`JSP90.OddCycleErdosPosa r`, Reed–Robertson–Seymour–Thomas).

This file attacks from the other side: **the class on which the conclusion of Erdős #73 is not
merely bounded but is known exactly**.  It is the classical class of *cluster graphs* — graphs that
are disjoint unions of complete graphs — and on this class the answer is exact:

```lean
JSP90.maxDef_cluster                     : MaxDef G = ∑ C ∈ 𝒬, (|C| - 2)
JSP90.closeToBipartite_iff_maxDef_cluster : CloseToBipartite m G ↔ MaxDef G ≤ m
JSP90.erdos73On_of_cluster               : LocIndep k G → CloseToBipartite k G
```

That last line is **a new instance of the headline theorem with the optimal constant
`f(k) = k`** — the same constant as `JSP90.erdos73On_of_disjointOddCycles` of round 98 and
`JSP90.erdos73On_of_maxDegLe_two` of round 100, but on a **strictly larger class**:

* `JSP90.erdos73On_of_disjointOddCycles` needs `DisjointFamily (OddCycles G)`, i.e. *any two odd
  cycles of `G` are vertex-disjoint*.  A cluster graph with a `K_5` component fails this, because
  the triangle `{0,1,2}` and the Hamiltonian cycle `0-1-2-3-4-0` meet — the dev already records
  this as `JSP90.not_oddCyclesDisjoint_completeGraph_five`;
* the cluster class contains `K_5 ⊔ K_5`, `K_4 ⊔ K_3`, `K_7` and every disjoint union of these, so
  the hypothesis of this round is *strictly weaker* than round 98's, the constant is the same, and
  it is still optimal (`JSP90.erdos73_lower_bound`).

So the identity function of round 98 does **not** stop at "the odd cycles are pairwise disjoint":
it covers every graph whose pieces are complete.  What is needed beyond this class is not a larger
class but a *different constant*.

## The mathematics

For a cluster graph, three quantities that are only comparable in general are all **equal**:

| quantity | value on a cluster graph |
| --- | --- |
| independence number `α(G[X])`, for every `X` | the number of pieces met by `X` |
| maximum deficiency `MaxDef G` | `∑ (|C| - 2)` |
| odd cycle transversal number `τ(G)` | `∑ (|C| - 2)` |

so the whole of Erdős #73 becomes a statement about the sizes of the pieces:

```lean
LocIndep k G         ↔  MaxDef G ≤ k   (JSP90.locIndep_iff_maxDef_le, round 54)
CloseToBipartite m G ↔  MaxDef G ≤ m   (this file)
```

## What is proved

1. `JSP90.indepCard_cluster` — **the counting lemma**: `α(G[X]) = #{C ∈ 𝒬 : X ∩ C ≠ ∅}` for *every*
   vertex set `X`.  An independent set meets each piece (a clique) in at most one vertex, and one
   vertex from each met piece is independent because the pieces are anticomplete.
2. `JSP90.defOf_le_sum_cost`, `JSP90.maxDef_cluster` — **the maximum deficiency of a cluster graph
   is the sum of the piece costs**, `MaxDef G = ∑_{C ∈ 𝒬} (|C| - 2)`; the upper bound holds for
   every vertex set and the lower bound is read off `X = V`.
3. `JSP90.exists_oddCycle_transversal` — **an optimal odd cycle transversal of exactly that size
   exists**: `∃ D, D.card = MaxDef G ∧ HitsOddCycles G D`.  Two vertices are removed from every
   piece of at least three vertices; a cycle of `G` lies in a single piece
   (`JSP90.isOddCycle_sub_anticoverCoverFamily`) and has at least three vertices, so it cannot
   survive.  With `JSP90.maxDef_le_of_hitsOddCycles` this says `τ(G) = MaxDef G`: the sandwich
   `ν(G) ≤ MaxDef G ≤ τ(G)` of round 54 is an equality on this class.
4. `JSP90.closeToBipartite_iff_maxDef_cluster`, `JSP90.closeToBipartite_iff_cluster_cost` — the
   **exact value of the conclusion of Erdős #73 on the class**.
5. **`JSP90.erdos73On_of_cluster` — a new instance of the headline theorem with the optimal
   constant `k`**, strictly weaker in hypothesis than round 98's, plus
   `JSP90.erdos73On_of_cluster_univ` in the house style.
6. `JSP90.cluster_isBipartite_iff`, `JSP90.erdos73On_cluster_zero` — `G.IsBipartite ↔ every piece
   has at most two vertices`, so the class contains the proved case `k = 0`
   (`JSP90.erdos73_zero`) with the exact constant.
7. `JSP90.maxDef_cluster_univ` — for a decomposition with a single piece the formula of this file
   reads `MaxDef G = |V| - 2`, i.e. it contains `JSP90.maxDef_completeGraph` of round 54.

## What is *not* proved

`jsp_000090_main` is still not declared and `JSP90.OddCycleErdosPosa r` is unchanged.  Apart from
locating the boundary of the identity function, this file proves nothing about graphs whose pieces
are not complete.

## File conventions

No statement in this file mentions a concrete vertex type (`Fin n`, `Fin 3 × Fin k`): the concrete
witnesses live in `lean/JSPProblem/ClusterSharp.lean`, which deliberately has **no** `DecidableEq`
instance in scope (see the toolchain notes in `discovery/JSP-000090/policy.json`). -/

import JSPProblem.Deficiency
import JSPProblem.Additive
import JSPProblem.Weight

namespace JSP90

open Finset Fintype Set

universe u

variable {V : Type u} [Fintype V]

noncomputable section

local instance instDecidableEqCluster : DecidableEq V := Classical.decEq V

/-- The decider for "is `S` an independent set of `G`?" (as in `JSPProblem/Deficiency.lean`). -/
local instance instDecidablePredIsIndepSetCluster (G : SimpleGraph V) :
    DecidablePred fun S : Finset V => G.IsIndepSet S := fun _ => Classical.propDecidable _

/-! ## 0. Two counting lemmas about unions of pairwise disjoint pieces -/

/-- **The cardinality of a union of pairwise disjoint finsets is the sum of their
cardinalities.**  (Proved by induction, because `Finset.card_biUnion` at this revision wants the
hypothesis as a `Multiset.PairwiseDisjoint`, which is awkward to build for a finset of finsets.) -/
theorem card_biUnion_eq_sum {ι : Type*} {P : Finset ι} (g : ι → Finset V)
    (hdis : ∀ (X Y : ι), X ∈ P → Y ∈ P → X ≠ Y → ∀ (x : V), x ∈ g X → x ∉ g Y) :
    (P.biUnion g).card = ∑ X ∈ P, (g X).card := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert X t hX ih =>
      have hne : ∀ (Y : ι), Y ∈ t → X ≠ Y := fun Y hY hXY => by
        subst hXY
        exact hX hY
      have hdis' : ∀ (Y : ι), Y ∈ t → ∀ (x : V), x ∈ g X → x ∉ g Y :=
        fun Y hY x hx hx2 => absurd hx2
          (hdis X Y (Finset.mem_insert_self X t) (Finset.mem_insert_of_mem hY) (hne Y hY) x hx)
      have heq : (t.biUnion g).card = ∑ Y ∈ t, (g Y).card :=
        ih (hdis := fun Y Z hY hZ hYZ x hx hx2 => absurd hx2
          (hdis Y Z (Finset.mem_insert_of_mem hY) (Finset.mem_insert_of_mem hZ) hYZ x hx))
      have hle : (t.biUnion g).card ≤ ∑ Y ∈ t, (g Y).card := Nat.le_of_eq heq
      have hge : ∑ Y ∈ t, (g Y).card ≤ (t.biUnion g).card := Nat.le_of_eq heq.symm
      rw [Finset.biUnion_insert, Finset.sum_insert hX]
      refine le_antisymm ?_ ?_
      · exact Nat.le_trans (Finset.card_union_le _ _)
          (Nat.add_le_add (le_refl _) hle)
      · have hempty : g X ∩ t.biUnion g = ∅ :=
          Finset.disjoint_iff_inter_eq_empty.mp (Finset.disjoint_left.mpr fun x hx hx2 => by
            obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx2
            exact (hdis' C hC x hx) hxC)
        have h2 : (g X).card + (t.biUnion g).card = (g X ∪ t.biUnion g).card := by
          have h := Finset.card_union_add_card_inter (g X) (t.biUnion g)
          rw [hempty, Finset.card_empty] at h
          omega
        exact (Nat.add_le_add_left hge _).trans (Nat.le_of_eq h2)

/-! ## 1. The class: graphs that are disjoint unions of complete graphs -/

/-- **`𝒬` is a cluster decomposition of `G`** if

* the pieces of `𝒬` are pairwise disjoint and pairwise anticomplete and they **cover** `V`
  (`AnticoverCoverFamily`, so every cycle of `G` lies in one piece);
* every piece has **at least two** vertices — a piece of size `1` would be an isolated vertex and
  would contribute `-1` to the deficiency sum, which is why it is excluded here; and
* every piece is a **clique**.

A graph admitting such a decomposition is a *cluster graph* without isolated vertices. -/
def ClusterDecomposition (G : SimpleGraph V) (𝒬 : Finset (Finset V)) : Prop :=
  AnticoverCoverFamily G 𝒬 ∧
    (∀ X ∈ 𝒬, 2 ≤ X.card) ∧
    (∀ X ∈ 𝒬, ∀ p q : V, p ∈ X → q ∈ X → p ≠ q → G.Adj p q) ∧
    (∀ x : V, ∃ X ∈ 𝒬, x ∈ X)

/-- The pieces of `𝒬` that a vertex set `X` meets. -/
def piecesMet (𝒬 : Finset (Finset V)) (X : Finset V) : Finset (Finset V) :=
  𝒬.filter (fun C : Finset V => (X ∩ C).Nonempty)

theorem mem_piecesMet {𝒬 : Finset (Finset V)} {X C : Finset V} :
    C ∈ piecesMet 𝒬 X ↔ C ∈ 𝒬 ∧ (X ∩ C).Nonempty :=
  Finset.mem_filter

/-- A piece met by `X` lies in `𝒬` and is met by `X`. -/
theorem piecesMet_of_mem {𝒬 : Finset (Finset V)} {X C : Finset V} (hC : C ∈ piecesMet 𝒬 X) :
    C ∈ 𝒬 ∧ (X ∩ C).Nonempty := by
  rw [mem_piecesMet] at hC
  exact hC

/-- A piece of `𝒬` met by `X` is a piece met by `X`. -/
theorem mem_piecesMet_of_mem {𝒬 : Finset (Finset V)} {X C : Finset V} (hC : C ∈ 𝒬)
    (hne : (X ∩ C).Nonempty) : C ∈ piecesMet 𝒬 X := by
  rw [mem_piecesMet]
  exact ⟨hC, hne⟩

/-- **The pieces met by a subset are met by the whole set.** -/
theorem piecesMet_mono {𝒬 : Finset (Finset V)} {S X : Finset V} (hS : S ⊆ X) :
    piecesMet 𝒬 S ⊆ piecesMet 𝒬 X := by
  intro C hC
  obtain ⟨hC', ⟨v, hv⟩⟩ := piecesMet_of_mem hC
  obtain ⟨hvS, hvC⟩ := Finset.mem_inter.mp hv
  exact mem_piecesMet_of_mem hC' ⟨v, Finset.mem_inter.mpr ⟨hS hvS, hvC⟩⟩

/-! ## 2. The pieces are pairwise disjoint -/

theorem inter_eq_empty {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) {X Y : Finset V}
    (hX : X ∈ 𝒬) (hY : Y ∈ 𝒬) (hne : X ≠ Y) : X ∩ Y = ∅ :=
  hd.1.1 X hX Y hY hne

theorem anticomplete {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) {X Y : Finset V}
    (hX : X ∈ 𝒬) (hY : Y ∈ 𝒬) (hne : X ≠ Y) {x : V} (hx : x ∈ X) {y : V} (hy : y ∈ Y) :
    ¬ G.Adj x y :=
  hd.1.2 X hX Y hY hne x hx y hy

theorem two_le_card {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) {X : Finset V}
    (hX : X ∈ 𝒬) : 2 ≤ X.card :=
  hd.2.1 X hX

theorem clique {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) {X : Finset V}
    (hX : X ∈ 𝒬) {p q : V} (hp : p ∈ X) (hq : q ∈ X) (hne : p ≠ q) : G.Adj p q :=
  hd.2.2.1 X hX p q hp hq hne

theorem cover {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) {x : V} :
    ∃ X ∈ 𝒬, x ∈ X :=
  hd.2.2.2 x

/-- **Every piece meets the whole vertex set**: the pieces are the parts of a partition. -/
theorem piecesMet_univ {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) :
    piecesMet 𝒬 (Finset.univ : Finset V) = 𝒬 := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro C hC
    exact (piecesMet_of_mem hC).1
  · intro C hC
    have htwo : 2 ≤ C.card := two_le_card hd hC
    obtain ⟨x, hx⟩ : (C : Finset V).Nonempty := Finset.card_ne_zero.mp (by omega)
    exact mem_piecesMet_of_mem hC ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_univ _, hx⟩⟩

/-- **The `PairwiseDisjoint` certificate that `JSP90.card_biUnion_eq_sum` asks for, for the family
`C ↦ X ∩ C` over pairwise disjoint pieces.** -/
theorem pairwiseDisjoint_inter {𝒬 : Finset (Finset V)} {X : Finset V}
    (hdisj : ∀ (C Y : Finset V), C ∈ 𝒬 → Y ∈ 𝒬 → C ≠ Y → C ∩ Y = ∅) :
    ∀ (C Y : Finset V), C ∈ 𝒬 → Y ∈ 𝒬 → C ≠ Y →
      ∀ (z : V), z ∈ X ∩ C → z ∉ X ∩ Y := by
  intro C Y hC hY hne z hz hz2
  have hbad : z ∈ C ∩ Y := Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hz).2, (Finset.mem_inter.mp hz2).2⟩
  rw [hdisj C Y hC hY hne] at hbad
  simp at hbad

/-- An independent set meets every piece in at most one vertex: a piece is a clique. -/
theorem card_inter_le_one {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬)
    {C X S : Finset V} (hC : C ∈ 𝒬) (hSsub : S ⊆ X) (hSi : G.IsIndepSet S) :
    (S ∩ C).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  by_contra hne
  obtain ⟨haS, haC⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbS, hbC⟩ := Finset.mem_inter.mp hb
  exact False.elim ((IsIndepSet.apply' hSi haS hbS hne) (clique hd hC haC hbC hne))

/-! ## 3. The counting lemma: `α(G[X])` counts the pieces met by `X` -/

/-- **THE COUNTING LEMMA, upper half.**  An independent subset of `X` meets each piece in at most
one vertex, so its size is at most the number of pieces it meets. -/
theorem card_le_piecesMet {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) {S X : Finset V}
    (hSsub : S ⊆ X) (hSi : G.IsIndepSet S) : S.card ≤ (piecesMet 𝒬 X).card := by
  -- each vertex of `S` is sent to a piece containing it; the pieces are pairwise disjoint, so the
  -- map is injective on `S` and `S` injects into the pieces met by `X`
  have key : ∀ v : V, ∃ C ∈ 𝒬, v ∈ C := fun v => cover hd (x := v)
  obtain ⟨g, hgmem⟩ : ∃ g : V → Finset V, ∀ v, g v ∈ 𝒬 ∧ v ∈ g v :=
    ⟨fun v => Classical.choose (key v), fun v => (key v).choose_spec⟩
  refine Finset.card_le_card_of_injOn g ?_ ?_
  · intro v hv
    have hvS : v ∈ S := Finset.mem_coe.mp hv
    exact mem_piecesMet_of_mem (hgmem v).1
      ⟨v, Finset.mem_inter.mpr ⟨hSsub hvS, (hgmem v).2⟩⟩
  · intro a ha b hb hab
    have haS : a ∈ S := Finset.mem_coe.mp ha
    have hbS : b ∈ S := Finset.mem_coe.mp hb
    by_cases hEq : g a = g b
    · -- two points of `S` in one piece: that piece is a clique, so `S` is not independent
      have hbP : b ∈ g a := hEq ▸ (hgmem b).2
      by_contra hcon
      have hsub2 : ({a, b} : Finset V) ⊆ S ∩ g a := Finset.insert_subset
        (Finset.mem_inter.mpr ⟨haS, (hgmem a).2⟩)
        (Finset.insert_subset (Finset.mem_inter.mpr ⟨hbS, hbP⟩) (Finset.empty_subset _))
      have h1 : (S ∩ g a).card ≤ 1 := card_inter_le_one hd (hgmem a).1 hSsub hSi
      have hpair : 2 ≤ ({a, b} : Finset V).card := by
        rw [Finset.card_pair_eq_two_iff.mpr hcon]
      have h2 : 2 ≤ (S ∩ g a).card := le_trans hpair (Finset.card_le_card hsub2)
      omega
    · exact False.elim (hEq hab)

/-- A choice of one vertex per met piece is injective: two different pieces are disjoint. -/
theorem inj_pieces_choice {𝒬 P : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬)
    (hPsub : ∀ C ∈ P, C ∈ 𝒬) {g : {C // C ∈ P} → V} (hg : ∀ e, g e ∈ (e.val : Finset V)) :
    Function.Injective g := by
  intro e e' heq
  by_cases hEq : e = e'
  · exact hEq
  · have hmem : g e' ∈ e.val ∩ e'.val := Finset.mem_inter.mpr ⟨heq ▸ hg e, hg e'⟩
    have hempty := inter_eq_empty hd (hPsub e.val e.property) (hPsub e'.val e'.property)
      (fun h => hEq (Subtype.ext h))
    rw [hempty] at hmem
    simp at hmem

/-- **THE COUNTING LEMMA, lower half.**  Choosing one vertex in each piece met by `X` gives an
independent set of size `#{pieces met by X}`. -/
theorem exists_indep_onePerPiece {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬)
    {X : Finset V} :
    ∃ S : Finset V, S ⊆ X ∧ G.IsIndepSet S ∧ (piecesMet 𝒬 X).card ≤ S.card := by
  have hne : ∀ e : {C // C ∈ piecesMet 𝒬 X}, (X ∩ e.val).Nonempty := by
    intro e
    have hmem : e.val ∈ piecesMet 𝒬 X := e.property
    exact (piecesMet_of_mem hmem).2
  obtain ⟨g, hg⟩ : ∃ g : {C // C ∈ piecesMet 𝒬 X} → V,
      ∀ e, g e ∈ (X ∩ e.val) := by
    refine ⟨fun e => Classical.choose (hne e), fun e => Classical.choose_spec (hne e)⟩
  set S : Finset V := (piecesMet 𝒬 X).attach.image g with hS
  refine ⟨S, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_inter.mp (hg e)).1
  · refine isIndepSet_of_intro fun a b ha hb hne hab => ?_
    obtain ⟨ea, -, hea⟩ := Finset.mem_image.mp ha
    obtain ⟨eb, -, heb⟩ := Finset.mem_image.mp hb
    by_cases hEq : ea = eb
    · exact False.elim (hne (Eq.trans hea.symm (Eq.trans (congrArg g hEq) heb)))
    · exact False.elim ((anticomplete hd (piecesMet_of_mem ea.2).1 (piecesMet_of_mem eb.2).1
        (fun h => hEq (Subtype.ext h)) (hea ▸ (Finset.mem_inter.mp (hg ea)).2)
        (heb ▸ (Finset.mem_inter.mp (hg eb)).2)) hab)
  · rw [hS, Finset.card_image_of_injective _ (inj_pieces_choice hd
        (fun C hC => (piecesMet_of_mem hC).1) (fun e => (Finset.mem_inter.mp (hg e)).2)),
      Finset.card_attach]

/-- **THE COUNTING LEMMA: on a cluster graph the independence number of an induced subgraph is
exactly the number of pieces that subgraph meets**, `α(G[X]) = #{C ∈ 𝒬 : X ∩ C ≠ ∅}`.  A largest
independent set of `G[X]` picks one vertex from every piece met by `X`, and no more. -/
theorem indepCard_cluster {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) (X : Finset V) :
    indepCard G X = (piecesMet 𝒬 X).card := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le_iff.mpr fun S hS => ?_
    exact card_le_piecesMet hd (sub_of_mem_indepSets hS) (Finset.mem_filter.mp hS).2
  · obtain ⟨S, hSsub, hSi, hle⟩ := exists_indep_onePerPiece hd (X := X)
    exact calc (piecesMet 𝒬 X).card ≤ S.card := hle
      _ ≤ indepCard G X := le_indepCard_of_isIndepSet hSsub hSi

/-! ## 4. The maximum deficiency of a cluster graph -/

/-- The pieces partition every vertex set, so its size is the sum of the sizes of the parts. -/
theorem card_le_sum_card_inter {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬)
    (X : Finset V) : X.card ≤ ∑ C ∈ 𝒬, (X ∩ C).card := by
  have hbi : X = 𝒬.biUnion (fun C : Finset V => X ∩ C) := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro v hv
      obtain ⟨C, hC, hCv⟩ := cover hd (x := v)
      exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_inter.mpr ⟨hv, hCv⟩⟩
    · intro v (hv : v ∈ 𝒬.biUnion (fun C : Finset V => X ∩ C))
      have hex : ∃ C ∈ 𝒬, v ∈ X ∩ C := Finset.mem_biUnion.mp hv
      obtain ⟨C, hC, hX⟩ := hex
      exact (Finset.mem_inter.mp hX).1
  calc X.card ≤ ((𝒬.biUnion (fun C : Finset V => X ∩ C))).card :=
        Finset.card_le_card (fun _ hv => hbi ▸ hv)
    _ = ∑ C ∈ 𝒬, (X ∩ C).card := card_biUnion_eq_sum (ι := Finset V) (P := 𝒬)
        (g := fun C : Finset V => X ∩ C) (by
          intro C Y hC hY hne z hz hz2
          have hbad : z ∈ C ∩ Y := Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hz).2, (Finset.mem_inter.mp hz2).2⟩
          rw [inter_eq_empty hd hC hY hne] at hbad
          simp at hbad)

/-- A piece not met by `X` is met by `X` in no vertex at all. -/
theorem inter_eq_empty_of_not_mem_piecesMet {𝒬 : Finset (Finset V)} {X C : Finset V}
    (hC : C ∈ 𝒬) (hnP : C ∉ piecesMet 𝒬 X) : X ∩ C = ∅ := by
  by_contra hne
  exact hnP (mem_piecesMet_of_mem hC (Finset.nonempty_iff_ne_empty.mpr hne))

/-- **The arithmetic of the cost of a family of pieces**: if every piece has at least two
elements, then `|C| = (|C| - 2) + 2`, so `∑ |C| = (∑ (|C| - 2)) + 2 * |𝒬|`. -/
theorem sum_card_eq_sum_cost {s : Finset (Finset V)} (h2 : ∀ C ∈ s, 2 ≤ C.card) :
    (∑ C ∈ s, C.card) = (∑ C ∈ s, (C.card - 2)) + 2 * s.card := by
  have h1 : (∑ C ∈ s, C.card) = ∑ C ∈ s, ((C.card - 2) + 2) :=
    Finset.sum_congr rfl fun C hC => (Nat.sub_add_cancel (h2 C hC)).symm
  rw [h1, Finset.sum_add_distrib]
  have hs : (∑ x ∈ s, (2 : ℕ)) = 2 * s.card := by simp [Nat.mul_comm]
  rw [hs]

/-- The same, in the form in which it is used: the total cost is the total size minus twice the
number of pieces. -/
theorem sum_cost_eq {s : Finset (Finset V)} (h2 : ∀ C ∈ s, 2 ≤ C.card) :
    (∑ C ∈ s, C.card) - 2 * s.card = ∑ C ∈ s, (C.card - 2) := by
  rw [sum_card_eq_sum_cost h2, Nat.add_sub_cancel]

/-- The size of the part of `X` inside a piece. -/
theorem card_inter_le_card (X C : Finset V) : (X ∩ C).card ≤ C.card := by
  refine Finset.card_le_card (s := X ∩ C) (t := C) ?_
  intro v hv
  exact (Finset.mem_inter.mp hv).2

/-- A piece not met by `X` contributes nothing to the sum over the pieces. -/
theorem card_inter_eq_zero_of_not_mem_piecesMet {𝒬 : Finset (Finset V)} {X C : Finset V}
    (hC : C ∈ 𝒬) (hnP : C ∉ piecesMet 𝒬 X) : (X ∩ C).card = 0 := by
  rw [inter_eq_empty_of_not_mem_piecesMet hC hnP, Finset.card_empty]

/-- **THE COST OF THE PIECES IS AN UPPER BOUND FOR THE DEFICIENCY OF EVERY VERTEX SET.**  Piece `C`
contributes at most `(X ∩ C).card - 2`, because the independence number of `G[X]` is exactly the
number of pieces met by `X` (`JSP90.indepCard_cluster`). -/
theorem defOf_le_sum_cost {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) (X : Finset V) :
    defOf G X ≤ ∑ C ∈ 𝒬, ((X ∩ C).card - 2) := by
  set P : Finset (Finset V) := piecesMet 𝒬 X with hP
  have hPsub : P ⊆ 𝒬 := fun C hC => (piecesMet_of_mem hC).1
  have h3 : ∀ C ∈ P, (X ∩ C).card ≤ ((X ∩ C).card - 2) + 2 := by
    intro C _
    by_cases h : 2 ≤ (X ∩ C).card
    · rw [Nat.sub_add_cancel h]
    · have h0 : (X ∩ C).card - 2 = 0 := Nat.sub_eq_zero_of_le (by omega)
      rw [h0]
      omega
  calc defOf G X = X.card - 2 * indepCard G X := rfl
    _ ≤ (∑ C ∈ 𝒬, (X ∩ C).card) - 2 * P.card := by
        rw [indepCard_cluster hd]
        exact Nat.sub_le_sub_right (card_le_sum_card_inter hd X) _
    _ = (∑ C ∈ P, (X ∩ C).card) - 2 * P.card := by
        rw [Finset.sum_subset hPsub (fun C hC hnP =>
          card_inter_eq_zero_of_not_mem_piecesMet hC hnP)]
    _ ≤ (∑ C ∈ P, ((X ∩ C).card - 2 + 2)) - 2 * P.card :=
        Nat.sub_le_sub_right (Finset.sum_le_sum fun C hC => h3 C hC) _
    _ = (∑ C ∈ P, ((X ∩ C).card - 2) + ∑ _ ∈ P, 2) - 2 * P.card := by
        rw [Finset.sum_add_distrib]
    _ = (∑ C ∈ P, ((X ∩ C).card - 2) + 2 * P.card) - 2 * P.card := by
        rw [show (∑ _ ∈ P, (2 : ℕ)) = 2 * P.card from by simp [Nat.mul_comm]]
    _ = ∑ C ∈ P, ((X ∩ C).card - 2) := by omega
    _ ≤ ∑ C ∈ 𝒬, ((X ∩ C).card - 2) := by
        refine le_of_eq (Finset.sum_subset (f := fun C : Finset V => (X ∩ C).card - 2) hPsub ?_)
        intro C hC hnP
        have hz := card_inter_eq_zero_of_not_mem_piecesMet hC hnP
        rw [hz, Nat.sub_eq_zero_of_le (by omega)]

/-- **THE MAXIMUM DEFICIENCY OF A CLUSTER GRAPH IS BOUNDED BY THE SUM OF THE PIECE COSTS.** -/
theorem maxDef_le_sum_cost {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) :
    MaxDef G ≤ ∑ C ∈ 𝒬, (C.card - 2) := by
  refine maxDef_le fun X => ?_
  exact defOf_le_sum_cost hd X |>.trans
    (Finset.sum_le_sum fun C _ => Nat.sub_le_sub_right (card_inter_le_card X C) 2)

/-- **The deficiency of the whole vertex set is exactly the sum of the piece costs.** -/
theorem defOf_univ_cluster {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) :
    defOf G (Finset.univ : Finset V) = ∑ C ∈ 𝒬, (C.card - 2) := by
  have hbi : (Finset.univ : Finset V) = 𝒬.biUnion (fun C : Finset V => (C : Finset V)) := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro v hv
      obtain ⟨C, hC, hCv⟩ := cover hd (x := v)
      exact Finset.mem_biUnion.mpr ⟨C, hC, hCv⟩
    · intro v (hv : v ∈ 𝒬.biUnion (fun C : Finset V => (C : Finset V)))
      exact Finset.mem_univ v
  have heq : (Finset.univ : Finset V).card = ∑ C ∈ 𝒬, C.card :=
    calc (Finset.univ : Finset V).card = ((𝒬.biUnion (fun C : Finset V => (C : Finset V)))).card :=
          congrArg Finset.card hbi
      _ = ∑ C ∈ 𝒬, C.card := card_biUnion_eq_sum (ι := Finset V) (P := 𝒬)
          (g := fun C : Finset V => (C : Finset V)) (by
            intro C Y hC hY hne x hx hx2
            have hbad : x ∈ C ∩ Y := Finset.mem_inter.mpr ⟨hx, hx2⟩
            rw [inter_eq_empty hd hC hY hne] at hbad
            simp at hbad)
  rw [show defOf G (Finset.univ : Finset V) = (Finset.univ : Finset V).card - 2 * indepCard G
      (Finset.univ : Finset V) from rfl,
    indepCard_cluster hd _, piecesMet_univ hd, heq,
    sum_cost_eq (fun C hC => two_le_card hd hC)]

/-- **THE MAXIMUM DEFICIENCY OF A CLUSTER GRAPH, EXACTLY.**
`MaxDef G = ∑ C ∈ 𝒬, (|C| - 2)`: on a cluster graph, Erdős's hypothesis is a statement about the
sizes of the pieces alone. -/
theorem maxDef_cluster {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) :
    MaxDef G = ∑ C ∈ 𝒬, (C.card - 2) := by
  refine le_antisymm (maxDef_le_sum_cost hd) ?_
  rw [← defOf_univ_cluster hd]
  exact le_maxDef G (Finset.univ)

/-! ## 5. An optimal odd cycle transversal of exactly that size exists -/

/-- A finset of at least three elements contains two distinct elements. -/
theorem exists_pair_mem_ne {C : Finset V} (h3 : 3 ≤ C.card) :
    ∃ a b : V, a ∈ C ∧ b ∈ C ∧ a ≠ b := by
  obtain ⟨a, ha⟩ := (Finset.card_ne_zero (s := C)).mp (by omega)
  have hcard : (C.erase a : Finset V).Nonempty :=
    (Finset.card_ne_zero (s := C.erase a)).mp (by
      rw [Finset.card_erase_of_mem ha]
      omega)
  obtain ⟨b, hb⟩ := hcard
  rw [Finset.mem_erase] at hb
  exact ⟨a, b, ha, hb.2, Ne.symm hb.1⟩

/-- The pieces of at least three vertices: the only pieces that cost anything. -/
def bigPieces (𝒬 : Finset (Finset V)) : Finset (Finset V) :=
  𝒬.filter (fun C : Finset V => 3 ≤ C.card)

theorem mem_bigPieces {𝒬 : Finset (Finset V)} {C : Finset V} :
    C ∈ bigPieces 𝒬 ↔ C ∈ 𝒬 ∧ 3 ≤ C.card :=
  Finset.mem_filter

/-- **AN OPTIMAL ODD CYCLE TRANSVERSAL OF A CLUSTER GRAPH.**  There is a set `D` of exactly
`MaxDef G` vertices meeting every odd cycle of `G`: take two vertices out of every piece of at least
three vertices.  With `JSP90.maxDef_le_of_hitsOddCycles` this pins the odd cycle transversal
number of `G` to `MaxDef G`, so the sandwich `ν(G) ≤ MaxDef G ≤ τ(G)` of round 54 is an equality on
this class. -/
theorem exists_oddCycle_transversal {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) :
    ∃ D : Finset V, D.card = MaxDef G ∧ HitsOddCycles G D := by
  set P : Finset (Finset V) := bigPieces 𝒬 with hP
  have hPsub' : ∀ C ∈ P, C ∈ 𝒬 := fun C hC => (mem_bigPieces.mp hC).1
  have key2 : ∀ (C : Finset V) (hC : C ∈ P), ∃ p : V × V,
      (p.1 ∈ C ∧ p.2 ∈ C ∧ p.1 ≠ p.2) := by
    intro C hC
    obtain ⟨a, b, ha, hb, hab⟩ := exists_pair_mem_ne (C := C) (mem_bigPieces.mp hC).2
    exact ⟨(a, b), ha, hb, hab⟩
  -- the family `fam C = C minus two elements` on the pieces of `P` (and empty elsewhere)
  set fam : Finset V → Finset V := fun (C : Finset V) =>
    if hC : C ∈ P then
      C \ {(Classical.choose (key2 C hC)).1, (Classical.choose (key2 C hC)).2} else ∅ with hfam
  have hpP : ∀ (C : Finset V) (hC : C ∈ P), (Classical.choose (key2 C hC)).1 ∈ C ∧
      (Classical.choose (key2 C hC)).2 ∈ C ∧ (Classical.choose (key2 C hC)).1 ≠
        (Classical.choose (key2 C hC)).2 := by
    intro C hC
    exact Classical.choose_spec (key2 C hC)
  have hvalP : ∀ (C : Finset V) (hC : C ∈ P), (fam C : Finset V) =
      C \ {(Classical.choose (key2 C hC)).1, (Classical.choose (key2 C hC)).2} := by
    intro C hC
    rw [hfam]
    simp only [dif_pos hC]
  have hfamP : ∀ C ∈ P, (fam C).card = C.card - 2 := by
    intro C hC
    have h3 : 3 ≤ C.card := (mem_bigPieces.mp hC).2
    have hsub : {(Classical.choose (key2 C hC)).1, (Classical.choose (key2 C hC)).2} ⊆ C :=
      Finset.insert_subset (hpP C hC).1
        (Finset.insert_subset (hpP C hC).2.1 (Finset.empty_subset _))
    rw [hvalP C hC, Finset.card_sdiff_of_subset hsub,
      Finset.card_pair_eq_two_iff.mpr (hpP C hC).2.2]
  have hfamne : ∀ C ∈ P, (fam C).Nonempty := by
    intro C hC
    have h3 : 3 ≤ C.card := (mem_bigPieces.mp hC).2
    refine Finset.card_ne_zero.mp ?_
    rw [hfamP C hC]
    omega
  have hfamInj : ∀ C ∈ P, ∀ Y ∈ P, fam C = fam Y → C = Y := by
    intro C hC Y hY heq
    by_contra hne
    have hCY : C ∩ Y = ∅ := inter_eq_empty hd (hPsub' C hC) (hPsub' Y hY) hne
    obtain ⟨x, hx⟩ := hfamne C hC
    have hxY : x ∈ fam Y := heq ▸ hx
    rw [hvalP C hC] at hx
    rw [hvalP Y hY] at hxY
    have hbad : x ∈ C ∩ Y := Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hxY).1⟩
    rw [hCY] at hbad
    simp at hbad
  set I : Finset (Finset V) := P.image fam with hI
  set D : Finset V := I.biUnion (fun C : Finset V => (C : Finset V)) with hD
  have hsum2 : (∑ D ∈ I, D.card) = ∑ C ∈ P, (fam C).card := by
    have h : (∑ C ∈ P, (fam C).card) = ∑ D ∈ P.image fam, D.card := by
      refine Finset.sum_bij (s := P) (t := P.image fam)
        (f := fun C : Finset V => (fam C).card) (g := fun D : Finset V => D.card)
        (fun (C : Finset V) (_ : C ∈ P) => fam C) ?_ ?_ ?_ ?_
      · intro C hC
        exact Finset.mem_image.mpr ⟨C, hC, rfl⟩
      · intro C hC Y hY h
        exact hfamInj C hC Y hY h
      · intro D hD
        obtain ⟨C, hC, hCD⟩ := Finset.mem_image.mp hD
        exact ⟨C, hC, hCD⟩
      · intro C _
        rfl
    rw [← hI] at h
    exact h.symm
  have hsum1 : D.card = ∑ D ∈ I, D.card := by
    rw [hD, card_biUnion_eq_sum (ι := Finset V) (P := I) (g := fun C : Finset V => (C : Finset V)) (by
      intro C Y hC hY hne x hx hx2
      obtain ⟨C0, hC0, heqC⟩ := Finset.mem_image.mp hC
      obtain ⟨Y0, hY0, heqY⟩ := Finset.mem_image.mp hY
      have hx' : x ∈ fam C0 := heqC.symm ▸ hx
      have hx'' : x ∈ fam Y0 := heqY.symm ▸ hx2
      rw [hvalP C0 hC0] at hx'
      rw [hvalP Y0 hY0] at hx''
      have hbad : x ∈ C0 ∩ Y0 := Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hx').1, (Finset.mem_sdiff.mp hx'').1⟩
      have hCY : C0 ∩ Y0 = ∅ := inter_eq_empty hd (hPsub' C0 hC0) (hPsub' Y0 hY0)
        (fun h => hne (heqC.symm.trans ((congrArg fam h).trans heqY)))
      rw [hCY] at hbad
      simp at hbad)]
  have hsum3 : (∑ C ∈ P, (fam C).card) = ∑ C ∈ 𝒬, (C.card - 2) := by
    calc (∑ C ∈ P, (fam C).card) = ∑ C ∈ P, (C.card - 2) :=
          Finset.sum_congr rfl fun C hC => hfamP C hC
      _ = ∑ C ∈ 𝒬, (C.card - 2) := by
        rw [Finset.sum_subset (fun C hC => hPsub' C hC) (fun C hC hnP => by
          have hle : C.card ≤ 2 := by
            have hnP' : C ∉ bigPieces 𝒬 := hnP
            rw [mem_bigPieces, not_and_or] at hnP'
            exact Or.elim hnP' (fun h => (h hC).elim) (fun h => by omega)
          rw [Nat.sub_eq_zero_of_le (by omega)])]
  have hcardD : D.card = ∑ C ∈ 𝒬, (C.card - 2) := hsum1.trans (hsum2.trans hsum3)
  refine ⟨D, ?_, ?_⟩
  · rw [hcardD, maxDef_cluster hd]
  · intro D' hD'
    obtain ⟨C, hC, hsub⟩ := isOddCycle_sub_anticoverCoverFamily hd.1
      (fun Y _ => Finset.subset_univ _) (fun {x} hx => cover hd (x := x))
      (isOddCycle_of_induceFinset_univ hD')
    have hle := Finset.card_le_card hsub
    have hcardC : 3 ≤ C.card := Nat.le_trans (isOddCycle_card_ge_three hD') hle
    have hCP : C ∈ P := mem_bigPieces.mpr ⟨hC, hcardC⟩
    have hne1 : (fam C ∩ D').Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hEmpty
      have hsub' : D' ⊆ {(Classical.choose (key2 C hCP)).1, (Classical.choose (key2 C hCP)).2} := by
        intro x hx
        by_contra hn
        have hxfam : x ∈ fam C := by
          rw [hvalP C hCP]
          exact Finset.mem_sdiff.mpr ⟨hsub hx, by simp [Finset.mem_insert, hn]⟩
        have hbad : x ∈ fam C ∩ D' := Finset.mem_inter.mpr ⟨hxfam, hx⟩
        rw [hEmpty] at hbad
        simp at hbad
      have h2 : D'.card ≤ ({(Classical.choose (key2 C hCP)).1,
          (Classical.choose (key2 C hCP)).2} : Finset V).card := Finset.card_le_card hsub'
      rw [Finset.card_pair_eq_two_iff.mpr (hpP C hCP).2.2] at h2
      have h3 := isOddCycle_card_ge_three hD'
      omega
    obtain ⟨x, hx⟩ := hne1
    have hmem2 : x ∈ D := by
      have key : x ∈ ((I.biUnion (fun C : Finset V => (C : Finset V))) : Finset V) := by
        refine Finset.mem_biUnion.mpr ⟨fam C, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨C, hCP, rfl⟩
        · exact (Finset.mem_inter.mp hx).1
      rw [hD]
      exact key
    exact Finset.nonempty_iff_ne_empty.mp
      ⟨x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).2, hmem2⟩⟩

/-! ## 6. The conclusion of Erdős #73 on this class, and the new instance -/

/-- **THE EXACT VALUE OF THE CONCLUSION OF ERDŐS #73 ON A CLUSTER GRAPH.**  `G` is the union of a
bipartite graph and `m` vertices **iff** its maximum deficiency is at most `m` — i.e. on this class
the *hypothesis* of JSP-000090 and its *conclusion* are the same statement. -/
theorem closeToBipartite_iff_maxDef_cluster {𝒬 : Finset (Finset V)}
    (hd : ClusterDecomposition G 𝒬) {m : ℕ} : CloseToBipartite m G ↔ MaxDef G ≤ m := by
  constructor
  · intro h
    exact maxDef_le_closeToBipartite h
  · intro h
    obtain ⟨D, hDcard, hhits⟩ := exists_oddCycle_transversal hd
    exact (closeToBipartite_iff_hitsOddCycles (m := m)).mpr ⟨D, hDcard.symm ▸ h, hhits⟩

/-- The same, with the sum of the piece costs in place of `MaxDef`. -/
theorem closeToBipartite_iff_cluster_cost {𝒬 : Finset (Finset V)}
    (hd : ClusterDecomposition G 𝒬) {m : ℕ} :
    CloseToBipartite m G ↔ (∑ C ∈ 𝒬, (C.card - 2)) ≤ m := by
  rw [← maxDef_cluster hd]
  exact closeToBipartite_iff_maxDef_cluster hd

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, WITH THE OPTIMAL CONSTANT `f(k) = k`.**  If `G` is a
disjoint union of complete graphs (`𝒬` a cluster decomposition) and Erdős's hypothesis holds with
parameter `k`, then `G` is the union of a bipartite graph and **at most `k` vertices**.  No bound
is used on the odd girth, on the packing weight, on the degrees, or on the number of pieces; and
the hypothesis is *strictly weaker* than the disjoint-odd-cycle hypothesis of round 98, since
`K_5 ⊔ K_5` satisfies this one and fails that one. -/
theorem erdos73On_of_cluster {k : ℕ} {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬)
    (hG : LocIndep k G) : CloseToBipartite k G :=
  (closeToBipartite_iff_maxDef_cluster hd).mpr (locIndep_iff_maxDef_le.mp hG)

/-- The same instance in the house style, quantified over all finite vertex types. -/
theorem erdos73On_of_cluster_univ (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (𝒬 : Finset (Finset W)),
      ClusterDecomposition G 𝒬 → LocIndep k G → CloseToBipartite k G := by
  intro W instW G 𝒬 hd hG
  exact erdos73On_of_cluster hd hG

/-- **`G` is bipartite iff every piece has at most two vertices.**  The two-element pieces are
exactly the free ones, and a graph all of whose pieces have at most two vertices is a disjoint
union of edges and vertices. -/
theorem cluster_isBipartite_iff {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) :
    G.IsBipartite ↔ ∀ C ∈ 𝒬, C.card ≤ 2 := by
  constructor
  · intro hb
    have hz : (∑ C ∈ 𝒬, (C.card - 2)) = 0 := by
      rw [← maxDef_cluster hd, maxDef_eq_zero_iff.mpr hb]
    have hz' : ∀ C ∈ 𝒬, C.card - 2 = 0 := (Finset.sum_eq_zero_iff.mp hz)
    intro C hC
    have := hz' C hC
    omega
  · intro h
    have hz : (∑ C ∈ 𝒬, (C.card - 2)) = 0 := Finset.sum_eq_zero_iff.mpr fun C hC => by
      have hle := h C hC
      omega
    have : MaxDef G = 0 := by rw [maxDef_cluster hd, hz]
    exact maxDef_eq_zero_iff.mp this

/-- The proved case `k = 0` of Erdős #73 on this class, with the sharp constant `0`. -/
theorem erdos73On_cluster_zero {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬)
    (hG : LocIndep 0 G) : CloseToBipartite 0 G :=
  (closeToBipartite_iff_maxDef_cluster hd).mpr (locIndep_iff_maxDef_le.mp hG)

/-- **The formula of this file contains round 54's `MaxDef (K_n) = n - 2`**: for a decomposition
with a single piece, the sum has one term. -/
theorem maxDef_cluster_univ {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬)
    (h1 : 𝒬.card = 1) : MaxDef G = (Finset.univ : Finset V).card - 2 := by
  obtain ⟨C, heq⟩ := Finset.card_eq_one.mp h1
  subst heq
  have huniv : (Finset.univ : Finset V) = C := by
    refine Finset.Subset.antisymm (fun v hv => ?_) (fun v hv => ?_)
    · obtain ⟨Y, hY, hYv⟩ := cover hd (x := v)
      rw [Finset.mem_singleton] at hY
      exact hY ▸ hYv
    · exact Finset.mem_univ v
  rw [maxDef_cluster hd, Finset.sum_singleton]
  have hcard : C.card = (Finset.univ : Finset V).card := by rw [← huniv, Finset.card_univ]
  omega

end

end JSP90