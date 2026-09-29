/-
# JSP-000090, round 48 — **the connectivity and 1-cut reductions of Erdős Problem #73**

## What this file is

Round 47 proved that the conclusion of Erdős #73 is *additive* over an anticomplete decomposition of
the vertex set (`JSPProblem/Additive.lean`, `erdos73On_of_anticover_decomposition`) and named, as
the exact next step, the instance of that lemma for the family of **connected components**.  This
file is the ninth attack family: it carries out that step and then continues along the same
decomposition axis to the **1-cut** (a cut at a *single* vertex), which is the next step of the
classical Erdős–Pósa proof.  Together with round 43's 2-cut reduction the whole classical chain
*connected → 2-connected → 3-connected* is now formal.

The decomposition object of Part 1 is built from Mathlib's connectivity API
(`SimpleGraph.Reachable`, `reachable_eq_reflTransGen`), the first use of that API in this
development; earlier rounds formalised connectivity by hand, or not at all.

## Part 1–4: the connected components, and the connectivity reduction

* `compPiece G v = univ.filter (G.Reachable v)` and `compPieces G = univ.image compPiece` — the
  connected components of `G` as a family of vertex sets, and
  **`anticoverDecomposition_compPieces`: the components of `G` form an `AnticoverDecomposition`**
  (pairwise disjoint, pairwise anticomplete, covering `V`, and anticomplete to the complement of
  their union — the last clause is what a mere *cover* would not give, cf. round 47's negative
  result).  `compPiece_eq_of_reachable`, `inter_compPiece_eq_empty` and `compPiece_eq_of_adj` are
  the three finiteness facts behind it; `compPiece_piecePreconnected` is the irreducibility of a
  component.
* `card_le_of_pieces_pack` — the **counting lemma in the Erdős–Pósa form**, for a family of pieces
  indexed by an arbitrary type: if every packing of odd cycles of `G` has at most `r` members then
  a family of disjoint, anticomplete pieces each carrying an odd cycle has at most `r` members.
* `oddCycleErdosPosa_of_anticover_decomposition` — round 47's instance with the `LocIndep k G`
  hypothesis replaced by the packing bound `r`, i.e. the instance in the form in which the research
  statement `OddCycleErdosPosa r` is phrased.
* `erdos73On_of_connected_components` — **a new instance of the headline theorem**: if every
  connected component of `G` is `m`-close to bipartite, `LocIndep k G` forces
  `CloseToBipartite (k * m) G`, a constant independent of the number of components and with no
  bound on the odd girth, the packing weight or the number of branch vertices.
* `PieceErdős73On` / `erdos73On_of_piece` / `erdos73_of_erdos73_piece` — **the reduction**: if a
  constant `m` works for *connected pieces*, the constant `k * m` works for all graphs.
  `PieceErdős73On` is the form the classical proof needs, because the pieces of a decomposition
  (components, then blocks) are vertex sets of the *same* graph rather than graphs on their own
  vertex types; `PiecePreconnected G s` says that any two vertices of `s` are joined by a path of
  `G`.  For `s = V` this is `G.Preconnected` (`PiecePreconnected.univ`), so this is the classical
  "Erdős #73 reduces to connected graphs, at the price of a factor `k`".
* `PieceOddCycleErdosPosa` / `oddCycleErdosPosa_of_piece` / `erdos73_of_connected_erdosPosa` — the
  same reduction for the **research statement**: `OddCycleErdosPosa r` follows from its
  connected-piece case, with the explicit bound `r * m`.  So the blocker is now localised to a
  strictly weaker and precisely stated statement.

## Part 5–6: the 1-cut, its parity lemma, and the second reduction

* `OneSplit G v t` — a **1-cut split**: `V = {v} ⊔ T₁ ⊔ … ⊔ T_t` with the parts pairwise disjoint
  and pairwise anticomplete, i.e. `v` is a cut vertex.  This is the counterpart of
  `JSPProblem.Separator.VertexSplit` (a 2-cut), and it differs in exactly the way that matters for
  the constant: the two sides of a 2-cut share the *two* cut vertices and cost `+ 2`, whereas a
  1-cut shares a *single* vertex with every piece and costs `+ 1`.
* `OneSplit.cycle_subset_part` / `oddCycle_part_or_hit` — **a cycle of `G` avoiding the cut vertex
  lies in a single part** (the 1-cut counterpart of `VertexSplit.cycle_subset_parts`), so every odd
  cycle of `G` either meets `v` or lies in a part.
* `OneSplit.isBipartite_of_bipartite_pieces` — **THE 1-CUT PARITY LEMMA**: if every *piece*
  `T_i ∪ {v}` is bipartite then `G` is bipartite.  The colouring is glued from the pieces with
  `flipCol` at the single cut vertex.  The **pieces** and not the bare parts are the right objects,
  and this is recorded as a mathematical remark in the docstring of
  `OneSplit.one_nonBipartitePiece`: a triangle with a pendant vertex, cut at the triangle vertex
  carrying the pendant, has two *bipartite* parts and is not bipartite, so "all parts bipartite ⟹
  `G` bipartite" is false.
* `OneSplit.one_nonBipartitePiece` — the contrapositive: a non-bipartite `G` with a 1-cut has a
  non-bipartite piece.  The tempting strengthening "**at least two**" is **false** for the same
  triangle-with-pendant, which is why the depth bound below cannot be obtained from a single 1-cut.
* `OneSplit.card_nonBipartiteParts_le` — the counting lemma: under a packing bound `r`, at most `r`
  parts of a 1-cut are non-bipartite.
* `OneSplit.exists_transversal_nonBipartite` — an odd cycle transversal of size at most
  `1 + ∑_{i non-bipartite} m`, and hence
* **`erdos73On_of_1split_of_bounded_pieces` — A NEW INSTANCE OF THE HEADLINE THEOREM, along the
  1-cut axis**: if `LocIndep k` forces `CloseToBipartite m` in every part `T_i` of a 1-cut, then
  it forces `CloseToBipartite (1 + m * k) G`.  The constant `1 + m * k` is independent of the
  number `t` of parts and **improves on the 2-cut instance** `2 + m * k` of `JSPProblem/Count.lean`.
  `oddCycleErdosPosa_of_1split_of_bounded_pieces_about_pieces` is the form in which the hypothesis
  concerns the pieces, as the depth recursion needs.
* `erdos73On_of_1split_pieces` — **the classical chain, connected → 2-connected**: if the headline
  theorem holds with the constant `m` for connected pieces and `G` admits a 1-cut whose parts are
  joined to the cut vertex, then `LocIndep k G` forces `CloseToBipartite (1 + m * k) G`.
* `HasProper1Split`, `NoProper1Split`, `OneDepth` (with `oneDepth_succ`, `oneDepth_add`,
  `oneDepth_mono`), `oneBound` and
  **`oddCycleErdosPosa_of_noOneCut_of_bounded_oneDepth` — THE PRECISE REDUCTION ALONG THE 1-CUT
  AXIS**: Erdős–Pósa for odd cycles follows from (i) the 1-cut-free case and (ii) a uniform bound
  on the number of successive 1-cuts.  The 1-cut analogue of round 43's
  `erdos73_of_noSplit2_of_bounded_splitDepth`, and its analogue at the *piece* level: at each
  level one pays `1 + p * (bound below)`.

## Relation to the blocker

`jsp_000090_main` still needs `JSP90.OddCycleErdosPosa r` for arbitrary `r` (Erdős–Pósa for odd
cycles, Reed–Robertson–Seymour–Thomas 2002); `erdos73_of_erdosPosa` is proved, so that single
statement is all that is missing.  This file does not prove it, but it localises it twice:

1. it is enough to prove `PieceOddCycleErdosPosa r` (its `s = V` case being the connected case);
2. it is enough to prove it for graphs with no proper 1-cut, **provided** every graph of packing
   number `r` has 1-cut depth at most `d` — the block-cut tree theorem, which is the exact missing
   lemma (`oneDepth_le_of_packing`, not proved here; see `discovery/JSP-000090/policy.json`).
-/
import JSPProblem.Additive
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace JSP90

universe u

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqConnect : DecidableEq V := Classical.decEq V

local instance instDecidablePredReachable (G : SimpleGraph V) (v : V) :
    DecidablePred (G.Reachable v) := fun _ => Classical.propDecidable _

/-! ### Part 1 — the connected components as an anticomplete decomposition -/

section Components

/-- **An edge makes its two ends reachable from each other.** -/
theorem reachable_of_adj {G : SimpleGraph V} {v w : V} (h : G.Adj v w) : G.Reachable v w := by
  rw [SimpleGraph.reachable_eq_reflTransGen]
  exact Relation.ReflTransGen.single h

/-- **The connected component of the vertex `v`**, as a finset of vertices: the vertices reachable
from `v`.  Reachability is an equivalence, so this does not depend on the choice of `v` inside the
component (`compPiece_eq_of_reachable`), and the component is a vertex *cut* of `G`
(`anticoverDecomposition_compPieces`). -/
def compPiece (G : SimpleGraph V) (v : V) : Finset V :=
  (Finset.univ : Finset V).filter (G.Reachable v)

/-- **The family of the connected components of `G`**, as a family of vertex sets. -/
def compPieces (G : SimpleGraph V) : Finset (Finset V) := (Finset.univ : Finset V).image (compPiece G)

@[simp] theorem mem_compPiece (G : SimpleGraph V) (v x : V) :
    x ∈ compPiece G v ↔ G.Reachable v x := by
  simp only [compPiece, Finset.mem_filter, Finset.mem_univ, true_and]

theorem compPiece_self (G : SimpleGraph V) (v : V) : v ∈ compPiece G v :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ v, SimpleGraph.Reachable.refl v⟩

theorem compPiece_mem_compPieces (G : SimpleGraph V) (v : V) : compPiece G v ∈ compPieces G :=
  Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩

/-- **Every vertex lies in a component**: the components cover `V`. -/
theorem mem_compPiece_of_mem_univ (G : SimpleGraph V) (x : V) : x ∈ compPiece G x :=
  compPiece_self G x

/-- **Reachable vertices have the same component.** -/
theorem compPiece_eq_of_reachable (G : SimpleGraph V) {v w : V} (h : G.Reachable v w) :
    compPiece G v = compPiece G w := by
  ext x
  constructor
  · intro hx
    rw [mem_compPiece] at hx ⊢
    exact h.symm.trans hx
  · intro hx
    rw [mem_compPiece] at hx ⊢
    exact h.trans hx

/-- **The component of `v` is a module of `G`**: an edge out of it stays in it. -/
theorem mem_compPiece_of_adj_mem_compPiece (G : SimpleGraph V) {v w : V} (hv : v ∈ compPiece G v)
    (hadj : G.Adj v w) : w ∈ compPiece G v :=
  Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (SimpleGraph.Reachable.refl v).trans (reachable_of_adj hadj)⟩

/-- **Two distinct components are disjoint.** -/
theorem inter_compPiece_eq_empty (G : SimpleGraph V) {v w : V} (hne : compPiece G v ≠ compPiece G w) :
    compPiece G v ∩ compPiece G w = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hvw : G.Reachable v w :=
    ((mem_compPiece G v x).mp ((mem_inter.mp hx).1)).trans
      ((mem_compPiece G w x).mp ((mem_inter.mp hx).2)).symm
  exact hne (compPiece_eq_of_reachable G hvw)

/-- **An edge forces the two components to agree**: no edge of `G` joins two distinct components. -/
theorem compPiece_eq_of_adj (G : SimpleGraph V) {v w : V} (hadj : G.Adj v w) :
    compPiece G v = compPiece G w :=
  compPiece_eq_of_reachable G (reachable_of_adj hadj)

/-- **The connected components of `G` form a cover by pairwise anticomplete pieces.** -/
theorem anticoverCoverFamily_compPieces (G : SimpleGraph V) : AnticoverCoverFamily G (compPieces G) := by
  refine ⟨?_, ?_⟩
  · rintro X hX Y hY hne
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hY
    exact inter_compPiece_eq_empty G hne
  · rintro X hX Y hY hne x hx y hy hAdj
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hY
    have hvx : G.Reachable v x := (mem_compPiece G v x).mp hx
    have hxy : G.Reachable x y := reachable_of_adj hAdj
    have hwy : G.Reachable w y := (mem_compPiece G w y).mp hy
    exact hne ((compPiece_eq_of_reachable G hvx).trans ((compPiece_eq_of_reachable G hxy).trans
      (compPiece_eq_of_reachable G hwy).symm))

/-- **THE DECOMPOSITION: the connected components of `G` form an `AnticoverDecomposition`** — a
partition of `V` into pairwise anticomplete pieces, with no edge leaving a piece (which, since the
pieces cover `V`, says that no edge leaves their union).  This is the hypothesis of round 47's
instance `JSPProblem/Additive.lean` `erdos73On_of_anticover_decomposition`, and it is what the
family of components has and a mere cover by anticomplete pieces does not. -/
theorem anticoverDecomposition_compPieces (G : SimpleGraph V) :
    AnticoverDecomposition G (compPieces G) :=
  ⟨anticoverCoverFamily_compPieces G, fun X hX x hx y hy hadj => by
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hX
    have hvx : G.Reachable v x := (mem_compPiece G v x).mp hx
    have hyv : y ∉ compPiece G v := by
      intro hyv
      exact hy (Finset.mem_biUnion.mpr ⟨compPiece G v, compPiece_mem_compPieces G v, hyv⟩)
    exact absurd ((mem_compPiece G v y).mpr (hvx.trans (reachable_of_adj hadj))) hyv⟩

/-- **`PiecePreconnected G s`**: any two vertices of `s` are joined by a path of `G`.  For
`s = compPiece G v` this is exactly the connectivity of the connected component of `v` (and it is
implied by the connectivity of the induced subgraph `G[s]`), which is the *irreducibility* needed
to apply the instance of round 47. -/
def PiecePreconnected (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃u w : V⦄, u ∈ s → w ∈ s → G.Reachable u w

theorem PiecePreconnected.univ (G : SimpleGraph V) :
    PiecePreconnected G (Finset.univ : Finset V) ↔ G.Preconnected := by
  constructor
  · intro h u w
    exact h (Finset.mem_univ u) (Finset.mem_univ w)
  · intro h u w hu hw
    exact h u w

/-- **The graph induced on the whole vertex set is `G`.** -/
theorem induceFinset_univ (G : SimpleGraph V) : induceFinset G (Finset.univ : Finset V) = G := by
  ext u w
  simp [induce_adj]

/-- **Induced subgraphs compose**: `G[s][t] = G[s ∩ t]`. -/
theorem induceFinset_induceFinset {G : SimpleGraph V} (s t : Finset V) :
    induceFinset (induceFinset G s) t = induceFinset G (s ∩ t) := by
  ext u w
  constructor
  · intro h
    have h1 : u ∈ t := h.1
    have h2 : w ∈ t := h.2.1
    have h' := (induce_adj).mp h.2.2
    have h3 : u ∈ s := h'.1
    have h4 : w ∈ s := h'.2.1
    exact (induce_adj).mpr
      ⟨Finset.mem_inter.mpr ⟨h3, h1⟩, Finset.mem_inter.mpr ⟨h4, h2⟩, h'.2.2⟩
  · intro h
    have h' := (induce_adj).mp h
    have h1 : u ∈ t := Finset.mem_inter.mp h'.1 |>.2
    have h2 : w ∈ t := Finset.mem_inter.mp h'.2.1 |>.2
    have h3 : u ∈ s := Finset.mem_inter.mp h'.1 |>.1
    have h4 : w ∈ s := Finset.mem_inter.mp h'.2.1 |>.1
    exact (induce_adj).mpr ⟨h1, h2, h3, h4, h'.2.2⟩

/-- **A connected component is a connected piece**: any two of its vertices are reachable. -/
theorem compPiece_piecePreconnected (G : SimpleGraph V) (v : V) :
    PiecePreconnected G (compPiece G v) := by
  intro u w hu hw
  exact ((mem_compPiece G v u).mp hu).symm.trans ((mem_compPiece G v w).mp hw)

/-- **Two adjacent vertices have the same component.** -/
theorem eq_compPiece_of_adj (G : SimpleGraph V) {v w : V} (h : G.Adj v w) :
    compPiece G v = compPiece G w := compPiece_eq_of_adj G h

/-- **The induced graph on a component carries exactly the edges of `G` inside it.** -/
theorem induce_adj_compPiece (G : SimpleGraph V) {v x y : V} (hx : x ∈ compPiece G v)
    (hy : y ∈ compPiece G v) :
    (induceFinset G (compPiece G v)).Adj x y ↔ G.Adj x y :=
  Iff.intro (fun h => (JSP90.induce_adj.mp h).2.2)
    (fun h => (JSP90.induce_adj).mpr ⟨hx, hy, h⟩)

end Components

/-! ### Part 2 — the counting lemma in the Erdős–Pósa form -/

section Packing

/-- **The counting lemma, in the Erdős–Pósa form, for a family of pieces indexed by an arbitrary
type.**  Let `Q` be a family of pairwise disjoint, pairwise anticomplete pieces `p X` of `G`, each
carrying an odd cycle of `G`.  If every packing of odd cycles of `G` has at most `r` members then
`Q` has at most `r` members.

This is `JSPProblem/Additive.lean` `card_le_of_pieces` with the `LocIndep k G` hypothesis replaced
by the packing bound `r` (it is what the research statement `OddCycleErdosPosa r` is phrased in),
and with the index type of the family generalised — the parts of a 1-cut of `JSPProblem/Connect.lean`
are indexed by `Fin t`, not by `Finset V`. -/
theorem card_le_of_pieces_pack {ι : Type*} [Fintype ι] {r : ℕ} {Q : Finset ι} {p : ι → Finset V}
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r)
    (hdis : ∀ (X : ι), X ∈ Q → ∀ (Y : ι), Y ∈ Q → X ≠ Y → p X ∩ p Y = ∅)
    (hanti : ∀ (X : ι), X ∈ Q → ∀ (Y : ι), Y ∈ Q → X ≠ Y → ∀ (x : V), x ∈ p X → x ∉ p Y)
    (hodd : ∀ (X : ι), X ∈ Q → ∃ C, IsOddCycle (induceFinset G (p X)) C) : Q.card ≤ r := by
  classical
  have hmem : ∀ a : ↥Q, (a : ι) ∈ Q := fun a => a.property
  have hdis' : ∀ a b : ↥Q, (a : ι) ≠ (b : ι) → p (a : ι) ∩ p (b : ι) = ∅ :=
    fun a b hne => hdis (a : ι) (hmem a) (b : ι) (hmem b) hne
  have hsub' : ∀ a : ↥Q, (hodd (a : ι) (hmem a)).choose ⊆ p (a : ι) :=
    fun a => isOddCycle_sub_induceFinset (hodd (a : ι) (hmem a)).choose_spec
  have hInj : ∀ a b : ↥Q, (a : ι) ≠ (b : ι) →
      (hodd (a : ι) (hmem a)).choose ≠ (hodd (b : ι) (hmem b)).choose := by
    intro a b hne hab
    have hpos : 0 < (hodd (a : ι) (hmem a)).choose.card := by
      have h3 := isOddCycle_card_ge_three (hodd (a : ι) (hmem a)).choose_spec
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    have hxA : x ∈ p (a : ι) := hsub' a hx
    have hxB : x ∈ p (b : ι) := hsub' b (hab ▸ hx)
    exact absurd (Finset.mem_inter.mpr ⟨hxA, hxB⟩) (by rw [hdis' a b hne]; simp)
  have hInj' : Set.InjOn (fun a : ↥Q => (hodd (a : ι) (hmem a)).choose) (↑(Q.attach) : Set ↥Q) := by
    intro a _ b _ hab
    by_cases hne : (a : ι) = (b : ι)
    · apply Subtype.ext
      exact hne
    · exact absurd hab (hInj a b hne)
  set 𝒬'' : Finset (Finset V) :=
    (Q.attach).image fun a : ↥Q => (hodd (a : ι) (hmem a)).choose with h𝒬''def
  have hfam : IsOddCycleFamily (G := G) 𝒬'' := by
    refine ⟨?_, ?_⟩
    · intro C hC D hD hne
      obtain ⟨a, ha, hval⟩ := Finset.mem_image.mp hC
      obtain ⟨b, hb, hval'⟩ := Finset.mem_image.mp hD
      have hne' : (a : ι) ≠ (b : ι) := by
        intro h
        have hab : a = b := Subtype.ext h
        subst hab
        exact hne (hval.symm.trans hval')
      have hmemc := hsub' a
      have hmemD := hsub' b
      rw [hval] at hmemc
      rw [hval'] at hmemD
      refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have hx' : x ∈ C ∧ x ∈ D := Finset.mem_inter.mp hx
      exact absurd (Finset.mem_inter.mpr ⟨hmemc hx'.1, hmemD hx'.2⟩)
        (by rw [hdis' a b hne']; simp)
    · intro C hC
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
      exact (hodd (a : ι) (hmem a)).choose_spec.of_induceFinset
  have hle := hpack 𝒬'' hfam
  rw [h𝒬''def, Finset.card_image_of_injOn hInj', Finset.card_attach] at hle
  exact hle

/-- **THE COUNTING LEMMA FOR A COVER, in the Erdős–Pósa form**: if every packing of odd cycles of
`G` has at most `r` members, then at most `r` pieces of an anticomplete cover of the vertices
induce a non-bipartite graph.  (The `LocIndep` version is
`JSPProblem/Additive.lean` `card_nonBipartiteParts_le_cover`.) -/
theorem card_nonBipartiteParts_le_cover_pack {r : ℕ}
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r)
    {𝒬 : Finset (Finset V)} (h : AnticoverCoverFamily G 𝒬)
    [DecidablePred fun X => ¬ (induceFinset G X).IsBipartite] :
    (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).card ≤ r := by
  classical
  refine card_le_of_pieces_pack (ι := Finset V) (p := fun X => X) hpack ?_ ?_ ?_
  · intro X hX Y hY hne
    exact h.1 X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hne
  · intro X hX Y hY hne x hx hy
    exact absurd (Finset.mem_inter.mpr ⟨hx, hy⟩) (by
      rw [h.1 X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hne]; simp)
  · intro X hX
    by_contra hcon
    exact (Finset.mem_filter.mp hX).2 (isBipartite_of_no_oddCycle hcon)

end Packing

/-! ### Part 3 — the instance in the Erdős–Pósa form, and the connectivity reduction -/

section Instance

/-- **THE INSTANCE IN THE ERDŐS–PÓSA FORM.**  If the vertices of `G` are partitioned into pairwise
anticomplete pieces and every *non-bipartite* piece is `m`-close to bipartite, then a graph whose
odd cycle packings have at most `r` members is `CloseToBipartite (r * m)`.

This is round 47's `erdos73On_of_anticover_decomposition` with the `LocIndep k G` hypothesis
replaced by the packing bound `r` (which is how the research statement `OddCycleErdosPosa r` is
phrased), so that the *connected* case of the research statement becomes available.  The constant
`r * m` is independent of the number of pieces. -/
theorem oddCycleErdosPosa_of_anticover_decomposition {r m : ℕ} (𝒬 : Finset (Finset V))
    (h : AnticoverDecomposition G 𝒬) (hcov : ∀ (x : V), ∃ X ∈ 𝒬, x ∈ X)
    (hm : ∀ X ∈ 𝒬, ¬ (induceFinset G X).IsBipartite → CloseToBipartite m (induceFinset G X))
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r)
    [DecidablePred fun X => ¬ (induceFinset G X).IsBipartite] :
    CloseToBipartite (r * m) G := by
  classical
  have hcover := h.1
  have hcard : (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).card ≤ r :=
    card_nonBipartiteParts_le_cover_pack hpack hcover
  have hdis' : ∀ X ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite), ∀ Y ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite), X ≠ Y → X ∩ Y = ∅ := by
    intro X hX Y hY hne
    exact hcover.1 X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hne
  have hedge' : ∀ X ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite), ∀ Y ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite), X ≠ Y →
      ∀ (x : V), x ∈ X → ∀ (y : V), y ∈ Y → ¬ G.Adj x y := by
    intro X hX Y hY hne x hx y hy
    exact hcover.2 X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hne x hx y hy
  have hfam : AnticoverFamily G (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite) :=
    ⟨hdis', hedge',
      fun X hX => by
        have hnb : ¬ (induceFinset G X).IsBipartite := (Finset.mem_filter.mp hX).2
        have hex2 : ∃ C, IsOddCycle (induceFinset G X) C := by
          by_contra hcon2
          exact hnb (isBipartite_of_no_oddCycle hcon2)
        obtain ⟨C, hC⟩ := hex2
        exact ⟨C, hC.of_induceFinset, isOddCycle_sub_induceFinset hC⟩⟩
  have hm' : ∀ (X : Finset V), X ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite) → CloseToBipartite m (induceFinset G X) :=
    fun X hX => hm X (Finset.mem_filter.mp hX).1 (Finset.mem_filter.mp hX).2
  have h1 := closeToBipartite_of_anticoverFamily_cost hfam hm'
  have h1' : CloseToBipartite (m * (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).card)
      (induceFinset G ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) := by
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm] at h1
    exact h1
  clear h1
  have hrest : (induceFinset G ((Finset.univ : Finset V) \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id))).IsBipartite := by
    refine isBipartite_of_no_oddCycle ?_
    rintro ⟨C, hC⟩
    have hC' : IsOddCycle G C := hC.of_induceFinset
    have hsubX : ∃ X ∈ 𝒬, C ⊆ X := isOddCycle_sub_anticoverCover
      ((Finset.univ : Finset V) \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id))
      hcover (fun x hx => hcov x) hC'
        (isOddCycle_sub_induceFinset
          (s := (Finset.univ : Finset V) \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) hC)
    obtain ⟨X, hX, hCX⟩ := hsubX
    have hCX' : IsOddCycle (induceFinset G X) C := hC'.induceFinset (s := X) hCX
    have hCsub : C ⊆ (Finset.univ : Finset V) \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id) :=
      isOddCycle_sub_induceFinset
        (s := (Finset.univ : Finset V) \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) hC
    by_cases hXbip : (induceFinset G X).IsBipartite
    · exact absurd ⟨C, hCX'⟩ (JSP90.not_isOddCycle_of_isBipartite hXbip)
    · have hXU : X ⊆ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id) :=
        fun x hx => Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, hXbip⟩, hx⟩
      have h3 := isOddCycle_card_ge_three hCX'
      have hpos : 0 < C.card := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      exact absurd (hXU (hCX hx)) (Finset.mem_sdiff.mp (hCsub hx)).2
  have hAB : Anticover G ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id) (Finset.univ \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hxA hxB
      exact absurd hxA (Finset.mem_sdiff.mp hxB).2
    · ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    · intro v hvA w hwB hv
      have hvX : ∃ X ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite), v ∈ X :=
        Finset.mem_biUnion.mp hvA
      obtain ⟨X, hX', hvX'⟩ := hvX
      by_cases hwU : w ∈ 𝒬.biUnion id
      · have hwW : ∃ Y ∈ 𝒬, w ∈ Y := Finset.mem_biUnion.mp hwU
        obtain ⟨Y, hY, hwY⟩ := hwW
        have hXU : X ⊆ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id :=
          fun x hx => Finset.mem_biUnion.mpr ⟨X, hX', hx⟩
        have hne : X ≠ Y := by
          intro hXY
          subst hXY
          exact absurd (hXU hwY) (Finset.mem_sdiff.mp hwB).2
        exact absurd hv
          (hcover.2 X (Finset.mem_filter.mp hX').1 Y hY hne v hvX' w hwY)
      · exact absurd hv (h.2 X (Finset.mem_filter.mp hX').1 v hvX' w hwU)
  have h2 := closeToBipartite_of_anticover hAB h1' (closeToBipartite_zero_of_isBipartite hrest)
  have h2' : CloseToBipartite (m * (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).card) G := by
    convert h2 using 1 <;> omega
  exact closeToBipartite_mono (m' := r * m)
    (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right m hcard) h2'

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, along the connectivity axis.**  If every connected
component of `G` is `m`-close to bipartite, then `LocIndep k G` forces `CloseToBipartite (k * m) G`.

The constant `k * m` is **independent of the number of components** (at most `k` of them are
non-bipartite, by `card_nonBipartiteParts_le_cover_pack`), and no bound is assumed on the odd
girth, on the packing weight or on the number of branch vertices.  This is the instance round 47
named as the next step. -/
theorem erdos73On_of_connected_components {k m : ℕ} (hG : LocIndep k G)
    (hm : ∀ (v : V), ¬ (induceFinset G (compPiece G v)).IsBipartite →
      CloseToBipartite m (induceFinset G (compPiece G v)))
    [DecidablePred fun v : V => ¬ (induceFinset G (compPiece G v)).IsBipartite] :
    CloseToBipartite (k * m) G := by
  classical
  letI : DecidablePred fun X => ¬ (induceFinset G X).IsBipartite :=
    fun _ => Classical.propDecidable _

  exact erdos73On_of_anticover_decomposition hG (compPieces G)
    (anticoverDecomposition_compPieces G)
    (fun x => ⟨compPiece G x, compPiece_mem_compPieces G x, compPiece_self G x⟩)
    (fun X hX hnb => by
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hX
      exact hm v hnb)

end Instance

/-! ### Part 4 — Erdős Problem #73 reduces to connected graphs -/

section Reduction

/-- **ERDŐS #73 FOR *CONNECTED PIECES*.**  `PiecePreconnected G s` says that any two vertices of the
vertex set `s` are joined by a path of `G`; for `s` the vertex set of a connected component (or,
later, of a block) this is exactly the connectivity of that piece, and it is the form in which the
classical proof of Erdős–Pósa needs the hypothesis: the pieces of the decomposition are *vertex
sets of `G`*, not graphs on vertex types of their own.  `PieceErdős73On k m` is therefore the
classical "Erdős #73 for connected graphs" with the pieces spelled out. -/
def PieceErdős73On (k m : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
    ∀ (s : Finset W), PiecePreconnected G s → ¬ (induceFinset G s).IsBipartite →
      CloseToBipartite m (induceFinset G s)

/-- **ERDŐS #73 RESTRICTED TO CONNECTED GRAPHS**, in the form of this development: the
`PieceErdős73On` instance on the whole vertex set.  `PiecePreconnected G univ` *is* `G.Preconnected`
(`PiecePreconnected.univ`). -/
def PreconnectedErdős73On (k m : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.Preconnected →
    CloseToBipartite m G

theorem pieceErdős73On_of_preconnected (h : PieceErdős73On.{u} k m) :
    PreconnectedErdős73On.{u} k m := by
  intro W instW G hG hconn
  by_cases hb : G.IsBipartite
  · exact ⟨∅, Nat.zero_le _, isBipartite_delete hb⟩
  · have h1 := h W instW G hG (Finset.univ : Finset W) ((PiecePreconnected.univ G).mpr hconn)
      (by simpa only [induceFinset_univ] using hb)
    simpa only [induceFinset_univ] using h1

/-- **THE CONNECTIVITY REDUCTION OF ERDŐS #73.**  If a constant `m` works for *connected pieces*
—in particular for connected graphs — then the constant `k * m` works for all graphs: every graph
is the anticomplete union of its connected components, and at most `k` of them can be
non-bipartite.  So the constant `k * m` is all that the disconnected case costs. -/
theorem erdos73On_of_piece {k m : ℕ} (h : PieceErdős73On.{u} k m) : Erdős73On.{u} k (k * m) := by
  intro W instW H hG
  classical
  letI : DecidablePred fun v : W => ¬ (induceFinset H (compPiece H v)).IsBipartite :=
    fun _ => Classical.propDecidable _
  exact erdos73On_of_connected_components hG (fun v hnb =>
    h W instW H hG (compPiece H v) (compPiece_piecePreconnected H v) hnb)

/-- **ERDŐS #73 FOR CONNECTED PIECES.** -/
def Erdős73Piece (k : ℕ) : Prop := ∃ m : ℕ, PieceErdős73On.{u} k m

/-- **Hence the full Erdős #73**: it is enough to prove the headline theorem for connected
pieces.  This is the first step of the classical proof of Erdős–Pósa for odd cycles, and it is now
a proved reduction with the explicit constant `k * m`. -/
theorem erdos73_of_erdos73_piece {k : ℕ} (h : Erdős73Piece.{u} k) : Erdős73.{u} k :=
  ⟨k * h.choose, erdos73On_of_piece h.choose_spec⟩

/-- The converse: the statement for connected pieces follows from the full statement (applied to
a graph on the piece, whose odd cycles are those of the piece). -/
theorem erdos73Piece_of_erdos73 {k : ℕ} (h : Erdős73.{u} k) : Erdős73Piece.{u} k := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun W instW G hG s hs hnb => ?_⟩
  have h1 := hm W instW (induceFinset G s) (hG.of_induceFinset s)
  have huniv : s ∩ (Finset.univ : Finset W) = s := by
    ext x
    simp
  simpa only [induceFinset_induceFinset, huniv, induceFinset_univ] using h1

/-- **THE RESEARCH STATEMENT RESTRICTED TO CONNECTED PIECES** (Erdős–Pósa for odd cycles in
connected graphs, with the pieces spelled out). -/
def PieceOddCycleErdosPosa (r : ℕ) : Prop :=
  ∃ m : ℕ, ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (s : Finset W),
    PiecePreconnected G s → ¬ (induceFinset G s).IsBipartite →
    (∀ C : Finset (Finset W), IsOddCycleFamily (G := induceFinset G s) C → C.card ≤ r) →
    CloseToBipartite m (induceFinset G s)

/-- **THE CONNECTIVITY REDUCTION OF THE RESEARCH STATEMENT.**  Erdős–Pósa for odd cycles in
connected pieces implies Erdős–Pósa for odd cycles in all graphs, with the explicit bound `r * m`:
the components of `G` are an anticomplete decomposition, at most `r` of them are non-bipartite, and
each of them costs `m`.

This is a **new, strictly weaker, precisely stated missing lemma**: to close `jsp_000090_main` it is
now enough to prove `PieceOddCycleErdosPosa r` for every `r` (and, by the connectivity lemma, its
case `s = univ` is the connected case). -/
theorem oddCycleErdosPosa_of_piece {r : ℕ} (h : PieceOddCycleErdosPosa.{u} r) :
    OddCycleErdosPosa.{u} r := by
  obtain ⟨m, hm⟩ := h
  refine ⟨r * m, fun W instW H hpack => ?_⟩
  classical
  letI : DecidablePred fun X : Finset W => ¬ (induceFinset H X).IsBipartite :=
    fun _ => Classical.propDecidable _
  exact oddCycleErdosPosa_of_anticover_decomposition (compPieces H)
    (anticoverDecomposition_compPieces H)
    (fun x => ⟨compPiece H x, compPiece_mem_compPieces H x, compPiece_self H x⟩)
    (fun X hX hnb => by
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hX
      exact hm W instW H (compPiece H v) (compPiece_piecePreconnected H v) hnb
        (fun D hD => hpack D hD.of_induceFinset)) hpack

/-- **Erdős–Pósa for odd cycles follows from the connected case** — the reduction by which
`jsp_000090_main` is localised.  Since `erdos73_of_erdosPosa` is proved, the headline theorem
follows from `PieceOddCycleErdosPosa r` for every `r`. -/
theorem erdos73_of_connected_erdosPosa (h : ∀ r, PieceOddCycleErdosPosa.{u} r) :
    ∀ k, Erdős73.{u} k :=
  erdos73_of_erdosPosa fun r => oddCycleErdosPosa_of_piece (h r)

end Reduction

/-! ### Part 5 — a 1-cut: the pieces of a cut at ONE vertex -/

section OneCut

/-- **A 1-cut split of `G` at the vertex `v` into `t` parts**: every vertex of `G` is either `v`
itself or lies in one of the `t` nonempty parts, the parts are pairwise disjoint and pairwise
**anticomplete** (no edge joins them), and `t ≥ 1`.  Equivalently, `G - v` is a disjoint union of
`t` induced subgraphs with no edges between them, i.e. `v` is a vertex cut.

This is the decomposition of the classical proof at a *cut vertex*, the counterpart of
`JSPProblem.Separator.VertexSplit` (a 2-cut).  The two differ in one respect which matters for the
constant: the two sides of a 2-cut share the two cut vertices, so they cost `+ 2`
(`erdos73On_of_split_of_bounded_pieces`), whereas here the single vertex `v` is charged **once**,
whatever the number of parts. -/
structure OneSplit (G : SimpleGraph V) (v : V) (t : ℕ) where
  /-- the `t` parts of `V \ {v}` -/
  parts : Fin t → Finset V
  /-- the split is nontrivial: at least one part -/
  ht : 0 < t
  /-- no part is empty -/
  hne : ∀ i : Fin t, (parts i).Nonempty
  /-- the parts are pairwise disjoint -/
  hdisj : ∀ i j : Fin t, i ≠ j → parts i ∩ parts j = ∅
  /-- the parts, together with `v`, exhaust the vertices of `G` -/
  hcov : ∀ x : V, x = v ∨ (∃ i : Fin t, x ∈ parts i)
  /-- two distinct parts are anticomplete -/
  hanti : ∀ i j : Fin t, i ≠ j → ∀ x ∈ parts i, ∀ y ∈ parts j, ¬ G.Adj x y

variable {v : V} {t : ℕ} (sp : OneSplit G v t)

/-- A vertex other than the cut vertex lies in some part. -/
theorem OneSplit.mem_parts {x : V} (hx : x ≠ v) : ∃ i : Fin t, x ∈ sp.parts i := by
  rcases sp.hcov x with h | h
  · exact absurd h hx
  · exact h

/-- **A cycle of `G` which avoids the cut vertex lies in a single part.**  This is the 1-cut
counterpart of `VertexSplit.cycle_subset_parts`, and it is the statement that an odd cycle of `G`
either meets `v` or lies in a part — the fact that the transversal `1 + ∑ m` below rests on. -/
theorem OneSplit.cycle_subset_part {C : Finset V} (hC : IsOddCycle G C) (hv : C ∩ {v} = ∅) :
    ∃ i : Fin t, C ⊆ sp.parts i := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hmem : ∀ j : Fin m, f j ≠ v := by
    intro j hj
    have h1 : f j ∈ C := (hCmem (f j)).mpr ⟨j, rfl⟩
    have h2 : f j ∈ C ∩ {v} := Finset.mem_inter.mpr ⟨h1, Finset.mem_singleton.mpr hj⟩
    have h3 : f j ∉ C ∩ ({v} : Finset V) := by rw [hv]; simp
    exact h3 h2
  obtain ⟨i, hi⟩ := sp.mem_parts (hmem (⟨0, by omega⟩ : Fin m))
  have hj0 : f (⟨0, by omega⟩ : Fin m) ∈ sp.parts i := hi
  have hstep : ∀ j : Fin m, (f j ∈ sp.parts i) ↔ (f (cycSucc j) ∈ sp.parts i) := by
    intro j
    constructor
    · intro hj
      by_contra hn
      obtain ⟨l, hnl⟩ := sp.mem_parts (hmem (cycSucc j))
      have hjl : l = i := by
        by_contra hne
        exact (sp.hanti i l (Ne.symm hne) (f j) hj (f (cycSucc j)) hnl) (hcyc j)
      subst hjl
      exact hn hnl
    · intro hj
      by_contra hn
      obtain ⟨l, hnl⟩ := sp.mem_parts (hmem j)
      have hjl : l = i := by
        by_contra hne
        exact (sp.hanti i l (Ne.symm hne) (f (cycSucc j)) hj (f j) hnl) (hcyc j).symm
      subst hjl
      exact hn hnl
  refine ⟨i, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := (hCmem x).mp hx
  subst x
  exact mem_all_of_congr (m := m) (P := fun j : Fin m => f j ∈ sp.parts i) (by omega)
    (fun j => (hstep j).symm) hj0

/-- The odd cycles of `G` which avoid the cut vertex lie in the parts. -/
theorem OneSplit.oddCycle_part_or_hit {C : Finset V} (hC : IsOddCycle G C) :
    C ∩ {v} ≠ ∅ ∨ ∃ i : Fin t, IsOddCycle (induceFinset G (sp.parts i)) C := by
  by_cases hv : C ∩ {v} = ∅
  · obtain ⟨i, hi⟩ := sp.cycle_subset_part hC hv
    exact Or.inr ⟨i, hC.induceFinset hi⟩
  · exact Or.inl hv

/-- **A piece is a connected piece as soon as its vertices are joined to the cut vertex.**  If every
vertex of `T_i` is reachable from the cut vertex `v` — which holds as soon as `T_i` is a connected
component of `G - v` meeting `v` — then any two vertices of the piece `T_i ∪ {v}` are joined by a
path, through `v`.

A bare `OneSplit` does **not** say this: the parts are the components of `G - v` in the intended
use, and that is exactly the hypothesis carried by `erdos73On_of_1split_pieces`. -/
theorem OneSplit.piece_piecePreconnected (sp : OneSplit G v t) (i : Fin t)
    (hi : ∀ x ∈ sp.parts i, G.Reachable v x) : PiecePreconnected G (insert v (sp.parts i)) := by
  have hr : ∀ x : V, x ∈ insert v (sp.parts i) → G.Reachable v x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h' | h'
    · rw [h']
    · exact hi x h'
  intro u w hu hw
  exact (hr u hu).symm.trans (hr w hw)

/-- **The parts which are not bipartite.** -/
def OneSplit.nonBipartiteParts (sp : OneSplit G v t) [DecidablePred fun i =>
    ¬ (induceFinset G (sp.parts i)).IsBipartite] : Finset (Fin t) :=
  (Finset.univ : Finset (Fin t)).filter fun i => ¬ (induceFinset G (sp.parts i)).IsBipartite

/-- **The pieces `T_i ∪ {v}` which are not bipartite.**  (A *piece* is the part together with the cut
vertex: an odd cycle of `G` which meets the cut lives in a piece, `OneSplit.oddCycle_part_or_hit`.) -/
def OneSplit.nonBipartitePieces (sp : OneSplit G v t) [DecidablePred fun i =>
    ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite] : Finset (Fin t) :=
  (Finset.univ : Finset (Fin t)).filter fun i =>
    ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite

/-- **THE 1-CUT PARITY LEMMA.**  If every *piece* `T_i ∪ {v}` of a 1-cut of `G` is bipartite then `G`
is bipartite.

The colouring is glued from the pieces: two distinct parts are anticomplete, so their colours never
interfere, and there is a *single* vertex of the cut, so every piece can be rescaled (`flipCol`) to
give it the same colour.  This is the 1-cut analogue of `VertexSplit.isBipartite_of_split`, and it
is the reason a graph with a cut vertex is never the hard case of Erdős–Pósa.

**The pieces, not the bare parts, are the right objects**: a single vertex can see both colours of a
part (`K_2` plus a new vertex is `K_3`), so the statement about the bare parts is false; the
statement about the pieces is the classical 1-sum lemma. -/
theorem OneSplit.isBipartite_of_bipartite_pieces (sp : OneSplit G v t) [Fintype V]
    (h : ∀ i : Fin t, (induceFinset G (insert v (sp.parts i))).IsBipartite) : G.IsBipartite := by
  classical
  have hg : ∀ i : Fin t, ∃ c : V → Bool, Good2On G c (insert v (sp.parts i)) := by
    intro i
    obtain ⟨s, tt, hst⟩ := SimpleGraph.IsBipartite.exists_isBipartiteWith (h i)
    refine ⟨fun x => if x ∈ s then false else true, ?_⟩
    intro x y hx hy hAdj
    rcases hst.mem_of_adj ((induce_adj).mpr ⟨hx, hy, hAdj⟩) with ⟨hxs, hyt⟩ | ⟨hxt, hys⟩
    · have hyn : y ∉ s := Set.disjoint_right.mp hst.disjoint hyt
      simp [hxs, hyn]
    · have hxn : x ∉ s := Set.disjoint_right.mp hst.disjoint hxt
      simp [hxn, hys]
  set ci : Fin t → (V → Bool) := fun i => (hg i).choose with hci
  have hci' : ∀ i : Fin t, Good2On G (ci i) (insert v (sp.parts i)) := fun i => (hg i).choose_spec
  have hd : ∀ i : Fin t, Good2On G (flipCol (ci i) v) (insert v (sp.parts i)) :=
    fun i => (hci' i).flip v
  have hcut : ∀ i : Fin t, flipCol (ci i) v v = false := by
    intro i
    simp [flipCol]
  have hmemv : ∀ i : Fin t, v ∈ insert v (sp.parts i) := fun i => Finset.mem_insert_self v _
  have hmemvi : ∀ (i : Fin t) (x : V), x ∈ sp.parts i → x ∈ insert v (sp.parts i) :=
    fun i x hx => Finset.mem_insert_of_mem hx
  have hne : ∀ i : Fin t, ∀ ⦃x y : V⦄, x ∈ insert v (sp.parts i) → y ∈ insert v (sp.parts i) →
      G.Adj x y → flipCol (ci i) v x ≠ flipCol (ci i) v y := by
    intro i x y hx hy hAdj
    exact hd i (x := x) (y := y) hx hy hAdj
  have hpart : ∀ x : V, x ≠ v → ∃ i : Fin t, x ∈ sp.parts i := fun x hx => sp.mem_parts hx
  set cfun : V → Bool := fun x => if hx : x = v then false
    else flipCol (ci (hpart x hx).choose) v x with hcfun
  have hc_v : cfun v = false := by simp [cfun]
  have hc_x : ∀ (x : V) (hx : x ≠ v),
      cfun x = flipCol (ci (hpart x hx).choose) v x := by
    intro x hx
    simp [cfun, hx]
  have hc_xv : ∀ (x : V) (h : x = v), cfun x = false := by
    intro x h
    simp [cfun, h]
  refine Good2.isBipartite (c := cfun) ?_
  intro x y hAdj
  by_cases hxv : x = v
  · by_cases hyv : y = v
    · rw [hxv, hyv] at hAdj
      exact (G.irrefl hAdj).elim
    · have h1 := hne (hpart y hyv).choose (x := v) (y := y) (hmemv (hpart y hyv).choose)
        (hmemvi (hpart y hyv).choose y (hpart y hyv).choose_spec) (hxv ▸ hAdj)
      rw [hcut (hpart y hyv).choose] at h1
      rw [hc_xv x hxv, hc_x y hyv]
      exact h1
  · by_cases hyv : y = v
    · have h1 := hne (hpart x hxv).choose (x := x) (y := v)
        (hmemvi (hpart x hxv).choose x (hpart x hxv).choose_spec)
        (hmemv (hpart x hxv).choose) (hyv ▸ hAdj)
      rw [hcut (hpart x hxv).choose] at h1
      rw [hc_x x hxv, hc_xv y hyv]
      exact h1
    · have hceq : (hpart y hyv).choose = (hpart x hxv).choose := by
        by_contra hn
        have hn' : (hpart x hxv).choose ≠ (hpart y hyv).choose := fun h => hn h.symm
        exact (sp.hanti (hpart x hxv).choose (hpart y hyv).choose hn' x
          ((hpart x hxv).choose_spec) y ((hpart y hyv).choose_spec)) hAdj
      have h1 := hne (hpart x hxv).choose (x := x) (y := y)
        (hmemvi (hpart x hxv).choose x (hpart x hxv).choose_spec)
        (hceq ▸ hmemvi (hpart y hyv).choose y (hpart y hyv).choose_spec) hAdj
      rw [hc_x x hxv, hc_x y hyv, hceq]
      exact h1

/-- **THE 1-SUM LEMMA, in both directions.**  `G` is bipartite **iff** every piece `T_i ∪ {v}` of a
1-cut of `G` is bipartite.

The forward direction is the restriction of a 2-colouring to an induced subgraph; the backward
direction is `OneSplit.isBipartite_of_bipartite_pieces`.  This is the classical statement that
bipartiteness is preserved by wedging at a single vertex, and it is what makes a cut vertex
uninteresting for Erdős–Pósa. -/
theorem isBipartite_iff_bipartite_pieces (sp : OneSplit G v t) [Fintype V] :
    G.IsBipartite ↔ ∀ i : Fin t, (induceFinset G (insert v (sp.parts i))).IsBipartite := by
  constructor
  · intro hb i
    obtain ⟨c, hc⟩ := hb
    refine ⟨SimpleGraph.Coloring.mk c fun hadj => ?_⟩
    exact hc ((induce_adj.mp hadj).2.2)
  · exact sp.isBipartite_of_bipartite_pieces

/-- **The 1-cut parity lemma, contraposed: a non-bipartite graph with a 1-cut has a
non-bipartite piece.**  This is the classical observation behind the 1-cut decomposition: the
difficulty of `G` is concentrated in the pieces.

**A negative result worth recording.**  The tempting strengthening "*at least **two** non-bipartite
pieces*" is **false**, and the counterexample is the reason the *pieces* (and not the parts) are the
right objects: let `G` be a triangle with a pendant vertex and let `v` be the triangle vertex
carrying the pendant.  Then `G - v` has the two parts `{other two triangle vertices}` and
`{pendant}`, both of which are bipartite, the piece `triangle ∪ {v}` is not bipartite and the piece
`{v, pendant}` is: `G` is not bipartite and admits a 1-cut with **exactly one** non-bipartite
piece.  The depth bound a proof of Erdős–Pósa needs is therefore *not* obtainable from a single
1-cut; it is the block-cut tree theorem (`oneDepth_le_of_packing`, below), in which alternate
*blocks* of a chain carry disjoint odd cycles. -/
theorem OneSplit.one_nonBipartitePiece [Fintype V] (sp : OneSplit G v t)
    [DecidablePred fun i => ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite]
    (hnb : ¬ G.IsBipartite) : 1 ≤ (sp.nonBipartitePieces : Finset (Fin t)).card := by
  classical
  by_contra hlt
  refine hnb (sp.isBipartite_of_bipartite_pieces fun i => ?_)
  by_cases hbi : (induceFinset G (insert v (sp.parts i))).IsBipartite
  · exact hbi
  · have hmem : i ∈ sp.nonBipartitePieces := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hbi⟩
    have hpos : 0 < (sp.nonBipartitePieces : Finset (Fin t)).card := Finset.card_pos.mpr ⟨i, hmem⟩
    have h1 : 1 ≤ (sp.nonBipartitePieces : Finset (Fin t)).card := by omega
    exact (hlt h1).elim

/-- **A non-bipartite part makes its piece non-bipartite.** -/
theorem OneSplit.mem_nonBipartitePieces_of_mem_nonBipartiteParts [Fintype V] (sp : OneSplit G v t)
    [DecidablePred fun i => ¬ (induceFinset G (sp.parts i)).IsBipartite]
    [DecidablePred fun i => ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite]
    {i : Fin t} (hi : i ∈ sp.nonBipartiteParts) : i ∈ sp.nonBipartitePieces := by
  obtain ⟨-, hnb⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun hb => ?_⟩
  exact hnb (isBipartite_induceFinset_of_isBipartite hb (Finset.subset_insert v (sp.parts i)))

/-- **THE COUNTING LEMMA FOR A 1-CUT.**  If every packing of odd cycles of `G` has at most `r`
members then at most `r` parts of a 1-cut are non-bipartite: the non-bipartite parts are pairwise
disjoint, each carries an odd cycle, and one odd cycle per part is a packing. -/
theorem OneSplit.card_nonBipartiteParts_le {r : ℕ} (sp : OneSplit G v t) [Fintype V]
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r)
    [DecidablePred fun i => ¬ (induceFinset G (sp.parts i)).IsBipartite] :
    (sp.nonBipartiteParts : Finset (Fin t)).card ≤ r := by
  classical
  refine card_le_of_pieces_pack (ι := Fin t) (Q := sp.nonBipartiteParts) (p := sp.parts) hpack ?_ ?_ ?_
  · rintro X hX Y hY hne
    have hne' : X ≠ Y := by
      intro hne'
      apply hne
      simp [hne']
    exact sp.hdisj X Y hne'
  · intro X hX Y hY hne x hx hy
    have hne' : X ≠ Y := by
      intro hne'
      apply hne
      simp [hne']
    have hxy : sp.parts X ∩ sp.parts Y = ∅ := sp.hdisj X Y hne'
    exact absurd (Finset.mem_inter.mpr ⟨hx, hy⟩) (by rw [hxy]; simp)
  · intro X hX
    by_contra hcon
    exact (Finset.mem_filter.mp hX).2 (isBipartite_of_no_oddCycle hcon)

/-- **A TRANSVERSAL BUILT FROM THE NON-BIPARTITE PARTS OF A 1-CUT.**  If every non-bipartite part
`T_i` of a 1-cut is `m`-close to bipartite, then `{v}` together with one transversal per
non-bipartite part meets every odd cycle of `G`: an odd cycle either meets the cut vertex `v` or
lies in a single part, and the parts which are bipartite carry none. -/
theorem OneSplit.exists_transversal_nonBipartite {m : ℕ} (sp : OneSplit G v t) [Fintype V]
    [DecidablePred fun i => ¬ (induceFinset G (sp.parts i)).IsBipartite]
    (hpart : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (sp.parts i))) :
    ∃ Y : Finset V, HitsOddCycles G Y ∧ Y.card ≤ 1 + ∑ i ∈ sp.nonBipartiteParts, m := by
  classical
  have hex : ∀ i ∈ sp.nonBipartiteParts, ∃ Z : Finset V, Z.card ≤ m ∧
      (deleteFinset (induceFinset G (sp.parts i)) Z).IsBipartite := fun i hi => hpart i hi
  set X : Fin t → Finset V := fun i =>
    if hi : i ∈ sp.nonBipartiteParts then (hex i hi).choose else ∅ with hX
  have hXc : ∀ i : Fin t, X i =
      (if hi : i ∈ sp.nonBipartiteParts then (hex i hi).choose else ∅) := fun i => hX ▸ rfl
  have hXcard : ∀ i ∈ sp.nonBipartiteParts, (X i).card ≤ m := by
    intro i hi
    rw [hXc i, dite_eq_left hi]
    exact ((hex i hi).choose_spec).1
  have hXhits : ∀ i ∈ sp.nonBipartiteParts,
      HitsOddCycles (induceFinset G (sp.parts i)) (X i) := by
    intro i hi
    rw [hXc i, dite_eq_left hi]
    exact hitsOddCycles_of_isBipartite_delete ((hex i hi).choose_spec).2
  have hYhits : HitsOddCycles G (insert v (sp.nonBipartiteParts.biUnion X)) := by
    intro C hC hdis
    rcases sp.oddCycle_part_or_hit hC with hhit | ⟨i, hi⟩
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hhit
      have hxv : x = v := Finset.mem_singleton.mp (Finset.mem_inter.mp hx).2
      have hxmem : x ∈ C ∩ insert v (sp.nonBipartiteParts.biUnion X) :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, Finset.mem_insert.mpr (Or.inl hxv)⟩
      rw [hdis] at hxmem
      simp at hxmem
    · by_cases hi' : i ∈ sp.nonBipartiteParts
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr (hXhits i hi' C hi)
        have hx1 : x ∈ C := (Finset.mem_inter.mp hx).1
        have hx2 : x ∈ X i := (Finset.mem_inter.mp hx).2
        have hxmem : x ∈ C ∩ insert v (sp.nonBipartiteParts.biUnion X) :=
          Finset.mem_inter.mpr ⟨hx1, Finset.mem_insert.mpr
            (Or.inr (Finset.mem_biUnion.mpr ⟨i, hi', hx2⟩))⟩
        rw [hdis] at hxmem
        simp at hxmem
      · have hb : (induceFinset G (sp.parts i)).IsBipartite := by
          by_contra hnb
          exact hi' (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hnb⟩)
        exact (not_isOddCycle_of_isBipartite hb ⟨C, hi⟩)
  refine ⟨insert v (sp.nonBipartiteParts.biUnion X), hYhits, ?_⟩
  have hle : (insert v (sp.nonBipartiteParts.biUnion X) : Finset V).card
      ≤ (sp.nonBipartiteParts.biUnion X).card + 1 := Finset.card_insert_le v _
  have hcard' : (sp.nonBipartiteParts.biUnion X).card ≤ ∑ i ∈ sp.nonBipartiteParts, m := by
    calc (sp.nonBipartiteParts.biUnion X).card ≤ ∑ i ∈ sp.nonBipartiteParts, (X i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ sp.nonBipartiteParts, m := Finset.sum_le_sum fun i hi => hXcard i hi
  omega

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, ALONG THE 1-CUT AXIS.**  If `LocIndep k` forces
`CloseToBipartite m` in every part `T_i` of a 1-cut of `G`, then it forces
`CloseToBipartite (1 + m * k) G`.

The constant `1 + m * k` is independent of the number `t` of parts (only the non-bipartite ones
are charged, and there are at most `k` of them, `OneSplit.card_nonBipartiteParts_le`) and it
improves on the 2-cut instance `2 + m * k` of `JSPProblem/Count.lean`, because a 1-cut shares a
*single* vertex with each of its pieces.  No bound on the odd girth is used. -/
theorem closeToBipartite_of_1split_of_bounded_pieces (k m t : ℕ) [Fintype V] (sp : OneSplit G v t)
    [DecidablePred fun i => ¬ (induceFinset G (sp.parts i)).IsBipartite]
    (hpart : ∀ i ∈ sp.nonBipartiteParts, CloseToBipartite m (induceFinset G (sp.parts i)))
    (hG : LocIndep k G) : CloseToBipartite (1 + m * k) G := by
  classical
  obtain ⟨Y, hY, hYcard⟩ := sp.exists_transversal_nonBipartite (m := m) hpart
  have hJ : (sp.nonBipartiteParts : Finset (Fin t)).card ≤ k :=
    sp.card_nonBipartiteParts_le (fun C hC => hG.oddCycleFamily_card_le hC)
  have hsum : (∑ i ∈ sp.nonBipartiteParts, m) ≤ m * k := by
    have h1 : (∑ i ∈ sp.nonBipartiteParts, m)
        = (sp.nonBipartiteParts : Finset (Fin t)).card * m := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    have h2 : (sp.nonBipartiteParts : Finset (Fin t)).card * m ≤ m * k := by
      have h2' := Nat.mul_le_mul hJ (le_refl m)
      rwa [Nat.mul_comm k m] at h2'
    exact h1.le.trans h2
  have hcard : Y.card ≤ 1 + m * k := hYcard.trans (Nat.add_le_add_left hsum 1)
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 1 + m * k)).mpr ⟨Y, hcard, hY⟩

/-- **The 1-cut instance in the Erdős–Pósa form**: a bound `r` on the odd cycle packings of `G` is
enough, with the constant `1 + m * r`. -/
theorem closeToBipartite_of_1split_of_bounded_pieces_pack {r m : ℕ} [Fintype V]
    (sp : OneSplit G v t) [DecidablePred fun i => ¬ (induceFinset G (sp.parts i)).IsBipartite]
    (hpart : ∀ i ∈ sp.nonBipartiteParts, CloseToBipartite m (induceFinset G (sp.parts i)))
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r) :
    CloseToBipartite (1 + m * r) G := by
  classical
  obtain ⟨Y, hY, hYcard⟩ := sp.exists_transversal_nonBipartite (m := m) hpart
  have hJ : (sp.nonBipartiteParts : Finset (Fin t)).card ≤ r :=
    sp.card_nonBipartiteParts_le hpack
  have hsum : (∑ i ∈ sp.nonBipartiteParts, m) ≤ m * r := by
    have h1 : (∑ i ∈ sp.nonBipartiteParts, m)
        = (sp.nonBipartiteParts : Finset (Fin t)).card * m := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    have h2 : (sp.nonBipartiteParts : Finset (Fin t)).card * m ≤ m * r := by
      have h2' := Nat.mul_le_mul hJ (le_refl m)
      rwa [Nat.mul_comm r m] at h2'
    exact h1.le.trans h2
  have hcard : Y.card ≤ 1 + m * r := hYcard.trans (Nat.add_le_add_left hsum 1)
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 1 + m * r)).mpr ⟨Y, hcard, hY⟩

/-- **The same new instance, in the form in which the headline theorem composes**: if `LocIndep k`
forces `CloseToBipartite m` in every part `T_i` of a 1-cut, then it forces
`CloseToBipartite (1 + m * k) G`. -/
theorem erdos73On_of_1split_of_bounded_pieces (k m t : ℕ) [Fintype V] (sp : OneSplit G v t)
    [DecidablePred fun i => ¬ (induceFinset G (sp.parts i)).IsBipartite]
    (hpiece : ∀ i : Fin t, LocIndep k (induceFinset G (sp.parts i)) →
      CloseToBipartite m (induceFinset G (sp.parts i)))
    (hG : LocIndep k G) : CloseToBipartite (1 + m * k) G := by
  have hLoc : ∀ i : Fin t, LocIndep k (induceFinset G (sp.parts i)) :=
    fun i => hG.of_induceFinset (sp.parts i)
  exact closeToBipartite_of_1split_of_bounded_pieces (k := k) (m := m) (t := t) sp
    (fun i _ => hpiece i (hLoc i)) hG

/-- **The same instance for the research statement**: the *packing number* of `G` replaces the
`LocIndep` parameter. -/
theorem oddCycleErdosPosa_of_1split_of_bounded_pieces {r m : ℕ} [Fintype V] (sp : OneSplit G v t)
    [DecidablePred fun i => ¬ (induceFinset G (sp.parts i)).IsBipartite]
    (hpiece : ∀ i : Fin t,
      (∀ C : Finset (Finset V), IsOddCycleFamily (G := induceFinset G (sp.parts i)) C → C.card ≤ r) →
        CloseToBipartite m (induceFinset G (sp.parts i)))
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r) :
    CloseToBipartite (1 + m * r) G := by
  have hLoc : ∀ i : Fin t,
      (∀ C : Finset (Finset V), IsOddCycleFamily (G := induceFinset G (sp.parts i)) C → C.card ≤ r) :=
    fun i => fun C hC => hpack C hC.of_induceFinset
  exact closeToBipartite_of_1split_of_bounded_pieces_pack (r := r) (m := m) sp
    (fun i _ => hpiece i (hLoc i)) hpack

/-- **The 1-cut instance in the form used by the depth recursion**: the hypothesis is about the
*pieces* `T_i ∪ {v}` — the objects the decomposition `OneDepth` is about — rather than about the
bare parts.  A non-bipartite part has a non-bipartite piece
(`OneSplit.mem_nonBipartitePieces_of_mem_nonBipartiteParts`), so the two forms agree on the parts
which are charged. -/
theorem oddCycleErdosPosa_of_1split_of_bounded_pieces_about_pieces {r m : ℕ} [Fintype V]
    (sp : OneSplit G v t) [DecidablePred fun i => ¬ (induceFinset G (sp.parts i)).IsBipartite]
    (hpiece : ∀ i : Fin t,
      (∀ C : Finset (Finset V),
        IsOddCycleFamily (G := induceFinset G (insert v (sp.parts i))) C → C.card ≤ r) →
        CloseToBipartite m (induceFinset G (insert v (sp.parts i))))
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r) :
    CloseToBipartite (1 + m * r) G := by
  classical
  letI : DecidablePred fun i : Fin t =>
      ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite :=
    fun _ => Classical.propDecidable _
  have hpart : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (sp.parts i)) := by
    intro i hi
    refine closeToBipartite_induceFinset_of_sub (Finset.subset_insert v (sp.parts i)) (hpiece i ?_)
    intro C hC
    exact hpack C hC.of_induceFinset
  exact closeToBipartite_of_1split_of_bounded_pieces_pack (r := r) (m := m) sp hpart hpack

/-! ### Part 6 — the 1-cut depth, and the reduction to the 1-cut-free case -/

section Depth

/-- **`G` has a proper 1-cut**: a split `V = {v} ⊔ T₁ ⊔ … ⊔ T_t` with `t ≥ 2` pairwise anticomplete
nonempty parts, i.e. `v` is a cut vertex which really separates. -/
def HasProper1Split (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (t : ℕ) (sp : OneSplit G v t), 2 ≤ t

/-- **`G` has no proper 1-cut** — the 2-connected case, in the sense that matters for odd cycles. -/
def NoProper1Split (G : SimpleGraph V) : Prop := ¬ HasProper1Split G

theorem hasProper1Split_of_oneSplit {v : V} {t : ℕ} (sp : OneSplit G v t) (h2t : 2 ≤ t) :
    HasProper1Split G := ⟨v, t, sp, h2t⟩

theorem not_hasProper1Split_of_no_proper (h : NoProper1Split G) :
    ∀ (v : V) (t : ℕ) (sp : OneSplit G v t), ¬ (2 ≤ t) := by
  intro v t sp h2t
  exact h (hasProper1Split_of_oneSplit sp h2t)

/-- **`OneDepth G d`**: the vertex set of `G` splits, by at most `d` successive **1-cuts** (the
pieces being the parts together with the cut vertex), into pieces which are each *either bipartite
or 1-cut-free*.  `d = 0` is the 1-cut-free case; a bipartite piece stops the recursion for free,
which is exactly why the depth of the decomposition is bounded by the *odd girth* of the
block-cut tree rather than by `|V|`.

This is the invariant of the classical induction along a 1-cut decomposition, the 1-cut analogue
of `JSPProblem/Count.lean` `SplitDepth`. -/
def OneDepth (G : SimpleGraph V) : ℕ → Prop
  | 0 => G.IsBipartite ∨ NoProper1Split G
  | d + 1 => G.IsBipartite ∨ NoProper1Split G ∨
      ∃ (v : V) (t : ℕ) (sp : OneSplit G v t) (h2t : 2 ≤ t),
        ∀ i : Fin t, OneDepth (induceFinset G (insert v (sp.parts i))) d

/-- **The depth is monotone**: a decomposition of depth `d` is one of any larger depth. -/
theorem oneDepth_succ {G : SimpleGraph V} {d : ℕ} (h : OneDepth G d) : OneDepth G (d + 1) := by
  cases d with
  | zero =>
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  | succ e =>
      rcases h with h | h
      · exact Or.inl h
      · rcases h with h | h
        · exact Or.inr (Or.inl h)
        · obtain ⟨v, t, sp, h2t, hmem⟩ := h
          exact Or.inr (Or.inr ⟨v, t, sp, h2t, fun i => oneDepth_succ (hmem i)⟩)

theorem oneDepth_add {G : SimpleGraph V} (n : ℕ) {d : ℕ} (h : OneDepth G d) : OneDepth G (d + n) := by
  induction n with
  | zero => simpa using h
  | succ n ih => exact oneDepth_succ ih

theorem oneDepth_mono {G : SimpleGraph V} {d e : ℕ} (h : OneDepth G d) (hle : d ≤ e) :
    OneDepth G e := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact oneDepth_add c h

/-- A bipartite graph is `m`-close to bipartite for every `m`. -/
theorem closeToBipartite_of_isBipartite' {m : ℕ} (h : G.IsBipartite) : CloseToBipartite m G :=
  ⟨∅, Nat.zero_le _, isBipartite_delete h⟩

/-- **The bound obtained by decomposing `G` with `d` successive 1-cuts**, assuming the
1-cut-free case holds with the function `m`: at each level one pays `1 + p * (bound of the level
below)`, `p` being the packing number, because at most `p` parts are non-bipartite
(`OneSplit.card_nonBipartiteParts_le`) and the cut vertex is charged once. -/
def oneBound (m : ℕ → ℕ) (p d : ℕ) : ℕ :=
  Nat.rec (m p) (fun _ b => max (m p) (1 + p * b)) d

/-- **`oneBound m p d ≥ m p`.** -/
theorem le_oneBound (m : ℕ → ℕ) (p d : ℕ) : m p ≤ oneBound m p d := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ e ih => exact Nat.le_max_left _ _

/-- **THE PRECISE REDUCTION ALONG THE 1-CUT AXIS.**  Erdős–Pósa for odd cycles follows from (i) the
1-cut-free case — graphs with no cut vertex — and (ii) a uniform bound on the number of successive
1-cuts of `G`.

Concretely: suppose that for every packing number `p` there is a constant `m p` such that a graph
with no proper 1-cut and packing number at most `p` is `CloseToBipartite (m p)`, and that every
graph with packing number at most `p` can be decomposed by at most `d` successive 1-cuts
(`OneDepth H d`).  Then every graph with packing number at most `p` is
`CloseToBipartite (oneBound m p d)`.

Since `erdos73_of_erdosPosa` is proved, this says: **`jsp_000090_main` follows from the 1-cut-free
case of Erdős–Pósa for odd cycles together with the block-cut tree bound.**  Everything else — the
local structure at a shortest odd cycle (`Chord.lean`, `Fan.lean`), the residue induction
(`Residue.lean`), the anticomplete decompositions and their counting (`Additive.lean`), the 1-cut
decomposition and its counting (this file) — is proved. -/
theorem oddCycleErdosPosa_of_noOneCut_of_bounded_oneDepth (d : ℕ) (m : ℕ → ℕ)
    (hm : ∀ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (p : ℕ),
      (∀ C : Finset (Finset W), IsOddCycleFamily (G := H) C → C.card ≤ p) →
      NoProper1Split H → CloseToBipartite (m p) H)
    (hd : ∀ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (p : ℕ),
      (∀ C : Finset (Finset W), IsOddCycleFamily (G := H) C → C.card ≤ p) → OneDepth H d)
    (p : ℕ) : OddCycleErdosPosa.{u} p := by
  have key : ∀ (W : Type u) (instW : Fintype W) (H : SimpleGraph W) (p' : ℕ) (d' : ℕ),
      (∀ C : Finset (Finset W), IsOddCycleFamily (G := H) C → C.card ≤ p') →
      OneDepth H d' → CloseToBipartite (oneBound m p' d') H := by
    intro W instW H p' d'
    induction d' using Nat.strong_induction_on generalizing W H with
    | h d' ih =>
        intro hpack hd'
        rcases d' with _ | e
        · rcases hd' with hb | hd'
          · exact closeToBipartite_of_isBipartite' hb
          · obtain ⟨Z, hZ, hZbip⟩ := hm W instW H p' hpack hd'
            exact ⟨Z, hZ.trans (le_oneBound m p' 0), hZbip⟩
        · rcases hd' with hb | hd'
          · exact closeToBipartite_of_isBipartite' hb
          · rcases hd' with hd' | hd'
            · obtain ⟨Z, hZ, hZbip⟩ := hm W instW H p' hpack hd'
              exact ⟨Z, hZ.trans (le_oneBound m p' (e + 1)), hZbip⟩
            · obtain ⟨v, t, sp, h2t, hpieces⟩ := hd'
              classical
              have hpi : ∀ (i : Fin t),
                  (∀ C : Finset (Finset W),
                    IsOddCycleFamily (G := induceFinset H (insert v (sp.parts i))) C →
                      C.card ≤ p') →
                    CloseToBipartite (oneBound m p' e)
                      (induceFinset H (insert v (sp.parts i))) := by
                intro i hpi'
                by_cases hbi : (induceFinset H (insert v (sp.parts i))).IsBipartite
                · exact closeToBipartite_of_isBipartite' hbi
                · exact ih e (by omega) (W := W) (instW := instW)
                    (H := induceFinset H (insert v (sp.parts i)))
                    (fun C hC => hpack C hC.of_induceFinset)
                    (oneDepth_mono (hpieces i) (by omega))
              obtain ⟨Z, hZcard, hZbip⟩ :=
                oddCycleErdosPosa_of_1split_of_bounded_pieces_about_pieces
                  (r := p') (m := oneBound m p' e) sp hpi hpack
              have h1' : Z.card ≤ 1 + p' * oneBound m p' e := by
                have hZcard' := hZcard
                rwa [Nat.mul_comm (oneBound m p' e) p'] at hZcard'
              exact ⟨Z, h1'.trans (Nat.le_max_right _ _), hZbip⟩
  refine ⟨oneBound m p d, ?_⟩
  intro W instW H hpack
  exact key W instW H p d hpack (hd W instW H p hpack)

end Depth

/-- **THE CLASSICAL REDUCTION, CHAINED: connected pieces, then 1-cut-free pieces.**  If the
headline theorem holds with the constant `m` on *connected pieces* and `G` admits a 1-cut whose
parts satisfy the same local hypothesis, then `LocIndep k G` forces
`CloseToBipartite (1 + m * k) G`: a non-bipartite part has a non-bipartite piece, the piece is a
connected piece, the parts are charged `m` each, there are at most `k` of them, and the cut vertex
is charged once.

Composing with `erdos73On_of_piece` this is the statement *"Erdős #73 with the constant `m` for
connected graphs implies Erdős #73 with the constant `1 + m * k` for graphs with a cut vertex"* —
the first two steps of the classical reduction *connected → 2-connected*. -/
theorem erdos73On_of_1split_pieces {k m t : ℕ} (hP : PieceErdős73On.{u_1} k m) [Fintype V]
    (sp : OneSplit G v t) [DecidablePred fun i => ¬ (induceFinset G (sp.parts i)).IsBipartite]
    (hpre : ∀ i : Fin t, ∀ x ∈ sp.parts i, G.Reachable v x)
    (hG : LocIndep k G) : CloseToBipartite (1 + m * k) G := by
  classical
  have hpiece : ∀ (i : Fin t), LocIndep k (induceFinset G (sp.parts i)) →
      CloseToBipartite m (induceFinset G (sp.parts i)) := by
    intro i hLoc
    by_cases hbi : (induceFinset G (sp.parts i)).IsBipartite
    · exact closeToBipartite_of_isBipartite' hbi
    · have hnb' : ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite :=
        (Finset.mem_filter.mp
          (sp.mem_nonBipartitePieces_of_mem_nonBipartiteParts
            (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hbi⟩))).2
      exact closeToBipartite_induceFinset_of_sub (Finset.subset_insert v (sp.parts i))
        (hP V _ G hG (insert v (sp.parts i)) (sp.piece_piecePreconnected i (hpre i)) hnb')
  exact erdos73On_of_1split_of_bounded_pieces (k := k) (m := m) (t := t) sp hpiece hG

end OneCut

end

end JSP90
