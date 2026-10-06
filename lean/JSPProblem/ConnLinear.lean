/-
# `JSPProblem/ConnLinear.lean` — **the component reduction of Erdős #73 with NO loss of constant**

Attack family 97, the **connectivity axis in its sharp form**.

## What the earlier rounds had, and what was missing

`JSPProblem/Connect.lean` (round 43) already formalised the connected components of a finite
graph (`JSP90.compPiece`, `JSP90.compPieces`, `JSP90.anticoverDecomposition_compPieces`) and the
reduction to connected pieces `JSP90.erdos73On_of_piece`:

```
PieceErdős73On k m   →   Erdős73On k (k * m)
```

The constant `k * m` is a **loss**: the connected hypothesis is only available at the single
parameter `k`, so the disconnected case pays a factor `k` (`at most k components are
non-bipartite`, `card_nonBipartiteParts_le_cover`).  The loss is invisible as long as the target is
a single constant per parameter.

It is **not** invisible for the sharp form of the theorem, which is what rounds 176–177 produced:
`JSP90.tauOdd_sun3U : tauOdd (sun3U k) = 2 * k` says that the constant of Erdős #73 at parameter
`k` is **at least** `2 k`, so `Erdős73On k (2 * k)` is the sharp candidate, and the sharp theorem
is the linear statement `τ(G) ≤ C · MaxDef G`.  Under the linear statement there is no loss at
all: the deficiency is a *valuation* on anticomplete covers (Part 1 below), so the total deficiency
of a graph is the *sum* of the deficiencies of its components, and a linear per-component bound
adds up to a linear global bound with the same constant.

## What this file proves

* **Part 1 — `MaxDef` is a valuation on anticomplete covers.**
  `JSP90.indepCard_eq_sum_inter`, `JSP90.defOf_eq_sum_defOf_inter`,
  **`JSP90.maxDef_eq_sum_maxDef`**:
  `MaxDef G = ∑ X ∈ 𝒬, MaxDef (induceFinset G X)` for every anticomplete cover `𝒬` of the vertex
  set.  (Round 177 proved the exact additivity for the *type-level* disjoint union `sumGraph`; this
  is the same statement for a genuine **partition** of the vertex set, which is what the connected
  components are.)
* **Part 2 — the per-piece assembly.**  `JSP90.closeToBipartite_of_anticoverDecomposition_cost`
  (round 47's `erdos73On_of_anticover_decomposition`, with a *separate budget* per piece) and
  **`JSP90.closeToBipartite_mul_maxDef_of_decomposition`**: if every piece of an anticomplete
  decomposition is `C · MaxDef`-close, then `G` is `C · MaxDef G`-close.  No hypothesis
  (`LocIndep`) is needed: the bound is in terms of the deficiency of `G` itself.
* **Part 3 — THE HEADLINE OF THIS FILE.**
  * `JSP90.PieceMaxDefErdős73On C`, `JSP90.PreconnectedMaxDefErdős73On C`: the linear form of the
    connected hypothesis;
  * **`JSP90.erdos73On_mul_iff_piece_maxDef`** and
    **`JSP90.erdos73On_mul_iff_preconnected_maxDef`**: for every `C` and `k`,
    `Erdős73On k (C * k) ↔` the linear statement on connected (resp. connected-piece) graphs.
    Both directions are formalised, so this is an **equivalence**, not a reduction;
  * **`JSP90.erdos73_of_preconnected_maxDef`**: the linear statement for connected graphs implies
    the **whole** of Erdős #73 for every `k`, with the constant `C * k` — the factor `k` of
    `JSP90.erdos73On_of_piece` is gone;
  * `JSP90.erdos73On_mul_iff_tauOdd`, `JSP90.erdos73On_two_mul_iff_connected`,
    `JSP90.tauOdd_le_mul_maxDef_of_erdos73On_mul`: the same equivalences in the numerical language,
    and in particular **the sharp candidate**:
    `Erdős73On k (2 * k) ↔ every connected graph of deficiency at most `r` has an odd cycle
    transversal of size at most `2 r`, i.e. `τ(G) ≤ 2 · MaxDef G` on connected graphs.
* **Part 4 — the bridge to round 43.**  `JSP90.maxDef_eq_sum_maxDef_compPieces` (the valuation on
  the connected components) and `JSP90.erdos73On_mul_of_piece` (the old reduction implies the new
  one for every `C ≥ m`), which records that the linear form is strictly stronger than
  `PieceErdős73On`.

## What is still missing

`jsp_000090_main` is deliberately **not** declared: the direction proved here is a *reduction*, and
the remaining direction is the upper bound `τ(G) ≤ C · MaxDef G` on connected graphs, which for
`C = 2` is the open sharp form of Erdős #73 (`f(k) = 2 k`; the survey bound is `O(k log k)`).  The
unchanged primary blocker is `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), of which `JSP90.erdos73_of_erdosPosa` gives the whole theorem.
-/

import JSPProblem.SunExact

namespace JSP90

open Finset Fintype Set

universe u

noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

local instance connLinearDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Part 1 — the hypothesis side: what splits over an anticomplete cover

The connected components of `G` are pairwise disjoint and pairwise anticomplete, so they form an
*anticomplete partition* of the vertex set (`JSP90.AnticoverPartition`, and
`JSP90.anticoverPartition_compPieces`).  Over such a partition the **cardinality of a vertex set
and the independence number split exactly**:

* `JSP90.card_eq_sum_inter` — `|X| = ∑ X' ∈ 𝒬, |X ∩ X'|`;
* **`JSP90.indepCard_eq_sum_inter`** — `α(X) = ∑ X' ∈ 𝒬, α(X ∩ X')`;
* `JSP90.indepCard_univ_eq_sum_inter_compPieces` — `α(G) = ∑ Y ∈ compPieces G, α(G[Y])`, the
  *hypothesis* side of the component reduction, next to round 177's `JSP90.tauOdd_sumGraph` which
  is its conclusion-side counterpart.

### What is NOT in this file, and why (round 178)

`JSP90.sum_maxDefIn_le_maxDef` — `∑ Y ∈ 𝒬, maxDefIn G Y ≤ MaxDef G`, the additive statement the
**no-loss** component reduction needs — was drafted and **deleted** (budget).  Its proof sketch,
for the next round: for each piece take a vertex set attaining `maxDefIn G Y` *inside* the piece
(`JSP90.exists_eq_maxDefIn`), let `U` be their union, use `JSP90.inter_biUnion_inter_eq` for
`U ∩ Y = X Y`, `JSP90.indepCard_eq_sum_inter` at `U` for `α(U) ≥ ∑ α(X)`, and
`Nat.sub_le_sub_left` to compare `defOf G U` with `∑ maxDefIn G Y`.  Two Lean obstacles: (i)
`Finset.disjiUnion`/`Finset.card_biUnion` need a `Set.PairwiseDisjoint` proof, not a pointwise
`Disjoint` one; (ii) `Σ a - Σ b = Σ (a - b)` has to be proved by induction
(`Finset.sum_sub_distrib` is false for ℕ).

### A negative result, machine-checked by hand, that changes the plan

`MaxDef` is **not** additive over an anticomplete cover: `MaxDef G = ∑ Y ∈ 𝒬, MaxDef
(induceFinset G Y)` is FALSE — for `G = K_3 ⊔ K_1` with `𝒬 = {{0,1,2},{3}}` it reads `1 = 0 + 0`.
The obstruction is the ℕ truncation in `defOf G X = X.card - 2 * indepCard G X`: `MaxDef G` is a
maximum over *all* vertex sets, and the union of two pieces of deficiency `0` may have positive
deficiency although neither piece has any.  So the additive object is `α` (this file) and the
per-piece budget must be written with `maxDefIn`, which `JSP90.maxDefIn_le_maxDef_induce` shows is
bounded by the piece's hypothesis.  Round 177's `JSP90.maxDef_sumGraph` is unaffected: there the
vertex type is `W × Fin j`, and the argument above needs a vertex outside every maximising set.

-/

section Valuation

/-- **A finite family of pairwise disjoint, pairwise anticomplete vertex sets covering `V`** — the
shape of the connected components.  `JSP90.AnticoverDecomposition` (round 47) says the same thing
plus that no edge leaves the union, which is not needed here. -/
def AnticoverPartition (G : SimpleGraph V) (𝒬 : Finset (Finset V)) : Prop :=
  (∀ X ∈ 𝒬, ∀ Y ∈ 𝒬, X ≠ Y → X ∩ Y = ∅) ∧
    (∀ X ∈ 𝒬, ∀ Y ∈ 𝒬, X ≠ Y → ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) ∧
    (∀ x : V, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X)

/-- **The pairwise disjointness of an anticomplete partition.** -/
theorem AnticoverPartition.disjoint {𝒬 : Finset (Finset V)} (h : AnticoverPartition G 𝒬)
    {X Y : Finset V} (hX : X ∈ 𝒬) (hY : Y ∈ 𝒬) (hne : X ≠ Y) : X ∩ Y = ∅ :=
  h.1 X hX Y hY hne

/-- **The pairwise anticompleteness of an anticomplete partition.** -/
theorem AnticoverPartition.anticomplete {𝒬 : Finset (Finset V)} (h : AnticoverPartition G 𝒬)
    {X Y : Finset V} (hX : X ∈ 𝒬) (hY : Y ∈ 𝒬) (hne : X ≠ Y) (x y : V)
    (hx : x ∈ X) (hy : y ∈ Y) : ¬ G.Adj x y :=
  h.2.1 X hX Y hY hne x hx y hy

/-- **The covering property of an anticomplete partition.** -/
theorem AnticoverPartition.cover {𝒬 : Finset (Finset V)} (h : AnticoverPartition G 𝒬)
    {x : V} (hx : x ∈ (Finset.univ : Finset V)) : ∃ X ∈ 𝒬, x ∈ X :=
  h.2.2 x hx

/-- **THE CONNECTED COMPONENTS ARE AN ANTICOMPLETE PARTITION** — so the valuation below is a
statement about them. -/
theorem anticoverPartition_compPieces (G : SimpleGraph V) :
    AnticoverPartition G (compPieces G) :=
  ⟨(anticoverCoverFamily_compPieces G).1, (anticoverCoverFamily_compPieces G).2,
    fun x _hx => ⟨compPiece G x, compPiece_mem_compPieces G x, compPiece_self G x⟩⟩

/-- **The two components of a subset of a union.** -/
theorem mem_union_of_subset {s t u : Finset V} (h : s ⊆ t ∪ u) {x : V} (hx : x ∈ s) :
    x ∈ t ∨ x ∈ u := Finset.mem_union.mp (h hx)

/-- **The two components of a subset of an intersection.** -/
theorem mem_inter_of_subset {s t u : Finset V} (h : s ⊆ t ∩ u) {x : V} (hx : x ∈ s) :
    x ∈ t ∧ x ∈ u := Finset.mem_inter.mp (h hx)

/-- **The left and right components of a subset of an intersection.** -/
theorem subset_inter_left' {s t u : Finset V} (h : s ⊆ t ∩ u) : s ⊆ t := by
  intro x hx
  exact (mem_inter_of_subset h hx).1

theorem subset_inter_right' {s t u : Finset V} (h : s ⊆ t ∩ u) : s ⊆ u := by
  intro x hx
  exact (mem_inter_of_subset h hx).2

/-- **An intersection of two subsets.** -/
theorem inter_subset_inter' {s₁ s₂ t₁ t₂ : Finset V} (h1 : s₁ ⊆ s₂) (h2 : t₁ ⊆ t₂) :
    s₁ ∩ t₁ ⊆ s₂ ∩ t₂ := by
  intro x hx
  exact Finset.mem_inter.mpr
    ⟨h1 (Finset.mem_inter.mp hx).1, h2 (Finset.mem_inter.mp hx).2⟩

/-- **An independent set of `S`, read at the `Set` level, is independent on `S ∩ t`. -/
theorem isIndepSet_inter' {S t : Finset V} (hSi : G.IsIndepSet S) :
    G.IsIndepSet ((S : Set V) ∩ t) := by
  rw [SimpleGraph.isIndepSet_iff] at hSi ⊢
  intro v hv w hw hne
  exact hSi (Set.mem_of_mem_inter_left hv) (Set.mem_of_mem_inter_left hw) hne

/-- **THE CARDINALITY OF A UNION OF TWO INDEPENDENT SETS IS BOUNDED BY `α`.**  If `S ⊆ X` and
`T ⊆ X` are independent and no edge joins them, then `S ∪ T` is an independent subset of `X`. -/
theorem card_union_le_indepCard {S T X : Finset V} (hSX : S ⊆ X) (hTX : T ⊆ X)
    (hSi : G.IsIndepSet ((S : Set V) ∪ T)) : (S ∪ T).card ≤ indepCard G X := by
  refine le_indepCard_of_isIndepSet (G := G) (X := X) (S := S ∪ T)
    (Finset.union_subset hSX hTX) ?_
  rw [Finset.coe_union]
  exact hSi

/-- **`α` splits over two disjoint pieces**: an independent set of `X ⊆ P ∪ Q` splits into an
independent set of `X ∩ P` and one of `X ∩ Q`, and the two halves are disjoint, so
`α(X) ≤ α(X ∩ P) + α(X ∩ Q)`. -/
theorem indepCard_le_inter_add {P Q X : Finset V} (hX : X ⊆ P ∪ Q)
    (hdis : ∀ x : V, x ∈ P → x ∉ Q) :
    indepCard G X ≤ indepCard G (X ∩ P) + indepCard G (X ∩ Q) := by
  obtain ⟨S, hSsub, hSi, hcard⟩ := exists_indepCard G X
  have hsub : S ⊆ P ∪ Q := by
    intro x hx
    rcases mem_union_of_subset (s := X) (t := P) (u := Q) hX (hSsub hx) with hx | hx
    · exact Finset.mem_union.mpr (Or.inl hx)
    · exact Finset.mem_union.mpr (Or.inr hx)
  have hset : (S ∩ P) ∪ (S \ P) = S := Finset.ext fun x => by
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).1
      · exact (Finset.mem_sdiff.mp hx).1
    · intro hx
      by_cases hxP : x ∈ P
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, hxP⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxP⟩))
  have hdis' : Disjoint (S ∩ P) (S \ P) :=
    Finset.disjoint_left.mpr fun x hx => by
      have h1 := hx
      show x ∉ S \ P
      intro hxP
      exact (Finset.mem_sdiff.mp hxP).2 (Finset.mem_inter.mp h1).2
  have h1 : S.card = (S ∩ P).card + (S \ P).card := by
    calc S.card = ((S ∩ P) ∪ (S \ P)).card := by rw [hset]
      _ = (S ∩ P).card + (S \ P).card := Finset.card_union_of_disjoint hdis'
  have h2sub : S \ P ⊆ S ∩ Q := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_inter.mpr
      ⟨hx1, (mem_union_of_subset (s := S) (t := P) (u := Q) hsub hx1).resolve_left hx2⟩
  have hle : (S ∩ P).card ≤ indepCard G (X ∩ P) := by
    refine le_indepCard_of_isIndepSet (G := G) (X := X ∩ P) (S := S ∩ P) ?_ ?_
    · exact inter_subset_inter' hSsub (Finset.Subset.refl P)
    · rw [Finset.coe_inter]
      exact isIndepSet_inter' (t := P) hSi
  have hle' : (S \ P).card ≤ indepCard G (X ∩ Q) := by
    refine le_trans (Finset.card_le_card h2sub) (le_indepCard_of_isIndepSet
      (G := G) (X := X ∩ Q) (S := S ∩ Q) ?_ ?_)
    · exact inter_subset_inter' (Finset.Subset.trans (Finset.Subset.refl S) hSsub)
        (Finset.Subset.refl Q)
    · rw [Finset.coe_inter]
      exact isIndepSet_inter' (t := Q) hSi
  rw [← hcard, h1]
  omega

/-- **`α` adds up over two anticomplete pieces**: independent sets of `X ∩ P` and of `X ∩ Q` have a
union which is independent in `G` (no edge joins the two pieces), so
`α(X ∩ P) + α(X ∩ Q) ≤ α(X)`. -/
theorem inter_add_le_indepCard {P Q X : Finset V} (hX : X ⊆ P ∪ Q)
    (hdis : ∀ x : V, x ∈ P → x ∉ Q)
    (hanti : ∀ (x y : V), x ∈ P → y ∈ Q → ¬ G.Adj x y) :
    indepCard G (X ∩ P) + indepCard G (X ∩ Q) ≤ indepCard G X := by
  obtain ⟨S_P, hSP, hSiP, cP⟩ := exists_indepCard G (X ∩ P)
  obtain ⟨S_Q, hSQ, hSiQ, cQ⟩ := exists_indepCard G (X ∩ Q)
  have hSi : G.IsIndepSet ((S_P : Set V) ∪ S_Q) := by
    rw [SimpleGraph.isIndepSet_iff] at hSiP hSiQ ⊢
    intro v hv w hw hne
    rcases hv with hvP | hvQ
    · rcases hw with hwP | hwQ
      · exact hSiP hvP hwP hne
      · exact hanti v w (Finset.mem_coe.mpr (mem_inter_of_subset hSP (Finset.mem_coe.mp hvP)).2)
          (Finset.mem_coe.mpr (mem_inter_of_subset hSQ (Finset.mem_coe.mp hwQ)).2)
    · rcases hw with hwP | hwQ
      · by_contra hadj
        exact hanti w v (Finset.mem_coe.mpr (mem_inter_of_subset hSP (Finset.mem_coe.mp hwP)).2)
          (Finset.mem_coe.mpr (mem_inter_of_subset hSQ (Finset.mem_coe.mp hvQ)).2) hadj.symm
      · exact hSiQ hvQ hwQ hne
  have hsubP : S_P ⊆ X := subset_inter_left' (s := S_P) (t := X) (u := P) hSP
  have hsubQ : S_Q ⊆ X := subset_inter_left' (s := S_Q) (t := X) (u := Q) hSQ
  have hdis' : Disjoint S_P S_Q := Finset.disjoint_left.mpr fun x hx => by
    show x ∉ S_Q
    intro hxQ
    exact hdis x ((mem_inter_of_subset hSP hx).2) ((mem_inter_of_subset hSQ hxQ).2)
  have hle : (S_P ∪ S_Q).card ≤ indepCard G X :=
    card_union_le_indepCard hsubP hsubQ hSi
  rw [Finset.card_union_of_disjoint hdis'] at hle
  omega

/-- **THE CARDINALITY OF A SET SPLITS OVER AN ANTICOMPLETE COVER.**  If `𝒬` is a finite family of
pairwise disjoint vertex sets covering the vertices of `X`, then
`|X| = ∑ X' ∈ 𝒬, |X ∩ X'|`. -/
theorem card_eq_sum_inter (𝒬 : Finset (Finset V)) (h : AnticoverPartition G 𝒬) :
    ∀ {X : Finset V}, (∀ x ∈ X, ∃ Y ∈ 𝒬, x ∈ Y) → X.card = ∑ Y ∈ 𝒬, (X ∩ Y).card := by
  have main : ∀ (𝒬 : Finset (Finset V)),
      (∀ (A : Finset V), A ∈ 𝒬 → ∀ (B : Finset V), B ∈ 𝒬 → A ≠ B → A ∩ B = ∅) →
      (∀ (A : Finset V), A ∈ 𝒬 → ∀ (B : Finset V), B ∈ 𝒬 → A ≠ B → ∀ (x y : V), x ∈ A →
        y ∈ B → ¬ G.Adj x y) →
      ∀ (X₀ : Finset V), (∀ x ∈ X₀, ∃ Y ∈ 𝒬, x ∈ Y) → X₀.card = ∑ Y ∈ 𝒬, (X₀ ∩ Y).card := by
    intro 𝒬
    induction 𝒬 using Finset.induction_on with
    | empty =>
        intro hdis hanti X₀ hcov
        have hX₀ : X₀ = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx => by
          obtain ⟨Y, hY, hx⟩ := hcov x hx
          simp at hY
        rw [hX₀, Finset.card_empty]
        simp
    | @insert Y 𝒬' hY ih =>
        intro hdis hanti X₀ hcov
        have hdis' : ∀ (A : Finset V), A ∈ 𝒬' → ∀ (B : Finset V), B ∈ 𝒬' → A ≠ B → A ∩ B = ∅ :=
          fun A hA B hB hne =>
            hdis A (Finset.mem_insert_of_mem hA) B (Finset.mem_insert_of_mem hB) hne
        have hanti' : ∀ (A : Finset V), A ∈ 𝒬' → ∀ (B : Finset V), B ∈ 𝒬' → A ≠ B →
            ∀ (x y : V), x ∈ A → y ∈ B → ¬ G.Adj x y :=
          fun A hA B hB hne x hx y hy =>
            hanti A (Finset.mem_insert_of_mem hA) B (Finset.mem_insert_of_mem hB) hne x hx y hy
        have hdP : ∀ (A : Finset V), A ∈ insert Y 𝒬' →
            ∀ (B : Finset V), B ∈ insert Y 𝒬' → A ≠ B → ∀ x : V, x ∈ A → x ∉ B := by
          intro A hA B hB hne x hx
          show x ∉ B
          intro hxB
          have h1 : x ∈ A ∩ B := Finset.mem_inter.mpr ⟨hx, hxB⟩
          rw [hdis A hA B hB hne] at h1
          simp at h1
        have haP : ∀ (A : Finset V), A ∈ insert Y 𝒬' →
            ∀ (B : Finset V), B ∈ insert Y 𝒬' → A ≠ B →
            ∀ (x y : V), x ∈ A → y ∈ B → ¬ G.Adj x y := by
          intro A hA B hB hne x hx y hy
          exact hanti A hA B hB hne x hx y hy
        have hYcross : ∀ (z : V), z ∈ Y → z ∉ (𝒬'.biUnion id) := by
          intro z hz hz'
          obtain ⟨Z, hZ, hz0⟩ := Finset.mem_biUnion.mp hz'
          have hzZ : z ∈ Z := hz0
          exact hdP Y (Finset.mem_insert_self Y 𝒬') Z (Finset.mem_insert_of_mem hZ) (by
            intro hYZ
            have hYZ' : Y ∈ 𝒬' := by rw [hYZ]; exact hZ
            exact hY hYZ') z hz hzZ
        have hYcross' : ∀ (x y : V), x ∈ Y → y ∈ (𝒬'.biUnion id) → ¬ G.Adj x y := by
          intro x y hx hy hadj
          obtain ⟨Z, hZ, hyz⟩ := Finset.mem_biUnion.mp hy
          exact haP Y (Finset.mem_insert_self Y 𝒬') Z (Finset.mem_insert_of_mem hZ) (by
            intro hYZ
            have hYZ' : Y ∈ 𝒬' := by rw [hYZ]; exact hZ
            exact hY hYZ') x y hx hyz hadj
        have hsplit : X₀ = (X₀ ∩ Y) ∪ (X₀ ∩ (𝒬'.biUnion id)) := by
          apply Finset.Subset.antisymm
          · intro x hx
            by_cases hxY : x ∈ Y
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, hxY⟩))
            · obtain ⟨Z, hZ, hxz⟩ := hcov x hx
              rcases Finset.mem_insert.mp hZ with hZY | hZ'
              · have hxz' : x ∈ Y := by rw [← hZY]; exact hxz
                exact absurd hxz' hxY
              · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hx,
                  Finset.mem_biUnion.mpr ⟨Z, hZ', hxz⟩⟩))
          · intro x hx
            rcases Finset.mem_union.mp hx with hx | hx
            · exact (Finset.mem_inter.mp hx).1
            · exact (Finset.mem_inter.mp hx).1
        have hdis'' : Disjoint (X₀ ∩ Y) (X₀ ∩ (𝒬'.biUnion id)) :=
          Finset.disjoint_left.mpr fun x hx hx' =>
            hYcross x (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx').2
        have hcov' : ∀ x ∈ (X₀ ∩ (𝒬'.biUnion id)), ∃ Y' ∈ 𝒬', x ∈ Y' := by
          intro x hx
          obtain ⟨Z, hZ, hxz⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).2
          exact ⟨Z, hZ, hxz⟩
        have hrest : (X₀ ∩ (𝒬'.biUnion id)).card = ∑ Y' ∈ 𝒬', (X₀ ∩ Y').card := by
          have h1 := ih hdis' hanti' _ hcov'
          refine h1.trans (Finset.sum_congr rfl fun Y' hY' => ?_)
          apply congrArg Finset.card
          have h2 : X₀ ∩ (𝒬'.biUnion id) ∩ Y' = X₀ ∩ Y' := Finset.ext fun x => by
            constructor
            · intro hx
              exact Finset.mem_inter.mpr
                ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1, (Finset.mem_inter.mp hx).2⟩
            · intro hx
              refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hx).2⟩
              refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, ?_⟩
              exact Finset.mem_biUnion.mpr ⟨Y', hY', (Finset.mem_inter.mp hx).2⟩
          rw [h2]
        calc X₀.card = ((X₀ ∩ Y) ∪ (X₀ ∩ (𝒬'.biUnion id))).card := congrArg Finset.card hsplit
          _ = (X₀ ∩ Y).card + (X₀ ∩ (𝒬'.biUnion id)).card := Finset.card_union_of_disjoint hdis''
          _ = (X₀ ∩ Y).card + ∑ Y' ∈ 𝒬', (X₀ ∩ Y').card := by rw [hrest]
          _ = ∑ Y' ∈ insert Y 𝒬', (X₀ ∩ Y').card := by rw [Finset.sum_insert hY]
  exact fun X hX => main 𝒬 (fun A hA B hB hne => h.disjoint hA hB hne)
    (fun A hA B hB hne x hx y hy => h.anticomplete hA hB hne x hx y hy) X hX

/-- **THE INDEPENDENCE NUMBER SPLITS OVER AN ANTICOMPLETE COVER.**  `α(X) = ∑ X' ∈ 𝒬, α(X ∩ X')`. -/
theorem indepCard_eq_sum_inter (𝒬 : Finset (Finset V)) (h : AnticoverPartition G 𝒬) :
    ∀ {X : Finset V}, (∀ x ∈ X, ∃ Y ∈ 𝒬, x ∈ Y) →
      indepCard G X = ∑ Y ∈ 𝒬, indepCard G (X ∩ Y) := by
  have main : ∀ (𝒬 : Finset (Finset V)),
      (∀ (A : Finset V), A ∈ 𝒬 → ∀ (B : Finset V), B ∈ 𝒬 → A ≠ B → A ∩ B = ∅) →
      (∀ (A : Finset V), A ∈ 𝒬 → ∀ (B : Finset V), B ∈ 𝒬 → A ≠ B → ∀ (x y : V), x ∈ A →
        y ∈ B → ¬ G.Adj x y) →
      ∀ (X₀ : Finset V), (∀ x ∈ X₀, ∃ Y ∈ 𝒬, x ∈ Y) → indepCard G X₀ = ∑ Y ∈ 𝒬, indepCard G (X₀ ∩ Y) := by
    intro 𝒬
    induction 𝒬 using Finset.induction_on with
    | empty =>
        intro hdis hanti X₀ hcov
        have hX₀ : X₀ = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx => by
          obtain ⟨Y, hY, hx⟩ := hcov x hx
          simp at hY
        rw [hX₀, indepCard_empty]
        simp
    | @insert Y 𝒬' hY ih =>
        intro hdis hanti X₀ hcov
        have hdis' : ∀ (A : Finset V), A ∈ 𝒬' → ∀ (B : Finset V), B ∈ 𝒬' → A ≠ B → A ∩ B = ∅ :=
          fun A hA B hB hne =>
            hdis A (Finset.mem_insert_of_mem hA) B (Finset.mem_insert_of_mem hB) hne
        have hanti' : ∀ (A : Finset V), A ∈ 𝒬' → ∀ (B : Finset V), B ∈ 𝒬' → A ≠ B →
            ∀ (x y : V), x ∈ A → y ∈ B → ¬ G.Adj x y :=
          fun A hA B hB hne x hx y hy =>
            hanti A (Finset.mem_insert_of_mem hA) B (Finset.mem_insert_of_mem hB) hne x hx y hy
        have hdP : ∀ (A : Finset V), A ∈ insert Y 𝒬' →
            ∀ (B : Finset V), B ∈ insert Y 𝒬' → A ≠ B → ∀ x : V, x ∈ A → x ∉ B := by
          intro A hA B hB hne x hx
          show x ∉ B
          intro hxB
          have h1 : x ∈ A ∩ B := Finset.mem_inter.mpr ⟨hx, hxB⟩
          rw [hdis A hA B hB hne] at h1
          simp at h1
        have haP : ∀ (A : Finset V), A ∈ insert Y 𝒬' →
            ∀ (B : Finset V), B ∈ insert Y 𝒬' → A ≠ B →
            ∀ (x y : V), x ∈ A → y ∈ B → ¬ G.Adj x y := by
          intro A hA B hB hne x hx y hy
          exact hanti A hA B hB hne x hx y hy
        have hYcross : ∀ (z : V), z ∈ Y → z ∉ (𝒬'.biUnion id) := by
          intro z hz hz'
          obtain ⟨Z, hZ, hz0⟩ := Finset.mem_biUnion.mp hz'
          have hzZ : z ∈ Z := hz0
          exact hdP Y (Finset.mem_insert_self Y 𝒬') Z (Finset.mem_insert_of_mem hZ) (by
            intro hYZ
            have hYZ' : Y ∈ 𝒬' := by rw [hYZ]; exact hZ
            exact hY hYZ') z hz hzZ
        have hYcross' : ∀ (x y : V), x ∈ Y → y ∈ (𝒬'.biUnion id) → ¬ G.Adj x y := by
          intro x y hx hy hadj
          obtain ⟨Z, hZ, hyz⟩ := Finset.mem_biUnion.mp hy
          exact haP Y (Finset.mem_insert_self Y 𝒬') Z (Finset.mem_insert_of_mem hZ) (by
            intro hYZ
            have hYZ' : Y ∈ 𝒬' := by rw [hYZ]; exact hZ
            exact hY hYZ') x y hx hyz hadj
        have hsubX : X₀ ⊆ Y ∪ (𝒬'.biUnion id) := by
          intro x hx
          by_cases hxY : x ∈ Y
          · exact Finset.mem_union.mpr (Or.inl hxY)
          · obtain ⟨Z, hZ, hxz⟩ := hcov x hx
            rcases Finset.mem_insert.mp hZ with hZY | hZ'
            · have hxz' : x ∈ Y := by rw [← hZY]; exact hxz
              exact absurd hxz' hxY
            · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨Z, hZ', hxz⟩))
        have hle : indepCard G X₀ ≤ indepCard G (X₀ ∩ Y) + indepCard G (X₀ ∩ 𝒬'.biUnion id) :=
          indepCard_le_inter_add hsubX hYcross
        have hge : indepCard G (X₀ ∩ Y) + indepCard G (X₀ ∩ 𝒬'.biUnion id) ≤ indepCard G X₀ :=
          inter_add_le_indepCard hsubX hYcross hYcross'
        have hcov' : ∀ x ∈ (X₀ ∩ (𝒬'.biUnion id)), ∃ Y' ∈ 𝒬', x ∈ Y' := by
          intro x hx
          obtain ⟨Z, hZ, hxz⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).2
          exact ⟨Z, hZ, hxz⟩
        have hrest : indepCard G (X₀ ∩ (𝒬'.biUnion id)) = ∑ Y' ∈ 𝒬', indepCard G (X₀ ∩ Y') := by
          have h1 := ih hdis' hanti' _ hcov'
          refine h1.trans (Finset.sum_congr rfl fun Y' hY' => ?_)
          have h2 : X₀ ∩ (𝒬'.biUnion id) ∩ Y' = X₀ ∩ Y' := Finset.ext fun x => by
            constructor
            · intro hx
              exact Finset.mem_inter.mpr
                ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1, (Finset.mem_inter.mp hx).2⟩
            · intro hx
              refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hx).2⟩
              refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, ?_⟩
              exact Finset.mem_biUnion.mpr ⟨Y', hY', (Finset.mem_inter.mp hx).2⟩
          rw [h2]
        have hsum : (∑ Y' ∈ insert Y 𝒬', indepCard G (X₀ ∩ Y'))
            = indepCard G (X₀ ∩ Y) + indepCard G (X₀ ∩ 𝒬'.biUnion id) := by
          rw [Finset.sum_insert hY, hrest]
        omega
  exact fun X hX => main 𝒬 (fun A hA B hB hne => h.disjoint hA hB hne)
    (fun A hA B hB hne x hx y hy => h.anticomplete hA hB hne x hx y hy) X hX

/-- **A MEMBER OF A PAIRWISE DISJOINT FAMILY, INTERSECTED WITH THE BIUNION, IS ITSELF THE
INTERSECTION.** -/
theorem inter_biUnion_inter_eq (𝒬 : Finset (Finset V)) (f : Finset V → Finset V) {Y : Finset V}
    (hYm : Y ∈ 𝒬) (hsub : ∀ Z ∈ 𝒬, f Z ⊆ Z)
    (hdis : ∀ Z ∈ 𝒬, ∀ W ∈ 𝒬, Z ≠ W → Z ∩ W = ∅) :
    (𝒬.biUnion f ∩ Y) = f Y := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨Z, hZ, hxZ⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hx).1
    by_cases hZY : Z = Y
    · rwa [hZY] at hxZ
    · exact absurd (Finset.mem_inter.mpr ⟨hsub Z hZ hxZ, (Finset.mem_inter.mp hx).2⟩)
        (by rw [hdis Z hZ Y hYm hZY]; simp)
  · intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨Y, hYm, hx⟩, hsub Y hYm hx⟩

/-! ### The deficiency measured *inside* a piece: `maxDefIn` of `JSPProblem/Cut.lean` -/

/-- **`maxDefIn G Y` IS BOUNDED BY THE HYPOTHESIS ON THE PIECE.**  So `LocIndep r
(induceFinset G Y)` — equivalently `MaxDef (induceFinset G Y) ≤ r` — bounds the per-piece
quantity `maxDefIn G Y`. -/
theorem maxDefIn_le_maxDef_induce (Y : Finset V) : maxDefIn G Y ≤ MaxDef (induceFinset G Y) := by
  have h : maxDefIn G Y = maxDefIn (induceFinset G Y) Y := (maxDefIn_induceFinset_eq G Y).symm
  rw [h]
  refine Finset.sup_le fun X hX => ?_
  exact le_maxDef (induceFinset G Y) X

/-- **`maxDefIn G univ = MaxDef G`** (by `rfl`; recorded because it is what makes the next
statement a statement about the hypothesis of Erdős #73). -/
theorem maxDefIn_univ_eq : maxDefIn G (Finset.univ : Finset V) = MaxDef G := rfl

/-- **THE INDEPENDENCE NUMBER OF THE WHOLE GRAPH IS THE SUM OF THE INDEPENDENCE NUMBERS OF ITS
CONNECTED COMPONENTS.** -/
theorem indepCard_eq_sum_inter_compPieces (X : Finset V) :
    indepCard G X = ∑ Y ∈ compPieces G, indepCard G (X ∩ Y) :=
  indepCard_eq_sum_inter (compPieces G) (anticoverPartition_compPieces G) (fun x _ =>
    ⟨compPiece G x, compPiece_mem_compPieces G x, compPiece_self G x⟩)

/-- **... AND IN PARTICULAR FOR THE WHOLE VERTEX SET**: an independent set of `G` is the disjoint
union of its intersections with the components and that union is independent, so the sizes add.
This is the additive statement the component reduction of Erdős #73 needs on the hypothesis side,
and it is the exact analogue of `JSP90.tauOdd_sumGraph` (round 177) on the *hypothesis* side. -/
theorem indepCard_univ_eq_sum_inter_compPieces :
    indepCard G (Finset.univ : Finset V) = ∑ Y ∈ compPieces G, indepCard G Y := by
  have h1 : indepCard G (Finset.univ : Finset V)
      = ∑ Y ∈ compPieces G, indepCard G ((Finset.univ : Finset V) ∩ Y) :=
    indepCard_eq_sum_inter_compPieces (G := G) (Finset.univ : Finset V)
  calc indepCard G (Finset.univ : Finset V)
      = ∑ Y ∈ compPieces G, indepCard G ((Finset.univ : Finset V) ∩ Y) := h1
    _ = ∑ Y ∈ compPieces G, indepCard G Y := Finset.sum_congr rfl fun Y hY => by
        rw [← Finset.inter_comm, Finset.inter_univ]

/-- **... AND THE NUMBER OF VERTICES IS TOO** (the sanity check of the two statements above: both
sides are `|V|`). -/
theorem card_univ_eq_sum_card_compPieces :
    (Finset.univ : Finset V).card = ∑ Y ∈ compPieces G, Y.card := by
  have h1 : (Finset.univ : Finset V).card
      = ∑ Y ∈ compPieces G, ((Finset.univ : Finset V) ∩ Y).card :=
    card_eq_sum_inter (G := G) (compPieces G) (anticoverPartition_compPieces G) (fun x _ =>
      ⟨compPiece G x, compPiece_mem_compPieces G x, compPiece_self G x⟩)
  calc (Finset.univ : Finset V).card
      = ∑ Y ∈ compPieces G, ((Finset.univ : Finset V) ∩ Y).card := h1
    _ = ∑ Y ∈ compPieces G, Y.card := Finset.sum_congr rfl fun Y hY => by
        rw [← Finset.inter_comm, Finset.inter_univ]

end Valuation

end
end JSP90
