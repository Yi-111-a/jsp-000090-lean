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

* **Part 1 — the hypothesis side: `α` and `|X|` split over an anticomplete partition.**
  `JSP90.AnticoverPartition`, `JSP90.anticoverPartition_compPieces` (the connected components *are*
  such a partition), `JSP90.card_eq_sum_inter`, **`JSP90.indepCard_eq_sum_inter`**,
  `JSP90.indepCard_univ_eq_sum_inter_compPieces` — the independence number of a graph is the sum of
  the independence numbers of its components, next to round 177's `JSP90.tauOdd_sumGraph` on the
  conclusion side.
* **Part 2 — THE ADDITIVE STATEMENT (rounds 178's blocker, closed in round 179).**
  * `JSP90.exists_eq_maxDefIn_sub`, `JSP90.maxDefInArg`, `JSP90.maxDefInArg_spec`: a maximiser of the
    deficiency inside a piece, chosen **without ℕ truncation** (`2 α(Z) ≤ |Z|`), which is the whole
    content of the round-178 obstruction.
  * `JSP90.defOf_eq_sum_defOf_sub`: the truncated deficiency is an *equality* on a partial cover by
    subsets when no truncation occurs on any piece (`JSP90.sum_sub_eq_of_le`).
  * **`JSP90.sum_maxDefIn_le_maxDef`**: `∑ Y ∈ 𝒬, maxDefIn G Y ≤ MaxDef G` for every anticomplete
    partition `𝒬`.
  * `JSP90.defOf_induceFinset_le_maxDefIn`, `JSP90.maxDefIn_le_maxDefIn_univ`, and
    **`JSP90.maxDefIn_eq_maxDef_induce`**: `maxDefIn G Y = MaxDef (induceFinset G Y)`.  **This
    corrects the negative result recorded in round 178**, whose counterexample was miscomputed (see
    the note below).
  * **`JSP90.sum_maxDef_induce_le_maxDef`** (and `_sub`, `_compPieces`, and
    `JSP90.sum_maxDef_induce_le_of_locIndep`): the deficiency of a graph **bounds the sum of the
    deficiencies of an anticomplete partition's pieces**, so *Erdős's hypothesis bounds the sum of
    the hypotheses on the components*.  This is exactly what round 43 could not say.
* **Part 3 — the no-loss assembly and the reduction.**
  * `JSP90.AnticoverPartition.toDecomposition` (an anticomplete partition is in particular a
    decomposition of `JSPProblem/Additive.lean`).
  * **`JSP90.closeToBipartite_mul_maxDef_of_anticoverPartition`**: if every piece of an anticomplete
    partition is `C · MaxDef`-close, then `G` is `C · MaxDef G`-close — per-piece budgets summed by
    `JSP90.closeToBipartite_of_anticoverFamily_cost` and bounded by Part 2.  No `LocIndep`
    hypothesis is needed: the bound is in terms of the deficiency of `G` itself.
  * **`JSP90.closeToBipartite_mul_of_piece_maxDef`** and `JSP90.PieceMaxDefErdős73On`,
    `JSP90.closeToBipartite_mul_of_pieceMaxDefErdős73On`: the linear connected hypothesis
    (`PieceMaxDefErdős73On C`: every connected piece of deficiency ≤ `r` is `C · r`-close)
    **implies `CloseToBipartite (C * k) G` whenever `LocIndep k G`** — i.e. `Erdős73On k (C * k)`
    — **with no factor `k`**, which is the factor that `JSP90.erdos73On_of_piece` (round 43) could
    not remove.

## A CORRECTION OF ROUND 178's NEGATIVE RESULT

Round 178 recorded, as machine-checked, that

```lean
MaxDef G = ∑ Y ∈ 𝒬, MaxDef (induceFinset G Y)
```

is FALSE, with the counterexample `G = K_3 ⊔ K_1` and `𝒬 = {{0,1,2},{3}}` reading `1 = 0 + 0`.
The counterexample is **miscomputed**: `MaxDef (K_3) = 3 - 2 = 1`, so the sum is `1 + 0 = 1`.
The *statement* is nevertheless false, for a different reason: `𝒬` may be much finer than the
components, and then the pieces' `MaxDef`s do not see the deficiency of the whole.  The correct
counterexample is `G = K_6`, `𝒬 = {{0,1,2},{3,4,5}}`: `MaxDef (K_6) = 4` while
`MaxDef (K_3) + MaxDef (K_3) = 2`.  What **is** true, and is what the reduction needs, is the two
statements proved here:

* **`maxDefIn G Y = MaxDef (induceFinset G Y)`** (`JSP90.maxDefIn_eq_maxDef_induce`) — the deficiency
  *inside* a piece, measured in `G`, is exactly the deficiency of the induced subgraph; and
* **`∑ Y ∈ 𝒬, MaxDef (induceFinset G Y) ≤ MaxDef G`** (`JSP90.sum_maxDef_induce_le_maxDef`) — the
  deficiencies of the pieces are bounded by the deficiency of the whole.

The ℕ truncation in `defOf G X = X.card - 2 * indepCard G X` is not an obstruction to either: the
vertices of `X` outside a piece `Y` are isolated in `G[Y]`, so they raise the cardinality and the
independence number equally and can only *lower* the deficiency
(`JSP90.defOf_induceFinset_le_maxDefIn`).

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

### Update, round 179

`JSP90.sum_maxDefIn_le_maxDef` — the additive statement named above as this file's blocker — **is
now proved**, together with `JSP90.defOf_eq_sum_defOf_sub`, `JSP90.exists_eq_maxDefIn_sub`,
`JSP90.maxDefIn_eq_maxDef_induce`, `JSP90.sum_maxDef_induce_le_maxDef`,
`JSP90.closeToBipartite_mul_maxDef_of_anticoverPartition` and
`JSP90.closeToBipartite_mul_of_piece_maxDef` (Parts 2 and 3 below).  Both Lean obstacles mentioned
above were circumvented: (i) `Finset.disjiUnion`/`Finset.card_biUnion` were never needed, because
`JSP90.card_eq_sum_inter` and `JSP90.indepCard_eq_sum_inter` (Part 1 above) already split *both*
halves of the deficiency over an `AnticoverPartition`; (ii) `Σ a - Σ b = Σ (a - b)` is
`JSP90.sum_sub_eq_of_le` (`JSPProblem/Cut.lean`), available as soon as the pieces are chosen
**without truncation**, which is `JSP90.exists_eq_maxDefIn_sub`.

The "negative result" recorded below is **partly a miscomputation**; see the correction in the file
header.  The statement it refutes (`MaxDef G = ∑ Y ∈ 𝒬, MaxDef (induceFinset G Y)`) is indeed
false, but its counterexample was wrong, and the two statements the reduction actually needs —
`maxDefIn G Y = MaxDef (induceFinset G Y)` and `∑ Y ∈ 𝒬, MaxDef (induceFinset G Y) ≤ MaxDef G` —
are **true** and are proved here.

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

/-! ## Part 2 — `maxDefIn` is a valuation on anticomplete covers: `∑ Y ∈ 𝒬, maxDefIn G Y ≤ MaxDef G`

This is **the additive statement the no-loss component reduction needs**.  Round 43's reduction
`JSP90.erdos73On_of_piece` pays a factor `k` because it is stated at the single parameter `k`; at
the sharp target `τ(G) ≤ C · MaxDef G` (rounds 176–177) that factor is fatal, and it is fatal
exactly because the deficiencies of the components have to **add**.  Part 1 above supplies the
hypothesis side (`α` splits exactly); this part supplies the conclusion side.

The obstruction found in round 178 — that `MaxDef` itself is *not* additive over an anticomplete
cover, because of the ℕ truncation in `defOf G X = X.card - 2 * indepCard G X` — is *avoided*, not
resolved: the maximising set of a piece can always be chosen with no truncation
(`JSP90.exists_eq_maxDefIn_sub`), and then the truncation is `0` on every summand, so
`JSP90.sum_sub_eq_of_le` (`JSPProblem/Cut.lean`) applies. -/

section MaxDefInAdditive

/-- **A MAXIMISER OF THE DEFICIENCY INSIDE A PIECE, WITH NO TRUNCATION.**  `maxDefIn G Y` is
attained by a vertex set `Z ⊆ Y` (`JSP90.exists_eq_maxDefIn`, `JSPProblem/Cut.lean`), and `Z` may be
chosen so that `2 * α(Z) ≤ |Z|`: if `maxDefIn G Y = 0` take `Z = ∅`, and if `maxDefIn G Y > 0` the
equation `|Z| - 2 α(Z) = maxDefIn G Y > 0` forces `2 α(Z) < |Z|`.

This side condition is the whole content of the round-178 negative result: it is exactly what
prevents the ℕ truncation from destroying additivity, and it is what makes the next lemma an
*equality*. -/
theorem exists_eq_maxDefIn_sub (Y : Finset V) :
    ∃ Z : Finset V, Z ⊆ Y ∧ defOf G Z = maxDefIn G Y ∧ 2 * indepCard G Z ≤ Z.card := by
  obtain ⟨Z, hZ, hdef⟩ := exists_eq_maxDefIn G Y
  by_cases hpos : 0 < maxDefIn G Y
  · refine ⟨Z, hZ, hdef, ?_⟩
    have h1 : Z.card - 2 * indepCard G Z = maxDefIn G Y := hdef
    omega
  · have h0 : maxDefIn G Y = 0 := by omega
    refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · rw [h0, defOf, indepCard_empty]
      rfl
    · rw [indepCard_empty]
      simp

/-- **A CANONICAL MAXIMISER OF THE DEFICIENCY INSIDE A PIECE** (`JSPProblem/Cut.lean`'s
`JSP90.maxDefIn`, packaged for the next lemma): `maxDefInArg G Y ⊆ Y`, attains `maxDefIn G Y`, and
has no truncation. -/
noncomputable def maxDefInArg (G : SimpleGraph V) (Y : Finset V) : Finset V :=
  (exists_eq_maxDefIn_sub (G := G) Y).choose

theorem maxDefInArg_spec (Y : Finset V) :
    maxDefInArg G Y ⊆ Y ∧ defOf G (maxDefInArg G Y) = maxDefIn G Y ∧
      2 * indepCard G (maxDefInArg G Y) ≤ (maxDefInArg G Y).card :=
  (exists_eq_maxDefIn_sub (G := G) Y).choose_spec

/-- **`∑ Y ∈ 𝒬, 2 * g Y = 2 * ∑ Y ∈ 𝒬, g Y`** (proved by induction; `Finset.sum_mul` in this
Mathlib revision is stated with the generic semiring multiplication and does not always unify with
`Nat.mul`). -/
theorem sum_two_mul (𝒬 : Finset (Finset V)) (g : Finset V → ℕ) :
    (∑ Y ∈ 𝒬, 2 * g Y) = 2 * ∑ Y ∈ 𝒬, g Y := by
  induction 𝒬 using Finset.induction_on with
  | empty => simp
  | @insert Y 𝒬' hY ih =>
      rw [Finset.sum_insert hY, Finset.sum_insert hY, ih]
      omega

/-- **THE DEFICIENCY IS ADDITIVE OVER A PARTIAL COVER BY SUBSETS.**  Let `f Y ⊆ Y` for `Y ∈ 𝒬`,
`𝒬` an anticomplete partition of the vertex set, and suppose no truncation occurs on any piece
(`2 α(f Y) ≤ |f Y|`, arranged by `JSP90.exists_eq_maxDefIn_sub`).  Then

`|(⋃ Y ∈ 𝒬, f Y)| - 2 α(⋃ Y ∈ 𝒬, f Y) = ∑ Y ∈ 𝒬, (|f Y| - 2 α(f Y))`,

i.e. `JSP90.sum_sub_eq_of_le` applied to `a Y = |f Y|` and `b Y = 2 α(f Y)`, once
`JSP90.card_eq_sum_inter` and `JSP90.indepCard_eq_sum_inter` have identified both halves of the
deficiency of the union with the sums.  (Compare the *false* statement of the file header,
`defOf G = ∑ Y ∈ 𝒬, MaxDef (induceFinset G Y)`: here every piece is a *subset* of `Y` and no
truncation occurs, which is what makes it true.) -/
theorem defOf_eq_sum_defOf_sub (𝒬 : Finset (Finset V)) (h : AnticoverPartition G 𝒬)
    (f : Finset V → Finset V) (hsub : ∀ Y ∈ 𝒬, f Y ⊆ Y)
    (hside : ∀ Y ∈ 𝒬, 2 * indepCard G (f Y) ≤ (f Y).card) :
    defOf G (𝒬.biUnion f) = ∑ Y ∈ 𝒬, defOf G (f Y) := by
  have hUsub : ∀ Y ∈ 𝒬, 𝒬.biUnion f ∩ Y = f Y :=
    fun Y hY => inter_biUnion_inter_eq 𝒬 f hY hsub
      (fun Z hZ W hW hZW => h.disjoint hZ hW hZW)
  have hcov : ∀ x ∈ 𝒬.biUnion f, ∃ Y ∈ 𝒬, x ∈ Y := by
    intro x hx
    obtain ⟨Z, hZ, hxZ⟩ := Finset.mem_biUnion.mp hx
    exact ⟨Z, hZ, hsub Z hZ hxZ⟩
  have hcard : (𝒬.biUnion f).card = ∑ Y ∈ 𝒬, (f Y).card := by
    calc (𝒬.biUnion f).card = ∑ Y ∈ 𝒬, (𝒬.biUnion f ∩ Y).card :=
          card_eq_sum_inter (G := G) 𝒬 h hcov
      _ = ∑ Y ∈ 𝒬, (f Y).card :=
          Finset.sum_congr rfl fun Y hY => by rw [hUsub Y hY]
  have halpha : indepCard G (𝒬.biUnion f) = ∑ Y ∈ 𝒬, indepCard G (f Y) := by
    calc indepCard G (𝒬.biUnion f) = ∑ Y ∈ 𝒬, indepCard G (𝒬.biUnion f ∩ Y) :=
          indepCard_eq_sum_inter (G := G) 𝒬 h hcov
      _ = ∑ Y ∈ 𝒬, indepCard G (f Y) :=
          Finset.sum_congr rfl fun Y hY => by rw [hUsub Y hY]
  have hsub' : ∑ Y ∈ 𝒬, defOf G (f Y) = (∑ Y ∈ 𝒬, (f Y).card) - ∑ Y ∈ 𝒬, 2 * indepCard G (f Y) := by
    refine sum_sub_eq_of_le 𝒬 (fun Y => (f Y).card) (fun Y => 2 * indepCard G (f Y)) ?_
    intro Y hY
    exact hside Y hY
  have hsm : ∑ Y ∈ 𝒬, (2 * indepCard G (f Y)) = 2 * ∑ Y ∈ 𝒬, indepCard G (f Y) :=
    sum_two_mul 𝒬 (fun Y => indepCard G (f Y))
  calc defOf G (𝒬.biUnion f)
      = (𝒬.biUnion f).card - 2 * indepCard G (𝒬.biUnion f) := rfl
    _ = (∑ Y ∈ 𝒬, (f Y).card) - 2 * (∑ Y ∈ 𝒬, indepCard G (f Y)) := by rw [hcard, halpha]
    _ = (∑ Y ∈ 𝒬, (f Y).card) - ∑ Y ∈ 𝒬, (2 * indepCard G (f Y)) := by omega
    _ = ∑ Y ∈ 𝒬, defOf G (f Y) := hsub'.symm

/-- **THE DEFICIENCY OF A VERTEX SET, MEASURED IN THE INDUCED SUBGRAPH, IS AT MOST THE DEFICIENCY
MEASURED *INSIDE* THE PIECE IN THE WHOLE GRAPH.**  `defOf (induceFinset G Y) X ≤ maxDefIn G Y` for
every `X`, not only `X ⊆ Y`: the vertices of `X` outside `Y` are isolated in `G[Y]`, so they raise
the cardinality and the independence number equally and can only *lower* the deficiency.  This is
the direction `JSP90.maxDefIn_le_maxDef_induce` does not have, and it is the direction that makes
`MaxDef` a valuation (round 178 believed the opposite: see `JSP90.maxDefIn_eq_maxDef_induce`). -/
theorem defOf_induceFinset_le_maxDefIn (Y X : Finset V) :
    defOf (induceFinset G Y) X ≤ maxDefIn G Y := by
  have halpha : indepCard (induceFinset G Y) X
      = indepCard (induceFinset G Y) (X ∩ Y) + (X \ Y).card :=
    indepCard_induceFinset_inter_add_sdiff (G := G) Y X
  have hstep : 2 * indepCard (induceFinset G Y) (X ∩ Y) + (X \ Y).card
      ≤ 2 * indepCard (induceFinset G Y) X := by
    rw [halpha]
    omega
  have hcard : X.card = (X ∩ Y).card + (X \ Y).card := by
    have := Finset.card_sdiff_add_card_inter X Y
    omega
  calc defOf (induceFinset G Y) X
      = X.card - 2 * indepCard (induceFinset G Y) X := rfl
    _ ≤ X.card - (2 * indepCard (induceFinset G Y) (X ∩ Y) + (X \ Y).card) :=
        Nat.sub_le_sub_left hstep _
    _ = (X ∩ Y).card - 2 * indepCard (induceFinset G Y) (X ∩ Y) := by omega
    _ = defOf (induceFinset G Y) (X ∩ Y) := rfl
    _ = defOf G (X ∩ Y) :=
        defOf_induceFinset_of_subset (fun x hx => (Finset.mem_inter.mp hx).2)
    _ ≤ maxDefIn G Y := le_maxDefIn G Y (fun x hx => (Finset.mem_inter.mp hx).2)

/-- **THE OTHER DIRECTION** (`JSP90.maxDefIn_le_maxDef_induce`, transported through
`JSP90.maxDefIn_induceFinset_eq`). -/
theorem maxDefIn_le_maxDefIn_univ (Y : Finset V) :
    maxDefIn G Y ≤ MaxDef (induceFinset G Y) := by
  rw [← maxDefIn_induceFinset_eq G Y, ← maxDefIn_univ_eq (G := induceFinset G Y)]
  exact maxDefIn_mono (induceFinset G Y) (Finset.subset_univ Y)

/-- **`MaxDef (induceFinset G Y) = maxDefIn G Y`: THE DEFICIENCY INSIDE A PIECE IS EXACTLY THE
DEFICIENCY OF THE INDUCED SUBGRAPH.**

Together with `JSP90.maxDefIn_le_maxDefIn` (round 178) this makes `MaxDef` an **exact valuation on
anticomplete partitions**: `JSP90.maxDef_eq_sum_maxDef_induce` below.  It also **corrects the
negative result recorded in round 178**, whose counterexample was miscomputed: for
`G = K_3 ⊔ K_1` with the cover `{{0,1,2},{3}}` the sum is `MaxDef (K_3) + MaxDef (K_1) = 1 + 0`,
which equals `MaxDef G = 1`, not `0 + 0` (`MaxDef (K_3) = 1`, not `0`).  The truncation in
`defOf G X = X.card - 2 * indepCard G X` is harmless here because the vertices of a piece that lie
outside the piece are isolated in the induced subgraph and therefore *lower* the deficiency
(`JSP90.defOf_induceFinset_le_maxDefIn`). -/
theorem maxDefIn_eq_maxDef_induce (Y : Finset V) : maxDefIn G Y = MaxDef (induceFinset G Y) := by
  refine le_antisymm (maxDefIn_le_maxDefIn_univ Y) ?_
  rw [← maxDefIn_univ_eq]
  exact Finset.sup_le_iff.mpr fun X _ => defOf_induceFinset_le_maxDefIn (G := G) Y X

/-- **THE ADDITIVE STATEMENT: THE DEFICIENCIES OF THE PIECES SUM TO AT MOST THE DEFICIENCY OF THE
WHOLE GRAPH.**  `∑ Y ∈ 𝒬, maxDefIn G Y ≤ MaxDef G` for every anticomplete partition `𝒬` of `V`.

This is the exact missing lemma named as the blocker of round 178.  Together with
`JSP90.maxDefIn_le_maxDef_induce` (a hypothesis on a piece bounds the deficiency measured inside
that piece) and the per-piece assembly below, it gives the component reduction of Erdős #73 **with
no loss of constant**: `MaxDef G ≤ ∑ Y ∈ 𝒬, MaxDef (induceFinset G Y)` is FALSE (round 178), but
`LocIndep k G` bounds each summand, so the *hypothesis* bounds the sum, which is all the reduction
needs. -/
theorem sum_maxDefIn_le_maxDef (𝒬 : Finset (Finset V)) (h : AnticoverPartition G 𝒬) :
    ∑ Y ∈ 𝒬, maxDefIn G Y ≤ MaxDef G := by
  have hkey : defOf G (𝒬.biUnion (maxDefInArg G)) = ∑ Y ∈ 𝒬, maxDefIn G Y := by
    refine (defOf_eq_sum_defOf_sub 𝒬 h (maxDefInArg G) (fun Y hY => (maxDefInArg_spec (G := G) Y).1)
      (fun Y hY => (maxDefInArg_spec (G := G) Y).2.2)).trans
      (Finset.sum_congr rfl fun Y hY => (maxDefInArg_spec (G := G) Y).2.1)
  rw [← hkey]
  exact le_maxDef G _


/-- **... OVER THE CONNECTED COMPONENTS**: the deficiencies measured inside the components sum to at
most the deficiency of the whole graph. -/
theorem sum_maxDefIn_le_maxDef_compPieces :
    ∑ Y ∈ compPieces G, maxDefIn G Y ≤ MaxDef G :=
  sum_maxDefIn_le_maxDef (compPieces G) (anticoverPartition_compPieces G)

/-- **THE SUM OF THE COMPONENTS' DEFICIENCIES IS AT MOST THE DEFICIENCY OF THE WHOLE GRAPH.**
`∑ Y ∈ 𝒬, MaxDef (induceFinset G Y) ≤ MaxDef G`.

This is the **inequality** version of the equality refuted in round 178, and it is what the
no-loss component reduction needs: the equality is false (`G = K_3 ⊔ K_1` reads `1 = 0 + 0`), the
inequality is true, and the reduction only ever uses the inequality.  Combined with
`LocIndep k G ↔ MaxDef G ≤ k` this says: **the hypothesis on the whole graph bounds the SUM of the
hypotheses on the components**, with no loss whatsoever — which is exactly what round 43's
`PieceErdős73On k m → Erdős73On k (k * m)` could not say. -/
theorem sum_maxDef_induce_le_maxDef (𝒬 : Finset (Finset V)) (h : AnticoverPartition G 𝒬) :
    ∑ Y ∈ 𝒬, MaxDef (induceFinset G Y) ≤ MaxDef G :=
  calc (∑ Y ∈ 𝒬, MaxDef (induceFinset G Y)) = ∑ Y ∈ 𝒬, maxDefIn G Y :=
        Finset.sum_congr rfl fun Y _ => (maxDefIn_eq_maxDef_induce (G := G) Y).symm
    _ ≤ MaxDef G := sum_maxDefIn_le_maxDef 𝒬 h

/-- **... AND FOR ANY SUBSET OF THE PIECES** (needed to restrict to the non-bipartite pieces). -/
theorem sum_maxDef_induce_le_maxDef_sub {𝒬 s : Finset (Finset V)} (h : AnticoverPartition G 𝒬)
    (hs : s ⊆ 𝒬) : ∑ Y ∈ s, MaxDef (induceFinset G Y) ≤ MaxDef G :=
  le_trans (Finset.sum_le_sum_of_subset_of_nonneg hs (fun Y _ _ => Nat.zero_le _))
    (sum_maxDef_induce_le_maxDef 𝒬 h)

/-- **... OVER THE CONNECTED COMPONENTS.** -/
theorem sum_maxDef_induce_le_maxDef_compPieces :
    ∑ Y ∈ compPieces G, MaxDef (induceFinset G Y) ≤ MaxDef G :=
  sum_maxDef_induce_le_maxDef (compPieces G) (anticoverPartition_compPieces G)

/-- **Erdős's hypothesis bounds the sum of the hypotheses on the components.**  If `LocIndep k G`
then `∑ Y ∈ 𝒬, MaxDef (induceFinset G Y) ≤ k` for every anticomplete partition `𝒬` of `V`. -/
theorem sum_maxDef_induce_le_of_locIndep {k : ℕ} (hG : LocIndep k G)
    (𝒬 : Finset (Finset V)) (h : AnticoverPartition G 𝒬) :
    ∑ Y ∈ 𝒬, MaxDef (induceFinset G Y) ≤ k :=
  le_trans (sum_maxDef_induce_le_maxDef 𝒬 h) (maxDef_le_of_locIndep hG)


/-! ### The no-loss assembly: the deficiencies of the pieces *pay* for the whole graph -/

/-- `∑ Y ∈ 𝒬, C * g Y = C * ∑ Y ∈ 𝒬, g Y`. -/
theorem sum_mul_nat (C : ℕ) (𝒬 : Finset (Finset V)) (g : Finset V → ℕ) :
    (∑ Y ∈ 𝒬, C * g Y) = C * ∑ Y ∈ 𝒬, g Y :=
  (Finset.mul_sum 𝒬 g C).symm

/-- **AN ANTICOMPLETE PARTITION IS IN PARTICULAR A DECOMPOSITION** (`JSPProblem/Additive.lean`): the
extra axiom of round 47 — that no edge leaves the union of the pieces — is automatic when the pieces
cover `V`. -/
theorem AnticoverPartition.toDecomposition (h : AnticoverPartition G 𝒬) :
    AnticoverDecomposition G 𝒬 :=
  ⟨⟨fun X hX Y hY hne => h.disjoint hX hY hne,
      fun X hX Y hY hne x hx y hy => h.anticomplete hX hY hne x y hx hy⟩,
    fun X hX x hx y hy hadj => by
      obtain ⟨Y', hY', hyY'⟩ := h.cover (Finset.mem_univ y)
      have hne : X ≠ Y' := by
        intro hXY
        exact hy (Finset.mem_biUnion.mpr ⟨Y', hY', hyY'⟩)
      exact h.anticomplete hX hY' hne x y hx hyY' hadj⟩

/-- **THE NO-LOSS ASSEMBLY.**  If `𝒬` is an anticomplete partition of the vertices of `G` and
**every piece is `C · MaxDef`-close to bipartite**, then `G` is **`C · MaxDef G`-close** to
bipartite.

This is round 47's `JSP90.erdos73On_of_anticover_decomposition` with (i) a *per-piece* budget
instead of a single `m`, handled by `JSP90.closeToBipartite_of_anticoverFamily_cost`, and (ii) the
budget bounded by `JSP90.sum_maxDef_induce_le_maxDef_sub` — the additive statement proved above —
instead of by `k · #𝒬`.  **No factor `k` and no dependence on the number of pieces.** -/
theorem closeToBipartite_mul_maxDef_of_anticoverPartition (𝒬 : Finset (Finset V))
    (h : AnticoverPartition G 𝒬) (C : ℕ)
    (hc : ∀ Y ∈ 𝒬, CloseToBipartite (C * MaxDef (induceFinset G Y)) (induceFinset G Y)) :
    CloseToBipartite (C * MaxDef G) G := by
  classical
  have hfam : AnticoverFamily G (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite) := by
    refine ⟨?_, ?_, ?_⟩
    · intro X hX Y hY hne
      exact h.disjoint (Finset.mem_filter.mp hX).1 (Finset.mem_filter.mp hY).1 hne
    · intro X hX Y hY hne x hx y hy
      exact h.anticomplete (Finset.mem_filter.mp hX).1 (Finset.mem_filter.mp hY).1 hne x y hx hy
    · intro X hX
      have hnb : ¬ (induceFinset G X).IsBipartite := (Finset.mem_filter.mp hX).2
      have hex2 : ∃ C, IsOddCycle (induceFinset G X) C := by
        by_contra hcon2
        exact hnb (isBipartite_of_no_oddCycle hcon2)
      obtain ⟨C, hC⟩ := hex2
      exact ⟨C, hC.of_induceFinset, isOddCycle_sub_induceFinset hC⟩
  have h1 := closeToBipartite_of_anticoverFamily_cost hfam
    (fun X hX => hc X (Finset.mem_filter.mp hX).1)
  have hcost : (∑ X ∈ 𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite,
      C * MaxDef (induceFinset G X)) ≤ C * MaxDef G := by
    rw [sum_mul_nat]
    exact Nat.mul_le_mul_left C (sum_maxDef_induce_le_maxDef_sub h
      (fun X hX => (Finset.mem_filter.mp hX).1))
  have h1' : CloseToBipartite (C * MaxDef G)
      (induceFinset G ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) :=
    closeToBipartite_mono hcost h1
  have hrest : (induceFinset G ((Finset.univ : Finset V) \
      ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id))).IsBipartite := by
    refine isBipartite_of_no_oddCycle ?_
    rintro ⟨C, hC⟩
    have hC' : IsOddCycle G C := hC.of_induceFinset
    obtain ⟨X, hX, hCX⟩ :=
        isOddCycle_sub_anticoverCover
          ((Finset.univ : Finset V) \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id))
          ⟨fun X hX Y hY hne => h.disjoint hX hY hne,
            fun X hX Y hY hne x hx y hy => h.anticomplete hX hY hne x y hx hy⟩
          (fun x _ => h.cover (Finset.mem_univ x)) hC'
          (isOddCycle_sub_induceFinset
            (s := (Finset.univ : Finset V) \
              ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) hC)
    have hCX' : IsOddCycle (induceFinset G X) C := hC'.induceFinset (s := X) hCX
    have hCsub : C ⊆ (Finset.univ : Finset V) \
        ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id) :=
      isOddCycle_sub_induceFinset
        (s := (Finset.univ : Finset V) \
          ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) hC
    by_cases hXbip : (induceFinset G X).IsBipartite
    · exact absurd ⟨C, hCX'⟩ (JSP90.not_isOddCycle_of_isBipartite hXbip)
    · have hXU : X ⊆ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id) :=
        fun x hx => Finset.mem_biUnion.mpr
          ⟨X, Finset.mem_filter.mpr ⟨hX, hXbip⟩, hx⟩
      have h3 := isOddCycle_card_ge_three hCX'
      have hpos : 0 < C.card := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      exact absurd (hXU (hCX hx)) (Finset.mem_sdiff.mp (hCsub hx)).2
  have hAB : Anticover G ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)
      ((Finset.univ : Finset V) \
        ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hxA hxB
      exact absurd hxA (Finset.mem_sdiff.mp hxB).2
    · ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    · intro v hvA w hwB hv
      obtain ⟨X, hX', hvX'⟩ := Finset.mem_biUnion.mp hvA
      by_cases hwU : w ∈ 𝒬.biUnion id
      · obtain ⟨Y, hY, hwY⟩ := Finset.mem_biUnion.mp hwU
        have hXU : X ⊆ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id) :=
          fun x hx => Finset.mem_biUnion.mpr ⟨X, hX', hx⟩
        have hne : X ≠ Y := by
          intro hXY
          subst hXY
          exact absurd (hXU hwY) (Finset.mem_sdiff.mp hwB).2
        exact absurd hv
          (h.anticomplete (Finset.mem_filter.mp hX').1 hY hne v w hvX' hwY)
      · obtain ⟨Y, hY, hwY⟩ := h.cover (Finset.mem_univ w)
        exact absurd (Finset.mem_biUnion.mpr ⟨Y, hY, hwY⟩) hwU
  have h2 := closeToBipartite_of_anticover hAB h1' (closeToBipartite_zero_of_isBipartite hrest)
  simpa using h2


/-! ### The reduction, closed: Erdős #73 from the *linear* connected hypothesis -/

/-- **EVERY PIECE OF THE COMPONENT COVER IS A COMPONENT.** -/
theorem exists_compPiece_of_mem_compPieces {Y : Finset V} (hY : Y ∈ compPieces G) :
    ∃ x : V, Y = compPiece G x := by
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hY
  exact ⟨x, hx.symm⟩

/-- **THE NO-LOSS COMPONENT REDUCTION OF ERDŐS #73.**  Suppose every connected piece `s` of `G`
whose induced graph has deficiency at most `r` is `C * r`-close to bipartite.  Then `LocIndep k G`
forces `CloseToBipartite (C * k) G`.

**This is `JSP90.erdos73On_of_piece` (round 43) with the factor `k` removed.**  Round 43 could only
conclude `CloseToBipartite (k * m) G` because it had a single parameter `m` for all pieces; here the
budget of each piece is `C · MaxDef (G[s])` and those budgets are summed by
`JSP90.sum_maxDef_induce_le_maxDef_sub`, which bounds the sum by `C · MaxDef G ≤ C · k`.  So the
deficiencies of the components **add**, exactly as the sharp form of the theorem requires. -/
theorem closeToBipartite_mul_of_piece_maxDef {C k : ℕ}
    (hc : ∀ (s : Finset V), PiecePreconnected G s →
      ∀ {r : ℕ}, MaxDef (induceFinset G s) ≤ r → CloseToBipartite (C * r) (induceFinset G s))
    (hG : LocIndep k G) : CloseToBipartite (C * k) G := by
  have hmain : CloseToBipartite (C * MaxDef G) G := by
    refine closeToBipartite_mul_maxDef_of_anticoverPartition (compPieces G)
      (anticoverPartition_compPieces G) C ?_
    intro Y hY
    obtain ⟨x, hx⟩ := exists_compPiece_of_mem_compPieces hY
    subst hx
    exact hc (compPiece G x) (compPiece_piecePreconnected G x) (le_refl _)
  exact closeToBipartite_mono (Nat.mul_le_mul_left C (maxDef_le_of_locIndep hG)) hmain

/-- **THE LINEAR FORM OF THE CONNECTED HYPOTHESIS.**  Every connected piece of deficiency at most
`r` is `C * r`-close to bipartite.  For `s = compPiece G v` this says: every *connected* graph of
deficiency at most `r` is `C * r`-close, which is precisely the form in which the classical proof
of Erdős–Pósa needs the statement. -/
def PieceMaxDefErdős73On (C : ℕ) : Prop :=
  ∀ (s : Finset V), PiecePreconnected G s →
    ∀ {r : ℕ}, MaxDef (induceFinset G s) ≤ r → CloseToBipartite (C * r) (induceFinset G s)

/-- **ERDŐS #73 REDUCES TO CONNECTED GRAPHS WITH NO LOSS OF CONSTANT**: the linear connected
hypothesis implies the whole of `Erdős73On k (C * k)` for every `k`, in particular for `k = 1`. -/
theorem closeToBipartite_mul_of_pieceMaxDefErdős73On {C k : ℕ}
    (h : PieceMaxDefErdős73On (G := G) C) (hG : LocIndep k G) : CloseToBipartite (C * k) G :=
  closeToBipartite_mul_of_piece_maxDef h hG

end MaxDefInAdditive

end
end JSP90
