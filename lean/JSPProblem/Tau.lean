import JSPProblem.Exact
import JSPProblem.Piece
import JSPProblem.Petersen

/-!
# JSP-000090, round 140 — `JSPProblem/Tau.lean`: **the odd cycle transversal number `τ_odd`, its
# exact additivity, and the budget-split form of Erdős #73**

Attack family 69.  Every constant in this development so far has been stated as
`CloseToBipartite m G`, i.e. as a *one-sided* statement about a *number* `m`.  The object that the
conclusion of Erdős #73 actually talks about is the **odd cycle transversal number**

```lean
JSP90.tauOdd G = min { |Z| : Z meets every odd cycle of G }
```

which this file introduces.  Three things become available for the first time.

## Part 1 — `τ_odd` exists, and the conclusion of Erdős #73 *is* a bound on it

`JSP90.closeToBipartite_iff_tauOdd_le (m) : CloseToBipartite m G ↔ tauOdd G ≤ m`.  So the whole
question "is `G` the union of a bipartite graph and `f(k)` vertices?" is the question "is
`τ_odd G ≤ f(k)`?", and `JSP90.maxDef_le_tauOdd` (`MaxDef G ≤ τ_odd G`) puts Erdős's hypothesis
`LocIndep k G` on the other side of it.  Nothing below assumes Erdős #73.

## Part 2 — **`τ_odd` is EXACTLY additive over an anticomplete cover**

```lean
JSP90.tauOdd_anticover_add : tauOdd G = ∑ X ∈ 𝒬, tauOdd (induceFinset G X)
```

This is the exactness statement that `JSPProblem/Exact.lean` (round 105) could only get in the `≤`
direction (`closeToBipartite_iff_cost_cover`; the header of `JSPProblem/Deficiency.lean` says "the
converse is not proved here"): there the pieces *pay jointly*, i.e. one only knows `∑ c X ≤ m`.
Here the two sides are **equal as numbers**, so a cover costs exactly what its pieces cost.  The two
halves are two different arguments: the transversal side glues minimum transversals of the pieces
(`hitsOddCycles_of_anticoverCover`, `card_biUnion_eq_sum`), and the counting side restricts a
minimum transversal of `G` to each piece and adds, using disjointness (`card_sum_inter_le`).

## Part 3 — **the exact accounting at a 1-cut and at a 2-cut**

* `JSP90.tauOdd_le_sum_onePieces` — **at a 1-cut, `τ_odd` adds over the PIECES with NO `+1`, each
  piece charged its own minimum** (`∑ tauOdd (T_i ∪ {v})`), against the uniform constant `m * t` of
  `JSPProblem/Piece.lean`;
* `JSP90.tauOdd_ge_sum_parts` — **and it dominates the sum over the PARTS**
  (`∑ tauOdd (T_i) ≤ τ_odd G`);
* `JSP90.tauOdd_onePiece_le` — a piece costs at most one more than its part, so
  `JSP90.tauOdd_oneSplit_interval` says **`τ_odd` is within the number of parts of the sum over the
  parts**;
* `JSP90.tauOdd_eq_onePiece_of_bipartite_pieces` — round 110's one-sided 1-cut reduction as an
  equality of numbers: `τ_odd G = tauOdd (T_{i₀} ∪ {v})` when that piece is the only non-bipartite
  one;
* `JSP90.tauOdd_le_add_two_of_vertexSplit` — at a **2-cut** the error is `+2`
  (`τ_odd G ≤ 2 + ∑ i, tauOdd (T_i ∪ {a, b})`), the sharp form of the `2 + m * t` of
  `JSPProblem/CutVertex.lean`.

## Part 4 — **the budget-split form of Erdős #73 (new instances)**

`JSPProblem/Exact.lean` proves `erdos73On_of_pieceMaxDef`: on a cover by pieces which are
MaxDef-close, `LocIndep k G` gives `CloseToBipartite k G`.  The general forms are

```lean
JSP90.erdos73On_of_anticoverCover_of_pieceDeficit : each piece satisfies the conclusion at every
  parameter up to ITS OWN deficiency, with its own constant ⟹ G does, with the constants added up
JSP90.erdos73On_of_anticoverCover_of_piecePacking : each piece satisfies the conclusion from its own
  packing bound ⟹ G does
```

the second being the formal statement of "Erdős–Pósa splits over an anticomplete cover".  Their
corollaries: `…_of_maxDef` (round 105 recovered), `…_of_bounded_pieceGirth` (odd girth `≤ ℓ X`
**per piece**, constants `ℓ X * MaxDef (G[X])`), `…_of_bounded_girth` (a uniform `ℓ` again gives the
classical `ℓ * k`), and `JSP90.closeToBipartite_of_anticover_two_of_maxDef` — **the two budgets split
as well**: `MaxDef G[A] ≤ k₁`, `MaxDef G[B] ≤ k₂` and Erdős #73 at `k₁` and at `k₂` give Erdős #73
at `k₁ + k₂` with constant `m₁ + m₂`.

## Part 5 — sharpness, and a machine-checked obstruction

* `JSP90.tauOdd_p9Family : tauOdd (p9Family k) = 2 * k` — round 76's `f(k) ≥ 2 k` as a number;
* `JSP90.tauOdd_wf : tauOdd wf = 1` and **`JSP90.not_tauOdd_additive_oneSplit`** — **the exactness
  of Part 2 does NOT extend to cuts**: on the windmill (two triangles meeting in one vertex, the
  `wf_oneSplit` of `JSPProblem/Piece.lean`) `τ_odd = 1` while the two non-bipartite pieces cost `1`
  each.  The pieces are the object one must use at a cut, and this is why the `+2` of the 2-cut
  statement cannot be removed.

## Toolchain notes (they cost most of the round)

* `Nat.find` searches over `ℕ`, so `tauOdd` has to be defined on a predicate of *cardinalities*:
  `Nat.find (p := fun n => ∃ Z, HitsOddCycles G Z ∧ Z.card ≤ n)`.  The `DecidablePred` instance for
  that predicate is needed not only by the definition but by `Nat.find_spec` and `Nat.find_min'` in
  every later lemma, so it must be a `local instance`, and `p` must be given **explicitly** — with
  only the expected type `ℕ` there is nothing to determine `p` from and instance resolution fails
  with "`Fintype ?m` is stuck".
* An `∃` in `Prop` is squashed: `.1`/`.2` are **not** available on `tauOdd_spec`'s statement.  The
  minimum transversal is therefore packaged as a `Subtype` (`tauOddMin`), and every `obtain` of an
  `∃` must stay inside a proof (projections are fine *there*).
* The transversals `∅` and `{v}` are useless as *witnesses*: `HitsOddCycles G ∅` is false.  The
  witness for `tauOdd_zero_iff`'s backward direction is `(Finset.univ : Finset V)`, and for
  `τ ≥ 1` one uses `tauOdd_zero_iff` plus a non-bipartiteness certificate (never an explicit
  `HitsOddCycles G ∅`).
* `Finset.nonempty_iff_ne_empty` at this revision is `s ≠ ∅ ↔ s.Nonempty`, so **`.mpr`** turns a
  `≠ ∅` proof into a `Nonempty`; `.mp` goes the other way.  `Finset.Subset.card_le_card` is a
  one-way theorem (`s ⊆ t → s.card ≤ t.card`); the converse is
  `Finset.eq_of_subset_of_card_le : s ⊆ t → t.card ≤ s.card → s = t`.
* `Finset.eq_of_subset_of_card_le hsub hle` returns `C = S` for `hsub : C ⊆ S` and
  `hle : S.card ≤ C.card` (the "card inequality over the *second* set"), i.e. it does **not** need a
  `.symm`.
* `rw [h]` rewrites the hypothesis, not the goal: to use `h : A = B` in a goal about `B`, write
  `rw [h] at goal` or `rw [← h]` on a goal mentioning `B`.
* `Finset.mem_insert` is an `Iff` (`a ∈ insert b s ↔ a = b ∨ a ∈ s`) but at this revision
  `Finset.mem_singleton` is `b ∈ {a} ↔ b = a` *and* `Finset.card_union_le` takes the second finset
  explicitly (`Finset.card_union_le s t : (s ∪ t).card ≤ s.card + t.card`).
* **The `DecidableEq` trap (the one that blocked a whole route).**  The `Finset`s of
  `JSPProblem/Windmill.lean` and `JSPProblem/Piece.lean` were elaborated with Mathlib's computable
  `instDecidableEqFin`, while a file-local classical `DecidableEq V` wins for *most* literals but
  not all, so `insert 0 (wfPiece 0)` and `({0, 1, 2} : Finset (Fin 6))` can be two syntactically
  different finsets of the same vertex set.  Consequences: (a) an equality between the two is
  provable (`rw [insert_0_wfPiece_0]` closes it), but (b) passing a term whose *type* mentions one
  of them where the other is expected fails with "synthesized instance is not definitionally equal
  to expression inferred by typing rules"; (c) `SimpleGraph.IsClique` is stated on a **`Set`**, so
  even the triangle-of-the-windmill clique `wf.IsClique ({0,1,2} : Finset (Fin 6))` is out of reach
  this way.  The work-around used here is the *transversal* route instead of the clique route: an
  odd cycle of a three-vertex piece is the whole piece
  (`Finset.eq_of_subset_of_card_le` + `simp`), so `{1}` is a transversal of the first piece and
  `{3}` of the second.

## What is *not* proved

`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) and hence `jsp_000090_main`: this file
gives exact arithmetic for `τ_odd`, not a bound on it in terms of `k`.  `jsp_000090_main` is
deliberately not declared, so the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 400000

local instance tauDecidableEq : DecidableEq V := Classical.decEq V


/-! ## Part 1 — the odd cycle transversal number -/

section TauOdd

/-- **A transversal always exists**: the whole vertex set meets every odd cycle. -/
theorem exists_hitsOddCycles : ∃ Z : Finset V, HitsOddCycles G Z :=
  ⟨(Finset.univ : Finset V), by
    intro C hC
    rw [Finset.inter_univ]
    exact (hC.nonempty).ne_empty⟩

/-- **THE LEAST CARDINALITY OF AN ODD CYCLE TRANSVERSAL EXISTS.** -/
theorem exists_hitsOddCycles_card_le :
    ∃ n : ℕ, ∃ Z : Finset V, HitsOddCycles G Z ∧ Z.card ≤ n :=
  ⟨Fintype.card V, (Finset.univ : Finset V), by
    intro C hC
    rw [Finset.inter_univ]
    exact (hC.nonempty).ne_empty, (le_refl _)⟩

/-- The decidability that `Nat.find` and its lemmas need for the predicate of `tauOdd`: the
existential runs over `Finset V`, which is a `Fintype`, and the odd-cycle condition is classical. -/
local instance tauOddDecidable (G : SimpleGraph V) :
    DecidablePred (fun n : ℕ => ∃ Z : Finset V, HitsOddCycles G Z ∧ Z.card ≤ n) :=
  fun _ => Classical.propDecidable _

/-- **`tauOdd G` is the least cardinality of a set meeting every odd cycle of `G`.**

The minimum is taken over the cardinalities, and `Nat.find` produces it because a transversal
exists (`JSP90.exists_hitsOddCycles_card_le`).  Nothing else about `G` is used: no hypothesis, no
`LocIndep`, no packing bound. -/
noncomputable def tauOdd (G : SimpleGraph V) : ℕ :=
  Nat.find (p := fun n : ℕ => ∃ Z : Finset V, HitsOddCycles G Z ∧ Z.card ≤ n)
    (exists_hitsOddCycles_card_le (G := G))

/-- **A MINIMUM TRANSVERSAL EXISTS AND HAS CARDINALITY `tauOdd G`.** -/
theorem tauOdd_spec : ∃ Z : Finset V, HitsOddCycles G Z ∧ Z.card = tauOdd G := by
  obtain ⟨Z, hZ, hle⟩ := Nat.find_spec (exists_hitsOddCycles_card_le (G := G))
  have hmin : tauOdd G ≤ Z.card :=
    Nat.find_min' (exists_hitsOddCycles_card_le (G := G)) (m := Z.card) ⟨Z, hZ, le_refl _⟩
  exact ⟨Z, hZ, Nat.le_antisymm hle hmin⟩

/-- **EVERY TRANSVERSAL IS AT LEAST `tauOdd G`.**  This is the definition of the minimum. -/
theorem tauOdd_le {Z : Finset V} (hZ : HitsOddCycles G Z) : tauOdd G ≤ Z.card :=
  Nat.find_min' (exists_hitsOddCycles_card_le (G := G)) (m := Z.card) ⟨Z, hZ, le_refl _⟩

/-- **THE MINIMUM TRANSVERSAL, PACKAGED AS A SUBTYPE** so that it can be projected on: an `∃` in
`Prop` is squashed, so `.1`/`.2` are not available on `JSP90.tauOdd_spec`.  Everything below glues
these. -/
noncomputable def tauOddMin (G : SimpleGraph V) :
    {Z : Finset V // HitsOddCycles G Z ∧ Z.card = tauOdd G} :=
  ⟨(tauOdd_spec (G := G)).choose, (tauOdd_spec (G := G)).choose_spec.1,
    (tauOdd_spec (G := G)).choose_spec.2⟩

/-- A minimum transversal hits every odd cycle. -/
theorem hitsOddCycles_of_tauOddMin (G : SimpleGraph V) :
    HitsOddCycles G (tauOddMin G).1 :=
  (tauOddMin G).2.1

/-- A minimum transversal has cardinality `tauOdd G`. -/
theorem card_tauOddMin (G : SimpleGraph V) : (tauOddMin G).1.card = tauOdd G :=
  (tauOddMin G).2.2

/-- **THE CONCLUSION OF ERDŐS #73 IS A BOUND ON `tauOdd`, AND NOTHING ELSE.**  `CloseToBipartite m G`
holds exactly when the least odd cycle transversal of `G` has at most `m` vertices. -/
theorem closeToBipartite_iff_tauOdd_le {m : ℕ} :
    CloseToBipartite m G ↔ tauOdd G ≤ m := by
  constructor
  · rintro ⟨X, hX, hhit⟩
    exact le_trans (tauOdd_le (hitsOddCycles_of_isBipartite_delete hhit)) hX
  · intro h
    obtain ⟨Z, hZ, hcard⟩ := tauOdd_spec (G := G)
    exact (closeToBipartite_iff_hitsOddCycles (V := V) (G := G) (m := m)).mpr
      ⟨Z, le_trans hcard.le h, hZ⟩

/-- **THE HYPOTHESIS OF ERDŐS #73 IS A LOWER BOUND ON `tauOdd`.**  `MaxDef G ≤ tauOdd G`, the
numerical form of `JSPProblem/Deficiency.lean`'s `maxDef_le_closeToBipartite`. -/
theorem maxDef_le_tauOdd : MaxDef G ≤ tauOdd G := by
  have h1 : CloseToBipartite (tauOdd G) G :=
    (closeToBipartite_iff_tauOdd_le (G := G) (m := tauOdd G)).mpr (Nat.le_refl _)
  exact maxDef_le_closeToBipartite h1

/-- **A GRAPH IS BIPARTITE EXACTLY WHEN `tauOdd` IS ZERO.**  The odd-cycle characterisation of
bipartiteness in the language of the number. -/
theorem tauOdd_zero_iff : tauOdd G = 0 ↔ G.IsBipartite := by
  constructor
  · intro h
    have hn : ¬ ∃ C : Finset V, IsOddCycle G C := by
      rintro ⟨C, hC⟩
      obtain ⟨Z, hZ, hcard⟩ := tauOdd_spec (G := G)
      have hZ0 : Z = ∅ := Finset.card_eq_zero.mp (hcard.trans h)
      have hhit : HitsOddCycles G ∅ := by
        rw [hZ0] at hZ
        intro D hD
        exact absurd (Finset.inter_empty D) (hZ D hD)
      exact absurd (Finset.inter_empty C) (hhit C hC)
    exact isBipartite_of_no_oddCycle hn
  · intro h
    have h1 : CloseToBipartite 0 G := ⟨∅, by simp, isBipartite_delete h⟩
    have h2 : tauOdd G ≤ 0 := by
      rw [closeToBipartite_iff_tauOdd_le] at h1
      exact h1
    omega

/-- **`tauOdd` OF A BIPARTITE GRAPH IS ZERO**, the form used below. -/
theorem tauOdd_eq_zero_of_isBipartite (h : G.IsBipartite) : tauOdd G = 0 :=
  (tauOdd_zero_iff (G := G)).mpr h

/-- **MONOTONICITY: A TRANSVERSAL OF `G` IS A TRANSVERSAL OF EVERY INDUCED SUBGRAPH, SO `tauOdd`
INCREASES WHEN VERTICES ARE ADDED.** -/
theorem tauOdd_induceFinset_le (X : Finset V) :
    tauOdd (induceFinset G X) ≤ tauOdd G := by
  obtain ⟨Z, hZ, hmin⟩ := tauOdd_spec (G := G)
  exact le_trans (tauOdd_le (Z := Z) (fun C hC => hZ C (IsOddCycle.of_induceFinset hC))) hmin.le

end TauOdd

/-! ## Part 2 — exact additivity over an anticomplete cover -/

section Cover

/-- **A SET MEETING EVERY ODD CYCLE OF EVERY PIECE MEETS EVERY ODD CYCLE OF `G`.** -/
theorem hitsOddCycles_of_anticoverCover {𝒬 : Finset (Finset V)}
    (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X)
    {Z : Finset V} (hZ : ∀ X ∈ 𝒬, HitsOddCycles (induceFinset G X) Z) : HitsOddCycles G Z := by
  intro C hC
  obtain ⟨X, hX, hCX⟩ :=
    isOddCycle_sub_anticoverCover (s := (Finset.univ : Finset V)) h hcov hC (Finset.subset_univ C)
  have hCX' : IsOddCycle (induceFinset G X) C := IsOddCycle.induceFinset hC hCX
  exact hZ X hX C hCX'

/-- **`tauOdd` IS EXACTLY ADDITIVE OVER AN ANTICOMPLETE COVER.**

The statement round 105 (`JSPProblem/Exact.lean` `closeToBipartite_iff_cost_cover`) could only make
is: the pieces pay *jointly*, `∑ c X ≤ m`.  Here the two numbers are **equal**: the transversal
number of `G` is the *sum* of the transversal numbers of the pieces. -/
theorem tauOdd_anticover_add {𝒬 : Finset (Finset V)} (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X) :
    tauOdd G = ∑ X ∈ 𝒬, tauOdd (induceFinset G X) := by
  classical
  -- the transversal half: glue minimum transversals of the pieces, restricted to the pieces
  have hle : tauOdd G ≤ ∑ X ∈ 𝒬, tauOdd (induceFinset G X) := by
    let W : Finset V → Finset V :=
      fun X => if hX : X ∈ 𝒬 then (tauOddMin (G := induceFinset G X)).1 else ∅
    have hWcard : ∀ X ∈ 𝒬, (W X).card = tauOdd (induceFinset G X) := by
      intro X hX
      have hW : W X = (tauOddMin (G := induceFinset G X)).1 := by
        show (if hX : X ∈ 𝒬 then (tauOddMin (G := induceFinset G X)).1 else ∅) = _
        simp [hX]
      rw [hW]
      exact card_tauOddMin (G := induceFinset G X)
    have hWhits : ∀ X ∈ 𝒬, HitsOddCycles (induceFinset G X) (W X) := by
      intro X hX
      have hW : W X = (tauOddMin (G := induceFinset G X)).1 := by
        show (if hX : X ∈ 𝒬 then (tauOddMin (G := induceFinset G X)).1 else ∅) = _
        simp [hX]
      rw [hW]
      exact hitsOddCycles_of_tauOddMin (G := induceFinset G X)
    have key2 : ∃ Z : Finset V, HitsOddCycles G Z ∧
        Z.card ≤ ∑ X ∈ 𝒬, tauOdd (induceFinset G X) := by
      refine ⟨𝒬.biUnion W, ?_, ?_⟩
      · refine hitsOddCycles_of_anticoverCover h hcov ?_
        intro Y hY C hC
        have hne : C ∩ W Y ≠ ∅ := hWhits Y hY C hC
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hxm := Finset.mem_inter.mp hx
        have hne' : (C ∩ (𝒬.biUnion W)).Nonempty :=
          ⟨x, Finset.mem_inter.mpr ⟨hxm.1, Finset.mem_biUnion.mpr ⟨Y, hY, hxm.2⟩⟩⟩
        exact ne_empty_of_nonempty hne'
      · have h1 : (𝒬.biUnion W).card ≤ ∑ X ∈ 𝒬, (W X).card := Finset.card_biUnion_le
        have h3 : (∑ X ∈ 𝒬, (W X).card) = ∑ X ∈ 𝒬, tauOdd (induceFinset G X) :=
          Finset.sum_congr rfl fun X hX => hWcard X hX
        omega
    obtain ⟨Z, hZ, hle'⟩ := key2
    exact le_trans (tauOdd_le hZ) hle'
  -- the counting half: restrict a minimum transversal of `G` to each piece and add
  have hge : (∑ X ∈ 𝒬, tauOdd (induceFinset G X)) ≤ tauOdd G := by
    obtain ⟨W, hW, hmin⟩ := tauOdd_spec (G := G)
    have h1 : (∑ X ∈ 𝒬, tauOdd (induceFinset G X)) ≤ ∑ X ∈ 𝒬, (W ∩ X).card := by
      refine Finset.sum_le_sum fun X hX => ?_
      refine tauOdd_le (Z := W ∩ X) ?_
      intro C hC
      have hne : C ∩ W ≠ ∅ := hW C (IsOddCycle.of_induceFinset hC)
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hxm := Finset.mem_inter.mp hx
      have hne' : (C ∩ (W ∩ X)).Nonempty :=
        ⟨x, Finset.mem_inter.mpr
          ⟨hxm.1, Finset.mem_inter.mpr ⟨hxm.2, isOddCycle_sub_induceFinset hC hxm.1⟩⟩⟩
      exact ne_empty_of_nonempty hne'
    have h2 := card_sum_inter_le (𝒬 := 𝒬) (Z := W) h.1
    omega
  exact le_antisymm hle hge

/-- **TWO ANTICOMPLETE COVERS OF THE SAME VERTICES GIVE THE SAME NUMBER.** -/
theorem tauOdd_eq_of_two_covers {𝒬 𝒬' : Finset (Finset V)} (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X)
    (h' : AnticoverCoverFamily G 𝒬')
    (hcov' : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬', x ∈ X) :
    (∑ X ∈ 𝒬, tauOdd (induceFinset G X)) = ∑ X ∈ 𝒬', tauOdd (induceFinset G X) :=
  (tauOdd_anticover_add h hcov).symm.trans (tauOdd_anticover_add h' hcov')

/-- **THE TWO-PIECE FORM: `tauOdd` ADDS EXACTLY OVER AN ANTICOMPLETE SPLIT.**  `V = A ⊔ B` with no
edge between the two sides, i.e. the shape of the connected components of a graph. -/
theorem tauOdd_induceFinset_add {A B : Finset V} (hAB : Anticover G A B) :
    tauOdd G = tauOdd (induceFinset G A) + tauOdd (induceFinset G B) := by
  have hAB' : A ∪ B = (Finset.univ : Finset V) := hAB.2.1
  have hdisAB : ∀ x : V, x ∈ A → x ∉ B := hAB.1
  have hantiAB : ∀ v ∈ A, ∀ w ∈ B, ¬ G.Adj v w := hAB.2.2
  have hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) →
      ∃ Y ∈ ({A, B} : Finset (Finset V)), x ∈ Y := by
    intro x hx
    rw [← hAB'] at hx
    rcases Finset.mem_union.mp hx with hA | hB
    · exact ⟨A, by simp, hA⟩
    · exact ⟨B, by simp, hB⟩
  have mem2 : ∀ (X : Finset V), X ∈ ({A, B} : Finset (Finset V)) → X = A ∨ X = B := by
    intro X hX
    rcases Finset.mem_insert.mp hX with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (by simpa using h2)
  have hfam : AnticoverCoverFamily G ({A, B} : Finset (Finset V)) := by
    refine ⟨?_, ?_⟩
    · intro X hX Y hY hne
      rcases mem2 X hX with hXA | hXB <;> rcases mem2 Y hY with hYA | hYB
      · exact absurd (hXA.trans hYA.symm) hne
      · refine (Finset.disjoint_iff_inter_eq_empty).mp (Finset.disjoint_left.mpr ?_)
        intro x hx
        rw [hYB]
        exact hdisAB x (by simpa [hXA] using hx)
      · refine (Finset.disjoint_iff_inter_eq_empty).mp (Finset.disjoint_left.mpr ?_)
        intro x hx
        rw [hYA]
        intro hxA
        exact hdisAB x hxA (by simpa [hXB] using hx)
      · exact absurd (hXB.trans hYB.symm) hne
    · intro X hX Y hY hne v hvX w hwY
      rcases mem2 X hX with hXA | hXB <;> rcases mem2 Y hY with hYA | hYB
      · exact absurd (hXA.trans hYA.symm) hne
      · exact hantiAB v (by simpa [hXA] using hvX) w (by simpa [hYB] using hwY)
      · intro hvw
        exact hantiAB w (by simpa [hYA] using hwY) v (by simpa [hXB] using hvX) hvw.symm
      · exact absurd (hXB.trans hYB.symm) hne
  -- the two halves, proved directly (no `Finset` sum over the two pieces, so that the degenerate
  -- case `A = B` — which forces `V = ∅` — needs no case split)
  have hle : tauOdd G ≤ tauOdd (induceFinset G A) + tauOdd (induceFinset G B) := by
    have hZA : HitsOddCycles (induceFinset G A)
        ((tauOddMin (G := induceFinset G A)).1) :=
      hitsOddCycles_of_tauOddMin (G := induceFinset G A)
    have hZB : HitsOddCycles (induceFinset G B)
        ((tauOddMin (G := induceFinset G B)).1) :=
      hitsOddCycles_of_tauOddMin (G := induceFinset G B)
    refine le_trans (tauOdd_le (Z :=
      (tauOddMin (G := induceFinset G A)).1 ∪ (tauOddMin (G := induceFinset G B)).1) ?_) ?_
    · intro C hC
      rcases isOddCycle_sub_anticover hAB hC with hCA | hCB
      · have hne : C ∩ (tauOddMin (G := induceFinset G A)).1 ≠ ∅ :=
          hZA C (IsOddCycle.induceFinset hC hCA)
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hxm := Finset.mem_inter.mp hx
        exact ne_empty_of_nonempty ⟨x, Finset.mem_inter.mpr
          ⟨hxm.1, Finset.mem_union_left _ hxm.2⟩⟩
      · have hne : C ∩ (tauOddMin (G := induceFinset G B)).1 ≠ ∅ :=
          hZB C (IsOddCycle.induceFinset hC hCB)
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hxm := Finset.mem_inter.mp hx
        exact ne_empty_of_nonempty ⟨x, Finset.mem_inter.mpr
          ⟨hxm.1, Finset.mem_union_right _ hxm.2⟩⟩
    · have h3 : ((tauOddMin (G := induceFinset G A)).1 ∪
          (tauOddMin (G := induceFinset G B)).1).card
          ≤ (tauOddMin (G := induceFinset G A)).1.card
            + (tauOddMin (G := induceFinset G B)).1.card :=
        Finset.card_union_le (tauOddMin (G := induceFinset G A)).1
          (tauOddMin (G := induceFinset G B)).1
      rw [card_tauOddMin (G := induceFinset G A), card_tauOddMin (G := induceFinset G B)] at h3
      exact h3
  have hge : tauOdd (induceFinset G A) + tauOdd (induceFinset G B) ≤ tauOdd G := by
    obtain ⟨Z, hZ, hmin⟩ := tauOdd_spec (G := G)
    have h1 : tauOdd (induceFinset G A) ≤ (Z ∩ A).card := by
      refine tauOdd_le (Z := Z ∩ A) ?_
      intro C hC
      have hne : C ∩ Z ≠ ∅ := hZ C (IsOddCycle.of_induceFinset hC)
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hxm := Finset.mem_inter.mp hx
      have hne' : (C ∩ (Z ∩ A)).Nonempty :=
        ⟨x, Finset.mem_inter.mpr
          ⟨hxm.1, Finset.mem_inter.mpr ⟨hxm.2, isOddCycle_sub_induceFinset hC hxm.1⟩⟩⟩
      exact ne_empty_of_nonempty hne'
    have h2 : tauOdd (induceFinset G B) ≤ (Z ∩ B).card := by
      refine tauOdd_le (Z := Z ∩ B) ?_
      intro C hC
      have hne : C ∩ Z ≠ ∅ := hZ C (IsOddCycle.of_induceFinset hC)
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hxm := Finset.mem_inter.mp hx
      have hne' : (C ∩ (Z ∩ B)).Nonempty :=
        ⟨x, Finset.mem_inter.mpr
          ⟨hxm.1, Finset.mem_inter.mpr ⟨hxm.2, isOddCycle_sub_induceFinset hC hxm.1⟩⟩⟩
      exact ne_empty_of_nonempty hne'
    have h3 : (Z ∩ A).card + (Z ∩ B).card = Z.card := by
      have heq : Z = (Z ∩ A) ∪ (Z ∩ B) := by
        apply Finset.Subset.antisymm
        · intro x hx
          rw [Finset.mem_union]
          have hx' : x ∈ A ∪ B := by
            rw [hAB']
            exact Finset.mem_univ x
          rcases Finset.mem_union.mp hx' with hA | hB
          · exact Or.inl (Finset.mem_inter.mpr ⟨hx, hA⟩)
          · exact Or.inr (Finset.mem_inter.mpr ⟨hx, hB⟩)
        · intro x hx
          exact (Finset.mem_union.mp hx).elim
            (fun h => (Finset.mem_inter.mp h).1) (fun h => (Finset.mem_inter.mp h).1)
      have hdis0 : Disjoint (Z ∩ A) (Z ∩ B) := by
        rw [Finset.disjoint_left]
        intro x hx hy
        exact hAB.1 (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hy).2
      have hunion : ((Z ∩ A) ∪ (Z ∩ B)).card = (Z ∩ A).card + (Z ∩ B).card :=
        Finset.card_union_of_disjoint hdis0
      calc (Z ∩ A).card + (Z ∩ B).card = ((Z ∩ A) ∪ (Z ∩ B)).card := hunion.symm
        _ = Z.card := congrArg Finset.card heq.symm
    omega
  exact le_antisymm hle hge

end Cover

/-! ## Part 3 — the exact accounting at a 1-cut and at a 2-cut -/

section Cuts

/-- **The piece of a 1-cut at the part `i`**: the part together with the cut vertex.  This is the
`insert v (sp.parts i)` of `JSPProblem/Piece.lean`, given a name. -/
noncomputable def onePiece {v : V} {t : ℕ} (sp : OneSplit G v t) (i : Fin t) : Finset V :=
  insert v (sp.parts i)

/-- **The minimum transversal of the piece `T_i ∪ {v}` of a 1-cut.** -/
noncomputable def onePieceMin {v : V} {t : ℕ} (sp : OneSplit G v t) (i : Fin t) : Finset V :=
  (tauOddMin (G := induceFinset G (onePiece sp i))).1

@[simp] theorem hitsOddCycles_onePieceMin {v : V} {t : ℕ} (sp : OneSplit G v t) (i : Fin t) :
    HitsOddCycles (induceFinset G (onePiece sp i)) (onePieceMin sp i) :=
  hitsOddCycles_of_tauOddMin (G := induceFinset G (onePiece sp i))

@[simp] theorem card_onePieceMin {v : V} {t : ℕ} (sp : OneSplit G v t) (i : Fin t) :
    (onePieceMin sp i).card = tauOdd (induceFinset G (onePiece sp i)) :=
  card_tauOddMin (G := induceFinset G (onePiece sp i))

/-- **AT A 1-CUT, `tauOdd` ADDS OVER THE PIECES, WITH NO `+1`, EACH PIECE CHARGED ITS OWN MINIMUM.**

`JSPProblem/Piece.lean` `closeToBipartite_of_1split_bounded_pieces` composes a *uniform* bound `m`
on the `t` pieces into `m * t`.  Here each piece is charged the *minimum* transversal of that piece,
so the constant is `∑ i, tauOdd (T_i ∪ {v})`, which is never larger and does not mention the number
of parts at all. -/
theorem tauOdd_le_sum_onePieces {v : V} {t : ℕ} (sp : OneSplit G v t) [Fintype V] :
    tauOdd G ≤ ∑ i : Fin t, tauOdd (induceFinset G (onePiece sp i)) := by
  classical
  have hWcard : ∀ i, (onePieceMin sp i).card = tauOdd (induceFinset G (onePiece sp i)) :=
    fun i => card_onePieceMin sp i
  have hWhits : ∀ i, HitsOddCycles (induceFinset G (onePiece sp i)) (onePieceMin sp i) :=
    fun i => hitsOddCycles_onePieceMin sp i
  have key2 : ∃ Z : Finset V, HitsOddCycles G Z ∧
      Z.card ≤ ∑ i : Fin t, tauOdd (induceFinset G (onePiece sp i)) := by
    refine ⟨(Finset.univ : Finset (Fin t)).biUnion (onePieceMin sp), ?_, ?_⟩
    · intro C hC
      obtain ⟨i, hi, hiS⟩ := sp.oddCycle_piece hC
      have hi' : IsOddCycle (induceFinset G (onePiece sp i)) C :=
        IsOddCycle.induceFinset hC hiS
      have hne : C ∩ onePieceMin sp i ≠ ∅ := hWhits i C hi'
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hxm := Finset.mem_inter.mp hx
      have hne' : (C ∩ ((Finset.univ : Finset (Fin t)).biUnion (onePieceMin sp))).Nonempty :=
        ⟨x, Finset.mem_inter.mpr ⟨hxm.1, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hxm.2⟩⟩⟩
      exact ne_empty_of_nonempty hne'
    · have h1 : ((Finset.univ : Finset (Fin t)).biUnion (onePieceMin sp)).card
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)), (onePieceMin sp i).card :=
      Finset.card_biUnion_le
      have h2 : (∑ i ∈ (Finset.univ : Finset (Fin t)), (onePieceMin sp i).card)
          = ∑ i : Fin t, tauOdd (induceFinset G (onePiece sp i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact hWcard i
      omega
  obtain ⟨Z, hZ, hle'⟩ := key2
  exact le_trans (tauOdd_le hZ) hle'

/-- **AT A 1-CUT, `tauOdd` DOMINATES THE SUM OVER THE PARTS.**  The parts are pairwise disjoint, and
the restriction of a transversal of `G` to a part is a transversal of the part. -/
theorem tauOdd_ge_sum_parts {v : V} {t : ℕ} (sp : OneSplit G v t) [Fintype V] :
    (∑ i : Fin t, tauOdd (induceFinset G (sp.parts i))) ≤ tauOdd G := by
  classical
  obtain ⟨Z, hZ, hmin⟩ := tauOdd_spec (G := G)
  have h1 : (∑ i : Fin t, tauOdd (induceFinset G (sp.parts i)))
      ≤ ∑ i : Fin t, (Z ∩ sp.parts i).card := by
    refine Finset.sum_le_sum fun i _ => ?_
    refine tauOdd_le (Z := Z ∩ sp.parts i) ?_
    intro C hC
    have hne : C ∩ Z ≠ ∅ := hZ C (IsOddCycle.of_induceFinset hC)
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hxm := Finset.mem_inter.mp hx
    have hne' : (C ∩ (Z ∩ sp.parts i)).Nonempty :=
      ⟨x, Finset.mem_inter.mpr
        ⟨hxm.1, Finset.mem_inter.mpr ⟨hxm.2, isOddCycle_sub_induceFinset hC hxm.1⟩⟩⟩
    exact ne_empty_of_nonempty hne'
  have hdis : ∀ (i j : Fin t), i ≠ j →
      ∀ (x : V), x ∈ (Z ∩ sp.parts i) → x ∉ (Z ∩ sp.parts j) := by
    intro i j hij x hx hy
    exact false_of_mem_inter (sp.hdisj i j hij)
      (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hy).2⟩)
  have hbi : ((Finset.univ : Finset (Fin t)).biUnion fun i => Z ∩ sp.parts i)
      = Z ∩ (Finset.univ : Finset (Fin t)).biUnion fun i => sp.parts i := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    constructor
    · rintro ⟨a, ha, hz, hva⟩
      exact ⟨hz, a, ha, hva⟩
    · rintro ⟨hz, a, ha, hva⟩
      exact ⟨a, ha, hz, hva⟩
  have hdis' : ∀ (X Y : Fin t), X ∈ (Finset.univ : Finset (Fin t)) →
      Y ∈ (Finset.univ : Finset (Fin t)) → X ≠ Y →
      ∀ (x : V), x ∈ (Z ∩ sp.parts X) → x ∉ (Z ∩ sp.parts Y) := by
    intro X Y _ _ hij x hx hy
    exact hdis X Y hij x hx hy
  have heq : (∑ i : Fin t, (Z ∩ sp.parts i).card)
      = (Z ∩ (Finset.univ : Finset (Fin t)).biUnion fun i => sp.parts i).card := by
    rw [← card_biUnion_eq_sum _ hdis', hbi]
  have h2 : (∑ i : Fin t, (Z ∩ sp.parts i).card) ≤ Z.card := by
    calc (∑ i : Fin t, (Z ∩ sp.parts i).card)
        = (Z ∩ (Finset.univ : Finset (Fin t)).biUnion fun i => sp.parts i).card := heq
      _ ≤ Z.card := Finset.card_le_card Finset.inter_subset_left
  omega

/-- **A PIECE COSTS AT MOST ONE MORE THAN ITS PART**: adding the cut vertex forces at most one
further deletion. -/
theorem tauOdd_onePiece_le {v : V} {t : ℕ} (sp : OneSplit G v t) (i : Fin t) :
    tauOdd (induceFinset G (onePiece sp i)) ≤ tauOdd (induceFinset G (sp.parts i)) + 1 := by
  classical
  obtain ⟨Z, hZ, hmin⟩ := tauOdd_spec (G := induceFinset G (sp.parts i))
  refine le_trans (tauOdd_le (Z := Z ∪ ({v} : Finset V)) ?_) ?_
  · intro C hC
    by_cases hv : v ∈ C
    · exact ne_empty_of_nonempty
        ⟨v, Finset.mem_inter.mpr ⟨hv, by simp⟩⟩
    · have hsub : C ⊆ sp.parts i := by
        intro y hy
        have hyP : y ∈ onePiece sp i := isOddCycle_sub_induceFinset hC hy
        rw [onePiece, Finset.mem_insert] at hyP
        rcases hyP with hyP | hyP
        · exact absurd (hyP ▸ hy) hv
        · exact hyP
      have hne : C ∩ Z ≠ ∅ := hZ C ((hC.of_induceFinset).induceFinset hsub)
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hxm := Finset.mem_inter.mp hx
      exact ne_empty_of_nonempty
        ⟨x, Finset.mem_inter.mpr ⟨hxm.1, Finset.mem_union_left _ hxm.2⟩⟩
  · have h2 : (Z ∪ ({v} : Finset V)).card ≤ Z.card + 1 := by
      have h3 := Finset.card_union_le Z ({v} : Finset V)
      rw [Finset.card_singleton] at h3
      omega
    omega

/-- **THE EXACT ACCOUNTING AT A 1-CUT: `tauOdd` LIES BETWEEN THE SUM OVER THE PARTS AND THE SUM OVER
THE PARTS PLUS THE NUMBER OF PARTS.**

This is the numerical form of the whole piece axis (`JSPProblem/Piece.lean`): a block-cut
decomposition costs, at a cut vertex, at most one vertex per part, and nothing more. -/
theorem tauOdd_oneSplit_interval {v : V} {t : ℕ} (sp : OneSplit G v t) [Fintype V] :
    (∑ i : Fin t, tauOdd (induceFinset G (sp.parts i))) ≤ tauOdd G ∧
      tauOdd G ≤ ∑ i : Fin t, (tauOdd (induceFinset G (sp.parts i)) + 1) :=
  ⟨tauOdd_ge_sum_parts sp,
   le_trans (tauOdd_le_sum_onePieces sp)
     (Finset.sum_le_sum fun i _ => tauOdd_onePiece_le sp i)⟩

/-- **A ONE-SIDED 1-CUT IS FREE, IN THE LANGUAGE OF THE NUMBER.**  If `T_{i₀} ∪ {v}` is the only
non-bipartite piece then `tauOdd G = tauOdd (T_{i₀} ∪ {v})` — `JSPProblem/Piece.lean`
`closeToBipartite_iff_of_oneNonBipartitePiece` as an equality of numbers. -/
theorem tauOdd_eq_onePiece_of_bipartite_pieces {v : V} {t : ℕ} (sp : OneSplit G v t) [Fintype V]
    {i₀ : Fin t} (hbip : ∀ i, i ≠ i₀ → (induceFinset G (onePiece sp i)).IsBipartite) :
    tauOdd G = tauOdd (induceFinset G (onePiece sp i₀)) := by
  refine le_antisymm ?_ (tauOdd_induceFinset_le _)
  calc tauOdd G ≤ ∑ i : Fin t, tauOdd (induceFinset G (onePiece sp i)) :=
      tauOdd_le_sum_onePieces sp
    _ = tauOdd (induceFinset G (onePiece sp i₀)) := by
      have h1 : ∀ b ∈ (Finset.univ : Finset (Fin t)), b ≠ i₀ →
          tauOdd (induceFinset G (onePiece sp b)) = 0 := by
        intro b _ hb
        exact tauOdd_eq_zero_of_isBipartite (hbip b hb)
      have h2 : i₀ ∉ (Finset.univ : Finset (Fin t)) →
          tauOdd (induceFinset G (onePiece sp i₀)) = 0 := by
        intro hi
        exact absurd (Finset.mem_univ i₀) hi
      exact Finset.sum_eq_single i₀ h1 h2

/-- **The minimum transversal of the piece `T_i ∪ {a, b}` of a 2-cut.** -/
noncomputable def twoPieceMin {a b : V} {t : ℕ} (sp : VertexSplit G a b t) (i : Fin t) : Finset V :=
  (tauOddMin (G := induceFinset G (sp.piece i))).1

@[simp] theorem hitsOddCycles_twoPieceMin {a b : V} {t : ℕ} (sp : VertexSplit G a b t)
    (i : Fin t) : HitsOddCycles (induceFinset G (sp.piece i)) (twoPieceMin sp i) :=
  hitsOddCycles_of_tauOddMin (G := induceFinset G (sp.piece i))

@[simp] theorem card_twoPieceMin {a b : V} {t : ℕ} (sp : VertexSplit G a b t) (i : Fin t) :
    (twoPieceMin sp i).card = tauOdd (induceFinset G (sp.piece i)) :=
  card_tauOddMin (G := induceFinset G (sp.piece i))

/-- **AT A 2-CUT, `tauOdd` IS AT MOST THE SUM OVER THE PIECES PLUS THE TWO VERTICES OF THE CUT.**
The sharp form of `JSPProblem/CutVertex.lean`
`VertexSplit.closeToBipartite_two_of_nonBipartiteParts` (`2 + m * r`). -/
theorem tauOdd_le_add_two_of_vertexSplit {a b : V} {t : ℕ} (sp : VertexSplit G a b t) [Fintype V] :
    tauOdd G ≤ 2 + ∑ i : Fin t, tauOdd (induceFinset G (sp.piece i)) := by
  classical
  have hWcard : ∀ i, (twoPieceMin sp i).card = tauOdd (induceFinset G (sp.piece i)) :=
    fun i => card_twoPieceMin sp i
  have hWhits : ∀ i, HitsOddCycles (induceFinset G (sp.piece i)) (twoPieceMin sp i) :=
    fun i => hitsOddCycles_twoPieceMin sp i
  have key2 : ∃ Z : Finset V, HitsOddCycles G Z ∧
      Z.card ≤ 2 + ∑ i : Fin t, tauOdd (induceFinset G (sp.piece i)) := by
    refine ⟨insert a (insert b ((Finset.univ : Finset (Fin t)).biUnion (twoPieceMin sp))), ?_, ?_⟩
    · intro C hC
      rcases sp.oddCycle_piece_or_avoid hC with ⟨i, hi⟩ | hne
      · have hi' : IsOddCycle (induceFinset G (sp.piece i)) C := IsOddCycle.induceFinset hC hi
        have hne' : C ∩ twoPieceMin sp i ≠ ∅ := hWhits i C hi'
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne'
        have hxm := Finset.mem_inter.mp hx
        have hne'' :
            (C ∩ (insert a (insert b ((Finset.univ : Finset (Fin t)).biUnion (twoPieceMin sp))))).Nonempty :=
          ⟨x, Finset.mem_inter.mpr
            ⟨hxm.1, Finset.mem_insert.mpr
              (Or.inr (Finset.mem_insert.mpr
                (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hxm.2⟩))))⟩⟩
        exact ne_empty_of_nonempty hne''
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hxc : x ∈ C := (Finset.mem_inter.mp hx).1
        rcases Finset.mem_insert.mp (Finset.mem_inter.mp hx).2 with h | h
        · exact ne_empty_of_nonempty ⟨x, Finset.mem_inter.mpr ⟨hxc,
            Finset.mem_insert.mpr (Or.inl h)⟩⟩
        · have h' : x = b := Finset.mem_singleton.mp h
          exact ne_empty_of_nonempty ⟨x, Finset.mem_inter.mpr ⟨hxc,
              Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h')))⟩⟩
    · have h1 : ((Finset.univ : Finset (Fin t)).biUnion (twoPieceMin sp)).card
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)), (twoPieceMin sp i).card :=
      Finset.card_biUnion_le
      have h2 : (insert a (insert b ((Finset.univ : Finset (Fin t)).biUnion (twoPieceMin sp)))).card ≤
          ((Finset.univ : Finset (Fin t)).biUnion (twoPieceMin sp)).card + 2 := by
        have e1 := Finset.card_insert_le a
          (insert b ((Finset.univ : Finset (Fin t)).biUnion (twoPieceMin sp)))
        have e2 := Finset.card_insert_le b ((Finset.univ : Finset (Fin t)).biUnion (twoPieceMin sp))
        omega
      have h3 : (∑ i ∈ (Finset.univ : Finset (Fin t)), (twoPieceMin sp i).card)
          = ∑ i : Fin t, tauOdd (induceFinset G (sp.piece i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact hWcard i
      omega
  obtain ⟨Z, hZ, hle'⟩ := key2
  exact le_trans (tauOdd_le hZ) hle'

end Cuts

/-! ## Part 4 — the budget-split form of Erdős #73 -/

section Budget

/-- **THE MASTER REDUCTION: ERDŐS #73 FOR `G` FOLLOWS FROM ERDŐS #73 FOR THE PIECES, EACH PIECE AT
EVERY PARAMETER UP TO **ITS OWN** DEFICIENCY, WITH THE CONSTANTS ADDED UP.**

This is the general form of `JSPProblem/Exact.lean` `erdos73On_of_pieceMaxDef`: instead of
requiring every piece to be MaxDef-close with the same constant `k`, every piece is required to
satisfy the conclusion at every local parameter up to its own deficiency, with its own constant
`g X j`, and the total constant is `∑ X, g X (MaxDef (G[X]))`.

The **budget splits**: `LocIndep k G` is used only through `LocIndep (MaxDef (G[X])) (G[X])` for each
piece, i.e. each piece is asked at its own deficiency, which is at most `MaxDef G`; no piece is
asked at the parameter `k` of the whole graph unless its deficiency really is `k`. -/
theorem erdos73On_of_anticoverCover_of_pieceDeficit {k : ℕ} {𝒬 : Finset (Finset V)}
    {g : Finset V → ℕ → ℕ} (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X)
    (hg : ∀ X ∈ 𝒬, ∀ j, j ≤ MaxDef (induceFinset G X) → LocIndep j (induceFinset G X) →
      CloseToBipartite (g X j) (induceFinset G X))
    (hG : LocIndep k G) :
    CloseToBipartite (∑ X ∈ 𝒬, g X (MaxDef (induceFinset G X))) G := by
  refine closeToBipartite_of_cover_cost h hcov ?_
  intro X hX
  exact hg X hX (MaxDef (induceFinset G X)) (le_refl _)
    (locIndep_of_maxDef_le (le_refl _))

/-- **THE SAME REDUCTION IN THE ERDŐS–PÓSA SHAPE: each piece is asked at its own PACKING bound.**

If the Erdős–Pósa theorem for odd cycles is known for the piece `G[X]` at every packing bound, then
it holds for `G`.  This is the formal statement of "the Erdős–Pósa theorem splits over an
anticomplete cover", i.e. that the reduction `JSP90.erdos73_of_erdosPosa` is compatible with the
decomposition theory. -/
theorem erdos73On_of_anticoverCover_of_piecePacking {k : ℕ} {𝒬 : Finset (Finset V)}
    {m : Finset V → ℕ} (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X)
    (hp : ∀ X ∈ 𝒬, ∀ j : ℕ,
      (∀ C, IsOddCycleFamily (G := induceFinset G X) C → C.card ≤ j) →
        LocIndep j (induceFinset G X) → CloseToBipartite (m X) (induceFinset G X))
    (hG : LocIndep k G) : CloseToBipartite (∑ X ∈ 𝒬, m X) G := by
  classical
  refine erdos73On_of_anticoverCover_of_pieceDeficit (g := fun X _ => m X) h hcov ?_ hG
  intro X hX j _ hX'
  exact hp X hX j (fun C hC => hX'.oddCycleFamily_card_le hC) hX'

/-- **ROUND 105'S INSTANCE, IN THE NEW FORM.**  The pieces are each MaxDef-close and the budgets
split; the total is `∑ X, MaxDef (G[X]) = MaxDef G`. -/
theorem erdos73On_of_anticoverCover_of_maxDef {k : ℕ} {𝒬 : Finset (Finset V)}
    (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X)
    (hc : ∀ X ∈ 𝒬, CloseToBipartite (MaxDef (induceFinset G X)) (induceFinset G X))
    (hG : LocIndep k G) : CloseToBipartite (MaxDef G) G := by
  have h1 : CloseToBipartite (∑ X ∈ 𝒬, MaxDef (induceFinset G X)) G := by
    refine erdos73On_of_anticoverCover_of_pieceDeficit
      (g := fun X _ => MaxDef (induceFinset G X)) h hcov ?_ hG
    intro X hX j _ _
    exact hc X hX
  have h2 : (∑ X ∈ 𝒬, MaxDef (induceFinset G X)) = MaxDef G :=
    (maxDef_eq_sum_of_cover h hcov).symm
  exact h2 ▸ h1

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM: BOUNDED ODD GIRTH *PER PIECE*.**

If every odd cycle of the piece `G[X]` has at most `ℓ X` vertices — the odd girth bound is a
property of the pieces, with a different bound for each — then Erdős #73 holds for `G` with the
constant `∑ X, ℓ X * MaxDef (G[X])`.  Compared with `JSPProblem/Transversal.lean`
`erdos73On_of_bounded_odd_girth` (one bound `ℓ` for the whole graph) the hypothesis is a *per-piece*
one and the constants are *added* rather than multiplied by the whole-graph parameter. -/
theorem erdos73On_of_anticoverCover_of_bounded_pieceGirth {k : ℕ}
    {𝒬 : Finset (Finset V)} (ℓ : Finset V → ℕ) (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X)
    (hlen : ∀ X ∈ 𝒬, ∀ C, IsOddCycle (induceFinset G X) C → C.card ≤ ℓ X)
    (hG : LocIndep k G) :
    CloseToBipartite (∑ X ∈ 𝒬, ℓ X * MaxDef (induceFinset G X)) G := by
  have hg : ∀ X ∈ 𝒬, ∀ j, j ≤ MaxDef (induceFinset G X) → LocIndep j (induceFinset G X) →
      CloseToBipartite (ℓ X * j) (induceFinset G X) := by
    intro X hX j hj hX'
    exact erdos73On_of_bounded_odd_girth j (ℓ X) V (inferInstance : Fintype V)
      (induceFinset G X) hX' (fun C hC => hlen X hX C hC)
  exact erdos73On_of_anticoverCover_of_pieceDeficit (g := fun X j => ℓ X * j) h hcov hg hG

/-- **A UNIFORM ODD GIRTH BOUND ON THE PIECES GIVES THE CLASSICAL CONSTANT `ℓ * k`.**  The
deficiency splits over the cover (`JSP90.maxDef_eq_sum_of_cover`, round 105), so the sum of the
piece costs is `ℓ * MaxDef G ≤ ℓ * k`. -/
theorem erdos73On_of_anticoverCover_of_bounded_girth {k ℓ : ℕ} {𝒬 : Finset (Finset V)}
    (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X)
    (hlen : ∀ X ∈ 𝒬, ∀ C, IsOddCycle (induceFinset G X) C → C.card ≤ ℓ)
    (hG : LocIndep k G) : CloseToBipartite (ℓ * k) G := by
  have h1 := erdos73On_of_anticoverCover_of_bounded_pieceGirth (k := k) (fun _ => ℓ) h hcov hlen hG
  have h2 : (∑ X ∈ 𝒬, ℓ * MaxDef (induceFinset G X)) = ℓ * MaxDef G := by
    have h2' := (maxDef_eq_sum_of_cover h hcov).symm
    rw [← h2']
    rw [Finset.mul_sum]
  have h3 : ℓ * MaxDef G ≤ ℓ * k :=
    Nat.mul_le_mul_left ℓ (maxDef_le_of_locIndep hG)
  exact closeToBipartite_mono (h2 ▸ h3) h1

/-- **THE TWO BUDGETS SPLIT AS WELL: `MaxDef G[A] ≤ k₁` and `MaxDef G[B] ≤ k₂`, with Erdős #73 at
`k₁` and at `k₂`, give Erdős #73 at `k₁ + k₂` with constant `m₁ + m₂`.**

This is the `Erdős73On`-level statement of `JSP90.tauOdd_induceFinset_add`: the two halves of an
anticomplete split are independent instances of the problem, and the answer adds. -/
theorem closeToBipartite_of_anticover_two_of_maxDef {k1 k2 m1 m2 : ℕ} {A B : Finset V}
    (hAB : Anticover G A B) (hk1 : MaxDef (induceFinset G A) ≤ k1)
    (hk2 : MaxDef (induceFinset G B) ≤ k2)
    (h1 : ∀ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      LocIndep k1 H → CloseToBipartite m1 H)
    (h2 : ∀ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      LocIndep k2 H → CloseToBipartite m2 H) :
    CloseToBipartite (m1 + m2) G := by
  have hsum := tauOdd_induceFinset_add hAB
  have ha : tauOdd (induceFinset G A) ≤ m1 := by
    obtain ⟨Z, hcard, hZ⟩ := (closeToBipartite_iff_hitsOddCycles (V := V)
      (G := induceFinset G A) (m := m1)).mp (h1 V _ _ (locIndep_of_maxDef_le hk1))
    exact le_trans (tauOdd_le hZ) hcard
  have hb : tauOdd (induceFinset G B) ≤ m2 := by
    obtain ⟨Z, hcard, hZ⟩ := (closeToBipartite_iff_hitsOddCycles (V := V)
      (G := induceFinset G B) (m := m2)).mp (h2 V _ _ (locIndep_of_maxDef_le hk2))
    exact le_trans (tauOdd_le hZ) hcard
  refine (closeToBipartite_iff_tauOdd_le (G := G) (m := m1 + m2)).mpr ?_
  rw [hsum]
  exact le_trans (add_le_add ha hb) (le_refl _)

/-- **THE SAME, IN THE `Erdős73On` FORM: THE ANSWER TO ERDŐS #73 ADDS OVER AN ANTICOMPLETE SPLIT
WHOSE TWO DEFICIENCIES SPLIT ACCORDINGLY.** -/
theorem erdos73On_of_anticover_two {k1 k2 m1 m2 : ℕ} {A B : Finset V} (hAB : Anticover G A B)
    (hk1 : MaxDef (induceFinset G A) ≤ k1) (hk2 : MaxDef (induceFinset G B) ≤ k2)
    (h1 : Erdős73On.{u} k1 m1) (h2 : Erdős73On.{u} k2 m2) :
    CloseToBipartite (m1 + m2) G :=
  closeToBipartite_of_anticover_two_of_maxDef hAB hk1 hk2 h1 h2

end Budget

/-! ## Part 5 — sharpness, and the obstruction to extending the exactness to cuts -/

section Sharp

/-- **THE EXACT VALUE OF `tauOdd` ON THE LOWER-BOUND WITNESS: `tauOdd (p9Family k) = 2 * k`.**

Round 76's `f(k) ≥ 2 k` (Erdős Problem #73) in the language of the number: the disjoint union of `k`
copies of `p9` has least odd cycle transversal of size exactly `2 k`. -/
theorem tauOdd_p9Family (k : ℕ) : tauOdd (p9Family k) = 2 * k := by
  have hle : tauOdd (p9Family k) ≤ 2 * k :=
    (closeToBipartite_iff_tauOdd_le (G := p9Family k) (m := 2 * k)).mp
      ((closeToBipartite_p9Family_iff (k := k) (m := 2 * k)).mpr (Nat.le_refl _))
  refine Nat.le_antisymm hle (le_of_not_gt ?_)
  intro h
  have h2 : CloseToBipartite (2 * k - 1) (p9Family k) := by
    refine (closeToBipartite_iff_tauOdd_le (G := p9Family k) (m := 2 * k - 1)).mpr ?_
    have h3 : tauOdd (p9Family k) ≤ 2 * k - 1 := by omega
    exact h3
  exact absurd h2 (by
    intro hcon
    rw [closeToBipartite_p9Family_iff] at hcon
    omega)

/-- **THE EXACT VALUE OF `tauOdd` ON THE WINDMILL: `tauOdd wf = 1`.** -/
theorem tauOdd_wf : tauOdd wf = 1 := by
  have hle : tauOdd wf ≤ 1 :=
    (closeToBipartite_iff_tauOdd_le (G := wf) (m := 1)).mp windmill_closeToBipartite_one
  refine Nat.le_antisymm hle (le_of_not_gt ?_)
  intro h
  have hnb : ¬ wf.IsBipartite :=
    fun hb => (not_isOddCycle_of_isBipartite hb) exists_isOddCycle_wf
  exact hnb ((tauOdd_zero_iff (G := wf)).mp (Nat.lt_one_iff.mp h))

section WindmillPieces


/-- The first piece of `wf` is the triangle `{0, 1, 2}`. -/
theorem insert_0_wfPiece_0 : insert 0 (wfPiece 0) = ({0, 1, 2} : Finset (Fin 6)) := by
  rw [wfPiece_0]

/-- The second piece of `wf` is the triangle `{0, 3, 4}`. -/
theorem insert_0_wfPiece_1 : insert 0 (wfPiece 1) = ({0, 3, 4} : Finset (Fin 6)) := by
  rw [wfPiece_1]

/-- **`{1}` IS AN ODD CYCLE TRANSVERSAL OF THE FIRST PIECE.**  The piece is the triangle `{0, 1, 2}`,
so the only odd cycle of it is the whole piece: an odd cycle has at least three vertices and the
piece has exactly three. -/
theorem hitsOddCycles_one_wf_piece_0 :
    HitsOddCycles (induceFinset wf (insert 0 (wfPiece 0)))
      (insert (1 : Fin 6) (∅ : Finset (Fin 6))) := by
  intro C hC
  have hsub : C ⊆ insert 0 (wfPiece 0) := isOddCycle_sub_induceFinset hC
  have h3 : 3 ≤ C.card := isOddCycle_card_ge_three hC
  have hcard : (insert 0 (wfPiece 0) : Finset (Fin 6)).card = 3 := by
    simp [wfPiece_0]
  have hle : (insert 0 (wfPiece 0) : Finset (Fin 6)).card ≤ C.card := by rw [hcard]; omega
  have heq : C = insert 0 (wfPiece 0) := Finset.eq_of_subset_of_card_le hsub hle
  rw [heq]
  exact ne_empty_of_nonempty ⟨1, by simp [wfPiece_0]⟩

/-- **`{3}` IS AN ODD CYCLE TRANSVERSAL OF THE SECOND PIECE.** -/
theorem hitsOddCycles_three_wf_piece_1 :
    HitsOddCycles (induceFinset wf (insert 0 (wfPiece 1)))
      (insert (3 : Fin 6) (∅ : Finset (Fin 6))) := by
  intro C hC
  have hsub : C ⊆ insert 0 (wfPiece 1) := isOddCycle_sub_induceFinset hC
  have h3 : 3 ≤ C.card := isOddCycle_card_ge_three hC
  have hcard : (insert 0 (wfPiece 1) : Finset (Fin 6)).card = 3 := by
    simp [wfPiece_1]
  have hle : (insert 0 (wfPiece 1) : Finset (Fin 6)).card ≤ C.card := by rw [hcard]; omega
  have heq : C = insert 0 (wfPiece 1) := Finset.eq_of_subset_of_card_le hsub hle
  rw [heq]
  exact ne_empty_of_nonempty ⟨3, by simp [wfPiece_1]⟩

/-- **THE FIRST PIECE OF `wf` IS `1`-CLOSE TO BIPARTITE.** -/
theorem closeToBipartite_one_wf_piece_0 :
    CloseToBipartite 1 (induceFinset wf (insert 0 (wfPiece 0))) :=
  (closeToBipartite_iff_hitsOddCycles (G := induceFinset wf (insert 0 (wfPiece 0)))
    (m := 1)).mpr ⟨insert (1 : Fin 6) (∅ : Finset (Fin 6)), by simp,
      hitsOddCycles_one_wf_piece_0⟩

/-- **THE SECOND PIECE OF `wf` IS `1`-CLOSE TO BIPARTITE.** -/
theorem closeToBipartite_one_wf_piece_1 :
    CloseToBipartite 1 (induceFinset wf (insert 0 (wfPiece 1))) :=
  (closeToBipartite_iff_hitsOddCycles (G := induceFinset wf (insert 0 (wfPiece 1)))
    (m := 1)).mpr ⟨insert (3 : Fin 6) (∅ : Finset (Fin 6)), by simp,
      hitsOddCycles_three_wf_piece_1⟩

/-- **`tauOdd` OF THE FIRST PIECE OF `wf` IS EXACTLY ONE.** -/
theorem tauOdd_wf_piece_0 : tauOdd (induceFinset wf (insert 0 (wfPiece 0))) = 1 := by
  have hle : tauOdd (induceFinset wf (insert 0 (wfPiece 0))) ≤ 1 :=
    (closeToBipartite_iff_tauOdd_le (G := induceFinset wf (insert 0 (wfPiece 0)))
      (m := 1)).mp closeToBipartite_one_wf_piece_0
  refine Nat.le_antisymm hle (le_of_not_gt ?_)
  intro h
  exact not_isBipartite_wf_piece_0
    ((tauOdd_zero_iff (G := induceFinset wf (insert 0 (wfPiece 0)))).mp (Nat.lt_one_iff.mp h))

/-- **`tauOdd` OF THE SECOND PIECE OF `wf` IS EXACTLY ONE.** -/
theorem tauOdd_wf_piece_1 : tauOdd (induceFinset wf (insert 0 (wfPiece 1))) = 1 := by
  have hle : tauOdd (induceFinset wf (insert 0 (wfPiece 1))) ≤ 1 :=
    (closeToBipartite_iff_tauOdd_le (G := induceFinset wf (insert 0 (wfPiece 1)))
      (m := 1)).mp closeToBipartite_one_wf_piece_1
  refine Nat.le_antisymm hle (le_of_not_gt ?_)
  intro h
  exact not_isBipartite_wf_piece_1
    ((tauOdd_zero_iff (G := induceFinset wf (insert 0 (wfPiece 1)))).mp (Nat.lt_one_iff.mp h))

/-- **MACHINE-CHECKED OBSTRUCTION: THE EXACTNESS OF `tauOdd_anticover_add` DOES NOT EXTEND TO CUTS.**

On the windmill — two triangles `0 1 2` and `0 3 4` meeting in the vertex `0`, which is the
`JSP90.wf_oneSplit` of `JSPProblem/Piece.lean` — the transversal number is `1`, while the two
non-bipartite pieces of the cut cost `1` each.  So at a cut the pieces **over-count** by the shared
cut vertex: exact additivity holds for anticomplete covers, where the pieces are *disjoint*, and
not for the pieces of a cut, where they overlap in the vertices of the cut.  This is why the `+2`
of `JSP90.tauOdd_le_add_two_of_vertexSplit` cannot be removed. -/
theorem not_tauOdd_additive_oneSplit :
    tauOdd wf < tauOdd (induceFinset wf (insert 0 (wfPiece 0))) +
      tauOdd (induceFinset wf (insert 0 (wfPiece 1))) := by
  rw [tauOdd_wf, tauOdd_wf_piece_0, tauOdd_wf_piece_1]
  omega

end WindmillPieces

end Sharp

end

end JSP90