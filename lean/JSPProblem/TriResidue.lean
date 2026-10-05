import JSPProblem.TriFix
import JSPProblem.TriFive

/-!
# JSP-000090, round 168 -- `JSPProblem/TriResidue.lean`: **THE RESIDUE OF A TRIANGLE IS BIPARTITE AT
## `LocIndep 1`, AT EVERY ORDER**

Attack family 90 (the EIGHT-VERTEX INSTANCE, second gap).  Round 167 closed the counting step of the
eight-vertex triangle case (`lean/JSPProblem/TriFive.lean`, `JSP90.loc8_lemma`, over a five-point
residue `K_{2,3}`) but recorded two gaps.  This file closes the **second** one, and does so in a
stronger form than was asked for:

```lean
JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one
  (hG : LocIndep 1 G) {T : Finset V} (hT : G.IsNClique 3 T) : (deleteFinset G T).IsBipartite
```

There is **no bound on `|V|`**.  Round 150's
`JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_seven`
(`lean/JSPProblem/Seven.lean`) needs `|V| ≤ 7` because it only knows how to rule out an odd cycle
of `3` vertices in the residue (`JSP90.not_isNClique_three_of_disjoint_of_locIndep_one`), and the
five-vertex odd cycle of the eight-vertex residue is exactly the case that bound could not reach.
The counting argument here has no such limit.

## The counting argument

Let `D` be an odd cycle of `G` vertex-disjoint from the triangle `T`, of odd cardinality `m ≥ 3`.
Erdős's hypothesis read on the `m + 3` points of `T ∪ D` gives an independent set `S` with
`2 * |S| + 1 ≥ m + 3`, while

* an independent set meets the triangle in at most **one** point
  (`JSP90.card_le_one_of_isIndepSet_sub_of_card_C_eq_three`);
* an independent set inside the odd cycle `D` has at most `(m - 1) / 2` points
  (`JSP90.two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle`, i.e. `α(C_m) ≤ ⌊m / 2⌋`);

so `2 * |S| + 1 ≤ 2 * (1 + (m - 1) / 2) + 1 = m + 2 < m + 3`, a contradiction.  Nothing in the
argument mentions `|V|`, which is why the residue of a triangle is bipartite at **every** order, and
in particular the eight-vertex transfer of `JSP90.triCase` — whose residue `X = {0, 1} + {2, 3, 4}`
is a `K_{2,3}` and needs a proper two-colouring of `G[X]` before anything else can be said — is now
unblocked.

`JSP90.not_isOddCycle_of_disjoint_of_isNClique_three_of_locIndep_one` is the statement of the
counting step alone; at `m = 3` it is round 150's
`JSP90.not_isNClique_three_of_disjoint_of_locIndep_one`, which is *not* redeclared here.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

local instance trResDec : DecidableEq V := Classical.decEq V

local instance trResAdj : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _

/-! ## Part 0 — the two counts an independent set inside `T ∪ D` obeys -/

/-- **AN INDEPENDENT SET MEETS A TRIANGLE IN AT MOST ONE POINT** (restated at the interface this
file uses, with the intersection in the hypothesis).

`JSP90.card_inter_le_one_of_isNClique_three_indep` of `lean/JSPProblem/TriFix.lean` is the same
statement with the same hypotheses; the name here is the one the counting step reads. -/
theorem card_inter_T_le_one_of_isNClique_three_indep {C s : Finset V} (hC : G.IsNClique 3 C)
    (hs : G.IsIndepSet s) : (s ∩ C).card ≤ 1 :=
  card_inter_le_one_of_isNClique_three_indep hC hs

/-! ## Part 1 — **A TRIANGLE AND AN ODD CYCLE ARE NEVER VERTEX-DISJOINT AT `LocIndep 1`** -/

/-- **AT `LocIndep 1` A TRIANGLE AND AN ODD CYCLE OF `G` ARE NEVER VERTEX-DISJOINT.**

```lean
LocIndep 1 G → G.IsNClique 3 T → IsOddCycle G D → T ∩ D = ∅ → False
```

Let `m = |D|`, odd and `≥ 3`.  Erdős's hypothesis on the `m + 3` points of `T ∪ D` supplies an
independent set `S` with `2 * |S| + 1 ≥ m + 3`; an independent set meets the triangle in at most one
point and the odd cycle in at most `(m - 1) / 2` points, so `2 * |S| + 1 ≤ m + 2`.  Contradiction.

At `m = 3` this is `JSP90.not_isNClique_three_of_disjoint_of_locIndep_one` (round 150), which is
what the seven-vertex axis used; the statement here is the odd cycle of **any** length, and that is
what the eight-vertex residue needs. -/
theorem not_isOddCycle_of_disjoint_of_isNClique_three_of_locIndep_one (hG : LocIndep 1 G)
    {T D : Finset V} (hT : G.IsNClique 3 T) (hD : IsOddCycle G D) (hdis : T ∩ D = ∅) : False := by
  obtain ⟨_, hT3⟩ := G.isNClique_iff.mp hT
  -- Erdős's hypothesis, read on the `|T| + |D| = 3 + m` points of `T ∪ D`
  obtain ⟨S, hSsub, hSi, hb⟩ := hG (T ∪ D)
  -- an independent set meets the triangle in at most one point
  have hST : (S ∩ T).card ≤ 1 := card_inter_T_le_one_of_isNClique_three_indep hT hSi
  -- an independent set inside the odd cycle has at most `(|D| - 1) / 2` points
  have hSD : 2 * (S ∩ D).card + 1 ≤ D.card :=
    two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle hD
      (hSi.mono (Finset.inter_subset_left)) Finset.inter_subset_right
  -- `S ⊆ T ∪ D`, so `S` splits into the two pieces
  have hUnion : (S ∩ T) ∪ (S ∩ D) = S := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with h | h
      · exact (Finset.mem_inter.mp h).1
      · exact (Finset.mem_inter.mp h).1
    · intro hz
      rcases mem_inter_or_sdiff S (T ∪ D) z hz with h | h
      · rcases Finset.mem_union.mp (Finset.mem_inter.mp h).2 with h' | h'
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hz, h'⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hz, h'⟩))
      · exact absurd (hSsub hz) ((Finset.mem_sdiff.mp h).2)
  have hinterEmpty : (S ∩ T) ∩ (S ∩ D) = ∅ := by
    ext z
    constructor
    · intro hz
      have h1 := Finset.mem_inter.mp hz
      have h2 : z ∈ T ∩ D :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h1.1).2, (Finset.mem_inter.mp h1.2).2⟩
      rw [hdis] at h2
      simp at h2
    · intro hz
      simp at hz
  have hsum : S.card = (S ∩ T).card + (S ∩ D).card := by
    have h1 := Finset.card_union_add_card_inter (S ∩ T) (S ∩ D)
    rw [hUnion, Finset.card_eq_zero.mpr hinterEmpty, add_zero] at h1
    exact h1
  -- the cardinality of `T ∪ D` is `3 + |D|`
  have hcardUnion : (T ∪ D).card = 3 + D.card := by
    have h1 := Finset.card_union_add_card_inter T D
    rw [Finset.card_eq_zero.mpr hdis, hT3, add_zero] at h1
    omega
  -- `2 * |S| + 1 ≥ |T ∪ D| = 3 + |D|`, while the two counts give `2 * |S| + 1 ≤ 2 + |D|`
  have hge : 2 * S.card + 1 ≥ 3 + D.card := by rw [hcardUnion] at hb; exact hb
  have hle : 2 * S.card + 1 ≤ 2 + D.card := by rw [hsum]; omega
  omega

/-! ## Part 2 — **THE RESIDUE OF A TRIANGLE IS BIPARTITE AT `LocIndep 1`** -/

/-- **THE RESIDUE OF A TRIANGLE IS BIPARTITE AT `LocIndep 1`, AT EVERY ORDER.**

```lean
LocIndep 1 G → G.IsNClique 3 T → (deleteFinset G T).IsBipartite
```

An odd cycle `D` of the residue `G[V \ T]` is an odd cycle of `G` vertex-disjoint from the triangle
`T`, which Part 1 forbids; the odd-cycle characterisation of bipartiteness
(`JSP90.isBipartite_of_no_oddCycle`) closes the argument.

This is round 150's
`JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_seven` **with the bound
`|V| ≤ 7` removed** — that bound was there only because the five-vertex odd cycle of the residue was
out of reach, and the general count of Part 1 reaches it.  Two consequences:

* the eight-vertex transfer of `JSP90.triCase` (whose residue is the five-point `K_{2,3}` of
  `lean/JSPProblem/TriFiveLang.lean`) now has the proper two-colouring of the residue it needs;
* the statement holds at every order, so the triangle case of Erdős #73 at `k = 1` is not confined
  to small graphs. -/
theorem isBipartite_delete_of_isNClique_three_of_locIndep_one (hG : LocIndep 1 G)
    {T : Finset V} (hT : G.IsNClique 3 T) : (deleteFinset G T).IsBipartite := by
  rw [deleteFinset]
  refine isBipartite_of_no_oddCycle fun hD => ?_
  obtain ⟨D, hD⟩ := hD
  obtain ⟨hD', hDsub⟩ := isOddCycle_induceFinset hD
  have hdis : T ∩ D = ∅ := by
    ext z
    constructor
    · intro hz
      have h1 := Finset.mem_inter.mp hz
      exact False.elim ((Finset.mem_sdiff.mp (hDsub h1.2)).2 h1.1)
    · intro hz
      exact False.elim (by simpa using hz)
  exact not_isOddCycle_of_disjoint_of_isNClique_three_of_locIndep_one hG hT hD' hdis

/-- **THE EIGHT-VERTEX FORM, in the shape round 167 recorded as the second gap.**  The bridge the
`Fin 8` transfer consumes: at `LocIndep 1` and `|V| ≤ 8` the five vertices outside a triangle induce
a bipartite graph, i.e. the residue carries the proper two-colouring that
`JSP90.properM`/`JSP90.okMono` of `lean/JSPProblem/TriFiveLang.lean` are read against. -/
theorem isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_eight (hG : LocIndep 1 G)
    (_hV : Fintype.card V ≤ 8) {T : Finset V} (hT : G.IsNClique 3 T) :
    (deleteFinset G T).IsBipartite :=
  isBipartite_delete_of_isNClique_three_of_locIndep_one hG hT

/-- **THE RESIDUE OF A TRIANGLE IS BIPARTITE IN THE PIECE FORM**: inside any induced subgraph, deleting
one of its triangles leaves a bipartite graph.  This is the shape a peeling argument consumes, and it
is again free of any bound on the order of the piece. -/
theorem isBipartite_delete_of_isNClique_three_of_locIndep_one_piece (hG : LocIndep 1 G)
    {U : Finset V} {T : Finset V} (hT : (induceFinset G U).IsNClique 3 T) :
    (deleteFinset (induceFinset G U) T).IsBipartite := by
  -- `LocIndep 1` passes to the piece (`induceFinset G U`), and `T` is a triangle there
  exact isBipartite_delete_of_isNClique_three_of_locIndep_one (G := induceFinset G U)
    (locIndep_one_of_locIndep_one_induceFinset hG) hT

end

end JSP90
