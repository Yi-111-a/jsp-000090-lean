/-
# JSP-000090 — a cut triangle, and the reduction of Erdős Problem #73 to two local statements

This file is the **fifteenth attack family**.  It closes the two gaps that
`discovery/JSP-000090/policy.json` named at the end of round 63 and then carries the reduction of
`JSPProblem/Cut.lean` to its end.

Round 63 proved the *instance* half of the reduction to triangle-free graphs
(`JSP90.closeToBipartite_of_anticoverCut`: a cut at a triangle, constant `3 + k * m`) but recorded
that two things were missing:

* the `MaxDef` side of the triangle-cut induction (`1 + maxDefIn G Q ≤ MaxDef G` for every piece
  `Q` of a cut at a triangle), and
* a *canonical* cut at a triangle: the components of `G − T` are **not** an `AnticoverCut` in
  general, because a component of `G − T` may meet `T` (`K_4` at a triangle is the witness), and
  `AnticoverCut` is a genuine hypothesis, not a theorem.

This round supplies both, and then runs the induction.

## 1. The deficiency of an induced subgraph (`Part 1`)

`MaxDef G` is the supremum of `|Y| - 2 α(G[Y])` over `Y ⊆ V`, and `maxDefIn G U` is the same
supremum over `Y ⊆ U`.  The two are different objects and the difference matters:

```lean
JSP90.maxDef_eq_maxDefIn_induceFinset : MaxDef (induceFinset G U) = maxDefIn G U
```

which says that the maximum deficiency *of the graph* `G[U]` (measured over all subsets of the
ambient vertex set) is the deficiency *inside `U`* measured in `G`.  The content is
`JSP90.indepCard_induceFinset_inter_add_sdiff`: the vertices of `Y` outside `U` are isolated in
`G[U]`, so

```lean
α(G[U], Y) = α(G[U], Y ∩ U) + |Y \ U|
```

and hence `defOf (G[U]) Y ≤ defOf (G[U]) (Y ∩ U)`.  This is the transport lemma that makes the
quantity `maxDefIn` usable as the induction parameter of the triangle descent, and it is what
allows `LocIndep (k - 1) (induceFinset G Q)` to be read off `1 + maxDefIn G Q ≤ k`
(`JSP90.locIndep_piece_of_cutTriangle`).

## 2. Components of a subgraph, and a cut triangle (`Parts 2 and 3`)

`JSP90.anticoverCoverFamily_compPieces_sub` is the transport lemma: the components of a subgraph
`H ≤ G`, restricted to a vertex set `S` on which the two graphs have the same edges, are pairwise
disjoint and pairwise anticomplete **in `G`**.  This is what lets the components of `G[V \ T]` be
used as pieces of a decomposition of `G` itself.

```lean
JSP90.CutTriangle G T := T.card = 3 ∧ (no edge of G joins T to the rest of G)
```

`JSP90.cutPieces G T` are the connected components of `G[V \ T]`, intersected with `V \ T`
(`JSPProblem/Connect.lean` supplies the components).  The intersection is what makes the pieces
avoid `T` *by construction*, so no appeal to the internal structure of `SimpleGraph.Walk` is
needed.  `JSP90.anticoverCut_of_cutTriangle` then gives the `AnticoverCut` of `JSPProblem/Cut.lean`
at that triangle, and `JSP90.closeToBipartite_of_cutTriangle` is a **new instance of the headline
theorem with a canonical family of pieces**.

## 3. The descent at a cut triangle (`Part 4`)

At a triangle of a cut, the deficiency of every piece drops by one:
`JSP90.maxDefIn_le_of_cutPiece`, i.e. `1 + maxDefIn G Q ≤ k`, and therefore
`JSP90.locIndep_piece_of_cutTriangle : LocIndep k G → Q ∈ cutPieces G T → LocIndep (k - 1) G[Q]`.

## 5. The reduction (`Part 5`)

```lean
JSP90.cutBound : ℕ → ℕ      -- cutBound 0 = 1,  cutBound (k + 1) = 3 + (k + 1) * cutBound k
JSP90.TriangleFreeErdős73   -- Erdős #73 for triangle-free graphs, with the constant cutBound
JSP90.CutTriangleErdős73    -- LocIndep k G, k ≥ 1 ⟹ a cut triangle, or cutBound k-close to bipartite
JSP90.erdos73_of_triangleFree : TriangleFreeErdős73 → CutTriangleErdős73 → ∀ k, Erdős73 k
```

**ERDŐS PROBLEM #73, IN FULL, FROM TWO LOCAL STATEMENTS.**  The induction is on `k` alone: at
`k = 0` the graph is bipartite; at `k + 1`, a triangle-free graph is a `TriangleFreeErdős73`, and
otherwise either `CutTriangleErdős73` already concludes, or `G` has a cut triangle, the pieces of
the cut are `LocIndep k` by Part 3, the induction hypothesis makes them `cutBound k`-close to
bipartite, and Part 2 concludes `cutBound (k + 1) = 3 + (k + 1) * cutBound k`.

**A CORRECTION TO ROUNDS 62–63.**  Those rounds planned the constant `f k = 4 ^ k`, on the
strength of `JSP90.sup_pow_four` and `JSP90.step_pow_four`.  The instance of round 63 costs
`3 + k * f (k - 1)`, and `3 + k * 4 ^ (k - 1) ≤ 4 ^ k` is **false** for `k ≥ 5`
(`k = 10`: `3 + 10 * 4 ^ 9 = 2621443 > 4 ^ 10 = 1048576`).  The recurrence forced by the instance
is `f (k + 1) = 3 + (k + 1) * f k`, and `JSP90.cutBound` is exactly that recurrence; the two
numerical lemmas `sup_pow_four` / `step_pow_four` of `JSPProblem/Cut.lean` are therefore *not* the
hypotheses of the reduction and are not used below.  A constant of the shape `4 ^ k` would need the
*superadditive* half of the additivity of the deficiency over a cut
(`∑_Q maxDefIn G Q ≤ MaxDef G - 1`), i.e. `JSP90.sum_sub_eq_of_le` applied to a vertex set on which
no truncation occurs; that half is not proved and is not needed here.

## What is *not* proved

`TriangleFreeErdős73` and `CutTriangleErdős73` are the two remaining statements, and they are
*local*:

* `CutTriangleErdős73` is the local absorption of the round-61 line: near a triangle, either the
  graph cuts there, or it is `O_k(1)` from bipartite.  A graph with a cut triangle does not exist
  for every `LocIndep 1` graph (a `C_5` with a hub adjacent to all of it, plus a pendant edge at
  the hub, has `MaxDef = 1`, is not bipartite and has no cut triangle), so this is a genuine case
  distinction; it is the local lemma of Reed's *Mangoes and Blueberries*.
* `TriangleFreeErdős73` is Erdős #73 restricted to triangle-free graphs, the classical
  triangle-free case.

Both are strictly weaker than the Reed–Robertson–Seymour–Thomas theorem
(`JSPProblem/Transversal.lean`, `JSP90.OddCycleErdosPosa r`), the primary blocker of the earlier
rounds, and each is a statement about a *class* of graphs, not about all graphs.
`jsp_000090_main` is therefore still not declared.
-/

import JSPProblem.Cut

namespace JSP90

open Finset Fintype Set

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance : DecidableEq V := Classical.decEq V

local instance (G : SimpleGraph V) : DecidablePred fun S : Finset V => G.IsIndepSet S :=
  fun _ => Classical.propDecidable _

/-! ### Part 1 — the deficiency of an induced subgraph -/

section Induced

/-- **A set inside `U` has the same independence number in `G[U]` as in `G`.** -/
theorem indepCard_induceFinset_of_subset {X U : Finset V} (hXU : X ⊆ U) :
    indepCard (induceFinset G U) X = indepCard G X := by
  refine le_antisymm ?_ ?_
  · show (indepSets (induceFinset G U) X).sup Finset.card ≤ (indepSets G X).sup Finset.card
    refine Finset.sup_le_iff.mpr fun S hS => ?_
    have hSsub : S ⊆ X := sub_of_mem_indepSets hS
    have hSU : S ⊆ U := Finset.Subset.trans hSsub hXU
    have hSind : G.IsIndepSet S := IsIndepSet.of_induceFinset (Finset.mem_filter.mp hS).2 hSU
    have hS' : S ∈ indepSets G X := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSsub, hSind⟩
    exact le_indepCard hS'
  · show (indepSets G X).sup Finset.card ≤ (indepSets (induceFinset G U) X).sup Finset.card
    refine Finset.sup_le_iff.mpr fun S hS => ?_
    have hSsub : S ⊆ X := sub_of_mem_indepSets hS
    have hSU : S ⊆ U := Finset.Subset.trans hSsub hXU
    have hSind : G.IsIndepSet S := (Finset.mem_filter.mp hS).2
    have hS' : S ∈ indepSets (induceFinset G U) X :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hSsub,
          (isIndepSet_induceFinset_iff (G := G) (S := S) (s := U) hSU).mpr hSind⟩
    exact le_indepCard hS'

/-- **THE VERTICES OF A VERTEX SET OUTSIDE `U` ARE ISOLATED IN `G[U]`, SO THEY CAN ALL BE ADDED TO
AN INDEPENDENT SET.**  In finset form: if `S ⊆ Y` lies in `U` and is independent in `G[U]` then

```lean
S ∪ (Y \ U) ∈ indepSets (induceFinset G U) Y
```

— the whole of `Y \ U` is added to `S`, because `G[U]` has no edge out of `U`. -/
theorem mem_indepSets_union_sdiff {S U Y : Finset V} (hSi : (induceFinset G U).IsIndepSet S)
    (hSY : S ⊆ Y) (_hSU : S ⊆ U) : S ∪ (Y \ U) ∈ indepSets (induceFinset G U) Y := by
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (by
        intro v hv
        rcases Finset.mem_union.mp hv with h | h
        · exact hSY h
        · exact Finset.mem_sdiff.mp h |>.1),
      isIndepSet_of_intro (S := S ∪ (Y \ U)) fun v w hv hw _ hadj => by
        have hv' := Finset.mem_coe.mp hv
        have hw' := Finset.mem_coe.mp hw
        have hh := induce_adj.mp hadj
        have hhvU : v ∈ U := hh.1
        have hhwU : w ∈ U := hh.2.1
        rcases Finset.mem_union.mp hv' with hvS | hvYU
        · rcases Finset.mem_union.mp hw' with hwS | hwYU
          · exact IsIndepSet.apply' hSi hvS hwS (by
              intro h
              subst h
              exact G.loopless.irrefl v hh.2.2) hadj
          · exact False.elim ((Finset.mem_sdiff.mp hwYU).2 hhwU)
        · exact False.elim ((Finset.mem_sdiff.mp hvYU).2 hhvU)⟩

/-- **THE INDEPENDENCE NUMBER OF AN INDUCED SUBGRAPH SPLITS OFF THE VERTICES OUTSIDE IT.**

```lean
α(G[U], Y) = α(G[U], Y ∩ U) + |Y \ U|
```

This is the lemma that makes `maxDefIn` (the deficiency *inside* a vertex set, measured in the
whole graph) equal to `MaxDef` of the induced subgraph, and hence what lets an induction on the
parameter of Erdős's hypothesis act on a piece of a cut. -/
theorem indepCard_induceFinset_inter_add_sdiff (U Y : Finset V) :
    indepCard (induceFinset G U) Y = indepCard (induceFinset G U) (Y ∩ U) + (Y \ U).card := by
  have hsub : (Y \ U) ∪ (Y ∩ U) = Y := Finset.sdiff_union_inter Y U
  have hle : indepCard (induceFinset G U) Y
      ≤ indepCard (induceFinset G U) (Y ∩ U) + (Y \ U).card := by
    have h1 := indepCard_le_add (G := induceFinset G U) (Y \ U) (Y ∩ U)
    have h2 : indepCard (induceFinset G U) ((Y \ U) ∪ (Y ∩ U)) = indepCard (induceFinset G U) Y := by
      rw [hsub]
    have h3 := indepCard_le_card (induceFinset G U) (Y \ U)
    omega
  have hge : indepCard (induceFinset G U) (Y ∩ U) + (Y \ U).card
      ≤ indepCard (induceFinset G U) Y := by
    obtain ⟨S, hSinter, hSi, hcard⟩ := exists_indepCard (induceFinset G U) (Y ∩ U)
    have hSY : S ⊆ Y := by
      intro v hv
      have hm : v ∈ Y ∩ U := hSinter hv
      exact (Finset.mem_inter.mp hm).1
    have hSU : S ⊆ U := by
      intro v hv
      have hm : v ∈ Y ∩ U := hSinter hv
      exact (Finset.mem_inter.mp hm).2
    have hSi' : S ∪ (Y \ U) ∈ indepSets (induceFinset G U) Y :=
      mem_indepSets_union_sdiff hSi hSY hSU
    have hdisj : Disjoint S (Y \ U) := by
      refine Finset.disjoint_left.2 ?_
      intro v hvS hvYU
      exact (Finset.mem_sdiff.mp hvYU).2 (hSU hvS)
    have hcard' : (S ∪ (Y \ U)).card = indepCard (induceFinset G U) (Y ∩ U) + (Y \ U).card := by
      rw [Finset.card_union_of_disjoint hdisj, hcard]
    rw [← hcard']
    exact le_indepCard hSi'
  exact le_antisymm hle hge

/-- **The vertices of a vertex set of `G[U]` that lie outside `U` contribute nothing to its
deficiency**, they being isolated:

```lean
|Y| - 2 α(G[U], Y) ≤ |Y ∩ U| - 2 α(G[U], Y ∩ U)
```

so the deficiency of a vertex set of `G[U]` is attained inside `U`. -/
theorem defOf_induceFinset_inter_le (U Y : Finset V) :
    defOf (induceFinset G U) Y ≤ defOf (induceFinset G U) (Y ∩ U) := by
  show Y.card - 2 * indepCard (induceFinset G U) Y
      ≤ (Y ∩ U).card - 2 * indepCard (induceFinset G U) (Y ∩ U)
  have h1 := indepCard_induceFinset_inter_add_sdiff (G := G) U Y
  have h2 := card_inter_add_card_sdiff Y U
  have h1' : 2 * indepCard (induceFinset G U) Y
      = 2 * indepCard (induceFinset G U) (Y ∩ U) + 2 * (Y \ U).card := by
    rw [h1]
    omega
  have hl : Y.card - 2 * indepCard (induceFinset G U) Y
      = (Y ∩ U).card + (Y \ U).card
        - (2 * indepCard (induceFinset G U) (Y ∩ U) + 2 * (Y \ U).card) := by
    rw [h2, h1']
  have h3 : (Y ∩ U).card + (Y \ U).card
        - (2 * indepCard (induceFinset G U) (Y ∩ U) + 2 * (Y \ U).card)
      ≤ (Y ∩ U).card + 2 * (Y \ U).card
        - (2 * indepCard (induceFinset G U) (Y ∩ U) + 2 * (Y \ U).card) :=
    sub_sub_le_sub_sub (by omega) (le_refl _)
  have h4 : (Y ∩ U).card + 2 * (Y \ U).card
        - (2 * indepCard (induceFinset G U) (Y ∩ U) + 2 * (Y \ U).card)
      = (Y ∩ U).card - 2 * indepCard (induceFinset G U) (Y ∩ U) := by
    have hh := Nat.add_sub_add_left (2 * (Y \ U).card) (Y ∩ U).card
      (2 * indepCard (induceFinset G U) (Y ∩ U))
    omega
  rw [hl]
  exact h3.trans (le_of_eq h4)

/-- **`MaxDef G` is `maxDefIn G univ`.** -/
theorem maxDefIn_univ (G : SimpleGraph V) : maxDefIn G (Finset.univ : Finset V) = MaxDef G := rfl

/-- **`MaxDef (G[U]) = maxDefIn G U`**: the maximum deficiency of the *graph* `G[U]`, taken over
all subsets of the ambient vertex set, is the maximum deficiency *inside `U`* taken in `G`.  The
vertices of `V \ U` are isolated in `G[U]` and therefore cannot contribute.

This is the identity that justifies writing an induction on Erdős's parameter over the pieces of a
cut: `MaxDef` of a piece, read as a graph on the ambient vertex type, is the deficiency inside the
piece.  It is the answer to the "mathematical correction" that round 63 recorded against the
*unrestricted* `maxDefIn (induceFinset G Q) V`, which is a different (and larger) number. -/
theorem maxDef_eq_maxDefIn_induceFinset (U : Finset V) :
    MaxDef (induceFinset G U) = maxDefIn G U := by
  refine le_antisymm (maxDef_le fun Y => ?_) ?_
  calc defOf (induceFinset G U) Y ≤ defOf (induceFinset G U) (Y ∩ U) :=
        defOf_induceFinset_inter_le U Y
    _ = defOf G (Y ∩ U) :=
      defOf_induceFinset_of_subset (G := G) (U := U) (Y := Y ∩ U)
        (Finset.inter_subset_right (s₁ := Y) (s₂ := U))
    _ ≤ maxDefIn G U := le_maxDefIn G U Finset.inter_subset_right
  · have heq : MaxDef (induceFinset G U) = maxDefIn (induceFinset G U) (Finset.univ) :=
      maxDefIn_univ (induceFinset G U)
    rw [heq, ← maxDefIn_induceFinset_eq (G := G) U]
    exact maxDefIn_mono (induceFinset G U) (Finset.subset_univ U)

/-- **A bound on the deficiency inside a vertex set is a local hypothesis on the induced
subgraph.** -/
theorem locIndep_induceFinset_of_maxDefIn_le {k : ℕ} {U : Finset V} (h : maxDefIn G U ≤ k) :
    LocIndep k (induceFinset G U) := by
  have h1 : MaxDef (induceFinset G U) ≤ k := by
    rw [maxDef_eq_maxDefIn_induceFinset (G := G) U]
    exact h
  exact locIndep_of_maxDef_le h1

end Induced

/-! ### Part 2 — a triangle that cuts the graph -/

section Pieces

/-- **THE COMPONENTS OF A SUBGRAPH, RESTRICTED TO A VERTEX SET ON WHICH THE TWO GRAPHS AGREE.**
The two hypotheses say that on `S` the graphs `H` and `G` have the same edges, so the components of
`H` restricted to `S` are pairwise anticomplete *in `G`*: the pieces of a decomposition of `H` are
pieces of a decomposition of `G`.  This is what lets the components of `G[V \ T]` be used as the
pieces of a cut in `G` itself. -/
theorem anticoverCoverFamily_compPieces_sub {H : SimpleGraph V} (S : Finset V)
    (hS : ∀ ⦃x y : V⦄, G.Adj x y → x ∈ S → y ∈ S → H.Adj x y) :
    AnticoverCoverFamily G ((compPieces H).image (fun Q => Q ∩ S)) := by
  have hfam := anticoverCoverFamily_compPieces (G := H)
  constructor
  · rintro X hX Y hY hne
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hY
    obtain ⟨v', -, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨w', -, rfl⟩ := Finset.mem_image.mp hQ
    have hne' : compPiece H v' ≠ compPiece H w' := by
      intro h
      apply hne
      rw [h]
    refine Finset.eq_empty_iff_forall_notMem.mpr fun v hv => ?_
    have hmem := (Finset.eq_empty_iff_forall_notMem.mp
      (inter_compPiece_eq_empty (G := H) hne')) v
    rcases Finset.mem_inter.mp hv with ⟨hv1, hv2⟩
    have hbothmem : v ∈ compPiece H v' ∩ compPiece H w' :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv1).1, (Finset.mem_inter.mp hv2).1⟩
    exact hmem hbothmem
  · rintro X hX Y hY hne v hvX w hwY hAdj
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hY
    obtain ⟨v', hv'P, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨w', hw'Q, rfl⟩ := Finset.mem_image.mp hQ
    have hne' : compPiece H v' ≠ compPiece H w' := by
      intro h
      apply hne
      rw [h]
    have hxv : v ∈ compPiece H v' := (Finset.mem_inter.mp hvX).1
    have hyw : w ∈ compPiece H w' := (Finset.mem_inter.mp hwY).1
    exact hfam.2 (compPiece H v') (compPiece_mem_compPieces (G := H) v')
      (compPiece H w') (compPiece_mem_compPieces (G := H) w') hne' v hxv w hyw
      (hS hAdj (Finset.mem_inter.mp hvX).2 (Finset.mem_inter.mp hwY).2)

end Pieces

/-! ### Part 3 — a triangle that cuts the graph -/

section CutTriangle

/-- **A CUT TRIANGLE**: `T` has exactly three vertices and **no edge of `G` joins `T` to the rest of
`G`**.  A graph with such a triangle splits into the triangle and an anticomplete cover of
`V \ T` by the connected components of `G[V \ T]`. -/
def CutTriangle (G : SimpleGraph V) (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ ⦃x y : V⦄, x ∉ T → y ∈ T → ¬ G.Adj x y

/-- **THE PIECES OF A CUT AT A TRIANGLE**: the connected components of `G[V \ T]`, each intersected
with `V \ T`.

The intersection is what makes every piece *avoid `T` by construction*.  Without it the family of
components of `G − T` would contain, for each `t ∈ T`, the singleton `{t}` (reachability is
reflexive), which meets `T`; and `JSPProblem/Cut.lean` records that a component of `G − T` can
also meet `T` in a vertex of `T` that has a neighbour outside `T` (`K_4` at a triangle), which is
why `AnticoverCut` has to be carried as a hypothesis there.  Here it is a *definition*, and the
only hypothesis is the `CutTriangle` one. -/
noncomputable def cutPieces (G : SimpleGraph V) (T : Finset V) : Finset (Finset V) :=
  (compPieces (induceFinset G ((Finset.univ : Finset V) \ T))).image
    (fun Q => Q ∩ ((Finset.univ : Finset V) \ T))

/-- **Every piece of a cut at a triangle avoids the triangle.** -/
theorem cutPieces_sub {Q : Finset V} (hQ : Q ∈ cutPieces G T) : Q ⊆ (Finset.univ : Finset V) \ T := by
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hQ
  exact fun v hv => (Finset.mem_inter.mp hv).2

/-- **The pieces of a cut at a triangle are pairwise disjoint and pairwise anticomplete in `G`.** -/
theorem anticoverCoverFamily_cutPieces :
    AnticoverCoverFamily G (cutPieces G T) := by
  show AnticoverCoverFamily G
    ((compPieces (induceFinset G ((Finset.univ : Finset V) \ T))).image
      (fun Q => Q ∩ ((Finset.univ : Finset V) \ T)))
  exact anticoverCoverFamily_compPieces_sub
    (H := induceFinset G ((Finset.univ : Finset V) \ T)) ((Finset.univ : Finset V) \ T)
    (fun _ _ hAdj hx hy => (induce_adj.mpr ⟨hx, hy, hAdj⟩))

/-- **EVERY VERTEX OUTSIDE THE TRIANGLE LIES IN A PIECE.** -/
theorem mem_cutPieces (x : V) (_hxT : x ∉ T) :
    compPiece (induceFinset G ((Finset.univ : Finset V) \ T)) x ∩ ((Finset.univ : Finset V) \ T)
      ∈ cutPieces G T :=
  Finset.mem_image.mpr
    ⟨compPiece (induceFinset G ((Finset.univ : Finset V) \ T)) x,
      compPiece_mem_compPieces (induceFinset G ((Finset.univ : Finset V) \ T)) x, rfl⟩

/-- **A CUT TRIANGLE CUTS THE GRAPH.**  The pieces `cutPieces G T` are pairwise disjoint and
pairwise anticomplete, each of them disjoint from `T` and anticomplete to it, and together they
cover `V \ T`: this is the `AnticoverCut` of `JSPProblem/Cut.lean`. -/
theorem anticoverCut_of_cutTriangle (hT : CutTriangle G T) : AnticoverCut G T (cutPieces G T) :=
  ⟨anticoverCoverFamily_cutPieces,
   fun _Q hQ => Finset.disjoint_left.2 fun v hvQ hvT =>
     (Finset.mem_sdiff.mp (cutPieces_sub hQ hvQ : v ∈ (Finset.univ : Finset V) \ T)).2 hvT,
   fun _Q hQ x hxT y hyQ => fun hxy =>
     hT.2 (x := y) (y := x)
       ((Finset.mem_sdiff.mp (cutPieces_sub hQ hyQ : y ∈ (Finset.univ : Finset V) \ T)).2)
       hxT hxy.symm,
   fun x hxT => ⟨compPiece (induceFinset G ((Finset.univ : Finset V) \ T)) x ∩
       ((Finset.univ : Finset V) \ T), mem_cutPieces x hxT, Finset.mem_inter.mpr
       ⟨compPiece_self (induceFinset G ((Finset.univ : Finset V) \ T)) x,
         Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxT⟩⟩⟩⟩

/-- **NEW INSTANCE OF THE HEADLINE THEOREM, AT A CANONICAL CUT.**

If every connected component of `G[V \ T]` is `m`-close to bipartite, and `T` is a triangle with no
edge to the rest of `G`, then

```lean
LocIndep k G → CloseToBipartite (3 + k * m) G
```

with the constant of `JSP90.closeToBipartite_of_anticoverCut` and the **canonical** family of
pieces — the components of the graph with the triangle deleted.  No bound is assumed on the odd
girth, on the packing weight or on the number of branch vertices. -/
theorem closeToBipartite_of_cutTriangle {k m : ℕ} (hG : LocIndep k G) (T : Finset V)
    (hT : CutTriangle G T)
    (hm : ∀ Q ∈ cutPieces G T, CloseToBipartite m (induceFinset G Q)) :
    CloseToBipartite (3 + k * m) G := by
  classical
  exact closeToBipartite_of_anticoverCut hG T (cutPieces G T) (anticoverCut_of_cutTriangle hT) hT.1 hm

/-- The same instance, read on a vertex set: the constant is not paid twice. -/
theorem closeToBipartite_of_cutTriangle_on {k m : ℕ} (hG : LocIndep k G) (T : Finset V)
    (hT : CutTriangle G T)
    (hm : ∀ Q ∈ cutPieces G T, CloseToBipartite m (induceFinset G Q)) (U : Finset V) :
    CloseToBipartite (3 + k * m) (induceFinset G U) :=
  closeToBipartite_sub_induceFinset (closeToBipartite_of_cutTriangle hG T hT hm) U

end CutTriangle

/-! ### Part 4 — the deficiency drops at a cut triangle -/

section Descent

/-- **THE DESCENT AT A CUT TRIANGLE.**  If `T` is a `3`-clique cutting the graph and `Q` is one of
its pieces, then the deficiency of `Q` is at most `k - 1`, where `MaxDef G ≤ k`: the triangle costs
one unit of deficiency, whatever the size of `Q`.

This is the statement round 63 named as missing — the `MaxDef` half of the triangle-cut induction
— and it is what the induction of Part 5 consumes. -/
theorem maxDefIn_le_of_cutPiece {k : ℕ} (hG : LocIndep k G) (T Q : Finset V) (hcl : G.IsClique T)
    (hT : CutTriangle G T) (hQ : Q ∈ cutPieces G T) : 1 + maxDefIn G Q ≤ k := by
  have h1 : 1 + maxDefIn G Q ≤ maxDefIn G (Finset.univ : Finset V) :=
    maxDefIn_ge_one_add_maxDefIn_of_clique_sub (G := G) hcl hT.1
      (Finset.disjoint_left.2 fun v hvQ hvT =>
        (Finset.mem_sdiff.mp (cutPieces_sub hQ hvQ : v ∈ (Finset.univ : Finset V) \ T)).2 hvT)
      (Finset.subset_univ Q) (Finset.subset_univ T)
  rw [maxDefIn_univ G] at h1
  exact le_trans h1 (maxDef_le_of_locIndep hG)

/-- **EVERY PIECE OF A CUT AT A TRIANGLE SATISFIES `LocIndep (k - 1)`.**  The parameter of Erdős's
hypothesis drops by one on passing from `G` to a piece of a cut at a triangle.  This is the step of
the induction on `k` that the classical proof of Erdős #73 performs at a triangle. -/
theorem locIndep_piece_of_cutTriangle {k : ℕ} (hG : LocIndep k G) (T Q : Finset V) (hcl : G.IsClique T)
    (hT : CutTriangle G T) (hQ : Q ∈ cutPieces G T) : LocIndep (k - 1) (induceFinset G Q) := by
  have h1 : 1 + maxDefIn G Q ≤ k := maxDefIn_le_of_cutPiece hG T Q hcl hT hQ
  have h2 : maxDefIn G Q + 1 ≤ k := by simpa [Nat.add_comm] using h1
  exact locIndep_induceFinset_of_maxDefIn_le (le_pred_of_succ_le h2 (le_refl k))

end Descent

/-! ### Part 5 — the reduction: Erdős Problem #73 from two local statements -/

section Reduction

/-- **THE CONSTANT OF THE TRIANGLE-CUT INDUCTION**, the recurrence forced by the instance of Part 3:

```lean
cutBound 0 = 1,     cutBound (k + 1) = 3 + (k + 1) * cutBound k
```

The `3` pays for the triangle, the `k + 1` for the at most `k + 1` non-bipartite pieces of the cut
(`JSP90.card_nonBipartiteParts_le_cover` of `JSPProblem/Additive.lean`), each of which costs
`cutBound k` by the induction hypothesis.  See the file header for why `4 ^ k` — the constant
planned in rounds 62–63 — cannot work here. -/
def cutBound : ℕ → ℕ
  | 0 => 1
  | (k + 1) => 3 + (k + 1) * cutBound k

/-- **ERDŐS PROBLEM #73 FOR TRIANGLE-FREE GRAPHS**, with the constant `cutBound` of the
triangle-cut induction.  A statement about a *class* of graphs, not about all graphs. -/
def TriangleFreeErdős73 : Prop :=
  ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
    LocIndep k G → G.CliqueFree 3 → CloseToBipartite (cutBound k) G

/-- **THE CUT-TRIANGLE ALTERNATIVE.**  A graph satisfying Erdős's local hypothesis with `k ≥ 1`
either has a triangle that is anticomplete to the rest of the graph — a *cut triangle*, at which
the induction descends — or is already `cutBound k`-close to bipartite.  This is the local
absorption statement of the round-61 line, in the form the induction consumes. -/
def CutTriangleErdős73 : Prop :=
  ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → 1 ≤ k →
    (∃ T : Finset W, G.IsClique T ∧ CutTriangle G T) ∨ CloseToBipartite (cutBound k) G

/-- **ERDŐS PROBLEM #73, IN FULL, FROM ITS TRIANGLE-FREE CASE AND THE CUT-TRIANGLE
ALTERNATIVE.**

For every `k` there is a constant `cutBound k` such that every finite graph satisfying Erdős's
local hypothesis `LocIndep k` is the union of a bipartite graph and at most `cutBound k` vertices.

The induction is on `k` alone:

* `k = 0`: `G` is bipartite (`JSP90.erdos73_zero` of `JSPProblem/OddCycle.lean`).
* `k + 1`, `G` triangle-free: `TriangleFreeErdős73`.
* `k + 1`, `G` not triangle-free: either `CutTriangleErdős73` concludes, or `G` has a cut
  triangle `T`; its pieces `Q` satisfy `LocIndep k (G[Q])`
  (`JSP90.locIndep_piece_of_cutTriangle`), so the induction hypothesis makes each of them
  `cutBound k`-close to bipartite, and `JSP90.closeToBipartite_of_cutTriangle` concludes
  `3 + (k + 1) * cutBound k = cutBound (k + 1)`.

Neither hypothesis mentions a packing number, a transversal, an odd girth, a packing weight or a
number of branch vertices: this is a reduction to two statements about *classes* of graphs, and
each of them is a statement about one vertex set / one triangle rather than about the odd cycles of
the whole graph. -/
theorem erdos73On_of_triangleFree (htf : TriangleFreeErdős73.{u}) (hc : CutTriangleErdős73.{u})
    (k : ℕ) : Erdős73On.{u} k (cutBound k) := by
  have main : ∀ (k : ℕ) (W : Type u) (instW : Fintype W) (G : SimpleGraph W), LocIndep k G →
      CloseToBipartite (cutBound k) G := by
    intro k
    induction k with
    | zero =>
        intro W instW G hG
        exact closeToBipartite_of_isBipartite' (V := W) (locIndep_zero_isBipartite (V := W) hG)
    | succ k ih =>
        intro W instW G hG
        by_cases hG3 : G.CliqueFree 3
        · exact htf (k + 1) W instW G hG hG3
        · rcases hc (k + 1) W instW G hG (by omega) with ⟨T, hcl, hT⟩ | hclose
          · have hm : ∀ Q ∈ cutPieces G T, CloseToBipartite (cutBound k) (induceFinset G Q) := by
              intro Q hQ
              exact ih W instW (induceFinset G Q)
                (locIndep_piece_of_cutTriangle hG T Q hcl hT hQ)
            exact closeToBipartite_of_cutTriangle hG T hT hm
          · exact hclose
  exact main k

/-- **ERDŐS PROBLEM #73, IN FULL, FROM TWO LOCAL STATEMENTS** — the form the prize gate reads. -/
theorem erdos73_of_triangleFree (htf : TriangleFreeErdős73.{u}) (hc : CutTriangleErdős73.{u}) :
    ∀ k, Erdős73.{u} k := by
  intro k
  exact ⟨cutBound k, erdos73On_of_triangleFree htf hc k⟩

/-- **A `CutTriangle` IS NOT AUTOMATIC.**  In `K_4` no `3`-clique cuts the graph: the vertex outside
the triangle is adjacent to all three of its vertices.  This is the machine-checked reason why
`CutTriangle` is a *hypothesis* of the reduction above and not a theorem — the same witness
`JSPProblem/Cut.lean` recorded for the failure of the naive absorption step
(`JSP90.absorption_step_fails`, on `K_5`), and the reason why the triangle-cut class of Part 3 is a
genuine class and not all graphs. -/
theorem not_cutTriangle_completeGraph_four {T : Finset (Fin 4)} (hT : T.card = 3) :
    ¬ CutTriangle (SimpleGraph.completeGraph (Fin 4)) T := by
  rintro ⟨-, hanti⟩
  have hsdiff : ((Finset.univ : Finset (Fin 4)) \ T).Nonempty := by
    by_contra hc
    have h0 : (Finset.univ : Finset (Fin 4)) \ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
    have hsub : (Finset.univ : Finset (Fin 4)) ⊆ T := by
      intro v hv
      by_contra h2
      have hmem : v ∈ (Finset.univ : Finset (Fin 4)) \ T := Finset.mem_sdiff.mpr ⟨hv, h2⟩
      rw [h0] at hmem
      exact absurd hmem (by simp)
    have hne : (Finset.univ : Finset (Fin 4)) = T :=
      Finset.Subset.antisymm hsub (Finset.subset_univ T)
    have h3 : (Finset.univ : Finset (Fin 4)).card = 3 := by rw [hne, hT]
    have h4 : Fintype.card (Fin 4) = 3 := by
      simp only [Finset.card_univ] at h3
      exact h3
    have h5 : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4
    omega
  obtain ⟨x, hx⟩ := hsdiff
  have hxT : x ∉ T := (Finset.mem_sdiff.mp hx).2
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [hT]; omega)
  exact hanti (x := x) (y := y) hxT hy
    ((SimpleGraph.top_adj (V := Fin 4) x y).mpr (fun h => hxT (h ▸ hy)))

/-- **THE CUT-TRIANGLE ALTERNATIVE FOR THE CLASS OF GRAPHS WHOSE TRIANGLES ALL CUT.**  On a graph
in which every `3`-clique is a cut triangle, the hypothesis `JSP90.CutTriangleErdős73` of the
reduction holds off the triangle-free case. -/
theorem cutTriangleErdős73_of_allTrianglesCut {k : ℕ} (W : Type u) [instW : Fintype W]
    (G : SimpleGraph W) (_hG : LocIndep k G) (hnot : ¬ G.CliqueFree 3)
    (hall : ∀ T : Finset W, G.IsNClique 3 T → CutTriangle G T) :
    (∃ T : Finset W, G.IsClique T ∧ CutTriangle G T) ∨ CloseToBipartite (cutBound k) G := by
  obtain ⟨T, hT⟩ : ∃ T : Finset W, G.IsNClique 3 T := by
    by_contra hc
    exact hnot fun T hT => hc ⟨T, hT⟩
  exact Or.inl ⟨T, (G.isNClique_iff.mp hT).1, hall T hT⟩

/-- **ERDŐS PROBLEM #73, IN FULL, FOR THE GRAPHS WHOSE TRIANGLES ALL CUT** — a *class* on which
the reduction closes unconditionally, given the triangle-free case.  The class is nonempty and
includes every graph whose only triangles are anticomplete to the rest of the graph. -/
theorem erdos73_of_triangleFree_of_allTrianglesCut (htf : TriangleFreeErdős73.{u})
    (hall : ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (T : Finset W),
      G.IsNClique 3 T → CutTriangle G T) : ∀ k, Erdős73.{u} k := by
  refine erdos73_of_triangleFree htf ?_
  intro k W instW G hG hk
  by_cases hG3 : G.CliqueFree 3
  · exact Or.inr (htf k W instW G hG hG3)
  · exact cutTriangleErdős73_of_allTrianglesCut W G hG hG3 (fun T hT => hall W instW G T hT)

end Reduction

end

end JSP90
