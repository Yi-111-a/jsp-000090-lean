/-
# JSP-000090 — the descent at a triangle needs no separation, and Erdős Problem #73 is
# EQUIVALENT to its triangle-free case

This file is the **seventeenth attack family**.  It removes the second of the two statements that
`JSPProblem/CutTriangle.lean` (round 64) left open.

## What round 64 had, and what it did not need

Round 64 proved the reduction

```lean
JSP90.erdos73_of_triangleFree : TriangleFreeErdős73 → CutTriangleErdős73 → ∀ k, Erdős73 k
```

with two hypotheses, and it recorded both as blockers.  Both came from the *same* place: the
`AnticoverCut` structure of `JSPProblem/Cut.lean`,

```lean
AnticoverCut G T 𝒬 = AnticoverCoverFamily G 𝒬 ∧ (pieces disjoint from T) ∧ (pieces ANTICOMPLETE
  to T) ∧ (pieces cover V \ T)
```

and in particular from the **anticompleteness of the pieces to `T`**, which is exactly what
`JSP90.CutTriangle G T` supplies and which a component of `G − T` need not satisfy (`K_4` at a
triangle is the witness, `JSP90.not_cutTriangle_completeGraph_four`).

Re-reading the proof of `JSP90.closeToBipartite_of_anticoverCut` field by field, the third field of
`AnticoverCut` is used in **exactly one place**: the `Anticover` structure between `T ∪ NN` and its
complement, which the final step feeds to `JSP90.closeToBipartite_of_anticover`.  Everything
combinatorial — the counting of the non-bipartite pieces, the choice of one transversal per
non-bipartite piece, and the bipartite character of the residue — uses only that the pieces are
pairwise disjoint, pairwise anticomplete, covered, and each piece's own bipartiteness.

**Both requirements turn out to be avoidable, and the round proves it:**

* the descent.  `JSP90.maxDefIn_ge_one_add_maxDefIn_of_clique` (`JSPProblem/Cut.lean`) already only
  asks for `Disjoint U T`; no separation is used anywhere in it, and Part 1 below repackages it as
  `JSP90.maxDefIn_add_one_le_maxDef_of_triangle` (and, in the form that explains the arithmetic,
  `JSP90.maxDefIn_add_card_le_maxDef_add_two_of_clique`: *a clique of size `t` costs `t − 2` units of
  deficiency off any disjoint vertex set*).  Round 59 needed *separation*, round 64 needed the cut;
  only disjointness is used.
* the final step.  Part 2 replaces the `Anticover` recombination by the direct statement that the
  residue `G[V \ (T ∪ Z)]` is bipartite, whose proof is the pigeonhole step: an odd cycle of `G`
  avoiding `T` and covered by pairwise anticomplete pieces lies in a **single** piece
  (`JSP90.isOddCycle_sub_anticoverCover`), where it contradicts that piece's bipartiteness.  In
  fact the pieces then need not even be disjoint from `T`, and `T` need not be a clique — only
  `| T | = 3` is used, because the whole of `T` is deleted.

## The consequence: ONE statement, not two

```lean
JSP90.TriangleFreeOnly                     -- Erdős #73 for triangle-free graphs
JSP90.erdos73_iff_triangleFreeOnly : (∀ k, Erdős73 k) ↔ TriangleFreeOnly
JSP90.erdos73_of_triangleFreeOnly         -- Erdős #73, in full, from the triangle-free case alone
JSP90.cutTriangleErdős73_of_triangleFreeOnly -- round 64's second statement is now a THEOREM
```

The induction is on `k` alone, with the constant `JSP90.cutBound` of round 64, which is forced:

* `k = 0`: `G` is bipartite (`JSP90.erdos73_zero`).
* `k + 1`, `G` triangle-free: `TriangleFreeOnly`.
* `k + 1`, `G` not triangle-free: take **any** triangle `T`.  Its pieces — the connected components
  of `G − T` — are pairwise disjoint, pairwise anticomplete and cover `V \ T` with no hypothesis at
  all (`JSP90.anticoverCoverFamily_cutPieces`), and each satisfies `LocIndep k`
  (`JSP90.locIndep_piece_of_triangle`, by disjointness alone), hence `cutBound k`-close to bipartite
  by the induction hypothesis, and `JSP90.closeToBipartite_of_triangle` concludes
  `3 + (k + 1) * cutBound k = cutBound (k + 1)`.

So **`JSP90.CutTriangleErdős73` is discharged**: the local absorption statement of round 64, the one
whose counterexample (a `C_5` with a hub and a pendant edge: `MaxDef = 1`, not bipartite, no cut
triangle) made it look like a genuine case distinction, is a *consequence* of the triangle-free
case.  What remains is the single classical statement of Erdős #73 for triangle-free graphs, and
`JSP90.OddCycleErdosPosa r` of `JSPProblem/Transversal.lean` behind it.

## New instances of the headline theorem

* `JSP90.closeToBipartite_of_pieces` — the composition over a cut at a triangle with the
  anticompleteness to `T` **dropped** (rounds 63–64 needed it): a new, weaker hypothesis, the same
  constant `3 + k * m`, no bound on the odd girth, packing weight or number of branch vertices;
* `JSP90.closeToBipartite_of_triangle` — the same instance at the **canonical** family of pieces
  (the components of `G − T`) and at an **arbitrary** triangle, with no `CutTriangle` hypothesis;
* `JSP90.descent_tight` — **the descent of Part 1 is tight**: on the sharp witness `kTriangles k`
  (deficiency exactly `k`) a single triangle is disjoint from a vertex set of deficiency exactly
  `k − 1`.  The induction on `k` really does drop by exactly one unit per triangle.

## What is *not* proved

`JSP90.TriangleFreeOnly` — Erdős #73 for triangle-free graphs, constant `cutBound`.  This is a
statement about a class of graphs and is the whole remaining content of JSP-000090;
`jsp_000090_main` is therefore still not declared.
-/

import JSPProblem.Attach

namespace JSP90

open Finset Fintype Set

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance : DecidableEq V := Classical.decEq V

local instance (G : SimpleGraph V) : DecidablePred fun S : Finset V => G.IsIndepSet S :=
  fun _ => Classical.propDecidable _

/-! ### Part 1 — the descent at a triangle, with no separation hypothesis -/

section Descent

/-- **THE DESCENT AT A TRIANGLE, WITH NO SEPARATION HYPOTHESIS.**  If `T` is a triangle of `G` and
`X` is *any* vertex set disjoint from it — edges between `T` and `X` are not excluded — then

```lean
maxDefIn G X + 1 ≤ MaxDef G .
```

The triangle costs one unit of deficiency whatever the size of `X` and however `X` hangs off the
triangle.  This is the hypothesis-free form of the descent of `JSPProblem/OffCycle.lean`
(`1 + MaxDef (G[X]) ≤ MaxDef G` for `X` *separated* from an odd cycle) and of
`JSPProblem/CutTriangle.lean` Part 4 (the same, at a *cut* triangle). -/
theorem maxDefIn_add_one_le_maxDef_of_triangle {T X : Finset V} (hcl : G.IsClique T)
    (hcard : T.card = 3) (hdisj : Disjoint T X) : maxDefIn G X + 1 ≤ MaxDef G := by
  have h1 : 1 + maxDefIn G X ≤ maxDefIn G (X ∪ T) :=
    maxDefIn_ge_one_add_maxDefIn_of_clique hcl hcard
      (Finset.disjoint_left.mpr fun v hvX hvT => (Finset.disjoint_left.mp hdisj) hvT hvX)
  have h2 : maxDefIn G (X ∪ T) ≤ MaxDef G := by
    rw [← maxDefIn_univ G]
    exact maxDefIn_mono G (Finset.subset_univ _)
  rw [Nat.add_comm] at h1
  exact le_trans h1 h2

/-- The same descent, read on the induced graph: the deficiency of `G[X]` drops by one at every
triangle disjoint from `X`. -/
theorem maxDef_add_one_le_maxDef_of_triangle {T X : Finset V} (hcl : G.IsClique T)
    (hcard : T.card = 3) (hdisj : Disjoint T X) :
    MaxDef (induceFinset G X) + 1 ≤ MaxDef G := by
  rw [maxDef_eq_maxDefIn_induceFinset (U := X)]
  exact maxDefIn_add_one_le_maxDef_of_triangle hcl hcard hdisj

/-- **EVERY VERTEX SET DISJOINT FROM A TRIANGLE SATISFIES ERDŐS'S HYPOTHESIS WITH THE PARAMETER
DROPPED BY ONE.**  The induction step of the classical proof of Erdős #73 at a triangle, in the
form the reduction of Part 4 consumes. -/
theorem locIndep_of_disjoint_triangle {k : ℕ} (hG : LocIndep k G) {T X : Finset V}
    (hcl : G.IsClique T) (hcard : T.card = 3) (hdisj : Disjoint T X) :
    LocIndep (k - 1) (induceFinset G X) :=
  locIndep_induceFinset_of_maxDefIn_le
    (le_pred_of_succ_le (maxDefIn_add_one_le_maxDef_of_triangle hcl hcard hdisj)
      (maxDef_le_of_locIndep hG))

/-- **A CLIQUE COSTS `| T | - 2` UNITS OF DEFICIENCY OFF ANY DISJOINT VERTEX SET.**  In the linear
form: if `T` is a clique of size at least `2` and `X` is any vertex set disjoint from it, then

```lean
maxDefIn G X + | T | ≤ MaxDef G + 2 .
```

This is the general form of Part 1, and it is what makes the arithmetic of the descent explicit: a
clique of size `t` contributes `t − 2` to the deficiency of `G` *independently* of everything that
hangs off it.  It contains `JSP90.maxDef_allNeighOf_le` of `JSPProblem/Attach.lean` (the special
case `X = allNeighOf G T`) and it is the quantitative form of the fact that the completion sets of
`JSPProblem/Attach.lean` are *free* in the deficiency.  (No lower bound on `| T |` is needed: the
estimate is true for every clique, and is strongest for large ones.) -/
theorem maxDefIn_add_card_le_maxDef_add_two_of_clique {T X : Finset V} (hcl : G.IsClique T)
    (hdisj : Disjoint T X) : maxDefIn G X + T.card ≤ MaxDef G + 2 := by
  obtain ⟨Y, hYX, hY⟩ := exists_eq_maxDefIn G X
  have h1 : T.card + Y.card - 2 * (1 + indepCard G Y) ≤ MaxDef G :=
    maxDef_ge_card_add_card_sub_two_add hcl (X := Y)
      (Finset.disjoint_left.mpr fun v hvT hvY => (Finset.disjoint_left.mp hdisj) hvT (hYX hvY))
  have h1' : T.card + Y.card ≤ MaxDef G + 2 * (1 + indepCard G Y) := by
    rw [Nat.sub_le_iff_le_add] at h1
    exact h1
  by_cases hnt : 2 * indepCard G Y ≤ Y.card
  · have hkey : T.card + (Y.card - 2 * indepCard G Y) + 2 * indepCard G Y = T.card + Y.card := by
      rw [Nat.add_assoc, Nat.sub_add_cancel hnt]
    have h4 : T.card + Y.card ≤ MaxDef G + 2 + 2 * indepCard G Y := by
      simpa [Nat.mul_add, Nat.add_assoc] using h1'
    have h3 : T.card + (Y.card - 2 * indepCard G Y) + 2 * indepCard G Y
        ≤ (MaxDef G + 2) + 2 * indepCard G Y := by
      rw [hkey]
      exact h4
    have h5 : T.card + (Y.card - 2 * indepCard G Y) ≤ MaxDef G + 2 := by omega
    calc maxDefIn G X + T.card = (Y.card - 2 * indepCard G Y) + T.card := by
          rw [← hY]
          rfl
        _ = T.card + (Y.card - 2 * indepCard G Y) := Nat.add_comm _ _
        _ ≤ MaxDef G + 2 := h5
  · have hA : defOf G Y = 0 := by
      show Y.card - 2 * indepCard G Y = 0
      omega
    calc maxDefIn G X + T.card = 0 + T.card := by rw [← hY, hA]
      _ = T.card := Nat.zero_add _
      _ ≤ MaxDef G + 2 := maxDef_clique_add_two_le (T := T) hcl

/-- **THE CLIQUE FORM OF THE DESCENT, IN THE ORDER THE INDUCTION READS IT.** -/
theorem maxDefIn_le_of_disjoint_clique {T X : Finset V} (hcl : G.IsClique T)
    (hdisj : Disjoint T X) : maxDefIn G X + T.card - 2 ≤ MaxDef G := by
  have h := maxDefIn_add_card_le_maxDef_add_two_of_clique hcl hdisj
  omega

end Descent

/-! ### Part 2 — the composition at a triangle, with the anticompleteness to `T` dropped -/

section Pieces

/-- **NEW INSTANCE OF THE HEADLINE THEOREM, AT A CUT AT A TRIANGLE WITH NO CONDITION ON THE EDGES
FROM `T` TO THE PIECES.**

Suppose `T` has three vertices, `𝒬` is a family of pairwise disjoint, pairwise anticomplete pieces
covering `V \ T`, and each piece is `m`-close to bipartite.  Then

```lean
LocIndep k G → CloseToBipartite (3 + k * m) G .
```

Rounds 63–64 stated this with `JSP90.AnticoverCut`, which additionally demands that **no edge joins
`T` to any piece** — the `JSP90.CutTriangle` hypothesis.  Neither that demand nor the disjointness
of the pieces from `T` is needed, and `T` is not even required to be a clique, only to have three
vertices: see the file header.  The constant is independent of the number of pieces (at most `k` of
them are non-bipartite, by `JSP90.card_nonBipartiteParts_le_cover`) and no bound is assumed on the
odd girth, on the packing weight or on the number of branch vertices. -/
theorem closeToBipartite_of_pieces {k m : ℕ} (hG : LocIndep k G) (T : Finset V)
    (𝒬 : Finset (Finset V)) (hfam : AnticoverCoverFamily G 𝒬) (hcard : T.card = 3)
    (hcover : ∀ x : V, x ∉ T → ∃ Q ∈ 𝒬, x ∈ Q)
    (hm : ∀ Q ∈ 𝒬, CloseToBipartite m (induceFinset G Q)) :
    CloseToBipartite (3 + k * m) G := by
  classical
  set N : Finset (Finset V) := 𝒬.filter (fun X => ¬ (induceFinset G X).IsBipartite) with hNdef
  have hNcard : N.card ≤ k := by
    rw [hNdef]
    exact card_nonBipartiteParts_le_cover hG hfam
  have hfamN : AnticoverFamily G N := by
    refine ⟨?_, ?_, ?_⟩
    · intro X hX Y hY hne
      exact hfam.1 X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hne
    · intro X hX Y hY hne x hx y hy
      exact hfam.2 X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hne x hx y hy
    · intro X hX
      have hnb : ¬ (induceFinset G X).IsBipartite := (Finset.mem_filter.mp hX).2
      have hex2 : ∃ C, IsOddCycle (induceFinset G X) C := by
        by_contra hcon2
        exact hnb (isBipartite_of_no_oddCycle hcon2)
      obtain ⟨C, hC⟩ := hex2
      exact ⟨C, hC.of_induceFinset, isOddCycle_sub_induceFinset hC⟩
  have hm' : ∀ (X : Finset V), X ∈ N → CloseToBipartite m (induceFinset G X) := by
    intro X hX
    exact hm X (Finset.mem_filter.mp hX).1
  obtain ⟨X₁, hX₁card, hX₁b⟩ :=
    closeToBipartite_of_anticoverFamily_cost (c := fun _ => m) hfamN hm'
  have hsum : (∑ X ∈ N, m) ≤ m * k := by
    have h : (∑ X ∈ N, m) = N.card * m := by simp
    rw [h, Nat.mul_comm]
    exact Nat.mul_le_mul_left m hNcard
  have hX₁bound : X₁.card ≤ m * k := le_trans hX₁card hsum
  set NN : Finset V := N.biUnion (id : Finset V → Finset V) with hNN
  set Z : Finset V := X₁ ∩ NN with hZdef
  have hZcard : Z.card ≤ m * k :=
    le_trans (Finset.card_le_card (Finset.inter_subset_left : X₁ ∩ NN ⊆ X₁)) hX₁bound
  have hNbip : (induceFinset G (NN \ Z)).IsBipartite := by
    have heq : NN \ Z = NN \ X₁ := by
      ext x
      simp only [Finset.mem_sdiff, hNN, hZdef, Finset.mem_inter]
      tauto
    rw [heq, ← deleteFinset_induceFinset]
    exact hX₁b
  -- the part of `G` outside `T` and outside the non-bipartite pieces
  have hB : (induceFinset G ((Finset.univ : Finset V) \ (T ∪ NN))).IsBipartite := by
    refine isBipartite_of_no_oddCycle ?_
    rintro ⟨C, hC⟩
    have hC' : IsOddCycle G C := hC.of_induceFinset
    have hCsub : C ⊆ (Finset.univ : Finset V) \ (T ∪ NN) :=
      isOddCycle_sub_induceFinset (s := (Finset.univ : Finset V) \ (T ∪ NN)) hC
    have hxcov : ∀ x : V, x ∈ (Finset.univ : Finset V) \ (T ∪ NN) → ∃ Q ∈ 𝒬, x ∈ Q := by
      intro x hx
      have hh := Finset.mem_sdiff.mp hx
      exact hcover x (fun hxT => hh.2 (mem_union_left' T NN hxT))
    obtain ⟨X, hX, hCX⟩ :=
      isOddCycle_sub_anticoverCover ((Finset.univ : Finset V) \ (T ∪ NN)) hfam hxcov hC' hCsub
    have hCX' : IsOddCycle (induceFinset G X) C := hC'.induceFinset (s := X) hCX
    by_cases hXbip : (induceFinset G X).IsBipartite
    · exact absurd ⟨C, hCX'⟩ (JSP90.not_isOddCycle_of_isBipartite hXbip)
    · have hXU : X ⊆ NN := by
        show X ⊆ N.biUnion (id : Finset V → Finset V)
        exact fun x hx => Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, hXbip⟩, hx⟩
      have h3 := isOddCycle_card_ge_three hCX'
      have hpos : 0 < C.card := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      exact False.elim ((Finset.mem_sdiff.mp (hCsub hx)).2
        (mem_union_right' T NN (hXU (hCX hx))))
  -- **THE STEP THAT REPLACES THE `Anticover` RECOMBINATION**: the residue after deleting `T` and
  -- the transversals of the non-bipartite pieces is bipartite, because an odd cycle of it lies in
  -- a *single* piece.
  have hD : (induceFinset G ((Finset.univ : Finset V) \ (T ∪ Z))).IsBipartite := by
    refine isBipartite_of_no_oddCycle ?_
    rintro ⟨C, hC⟩
    have hC' : IsOddCycle G C := hC.of_induceFinset
    have hCsub : C ⊆ (Finset.univ : Finset V) \ (T ∪ Z) :=
      isOddCycle_sub_induceFinset (s := (Finset.univ : Finset V) \ (T ∪ Z)) hC
    have hxcov : ∀ x : V, x ∈ (Finset.univ : Finset V) \ (T ∪ Z) → ∃ Q ∈ 𝒬, x ∈ Q := by
      intro x hx
      have hh := Finset.mem_sdiff.mp hx
      exact hcover x (fun hxT => hh.2 (mem_union_left' T Z hxT))
    obtain ⟨X, hX, hCX⟩ :=
      isOddCycle_sub_anticoverCover ((Finset.univ : Finset V) \ (T ∪ Z)) hfam hxcov hC' hCsub
    have hCX' : IsOddCycle (induceFinset G X) C := hC'.induceFinset (s := X) hCX
    by_cases hXbip : (induceFinset G X).IsBipartite
    · exact absurd ⟨C, hCX'⟩ (JSP90.not_isOddCycle_of_isBipartite hXbip)
    · have hXN : X ∈ N := Finset.mem_filter.mpr ⟨hX, hXbip⟩
      have hXU : X ⊆ NN := by
        show X ⊆ N.biUnion (id : Finset V → Finset V)
        exact fun x hx => Finset.mem_biUnion.mpr ⟨X, hXN, hx⟩
      have hCsubNN : C ⊆ NN \ Z := by
        intro x hx
        refine Finset.mem_sdiff.mpr ⟨hXU (hCX hx), fun hxZ => ?_⟩
        have hh : ¬ (x ∈ T ∪ Z) := (Finset.mem_sdiff.mp (hCsub hx)).2
        rw [hZdef] at hxZ
        exact hh (mem_union_right' T Z hxZ)
      have hXsub : X \ Z ⊆ NN \ Z := by
        intro x hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxX, hxZ⟩
        exact Finset.mem_sdiff.mpr ⟨hXU hxX, hxZ⟩
      have hXbip' : (induceFinset G (X \ Z)).IsBipartite :=
        isBipartite_induceFinset_of_isBipartite hNbip hXsub
      have hCsubXZ : C ⊆ X \ Z := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨hCX hx, (Finset.mem_sdiff.mp (hCsubNN hx)).2⟩
      exact absurd ⟨C, hC'.induceFinset (s := X \ Z) hCsubXZ⟩
        (JSP90.not_isOddCycle_of_isBipartite hXbip')
  refine ⟨T ∪ Z, ?_, ?_⟩
  · have h1 : (T ∪ Z).card ≤ T.card + Z.card := Finset.card_union_le _ _
    have h2 : T.card + Z.card ≤ 3 + k * m := by
      rw [hcard]
      have hZcard' : Z.card ≤ k * m := by rw [Nat.mul_comm]; exact hZcard
      omega
    omega
  · have hdel : deleteFinset G (T ∪ Z)
        = induceFinset G ((Finset.univ : Finset V) \ (T ∪ Z)) := rfl
    rw [hdel]
    exact hD

/-- **THE SAME INSTANCE, READ ON A VERTEX SET.** -/
theorem closeToBipartite_of_pieces_on {k m : ℕ} (hG : LocIndep k G) (T : Finset V)
    (𝒬 : Finset (Finset V)) (hfam : AnticoverCoverFamily G 𝒬) (hcard : T.card = 3)
    (hcover : ∀ x : V, x ∉ T → ∃ Q ∈ 𝒬, x ∈ Q)
    (hm : ∀ Q ∈ 𝒬, CloseToBipartite m (induceFinset G Q)) (U : Finset V) :
    CloseToBipartite (3 + k * m) (induceFinset G U) :=
  closeToBipartite_sub_induceFinset (closeToBipartite_of_pieces hG T 𝒬 hfam hcard hcover hm) U

end Pieces

/-! ### Part 3 — the canonical pieces: the components of `G − T`, at any triangle -/

section Canonical

/-- **EVERY PIECE OF THE CANONICAL CUT AT A TRIANGLE SATISFIES `LocIndep (k - 1)`.**  No
`JSP90.CutTriangle` hypothesis: the components of `G − T` are disjoint from `T` by construction, and
disjointness is all the descent needs (`JSP90.maxDefIn_add_one_le_maxDef_of_triangle`). -/
theorem locIndep_piece_of_triangle {k : ℕ} (hG : LocIndep k G) (T Q : Finset V)
    (hcl : G.IsClique T) (hcard : T.card = 3) (hQ : Q ∈ cutPieces G T) :
    LocIndep (k - 1) (induceFinset G Q) :=
  locIndep_of_disjoint_triangle hG hcl hcard
    (Finset.disjoint_left.mpr fun v hvT hvQ =>
      (Finset.mem_sdiff.mp (cutPieces_sub hQ hvQ : v ∈ (Finset.univ : Finset V) \ T)).2 hvT)

/-- **NEW INSTANCE OF THE HEADLINE THEOREM, AT AN ARBITRARY TRIANGLE.**  If `T` is *any* triangle of
`G` and every connected component of `G − T` is `m`-close to bipartite, then

```lean
LocIndep k G → CloseToBipartite (3 + k * m) G .
```

Rounds 63–64 stated this with the `JSP90.CutTriangle` hypothesis — *no edge from the triangle to the
rest of the graph* — and `JSP90.not_cutTriangle_completeGraph_four` shows that hypothesis is not
automatic (`K_4`).  It is not needed.  The constant is independent of the number of components, and
no bound is assumed on the odd girth, on the packing weight or on the number of branch vertices. -/
theorem closeToBipartite_of_triangle {k m : ℕ} (hG : LocIndep k G) (T : Finset V)
    (hT : G.IsNClique 3 T)
    (hm : ∀ Q ∈ cutPieces G T, CloseToBipartite m (induceFinset G Q)) :
    CloseToBipartite (3 + k * m) G :=
  closeToBipartite_of_pieces hG T (cutPieces G T) (anticoverCoverFamily_cutPieces)
    (G.isNClique_iff.mp hT).2
    (fun x hxT => ⟨compPiece (induceFinset G ((Finset.univ : Finset V) \ T)) x ∩
        ((Finset.univ : Finset V) \ T), mem_cutPieces x hxT, Finset.mem_inter.mpr
      ⟨compPiece_self (induceFinset G ((Finset.univ : Finset V) \ T)) x,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxT⟩⟩⟩) hm

/-- The same instance read on a vertex set. -/
theorem closeToBipartite_of_triangle_on {k m : ℕ} (hG : LocIndep k G) (T : Finset V)
    (hT : G.IsNClique 3 T)
    (hm : ∀ Q ∈ cutPieces G T, CloseToBipartite m (induceFinset G Q)) (U : Finset V) :
    CloseToBipartite (3 + k * m) (induceFinset G U) :=
  closeToBipartite_sub_induceFinset (closeToBipartite_of_triangle hG T hT hm) U

end Canonical

/-! ### Part 4 — the reduction: Erdős Problem #73 is EQUIVALENT to its triangle-free case -/

section Reduction

/-- **ERDŐS PROBLEM #73 FOR TRIANGLE-FREE GRAPHS** — the single statement that remains.

This is `JSP90.TriangleFreeErdős73` of `JSPProblem/CutTriangle.lean`, restated here because Part 4
shows it is now the *whole* remaining content of JSP-000090. -/
def TriangleFreeOnly : Prop :=
  ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
    LocIndep k G → G.CliqueFree 3 → CloseToBipartite (cutBound k) G

/-- **THE TRIANGLE-FREE CASE IMPLIES ERDŐS PROBLEM #73, IN FULL, WITH THE CONSTANT `cutBound` OF
ROUND 64.**

The induction is on `k` alone:

* `k = 0`: `G` is bipartite (`JSP90.erdos73_zero` of `JSPProblem/OddCycle.lean`);
* `k + 1`, `G` triangle-free: `TriangleFreeOnly`;
* `k + 1`, `G` not triangle-free: take any triangle `T`.  The components of `G − T` are pairwise
  disjoint, pairwise anticomplete and cover `V \ T` with no hypothesis at all, each satisfies
  `LocIndep k` by `JSP90.locIndep_piece_of_triangle` (disjointness is enough), so the induction
  hypothesis makes each of them `cutBound k`-close to bipartite, and
  `JSP90.closeToBipartite_of_triangle` concludes `3 + (k + 1) * cutBound k = cutBound (k + 1)`. -/
theorem erdos73On_of_triangleFreeOnly (htf : TriangleFreeOnly.{u}) (k : ℕ) :
    Erdős73On.{u} k (cutBound k) := by
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
        · obtain ⟨T, hT⟩ : ∃ T : Finset W, G.IsNClique 3 T := by
            by_contra hc
            exact hG3 fun T hT => hc ⟨T, hT⟩
          have hcl : G.IsClique (T : Finset W) := (G.isNClique_iff.mp hT).1
          have hcard : T.card = 3 := (G.isNClique_iff.mp hT).2
          have hm : ∀ Q ∈ cutPieces G T, CloseToBipartite (cutBound k) (induceFinset G Q) := by
            intro Q hQ
            exact ih W instW (induceFinset G Q) (locIndep_piece_of_triangle hG T Q hcl hcard hQ)
          exact closeToBipartite_of_triangle hG T hT hm
  exact main k

/-- **ERDŐS PROBLEM #73, IN FULL, FROM ITS TRIANGLE-FREE CASE ALONE.** -/
theorem erdos73_of_triangleFreeOnly (htf : TriangleFreeOnly.{u}) : ∀ k, Erdős73.{u} k :=
  fun k => ⟨cutBound k, erdos73On_of_triangleFreeOnly htf k⟩

/-- The triangle-free case follows from Erdős #73 with the constant `cutBound`. -/
theorem triangleFreeOnly_of_erdos73 (h : ∀ k, Erdős73On.{u} k (cutBound k)) : TriangleFreeOnly.{u} :=
  fun k W instW G hG _ => h k W instW G hG

/-- **ERDŐS PROBLEM #73 IS EQUIVALENT TO ITS TRIANGLE-FREE CASE.**  In words: a triangle is never
the hard part of the problem.  Deleting a triangle costs three vertices and one unit of Erdős's
parameter, the components of the rest are pairwise anticomplete whatever the triangle is attached
to, and their deficiencies have all dropped by one — so the general theorem follows from the
triangle-free one by induction on `k`. -/
theorem erdos73_iff_triangleFreeOnly :
    (∀ k, Erdős73On.{u} k (cutBound k)) ↔ TriangleFreeOnly.{u} :=
  ⟨triangleFreeOnly_of_erdos73, erdos73On_of_triangleFreeOnly⟩

/-- **ROUND 64'S SECOND STATEMENT IS NOW A THEOREM.**  `JSP90.CutTriangleErdős73` — the local
absorption alternative of `JSPProblem/CutTriangle.lean` — follows from the triangle-free case, so it
is no longer a hypothesis of the reduction but a consequence of it.  The instance of
`JSPProblem/CutTriangle.lean` it was needed for is subsumed by `JSP90.erdos73_of_triangleFreeOnly`. -/
theorem cutTriangleErdős73_of_triangleFreeOnly (htf : TriangleFreeOnly.{u}) :
    CutTriangleErdős73.{u} := by
  intro k W instW G hG hk
  exact Or.inr (erdos73On_of_triangleFreeOnly htf k W instW G hG)

/-- **ERDŐS PROBLEM #73 FROM THE TRIANGLE-FREE CASE AND *NOTHING ELSE*, in the terminology of
round 64.**  `JSP90.CutTriangleErdős73` is not needed: the two statements are interchangeable, and
`JSP90.erdos73_of_triangleFree` of `JSPProblem/CutTriangle.lean` holds with its second hypothesis
dropped. -/
theorem erdos73_of_triangleFreeErdos73 (htf : TriangleFreeErdős73.{u}) : ∀ k, Erdős73.{u} k :=
  erdos73_of_triangleFreeOnly htf

end Reduction

/-! ### Part 5 — the descent of Part 1 is **tight**: its factor is exactly one -/

section Tight

/-- **AN INDEPENDENT SET OF `kTriangles k` THAT AVOIDS THE FIBRE `i` HAS AT MOST `k - 1` ELEMENTS.**
Each fibre is a `K_3`, so an independent set meets each fibre at most once. -/
theorem card_le_kTriangles_avoid {k : ℕ} (i : Fin k) {S : Finset (Fin 3 × Fin k)}
    (hS : (kTriangles k).IsIndepSet S)
    (hSi : S ⊆ (Finset.univ : Finset (Fin 3 × Fin k)) \ tri i) : S.card ≤ k - 1 := by
  have havoid : ∀ p : Fin 3 × Fin k, p ∈ S → p ∉ tri i :=
    fun p hp => (Finset.mem_sdiff.mp (hSi hp)).2
  rw [SimpleGraph.isIndepSet_iff] at hS
  refine le_trans (Finset.card_le_card_of_injOn (s := S)
    (t := (Finset.univ : Finset (Fin k)).erase i) (fun p : Fin 3 × Fin k => p.2)
    (fun p hp => Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩) ?_) ?_
  · intro hpi
    exact havoid p (Finset.mem_coe.mp hp) (mem_tri.mpr hpi)
  · intro p hp q hq h
    have hpS : p ∈ S := Finset.mem_coe.mp hp
    have hqS : q ∈ S := Finset.mem_coe.mp hq
    refine Prod.ext (by
      by_cases hc : p.1 = q.1
      · exact hc
      · exfalso
        exact hS hpS hqS (fun hpq => hc (congrArg Prod.fst hpq)) ((kTriangles_adj).2 ⟨h, hc⟩)) h
  · have h1 := Finset.card_erase_add_one (Finset.mem_univ (i : Fin k))
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega

/-- **THE DESCENT OF PART 1 IS TIGHT — THE FACTOR IS EXACTLY ONE.**  On the sharp witness
`kTriangles k` (`k` disjoint triangles, of deficiency exactly `k`, by
`JSP90.maxDef_kTriangles`) a single triangle is disjoint from a vertex set of deficiency exactly
`k - 1`.  So the induction on Erdős's parameter really does drop by exactly one unit per triangle:
neither a larger drop nor a `+ 1` per piece can be obtained from the hypothesis, and the constant
`JSP90.cutBound` of the reduction of Part 4 is not an artefact of a weak estimate. -/
theorem descent_tight {k : ℕ} (hk : 0 < k) (i : Fin k) :
    maxDefIn (kTriangles k) ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i) + 1
      = MaxDef (kTriangles k) := by
  have hcl : (kTriangles k).IsClique (↑(tri i) : Set (Fin 3 × Fin k)) := by
    intro a ha b hb hne
    have ha' : a ∈ tri i := ha
    have hb' : b ∈ tri i := hb
    have h12 : a.2 = i := mem_tri.mp ha'
    have h22 : b.2 = i := mem_tri.mp hb'
    rw [kTriangles_adj]
    refine ⟨h12.trans h22.symm, ?_⟩
    intro hcon
    exact hne (Prod.ext hcon (h12.trans h22.symm))
  have hcard : (tri i).card = 3 := card_tri i
  have hdisj : Disjoint (tri i) ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i) :=
    Finset.disjoint_left.mpr fun p hp1 hp2 => (Finset.mem_sdiff.mp hp2).2 hp1
  have hup : maxDefIn (kTriangles k) ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i) + 1
      ≤ MaxDef (kTriangles k) :=
    maxDefIn_add_one_le_maxDef_of_triangle hcl hcard hdisj
  have hαle : indepCard (kTriangles k) ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i) ≤ k - 1 := by
    show ((indepSets (kTriangles k)
        ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i)).sup Finset.card) ≤ k - 1
    refine Finset.sup_le fun S hS => ?_
    exact card_le_kTriangles_avoid i (Finset.mem_filter.mp hS).2
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
  have hαge : (k : ℕ) - 1 ≤ indepCard (kTriangles k)
      ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i) := by
    have hmem : (((Finset.univ : Finset (Fin k)).erase i).image
          fun j : Fin k => (⟨(0 : Fin 3), j⟩ : Fin 3 × Fin k))
        ∈ indepSets (kTriangles k)
          ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i) := by
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_powerset.mpr ?_
        intro p hp
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [mem_tri]
        exact ne_of_mem_erase hj
      · refine isIndepSet_of_intro fun v w hv hw hne hadj => ?_
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hw
        have hjl : j = l := by simpa using (kTriangles_adj.mp hadj).1
        exact hne (Prod.ext rfl hjl)
    have hle := le_indepCard hmem
    have hcardS : ((((Finset.univ : Finset (Fin k)).erase i).image
          fun j : Fin k => (⟨(0 : Fin 3), j⟩ : Fin 3 × Fin k))).card = k - 1 := by
      rw [Finset.card_image_of_injective _ (f := fun j : Fin k =>
        (⟨(0 : Fin 3), j⟩ : Fin 3 × Fin k))]
      · have h1 := Finset.card_erase_add_one (Finset.mem_univ (i : Fin k))
        simp only [Finset.card_univ, Fintype.card_fin] at h1
        omega
      · intro j l h
        exact congrArg Prod.snd h
    omega
  have hα : indepCard (kTriangles k) ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i) = k - 1 :=
    le_antisymm hαle hαge
  have hcardX : ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i).card = 3 * k - 3 := by
    have h1 := Finset.card_sdiff_of_subset (s := tri i)
      (t := (Finset.univ : Finset (Fin 3 × Fin k))) (Finset.subset_univ _)
    have huniv : ((Finset.univ : Finset (Fin 3 × Fin k))).card = 3 * k := by
      simp
    omega
  have hdef : defOf (kTriangles k) ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i) = k - 1 := by
    simp only [defOf, hα, hcardX]
    omega
  have hlo : k - 1 ≤ maxDefIn (kTriangles k) ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i) := by
    have hle := le_maxDefIn (kTriangles k) ((Finset.univ : Finset (Fin 3 × Fin k)) \ tri i)
      (fun _ h => h)
    rw [hdef] at hle
    exact hle
  rw [maxDef_kTriangles k] at hup ⊢
  omega

end Tight

end

end JSP90
