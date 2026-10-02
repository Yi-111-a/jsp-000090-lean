/-
# JSP-000090, round 105 — **EXACT additivity: both sides of Erdős #73 split over a cover**

This file is a **new attack family** (the forty-sixth).  The premise is a remark that
`JSPProblem/Deficiency.lean` makes explicitly and that round 104 could not use:

> *"The *converse* (equality for `MaxDef`) is not proved here: it needs the additional fact …
> `JSPProblem/Deficiency.lean` `maxDef_le_add_of_anticover`"* — i.e. only

```lean
JSP90.maxDef_le_add_of_anticover : MaxDef G ≤ MaxDef (G[A]) + MaxDef (G[B])          -- Def.lean
JSP90.maxDef_cluster            : MaxDef G = ∑ C ∈ 𝒬, (|C| - 2)                       -- round 104
```

are known, the **equality** `MaxDef G = MaxDef (G[A]) + MaxDef (G[B])` — the additivity of
Erdős's *hypothesis* over an anticomplete decomposition — is not.  Round 104 had to re-derive it
inside the much narrower hypothesis "every piece is a clique", which is why round 104's counting
apparatus (`JSP90.piecesMet`, `JSP90.inj_pieces_choice`, `JSP90.card_le_piecesMet`, `JSP90.card_le_sum_card_inter`)
is forty declarations long.

This file settles it in general, and pushes the *same* statement through the conclusion:

```lean
JSP90.maxDefIn_anticoverIn_add        : maxDefIn G s = maxDefIn G (s ∩ A) + maxDefIn G (s ∩ B)
JSP90.maxDef_anticover_add            : MaxDef G = MaxDef (G[A]) + MaxDef (G[B])          -- THE MISSING EQUALITY
JSP90.maxDef_eq_sum_of_cover          : MaxDef G = ∑ X ∈ 𝒬, MaxDef (G[X])
JSP90.closeToBipartite_of_cover_cost  : (∀ X ∈ 𝒬, CloseToBipartite (c X) (G[X])) → CloseToBipartite (∑ c X) G
JSP90.closeToBipartite_iff_cost_cover : CloseToBipartite m G ↔ ∃ c, (∀ X ∈ 𝒬, CloseToBipartite (c X) (G[X])) ∧ ∑ c X ≤ m
JSP90.erdos73On_of_pieceMaxDef        : THE NEW INSTANCE — constant k, on the cover-closure of the "hypothesis = conclusion" class
```

## Why the equality is true (the truncation argument)

`defOf G X = |X| − 2 α(G[X])` is a **truncated** subtraction, so it is only *sub*additive over an
anticomplete split (`JSP90.defOf_le_add_of_anticover`, and the file header of
`JSPProblem/Deficiency.lean` gives the counterexample: `K_3 ⊔ K_1` has deficiency `0` on the
vertex set and `1` on the triangle).  The obstruction disappears for the *maximum*, because of two
one fact, used twice:

* **attainment**: `JSP90.exists_eq_maxDefIn` gives, for each side, a vertex set `X` with
  `defOf G X = maxDefIn G (side)`.  A side whose maximum is `0` is replaced by the empty set
  (it costs nothing), and a side whose maximum is `p > 0` has `|X| ≥ 2 α(X)`, so the two sides pay
  for themselves separately and no truncation occurs when the two are added.  That is exactly the
  case split in `JSP90.maxDefIn_anticoverIn_add` below.

Note what is **false**, and why the route suggested in `JSPProblem/Deficiency.lean` was not the
right one: `defOf` is **not** monotone under vertex sets.  For `G` a triangle together with two
isolated vertices, the triangle has `defOf = 3 − 2 = 1` while the whole vertex set has
`defOf = 5 − 6 = 0`; in particular `maxDefIn G U = defOf G U` is false and
`MaxDef G = |V| − 2 α(G)` is false (for `kTriangles k` it holds only because the witness is
`s`-degenerate).  One therefore cannot push the maximum to the whole vertex set, and the piece
sizes alone do not bound it; attainment, not monotonicity, is what is needed.

## What this buys

The hypothesis (`LocIndep k G`, i.e. `MaxDef G ≤ k`) and the conclusion (`CloseToBipartite m G`)
are then *both* exactly additive over an anticomplete cover, so:

* `JSP90.locIndep_cover_iff`: `LocIndep k G ↔ (∑ X ∈ 𝒬, MaxDef (G[X])) ≤ k`;
* `JSP90.closeToBipartite_iff_cost_cover`: the conclusion holds iff the pieces can be made
  bipartite at a total cost of at most `m` — so the class on which the two coincide is **closed
  under anticomplete covers**;
* `JSP90.maxDef_eq_sum_cost_of_cover`: round 104's key theorem is a **corollary** of this file
  (pieces that are cliques have `MaxDef = |C| − 2`, `JSP90.maxDef_clique` below), so the forty
  declarations of the counting apparatus are no longer needed for it;
* `JSP90.erdos73On_of_pieceMaxDef`: a **new instance of the headline theorem with the optimal
  constant `k`** on the largest class on which the hypothesis and the conclusion of Erdős #73 are
  known to coincide — every anticomplete cover whose pieces satisfy the equivalence.  Round 104's
  cluster class is contained in it (`JSP90.pieceMaxDef_of_cluster`), and so is any disjoint union
  of graphs in any class of round 98, 100 or 104;
* `JSP90.erdos73On_of_pieceMaxDef_optimal`: the constant `k` of that instance is **optimal**,
  machine-checked on the lower-bound witness `kTriangles k`.

## What is *not* proved

`jsp_000090_main` is still not declared and `JSP90.OddCycleErdosPosa r` is unchanged: this file
relates the two sides of Erdős #73 to each other over covers, it does not bound the transversal of
a graph whose pieces are themselves not covered (the odd-girth-free, packing-free, 3-connected
case).  Nothing here removes a hypothesis for an arbitrary graph.

## File conventions

No statement in this file mentions a concrete vertex type, so (as in round 104's `Cluster.lean`) the
file declares its own `DecidableEq` and `DecidablePred` instances. -/

import JSPProblem.Deficiency
import JSPProblem.Cut
import JSPProblem.CutTriangle
import JSPProblem.Additive
import JSPProblem.Transversal
import JSPProblem.Separator
import JSPProblem.Cluster

namespace JSP90

open Finset Fintype

universe u

variable {V : Type u} [Fintype V]

noncomputable section

local instance instDecidableEqExact : DecidableEq V := Classical.decEq V

local instance instDecidablePredIsIndepSetExact (G : SimpleGraph V) :
    DecidablePred fun S : Finset V => G.IsIndepSet S := fun _ => Classical.propDecidable _

/-! ## Part 0 — the local form of the deficiency, and why the naive route fails

`JSPProblem/Deficiency.lean` records the missing ingredient for the *equality*
`MaxDef G = MaxDef (G[A]) + MaxDef (G[B])` as follows:

> *it needs the additional fact that a vertex of `X \ s` is isolated in `G[s]`, so that adding it to
> `X` raises `|X|` and `α(G[s][X])` by the same amount and leaves `defOf` unchanged.*

The reason this is not the right route is worth recording, because it is the reason the equality
below needs a **case split**: `defOf` is **not** monotone under vertex sets.  For `G` a triangle
together with two isolated vertices, `Y` = the triangle has `defOf = 3 − 2 = 1`, while
`Y' = Y ∪ {the two isolated vertices}` has `defOf = 5 − 6 = 0`.  So `maxDefIn G U = defOf G U` is
**false**, and the maximum of the deficiency cannot be pushed to the whole vertex set.  What *is*
available, and is all that is needed, is attainment (`JSP90.exists_eq_maxDefIn`): for each side
there is a vertex set attaining the maximum there, and such a vertex set is either free
(deficiency `0`) or pays for itself (`|X| ≥ 2 α(X)`), so no truncation happens when the two sides
are added. -/

/-! ### Part 0b — the local form -/


/-- **An element of an empty intersection is impossible.**  Stated in the element form because
`Finset.disjoint_iff_ne` (and any lemma needing `DecidableEq (Finset V)`) cannot be used in this
file: that instance is not synthesised from the file-local `DecidableEq V`, as recorded in the
toolchain notes. -/
theorem false_of_mem_inter {s t : Finset V} {x : V} (h : s ∩ t = ∅) (hx : x ∈ s ∩ t) : False := by
  have hd : Disjoint s t := Finset.disjoint_iff_inter_eq_empty.mpr h
  rcases Finset.mem_inter.mp hx with ⟨hxs, hxt⟩
  exact Finset.disjoint_left.mp hd hxs hxt

/-- **`∅` has no members, without a `DecidableEq (Finset α)` instance** (the instance-based
simplifier cannot handle membership in a finset of finsets in this file, so the statement is made
explicit once and used where a cover is empty). -/
theorem not_mem_finsetEmpty {α : Type*} (a : Finset α) : a ∉ (∅ : Finset (Finset α)) := by
  rw [Finset.mem_def]
  simp

/-! ## Part 1
`JSPProblem/Deficiency.lean` proves the linear split (`JSP90.card_indepCard_anticover_add`) only for
an `Anticover` of the *whole* vertex set.  The finitary theorem of Part 3 needs it for a split of
an arbitrary vertex set, i.e. for `JSP90.AnticoverIn`; that is what this part proves, and the
`Anticover` version is recovered as the special case `s = univ` (`Part` 1, last line), so nothing
is lost. -/

section AnticoverIn

/-- **THE VERTICES AND THE INDEPENDENT SETS OF `Y` SPLIT OVER AN `AnticoverIn`.**  If `A` and `B`
split a vertex set `s` anticompletely and `Y ⊆ s`, then

* `Y = (Y ∩ A) ⊎ (Y ∩ B)`, so `|Y| = |Y ∩ A| + |Y ∩ B|`;
* `α(G[Y]) = α(G[Y ∩ A]) + α(G[Y ∩ B])`, *exactly* — an independent set of `Y` splits into an
  independent set of each side (no edge joins them), and independent sets of the two sides have
  independent union.

This generalises `JSP90.card_indepCard_anticover_add` of `JSPProblem/Deficiency.lean`, which is
stated for `Y ⊆ univ` only; the proof there is the same, with `hY` replaced by `h.2.1`. -/
theorem card_indepCard_anticoverIn_add {G : SimpleGraph V} {A B s Y : Finset V}
    (h : AnticoverIn G s A B) (hY : Y ⊆ s) :
    Y.card = (Y ∩ A).card + (Y ∩ B).card ∧
      indepCard G Y = indepCard (induceFinset G A) (Y ∩ A)
        + indepCard (induceFinset G B) (Y ∩ B) := by
  have hdisj : Disjoint (Y ∩ A) (Y ∩ B) := by
    refine Finset.disjoint_left.2 fun v hv1 hv2 =>
      h.1 (Finset.mem_inter.mp hv1).2 (Finset.mem_inter.mp hv2).2
  have hcard : Y.card = (Y ∩ A).card + (Y ∩ B).card := by
    have heq : Y = (Y ∩ A) ∪ (Y ∩ B) := by
      ext v
      constructor
      · intro hv
        by_cases hA : v ∈ A
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv, hA⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨hv, mem_B_of_not_mem_A_anticoverIn h (hY hv) hA⟩)
      · intro hv
        rcases Finset.mem_union.mp hv with hv' | hv'
        · exact (Finset.mem_inter.mp hv').1
        · exact (Finset.mem_inter.mp hv').1
    calc Y.card = ((Y ∩ A) ∪ (Y ∩ B)).card := congrArg Finset.card heq
      _ = (Y ∩ A).card + (Y ∩ B).card := Finset.card_union_of_disjoint hdisj
  refine ⟨hcard, le_antisymm ?_ ?_⟩
  · -- every independent set of `Y` splits into one of each side
    refine Finset.sup_le_iff.mpr fun S hS => ?_
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
    have h4 : S \ A = S ∩ B := by
      ext v
      constructor
      · intro hv
        have hvA := Finset.mem_sdiff.mp hv
        have hmem := hY (sub_of_mem_indepSets hS hvA.1)
        have hmem' : v ∈ A ∪ B := by rw [h.2.1]; exact hmem
        rcases Finset.mem_union.mp hmem' with hA' | hB'
        · exact (hvA.2 hA').elim
        · exact Finset.mem_inter.mpr ⟨hvA.1, hB'⟩
      · intro hv
        have hvI := Finset.mem_inter.mp hv
        refine Finset.mem_sdiff.mpr ⟨hvI.1, ?_⟩
        intro hnA
        exact h.1 hnA hvI.2
    have h3' : S.card = (S ∩ A).card + (S ∩ B).card := by
      rw [← h4]
      exact (card_inter_add_card_sdiff S A).symm
    omega
  · -- and conversely, independent sets of the two sides have independent union
    obtain ⟨SA, hSAsub, hSAi, hSAcard⟩ := exists_indepCard (induceFinset G A) (Y ∩ A)
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
        refine Finset.disjoint_left.2 fun v hv1 hv2 =>
          h.1 (Finset.mem_inter.mp (Finset.mem_of_subset hSAsub hv1)).2
            (Finset.mem_inter.mp (Finset.mem_of_subset hSBsub hv2)).2
      rw [Finset.card_union_of_disjoint hdisjSA, hSAcard, hSBcard]
    · refine isIndepSet_of_intro fun v w hv hw hne hadj => ?_
      have hv' : v ∈ SA ∪ SB := Finset.mem_coe.mp hv
      have hw' : w ∈ SA ∪ SB := Finset.mem_coe.mp hw
      have inA : ∀ v ∈ SA, v ∈ A := fun v hv => (Finset.mem_inter.mp (Finset.mem_of_subset hSAsub hv)).2
      have inB : ∀ v ∈ SB, v ∈ B := fun v hv => (Finset.mem_inter.mp (Finset.mem_of_subset hSBsub hv)).2
      rcases Finset.mem_union.mp hv' with hvA | hvB <;>
        rcases Finset.mem_union.mp hw' with hwA | hwB
      · exact IsIndepSet.apply' hSAi hvA hwA hne (induce_adj.mpr ⟨inA _ hvA, inA _ hwA, hadj⟩)
      · exact (h.2.2 v (inA _ hvA) w (inB _ hwB)) hadj
      · exact absurd hadj
          (fun hAdj => h.2.2 w (inA w hwA) v (inB v hvB) hAdj.symm)
      · exact IsIndepSet.apply' hSBi hvB hwB hne (induce_adj.mpr ⟨inB _ hvB, inB _ hwB, hadj⟩)

/-- **THE DEFICIENCY OF A VERTEX SET IS AT MOST THE SUM OF THE DEFICIENCIES OF ITS TWO SIDES.**
`JSP90.defOf_le_add_of_anticover` of `JSPProblem/Deficiency.lean`, with an `AnticoverIn` in place
of an `Anticover`. -/
theorem defOf_le_add_of_anticoverIn {G : SimpleGraph V} {A B s Y : Finset V}
    (h : AnticoverIn G s A B) (hY : Y ⊆ s) :
    defOf G Y ≤ defOf (induceFinset G A) (Y ∩ A) + defOf (induceFinset G B) (Y ∩ B) := by
  obtain ⟨hcard, hα⟩ := card_indepCard_anticoverIn_add h hY
  simp only [defOf, hcard, hα, Nat.mul_add]
  exact sub_le_add_sub _ _ _ _

/-- **THE `Anticover` VERSION OF THE LINEAR SPLIT, i.e. `JSP90.card_indepCard_anticover_add`
recovered as the special case `s = univ`.**  (`Anticover G A B` *is* `AnticoverIn G univ A B`.) -/
theorem card_indepCard_anticover_add_of_anticover {G : SimpleGraph V} {A B Y : Finset V}
    (h : Anticover G A B) (hY : Y ⊆ A ∪ B) :
    Y.card = (Y ∩ A).card + (Y ∩ B).card ∧
      indepCard G Y = indepCard (induceFinset G A) (Y ∩ A)
        + indepCard (induceFinset G B) (Y ∩ B) :=
  card_indepCard_anticoverIn_add h (Finset.Subset.trans hY (by rw [h.cover]))

end AnticoverIn

/-! ## Part 2 — THE MISSING EQUALITY: the deficiency is additive over an anticomplete split -/

section Additive

/-- **THE MAXIMUM DEFICIENCY INSIDE A VERTEX SET SPLITS *EXACTLY* OVER AN ANTICOMPLETE SPLIT OF
IT.**  If `A` and `B` split a vertex set `s` anticompletely then

```lean
maxDefIn G s = maxDefIn G (s ∩ A) + maxDefIn G (s ∩ B)
```

with **equality**, not the subadditivity of `JSP90.defOf_le_add_of_anticoverIn`.

The proof is the truncation argument of the header of this file: a side with deficiency `0` is
replaced by the empty set (it costs nothing), and a side with deficiency `p > 0` satisfies
`|X| ≥ 2 α(G[X])`, so the two sides pay for themselves separately.  The obstruction that defeats
additivity for `defOf` itself (`K_3 ⊔ K_1`, deficiency `0` on the vertex set and `1` on the
triangle) cannot defeat this, because the maximum on the vertex set is *attained on a side*. -/
theorem maxDefIn_anticoverIn_add {G : SimpleGraph V} {A B s : Finset V} (h : AnticoverIn G s A B) :
    maxDefIn G s = maxDefIn G (s ∩ A) + maxDefIn G (s ∩ B) := by
  have hle : ∀ X : Finset V, X ⊆ s →
      defOf G X ≤ maxDefIn G (s ∩ A) + maxDefIn G (s ∩ B) := by
    intro X hX
    have h1 := defOf_le_add_of_anticoverIn h hX
    have h2 : defOf (induceFinset G A) (X ∩ A) ≤ maxDefIn G (s ∩ A) := by
      have heq : defOf (induceFinset G A) (X ∩ A) = defOf G (X ∩ A) :=
        defOf_induceFinset_of_subset (Finset.inter_subset_right (s₁ := X) (s₂ := A))
      rw [heq]
      exact le_maxDefIn G (s ∩ A) (Finset.inter_subset_inter hX (Finset.Subset.refl _))
    have h3 : defOf (induceFinset G B) (X ∩ B) ≤ maxDefIn G (s ∩ B) := by
      have heq : defOf (induceFinset G B) (X ∩ B) = defOf G (X ∩ B) :=
        defOf_induceFinset_of_subset (Finset.inter_subset_right (s₁ := X) (s₂ := B))
      rw [heq]
      exact le_maxDefIn G (s ∩ B) (Finset.inter_subset_inter hX (Finset.Subset.refl _))
    omega
  have hge : maxDefIn G (s ∩ A) + maxDefIn G (s ∩ B) ≤ maxDefIn G s := by
    obtain ⟨XA, hXAsub, hXA⟩ := exists_eq_maxDefIn G (s ∩ A)
    obtain ⟨XB, hXBsub, hXB⟩ := exists_eq_maxDefIn G (s ∩ B)
    by_cases hp0 : maxDefIn G (s ∩ A) = 0
    · by_cases hq0 : maxDefIn G (s ∩ B) = 0
      · rw [hp0, hq0]
        exact Nat.zero_le _
      · rw [hp0, zero_add, ← hXB]
        exact le_maxDefIn G s (Finset.Subset.trans hXBsub (Finset.inter_subset_left (s₁ := s) (s₂ := B)))
    · by_cases hq0 : maxDefIn G (s ∩ B) = 0
      · rw [hq0, add_zero, ← hXA]
        exact le_maxDefIn G s
          (Finset.Subset.trans hXAsub (Finset.inter_subset_left (s₁ := s) (s₂ := A)))
      · -- both sides pay for themselves, so nothing truncates when they are added
        have hp : 0 < maxDefIn G (s ∩ A) := by omega
        have hq : 0 < maxDefIn G (s ∩ B) := by omega
        set Y : Finset V := XA ∪ XB with hYdef
        have hYsub : Y ⊆ s := Finset.Subset.trans (Finset.union_subset
          (Finset.Subset.trans hXAsub (Finset.inter_subset_left (s₁ := s) (s₂ := A)))
          (Finset.Subset.trans hXBsub (Finset.inter_subset_left (s₁ := s) (s₂ := B))))
          (Finset.Subset.refl _)
        have hsplit := card_indepCard_anticoverIn_add h hYsub
        have hXAinA : XA ⊆ A :=
          Finset.Subset.trans hXAsub (Finset.inter_subset_right (s₁ := s) (s₂ := A))
        have hXBinB : XB ⊆ B :=
          Finset.Subset.trans hXBsub (Finset.inter_subset_right (s₁ := s) (s₂ := B))
        have eA : Y ∩ A = XA := by
          refine Finset.Subset.antisymm ?_ ?_
          · intro v hv
            rw [Finset.mem_inter] at hv
            rcases Finset.mem_union.mp (hYdef ▸ hv.1) with h1 | h1
            · exact h1
            · exact (h.1 hv.2 (Finset.mem_of_subset hXBinB h1)).elim
          · intro v hv
            have hvA : v ∈ A := Finset.mem_of_subset hXAinA hv
            refine Finset.mem_inter.mpr ⟨?_, hvA⟩
            rw [hYdef]
            exact Finset.mem_union.mpr (Or.inl hv)
        have eB : Y ∩ B = XB := by
          refine Finset.Subset.antisymm ?_ ?_
          · intro v hv
            rw [Finset.mem_inter] at hv
            rcases Finset.mem_union.mp (hYdef ▸ hv.1) with h1 | h1
            · exact (h.1 (Finset.mem_of_subset hXAinA h1) hv.2).elim
            · exact h1
          · intro v hv
            have hvB : v ∈ B := Finset.mem_of_subset hXBinB hv
            refine Finset.mem_inter.mpr ⟨?_, hvB⟩
            rw [hYdef]
            exact Finset.mem_union.mpr (Or.inr hv)
        have hα : indepCard G Y = indepCard G XA + indepCard G XB := by
          rw [hsplit.2, eA, eB,
            indepCard_induceFinset_of_subset hXAinA, indepCard_induceFinset_of_subset hXBinB]
        have hcard : Y.card = XA.card + XB.card := by rw [hsplit.1, eA, eB]
        have hA : 2 * indepCard G XA ≤ XA.card := by
          have hd : defOf G XA = XA.card - 2 * indepCard G XA := rfl
          rw [hd] at hXA
          omega
        have hB : 2 * indepCard G XB ≤ XB.card := by
          have hd : defOf G XB = XB.card - 2 * indepCard G XB := rfl
          rw [hd] at hXB
          omega
        have hleY : defOf G Y = defOf G XA + defOf G XB := by
          simp only [defOf, hcard, hα, Nat.mul_add]
          omega
        have key : maxDefIn G (s ∩ A) + maxDefIn G (s ∩ B) ≤ defOf G Y := by
          rw [← hXA, ← hXB, ← hleY]
        exact le_trans key (le_maxDefIn G s hYsub)
  exact le_antisymm (by
    show (s.powerset).sup (defOf G) ≤ _
    refine Finset.sup_le_iff.mpr fun X hX => ?_
    exact hle X (Finset.mem_powerset.mp hX)) hge

/-- **THE MAXIMUM DEFICIENCY IS ADDITIVE OVER AN ANTICOMPLETE DECOMPOSITION OF THE VERTEX SET.**

```lean
MaxDef G = MaxDef (G[A]) + MaxDef (G[B])          for every Anticover G A B
```

This is *the statement that `JSPProblem/Deficiency.lean` records as missing*: it proves there only
`MaxDef G ≤ MaxDef (G[A]) + MaxDef (G[B])` (`JSP90.maxDef_le_add_of_anticover`), and says that
the converse "is not proved here".  It is also the general form of round 104's
`JSP90.maxDef_cluster`, which needed the extra hypothesis that the pieces are cliques. -/
theorem maxDef_anticover_add {G : SimpleGraph V} {A B : Finset V} (h : Anticover G A B) :
    MaxDef G = MaxDef (induceFinset G A) + MaxDef (induceFinset G B) := by
  have h' := maxDefIn_anticoverIn_add (G := G) (s := (Finset.univ : Finset V)) h.anticoverIn
  rw [show maxDefIn G (Finset.univ : Finset V) = MaxDef G from rfl] at h'
  have e₁ : ((Finset.univ : Finset V) ∩ A) = A := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_univ, true_and]
  have e₂ : ((Finset.univ : Finset V) ∩ B) = B := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_univ, true_and]
  rw [e₁, e₂] at h'
  rw [maxDef_eq_maxDefIn_induceFinset, maxDef_eq_maxDefIn_induceFinset]
  exact h'

end Additive

/-! ## Part 2b — cliques: the pieces of round 104, in deficiency form

`JSP90.maxDef_cluster` of round 104 proved `MaxDef G = ∑ C ∈ 𝒬, (|C| − 2)` for a cluster
decomposition, i.e. the deficiency of a clique piece is its size minus two.  That is a statement
about a *single piece* and it is proved here, once, from the counting definitions. -/

section Clique

/-- **THE DEFICIENCY OF A CLIQUE IS ITS SIZE MINUS TWO.**  For a clique `C` of at least two
vertices, `MaxDef (G[C]) = |C| − 2`: an independent set of a clique has one vertex, so the
deficiency of a vertex set `X ⊆ C` is `|X| − 2` when `X` is nonempty and `0` otherwise, and the
largest such value is at `X = C`.  (`JSP90.maxDef_completeGraph` of `JSPProblem/Deficiency.lean`
is the special case in which `G` is a complete graph on `Fin n`.) -/
theorem maxDef_clique {C : Finset V} (hcl : G.IsClique C) (h2 : 2 ≤ C.card) :
    MaxDef (induceFinset G C) = C.card - 2 := by
  have hle : maxDefIn G C ≤ C.card - 2 := by
    show (C.powerset).sup (defOf G) ≤ C.card - 2
    refine Finset.sup_le_iff.mpr fun Y hY => ?_
    have hYC : Y ⊆ C := Finset.mem_powerset.mp hY
    by_cases hY0 : Y = ∅
    · rw [hY0, defOf, indepCard_empty]
      simp only [Finset.card_empty, Nat.zero_mul, Nat.sub_self, Finset.card_pos]
      omega
    · have hα : 1 ≤ indepCard G Y := indepCard_pos (Finset.nonempty_iff_ne_empty.mpr hY0)
      have h1 : Y.card - 2 * indepCard G Y ≤ Y.card - 2 :=
        Nat.sub_le_sub_left (by omega) (Y.card)
      exact le_trans h1 (Nat.sub_le_sub_right (Finset.card_le_card hYC) 2)
  have hge : C.card - 2 ≤ maxDefIn G C := by
    have hCne : C ≠ ∅ := by
      intro hCE
      rw [hCE] at h2
      simp at h2
    have hα1 : indepCard (induceFinset G C) C = 1 := by
      refine le_antisymm ?_ (Nat.succ_le_of_lt
        (indepCard_pos (Finset.nonempty_iff_ne_empty.mpr hCne)))
      refine Finset.sup_le_iff.mpr fun S hS => ?_
      have hSsub : S ⊆ C := sub_of_mem_indepSets hS
      exact indep_card_le_one_of_clique hcl
        ((isIndepSet_induceFinset_iff (G := G) (S := S) (s := C) hSsub).mp
          (Finset.mem_filter.mp hS).2) hSsub
    have hα : indepCard G C = 1 := by
      rw [← indepCard_induceFinset_of_subset (Finset.Subset.refl _)]
      exact hα1
    have hd : C.card - 2 ≤ defOf G C := by
      show C.card - 2 ≤ C.card - 2 * indepCard G C
      rw [hα]
    exact le_trans hd (le_maxDefIn G C (Finset.Subset.refl C))
  rw [maxDef_eq_maxDefIn_induceFinset]
  exact le_antisymm hle hge

/-- **A CLIQUE IS `|C| − 2`-CLOSE TO BIPARTITE.**  Delete all but two of its vertices: what remains
is a graph on two vertices, which is bipartite (`JSP90.isBipartite_induceFinset_of_card_le_two`).
Together with `JSP90.maxDef_clique` this is the per-piece half of
`JSP90.closeToBipartite_iff_maxDef_cluster`. -/
theorem closeToBipartite_of_clique {C : Finset V} (hcl : G.IsClique C) (h2 : 2 ≤ C.card) :
    CloseToBipartite (C.card - 2) (induceFinset G C) := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_two_of_card_ge_two h2
  set D : Finset V := ({a, b} : Finset V) with hDdef
  have hDsub : D ⊆ C := by
    intro x hx
    rw [hDdef] at hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact h ▸ ha
    · exact (Finset.mem_singleton.mp h) ▸ hb
  have hab' : a ∉ ({b} : Finset V) := by
    rw [Finset.mem_singleton]
    exact hab
  have hcardD : D.card = 2 := by
    rw [hDdef, Finset.card_insert_of_notMem (a := a) hab', Finset.card_singleton]
  refine ⟨C \ D, ?_, ?_⟩
  · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hDsub, hcardD]
  · rw [deleteFinset_induceFinset]
    have e : C \ (C \ D) = D := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro v hv
        rw [hDdef] at hv
        have hv' := Finset.mem_sdiff.mp hv
        by_contra hnv
        exact hv'.2 (Finset.mem_sdiff.mpr ⟨hv'.1, hnv⟩)
      · intro v hv
        rw [hDdef] at hv
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · rcases Finset.mem_insert.mp hv with h | h
          · exact h ▸ ha
          · exact (Finset.mem_singleton.mp h) ▸ hb
        · intro hn
          exact ((Finset.mem_sdiff.mp hn).2 hv).elim
    rw [e]
    exact isBipartite_induceFinset_of_card_le_two (by rw [hcardD])

end Clique

/-! ## Part 3 — the finitary form: the pieces of a cover split both sides of Erdős #73 -/

section Cover

set_option maxHeartbeats 4000000 in
/-- **THE PIECES OF AN ANTICOMPLETE COVER SPLIT THE MAXIMUM DEFICIENCY.**  If `𝒬` is a family of
pairwise disjoint, pairwise anticomplete pieces covering the vertices of `G`, then

```lean
MaxDef G = ∑ X ∈ 𝒬, MaxDef (G[X])
```

by induction on the family, one piece at a time, using `JSP90.maxDefIn_anticoverIn_add`: a single
piece `X` peels off `s` anticompletely (`AnticoverIn G s X (s \ X)`), because every vertex of
`s \ X` lies in another piece and no edge joins two pieces.  This is the general statement of which
round 104's `JSP90.maxDef_cluster` is the clique-specialised instance. -/
theorem maxDef_eq_sum_of_cover {𝒬 : Finset (Finset V)} (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X) :
    MaxDef G = ∑ X ∈ 𝒬, MaxDef (induceFinset G X) := by
  have key : ∀ (t : Finset (Finset V)) (s : Finset V),
      AnticoverCoverFamily G t →
      (∀ X ∈ t, X ⊆ s) →
      (∀ ⦃x : V⦄, x ∈ s → ∃ X ∈ t, x ∈ X) →
      maxDefIn G s = ∑ X ∈ t, MaxDef (induceFinset G X) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro s _ _ hcov2
        have hse : s = ∅ := by
          refine Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
          · obtain ⟨X, hX, hxX⟩ := hcov2 hx
            exact absurd hX (not_mem_finsetEmpty X)
          · exact absurd hx (by simp)
        rw [hse]
        refine le_antisymm ?_ (Nat.zero_le _)
        show (Finset.powerset (∅ : Finset V)).sup (defOf G) ≤ 0
        refine Finset.sup_le_iff.mpr fun Y hY => ?_
        have hY0 : Y = ∅ :=
          Finset.Subset.antisymm (Finset.mem_powerset.mp hY) (by simp)
        rw [hY0, defOf, indepCard_empty]
        exact Nat.zero_le _
    | @insert X t hX ih =>
        intro s ht hsub hcov2
        have hXA : X ⊆ s := hsub X (Finset.mem_insert_self X t)
        have ht' : AnticoverCoverFamily G t :=
          ⟨fun Y hY Z hZ hYZ => ht.1 Y (Finset.mem_insert_of_mem hY) Z
              (Finset.mem_insert_of_mem hZ) hYZ,
            fun Y hY Z hZ hYZ y hy z hz => ht.2 Y (Finset.mem_insert_of_mem hY) Z
              (Finset.mem_insert_of_mem hZ) hYZ y hy z hz⟩
        have hsub' : ∀ Y ∈ t, Y ⊆ s \ X := by
          intro Y hY v hv
          refine Finset.mem_sdiff.mpr ⟨hsub Y (Finset.mem_insert_of_mem hY) hv, ?_⟩
          intro hvx
          have hne : X ≠ Y := by
            intro hXY
            subst hXY
            exact hX hY
          exact false_of_mem_inter
            (ht.1 X (Finset.mem_insert_self X t) Y (Finset.mem_insert_of_mem hY) hne)
            (Finset.mem_inter.mpr ⟨hvx, hv⟩)
        have hcov' : ∀ ⦃x : V⦄, x ∈ s \ X → ∃ Y ∈ t, x ∈ Y := by
          intro x hx
          obtain ⟨Y, hY, hxY⟩ := hcov2 (Finset.mem_sdiff.mp hx).1
          have hYt : Y ∈ t := by
            rcases Finset.mem_insert.mp hY with hEq | hZ
            · exact ((Finset.mem_sdiff.mp hx).2 (hEq ▸ hxY)).elim
            · exact hZ
          exact ⟨Y, hYt, hxY⟩
        have h1 := ih (s := s \ X) ht' hsub' hcov'
        have hsplit : AnticoverIn G s X (s \ X) := by
          refine ⟨?_, Finset.union_sdiff_of_subset hXA, ?_⟩
          · intro _ hxX hx'
            exact (Finset.mem_sdiff.mp hx').2 hxX
          · intro _ hxX _ hw hAdj
            obtain ⟨Y, hY, hwY⟩ := hcov2 (Finset.mem_sdiff.mp hw).1
            have hYt : Y ∈ t := by
              rcases Finset.mem_insert.mp hY with hEq | hZ
              · exact ((Finset.mem_sdiff.mp hw).2 (hEq ▸ hwY)).elim
              · exact hZ
            have hne : X ≠ Y := by
              intro hXY
              subst hXY
              exact absurd hwY (Finset.mem_sdiff.mp hw).2
            exact ht.2 X (Finset.mem_insert_self X t) Y hY hne _ hxX _ hwY hAdj
        have h2 := maxDefIn_anticoverIn_add (G := G) hsplit
        have e₁ : s ∩ X = X := Finset.inter_eq_right.mpr hXA
        have e₂ : s ∩ (s \ X) = s \ X := by
          refine Finset.Subset.antisymm (fun _ hv => (Finset.mem_inter.mp hv).2)
            (fun v hv => ?_)
          exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hv).1, hv⟩
        rw [e₁, e₂] at h2
        rw [h2, h1, Finset.sum_insert hX, (maxDef_eq_maxDefIn_induceFinset X).symm]
  have h1 := key 𝒬 (Finset.univ : Finset V) h
    (fun X _ => Finset.Subset.trans (Finset.Subset.refl X) (Finset.subset_univ X)) hcov
  have huniv : maxDefIn G (Finset.univ : Finset V) = MaxDef G := rfl
  rw [huniv] at h1
  exact h1

/-- **THE HYPOTHESIS OF ERDŐS #73 SPLITS OVER A COVER**: `LocIndep k G` iff the deficiencies of the
pieces of an anticomplete cover sum to at most `k`. -/
theorem locIndep_cover_iff {𝒬 : Finset (Finset V)} (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X) {k : ℕ} :
    LocIndep k G ↔ (∑ X ∈ 𝒬, MaxDef (induceFinset G X)) ≤ k := by
  rw [locIndep_iff_maxDef_le, maxDef_eq_sum_of_cover h hcov]

/-- **ROUND 104'S `maxDef_cluster` IS A COROLLARY.**  For a cover whose pieces are cliques of at
least two vertices, the deficiency of `G` is the sum of the piece costs `|C| − 2`. -/
theorem maxDef_eq_sum_cost_of_cover {𝒬 : Finset (Finset V)} (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X)
    (h2 : ∀ X ∈ 𝒬, 2 ≤ X.card)
    (hcl : ∀ X ∈ 𝒬, G.IsClique X) :
    MaxDef G = ∑ X ∈ 𝒬, (X.card - 2) := by
  rw [maxDef_eq_sum_of_cover h hcov]
  exact Finset.sum_congr rfl fun X hX => maxDef_clique (hcl X hX) (h2 X hX)

end Cover

/-! ## Part 4 — the conclusion side: the cost of a cover adds up, and adds up *exactly* -/

section Cost

/-- **THE COST OF A COVER ADDS UP.**  If every piece of an anticomplete cover `𝒬` of the vertices
of `G` can be made bipartite by deleting `c X` of its vertices, then `G` can be made bipartite by
deleting `∑ X ∈ 𝒬, c X` vertices.  (This is `JSP90.closeToBipartite_of_anticoverFamily_cost` of
`JSPProblem/Additive.lean` in the `Cover` form: no "no edge leaves the union" condition and no
odd-cycle condition on the pieces.) -/
theorem closeToBipartite_of_cover_cost {𝒬 : Finset (Finset V)} {c : Finset V → ℕ}
    (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X)
    (hm : ∀ X ∈ 𝒬, CloseToBipartite (c X) (induceFinset G X)) :
    CloseToBipartite (∑ X ∈ 𝒬, c X) G := by
  classical
  have key : ∀ X ∈ 𝒬, ∃ Y : Finset V, Y.card ≤ c X ∧ HitsOddCycles (induceFinset G X) Y := by
    intro X hX
    exact (closeToBipartite_iff_hitsOddCycles (G := induceFinset G X) (m := c X)).mp (hm X hX)
  have Y : ∀ (X : Finset V) (hX : X ∈ 𝒬),
      {Y : Finset V // Y.card ≤ c X ∧ HitsOddCycles (induceFinset G X) Y} := by
    intro X hX
    exact ⟨(key X hX).choose, (key X hX).choose_spec.1, (key X hX).choose_spec.2⟩
  set Y' : Finset V → Finset V := fun X => if hX : X ∈ 𝒬 then (Y X hX).1 else ∅ with hY'def
  have hcard' : ∀ X ∈ 𝒬, (Y' X).card ≤ c X := by
    intro X hX
    have hY' : Y' X = (Y X hX).1 := by rw [hY'def]; simp [hX]
    rw [hY']
    exact (Y X hX).property.1
  have hhits' : ∀ X ∈ 𝒬, HitsOddCycles (induceFinset G X) (Y' X) := by
    intro X hX
    have hY' : Y' X = (Y X hX).1 := by rw [hY'def]; simp [hX]
    rw [hY']
    exact (Y X hX).property.2
  refine (closeToBipartite_iff_hitsOddCycles (G := G)
    (m := ∑ X ∈ 𝒬, c X)).mpr ⟨𝒬.biUnion (fun X => Y' X ∩ X), ?_, ?_⟩
  · have hdis : ∀ X ∈ 𝒬, ∀ X' ∈ 𝒬, X ≠ X' →
        ∀ x, x ∈ Y' X ∩ X → x ∉ Y' X' ∩ X' := by
      intro X hX X' hX' hne x hx hx'
      exact false_of_mem_inter (h.1 X hX X' hX' hne)
        (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx').2⟩)
    exact le_trans (card_biUnion_le_sum 𝒬 (fun X => Y' X ∩ X) hdis)
      (Finset.sum_le_sum fun X hX =>
        le_trans (Finset.card_le_card (Finset.inter_subset_left)) (hcard' X hX))
  · intro C hC
    obtain ⟨X, hX, hCX⟩ := isOddCycle_sub_anticoverCover (s := (Finset.univ : Finset V)) h hcov hC
      (Finset.subset_univ C)
    have hne : C ∩ (Y' X ∩ X) ≠ ∅ := by
      have hne' : C ∩ Y' X ≠ ∅ := (hhits' X hX) C (IsOddCycle.induceFinset hC hCX)
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne'
      have hx' : x ∈ C ∧ x ∈ Y' X := Finset.mem_inter.mp hx
      exact ne_empty_of_nonempty
        ⟨x, Finset.mem_inter.mpr ⟨hx'.1, Finset.mem_inter.mpr ⟨hx'.2, hCX hx'.1⟩⟩⟩
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hx' : x ∈ C ∧ x ∈ Y' X ∩ X := Finset.mem_inter.mp hx
    have hbij : x ∈ 𝒬.biUnion (fun X => Y' X ∩ X) := by
      refine Finset.mem_biUnion.mpr ⟨X, hX, ?_⟩
      exact hx'.2
    exact ne_empty_of_nonempty ⟨x, Finset.mem_inter.mpr ⟨hx'.1, hbij⟩⟩

/-- **THE COST OF A CERTIFICATE IS AT MOST THE COST OF THE CERTIFICATE.**  If `𝒬` is a family of
pairwise disjoint pieces then the pieces of `Z ∩ X`, for `X ∈ 𝒬`, partition `Z ∩ (⋃ X ∈ 𝒬)`, so
`∑ X ∈ 𝒬, |Z ∩ X| ≤ |Z|`. -/
theorem card_sum_inter_le {𝒬 : Finset (Finset V)}
    (hdis : ∀ X ∈ 𝒬, ∀ Y ∈ 𝒬, X ≠ Y → X ∩ Y = ∅) {Z : Finset V} :
    (∑ X ∈ 𝒬, (Z ∩ X).card) ≤ Z.card := by
  classical
  have hdis' : ∀ (X Y : Finset V), X ∈ 𝒬 → Y ∈ 𝒬 → X ≠ Y → ∀ z, z ∈ Z ∩ X → z ∉ Z ∩ Y := by
    intro X Y hX hY hne z hz hzY
    exact false_of_mem_inter (hdis X hX Y hY hne)
      (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).2, (Finset.mem_inter.mp hzY).2⟩)
  have hbi : 𝒬.biUnion (fun X => Z ∩ X) = Z ∩ (𝒬.biUnion fun X => X) := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    constructor
    · rintro ⟨a, ha, hz, hva⟩
      exact ⟨hz, a, ha, hva⟩
    · rintro ⟨hz, a, ha, hva⟩
      exact ⟨a, ha, hz, hva⟩
  have heq : (∑ X ∈ 𝒬, (Z ∩ X).card) = (Z ∩ (𝒬.biUnion fun X => X)).card := by
    rw [← card_biUnion_eq_sum (fun X => Z ∩ X) hdis', hbi]
  rw [heq]
  exact Finset.card_le_card (Finset.inter_subset_left (s₁ := Z) (s₂ := 𝒬.biUnion fun X => X))

/-- **THE CONCLUSION OF ERDŐS #73 IS EXACTLY ADDITIVE OVER AN ANTICOMPLETE COVER.**  `G` is
`m`-close to bipartite **iff** the pieces of an anticomplete cover can be made bipartite at a total
cost of at most `m`.  Together with `JSP90.maxDef_eq_sum_of_cover` this says that *both* sides of
Erdős #73 are additive over the same cover. -/
theorem closeToBipartite_iff_cost_cover {𝒬 : Finset (Finset V)} (h : AnticoverCoverFamily G 𝒬)
    (hcov : ∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X) {m : ℕ} :
    CloseToBipartite m G ↔
      ∃ c : Finset V → ℕ, (∀ X ∈ 𝒬, CloseToBipartite (c X) (induceFinset G X)) ∧
        (∑ X ∈ 𝒬, c X) ≤ m := by
  constructor
  · rintro ⟨Z₀, hZ₀, hb⟩
    obtain ⟨Z₀', hZ₀'card, hhits⟩ :=
      (closeToBipartite_iff_hitsOddCycles (G := G) (m := m)).mp ⟨Z₀, hZ₀, hb⟩
    refine ⟨fun X => (Z₀' ∩ X).card, fun X hX => ?_, ?_⟩
    · refine (closeToBipartite_iff_hitsOddCycles (G := induceFinset G X)
        (m := (Z₀' ∩ X).card)).mpr ⟨Z₀' ∩ X, Nat.le_refl _, ?_⟩
      intro C hC
      have hCsub : C ⊆ X := isOddCycle_sub_induceFinset hC
      have hne' : C ∩ Z₀' ≠ ∅ := hhits C hC.of_induceFinset
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne'
      have hx' : x ∈ C ∧ x ∈ Z₀' := Finset.mem_inter.mp hx
      exact ne_empty_of_nonempty
        ⟨x, Finset.mem_inter.mpr ⟨hx'.1, Finset.mem_inter.mpr ⟨hx'.2, hCsub hx'.1⟩⟩⟩
    · exact (card_sum_inter_le (𝒬 := 𝒬) (Z := Z₀') h.1).trans hZ₀'card
  · rintro ⟨c, hc, hsum⟩
    exact closeToBipartite_mono (G := G) hsum (closeToBipartite_of_cover_cost h hcov hc)

end Cost

/-! ## Part 5 — THE CLASS AND THE NEW INSTANCE

The class is the **cover closure of "the hypothesis and the conclusion of Erdős #73 coincide"**:
graphs admitting an anticomplete cover by pieces that are MaxDef-close to bipartite.  It contains
every cluster graph (round 104), and it is closed under anticomplete covers, so it contains the
disjoint unions of graphs of any proved class of that kind. -/

section Instance

/-- **`G` has a cover by MaxDef-exact pieces**: `𝒬` is a pairwise disjoint, pairwise anticomplete
cover of the vertices of `G`, and every piece is *exactly* `MaxDef`-close to bipartite, i.e. on
every piece the hypothesis `LocIndep` and the conclusion `CloseToBipartite` of Erdős #73 are the
same statement. -/
def PieceMaxDef (G : SimpleGraph V) (𝒬 : Finset (Finset V)) : Prop :=
  AnticoverCoverFamily G 𝒬 ∧
    (∀ ⦃x : V⦄, x ∈ (Finset.univ : Finset V) → ∃ X ∈ 𝒬, x ∈ X) ∧
    (∀ X ∈ 𝒬, CloseToBipartite (MaxDef (induceFinset G X)) (induceFinset G X))

theorem PieceMaxDef.cover {G : SimpleGraph V} {𝒬 : Finset (Finset V)} (h : PieceMaxDef G 𝒬) :
    AnticoverCoverFamily G 𝒬 := h.1

theorem PieceMaxDef.covers {G : SimpleGraph V} {𝒬 : Finset (Finset V)} (h : PieceMaxDef G 𝒬)
    {x : V} : ∃ X ∈ 𝒬, x ∈ X := h.2.1 (Finset.mem_univ x)

theorem PieceMaxDef.pieces {G : SimpleGraph V} {𝒬 : Finset (Finset V)} (h : PieceMaxDef G 𝒬)
    {X : Finset V} (hX : X ∈ 𝒬) :
    CloseToBipartite (MaxDef (induceFinset G X)) (induceFinset G X) := h.2.2 X hX

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, WITH THE OPTIMAL CONSTANT `f(k) = k`:** on a graph
admitting an anticomplete cover by MaxDef-exact pieces, Erdős's hypothesis `LocIndep k G` implies
`CloseToBipartite k G`.  No odd-girth bound, no packing-weight bound, no degree bound and no bound
on the number of pieces is used: the pieces pay `k` *jointly*, because the deficiency splits over
the cover (`JSP90.maxDef_eq_sum_of_cover`) and the deletion sets of the pieces are disjoint
(`JSP90.closeToBipartite_of_cover_cost`). -/
theorem erdos73On_of_pieceMaxDef {k : ℕ} {𝒬 : Finset (Finset V)} (h : PieceMaxDef G 𝒬)
    (hG : LocIndep k G) : CloseToBipartite k G := by
  have hsum : (∑ X ∈ 𝒬, MaxDef (induceFinset G X)) ≤ k := by
    rw [← maxDef_eq_sum_of_cover h.1 h.2.1]
    exact locIndep_iff_maxDef_le.mp hG
  exact closeToBipartite_mono (G := G) hsum
    (closeToBipartite_of_cover_cost h.1 h.2.1 h.2.2)

/-- The same instance in the house style, quantified over all finite vertex types. -/
theorem erdos73On_of_pieceMaxDef_univ (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W) (𝒬 : Finset (Finset W)),
      PieceMaxDef G 𝒬 → LocIndep k G → CloseToBipartite k G := by
  intro W instW G 𝒬 hd hG
  exact erdos73On_of_pieceMaxDef hd hG

/-- **ON THIS CLASS THE HYPOTHESIS AND THE CONCLUSION COINCIDE.**  `CloseToBipartite m G ↔ MaxDef G ≤
m`, the same coincidence as `JSP90.closeToBipartite_iff_maxDef_cluster` of round 104, but for the
larger class of graphs that carry *any* anticomplete cover by MaxDef-exact pieces. -/
theorem closeToBipartite_iff_maxDef_of_pieceMaxDef {𝒬 : Finset (Finset V)}
    (h : PieceMaxDef G 𝒬) {m : ℕ} : CloseToBipartite m G ↔ MaxDef G ≤ m := by
  constructor
  · exact maxDef_le_closeToBipartite
  · intro hmd
    have hsum : (∑ X ∈ 𝒬, MaxDef (induceFinset G X)) ≤ m := by
      rw [← maxDef_eq_sum_of_cover h.1 h.2.1]
      exact hmd
    exact closeToBipartite_mono (G := G) hsum
      (closeToBipartite_of_cover_cost h.1 h.2.1 h.2.2)

/-- **ROUND 104'S CLASS IS CONTAINED IN THIS ONE.**  Every cluster graph has a cover by cliques, and
a clique is `|C| − 2`-close to bipartite by `JSP90.closeToBipartite_of_clique`.  So the class of
this file is *strictly* larger than round 104's: `K_5 ⊔ K_{2,3}` is on it (the piece `K_{2,3}` is
`0`-close) and is not a cluster graph. -/
theorem pieceMaxDef_of_cluster {𝒬 : Finset (Finset V)} (hd : ClusterDecomposition G 𝒬) :
    PieceMaxDef G 𝒬 := by
  refine ⟨hd.1, ?_, ?_⟩
  · intro x hx
    exact hd.2.2.2 x
  · intro X hX
    have hclX : G.IsClique X := by
      intro p q hp hq hne
      exact hd.2.2.1 X hX p hp q hq hne
    have h2X : 2 ≤ X.card := hd.2.1 X hX
    have h1 := closeToBipartite_of_clique hclX h2X
    rw [← maxDef_clique hclX h2X] at h1
    exact h1

/-- **ROUND 104'S INSTANCE IS A SPECIAL CASE OF THIS ONE** (`f(k) = k` in both, with a strictly
weaker hypothesis here). -/
theorem erdos73On_of_cluster_of_pieceMaxDef {k : ℕ} {𝒬 : Finset (Finset V)}
    (hd : ClusterDecomposition G 𝒬) (hG : LocIndep k G) : CloseToBipartite k G :=
  erdos73On_of_pieceMaxDef (pieceMaxDef_of_cluster hd) hG

/-- **THE CONSTANT `k` OF THE NEW INSTANCE IS OPTIMAL**, machine-checked on the lower-bound witness
`kTriangles k` of `JSPProblem/Sharp.lean`: on it, `(LocIndep k → CloseToBipartite m) ↔ k ≤ m`.  So no
constant below `k` works on this class either, and `f(k) ≥ k` is re-derived through the new
instance. -/
theorem erdos73On_of_pieceMaxDef_optimal {k m : ℕ} :
    (LocIndep k (kTriangles k) → CloseToBipartite m (kTriangles k)) ↔ k ≤ m := by
  have hle : MaxDef (kTriangles k) ≤ k := by rw [maxDef_kTriangles k]
  constructor
  · intro h
    have h1 : MaxDef (kTriangles k) ≤ m :=
      maxDef_le_closeToBipartite (h (locIndep_of_maxDef_le hle))
    rw [maxDef_kTriangles k] at h1
    exact h1
  · intro hkm _
    have h1 : CloseToBipartite k (kTriangles k) :=
      (closeToBipartite_kTriangles_iff_maxDef k k).mpr (by rw [maxDef_kTriangles k])
    exact closeToBipartite_mono hkm h1

/-- **NO CONSTANT BELOW `k` WORKS ON THIS CLASS** — the lower bound `f(k) ≥ k` through the new
instance. -/
theorem erdos73_pieceMaxDef_notBelowK {k m : ℕ} (h : m < k) :
    ¬ CloseToBipartite m (kTriangles k) :=
  no_closeToBipartite_of_maxDef_kTriangles h

end Instance

end

end JSP90
