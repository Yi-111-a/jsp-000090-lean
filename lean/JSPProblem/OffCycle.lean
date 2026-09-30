/-
# JSP-000090, round 59 — **the deficiency off an odd cycle**

## What this file is

Round 54 replaced the hypothesis `LocIndep k G` of Erdős Problem #73 by the single **number**

```lean
MaxDef G = max { |X| - 2 * α(G[X]) : X ⊆ V }
```

and proved the sandwich `ν(G) ≤ MaxDef G ≤ τ(G)` (`JSPProblem/Deficiency.lean`, Part 3).  That
file ends with a *secondary blocker*, recorded in `discovery/JSP-000090/policy.json`:

> the equality version of the anticomplete additivity of `MaxDef` (needs
> `indepCard (G[s]) (X + {v}) = indepCard (G[s]) X + 1` for `v ∉ s`)

together with the note that

> the truncated deficiency is the wrong object for an additive argument: look for an
> **untruncated** surrogate

because `defOf` is truncated at zero (`Nat` subtraction): for a triangle together with one isolated
vertex the deficiency of the whole is `0` while the sum of the two parts is `1 + 0 = 1`.

**This file is the twelfth attack family** and it answers that note.  The right anchor is not an
arbitrary vertex set but **an odd cycle**: an odd cycle has deficiency *at least* `1`, so the
truncation can never bite, and the additivity becomes exact.  The result is

```lean
maxDef_ge_one_add_maxDef_of_oddCycle :
    IsOddCycle G C → (C and X disjoint, no edge between them) →
      1 + MaxDef (G[X]) ≤ MaxDef G
```

**THE DEFICIENCY OF A GRAPH IS THE DEFICIENCY OFF AN ODD CYCLE, PLUS ONE.**  Read classically:
*the part of `G` that hangs off an odd cycle has deficiency at most `MaxDef G - 1`*, so an
induction on the deficiency **does** make progress at an odd cycle — provided the odd cycle is
separated from the rest.  Rounds 42–48 proved the additive *conclusion* over anticomplete
decompositions (`JSP90.closeToBipartite_of_anticover`) and round 54 proved the subadditive
*hypothesis* (`JSP90.maxDef_le_add_of_anticover`, the `≤` direction only).  This file proves the
*other* direction of the hypothesis, in the sharp form, and identifies exactly when the induction
on `MaxDef` is legitimate:

* `maxDef_offCycle_le` (Part 3) — `MaxDef G ≤ k` and `1 ≤ k` give `MaxDef (G[X]) ≤ k - 1` for `X`
  separated from an odd cycle: **the induction measure decreases**;
* `isBipartite_offCycle_of_maxDef_le_one` — `MaxDef G ≤ 1` and `X` separated from an odd cycle give
  `G[X].IsBipartite`: **the `k = 1` case has a local reading** — everything hanging off an odd
  cycle is bipartite;
* `card_clique_offCycle_le` — a clique separated from an odd cycle has at most `MaxDef G + 1`
  vertices;
* `locIndep_of_separated_oddCycle` — `LocIndep` is inherited by the residue of a separated odd
  cycle with the parameter **decreased by one** (the existing `JSP90.LocIndep.of_deleteFinset`
  keeps it);
* Part 5 turns these into **a new instance of the headline theorem**: for graphs whose odd cycles
  are *layers* — pairwise vertex-disjoint, each separated from everything outside it, and every
  odd cycle of `G` being one of them — Erdős #73 holds with the **sharp constant `k`**
  (`erdos73On_of_layered`), proved by an induction on the deficiency, the first time this
  development proves an instance of the headline theorem that way.  The class is attained
  (`layeredOddCycles_kTriangles`) and closed under the deletion used in the induction
  (`layeredOddCycles_erase`).

## What is *not* proved

The layer condition of `LayeredOddCycles` is a genuine extra hypothesis: the graphs of Erdős #73
whose odd cycles *meet* (the "three triangles in a ring" on `6` vertices, or `K_5`) are **not**
layered, and for them the induction on `MaxDef` does not close.  The general theorem
(`MaxDef G ≤ k → CloseToBipartite (C * MaxDef G) G`, or equivalently `Erdős73 k`) is not proved
here; `JSP90.OddCycleErdosPosa` remains the primary blocker.  What is new is (i) the exact
additivity of the deficiency between an odd cycle and a separated set, (ii) the `MaxDef`-induction
step that it licenses, and (iii) the first `MaxDef`-inductive instance of the headline theorem. -/

import JSPProblem.Deficiency
import Mathlib.Data.Finset.SDiff

namespace JSP90

universe u

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqOff : DecidableEq V := Classical.decEq V

local instance instDecidablePredIndepOff (G : SimpleGraph V) :
    DecidablePred fun S : Finset V => G.IsIndepSet S := fun _ => Classical.propDecidable _

/-! ## Part 1 — the independence number is additive over separated unions

The statement `JSP90.card_indepCard_anticover_add` of `JSPProblem/Deficiency.lean` (Part 6) needs
the two parts of a decomposition to *cover* the vertex set.  The lemma below is the same statement
with no cover condition, for two arbitrary vertex sets; it is the ingredient the deficiency
arithmetic needs. -/

section Add

/-- **Two vertex sets separated from each other.**  `A` and `B` are **separated in `G`** if they are
disjoint and no edge of `G` joins them.  This is `JSP90.Anticover` (of `JSPProblem/Optimal.lean`)
*without* the cover condition: the two sets need not cover the vertex set. -/
def Separated (G : SimpleGraph V) (A B : Finset V) : Prop :=
  Disjoint A B ∧ ∀ (v : V) (hA : v ∈ A) (w : V) (hB : w ∈ B), ¬ G.Adj v w

/-- **THE INDEPENDENCE NUMBER IS ADDITIVE OVER SEPARATED UNIONS.**  If `A` and `B` are separated in
`G`, then the largest independent set of `G[A ∪ B]` is the disjoint union of a largest independent
set of `G[A]` and one of `G[B]`:

```lean
α(G[A ∪ B]) = α(G[A]) + α(G[B]).
```

This is `JSP90.card_indepCard_anticover_add` with the cover condition dropped, and it is the
combinatorial core of Part 2. -/
theorem indepCard_separated_add {A B : Finset V} (hAB : Separated G A B) :
    indepCard G (A ∪ B) = indepCard (induceFinset G A) A + indepCard (induceFinset G B) B := by
  obtain ⟨hdisj, hanti⟩ := hAB
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le_iff.mpr fun S hS => ?_
    have hSi : G.IsIndepSet S := (Finset.mem_filter.mp hS).2
    have hSsub : S ⊆ A ∪ B := sub_of_mem_indepSets hS
    have h1 : (S ∩ A : Finset V).card ≤ indepCard (induceFinset G A) A := by
      refine le_indepCard ?_
      set T : Finset V := S ∩ A with hT
      have hTA : T ⊆ A := by
        intro v hv
        rw [hT] at hv
        exact (Finset.mem_inter.mp hv).2
      have hTS : T ⊆ S := by
        intro v hv
        rw [hT] at hv
        exact (Finset.mem_inter.mp hv).1
      have hSiT : G.IsIndepSet T := IsIndepSet.subset (G := G) hSi hTS
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTA,
        isIndepSet_induceFinset_iff hTA |>.mpr hSiT⟩
    have h2 : (S ∩ B : Finset V).card ≤ indepCard (induceFinset G B) B := by
      refine le_indepCard ?_
      set T : Finset V := S ∩ B with hT
      have hTB : T ⊆ B := by
        intro v hv
        rw [hT] at hv
        exact (Finset.mem_inter.mp hv).2
      have hTS : T ⊆ S := by
        intro v hv
        rw [hT] at hv
        exact (Finset.mem_inter.mp hv).1
      have hSiT : G.IsIndepSet T := IsIndepSet.subset (G := G) hSi hTS
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTB,
        isIndepSet_induceFinset_iff hTB |>.mpr hSiT⟩
    have hsplit := card_inter_add_card_sdiff S B
    have h4 : S \ B ⊆ S ∩ A := by
      intro v hv
      have hv' := Finset.mem_sdiff.mp hv
      rcases Finset.mem_union.mp (hSsub hv'.1) with hA | hB
      · exact Finset.mem_inter.mpr ⟨hv'.1, hA⟩
      · exact absurd hB hv'.2
    have h4card : (S \ B).card ≤ (S ∩ A).card := Finset.card_le_card h4
    omega
  · obtain ⟨SA, hSAsub, hSAi, hSAcard⟩ := exists_indepCard (induceFinset G A) A
    obtain ⟨SB, hSBsub, hSBi, hSBcard⟩ := exists_indepCard (induceFinset G B) B
    have hmem : SA ∪ SB ∈ indepSets G (A ∪ B) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (fun v hv => ?_), ?_⟩
      · rcases Finset.mem_union.mp hv with hA | hB
        · exact Finset.mem_union_left _ (Finset.mem_of_subset hSAsub hA)
        · exact Finset.mem_union_right _ (Finset.mem_of_subset hSBsub hB)
      have hanti' : ∀ (v : V), v ∈ B → ∀ (w : V), w ∈ A → ¬ G.Adj v w := by
        intro v hvB w hwA h
        exact hanti w hwA v hvB h.symm
      refine isIndepSet_of_intro fun v w hv hw hne hadj => ?_
      have hvU : v ∈ SA ∨ v ∈ SB := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mpr hv) with h1 | h2
        · exact Or.inl h1
        · exact Or.inr h2
      have hwU : w ∈ SA ∨ w ∈ SB := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mpr hw) with h1 | h2
        · exact Or.inl h1
        · exact Or.inr h2
      rcases hvU with hA1 | hB1
      · rcases hwU with hA2 | hB2
        · exact IsIndepSet.apply' (G := G) (IsIndepSet.of_induceFinset hSAi hSAsub)
              hA1 hA2 hne hadj
        · exact hanti v (Finset.mem_of_subset hSAsub hA1) w (Finset.mem_of_subset hSBsub hB2) hadj
      · rcases hwU with hA2 | hB2
        · exact hanti' v (Finset.mem_of_subset hSBsub hB1) w (Finset.mem_of_subset hSAsub hA2) hadj
        · exact IsIndepSet.apply' (G := G) (IsIndepSet.of_induceFinset hSBi hSBsub)
              hB1 hB2 hne hadj
    have hcard : (SA ∪ SB).card = SA.card + SB.card :=
      Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (fun v hv1 hv2 =>
        Finset.disjoint_left.mp hdisj (Finset.mem_of_subset hSAsub hv1)
          (Finset.mem_of_subset hSBsub hv2)))
    rw [← hSAcard, ← hSBcard, ← hcard]
    exact le_indepCard hmem

/-- **`1 ≤ n - m` implies `m + 1 ≤ n`.**  This is the statement that a vertex set whose deficiency
is at least `1` is *not* truncated: the `Nat` subtraction `|X| - 2 * α` in `defOf` is the true
integer difference.  It is stated as a lemma because the `omega` of the pinned Mathlib does not
eliminate `Nat` subtraction out of hypotheses. -/
theorem le_succ_of_sub_pos {n m : ℕ} (h : 1 ≤ n - m) : m + 1 ≤ n := by
  exact Nat.succ_le_of_lt (Nat.sub_pos_iff_lt.mp (by omega))

/-- **`n + 1 ≤ m` and `m ≤ k` give `n ≤ k - 1`** — the arithmetic step of every use of
`JSP90.maxDef_offCycle_le` below.  It is stated as a lemma because `omega` in the pinned Mathlib does
not eliminate the truncation of `k - 1`. -/
theorem le_pred_of_succ_le {n m k : ℕ} (h1 : n + 1 ≤ m) (h2 : m ≤ k) : n ≤ k - 1 :=
  Nat.le_pred_of_lt (Nat.lt_of_succ_le (h1.trans h2))

/-- **THE COUNTING FORM OF THE ADDITIVITY**, phrased so that the truncation at zero of `Nat`
subtraction cannot interfere:

```lean
|A| + |B| - 2 * (α(G[A]) + α(G[B])) = defOf G (A ∪ B).
``` -/
theorem card_sub_two_separated_add {A B : Finset V} (hAB : Separated G A B) :
    A.card + B.card - 2 * (indepCard (induceFinset G A) A + indepCard (induceFinset G B) B)
      = defOf G (A ∪ B) := by
  have hcard : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB.1
  have hα := indepCard_separated_add hAB
  simp only [defOf, hcard, hα, Nat.mul_add]

/-- **EXACT ADDITIVITY OF THE DEFICIENCY, IN THE UNTRUNCATED REGIME.**  If `A` and `B` are separated
in `G` and *both* parts are `0`-deficient or worse (`2 * α(G[A]) ≤ |A|` and `2 * α(G[B]) ≤ |B|`,
which is automatic whenever the part carries an odd cycle), then

```lean
defOf G (A ∪ B) = defOf G[A] + defOf G[B]
```

**with equality**, not with the `≤` of `JSP90.maxDef_le_add_of_anticover`.

The two hypotheses are exactly what rules out the truncation, and they answer the "untruncated
surrogate" question of `discovery/JSP-000090/policy.json`: the deficiency of a part is never
truncated as soon as that part has deficiency `≥ 1`, so once *one* of the two parts carries an odd
cycle the additivity is exact.  Part 2 applies this with `A` an odd cycle. -/
theorem defOf_separated_add_of_nonneg {A B : Finset V} (hAB : Separated G A B)
    (hA : 2 * indepCard (induceFinset G A) A ≤ A.card)
    (hB : 2 * indepCard (induceFinset G B) B ≤ B.card) :
    defOf G (A ∪ B) = defOf (induceFinset G A) A + defOf (induceFinset G B) B := by
  have h1 := card_sub_two_separated_add hAB
  simp only [defOf] at h1 ⊢
  omega

/-- **`α(G[s]) = α(G)`: the independence number of a vertex set is that of the graph it
induces.**  This is what lets a deficiency be read inside a residue. -/
theorem indepSets_induceFinset (G : SimpleGraph V) (s : Finset V) :
    indepSets G s = indepSets (induceFinset G s) s := by
  ext S
  simp only [indepSets, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hS, hSi⟩
    exact ⟨hS, isIndepSet_induceFinset_iff hS |>.mpr hSi⟩
  · rintro ⟨hS, hSi⟩
    exact ⟨hS, isIndepSet_induceFinset_iff hS |>.mp hSi⟩

theorem indepCard_induceFinset (G : SimpleGraph V) (s : Finset V) :
    indepCard G s = indepCard (induceFinset G s) s := by
  unfold indepCard
  rw [indepSets_induceFinset]

/-- **The independence number of `X ∩ Y` is the same computed in `G[X]` and in `G[X ∩ Y]`** —
the technical fact that lets a deficiency be transported between a residue and the original
graph. -/
theorem indepCard_induceFinset_inter (G : SimpleGraph V) (X Y : Finset V) :
    indepCard (induceFinset G X) (X ∩ Y) = indepCard (induceFinset G (X ∩ Y)) (X ∩ Y) := by
  unfold indepCard
  congr 1
  ext S
  simp only [indepSets, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hS, hSi⟩
    have hSX : S ⊆ X := fun v hv => (Finset.mem_inter.mp (hS hv)).1
    exact ⟨hS, isIndepSet_induceFinset_iff (G := G) (S := S) (s := X ∩ Y) hS |>.mpr
      (isIndepSet_induceFinset_iff (G := G) (S := S) (s := X) hSX |>.mp hSi)⟩
  · rintro ⟨hS, hSi⟩
    have hSXY : S ⊆ X ∩ Y := fun v hv => hS hv
    have hSX : S ⊆ X := fun v hv => (Finset.mem_inter.mp (hS hv)).1
    exact ⟨hS, isIndepSet_induceFinset_iff (G := G) (S := S) (s := X) hSX |>.mpr
      (isIndepSet_induceFinset_iff (G := G) (S := S) (s := X ∩ Y) hSXY |>.mp hSi)⟩

/-- Consequently the deficiency of a vertex set is that of the graph it induces. -/
theorem defOf_induceFinset (G : SimpleGraph V) (s : Finset V) :
    defOf G s = defOf (induceFinset G s) s := by
  unfold defOf
  rw [indepCard_induceFinset]

/-- **A vertex set outside `X` is never where the deficiency of `G[X]` is largest.**  Inside the
graph `G[X]` the vertices outside `X` are isolated, so an independent set of `G[X]` lying in `Y`
consists of an independent set inside `X ∩ Y` together with all of `Y \ X`.  Consequently
`defOf (G[X]) Y ≤ defOf (G[X]) (X ∩ Y)`, and the maximiser of `MaxDef (G[X])` may be taken inside
`X`.  This is the technical point that lets Part 2 use `defOf_separated_add_of_nonneg` with the
maximiser of `MaxDef (G[X])`. -/
theorem defOf_induceFinset_le_inter {X Y : Finset V} :
    defOf (induceFinset G X) Y ≤ defOf (induceFinset G X) (X ∩ Y) := by
  have hα : indepCard (induceFinset G X) Y
      = indepCard (induceFinset G X) (X ∩ Y) + (Y \ X).card := by
    refine le_antisymm ?_ ?_
    · refine Finset.sup_le_iff.mpr fun S hS => ?_
      have hSi : (induceFinset G X).IsIndepSet S := (Finset.mem_filter.mp hS).2
      have hSsub : S ⊆ Y := sub_of_mem_indepSets hS
      have h1 : (S ∩ X : Finset V).card ≤ indepCard (induceFinset G X) (X ∩ Y) := by
        refine le_indepCard ?_
        set T : Finset V := S ∩ X with hT
        have hTsub : T ⊆ X ∩ Y := by
          intro v hv
          rw [hT] at hv
          have hv' := Finset.mem_inter.mp hv
          exact Finset.mem_inter.mpr ⟨hv'.2, hSsub hv'.1⟩
        have hTS : T ⊆ S := by
          intro v hv
          rw [hT] at hv
          exact (Finset.mem_inter.mp hv).1
        have hSiT : (induceFinset G X).IsIndepSet T := IsIndepSet.subset hSi hTS
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTsub, hSiT⟩
      have h2 : (S \ X).card ≤ (Y \ X).card := by
        refine Finset.card_le_card fun v hv => ?_
        have hv' := Finset.mem_sdiff.mp hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_of_subset hSsub hv'.1, hv'.2⟩
      have hsplit := card_inter_add_card_sdiff S X
      omega
    · obtain ⟨SX, hSXsub, hSXi, hSXcard⟩ := exists_indepCard (induceFinset G X) (X ∩ Y)
      have hSXsubY : SX ⊆ Y := fun v hv => (Finset.mem_inter.mp (hSXsub hv)).2
      set U : Finset V := SX ∪ (Y \ X) with hU
      have hUsub : U ⊆ Y := by
        rw [hU]
        exact Finset.union_subset hSXsubY (Finset.sdiff_subset)
      have hSiU : (induceFinset G X).IsIndepSet U := by
        refine isIndepSet_of_intro fun v w hv hw hne hadj => ?_
        have hAdj := (induce_adj.mp hadj)
        have hv' : v ∈ U := Finset.mem_coe.mpr hv
        have hw' : w ∈ U := Finset.mem_coe.mpr hw
        rcases Finset.mem_union.mp hv' with hvX | hvY
        · rcases Finset.mem_union.mp hw' with hwX | hwY
          · refine IsIndepSet.apply' hSXi hvX hwX hne ?_
            exact hadj
          · exact (Finset.mem_sdiff.mp hwY).2 hAdj.2.1
        · exact (Finset.mem_sdiff.mp hvY).2 hAdj.1
      have hmem : U ∈ indepSets (induceFinset G X) Y :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUsub, hSiU⟩
      have hdisjU : Disjoint SX (Y \ X) := Finset.disjoint_left.mpr fun v hv1 hv2 =>
        absurd (Finset.mem_of_subset hSXsub hv1)
          (fun hX => (Finset.mem_sdiff.mp hv2).2 (Finset.mem_inter.mp hX).1)
      calc indepCard (induceFinset G X) (X ∩ Y) + (Y \ X).card
          = SX.card + (Y \ X).card := by rw [hSXcard]
        _ = U.card := by rw [hU, Finset.card_union_of_disjoint hdisjU]
        _ ≤ indepCard (induceFinset G X) Y := le_indepCard hmem
  simp only [defOf, hα]
  have hcard : Y.card = (X ∩ Y).card + (Y \ X).card := by
    have h1 := card_inter_add_card_sdiff Y X
    rw [← congrArg Finset.card (Finset.inter_comm X Y)] at h1
    omega
  omega

/-- **A separated pair in a residue is a separated pair in `G`**: deleting vertices cannot create an
edge. -/
theorem Separated.deleteFinset [Fintype V] {A B : Finset V} (hAB : Separated G A B) (X : Finset V) :
    Separated (deleteFinset G X) A B :=
  ⟨hAB.1, fun v hvA w hwB hadj => hAB.2 v hvA w hwB (deleteFinset_adj.mp hadj).2.2⟩

end Add

/-! ## Part 2 — an odd cycle has deficiency at least one, and the two facts combine

The classical bound `α(C_m) ≤ ⌊m / 2⌋` of `JSP90.indep_card_le_of_odd_cycle`
(`JSPProblem/OddCycle.lean`) is the only input. -/

section OddCycleDef

/-- **AN ODD CYCLE HAS DEFICIENCY AT LEAST ONE.**  In the numerical language of
`JSPProblem/Deficiency.lean`:

```lean
2 * α(G[C]) + 1 ≤ |C|,    i.e.    defOf G[C] C ≥ 1.
```

This is the "one" of the `+ 1` in the main theorem of Part 2: an odd cycle is the cheapest
non-bipartite graph there is, and it costs exactly one unit of deficiency. -/
theorem two_indepCard_add_one_le_card_of_oddCycle {C : Finset V} (hC : IsOddCycle G C) :
    2 * indepCard (induceFinset G C) C + 1 ≤ C.card := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  have hCcard : C.card = m := by
    have heq : C = (Finset.univ : Finset (Fin m)).image f := by
      apply Finset.ext
      intro x
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := (hmem x).mp (Finset.mem_coe.mpr hx)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
      · intro hx
        obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
        exact Finset.mem_coe.mpr (hmem x |>.mpr ⟨i, hi⟩)
    rw [heq, Finset.card_image_of_injective (Finset.univ : Finset (Fin m)) hinj]
    simp
  obtain ⟨S, hSsub, hSi, hScard⟩ := exists_indepCard (induceFinset G C) C
  have hSiG : G.IsIndepSet S := IsIndepSet.of_induceFinset hSi hSsub
  have hSin : ∀ ⦃x : V⦄, x ∈ (S : Set V) → ∃ i : Fin m, f i = x := by
    intro x hx
    obtain ⟨i, hi⟩ := (hmem x).mp (Finset.mem_coe.mpr (Finset.mem_of_subset hSsub hx))
    exact ⟨i, hi⟩
  have hle := indep_card_le_of_odd_cycle hm f hinj hcyc S hSiG hSin
  omega

/-- **The deficiency of an odd cycle, as a vertex set of `G`, is at least one.** -/
theorem defOf_oddCycle_ge_one {C : Finset V} (hC : IsOddCycle G C) :
    1 ≤ defOf (induceFinset G C) C := by
  have h := two_indepCard_add_one_le_card_of_oddCycle hC
  simp only [defOf]
  omega

/-! ### THE MAIN THEOREM -/

/-- **THE DEFICIENCY OF A GRAPH IS THE DEFICIENCY OFF AN ODD CYCLE, PLUS ONE.**

Let `C` be an odd cycle of `G` and let `X ⊆ V` be separated from it (disjoint, and no edge of `G`
joins `C` to `X`).  Then

```lean
1 + MaxDef (G[X]) ≤ MaxDef G.
```

In words: **the part of `G` hanging off an odd cycle has deficiency at most `MaxDef G - 1`.**

This is the *other* direction of the anticomplete additivity of `JSPProblem/Deficiency.lean`
(`maxDef_le_add_of_anticover` is the `≤` direction; the file header of this one explains why the
`≥` direction fails in general and holds at an odd cycle), and it is what makes an **induction on
`MaxDef` legitimate at an odd cycle**. -/
theorem maxDef_ge_one_add_maxDef_of_oddCycle {C X : Finset V} (hC : IsOddCycle G C)
    (hCX : Separated G C X) : 1 + MaxDef (induceFinset G X) ≤ MaxDef G := by
  by_cases hzero : MaxDef (induceFinset G X) = 0
  · -- the "off-cycle" part is bipartite: nothing to add
    have h1 : 1 ≤ defOf G C := by
      rw [defOf_induceFinset G C]
      exact defOf_oddCycle_ge_one hC
    rw [hzero]
    exact le_trans (by omega) (le_maxDef G C)
  · obtain ⟨Y, hY⟩ := exists_eq_maxDef (induceFinset G X)
    -- the maximiser may be taken inside `X` (Part 1, `defOf_induceFinset_le_inter`)
    have hle := le_maxDef (induceFinset G X) (X ∩ Y)
    have hge := defOf_induceFinset_le_inter (G := G) (X := X) (Y := Y)
    have hZmax : defOf (induceFinset G X) (X ∩ Y) = MaxDef (induceFinset G X) := by omega
    have hsub : (X ∩ Y : Finset V) ⊆ X := fun _ hv => (Finset.mem_inter.mp hv).1
    have hYZ : Separated G C (X ∩ Y) :=
      ⟨Finset.disjoint_left.mpr fun v hvC hvZ =>
          Finset.disjoint_left.mp hCX.1 hvC (Finset.mem_of_subset hsub hvZ),
        fun v hvC w hwZ => hCX.2 v hvC w (Finset.mem_of_subset hsub hwZ)⟩
    have hA : 2 * indepCard (induceFinset G C) C ≤ C.card := by
      have h1 := two_indepCard_add_one_le_card_of_oddCycle hC
      omega
    have hZpos : 1 ≤ MaxDef (induceFinset G X) := Nat.pos_of_ne_zero hzero
    have hB : 2 * indepCard (induceFinset G (X ∩ Y)) (X ∩ Y) ≤ (X ∩ Y).card := by
      have h1 : defOf (induceFinset G (X ∩ Y)) (X ∩ Y) = MaxDef (induceFinset G X) := by
        rw [← hZmax]
        unfold defOf
        rw [indepCard_induceFinset_inter]
      have h1u : (X ∩ Y).card - 2 * indepCard (induceFinset G (X ∩ Y)) (X ∩ Y)
          = MaxDef (induceFinset G X) := h1
      have h1' : 1 ≤ (X ∩ Y).card - 2 * indepCard (induceFinset G (X ∩ Y)) (X ∩ Y) := by
        rw [h1u]
        exact hZpos
      have h2 := le_succ_of_sub_pos h1'
      omega
    have hEq := defOf_separated_add_of_nonneg hYZ hA hB
    have hge1 : 1 ≤ defOf (induceFinset G C) C := defOf_oddCycle_ge_one hC
    have hmax : defOf G (C ∪ (X ∩ Y)) ≤ MaxDef G := le_maxDef G (C ∪ (X ∩ Y))
    rw [hEq] at hmax
    have hZmax2 : MaxDef (induceFinset G X) = defOf (induceFinset G (X ∩ Y)) (X ∩ Y) := by
      have h1 : defOf (induceFinset G (X ∩ Y)) (X ∩ Y) = MaxDef (induceFinset G X) := by
        rw [← hZmax]
        unfold defOf
        rw [indepCard_induceFinset_inter]
      exact h1.symm
    rw [hZmax2]
    omega

/-- **A graph with an odd cycle has deficiency at least `1`.**  This is the numerical form of
`JSP90.maxDef_pos_of_not_isBipartite` of `JSPProblem/Deficiency.lean`, obtained here from the main
theorem with the empty separated set. -/
theorem maxDef_ge_one_of_oddCycle {C : Finset V} (hC : IsOddCycle G C) : 1 ≤ MaxDef G := by
  have h1 := maxDef_ge_one_add_maxDef_of_oddCycle (X := (∅ : Finset V)) hC
    (by simp [Separated])
  have h0 : MaxDef (induceFinset G (∅ : Finset V)) = 0 := maxDef_eq_zero_iff.mpr
    (isBipartite_induceFinset_of_card_le_two (G := G) (s := ∅) (by simp))
  rw [h0, Nat.add_zero] at h1
  exact h1

end OddCycleDef

/-! ## Part 3 — the consequences: the induction measure, the `k = 1` case, clique bounds -/

section Corollaries

/-- **THE INDUCTION MEASURE DECREASES OFF AN ODD CYCLE.**  If `MaxDef G ≤ k` with `1 ≤ k` and `X`
is separated from an odd cycle of `G`, then

```lean
MaxDef (G[X]) ≤ k - 1.
```

Together with `JSP90.maxDef_deleteFinset_le` (which only says the measure does not *increase*), this
is the step an induction on the deficiency needs, and it is the quantitative form of the classical
statement "an odd cycle costs one unit of deficiency, and the rest of the graph is one unit
cheaper". -/
theorem maxDef_offCycle_le {C X : Finset V} (hC : IsOddCycle G C) (hCX : Separated G C X)
    {k : ℕ} (hk : 1 ≤ k) (hG : MaxDef G ≤ k) : MaxDef (induceFinset G X) ≤ k - 1 := by
  have h := maxDef_ge_one_add_maxDef_of_oddCycle hC hCX
  have h1 : MaxDef (induceFinset G X) + 1 ≤ MaxDef G := by
    simpa [Nat.add_comm] using h
  exact le_pred_of_succ_le h1 hG

/-- **THE INDUCTION MEASURE, ON THE RESIDUE.**  Deleting an odd cycle that is separated from the
rest of the graph decreases the deficiency by at least one. -/
theorem maxDef_deleteFinset_oddCycle_le {C : Finset V} (hC : IsOddCycle G C)
    (hanti : ∀ v ∈ C, ∀ w ∉ C, ¬ G.Adj v w) {k : ℕ} (hk : 1 ≤ k) (hG : MaxDef G ≤ k) :
    MaxDef (deleteFinset G C) ≤ k - 1 := by
  have hsep : Separated G C ((Finset.univ : Finset V) \ C) :=
    ⟨Finset.disjoint_right.mpr fun a ha hC => (Finset.mem_sdiff.mp ha).2 hC,
      fun v hvC w hw => hanti v hvC w (by simpa using hw)⟩
  have h := maxDef_ge_one_add_maxDef_of_oddCycle hC hsep
  have hid : MaxDef (deleteFinset G C) = MaxDef (induceFinset G ((Finset.univ : Finset V) \ C)) := rfl
  rw [← hid] at h
  have h1 : MaxDef (deleteFinset G C) + 1 ≤ MaxDef G := by
    simpa [Nat.add_comm] using h
  exact le_pred_of_succ_le h1 hG

/-- **THE `k = 1` CASE HAS A LOCAL READING.**  If `MaxDef G ≤ 1` and `X` is separated from an odd
cycle of `G`, then `G[X]` is **bipartite**: with deficiency `1` the whole non-bipartite content of
`G` is the odd cycle itself, and everything separated from it is `0`-deficient. -/
theorem isBipartite_offCycle_of_maxDef_le_one {C X : Finset V} (hC : IsOddCycle G C)
    (hCX : Separated G C X) (hG : MaxDef G ≤ 1) : (induceFinset G X).IsBipartite := by
  have h1 := maxDef_offCycle_le hC hCX (k := 1) (by decide) hG
  rw [Nat.sub_self] at h1
  exact (maxDef_eq_zero_iff (G := induceFinset G X)).mp (Nat.eq_zero_of_le_zero h1)

/-- **A CLIQUE SEPARATED FROM AN ODD CYCLE HAS AT MOST `MaxDef G + 1` VERTICES.**  A consequence of
Part 2: a clique is its own maximum independent set complement, so a clique of size `t` separated
from an odd cycle forces `MaxDef G ≥ t - 1`.  In particular, if `MaxDef G ≤ 1` then a clique
separated from an odd cycle has at most `2` vertices — the reason the `k = 1` case is a "triangle
plus something bipartite" case. -/
theorem card_clique_offCycle_le {C X : Finset V} (hC : IsOddCycle G C) (hCX : Separated G C X)
    (hclq : (induceFinset G X).IsClique X) : X.card ≤ MaxDef G + 1 := by
  have hA : 2 * indepCard (induceFinset G C) C ≤ C.card := by
    have h1 := two_indepCard_add_one_le_card_of_oddCycle hC
    omega
  have hge1 : 1 ≤ defOf (induceFinset G C) C := defOf_oddCycle_ge_one hC
  by_cases hXcard : X.card ≤ 1
  · omega
  · have hXne : X.Nonempty := by
      refine Finset.nonempty_iff_ne_empty.mpr ?_
      intro hX
      have hXcard0 : X.card = 0 := Finset.card_eq_zero.mpr hX
      omega
    have hα : indepCard (induceFinset G X) X = 1 := by
      refine le_antisymm
        (Finset.sup_le_iff.mpr fun S hS => indep_card_le_one_of_clique hclq
          ((Finset.mem_filter.mp hS).2) (sub_of_mem_indepSets hS))
        (by have h1 := indepCard_pos (G := induceFinset G X) hXne; omega)
    have hB : 2 * indepCard (induceFinset G X) X ≤ X.card := by
      rw [hα]
      omega
    have hEq := defOf_separated_add_of_nonneg hCX hA hB
    have hle := le_maxDef G (C ∪ X)
    rw [hEq] at hle
    have hle' : defOf (induceFinset G C) C + (X.card - 2) ≤ MaxDef G := by
      simp only [defOf, hα] at hle
      exact hle
    omega

/-- **`LocIndep` is inherited by a set separated from an odd cycle, with the parameter one
smaller.**  The hypothesis of Erdős #73 in the form an induction needs: the "off-cycle" part
satisfies the hypothesis with the strictly smaller parameter `k - 1`. -/
theorem locIndep_offCycle {C X : Finset V} (hC : IsOddCycle G C) (hCX : Separated G C X)
    {k : ℕ} (hk : 1 ≤ k) (hG : LocIndep k G) : LocIndep (k - 1) (induceFinset G X) := by
  exact locIndep_of_maxDef_le (maxDef_offCycle_le hC hCX hk (maxDef_le_of_locIndep hG))

/-- **`LocIndep` is inherited by the residue of a separated odd cycle, with the parameter one
smaller.**  The step `JSP90.LocIndep.of_deleteFinset` of `JSPProblem/Residue.lean` keeps the
parameter `k`; this one *decreases* it, at the cost of the separation hypothesis. -/
theorem locIndep_of_separated_oddCycle [Fintype V] {C : Finset V} (hC : IsOddCycle G C)
    (hanti : ∀ v ∈ C, ∀ w ∉ C, ¬ G.Adj v w) {k : ℕ} (hk : 1 ≤ k) (hG : LocIndep k G) :
    LocIndep (k - 1) (deleteFinset G C) := by
  have hsep : Separated G C ((Finset.univ : Finset V) \ C) :=
    ⟨Finset.disjoint_right.mpr fun a ha hC => (Finset.mem_sdiff.mp ha).2 hC,
      fun v hvC w hw => hanti v hvC w (by simpa using hw)⟩
  have h1 := maxDef_ge_one_add_maxDef_of_oddCycle hC hsep
  have hid : MaxDef (deleteFinset G C) = MaxDef (induceFinset G ((Finset.univ : Finset V) \ C)) := rfl
  rw [← hid] at h1
  have h1' : MaxDef (deleteFinset G C) + 1 ≤ MaxDef G := by
    simpa [Nat.add_comm] using h1
  exact locIndep_of_maxDef_le (le_pred_of_succ_le h1' (maxDef_le_of_locIndep hG))

end Corollaries

/-! ## Part 4 — layered odd cycles, and a new instance of the headline theorem

`G` has **layered odd cycles** (`LayeredOddCycles G L`) if `L` is a family of vertex sets such that

* every member of `L` is an odd cycle of `G`;
* every member of `L` is **separated from the rest of `G`**: no edge joins it to `V \ C`;
* distinct members of `L` are disjoint;
* **every odd cycle of `G` is a member of `L`.**

So the odd cycles of `G` are layers: they are pairwise vertex-disjoint, each one is separated from
everything else, and there are no other odd cycles.  The class contains the disjoint union of `k`
triangles (`JSP90.layeredOddCycles_kTriangles` below) and it does *not* contain graphs whose odd
cycles meet (`JSP90.oddCyclesMeet_of_not_disjoint`): it is exactly the class on which the induction
on the deficiency closes, because deleting a layer leaves a layered graph
(`JSP90.layeredOddCycles_erase`) with a strictly smaller deficiency
(`JSP90.maxDef_deleteFinset_oddCycle_le`).

`erdos73On_of_layered` is the resulting instance: **Erdős #73 with the sharp constant `k` for
graphs whose odd cycles are layers, proved by an induction on the deficiency** — the first
`MaxDef`-inductive instance of the headline theorem in this development. -/

section Layered

/-- **Every member of `L` is an odd cycle of `G`.** -/
def OddCycleLayers (G : SimpleGraph V) (L : Finset (Finset V)) : Prop :=
  ∀ (C : Finset V), C ∈ L → IsOddCycle G C

/-- **Every member of `L` is separated from the rest of `G`**: no edge joins it to `V \ C`. -/
def SeparatedLayers (G : SimpleGraph V) (L : Finset (Finset V)) : Prop :=
  ∀ (C : Finset V) (v w : V), C ∈ L → v ∈ C → w ∉ C → ¬ G.Adj v w

/-- **Distinct members of `L` are disjoint.** -/
def DisjointLayers (G : SimpleGraph V) (L : Finset (Finset V)) : Prop :=
  ∀ (C D : Finset V), C ∈ L → D ∈ L → C = D ∨ Disjoint C D

/-- **Every odd cycle of `G` is a member of `L`.** -/
def CoveredOddCycles (G : SimpleGraph V) (L : Finset (Finset V)) : Prop :=
  ∀ (D : Finset V), IsOddCycle G D → D ∈ L

/-- **The odd cycles of `G` are layers.**  See the section header. -/
def LayeredOddCycles (G : SimpleGraph V) (L : Finset (Finset V)) : Prop :=
  OddCycleLayers G L ∧ SeparatedLayers G L ∧ DisjointLayers G L ∧ CoveredOddCycles G L

/-- **An odd cycle of a residue is an odd cycle that avoids the deleted set.**  The converse
direction of `JSP90.IsOddCycle.of_deleteFinset`; the existing lemmas of `JSPProblem/Residue.lean`
only give the statement existentially, this one keeps the vertex set. -/
theorem IsOddCycle.delete_avoiding [Fintype V] {B C : Finset V} (hC : IsOddCycle G C)
    (hdis : C ∩ B = ∅) : IsOddCycle (deleteFinset G B) C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  have hnot : ∀ x : V, x ∈ C → x ∉ B := by
    intro x hx hxB
    exact (Finset.eq_empty_iff_forall_notMem.mp hdis) x (Finset.mem_inter.mpr ⟨hx, hxB⟩)
  have hmem' : ∀ j : Fin m, f j ∈ (C : Set V) := fun j => hmem (f j) |>.mpr ⟨j, rfl⟩
  refine ⟨m, f, hm, hm3, hinj, fun j => ?_, hmem⟩
  exact (deleteFinset_adj.mpr ⟨hnot _ (hmem' j), hnot _ (hmem' (cycSucc j)), hcyc j⟩)

/-- **Every vertex of an odd cycle of the residue `G - C` lies outside `C`.** -/
theorem notMem_of_isOddCycle_deleteFinset [Fintype V] {C D : Finset V}
    (hD : IsOddCycle (deleteFinset G C) D) : ∀ v ∈ D, v ∉ C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  intro x hx hxC
  obtain ⟨j, hj⟩ := (hmem x).mp hx
  exact (deleteFinset_adj.mp (hcyc j)).1 (hj ▸ hxC)

/-- **Two distinct layers do not meet.** -/
theorem layered_inter_eq_empty {G : SimpleGraph V} {L : Finset (Finset V)}
    (hL : LayeredOddCycles G L) {C D : Finset V} (hC : C ∈ L) (hD : D ∈ L) (hne : C ≠ D) :
    C ∩ D = ∅ := by
  obtain ⟨-, -, hLdisj, -⟩ := hL
  exact Finset.disjoint_iff_inter_eq_empty.mp ((hLdisj C D hC hD).resolve_left hne)

/-- **A layer is separated from the whole of `V` outside it.** -/
theorem layered_separated_compl {G : SimpleGraph V} {L : Finset (Finset V)}
    (hL : LayeredOddCycles G L) {C : Finset V} (hC : C ∈ L) :
    Separated G C ((Finset.univ : Finset V) \ C) := by
  obtain ⟨-, hLanti, -, -⟩ := hL
  exact ⟨Finset.disjoint_right.mpr fun a ha hC => (Finset.mem_sdiff.mp ha).2 hC,
    fun v hvC w hw => hLanti C v w hC hvC (Finset.mem_sdiff.mp hw).2⟩

/-- **A bipartite graph has no layers.** -/
theorem layered_eq_empty_of_isBipartite {G : SimpleGraph V} (hG : G.IsBipartite)
    {L : Finset (Finset V)} (hL : LayeredOddCycles G L) : L = ∅ := by
  ext C
  constructor
  · intro hC
    exact by simpa using (not_isOddCycle_of_isBipartite (V := _) hG ⟨C, hL.1 C hC⟩)
  · intro h
    exact by simpa using h

/-- **Deleting a layer leaves a layered graph.**  This is what closes the induction of
`erdos73On_of_layered`: the family of layers of `G - C` is `L.erase C`, its members are still odd
cycles of the residue, still separated from the rest of the residue, still pairwise disjoint, and
every odd cycle of the residue is one of them. -/
theorem layeredOddCycles_erase [Fintype V] {G : SimpleGraph V} {L : Finset (Finset V)}
    (hL : LayeredOddCycles G L) {C : Finset V} (hC : C ∈ L) :
    LayeredOddCycles (deleteFinset G C) (L.erase C) := by
  obtain ⟨hLodd, hLanti, hLdisj, hLcov⟩ := hL
  obtain ⟨c, hc⟩ := (hLodd C hC).nonempty
  have hsep : ∀ D ∈ L, D ≠ C → D ∩ C = ∅ := by
    intro D hD hDne
    exact Finset.disjoint_iff_inter_eq_empty.mp ((hLdisj D C hD hC).resolve_left hDne)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D hD
    exact IsOddCycle.delete_avoiding (hLodd D (Finset.mem_of_mem_erase hD))
      (hsep D (Finset.mem_of_mem_erase hD) (Finset.ne_of_mem_erase hD))
  · intro D v w hD hvD hwD hAdj
    exact hLanti D v w (Finset.mem_of_mem_erase hD) hvD hwD
      ((deleteFinset_adj.mp hAdj).2.2)
  · intro C' D hC' hD
    exact hLdisj C' D (Finset.mem_of_mem_erase hC') (Finset.mem_of_mem_erase hD)
  · intro D hD
    have hDne : D ≠ C := by
      obtain ⟨v, hv⟩ := (hD).nonempty
      intro hDC
      exact notMem_of_isOddCycle_deleteFinset hD v hv (hDC ▸ hv)
    exact Finset.mem_erase_of_ne_of_mem hDne (hLcov D (IsOddCycle.of_deleteFinset hD))

/-- **A graph is bipartite if and only if it has no odd cycle.**  The odd-cycle characterisation of
bipartiteness, in the form needed below; it is the pair `JSP90.not_isOddCycle_of_isBipartite` and
`JSP90.isBipartite_of_no_oddCycle` of `JSPProblem/Transversal.lean`. -/
theorem isBipartite_iff_no_oddCycle [Fintype V] :
    G.IsBipartite ↔ ¬ ∃ C : Finset V, IsOddCycle G C :=
  ⟨not_isOddCycle_of_isBipartite, fun h => isBipartite_of_no_oddCycle h⟩

/-- **AN INDUCTION ON THE DEFICIENCY, FOR GRAPHS WHOSE ODD CYCLES ARE LAYERS — A NEW INSTANCE OF THE
HEADLINE THEOREM.**

Let `G` have layered odd cycles and let `LocIndep k G`.  Then `G` is the union of a bipartite graph
and `k` vertices.  The induction is on `k`, and the induction step is Part 3: deleting a layer,
which is separated from the rest, decreases the deficiency by at least one
(`JSP90.maxDef_deleteFinset_oddCycle_le`) and leaves a layered graph
(`JSP90.layeredOddCycles_erase`); the layer itself is killed by a single vertex. -/
theorem erdos73On_of_layered (k : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      (∃ L : Finset (Finset W), LayeredOddCycles G L) → CloseToBipartite k G := by
  induction k with
  | zero =>
      intro W instW G hG _
      exact erdos73On_zero W instW G hG
  | succ k ih =>
      intro W instW G hG ⟨L, hL⟩
      obtain ⟨hLodd, hLanti, hLdisj, hLcov⟩ := hL
      by_cases hb : G.IsBipartite
      · exact isBipartite_closeToBipartite (m := k + 1) hb
      · have hnone : ¬ (¬ ∃ C : Finset W, IsOddCycle G C) := by
          have h1 : ¬ G.IsBipartite ↔ ¬ (¬ ∃ C : Finset W, IsOddCycle G C) :=
            (isBipartite_iff_no_oddCycle (G := G)).not
          exact h1.mp hb
        obtain ⟨C, hC⟩ : ∃ C : Finset W, IsOddCycle G C := not_not.mp hnone
        have hCmem : C ∈ L := hLcov C hC
        obtain ⟨c, hc⟩ := hC.nonempty
        -- the induction hypothesis, applied to the residue of the layer `C`
        have hMaxDel : MaxDef (deleteFinset G C) ≤ k :=
          maxDef_deleteFinset_oddCycle_le hC
            (by intro v hvC w hw; exact hLanti C v w hCmem hvC hw) (by omega)
            (maxDef_le_of_locIndep hG)
        obtain ⟨T, hTcard, hTbip⟩ := ih W instW (deleteFinset G C)
          (locIndep_of_maxDef_le hMaxDel)
          ⟨L.erase C, layeredOddCycles_erase ⟨hLodd, hLanti, hLdisj, hLcov⟩ hCmem⟩
        have hT : HitsOddCycles (deleteFinset G C) T := hitsOddCycles_of_isBipartite_delete hTbip
        -- `T ∪ {c}` meets every odd cycle of `G`
        have hhit : HitsOddCycles G (T ∪ {c}) := by
          intro D hD
          by_cases hDT : D ∩ T = ∅
          · by_cases hDC : D ∩ C = ∅
            · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr
                (hT D (IsOddCycle.delete_avoiding hD hDC))
              exact False.elim ((Finset.eq_empty_iff_forall_notMem.mp hDT) x
                (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩))
            · have hDeq : D = C := by
                by_cases hDCeq : D = C
                · exact hDCeq
                · have h1 : C ∩ D = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
                    ((hLdisj C D hCmem (hLcov D hD)).resolve_left (fun hh => hDCeq hh.symm))
                  exact False.elim (hDC (Finset.inter_comm C D ▸ h1))
              subst hDeq
              have hmemc : c ∈ (D : Finset W) ∩ (T ∪ {c}) := by
                refine Finset.mem_inter.mpr ⟨?_, ?_⟩
                · exact hc
                · simp only [Finset.mem_union, Finset.mem_singleton]
                  exact Or.inr trivial
              exact Finset.nonempty_iff_ne_empty.mp ⟨c, hmemc⟩
          · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hDT
            have hxmem : x ∈ (D : Finset W) ∩ (T ∪ {c}) := by
              refine Finset.mem_inter.mpr ⟨?_, ?_⟩
              · exact (Finset.mem_inter.mp hx).1
              · simp only [Finset.mem_union, Finset.mem_singleton]
                exact Or.inl (Finset.mem_inter.mp hx).2
            exact Finset.nonempty_iff_ne_empty.mp ⟨x, hxmem⟩
        refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := k + 1)).mpr ⟨T ∪ {c}, ?_, hhit⟩
        calc (T ∪ {c} : Finset W).card ≤ T.card + ({c} : Finset W).card :=
            Finset.card_union_le T {c}
          _ = T.card + 1 := by simp
          _ ≤ k + 1 := by omega

/-- **ERDŐS #73 FOR GRAPHS WHOSE ODD CYCLES ARE LAYERS, WITH THE SHARP CONSTANT `k`.**  The
statement of `erdos73On_of_layered` with the two hypotheses interchanged, to record that the class
condition and the hypothesis are independent. -/
theorem erdos73On_of_layered_swap (k : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W),
      (∃ L : Finset (Finset W), LayeredOddCycles G L) → LocIndep k G → CloseToBipartite k G :=
  fun W instW G hL hG => erdos73On_of_layered k W instW G hG hL

/-- **THE HEADLINE THEOREM ON LAYERED GRAPHS, IN THE LANGUAGE OF THE DEFICIENCY.**  The form used
in the induction of `erdos73On_of_layered`, with `MaxDef` in place of `LocIndep`. -/
theorem closeToBipartite_of_layered_of_maxDef_le {k : ℕ} {G : SimpleGraph V}
    (hL : ∃ L : Finset (Finset V), LayeredOddCycles G L) (hG : MaxDef G ≤ k) :
    CloseToBipartite k G :=
  erdos73On_of_layered k V (inferInstance) G (locIndep_of_maxDef_le hG) hL

/-- **THE `k` DISJOINT TRIANGLES ARE LAYERED**, so the class of this part is non-trivial and the
constant `k` of `erdos73On_of_layered` is attained on it. -/
theorem layeredOddCycles_kTriangles {k : ℕ} :
    LayeredOddCycles (kTriangles k) ((Finset.univ : Finset (Fin k)).image (fun i => tri i)) := by
  have hmem : ∀ (C : Finset (Fin 3 × Fin k)),
      C ∈ (Finset.univ : Finset (Fin k)).image (fun i => tri i) ↔ ∃ i : Fin k, C = tri i := by
    intro C
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, Finset.mem_univ _, rfl⟩
  have hantico : ∀ (i : Fin k) (p : Fin 3 × Fin k), p ∈ tri i → ∀ q : Fin 3 × Fin k,
      q ∉ tri i → ¬ (kTriangles k).Adj p q := by
    intro i p hp q hq h
    have h1 : p.2 = q.2 := (kTriangles_adj.mp h).1
    have h2 : p.2 = i := mem_tri.mp hp
    have h3 : q.2 ≠ i := mem_tri.not.mp hq
    exact absurd h2 (h1 ▸ h3)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨i, rfl⟩ := (hmem C).mp hC
    exact isOddCycle_tri i
  · intro C v w hC hvC hwC hw
    obtain ⟨i, rfl⟩ := (hmem C).mp hC
    exact hantico i v hvC w hwC hw
  · intro C D hC hD
    obtain ⟨i, rfl⟩ := (hmem C).mp hC
    obtain ⟨j, rfl⟩ := (hmem D).mp hD
    by_cases h : i = j
    · exact Or.inl (h ▸ rfl)
    · exact Or.inr (tri_disjoint h)
  · intro D hD
    obtain ⟨i, rfl⟩ := oddCycle_eq_tri_of_kTriangles hD
    exact (hmem (tri i)).mpr ⟨i, rfl⟩

/-- **TWO ODD CYCLES THAT MEET CANNOT BOTH BE SEPARATED FROM THE REST** — the reason the class of
this part is a genuine restriction, and the formal reason the induction on the deficiency does not
apply to a graph such as the "three triangles in a ring" or `K_5`. -/
theorem oddCyclesMeet_of_not_disjoint {G : SimpleGraph V} {C D : Finset V} (hne : C ≠ D)
    (hint : C ∩ D ≠ ∅) : ¬ (Separated G C D ∧ Separated G D C) := by
  rintro ⟨hCD, _⟩
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hint
  exact Finset.disjoint_left.mp hCD.1 (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2

end Layered

end

end JSP90
