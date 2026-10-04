import JSPProblem.ThreeB

/-!
# JSP-000090, round 161 — `JSPProblem/ThreeA.lean`: **THE SHAPE-A HALF OF `JSP90.ThreeIntersectionFiveCycleUnique`**

Attack family 84.  This file is the second of the two concrete bets of
`discovery/JSP-000090/policy.json` after round 160, and the completion of round 161's
`lean/JSPProblem/ThreeB.lean`: **the shape-A half of MISSING LEMMA 3**.

## The statement proved here (0 placeholders)

> **`JSP90.shapeA_unique` — AT `|V| ≤ 7` TWO THREE-INTERSECTION FIVE-CYCLES OF THE SHAPE A WITH THE SAME
> PAIR OF OUTSIDE VERTICES ARE EQUAL.**

Together with `JSP90.shapeB_unique` of `JSPProblem/ThreeB.lean` and
`JSP90.shapeA_shapeB_exclusive` (the two shapes never mix over a fixed outside pair), this is
`JSP90.ThreeIntersectionFiveCycleUnique` at `|V| ≤ 7`.

## The proof

Read both cycles in the *single* ring `g` of `C` supplied by `JSP90.exists_ringShapeA` for the first
one, and use only two kinds of facts:

* **the neighbour sets inside `C`** (`JSP90.adjIn_C_pairs_of_ringShapeA`): in shape A the five points
  of `C` have the neighbour sets

  ```text
  N_C(a) = {b, d}   N_C(b) = {a, c}   N_C(c) = {b, e}   N_C(d) = {e, a}   N_C(e) = {d, c}
  ```

  (every vertex of a chordless five-cycle has exactly two neighbours inside it,
  `JSP90.card_neighIn_C_eq_two`, and shape A exhibits two adjacencies at each point);
* **the candidate sets of round 160** (`JSP90.adjIn_C_subset_of_shapeA`): `AdjIn G w1 C ⊆ {c, d}`
  and `AdjIn G w2 C ⊆ {a, e}` — the neighbours of the outside vertices in `C` are confined to two
  candidates each.

Since `a₂ ~ w2`, `a₁ ~ w2`, `c₂ ~ w1`, `c₁ ~ w1` we get the four alternatives

```text
a₂ = a₁ ∨ a₂ = e₁      a₁ = a₂ ∨ a₁ = e₂      c₂ = c₁ ∨ c₂ = d₁      c₁ = c₂ ∨ c₁ = d₂
```

and the four cases are:

| case | assumptions | outcome |
| --- | --- | --- |
| I | `a₁ = a₂`, `c₁ = c₂` | `N_C(a₁) ∩ N_C(c₁) = {b₁}` forces `b₂ = b₁`, hence `D = D'` |
| II | `a₁ = a₂`, `c₁ ≠ c₂` | `c₁ = d₂`, `c₂ = d₁`, so `{c₂, b₁} = N_C(a₁) = {b₂, c₁}` forces `c₂ = b₂`, impossible |
| III | `a₁ ≠ a₂`, `c₁ = c₂` | `a₂ = e₁`, `a₁ = e₂`, so `{b₁, e₁} = N_C(c₁) = {b₂, a₁}` forces `e₁ = a₁`, impossible |
| IV | `a₁ ≠ a₂`, `c₁ ≠ c₂` | all four missed points are read off, `C` is the union of the two triples and the two missed pairs, so `b₁ = b₂`, and `{a₁, c₁} = N_C(b₁) = {a₂, c₂}` forces `a₁ = c₂`, impossible |

So the shape-A half needs no new mathematical input: it is four cases of set arithmetic on the two
neighbour sets above.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]`.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 4000000

local instance thDecidableAdjRel5 (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

local instance thDecidableEq5 : DecidableEq V := Classical.decEq V

/- `JSP90.shapeA_unique` keeps the order bound `hV` and the cardinalities `hD5`, `hD5'` even though the
shape-A case analysis does not need them (the neighbour sets of Part 1 already separate the five points
of `C`): they are part of the interface of `JSP90.shape_unique_of_shapes`, which compares the two
shapes. -/
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Part 0 — the bookkeeping -/

/-- **THE NUMBER OF POINTS OF `C` WHICH `D` MISSES, WHEN `C` HAS FIVE POINTS AND `D` THREE OF THEM.** -/
lemma card_sdiff_eq_two {C D : Finset V} (hC5 : C.card = 5) (hi : (C ∩ D).card = 3) :
    (C \ D).card = 2 := by
  have h1 := Finset.card_sdiff_add_card_inter C D
  omega

/-- **A TWO-ELEMENT MISSED PAIR HAS TWO DISTINCT POINTS.** -/
lemma ne_of_card_sdiff {C D : Finset V} {d e : V} (hs : C \ D = {d, e}) (hcard : (C \ D).card = 2) :
    d ≠ e := by
  intro hde
  have h1 : ({d, e} : Finset V) = {d} := by
    ext z
    simp only [mem_pair_eq, Finset.mem_singleton]
    constructor
    · intro hz
      rcases hz with hz | hz
      · exact hz
      · exact hz.trans hde.symm
    · intro hz
      exact Or.inl hz
  rw [hs] at hcard
  rw [h1, Finset.card_singleton] at hcard
  omega

/-- **THE TWO MISSED POINTS OF A THREE-INTERSECTION FIVE-CYCLE ARE TWO DISTINCT POINTS OF `C` WHICH
`D` DOES NOT USE.** -/
lemma sdiff_pair_facts {C D : Finset V} {d e : V} (hs : C \ D = {d, e}) (hcard : (C \ D).card = 2) :
    d ∈ C ∧ d ∉ D ∧ e ∈ C ∧ e ∉ D ∧ d ≠ e := by
  have hd : d ∈ C \ D := mem_of_mem_congr' hs (mem_pair_eq.mpr (Or.inl rfl))
  have he : e ∈ C \ D := mem_of_mem_congr' hs (mem_pair_eq.mpr (Or.inr rfl))
  exact ⟨(Finset.mem_sdiff.mp hd).1, (Finset.mem_sdiff.mp hd).2, (Finset.mem_sdiff.mp he).1,
    (Finset.mem_sdiff.mp he).2, ne_of_card_sdiff hs hcard⟩

/-! ## Part 1 — the neighbour sets of a shape-A cycle inside `C` -/

/-- **THE NEIGHBOURS INSIDE `C` OF A POINT OF A SHORTEST ODD FIVE-CYCLE ARE THE TWO GIVEN ONES.**

A shortest odd five-cycle is chordless, so every one of its vertices has exactly two neighbours
inside it (`JSP90.card_neighIn_C_eq_two`); two distinct known neighbours therefore determine the set. -/
lemma adjIn_C_eq_pair {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) {x y z : V} (hx : x ∈ C)
    (hy : y ∈ C) (hz : z ∈ C) (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z) :
    AdjIn G x C = {y, z} := by
  have hc := card_neighIn_C_eq_two hC hshort hx
  exact eq_pair_of_card_two hc (mem_adjIn_of_adj hy hxy) (mem_adjIn_of_adj hz hxz) hyz

/-- **THE NEIGHBOUR SETS INSIDE `C` OF THE FIVE POINTS OF A SHAPE-A CYCLE.**

```text
N_C(a) = {b, d}   N_C(b) = {a, c}   N_C(c) = {b, e}   N_C(d) = {e, a}   N_C(e) = {d, c}
```

This is the shape-A counterpart of round 161's `JSP90.adjIn_C_pair_of_ringShapeB`: it reads the whole
neighbour structure of both shapes off the ring. -/
lemma adjIn_C_pairs_of_ringShapeA {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    {g : Fin 5 → V} {w1 w2 a b c d e : V}
    (h : RingShapeAData G C D g w1 w2 a b c d e) :
    AdjIn G a C = {b, d} ∧ AdjIn G b C = {a, c} ∧ AdjIn G c C = {b, e} ∧
      AdjIn G d C = {e, a} ∧ AdjIn G e C = {d, c} := by
  obtain ⟨-, -, hdist, hshape, hmissed⟩ := h
  obtain ⟨hDset, hab, hbc, hcw1, hw2a, hw1w2⟩ := hshape
  obtain ⟨hsdiff, hde, had, hce⟩ := hmissed
  obtain ⟨ha, hb, hc, hw1, hw2, hw, hab', hbc', hac'⟩ := hdist
  have haD : a ∈ D := by rw [hDset]; simp
  have hbD : b ∈ D := by rw [hDset]; simp
  have hcD : c ∈ D := by rw [hDset]; simp
  have hdmem : d ∈ C \ D := mem_of_mem_congr' hsdiff (mem_pair_eq.mpr (Or.inl rfl))
  have hemem : e ∈ C \ D := mem_of_mem_congr' hsdiff (mem_pair_eq.mpr (Or.inr rfl))
  have hdD : d ∉ D := fun hx => (Finset.mem_sdiff.mp hdmem).2 hx
  have heD : e ∉ D := fun hx => (Finset.mem_sdiff.mp hemem).2 hx
  have hdC : d ∈ C := (Finset.mem_sdiff.mp hdmem).1
  have heC : e ∈ C := (Finset.mem_sdiff.mp hemem).1
  have hbd' : b ≠ d := by
    intro h
    rw [h] at hbD
    exact hdD hbD
  have hbe : b ≠ e := by
    intro h
    rw [h] at hbD
    exact heD hbD
  have hce' : c ≠ e := by
    intro h
    rw [h] at hcD
    exact heD hcD
  have heda : e ≠ a := by
    intro h
    rw [← h] at haD
    exact heD haD
  have hdc : d ≠ c := by
    intro h
    rw [← h] at hcD
    exact hdD hcD
  have hedc : e ≠ c := by
    intro h
    rw [← h] at hcD
    exact heD hcD
  exact ⟨adjIn_C_eq_pair hC hshort ha hb hdC hab had hbd',
    adjIn_C_eq_pair hC hshort hb ha hc hab.symm hbc hac',
    adjIn_C_eq_pair hC hshort hc hb heC hbc.symm hce hbe,
    adjIn_C_eq_pair hC hshort hdC heC ha hde had.symm heda,
    adjIn_C_eq_pair hC hshort heC hdC hc hde.symm hce.symm hdc⟩

/-! ## Part 2 — THE SHAPE-A HALF OF `JSP90.ThreeIntersectionFiveCycleUnique` -/

/-- **AT `|V| ≤ 7` TWO THREE-INTERSECTION FIVE-CYCLES OF THE SHAPE A WITH THE SAME PAIR OF OUTSIDE
VERTICES ARE EQUAL.**

This is the **shape-A half of `JSP90.ThreeIntersectionFiveCycleUnique`**, proved; the case analysis
is written out in the header of this file.  The hypotheses `hD5`, `hD5'`, `hi` are the "five-cycle
meeting `C` in three points" data of the two cycles (they are exactly the corresponding conjuncts
of `JSP90.ThreeIntersectionFiveCycleUnique`); note that the case analysis itself needs **no order
bound**: at `|V| > 7` the shape A is still unique over a fixed pair of outside vertices, only the
final identification of the outside pair needs `hV` (in `JSP90.eq_of_sdiff_eq_of_card_le_seven`). -/
theorem shapeA_unique {C D D' : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) (hV : Fintype.card V ≤ 7)
    (hD5 : D.card = 5) (hD5' : D'.card = 5) (hi : (C ∩ D).card = 3)
    {f : Fin 5 → V} (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y)
    {w1 w2 : V} (hA : IsShapeA G C D w1 w2) (hA' : IsShapeA G C D' w1 w2) : D = D' := by
  obtain ⟨g, hg, hcycg, hmemg, a₁, b₁, c₁, d₁, e₁, hdata1⟩ :=
    exists_ringShapeA hC hshort hC5 f hf hcyc hmem hA
  obtain ⟨g', hg', hcycg', hmemg', a₂, b₂, c₂, d₂, e₂, hdata2⟩ :=
    exists_ringShapeA hC hshort hC5 f hf hcyc hmem hA'
  have hd1 := hdata1
  have hd2 := hdata2
  obtain ⟨hDset1, h1ab, h1bc, h1cw1, h1w2a, h1w1w2⟩ := hd1.shape
  obtain ⟨hsdiff1, h1de, h1ad, h1ce⟩ := hd1.missed
  obtain ⟨h1aC, h1bC, h1cC, hw1, hw2, hw, h1abne, h1bcne, h1acne⟩ := hd1.distinct
  obtain ⟨hDset2, h2ab, h2bc, h2cw1, h2w2a, h2w1w2⟩ := hd2.shape
  obtain ⟨hsdiff2, h2de, h2ad, h2ce⟩ := hd2.missed
  obtain ⟨h2aC, h2bC, h2cC, hw1', hw2', hw', h2abne, h2bcne, h2acne⟩ := hd2.distinct
  -- the intersections with `C`, the missed pairs and their cardinalities
  have hinter1 : C ∩ D = {a₁, b₁, c₁} :=
    inter_D_eq_triple hDset1 h1aC h1bC h1cC hw1 hw2 hw h1abne h1bcne h1acne
  have hinter2 : C ∩ D' = {a₂, b₂, c₂} :=
    inter_D_eq_triple hDset2 h2aC h2bC h2cC hw1' hw2' hw' h2abne h2bcne h2acne
  have hi2 : (C ∩ D').card = 3 := by rw [hinter2]; exact card_three h2abne h2acne h2bcne
  have hcard1 : (C \ D).card = 2 := card_sdiff_eq_two hC5 hi
  have hcard2 : (C \ D').card = 2 := card_sdiff_eq_two hC5 hi2
  obtain ⟨h1dC, h1dnotD, h1eC, h1enotD, h1dne⟩ := sdiff_pair_facts hsdiff1 hcard1
  obtain ⟨h2dC, h2dnotD, h2eC, h2enotD, h2dne⟩ := sdiff_pair_facts hsdiff2 hcard2
  -- the points used by `D` and by `D'`
  have ha1D : a₁ ∈ D := by rw [hDset1]; simp
  have hb1D : b₁ ∈ D := by rw [hDset1]; simp
  have hc1D : c₁ ∈ D := by rw [hDset1]; simp
  have hc2D : c₂ ∈ D' := by rw [hDset2]; simp
  -- the neighbour sets of the two cycles inside `C`
  obtain ⟨hNa1, hNb1, hNc1, hNd1, hNe1⟩ := adjIn_C_pairs_of_ringShapeA hC hshort hd1
  obtain ⟨hNa2, hNb2, hNc2, hNd2, hNe2⟩ := adjIn_C_pairs_of_ringShapeA hC hshort hd2
  -- the two cross-distinctness facts which the cases use
  have ha2c1 : a₂ ≠ c₁ := by
    intro hac
    have hmem : a₂ ∈ AdjIn G w2 C := mem_adjIn_of_adj (x := w2) (z := a₂) h2aC h2w2a
    have hsub : a₂ ∈ ({a₁, e₁} : Finset V) := (adjIn_C_subset_of_shapeA htf hd1).2 hmem
    rcases mem_pair_eq.mp hsub with h | h
    · exact h1acne (h.symm.trans hac)
    · exact h1enotD ((h.symm.trans hac) ▸ hc1D)
  have ha1c2 : a₁ ≠ c₂ := by
    intro hac
    have hmem : a₁ ∈ AdjIn G w2 C := mem_adjIn_of_adj (x := w2) (z := a₁) h1aC h1w2a
    have hsub : a₁ ∈ ({a₂, e₂} : Finset V) := (adjIn_C_subset_of_shapeA htf hd2).2 hmem
    rcases mem_pair_eq.mp hsub with h | h
    · exact h2acne (h.symm.trans hac)
    · exact h2enotD ((h.symm.trans hac) ▸ hc2D)
  by_cases haa : a₁ = a₂
  · by_cases hcc : c₁ = c₂
    · -- **CASE I**: the two cycles use the same three points of `C`
      have hb2a : b₂ ∈ AdjIn G a₁ C := by
        rw [haa]
        exact mem_adjIn_of_adj (x := a₂) (z := b₂) h2bC h2ab
      have hb2c : b₂ ∈ AdjIn G c₁ C := by
        rw [hcc]
        exact mem_adjIn_of_adj (x := c₂) (z := b₂) h2bC h2bc.symm
      have h1 : b₂ ∈ ({b₁, d₁} : Finset V) := hNa1 ▸ hb2a
      have h2 : b₂ ∈ ({b₁, e₁} : Finset V) := hNc1 ▸ hb2c
      have hb2mem : b₂ ∈ ({b₁, d₁} : Finset V) ∩ ({b₁, e₁} : Finset V) :=
        Finset.mem_inter.mpr ⟨h1, h2⟩
      rw [inter_pair_pair_of_ne h1dne] at hb2mem
      have hbb : b₂ = b₁ := Finset.mem_singleton.mp hb2mem
      rw [hDset1, hDset2, haa, hbb, hcc]
    · -- **CASE II**: `a₁ = a₂` and `c₁ ≠ c₂`: then `c₁ = d₂`, `c₂ = d₁`, and `{c₂, b₁} = {b₂, c₁}`
      -- forces `c₂ = b₂`
      have hmem : c₁ ∈ AdjIn G w1 C := mem_adjIn_of_adj (x := w1) (z := c₁) h1cC h1cw1.symm
      have hsub : c₁ ∈ ({c₂, d₂} : Finset V) := (adjIn_C_subset_of_shapeA htf hd2).1 hmem
      have hc1d2 : c₁ = d₂ := by
        rcases mem_pair_eq.mp hsub with h | h
        · exact absurd h hcc
        · exact h
      have hmem2 : c₂ ∈ AdjIn G w1 C := mem_adjIn_of_adj (x := w1) (z := c₂) h2cC h2cw1.symm
      have hsub2 : c₂ ∈ ({c₁, d₁} : Finset V) := (adjIn_C_subset_of_shapeA htf hd1).1 hmem2
      have hc2d1 : c₂ = d₁ := by
        rcases mem_pair_eq.mp hsub2 with h | h
        · exact absurd h (Ne.symm hcc)
        · exact h
      have hset : ({b₁, d₁} : Finset V) = {b₂, d₂} := by
        have hthis : AdjIn G a₁ C = AdjIn G a₂ C := by rw [haa]
        rw [← hNa1, hthis, hNa2]
      rw [← hc2d1, ← hc1d2] at hset
      have hc2mem : c₂ ∈ ({b₂, c₁} : Finset V) := hset ▸ (mem_pair_eq.mpr (Or.inr rfl))
      rcases mem_pair_eq.mp hc2mem with h | h
      · exact (h2bcne h.symm).elim
      · exact (Ne.symm hcc h).elim
  · by_cases hcc : c₁ = c₂
    · -- **CASE III**: `a₁ ≠ a₂` and `c₁ = c₂`: then `a₂ = e₁`, `a₁ = e₂`, and `{b₁, e₁} = {b₂, a₁}`
      -- forces `b₁ = a₁`
      have hmem : a₂ ∈ AdjIn G w2 C := mem_adjIn_of_adj (x := w2) (z := a₂) h2aC h2w2a
      have hsub : a₂ ∈ ({a₁, e₁} : Finset V) := (adjIn_C_subset_of_shapeA htf hd1).2 hmem
      have ha2e1 : a₂ = e₁ := by
        rcases mem_pair_eq.mp hsub with h | h
        · exact absurd h (Ne.symm haa)
        · exact h
      have hmem2 : a₁ ∈ AdjIn G w2 C := mem_adjIn_of_adj (x := w2) (z := a₁) h1aC h1w2a
      have hsub2 : a₁ ∈ ({a₂, e₂} : Finset V) := (adjIn_C_subset_of_shapeA htf hd2).2 hmem2
      have ha1e2 : a₁ = e₂ := by
        rcases mem_pair_eq.mp hsub2 with h | h
        · exact absurd h haa
        · exact h
      have he1a1 : e₁ ≠ a₁ := fun hh => haa ((ha2e1.trans hh).symm)
      have hset : ({b₁, e₁} : Finset V) = {b₂, e₂} := by
        have hthis : AdjIn G c₁ C = AdjIn G c₂ C := by rw [hcc]
        rw [← hNc1, hthis, hNc2]
      rw [← ha1e2] at hset
      have hb1mem : b₁ ∈ ({b₂, a₁} : Finset V) := hset ▸ (mem_pair_eq.mpr (Or.inl rfl))
      have he1mem : e₁ ∈ ({b₂, a₁} : Finset V) := hset ▸ (mem_pair_eq.mpr (Or.inr rfl))
      rcases mem_pair_eq.mp hb1mem with h | h
      · have hb1ne : b₁ ≠ e₁ := by intro hh; rw [hh] at hb1D; exact h1enotD hb1D
        rcases mem_pair_eq.mp he1mem with he | he
        · exact (hb1ne (h.trans he.symm)).elim
        · exact (he1a1 he).elim
      · exact (h1abne h.symm).elim
    · -- **CASE IV**: both `a` and `c` differ: then `a₂ = e₁`, `a₁ = e₂`, `c₁ = d₂`, `c₂ = d₁`,
      -- the five points of `C` are `e₁, b₂, c₂, c₁, a₁`, so `b₁ = b₂`, and `{a₁, c₁} = {a₂, c₂}`
      -- forces `a₁ = c₂`
      have hmem : a₂ ∈ AdjIn G w2 C := mem_adjIn_of_adj (x := w2) (z := a₂) h2aC h2w2a
      have hsub : a₂ ∈ ({a₁, e₁} : Finset V) := (adjIn_C_subset_of_shapeA htf hd1).2 hmem
      have ha2e1 : a₂ = e₁ := by
        rcases mem_pair_eq.mp hsub with h | h
        · exact absurd h (Ne.symm haa)
        · exact h
      have hmem2 : a₁ ∈ AdjIn G w2 C := mem_adjIn_of_adj (x := w2) (z := a₁) h1aC h1w2a
      have hsub2 : a₁ ∈ ({a₂, e₂} : Finset V) := (adjIn_C_subset_of_shapeA htf hd2).2 hmem2
      have ha1e2 : a₁ = e₂ := by
        rcases mem_pair_eq.mp hsub2 with h | h
        · exact absurd h haa
        · exact h
      have hmem3 : c₂ ∈ AdjIn G w1 C := mem_adjIn_of_adj (x := w1) (z := c₂) h2cC h2cw1.symm
      have hsub3 : c₂ ∈ ({c₁, d₁} : Finset V) := (adjIn_C_subset_of_shapeA htf hd1).1 hmem3
      have hc2d1 : c₂ = d₁ := by
        rcases mem_pair_eq.mp hsub3 with h | h
        · exact absurd h (Ne.symm hcc)
        · exact h
      have hmem4 : c₁ ∈ AdjIn G w1 C := mem_adjIn_of_adj (x := w1) (z := c₁) h1cC h1cw1.symm
      have hsub4 : c₁ ∈ ({c₂, d₂} : Finset V) := (adjIn_C_subset_of_shapeA htf hd2).1 hmem4
      have hc1d2 : c₁ = d₂ := by
        rcases mem_pair_eq.mp hsub4 with h | h
        · exact absurd h hcc
        · exact h
      have hc2notD : c₂ ∉ D := by rw [hc2d1]; exact h1dnotD
      -- `C` is the union of the triple of `D` and the missed pair, on both sides
      have hCeq : C = ({a₂, b₂, c₂} : Finset V) ∪ ({d₂, e₂} : Finset V) := by
        rw [← hinter2, ← hsdiff2, inter_union_sdiff' C D']
      rw [ha2e1, ← ha1e2, ← hc1d2] at hCeq
      have hbb : b₁ = b₂ := by
        have hb1mem : b₁ ∈ ({e₁, b₂, c₂} : Finset V) ∪ ({c₁, a₁} : Finset V) := by
          rw [hCeq.symm]
          exact h1bC
        have hb1e1 : b₁ ≠ e₁ := by
          intro h
          rw [h] at hb1D
          exact h1enotD hb1D
        have hb1c2 : b₁ ≠ c₂ := by
          intro h
          rw [h] at hb1D
          exact hc2notD hb1D
        rcases mem_union.mp hb1mem with h | h
        · rcases Finset.mem_insert.mp h with h | h
          · exact (hb1e1 h).elim
          · rcases Finset.mem_insert.mp h with h | h
            · exact h
            · rcases Finset.mem_singleton.mp h with h
              exact (hb1c2 h).elim
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with h | h
          · exact (h1bcne h).elim
          · exact (h1abne h.symm).elim
      have hset2 : ({a₁, c₁} : Finset V) = {a₂, c₂} := by
        have hthis : AdjIn G b₁ C = AdjIn G b₂ C := by rw [hbb]
        rw [← hNb1, hthis, hNb2]
      rcases mem_pair_eq.mp (hset2 ▸ (mem_pair_eq.mpr (Or.inl rfl))) with h | h
      · exact (haa h).elim
      · exact (ha1c2 h).elim

/-! ## Part 3 — the two halves together -/

/-- **A THREE-INTERSECTION FIVE-CYCLE CANNOT BE OF THE SHAPE A OVER AN OUTSIDE PAIR AND OF THE SHAPE B
OVER THE SAME PAIR** — the two-`D` version of `JSP90.shapeA_shapeB_exclusive`, which is what the
comparison of two different cycles needs (the two witnesses `D`, `E` are arbitrary). -/
theorem not_shapeA_of_shapeB {C D E : Finset V} (htf : ∀ S : Finset V, ¬ G.IsNClique 3 S)
    {w1 w2 : V} (hB : IsShapeB G C E w1 w2) (hA : IsShapeA G C D w1 w2) : False := by
  have hne : AdjIn G w1 C ∩ AdjIn G w2 C = ∅ := disjoint_adjIn_C_of_shapeA htf hA
  exact absurd hne (inter_adjIn_C_ne_empty_of_shapeB hB)


/-- **TWO THREE-INTERSECTION FIVE-CYCLES OF THE SAME SHAPE OVER THE SAME ORDERED PAIR OF OUTSIDE
VERTICES ARE EQUAL, AT `|V| ≤ 7`.**

This is `JSP90.shapeA_unique` and `JSP90.shapeB_unique` joined by
`JSP90.shapeA_shapeB_exclusive`, and it is the whole of `JSP90.ThreeIntersectionFiveCycleUnique` once
the outside pair of a three-intersection five-cycle is read in a fixed order (see the header: at
`|V| ≤ 7` the outside pair of two three-intersection five-cycles is the same two-element set
`univ \ C`, `JSP90.diffC_eq_univ_sdiff`, so only the order of the two points has to be matched). -/
theorem shape_unique_of_shapes {C D D' : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) (hV : Fintype.card V ≤ 7)
    (hD5 : D.card = 5) (hD5' : D'.card = 5) (hi : (C ∩ D).card = 3)
    {f : Fin 5 → V} (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) {w1 w2 : V}
    (h1 : IsShapeA G C D w1 w2 ∨ IsShapeB G C D w1 w2)
    (h2 : IsShapeA G C D' w1 w2 ∨ IsShapeB G C D' w1 w2) : D = D' := by
  rcases h1 with hA | hB <;> rcases h2 with hA' | hB'
  · exact shapeA_unique hC hshort hC5 htf hV hD5 hD5' hi hf hcyc hmem hA hA'
  · exact (not_shapeA_of_shapeB htf hB' hA).elim
  · exact (not_shapeA_of_shapeB htf hB hA').elim
  · exact shapeB_unique hC hshort hC5 htf hV hf hcyc hmem hB hB'

end
end JSP90
