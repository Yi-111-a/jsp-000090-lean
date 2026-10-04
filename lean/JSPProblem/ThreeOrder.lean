import JSPProblem.ThreeA
import JSPProblem.TriPair

/-!
# JSP-000090, round 162 — `JSPProblem/ThreeOrder.lean`: **MISSING LEMMA 3, CLOSED** —
# `JSP90.ThreeIntersectionFiveCycleUnique`, and the five-cycle case of the sharp seven-vertex
# instance

Attack family 85.  This file executes the concrete next bet of
`discovery/JSP-000090/policy.json` verbatim — *MISSING LEMMA 3, order bookkeeping* — and with it the
five-cycle case of `JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven`, which
`discovery/JSP-000090/policy.json` has named as the only remaining input of that case since round
155.

## What is proved (0 placeholders)

* **`JSP90.isShapeA_swap`, `JSP90.isShapeB_swap` — THE TWO SHAPES ARE SYMMETRIC IN THE OUTSIDE PAIR.**
  A shape A read over the reversed ordered pair is the shape A of the reversed path `c - b - a`; a
  shape B read over the reversed ordered pair is the shape B of the same three points with `b` and
  `c` exchanged (`w1 - a - w2 - b - c - w1`, read from `w2`, is `w2 - a - w1 - c - b - w2`).  This
  is the *only* input the bookkeeping needs, and it is the reason the order of the outside pair
  never carries information.
* **`JSP90.sdiff_D_eq_pair_of_isShapeA`, `JSP90.sdiff_D_eq_pair_of_isShapeB` — THE OUTSIDE PART OF A
  THREE-INTERSECTION FIVE-CYCLE IS EXACTLY THE OUTSIDE PAIR OF ITS SHAPE.**
* **`JSP90.three_intersection_fiveCycle_unique` — MISSING LEMMA 3, PROVED.**  At `|V| ≤ 7`, if `D`
  and `D'` are five-cycles of a triangle-free `G` meeting a shortest odd five-cycle `C` in exactly
  three points, then `D = D'`.  The argument is exactly the one `policy.json` records: (a) the two
  outside sets coincide (`JSP90.diffC_eq_univ_sdiff`), (b) each cycle has one of the two shapes with
  an *ordered* pair (`JSP90.exists_shape`), (c) the pairs are the same two-element set of two
  *distinct* points, so the two orders are either the same or opposite, (d) if they are the same,
  `JSP90.shape_unique_of_shapes` applies at once, and if they are opposite exactly one of the two
  shapes is read over a reversed pair, so `JSP90.isShapeA_swap` / `JSP90.isShapeB_swap` restore the
  hypotheses of `JSP90.shape_unique_of_shapes` and it applies again.
* **`JSP90.three_intersection_fiveCycle_unique'`, `JSP90.three_intersection_fiveCycle_unique''` — THE
  SAME STATEMENT WITHOUT THE RING DATA**, the second being the `huniq` of
  `JSP90.closeToBipartite_one_of_unique`.
* **`JSP90.hitsOddCycles_singleton_of_shortest_five`, `JSP90.closeToBipartite_one_of_shortest_five` —
  THE FIVE-CYCLE CASE, CLOSED: A NEW INSTANCE OF THE HEADLINE THEOREM WITH THE OPTIMAL CONSTANT `1`.**

  ```lean
  IsOddCycle G C → C shortest odd → C.card = 5 → |V| ≤ 7 → CloseToBipartite 1 G
  ```

  **with no hypothesis beyond the shortestness and the five points** — in particular **no
  `LocIndep` hypothesis at all**, and no triangle-freeness hypothesis either
  (`JSP90.htf_of_shortest_five'`: a shortest odd cycle of five vertices forces `G` triangle-free).
* **`JSP90.closeToBipartite_one_of_locIndep_one_card_le_seven_of_triangleFree` — THE TRIANGLE-FREE
  SEVEN-VERTEX INSTANCE WITH THE OPTIMAL CONSTANT `1`, AS A NEW INSTANCE OF THE HEADLINE THEOREM.**

  ```lean
  LocIndep 1 G → |V| ≤ 7 → (G has no 3-clique) → CloseToBipartite 1 G
  ```

  This **drops the extra "no five-cycle" hypothesis** of
  `JSP90.closeToBipartite_one_of_locIndep_one_card_le_seven_of_triangleFree_no5`
  (`lean/JSPProblem/TriPair.lean`), i.e. it is strictly stronger: with the five-cycle case settled,
  a triangle-free `LocIndep 1` graph on at most seven vertices is **one**-delete bipartite.  The
  class form `JSP90.LocIndepOneTriangleFree` and `JSP90.erdos73On_one_triangleFree_seven` carry the
  same statement in the `Erdős73On` shape, and
  `JSP90.hitsOddCycles_singleton_of_locIndep_one_card_le_seven_of_triangleFree` is the transversal
  form (a **common vertex** of all odd cycles).

## What is still missing

`MISSING LEMMA 1`, the **triangle case** of the sharp seven-vertex instance (the `|X| = 4`
sub-case): at `LocIndep 1`, `|V| ≤ 7`, `G.IsNClique 3 T`, `X = V \ T`, NOT all three of
`(deleteFinset G (T \ {t})).IsBipartite` can fail.  With `JSP90.closeToBipartite_two_of_…` split into
the cases `C.card = 3` (open), `C.card = 5` (this file) and `C.card = Fintype.card V`
(`lean/JSPProblem/Seven.lean`), that single case is now the whole of the triangle-side remainder of
JSP-000090's seven-vertex axis.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]`.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 4000000

local instance thDecidableAdjRel6 (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

local instance thDecidableEq6 : DecidableEq V := Classical.decEq V

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Part 0 — the two shapes are symmetric in the outside pair, and the outside part is the pair -/

/-- **THE OUTSIDE PART OF A SHAPE-A CYCLE IS THE OUTSIDE PAIR.** -/
lemma sdiff_D_eq_pair_of_isShapeA {C D : Finset V} {w1 w2 : V} (h : IsShapeA G C D w1 w2) :
    D \ C = {w1, w2} := by
  obtain ⟨a, b, c, ha, hb, hc, -, -, -, hw1, hw2, hw, hDset, -, -, -, -, -⟩ := h
  rw [hDset]
  ext z
  constructor
  · intro hz
    obtain ⟨hzD, hzC⟩ := Finset.mem_sdiff.mp hz
    rcases mem_five hzD with hza | hzb | hzc | hzw1 | hzw2
    · exact absurd (hza ▸ ha) hzC
    · exact absurd (hzb ▸ hb) hzC
    · exact absurd (hzc ▸ hc) hzC
    · exact Finset.mem_insert.mpr (Or.inl hzw1)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hzw2))
  · intro hz
    rcases Finset.mem_insert.mp hz with h | h
    · exact Finset.mem_sdiff.mpr ⟨mem_five_d h, h ▸ hw1⟩
    · exact Finset.mem_sdiff.mpr ⟨mem_five_e (Finset.mem_singleton.mp h), Finset.mem_singleton.mp h ▸ hw2⟩

/-- **THE OUTSIDE PART OF A SHAPE-B CYCLE IS THE OUTSIDE PAIR.** -/
lemma sdiff_D_eq_pair_of_isShapeB {C D : Finset V} {w1 w2 : V} (h : IsShapeB G C D w1 w2) :
    D \ C = {w1, w2} := by
  obtain ⟨a, b, c, ha, hb, hc, -, -, -, hw1, hw2, hw, hDset, -, -, -, -, -⟩ := h
  rw [hDset]
  ext z
  constructor
  · intro hz
    obtain ⟨hzD, hzC⟩ := Finset.mem_sdiff.mp hz
    rcases mem_five hzD with hza | hzb | hzc | hzw1 | hzw2
    · exact absurd (hza ▸ ha) hzC
    · exact absurd (hzb ▸ hb) hzC
    · exact absurd (hzc ▸ hc) hzC
    · exact Finset.mem_insert.mpr (Or.inl hzw1)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hzw2))
  · intro hz
    rcases Finset.mem_insert.mp hz with h | h
    · exact Finset.mem_sdiff.mpr ⟨mem_five_d h, h ▸ hw1⟩
    · exact Finset.mem_sdiff.mpr ⟨mem_five_e (Finset.mem_singleton.mp h), Finset.mem_singleton.mp h ▸ hw2⟩

/-- **A SHAPE A READ OVER THE REVERSED OUTSIDE PAIR IS A SHAPE A.**

`IsShapeA G C D w2 w1` supplies `D = {a, b, c, w2, w1}` with `a - b - c` a path of `C`,
`c ~ w2`, `a ~ w1` and `w1 ~ w2`; the triple `c, b, a` is the same shape A over `(w1, w2)` with the
path reversed. -/
theorem isShapeA_swap {C D : Finset V} {w1 w2 : V} (h : IsShapeA G C D w2 w1) :
    IsShapeA G C D w1 w2 := by
  obtain ⟨a, b, c, ha, hb, hc, hab', hbc', hac', hw1, hw2, hw, hDset, hab, hbc, hcw1, hw2a,
    hw1w2⟩ := h
  refine ⟨c, b, a, hc, hb, ha, hbc'.symm, hab'.symm, hac'.symm, hw2, hw1, hw.symm, ?_, hbc.symm,
    hab.symm, hw2a.symm, hcw1.symm, hw1w2.symm⟩
  have hset : ({a, b, c, w2, w1} : Finset V) = ({c, b, a, w1, w2} : Finset V) := by
    ext z
    constructor
    · intro hz
      rcases mem_five hz with h | h | h | h | h
      · exact mem_five_c h
      · exact mem_five_b h
      · exact mem_five_a h
      · exact mem_five_e h
      · exact mem_five_d h
    · intro hz
      rcases mem_five hz with h | h | h | h | h
      · exact mem_five_c h
      · exact mem_five_b h
      · exact mem_five_a h
      · exact mem_five_e h
      · exact mem_five_d h
  exact hset ▸ hDset

/-- **A SHAPE B READ OVER THE REVERSED OUTSIDE PAIR IS A SHAPE B.**

`IsShapeB G C D w2 w1` says `a` sees both outside points, `c ~ w2` and `b ~ w1`; over `(w1, w2)` the
same three points read with `b` and `c` exchanged, since the edge of `D` inside `C` is
unoriented. -/
theorem isShapeB_swap {C D : Finset V} {w1 w2 : V} (h : IsShapeB G C D w2 w1) :
    IsShapeB G C D w1 w2 := by
  obtain ⟨a, b, c, ha, hb, hc, hab', hbc', hac', hw1, hw2, hw, hDset, habc, ha_w2, ha_w1, hb_w1,
    hc_w2⟩ := h
  refine ⟨a, c, b, ha, hc, hb, hac', hbc'.symm, hab', hw2, hw1, hw.symm, ?_, habc.symm,
    ha_w1, ha_w2, hc_w2, hb_w1⟩
  have hset : ({a, b, c, w2, w1} : Finset V) = ({a, c, b, w1, w2} : Finset V) := by
    ext z
    constructor
    · intro hz
      rcases mem_five hz with h | h | h | h | h
      · exact mem_five_a h
      · exact mem_five_c h
      · exact mem_five_b h
      · exact mem_five_e h
      · exact mem_five_d h
    · intro hz
      rcases mem_five hz with h | h | h | h | h
      · exact mem_five_a h
      · exact mem_five_c h
      · exact mem_five_b h
      · exact mem_five_e h
      · exact mem_five_d h
  exact hset ▸ hDset
/-! ## Part 1 — MISSING LEMMA 3: at `|V| ≤ 7` there is at most one three-intersection five-cycle -/

/-- **EVERY THREE-INTERSECTION FIVE-CYCLE HAS A SHAPE WITH AN ORDERED PAIR OF OUTSIDE POINTS** — the
form of `JSP90.exists_shape` which names the two points in one existential, so that a single proof
handles both shapes. -/
theorem exists_ordered_shape {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (hD : IsOddCycle G D) (hD5 : D.card = 5)
    (hi : (D ∩ C).card = 3) :
    ∃ w1 w2 : V, w1 ≠ w2 ∧ (IsShapeA G C D w1 w2 ∨ IsShapeB G C D w1 w2) := by
  rcases exists_shape hC hshort hC5 f hf hcyc hmem hD hD5 hi with
    ⟨w1, w2, hw, hA⟩ | ⟨w1, w2, hw, hB⟩
  · exact ⟨w1, w2, hw, Or.inl hA⟩
  · exact ⟨w1, w2, hw, Or.inr hB⟩

/-- **MISSING LEMMA 3, PROVED: AT `|V| ≤ 7` AT MOST ONE FIVE-CYCLE OF A TRIANGLE-FREE GRAPH MEETS A
SHORTEST ODD FIVE-CYCLE IN EXACTLY THREE POINTS.**

This is `JSP90.ThreeIntersectionFiveCycleUnique` of `lean/JSPProblem/FiveCount.lean`, in the form in
which its inputs are available: the ring `f` of `C` and the order bound.  The proof is the
bookkeeping recorded in `discovery/JSP-000090/policy.json`:

* the two outside pairs are the same two-element set, because at `|V| ≤ 7` the outside part of a
  three-intersection five-cycle is all of `V \ C` (`JSP90.diffC_eq_univ_sdiff`) and, by
  `JSP90.sdiff_D_eq_pair_of_isShapeA` / `JSP90.sdiff_D_eq_pair_of_isShapeB`, it is exactly the
  outside pair of the shape;
* `JSP90.exists_shape` gives an *ordered* pair for each of the two cycles, and the pair of `D` is a
  pair of *distinct* points, so the two orders are either the same or opposite;
* if they are the same, `JSP90.shape_unique_of_shapes` applies;
* if they are opposite, exactly one of the two shapes is read over a reversed pair, and
  `JSP90.isShapeA_swap` / `JSP90.isShapeB_swap` turn it back into the same statement over the same
  ordered pair, so `JSP90.shape_unique_of_shapes` applies again. -/
theorem three_intersection_fiveCycle_unique {C D D' : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) (hV : Fintype.card V ≤ 7)
    (hD : IsOddCycle G D) (hD5 : D.card = 5) (hi : (D ∩ C).card = 3)
    (hD' : IsOddCycle G D') (hD5' : D'.card = 5) (hi' : (D' ∩ C).card = 3)
    {f : Fin 5 → V} (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) : D = D' := by
  obtain ⟨w1, w2, hw12, h1⟩ := exists_ordered_shape hC hshort hC5 f hf hcyc hmem hD hD5 hi
  obtain ⟨u1, u2, hu12, h2⟩ := exists_ordered_shape hC hshort hC5 f hf hcyc hmem hD' hD5' hi'
  -- the outside parts coincide, and each is the outside pair of its shape
  have hdiff : D \ C = D' \ C :=
    (diffC_eq_univ_sdiff hC5 hD5 hi hV).trans (diffC_eq_univ_sdiff hC5 hD5' hi' hV).symm
  have hpair : D \ C = ({w1, w2} : Finset V) := by
    rcases h1 with hA | hB
    · exact sdiff_D_eq_pair_of_isShapeA hA
    · exact sdiff_D_eq_pair_of_isShapeB hB
  have hpair' : D' \ C = ({u1, u2} : Finset V) := by
    rcases h2 with hA' | hB'
    · exact sdiff_D_eq_pair_of_isShapeA hA'
    · exact sdiff_D_eq_pair_of_isShapeB hB'
  -- so each outside point of `D` is one of the two outside points of `D'`
  have hmem1 : w1 ∈ (D' \ C) := by rw [← hdiff, hpair]; simp
  have hmem2 : w2 ∈ (D' \ C) := by rw [← hdiff, hpair]; simp
  have hmem1'' : w1 ∈ ({u1, u2} : Finset V) := by rw [← hpair']; exact hmem1
  have hmem2'' : w2 ∈ ({u1, u2} : Finset V) := by rw [← hpair']; exact hmem2
  have hm1 : w1 = u1 ∨ w1 = u2 := by
    rcases Finset.mem_insert.mp hmem1'' with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  have hm2 : w2 = u1 ∨ w2 = u2 := by
    rcases Finset.mem_insert.mp hmem2'' with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  -- the two orders are either the same or opposite
  have hinterC : (C ∩ D).card = 3 := by rw [Finset.inter_comm]; exact hi
  rcases hm1 with hA1 | hA1
  · rcases hm2 with hB | hB
    · exact absurd (hB.trans hA1.symm) (fun h => hw12 h.symm)
    · exact shape_unique_of_shapes hC hshort hC5 htf hV hD5 hD5' hinterC hf hcyc hmem h1
        (hA1.symm ▸ hB.symm ▸ h2)
  · rcases hm2 with hB | hB
    · have h2r : IsShapeA G C D' w1 w2 ∨ IsShapeB G C D' w1 w2 := by
        rcases h2 with hA' | hB'
        · exact Or.inl (hB.symm ▸ hA1.symm ▸ isShapeA_swap hA')
        · exact Or.inr (hB.symm ▸ hA1.symm ▸ isShapeB_swap hB')
      exact shape_unique_of_shapes hC hshort hC5 htf hV hD5 hD5' hinterC hf hcyc hmem h1 h2r
    · exact absurd (hB.trans hA1.symm) (fun h => hw12 h.symm)

/-- **THE SAME STATEMENT WITH NO RING DATA**: the ring `f` of `C` is extracted from `hC` together with
`JSP90.card_eq_cyclicOrder`. -/
theorem three_intersection_fiveCycle_unique' {C D D' : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) (hV : Fintype.card V ≤ 7)
    (hD : IsOddCycle G D) (hD5 : D.card = 5) (hi : (D ∩ C).card = 3)
    (hD' : IsOddCycle G D') (hD5' : D'.card = 5) (hi' : (D' ∩ C).card = 3) : D = D' := by
  have hex : ∃ (f : Fin 5 → V), Function.Injective f ∧
      (∀ j : Fin 5, G.Adj (f j) (f (cycSucc j))) ∧ (∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) := by
    obtain ⟨m, f, -, -, hf, hcyc, hmem⟩ := hC
    have hm5 : m = 5 := by
      have h := card_eq_cyclicOrder f hf hmem
      omega
    subst hm5
    exact ⟨f, hf, hcyc, hmem⟩
  obtain ⟨f, hf, hcyc, hmem⟩ := hex
  exact three_intersection_fiveCycle_unique hC hshort hC5 htf hV hD hD5 hi hD' hD5' hi' hf hcyc hmem

/-- **THE `huniq` OF `JSP90.closeToBipartite_one_of_unique`: at `|V| ≤ 7` the five-cycles of a
triangle-free `G` meeting a shortest odd five-cycle in three points form at most one element.** -/
theorem three_intersection_fiveCycle_unique'' {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) (hV : Fintype.card V ≤ 7) :
    ∀ D D' : Finset V, IsOddCycle G D → IsOddCycle G D' → D.card = 5 → D'.card = 5 →
      (D ∩ C).card = 3 → (D' ∩ C).card = 3 → D = D' := by
  intro D D' hD hD' hD5 hD5' hi hi'
  exact three_intersection_fiveCycle_unique' hC hshort hC5 htf hV hD hD5 hi hD' hD5' hi'

/-! ## Part 2 — the five-cycle case of the sharp seven-vertex instance -/

/-- **A SHORTEST ODD CYCLE OF FIVE VERTICES FORCES `G` TRIANGLE-FREE.** -/
theorem htf_of_shortest_five' {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5) :
    ∀ S : Finset V, ¬ G.IsNClique 3 S := by
  intro S hS
  have h1 := hshort S (isOddCycle_of_isNClique_three hS)
  have h2 : S.card = 3 := (G.isNClique_iff.mp hS).2
  omega

/-- **THE ODD CYCLES OF `G` HAVE A COMMON VERTEX WHEN A SHORTEST ODD FIVE-CYCLE EXISTS AND
`|V| ≤ 7`.**

This is `JSP90.hitsOddCycles_singleton_of_unique` of `lean/JSPProblem/FiveCount.lean`, with `huniq`
discharged by `JSP90.three_intersection_fiveCycle_unique''`. -/
theorem hitsOddCycles_singleton_of_shortest_five {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (hV : Fintype.card V ≤ 7) :
    ∃ c : V, HitsOddCycles G {c} := by
  have hex : ∃ (f : Fin 5 → V), Function.Injective f ∧
      (∀ j : Fin 5, G.Adj (f j) (f (cycSucc j))) ∧ (∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) := by
    obtain ⟨m, f, -, -, hf, hcyc, hmem⟩ := hC
    have hm5 : m = 5 := by
      have h := card_eq_cyclicOrder f hf hmem
      omega
    subst hm5
    exact ⟨f, hf, hcyc, hmem⟩
  obtain ⟨f, hf, hcyc, hmem⟩ := hex
  have htf : ∀ E : Finset V, ¬ G.IsNClique 3 E := htf_of_shortest_five' hC hshort hC5
  exact hitsOddCycles_singleton_of_unique hC hshort hC5 f hf hcyc hmem htf hV
    (three_intersection_fiveCycle_unique'' hC hshort hC5 htf hV)

/-- **ERDŐS #73 AT `k = 1` WITH THE OPTIMAL CONSTANT `1`, WHEN A SHORTEST ODD CYCLE OF `G` HAS FIVE
VERTICES AND `|V| ≤ 7` — A NEW INSTANCE OF THE HEADLINE THEOREM.**

```lean
IsOddCycle G C → (C shortest odd cycle) → C.card = 5 → |V| ≤ 7 → CloseToBipartite 1 G
```

**No `LocIndep` hypothesis occurs** — the instance is a statement about triangle-free graphs on at
most seven vertices, and `JSP90.htf_of_shortest_five'` shows triangle-freeness is a *consequence* of
the hypotheses here, so it is not needed either.  This is the five-cycle case of
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven`. -/
theorem closeToBipartite_one_of_shortest_five {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (hV : Fintype.card V ≤ 7) : CloseToBipartite 1 G := by
  obtain ⟨c, hc⟩ := hitsOddCycles_singleton_of_shortest_five hC hshort hC5 hV
  exact ⟨{c}, by simp, isBipartite_delete_of_hitsOddCycles hc⟩

/-! ## Part 3 — the triangle-free seven-vertex instance, with the optimal constant `1` -/

/-- **ON A TRIANGLE-FREE GRAPH OF ORDER AT MOST SEVEN EVERY ODD CYCLE HAS FIVE OR SEVEN VERTICES.** -/
theorem card_five_or_seven_of_triangleFree_card_le_seven (hV : Fintype.card V ≤ 7)
    (htf : ∀ D : Finset V, ¬ G.IsNClique 3 D) {C : Finset V} (hC : IsOddCycle G C) :
    C.card = 5 ∨ C.card = Fintype.card V := by
  have h5 := card_ge_five_of_isOddCycle_of_triangleFree htf hC
  have hle : C.card ≤ Fintype.card V := by
    have h1 := Finset.card_le_univ C
    have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    omega
  have hmod := card_mod_two_of_isOddCycle hC
  by_cases hseven : 7 ≤ C.card
  · right
    have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    omega
  · left
    omega

/-- **ERDŐS #73 AT `k = 1` WITH THE OPTIMAL CONSTANT `1`, ON TRIANGLE-FREE GRAPHS OF ORDER AT MOST
SEVEN — A NEW INSTANCE OF THE HEADLINE THEOREM, AND A STRICT STRENGTHENING OF
`JSP90.closeToBipartite_one_of_locIndep_one_card_le_seven_of_triangleFree_no5`.**

```lean
LocIndep 1 G → |V| ≤ 7 → (G has no 3-clique) → CloseToBipartite 1 G
```

`lean/JSPProblem/TriPair.lean` could prove this only with the extra hypothesis "no five-cycle",
because the five-cycle case was then open; with `JSP90.closeToBipartite_one_of_shortest_five` that
hypothesis is no longer needed.  A shortest odd cycle of a triangle-free graph on at most seven
vertices has five or seven vertices (`JSP90.card_five_or_seven_of_triangleFree_card_le_seven`); in
the first case Part 2 applies, in the second the cycle spans `V`
(`JSP90.closeToBipartite_one_of_shortest_oddCycle_of_card_eq`).  `LocIndep 1` is not used either. -/
theorem closeToBipartite_one_of_locIndep_one_card_le_seven_of_triangleFree
    (hV : Fintype.card V ≤ 7) (htf : ∀ D : Finset V, ¬ G.IsNClique 3 D) (hne : Nonempty V) :
    CloseToBipartite 1 G := by
  by_cases hodd : ∃ C : Finset V, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle hodd
    rcases card_five_or_seven_of_triangleFree_card_le_seven hV htf hC with hfive | hspan
    · exact closeToBipartite_one_of_shortest_five hC hshort hfive hV
    · exact closeToBipartite_one_of_shortest_oddCycle_of_card_eq hC hshort hspan
  · refine ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    exact isBipartite_of_no_oddCycle hodd

/-- **THE SAME INSTANCE IN THE TRANSVERSAL SHAPE: THE ODD CYCLES OF `G` HAVE A COMMON VERTEX.** -/
theorem hitsOddCycles_singleton_of_locIndep_one_card_le_seven_of_triangleFree
    (hV : Fintype.card V ≤ 7) (htf : ∀ D : Finset V, ¬ G.IsNClique 3 D) (hne : Nonempty V) :
    ∃ v : V, HitsOddCycles G {v} := by
  by_cases hodd : ∃ C : Finset V, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle hodd
    rcases card_five_or_seven_of_triangleFree_card_le_seven hV htf hC with hfive | hspan
    · exact hitsOddCycles_singleton_of_shortest_five hC hshort hfive hV
    · exact mem_hitsOddCycles_singleton_of_shortest_oddCycle_of_card_eq hC hshort hspan
  · obtain ⟨v⟩ := hne
    exact ⟨v, fun D hD => absurd ⟨D, hD⟩ hodd⟩

/-! ## Part 4 — the seven-vertex axis reduced to the triangle case -/

/-- **THE SHARP SEVEN-VERTEX INSTANCE WITH THE CONSTANT `2`, GIVEN THE TRIANGLE CASE.**

```lean
|V| ≤ 7 → (every triangle T of G has a vertex t ∈ T with G − (T \ {t}) bipartite)
  → CloseToBipartite 2 G
```

The constant `2` is the optimal one there (`JSPProblem/Six.lean`: the three-sun `sun3` on six
vertices satisfies `LocIndep 1` and has transversal number `2`).

**This is the reduction that makes the remaining work of the seven-vertex axis exactly one
statement.**  A shortest odd cycle `C` of `G` has three, five or seven vertices:

* `|C| = 5` — `JSP90.closeToBipartite_one_of_shortest_five` (this file);
* `|C| = 7 = |V|` — `JSP90.closeToBipartite_one_of_shortest_oddCycle_of_card_eq`
  (`lean/JSPProblem/Seven.lean`), because `C` spans the vertex set;
* `|C| = 3` — `C` is a triangle (`JSP90.isNClique_three_of_isOddCycle`), so `htri` supplies `t` with
  `G − (C \ {t})` bipartite, and `JSP90.closeToBipartite_of_residue`
  (`lean/JSPProblem/Residue.lean`) turns that into `CloseToBipartite (0 + |C \ {t}|) G =
  CloseToBipartite 2 G`.

So `htri` — the `|X| = 4` sub-case of MISSING LEMMA 1 — is the *only* remaining input. -/
theorem closeToBipartite_two_of_card_le_seven_of_triangleCase (hV : Fintype.card V ≤ 7)
    (htri : ∀ (T : Finset V), G.IsNClique 3 T → ∃ (t : V), t ∈ T ∧
      (deleteFinset G (T \ {t})).IsBipartite) : CloseToBipartite 2 G := by
  by_cases hodd : ∃ C : Finset V, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle hodd
    have h3 := isOddCycle_card_ge_three hC
    have hmod := card_mod_two_of_isOddCycle hC
    have hle : C.card ≤ Fintype.card V := by
      have h1 := Finset.card_le_univ C
      have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
      omega
    rcases le_or_gt C.card 4 with h | h
    · have hC3 : C.card = 3 := by omega
      have hT : G.IsNClique 3 C := isNClique_three_of_isOddCycle hC hC3
      obtain ⟨t, ht, hres⟩ := htri C hT
      have hcard : (C \ {t}).card = 2 := by
        have h1 : ({t} : Finset V).card = 1 := Finset.card_singleton t
        have h2 := Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr ht)
        omega
      have hres' : CloseToBipartite 0 (deleteFinset G (C \ {t})) := by
        refine ⟨∅, by simp, ?_⟩
        simpa [deleteFinset_empty] using hres
      obtain ⟨X, hX, hbis⟩ := closeToBipartite_of_residue (C := C \ {t}) (q := 0) hres'
      exact ⟨X, by omega, hbis⟩
    · by_cases hseven : 7 ≤ C.card
      · have hcard : C.card = Fintype.card V := by
          have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
          omega
        have h1 := closeToBipartite_one_of_shortest_oddCycle_of_card_eq hC hshort hcard
        obtain ⟨X, hX, hbis⟩ := h1
        exact ⟨X, by omega, hbis⟩
      · have hfive : C.card = 5 := by omega
        have h1 := closeToBipartite_one_of_shortest_five hC hshort hfive hV
        obtain ⟨X, hX, hbis⟩ := h1
        exact ⟨X, by omega, hbis⟩
  · have h1 : G.IsBipartite := isBipartite_of_no_oddCycle hodd
    refine ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    exact h1

/-- **The class of the instance, in the `LocIndepOneSmallOrder` shape of `lean/JSPProblem/Five.lean`.** -/
def LocIndepOneTriangleFree7.{w} (m n : ℕ) : Prop :=
  ∀ (W : Type w) (_ : Fintype W) (G : SimpleGraph W), Fintype.card W ≤ n → LocIndep 1 G →
    (∀ D : Finset W, ¬ G.IsNClique 3 D) → CloseToBipartite m G

/-- **ERDŐS #73 AT `k = 1`, CONSTANT `1`, ON TRIANGLE-FREE GRAPHS OF ORDER AT MOST SEVEN — THE
INSTANCE IN THE `Erdős73On` SHAPE.** -/
theorem erdos73On_one_triangleFree_seven : LocIndepOneTriangleFree7.{u} 1 7 :=
  fun (W : Type u) (_ : Fintype W) (G : SimpleGraph W) hV hG htf => by
    by_cases hne : Nonempty W
    · exact closeToBipartite_one_of_locIndep_one_card_le_seven_of_triangleFree hV htf hne
    · refine ⟨∅, by simp, ?_⟩
      rw [deleteFinset_empty]
      refine isBipartite_of_no_oddCycle (fun h => ?_)
      obtain ⟨D, hD⟩ := h
      obtain ⟨z, -⟩ := nonempty_of_card_pos (s := D) (by
        have h1 := isOddCycle_card_ge_three hD
        omega)
      exact absurd ⟨z⟩ hne

end
end JSP90
