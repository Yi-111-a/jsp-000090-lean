import JSPProblem.FiveCount

/-!
# JSP-000090, round 159 — `JSPProblem/Three.lean`: **THE SHAPE OF A THREE-INTERSECTION FIVE-CYCLE**

Attack family 81.  This file attacks the single blocker named by `discovery/JSP-000090/policy.json`
after round 155, namely `JSP90.ThreeIntersectionFiveCycleUnique` of `JSPProblem/FiveCount.lean`:

> **at most one five-cycle of `G` meets a shortest odd five-cycle `C` in exactly three points.**

Round 155 reduced the whole five-cycle case of the sharp seven-vertex instance to that one statement
(`JSP90.closeToBipartite_one_of_unique`) but proved nothing about the five-cycles themselves.  This file
proves the **local structure** of such a five-cycle — the two shapes it can have — which is exactly the
content `discovery/JSP-000090/r155.c` measured, and the input of any uniqueness proof.

## What is proved here (0 placeholders)

* **Part 0 — `JSP90.htf_of_shortest_five`.**  A shortest odd cycle of five vertices comes with its own
  triangle-freeness: a triangle would be a shorter odd cycle.
* **Part 1 — the arithmetic of the ring of a five-cycle.**  `JSP90.five_dist` (two distinct points are
  at distance one or two), `JSP90.five_iterate_ne`, `JSP90.five_iterate_five` (five steps come back),
  `JSP90.five_univ_eq_iter` (the five points of the ring), `JSP90.five_iterate_ne_pair`,
  `JSP90.not_mem_pair` (the three points of the ring at two, three or four steps), `JSP90.five_iterate_mem`
  and `JSP90.five_iterate_mem2` (which of the five points a position is).
* **Part 2 — `JSP90.neighIn_C_inj`: THE RING PAIR DETERMINES THE POINT.**  Two points of a shortest odd
  five-cycle with the same set of neighbours inside `C` are equal: `JSP90.five_pair_inj'` of round 152
  applied to `JSP90.filter_adj_C_eq_ringPair`.
* **Part 3 — `JSP90.diffC_eq_univ_sdiff`: THE ORDER HYPOTHESIS BUYS THE OUTSIDE SET.**  At `|V| ≤ 7` a
  five-cycle meeting `C` in three points has `D \ C = V \ C`, so `D` is determined by `D ∩ C`, i.e. by
  the missed pair `C \ D` (`JSP90.eq_of_inter_eq_of_diffC`).  This is the order hypothesis that the
  measurement of round 155 never used: **without `|V| ≤ 7` the uniqueness statement is false** (two
  five-cycles meeting `C` in three points can use two disjoint pairs of outside vertices; see
  `discovery/JSP-000090/r159.log`), so `|V| ≤ 7` is *essential* and this file records it explicitly.
* **Part 4 — `JSP90.IsShapeA`, `JSP90.IsShapeB`, `JSP90.exists_shape`: THE TWO SHAPES.**  Every
  three-intersection five-cycle of a triangle-free graph has one of exactly two shapes, proved by kernel
  proof from the cyclic ordering (no enumeration, no `decide` on graphs):

  * **shape A** — `w1 - w2 - a - b - c - w1`: the outside vertices are adjacent in `D`, `a - b - c` is a
    path of two edges of `C`, `w1 ~ c`, `w2 ~ a`;
  * **shape B** — `w1 - a - w2 - b - c - w1`: the outside vertices are at distance two in `D`, `a` sees
    both of them, and `b - c` is the only edge of `D` with both ends in `C`.

  The proof is the ring arithmetic of Part 1: the two positions of `D` outside `C` are at distance one
  (`JSP90.five_dist`, first two cases) or two (last two cases) along the ring, and
  `JSP90.compl_eq_pair` turns the cardinality-two complement into the corresponding pair.
* **Part 5 — what the shapes force.**  `JSP90.card_adjIn_D_eq_two` is round 152's degree lemma in the
  language of `AdjIn`, and with it
  * `JSP90.adjIn_D_pair_of_shapeA`: `AdjIn G w1 D = {c, w2}` and `AdjIn G w2 D = {a, w1}`;
  * `JSP90.adjIn_D_pair_of_shapeB`: `AdjIn G w1 D = {a, c}` and `AdjIn G w2 D = {a, b}`;
  * `JSP90.disjoint_adjIn_C_of_shapeA` and `JSP90.inter_adjIn_C_ne_empty_of_shapeB`: the two shapes are
    **mutually exclusive over the same outside pair**, because `AdjIn G w1 C ∩ AdjIn G w2 C` is empty
    in shape A (a common neighbour would close a triangle with `w1 - w2`) and contains `a` in shape B.

## What is *not* proved

The uniqueness itself (`JSP90.ThreeIntersectionFiveCycleUnique`, still a `def` in
`JSPProblem/FiveCount.lean`) and with it the five-cycle case of
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven`.  The remaining steps are named at the end of
this file and in `discovery/JSP-000090/policy.json`.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps reporting
`missing_theorems = ["jsp_000090_main"]`.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 4000000

local instance thDecidableAdjRel (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

local instance thDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Part 0 — a shortest odd five-cycle comes with its own triangle-freeness -/

/-- **A SHORTEST ODD CYCLE OF FIVE VERTICES IS TRIANGLE-FREE.**

A triangle of `G` is an odd cycle (`JSP90.isOddCycle_of_isNClique_three`) with three vertices, which is
shorter than `C`. -/
theorem htf_of_shortest_five {C : Finset V}
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5) :
    ∀ E : Finset V, ¬ G.IsNClique 3 E := by
  intro E hE
  have hodd : IsOddCycle G E := isOddCycle_of_isNClique_three hE
  have hcard : E.card = 3 := hE.2
  have h := hshort E hodd
  omega

/-! ## Part 1 — the arithmetic of the ring of a five-cycle -/

/-- **TWO DISTINCT POINTS OF A FIVE-CYCLE ARE AT DISTANCE ONE OR TWO ALONG THE RING.** -/
lemma five_dist (j k : Fin 5) (hne : j ≠ k) :
    cycSucc j = k ∨ cycPred j = k ∨ cycSucc (cycSucc j) = k ∨ cycPred (cycPred j) = k := by
  revert hne
  fin_cases j <;> fin_cases k <;> intro h <;> try {exact absurd rfl h} <;> decide

/-- **TWO ITERATES OF THE CYCLIC SUCCESSOR OUT OF THE SAME POINT, AT DIFFERENT STEPS BELOW FIVE, ARE
DIFFERENT.** -/
lemma five_iterate_ne (j : Fin 5) {k l : ℕ} (hl : l < 5) (hkl : k < l)
    (h : (cycSucc^[k] : Fin 5 → Fin 5) j = (cycSucc^[l] : Fin 5 → Fin 5) j) : False := by
  have hv := congrArg Fin.val h
  have h1 := cycSucc_pow_val (n := 5) k j
  have h2 := cycSucc_pow_val (n := 5) l j
  simp only [h1, h2] at hv
  have hj : j.val < 5 := j.2
  omega

/-- **FIVE STEPS AROUND THE RING OF A FIVE-CYCLE COME BACK TO THE STARTING POINT.** -/
lemma five_iterate_five (j : Fin 5) : (cycSucc^[5] : Fin 5 → Fin 5) j = j := by
  refine Fin.ext ?_
  have h := cycSucc_pow_val (n := 5) 5 j
  have hj : j.val < 5 := j.2
  simp only [h]
  omega

/-- **ONE, TWO, THREE, FOUR AND FIVE STEPS AROUND THE RING, WRITTEN AS NESTED SUCCESSORS.** -/
lemma five_iterate_one (j : Fin 5) : (cycSucc^[1] : Fin 5 → Fin 5) j = cycSucc j := by
  rw [Function.iterate_succ_apply, Function.iterate_zero_apply]

lemma five_iterate_two (j : Fin 5) :
    (cycSucc^[2] : Fin 5 → Fin 5) j = cycSucc (cycSucc j) := by
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_zero_apply]

lemma five_iterate_three (j : Fin 5) :
    (cycSucc^[3] : Fin 5 → Fin 5) j = cycSucc (cycSucc (cycSucc j)) := by
  rw [Function.iterate_succ_apply, five_iterate_two]

lemma five_iterate_four (j : Fin 5) :
    (cycSucc^[4] : Fin 5 → Fin 5) j = cycSucc (cycSucc (cycSucc (cycSucc j))) := by
  rw [Function.iterate_succ_apply, five_iterate_three]

lemma five_iterate_five' (j : Fin 5) :
    (cycSucc^[5] : Fin 5 → Fin 5) j = cycSucc (cycSucc (cycSucc (cycSucc (cycSucc j)))) := by
  rw [Function.iterate_succ_apply, five_iterate_four]

/-- **THE RING OF A FIVE-CYCLE, WRITTEN OUT.** -/
lemma five_univ_eq_iter (j : Fin 5) :
    (Finset.univ : Finset (Fin 5))
      = {j, cycSucc j, cycSucc (cycSucc j), cycSucc (cycSucc (cycSucc j)),
        cycSucc (cycSucc (cycSucc (cycSucc j)))} := by
  ext i
  fin_cases i <;> fin_cases j <;> simp [cycSucc] <;> decide

/-- **A POINT OF THE RING WHICH IS NEITHER `j` NOR ITS SUCCESSOR IS ONE OF THE THREE REMAINING
POINTS.** -/
lemma five_iterate_mem (j i : Fin 5) (hne1 : i ≠ j) (hne2 : i ≠ cycSucc j) :
    cycSucc (cycSucc j) = i ∨ cycSucc (cycSucc (cycSucc j)) = i ∨
      cycSucc (cycSucc (cycSucc (cycSucc j))) = i := by
  have hi : i ∈ ({j, cycSucc j, cycSucc (cycSucc j), cycSucc (cycSucc (cycSucc j)),
      cycSucc (cycSucc (cycSucc (cycSucc j)))} : Finset (Fin 5)) := by
    rw [← five_univ_eq_iter]
    exact Finset.mem_univ i
  rcases Finset.mem_insert.mp hi with h | h
  · exact absurd h hne1
  · rcases Finset.mem_insert.mp h with h | h
    · exact absurd h hne2
    · rcases Finset.mem_insert.mp h with h | h
      · exact Or.inl h.symm
      · rcases Finset.mem_insert.mp h with h | h
        · exact Or.inr (Or.inl h.symm)
        · have h' : i = cycSucc (cycSucc (cycSucc (cycSucc j))) := Finset.mem_singleton.mp h
          exact Or.inr (Or.inr h'.symm)

/-- **A POINT OF THE RING WHICH IS NEITHER `j` NOR ITS SUCCESSOR-SUCCESSOR IS ONE OF THE THREE
REMAINING POINTS** — the version used in shape B, where the outside positions are `j` and
`cycSucc (cycSucc j)`. -/
lemma five_iterate_mem2 (j i : Fin 5) (hne1 : i ≠ j) (hne2 : i ≠ cycSucc (cycSucc j)) :
    cycSucc j = i ∨ cycSucc (cycSucc (cycSucc j)) = i ∨
      cycSucc (cycSucc (cycSucc (cycSucc j))) = i := by
  have hi : i ∈ ({j, cycSucc j, cycSucc (cycSucc j), cycSucc (cycSucc (cycSucc j)),
      cycSucc (cycSucc (cycSucc (cycSucc j)))} : Finset (Fin 5)) := by
    rw [← five_univ_eq_iter]
    exact Finset.mem_univ i
  rcases Finset.mem_insert.mp hi with h | h
  · exact absurd h hne1
  · rcases Finset.mem_insert.mp h with h | h
    · exact Or.inl h.symm
    · rcases Finset.mem_insert.mp h with h | h
      · exact absurd h hne2
      · rcases Finset.mem_insert.mp h with h | h
        · exact Or.inr (Or.inl h.symm)
        · have h' : i = cycSucc (cycSucc (cycSucc (cycSucc j))) := Finset.mem_singleton.mp h
          exact Or.inr (Or.inr h'.symm)

/-- **THREE OR MORE STEPS AROUND THE RING LAND NEITHER AT `j` NOR AT ITS SUCCESSOR.** -/
lemma five_iterate_ne_pair (j : Fin 5) {k : ℕ} (hk : 2 ≤ k) (hk5 : k < 5) :
    ((cycSucc^[k] : Fin 5 → Fin 5) j ≠ j) ∧ ((cycSucc^[k] : Fin 5 → Fin 5) j ≠ cycSucc j) := by
  refine ⟨fun h => five_iterate_ne j (k := 0) (l := k) hk5 (by omega) h.symm, fun h => ?_⟩
  refine five_iterate_ne j (k := 1) (l := k) hk5 (by omega) ?_
  rw [h, Function.iterate_succ_apply, Function.iterate_zero_apply]

/-- **A POINT TWO, THREE OR FOUR STEPS AROUND THE RING IS NEITHER `j` NOR ITS SUCCESSOR.** -/
lemma not_mem_pair (j : Fin 5) (k : ℕ) (hk2 : 2 ≤ k) (hk5 : k < 5) :
    (cycSucc^[k] : Fin 5 → Fin 5) j ∉ ({j, cycSucc j} : Finset (Fin 5)) := by
  have h := five_iterate_ne_pair j hk2 hk5
  intro hi
  rcases Finset.mem_insert.mp hi with hi | hi
  · exact h.1 hi
  · exact h.2 (Finset.mem_singleton.mp hi)

/-! ## Part 2 — the ring pair determines the point of `C` -/

/-- **TWO POINTS OF A SHORTEST ODD FIVE-CYCLE WITH THE SAME NEIGHBOURS INSIDE IT ARE EQUAL.** -/
theorem neighIn_C_inj {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) {x y : V} (hx : x ∈ C) (hy : y ∈ C)
    (h : C.filter (fun z => G.Adj x z) = C.filter (fun z => G.Adj y z)) : x = y := by
  obtain ⟨i, hi⟩ := hmem x |>.mp hx
  obtain ⟨j, hj⟩ := hmem y |>.mp hy
  have h1 := filter_adj_C_eq_ringPair hC hshort hC5 f hf hcyc hmem i
  have h2 := filter_adj_C_eq_ringPair hC hshort hC5 f hf hcyc hmem j
  have hA : ({f (cycSucc i), f (cycPred i)} : Finset V) = C.filter (fun z => G.Adj x z) := by
    rw [← hi]
    exact h1.symm
  have hB : ({f (cycSucc j), f (cycPred j)} : Finset V) = C.filter (fun z => G.Adj y z) := by
    rw [← hj]
    exact h2.symm
  have h3 : ({f (cycSucc i), f (cycPred i)} : Finset V) = {f (cycSucc j), f (cycPred j)} :=
    hA.trans (h.trans hB.symm)
  have h4 := five_pair_inj' f hf i j h3
  exact hi.symm.trans ((congrArg f h4) ▸ hj)

/-! ## Part 3 — at `|V| ≤ 7` a three-intersection five-cycle is determined by its missed pair -/

/-- **THE OUTSIDE PART OF A THREE-INTERSECTION FIVE-CYCLE IS THE WHOLE OF `V \ C`.** -/
theorem diffC_eq_univ_sdiff {C D : Finset V} (hC5 : C.card = 5) (hD5 : D.card = 5)
    (hi : (D ∩ C).card = 3) (hV : Fintype.card V ≤ 7) :
    D \ C = (Finset.univ : Finset V) \ C := by
  have hsub : D \ C ⊆ (Finset.univ : Finset V) \ C := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hz).2⟩
  have h1 := Finset.card_sdiff_add_card_inter D C
  have hcardD : (D \ C).card = 2 := by omega
  have hge : 7 ≤ Fintype.card V := by
    have h2 := Finset.card_union_add_card_inter C D
    have h2' : (C ∩ D).card = 3 := by rw [Finset.inter_comm]; exact hi
    have h3 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
    have h4 := Finset.card_le_univ (C ∪ D)
    rw [hC5, hD5, h2'] at h2
    omega
  have hcardV : Fintype.card V = 7 := by omega
  have h5 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset V) C
  have h6 : ((Finset.univ : Finset V) ∩ C).card = 5 := by rw [Finset.inter_comm]; simp [hC5]
  have h7 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
  have hcardU : ((Finset.univ : Finset V) \ C).card = 2 := by omega
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

/-- **`s ∩ t ∪ s \ t = s`** (the `Finset` form of the set-theoretic identity of the same name). -/
lemma inter_union_sdiff' (s t : Finset V) : s ∩ t ∪ s \ t = s := by
  ext z
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · intro hz
    rcases hz with hz | hz
    · exact hz.1
    · exact hz.1
  · intro hz
    by_cases hzt : z ∈ t
    · exact Or.inl ⟨hz, hzt⟩
    · exact Or.inr ⟨hz, hzt⟩

/-- **TWO VERTEX SETS WITH THE SAME PARTS INSIDE AND OUTSIDE `C` ARE EQUAL.** -/
theorem eq_of_inter_eq_of_diffC {C D D' : Finset V} (h1 : D ∩ C = D' ∩ C) (h2 : D \ C = D' \ C) :
    D = D' := by
  rw [← inter_union_sdiff' D C, ← inter_union_sdiff' D' C, h1, h2]

/-! ## Part 4 — the two shapes of a three-intersection five-cycle -/

/-- **AN ELEMENT OF A FIVE-ELEMENT SET OF NAMED POINTS IS ONE OF THE FIVE.** -/
lemma mem_five {a b c d e y : V} (hy : y ∈ ({a, b, c, d, e} : Finset V)) :
    y = a ∨ y = b ∨ y = c ∨ y = d ∨ y = e := by
  rcases Finset.mem_insert.mp hy with h | h
  · exact Or.inl h
  · rcases Finset.mem_insert.mp h with h | h
    · exact Or.inr (Or.inl h)
    · rcases Finset.mem_insert.mp h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · rcases Finset.mem_insert.mp h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_singleton.mp h))))

lemma mem_five_a {a b c d e y : V} (h : y = a) : y ∈ ({a, b, c, d, e} : Finset V) :=
  Finset.mem_insert.mpr (Or.inl h)

lemma mem_five_b {a b c d e y : V} (h : y = b) : y ∈ ({a, b, c, d, e} : Finset V) :=
  Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))

lemma mem_five_c {a b c d e y : V} (h : y = c) : y ∈ ({a, b, c, d, e} : Finset V) :=
  Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl h)))))

lemma mem_five_d {a b c d e y : V} (h : y = d) : y ∈ ({a, b, c, d, e} : Finset V) :=
  Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
    (Or.inr (Finset.mem_insert.mpr (Or.inl h)))))))

lemma mem_five_e {a b c d e y : V} (h : y = e) : y ∈ ({a, b, c, d, e} : Finset V) :=
  Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
    (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))))))))

/-- **SHAPE A: THE OUTSIDE POINTS ARE ADJACENT IN `D`.**

The five-cycle runs `w1 - w2 - a - b - c - w1`, so `a - b - c` is a path of two edges of `C`, `w1` is
adjacent to the far endpoint `c` and `w2` to the near endpoint `a`. -/
def IsShapeA (G : SimpleGraph V) (C D : Finset V) (w1 w2 : V) : Prop :=
  ∃ a b c : V, a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ w1 ∉ C ∧ w2 ∉ C ∧ w1 ≠ w2 ∧
    D = {a, b, c, w1, w2} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c w1 ∧ G.Adj w2 a ∧ G.Adj w1 w2

/-- **SHAPE B: THE OUTSIDE POINTS ARE AT DISTANCE TWO IN `D`.**

The five-cycle runs `w1 - a - w2 - b - c - w1`: `a` sees both outside points, `w2` also sees `b`, `w1`
also sees `c`, and `b - c` is the only edge of `D` with both ends in `C`. -/
def IsShapeB (G : SimpleGraph V) (C D : Finset V) (w1 w2 : V) : Prop :=
  ∃ a b c : V, a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ w1 ∉ C ∧ w2 ∉ C ∧ w1 ≠ w2 ∧
    D = {a, b, c, w1, w2} ∧ G.Adj b c ∧ G.Adj a w1 ∧ G.Adj a w2 ∧ G.Adj b w2 ∧ G.Adj c w1

/-- **THE `D`-SIDE DATA OF SHAPE A, WHEN THE TWO OUTSIDE POSITIONS OF THE CYCLIC ORDERING OF `D` ARE
ADJACENT.** -/
theorem shapeA_data {C D : Finset V} (g : Fin 5 → V) (hg : Function.Injective g)
    (hgcyc : ∀ j : Fin 5, G.Adj (g j) (g (cycSucc j))) (hmem : ∀ y : V, y ∈ D ↔ ∃ j : Fin 5, g j = y)
    {P : Finset (Fin 5)}
    (hP : P = (Finset.univ : Finset (Fin 5)).filter (fun i => g i ∈ C)) {j : Fin 5} (hj : j ∉ P)
    (hcompl : (Finset.univ : Finset (Fin 5)) \ P = {j, cycSucc j}) :
    ∃ w1 w2 : V, w1 ≠ w2 ∧ IsShapeA G C D w1 w2 := by
  have hmemP : ∀ i ∈ ({j, cycSucc j} : Finset (Fin 5)), i ∉ P := by
    intro i hi
    have h3 : i ∈ (Finset.univ : Finset (Fin 5)) \ P := by rw [hcompl]; exact hi
    exact (Finset.mem_sdiff.mp h3).2
  have hmemC : ∀ i : Fin 5, i ∉ ({j, cycSucc j} : Finset (Fin 5)) → g i ∈ C := by
    intro i hi
    by_contra hcon
    have h1 : i ∉ P := by
      rw [hP]
      intro hmem
      exact hcon (Finset.mem_filter.mp hmem).2
    have h3 : i ∈ (Finset.univ : Finset (Fin 5)) \ P := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩
    rw [hcompl] at h3
    exact hi h3
  have hsuccne : cycSucc j ≠ j := cycSucc_ne j (by omega)
  have h23 : cycSucc (cycSucc j) ≠ cycSucc (cycSucc (cycSucc j)) := by
    intro h
    refine five_iterate_ne j (k := 2) (l := 3) (by omega) (by omega) ?_
    rw [five_iterate_two, five_iterate_three]
    exact h
  have h34 : cycSucc (cycSucc (cycSucc j)) ≠ cycSucc (cycSucc (cycSucc (cycSucc j))) := by
    intro h
    refine five_iterate_ne j (k := 3) (l := 4) (by omega) (by omega) ?_
    rw [five_iterate_three, five_iterate_four]
    exact h
  have h24 : cycSucc (cycSucc j) ≠ cycSucc (cycSucc (cycSucc (cycSucc j))) := by
    intro h
    refine five_iterate_ne j (k := 2) (l := 4) (by omega) (by omega) ?_
    rw [five_iterate_two, five_iterate_four]
    exact h
  have haC : g (cycSucc^[2] j) ∈ C := hmemC _ (not_mem_pair j 2 (by omega) (by omega))
  have hbC : g (cycSucc^[3] j) ∈ C := hmemC _ (not_mem_pair j 3 (by omega) (by omega))
  have hcC : g (cycSucc^[4] j) ∈ C := hmemC _ (not_mem_pair j 4 (by omega) (by omega))
  have hab' : g (cycSucc^[2] j) ≠ g (cycSucc^[3] j) := fun h => h23 (hg h)
  have hbc' : g (cycSucc^[3] j) ≠ g (cycSucc^[4] j) := fun h => h34 (hg h)
  have hac' : g (cycSucc^[2] j) ≠ g (cycSucc^[4] j) := fun h => h24 (hg h)
  have hw1C : g j ∉ C := by
    intro hc
    exact hj (by rw [hP]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  have hw2C : g (cycSucc j) ∉ C := by
    intro hc
    exact hmemP (cycSucc j) (by simp) (by rw [hP]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  have hwne : g j ≠ g (cycSucc j) := fun h => hsuccne (hg h.symm)
  have hDset : D = {g (cycSucc^[2] j), g (cycSucc^[3] j), g (cycSucc^[4] j), g j, g (cycSucc j)} := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hgy⟩ := (hmem y).mp hy
      rw [← hgy]
      by_cases hiP : i ∈ P
      · have hne1 : i ≠ j := fun h => hj (h ▸ hiP)
        have hne2 : i ≠ cycSucc j := fun h => hmemP _ (by simp) (h ▸ hiP)
        rcases five_iterate_mem j i hne1 hne2 with h | h | h
        · exact mem_five_a (congrArg g h.symm)
        · exact mem_five_b (congrArg g h.symm)
        · exact mem_five_c (congrArg g h.symm)
      · have hiQ : i ∈ (Finset.univ : Finset (Fin 5)) \ P := Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, hiP⟩
        rw [hcompl] at hiQ
        by_cases hij : i = j
        · exact mem_five_d (congrArg g hij)
        · have hisj : i = cycSucc j := by
            rcases Finset.mem_insert.mp hiQ with h | h
            · exact absurd h hij
            · exact Finset.mem_singleton.mp h
          exact mem_five_e (congrArg g hisj)
    · intro hy
      obtain ⟨i, hgy⟩ : ∃ i : Fin 5, g i = y := by
        rcases mem_five hy with h | h | h | h | h
        · exact ⟨cycSucc^[2] j, h.symm⟩
        · exact ⟨cycSucc^[3] j, h.symm⟩
        · exact ⟨cycSucc^[4] j, h.symm⟩
        · exact ⟨j, h.symm⟩
        · exact ⟨cycSucc j, h.symm⟩
      exact (hmem y).mpr ⟨i, hgy⟩
  have hcw1 : G.Adj (g (cycSucc^[4] j)) (g j) := by
    have h := hgcyc (cycSucc^[4] j)
    rw [five_iterate_four, ← five_iterate_five', five_iterate_five j] at h
    exact h
  refine Exists.intro (g j) ?_
  refine Exists.intro (g (cycSucc j)) ?_
  refine And.intro hwne ?_
  refine Exists.intro (g (cycSucc^[2] j)) ?_
  refine Exists.intro (g (cycSucc^[3] j)) ?_
  refine Exists.intro (g (cycSucc^[4] j)) ?_
  exact And.intro haC (And.intro hbC (And.intro hcC (And.intro hab' (And.intro hbc'
    (And.intro hac' (And.intro hw1C (And.intro hw2C (And.intro hwne (And.intro hDset
      (And.intro (hgcyc (cycSucc^[2] j)) (And.intro (hgcyc (cycSucc^[3] j))
        (And.intro hcw1 (And.intro (hgcyc (cycSucc j)) (hgcyc j))))))))))))))

/-- **THE `D`-SIDE DATA OF SHAPE B, WHEN THE TWO OUTSIDE POSITIONS OF THE CYCLIC ORDERING OF `D` ARE AT
DISTANCE TWO.** -/
theorem shapeB_data {C D : Finset V} (g : Fin 5 → V) (hg : Function.Injective g)
    (hgcyc : ∀ j : Fin 5, G.Adj (g j) (g (cycSucc j))) (hmem : ∀ y : V, y ∈ D ↔ ∃ j : Fin 5, g j = y)
    {P : Finset (Fin 5)}
    (hP : P = (Finset.univ : Finset (Fin 5)).filter (fun i => g i ∈ C)) {j : Fin 5} (hj : j ∉ P)
    (hcompl : (Finset.univ : Finset (Fin 5)) \ P = {j, cycSucc (cycSucc j)}) :
    ∃ w1 w2 : V, w1 ≠ w2 ∧ IsShapeB G C D w1 w2 := by
  have hmemP : ∀ i ∈ ({j, cycSucc (cycSucc j)} : Finset (Fin 5)), i ∉ P := by
    intro i hi
    have h3 : i ∈ (Finset.univ : Finset (Fin 5)) \ P := by rw [hcompl]; exact hi
    exact (Finset.mem_sdiff.mp h3).2
  have hmemC : ∀ i : Fin 5, i ∉ ({j, cycSucc (cycSucc j)} : Finset (Fin 5)) → g i ∈ C := by
    intro i hi
    by_contra hcon
    have h1 : i ∉ P := by
      rw [hP]
      intro hmem
      exact hcon (Finset.mem_filter.mp hmem).2
    have h3 : i ∈ (Finset.univ : Finset (Fin 5)) \ P := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩
    rw [hcompl] at h3
    exact hi h3
  have hnotmem1 : cycSucc j ∉ ({j, cycSucc (cycSucc j)} : Finset (Fin 5)) := by
    intro hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · exact cycSucc_ne j (by omega) hi
    · exact cycSucc_ne j (by omega)
        ((cycSucc_injective j _ (Finset.mem_singleton.mp hi)).symm)
  have hnotmem3 : (cycSucc^[3] : Fin 5 → Fin 5) j ∉ ({j, cycSucc (cycSucc j)} : Finset (Fin 5)) := by
    intro hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · refine five_iterate_ne j (k := 0) (l := 3) (by omega) (by omega) ?_
      rw [five_iterate_three]
      exact hi.symm
    · refine five_iterate_ne j (k := 2) (l := 3) (by omega) (by omega) ?_
      rw [five_iterate_three, five_iterate_two]
      exact (Finset.mem_singleton.mp hi).symm
  have hnotmem4 : (cycSucc^[4] : Fin 5 → Fin 5) j ∉ ({j, cycSucc (cycSucc j)} : Finset (Fin 5)) := by
    intro hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · refine five_iterate_ne j (k := 0) (l := 4) (by omega) (by omega) ?_
      rw [five_iterate_four]
      exact hi.symm
    · refine five_iterate_ne j (k := 2) (l := 4) (by omega) (by omega) ?_
      rw [five_iterate_four, five_iterate_two]
      exact (Finset.mem_singleton.mp hi).symm
  have h13 : cycSucc j ≠ cycSucc (cycSucc (cycSucc j)) := by
    intro h
    refine five_iterate_ne j (k := 1) (l := 3) (by omega) (by omega) ?_
    rw [five_iterate_one, five_iterate_three]
    exact h
  have h34 : cycSucc (cycSucc (cycSucc j)) ≠ cycSucc (cycSucc (cycSucc (cycSucc j))) := by
    intro h
    refine five_iterate_ne j (k := 3) (l := 4) (by omega) (by omega) ?_
    rw [five_iterate_three, five_iterate_four]
    exact h
  have h14 : cycSucc j ≠ cycSucc (cycSucc (cycSucc (cycSucc j))) := by
    intro h
    refine five_iterate_ne j (k := 1) (l := 4) (by omega) (by omega) ?_
    rw [five_iterate_one, five_iterate_four]
    exact h
  have haC : g (cycSucc j) ∈ C := hmemC _ hnotmem1
  have hbC : g (cycSucc^[3] j) ∈ C := hmemC _ hnotmem3
  have hcC : g (cycSucc^[4] j) ∈ C := hmemC _ hnotmem4
  have hab' : g (cycSucc j) ≠ g (cycSucc^[3] j) := fun h => h13 (hg h)
  have hbc' : g (cycSucc^[3] j) ≠ g (cycSucc^[4] j) := fun h => h34 (hg h)
  have hac' : g (cycSucc j) ≠ g (cycSucc^[4] j) := fun h => h14 (hg h)
  have hw1C : g j ∉ C := by
    intro hc
    exact hj (by rw [hP]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  have hw2C : g (cycSucc^[2] j) ∉ C := by
    intro hc
    exact hmemP (cycSucc^[2] j) (by simp)
      (by rw [hP]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  have hwne : g j ≠ g (cycSucc^[2] j) := by
    intro h
    refine five_iterate_ne j (k := 0) (l := 2) (by omega) (by omega) ?_
    rw [five_iterate_two]
    exact hg h
  have hDset : D = {g (cycSucc j), g (cycSucc^[3] j), g (cycSucc^[4] j), g j, g (cycSucc^[2] j)} := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hgy⟩ := (hmem y).mp hy
      rw [← hgy]
      by_cases hiP : i ∈ P
      · have hne1 : i ≠ j := fun h => hj (h ▸ hiP)
        have hne2 : i ≠ cycSucc (cycSucc j) := fun h => hmemP _ (by simp) (h ▸ hiP)
        rcases five_iterate_mem2 j i hne1 hne2 with h | h | h
        · exact mem_five_a (congrArg g h.symm)
        · exact mem_five_b (congrArg g h.symm)
        · exact mem_five_c (congrArg g h.symm)
      · have hiQ : i ∈ (Finset.univ : Finset (Fin 5)) \ P := Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, hiP⟩
        rw [hcompl] at hiQ
        by_cases hij : i = j
        · exact mem_five_d (congrArg g hij)
        · have hisj : i = cycSucc (cycSucc j) := by
            rcases Finset.mem_insert.mp hiQ with h | h
            · exact absurd h hij
            · exact Finset.mem_singleton.mp h
          exact mem_five_e (congrArg g hisj)
    · intro hy
      obtain ⟨i, hgy⟩ : ∃ i : Fin 5, g i = y := by
        rcases mem_five hy with h | h | h | h | h
        · exact ⟨cycSucc j, h.symm⟩
        · exact ⟨cycSucc^[3] j, h.symm⟩
        · exact ⟨cycSucc^[4] j, h.symm⟩
        · exact ⟨j, h.symm⟩
        · exact ⟨cycSucc^[2] j, h.symm⟩
      exact (hmem y).mpr ⟨i, hgy⟩
  have hcw1 : G.Adj (g (cycSucc^[4] j)) (g j) := by
    have h := hgcyc (cycSucc^[4] j)
    rw [five_iterate_four, ← five_iterate_five', five_iterate_five j] at h
    exact h
  refine Exists.intro (g j) ?_
  refine Exists.intro (g (cycSucc^[2] j)) ?_
  refine And.intro hwne ?_
  refine Exists.intro (g (cycSucc j)) ?_
  refine Exists.intro (g (cycSucc^[3] j)) ?_
  refine Exists.intro (g (cycSucc^[4] j)) ?_
  exact And.intro haC (And.intro hbC (And.intro hcC (And.intro hab' (And.intro hbc'
    (And.intro hac' (And.intro hw1C (And.intro hw2C (And.intro hwne (And.intro hDset
      (And.intro (hgcyc (cycSucc^[3] j)) (And.intro (hgcyc j).symm
        (And.intro (hgcyc (cycSucc j)) (And.intro (hgcyc (cycSucc^[2] j)).symm
          hcw1)))))))))))))

/-- **IF THE COMPLEMENT OF `P` IN THE FIVE POSITIONS HAS CARDINALITY TWO AND DOES NOT CONTAIN `j` OR
`k`, THEN IT IS THE PAIR `{j, k}`.** -/
lemma compl_eq_pair {P : Finset (Fin 5)} {j k : Fin 5}
    (hcard : ((Finset.univ : Finset (Fin 5)) \ P).card = 2) (hj : j ∉ P) (hk : k ∉ P)
    (hne : j ≠ k) : (Finset.univ : Finset (Fin 5)) \ P = {j, k} := by
  have hcard2 : ({j, k} : Finset (Fin 5)).card = 2 := Finset.card_pair_eq_two_iff.mpr hne
  have hsub : ({j, k} : Finset (Fin 5)) ⊆ (Finset.univ : Finset (Fin 5)) \ P := by
    intro i hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · subst hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩
    · have hi' : i = k := Finset.mem_singleton.mp hi
      subst hi'
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩
  refine (Finset.eq_of_subset_of_card_le (s := ({j, k} : Finset (Fin 5)))
    (t := (Finset.univ : Finset (Fin 5)) \ P) hsub ?_).symm
  omega

/-- **EVERY THREE-INTERSECTION FIVE-CYCLE HAS ONE OF THE TWO SHAPES.** -/
theorem exists_shape {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (hD : IsOddCycle G D) (hD5 : D.card = 5)
    (hi : (D ∩ C).card = 3) :
    (∃ w1 w2 : V, w1 ≠ w2 ∧ IsShapeA G C D w1 w2) ∨
      (∃ w1 w2 : V, w1 ≠ w2 ∧ IsShapeB G C D w1 w2) := by
  obtain ⟨m, g, -, -, hginj, hgcyc, hmemD⟩ := hD
  have hm5 : m = 5 := by
    have h := card_eq_cyclicOrder g hginj hmemD
    omega
  subst hm5
  set P : Finset (Fin 5) := (Finset.univ : Finset (Fin 5)).filter (fun i => g i ∈ C) with hPdef
  have hPsub : Finset.image g P = D ∩ C := by
    ext y
    simp only [hPdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter]
    constructor
    · rintro ⟨i, hiP, hgy⟩
      exact ⟨(hmemD y).mpr ⟨i, hgy⟩, hgy ▸ hiP⟩
    · intro hy
      obtain ⟨i, hgy⟩ := (hmemD y).mp hy.1
      exact ⟨i, hgy ▸ hy.2, hgy⟩
  have hPcard : P.card = 3 := by
    have h1 := Finset.card_image_of_injective (P : Finset (Fin 5)) (f := g)
      (fun a b hab => hginj hab)
    rw [hPsub, hi] at h1
    exact h1.symm
  have hcompl0 : ((Finset.univ : Finset (Fin 5)) \ P).card = 2 := by
    have h1 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin 5)) P
    have h2 : ((Finset.univ : Finset (Fin 5)) ∩ P).card = P.card := by rw [Finset.inter_comm]; simp
    have h3 : ((Finset.univ : Finset (Fin 5))).card = 5 := Finset.card_fin 5
    rw [h2, h3] at h1
    omega
  have hne0 : ((Finset.univ : Finset (Fin 5)) \ P).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j, hjQ⟩ := hne0
  have hne1 : (((Finset.univ : Finset (Fin 5)) \ P).erase j).Nonempty := by
    by_contra hcon
    have h2 : ((Finset.univ : Finset (Fin 5)) \ P).erase j = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcon
    have h3 : ((Finset.univ : Finset (Fin 5)) \ P).card = 1 := by
      have h4 := Finset.card_erase_add_one (show j ∈ ((Finset.univ : Finset (Fin 5)) \ P)
        from Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hjQ).2⟩)
      rw [h2, Finset.card_empty] at h4
      exact h4.symm
    omega
  obtain ⟨k, hk⟩ := hne1
  have hkQ : k ∈ (Finset.univ : Finset (Fin 5)) \ P := Finset.mem_of_mem_erase hk
  have hne : k ≠ j := Finset.ne_of_mem_erase hk
  have hj : j ∉ P := (Finset.mem_sdiff.mp hjQ).2
  have hkP : k ∉ P := (Finset.mem_sdiff.mp hkQ).2
  rcases five_dist j k hne.symm with hd | hd | hd | hd
  · refine Or.inl (shapeA_data g hginj hgcyc hmemD hPdef hj
      (by rw [hd]; exact (@compl_eq_pair P j k hcompl0 hj hkP hne.symm)))
  · have hjk : cycSucc k = j := by rw [← hd]; exact cycSucc_cycPred_five j
    refine Or.inl (shapeA_data g hginj hgcyc hmemD hPdef hkP
      (@compl_eq_pair P k (cycSucc k) hcompl0 hkP (hjk ▸ hj) ((cycSucc_ne k (by omega)).symm)))
  · refine Or.inr (shapeB_data g hginj hgcyc hmemD hPdef hj
      (by rw [hd]; exact (@compl_eq_pair P j k hcompl0 hj hkP hne.symm)))
  · have hjk : cycSucc (cycSucc k) = j := by
      have h1 : cycSucc k = cycPred j := by rw [← hd]; exact cycSucc_cycPred_five (cycPred j)
      exact (congrArg cycSucc h1).trans (cycSucc_cycPred_five j)
    refine Or.inr (shapeB_data g hginj hgcyc hmemD hPdef hkP
      (@compl_eq_pair P k (cycSucc (cycSucc k)) hcompl0 hkP (hjk ▸ hj) (by rw [hjk]; exact hne)))

/-! ## Part 5 — what the shapes force -/

/-- **EVERY VERTEX OF A FIVE-CYCLE OF A TRIANGLE-FREE GRAPH HAS EXACTLY TWO NEIGHBOURS INSIDE IT**
(round 152's `JSP90.card_neighIn_five_eq_two`, in the language of `AdjIn`). -/
theorem card_adjIn_D_eq_two {C D : Finset V}
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) (hD : IsOddCycle G D) (hD5 : D.card = 5)
    {x : V} (hx : x ∈ D) : (AdjIn G x D).card = 2 := by
  obtain ⟨m, g, hm, hm3, hginj, hgcyc, hmemD⟩ := hD
  have hD' : IsOddCycle G D := ⟨m, g, hm, hm3, hginj, hgcyc, hmemD⟩
  have hm5 : m = 5 := by
    have h := card_eq_cyclicOrder g hginj hmemD
    omega
  subst hm5
  obtain ⟨i, hi⟩ := hmemD x |>.mp hx
  rw [← hi]
  exact card_neighIn_five_eq_two hD' hD5 htf g hginj hgcyc hmemD i rfl

/-- **A FINSET OF CARDINALITY TWO CONTAINING TWO GIVEN POINTS IS THE PAIR OF THEM.** -/
lemma eq_pair_of_card_two {s : Finset V} {p q : V} (hcard : s.card = 2) (hp : p ∈ s) (hq : q ∈ s)
    (hpq : p ≠ q) : s = {p, q} := by
  have herase : s.erase p = {q} := by
    have hcard1 : (s.erase p).card = 1 := by
      have h1 := Finset.card_erase_add_one hp
      omega
    have hq' : q ∈ s.erase p := Finset.mem_erase_of_ne_of_mem (fun h => hpq h.symm) hq
    exact eq_singleton_of_card_eq_one_of_mem hcard1 hq'
  rw [← Finset.insert_erase hp, herase]

/-- **IN SHAPE A, THE NEIGHBOUR SET OF AN OUTSIDE VERTEX INSIDE `D` IS THE FAR ENDPOINT OF THE PATH
TOGETHER WITH THE OTHER OUTSIDE VERTEX.**  Concretely `AdjIn G w1 D = {c, w2}` and
`AdjIn G w2 D = {a, w1}`: round 152's degree lemma (`JSP90.card_adjIn_D_eq_two`) turns the two known
neighbours into the whole set. -/
theorem adjIn_D_pair_of_shapeA {C D : Finset V}
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) (hD : IsOddCycle G D) (hD5 : D.card = 5)
    {w1 w2 : V} (h : IsShapeA G C D w1 w2) :
    ∃ a b c : V, a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ w1 ∉ C ∧ w2 ∉ C ∧ w1 ≠ w2 ∧
      D = {a, b, c, w1, w2} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c w1 ∧ G.Adj w2 a ∧ G.Adj w1 w2 ∧
      AdjIn G w1 D = {c, w2} ∧ AdjIn G w2 D = {a, w1} := by
  obtain ⟨a, b, c, ha, hb, hc, hab', hbc', hac', hw1, hw2, hw, hDset, hab, hbc, hcw1, hw2a,
    hw1w2⟩ := h
  refine ⟨a, b, c, ha, hb, hc, hab', hbc', hac', hw1, hw2, hw, hDset, hab, hbc, hcw1, hw2a, hw1w2,
    ?_, ?_⟩
  · have hcard : (AdjIn G w1 D).card = 2 :=
      card_adjIn_D_eq_two hshort hC5 htf hD hD5 (by rw [hDset]; simp)
    have hne : c ≠ w2 := fun he => hw2 (he ▸ hc)
    have hcD : c ∈ D := by rw [hDset]; simp
    have hw2D : w2 ∈ D := by rw [hDset]; simp
    exact eq_pair_of_card_two hcard (mem_adjIn_of_adj hcD hcw1.symm)
      (mem_adjIn_of_adj hw2D hw1w2) hne
  · have hcard : (AdjIn G w2 D).card = 2 :=
      card_adjIn_D_eq_two hshort hC5 htf hD hD5 (by rw [hDset]; simp)
    have hne : a ≠ w1 := fun he => hw1 (he ▸ ha)
    have haD : a ∈ D := by rw [hDset]; simp
    have hw1D : w1 ∈ D := by rw [hDset]; simp
    exact eq_pair_of_card_two hcard (mem_adjIn_of_adj haD hw2a)
      (mem_adjIn_of_adj hw1D hw1w2.symm) hne

/-- **IN SHAPE B, THE NEIGHBOUR SET OF AN OUTSIDE VERTEX INSIDE `D` IS ITS TWO NEIGHBOURS IN THE
CYCLE.**  Concretely `AdjIn G w1 D = {a, c}` and `AdjIn G w2 D = {a, b}`. -/
theorem adjIn_D_pair_of_shapeB {C D : Finset V}
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) (hD : IsOddCycle G D) (hD5 : D.card = 5)
    {w1 w2 : V} (h : IsShapeB G C D w1 w2) :
    ∃ a b c : V, a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ w1 ∉ C ∧ w2 ∉ C ∧ w1 ≠ w2 ∧
      D = {a, b, c, w1, w2} ∧ G.Adj b c ∧ G.Adj a w1 ∧ G.Adj a w2 ∧ G.Adj b w2 ∧ G.Adj c w1 ∧
      AdjIn G w1 D = {a, c} ∧ AdjIn G w2 D = {a, b} := by
  obtain ⟨a, b, c, ha, hb, hc, hab', hbc', hac', hw1, hw2, hw, hDset, hbc, haw1, haw2, hbw2,
    hcw1⟩ := h
  refine ⟨a, b, c, ha, hb, hc, hab', hbc', hac', hw1, hw2, hw, hDset, hbc, haw1, haw2, hbw2, hcw1,
    ?_, ?_⟩
  · have hcard : (AdjIn G w1 D).card = 2 :=
      card_adjIn_D_eq_two hshort hC5 htf hD hD5 (by rw [hDset]; simp)
    have hne : a ≠ c := hac'
    have haD : a ∈ D := by rw [hDset]; simp
    have hcD : c ∈ D := by rw [hDset]; simp
    exact eq_pair_of_card_two hcard (mem_adjIn_of_adj haD haw1.symm)
      (mem_adjIn_of_adj hcD hcw1.symm) hne
  · have hcard : (AdjIn G w2 D).card = 2 :=
      card_adjIn_D_eq_two hshort hC5 htf hD hD5 (by rw [hDset]; simp)
    have hne : a ≠ b := hab'
    have haD : a ∈ D := by rw [hDset]; simp
    have hbD : b ∈ D := by rw [hDset]; simp
    exact eq_pair_of_card_two hcard (mem_adjIn_of_adj haD haw2.symm)
      (mem_adjIn_of_adj hbD hbw2.symm) hne

/-- **IN SHAPE A THE TWO OUTSIDE VERTICES HAVE NO COMMON NEIGHBOUR IN `C`**: a common neighbour would
close a triangle with the edge `w1 - w2` of `D`. -/
theorem disjoint_adjIn_C_of_shapeA {C D : Finset V} (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    {w1 w2 : V} (h : IsShapeA G C D w1 w2) : AdjIn G w1 C ∩ AdjIn G w2 C = ∅ := by
  rcases h with ⟨a, b, c, ha, hb, hc, hab', hbc', hac', hw1, hw2, hw, hD, hab, hbc, hcw1, hw2a,
    hw1w2⟩
  refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
  have hz1 := mem_adjIn.mp (Finset.mem_inter.mp hz).1
  have hz2 := mem_adjIn.mp (Finset.mem_inter.mp hz).2
  exact no_triangle_of_not_isNClique htf hw1w2 hz1.2 hz2.2

/-- **IN SHAPE B THE TWO OUTSIDE VERTICES HAVE A COMMON NEIGHBOUR IN `C`** — namely `a`. -/
theorem inter_adjIn_C_ne_empty_of_shapeB {C D : Finset V} {w1 w2 : V} (h : IsShapeB G C D w1 w2) :
    AdjIn G w1 C ∩ AdjIn G w2 C ≠ ∅ := by
  rcases h with ⟨a, b, c, ha, hb, hc, hab', hbc', hac', hw1, hw2, hw, hD, hbc, haw1, haw2, hbw2,
    hcw1⟩
  refine fun hcontra => Finset.notMem_empty a
    (hcontra ▸ Finset.mem_inter.mpr ⟨mem_adjIn_of_adj ha haw1.symm, mem_adjIn_of_adj ha haw2.symm⟩)

end
end JSP90