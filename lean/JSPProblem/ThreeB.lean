import JSPProblem.ThreeRing

/-!
# JSP-000090, round 161 — `JSPProblem/ThreeB.lean`: **THE SHAPE-B HALF OF `JSP90.ThreeIntersectionFiveCycleUnique`**

Attack family 83.  This file executes the first of the two concrete bets of
`discovery/JSP-000090/policy.json` after round 160: the **shape-B half** of MISSING LEMMA 3,
"at most one five-cycle of `G` meets a shortest odd five-cycle `C` in exactly three points" at
`|V| ≤ 7`.

The header of `JSPProblem/ThreeRing.lean` announced a "Part 5" — the ring data of the shape B — but
the file as it stands stops at the machine-checked refutation of the singleton claim, and the
corresponding declarations (`RingShapeBData`, `exists_ringShapeB`,
`inter_adjIn_C_eq_singleton_of_ringShapeB`) do **not** exist anywhere in the development.  This round
proves them, and with them the whole shape-B half of the uniqueness statement.

## What is proved here (0 placeholders)

* **Part 0 — the finset bookkeeping.**  `JSP90.sdiff_eq_sdiff_triple`, `JSP90.mem_pair_eq`,
  `JSP90.inter_pair_pair_of_ne`, `JSP90.pair_comm_finset`.
* **Part 1 — `JSP90.RingShapeBData`, `JSP90.RingShapeB`, `JSP90.exists_ringShapeB`: THE RING DATA OF
  A SHAPE-B CYCLE.**  For `IsShapeB G C D w1 w2` and a cyclic numbering `g` of `C` in which the
  edge `b - c` of `D` starts the ring (`g 0 = b`):

  ```text
        g 4     g 0     g 1     g 2     g 3
        x ————— b ————— c ————— y ————— a
  ```

  the point `a` (the one of the three points of `C` which sees both outside vertices) is the point of
  `C` at ring distance **two** from the edge `b - c`, the missed pair of `D` is **the pair of ring
  neighbours of `a`**, and `a` is adjacent to **neither** `b` nor `c` (the two triangles
  `w1 a c` and `w2 a b` are excluded by triangle-freeness).  So:

  ```lean
  pos    : (c = g 1 ∧ a = g 3) ∨ (c = g 4 ∧ a = g 2)
  mid    : g 0 = b
  missed : ∃ j, a = g j ∧ C \ D = {g (cycSucc j), g (cycPred j)}
  ```
* **Part 2 — `JSP90.sdiff_D_eq_adjIn_C_of_ringShapeB`: THE MISSED PAIR OF THE SHAPE B IS THE
  NEIGHBOUR SET OF THE SINGLE POINT `a` INSIDE `C`.**

  ```lean
  C \ D = AdjIn G a C
  ```

  (`JSP90.filter_adj_C_eq_ringPair` at the position of `a`.)  Together with Part 3 this is the whole
  input of the uniqueness argument: **the missed pair determines `a`**.
* **Part 3 — `JSP90.card_adjIn_C_le_two`, `JSP90.adjIn_C_pair_of_ringShapeB`,
  `JSP90.inter_adjIn_C_eq_singleton_of_ringShapeB`: THE COMMON NEIGHBOUR OF THE TWO OUTSIDE POINTS
  IS THE SINGLE POINT `a`.**

  ```lean
  (AdjIn G x C).card ≤ 2      -- every outside vertex, JSPProblem/Fan.lean
  AdjIn G w1 C = {a, c}   ∧   AdjIn G w2 C = {a, b}   ∧   AdjIn G w1 C ∩ AdjIn G w2 C = {a}
  ```
* **Part 4 — `JSP90.eq_of_sdiff_eq_of_card_le_seven`: AT `|V| ≤ 7` A THREE-INTERSECTION FIVE-CYCLE IS
  DETERMINED BY ITS MISSED PAIR.**  So MISSING LEMMA 3 is exactly the statement that *at most one of
  the ten candidate pairs is realised*.
* **Part 5 — `JSP90.shapeB_unique`: THE SHAPE-B HALF OF `JSP90.ThreeIntersectionFiveCycleUnique`,
  proved.**  At `|V| ≤ 7`, **two three-intersection five-cycles of the shape B with the same pair of
  outside vertices are equal**: they have the same `a` (Part 3), hence the same missed pair
  (Part 2), hence are equal (Part 4).
* **Part 6 — `JSP90.shapeA_shapeB_exclusive`: THE TWO SHAPES NEVER MIX OVER A FIXED OUTSIDE PAIR.**
  `AdjIn G w1 C ∩ AdjIn G w2 C` is empty for the shape A (round 159) and nonempty for the shape B.
  So the remaining case analysis of MISSING LEMMA 3 is the **shape-A half alone**.

## What is *not* proved

The **shape-A half** of `JSP90.ThreeIntersectionFiveCycleUnique`: at `|V| ≤ 7`, two
three-intersection five-cycles of shape A with the same pair of outside vertices are equal.  Round
160's `JSP90.adjIn_C_subset_of_shapeA` (the two candidate neighbour sets) is the input of that
case analysis; it is recorded in `discovery/JSP-000090/policy.json` as `next_bet`.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]`.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 4000000

/- Several lemmas below keep hypotheses they do not need (`hC5` in `card_adjIn_C_le_two`, `hC` in
`adjIn_C_pair_of_ringShapeB`, the ring data of the existential in `exists_ringShapeB`): they record
the setting of the ring lemmas they are instances of, and they are part of the interface the later
lemmas pass along. -/
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

local instance thDecidableAdjRel4 (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

local instance thDecidableEq4 : DecidableEq V := Classical.decEq V

/-! ## Part 0 — the finset bookkeeping shared with round 160 -/

/-- **THE MISSED PART OF `C` IS THE MISSED PART OF THE TRIPLE OF INSIDE POINTS.**  With
`C ∩ D = {a, b, c}` the points of `C` which `D` does not use are exactly the points of `C` outside
that triple. -/
lemma sdiff_eq_sdiff_triple {C D : Finset V} {a b c : V} (hinter : C ∩ D = {a, b, c}) :
    C \ D = C \ {a, b, c} := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_sdiff]
    exact ⟨hx.1, fun hx3 => hx.2 ((Finset.mem_inter.mp (mem_of_mem_congr' hinter hx3)).2)⟩
  · intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_sdiff]
    exact ⟨hx.1, fun hxD => hx.2 (mem_of_mem_congr hinter (Finset.mem_inter.mpr ⟨hx.1, hxD⟩))⟩

/-- **A POINT OF A TWO-ELEMENT SET IS ONE OF THE TWO.** -/
lemma mem_pair_eq {a b x : V} : x ∈ ({a, b} : Finset V) ↔ x = a ∨ x = b := by
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact Or.inl hx
    · rcases Finset.mem_singleton.mp hx with hx
      exact Or.inr hx
  · intro hx
    rcases hx with hx | hx
    · rw [hx]; exact Finset.mem_insert.mpr (Or.inl rfl)
    · rw [hx]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))

/-- **TWO TWO-ELEMENT SETS WITH ONE COMMON ELEMENT INTERSECT IN THE SINGLETON OF THAT ELEMENT.** -/
lemma inter_pair_pair_of_ne {a b c : V} (hcb : c ≠ b) :
    ({a, c} : Finset V) ∩ ({a, b} : Finset V) = {a} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · intro hx
    rcases mem_pair_eq.mp hx.1 with h1 | h1 <;> rcases mem_pair_eq.mp hx.2 with h2 | h2
    · exact h1
    · exact h1
    · exact h2
    · exact absurd (h1.symm.trans h2) hcb
  · intro hx
    exact ⟨mem_pair_eq.mpr (Or.inl hx), mem_pair_eq.mpr (Or.inl hx)⟩

/-- **A TWO-ELEMENT SET DOES NOT DEPEND ON THE ORDER OF ITS TWO ELEMENTS.** -/
lemma pair_comm_finset {a b : V} : ({a, b} : Finset V) = {b, a} := Finset.insert_comm a b ∅

/-! ## Part 1 — the ring data of the shape B -/

/-- **THE RING DATA OF A THREE-INTERSECTION FIVE-CYCLE OF THE SHAPE B.**

`D` is a three-intersection five-cycle of the shape B of `JSPProblem/Three.lean`, seen through a
cyclic numbering `g` of `C` in which the edge `b - c` of `D` starts the ring (`g 0 = b`):

```text
        g 4     g 0     g 1     g 2     g 3
        x ————— b ————— c ————— y ————— a
```

`a` is the point of the three points of `C` which sees **both** outside vertices `w1`, `w2`.  It is
the point of `C` at ring distance two from the edge `b - c`, the missed pair of `D` is **the pair of
ring-neighbours of `a`**, and `a` is adjacent to neither `b` nor `c` — the two triangles
`w1 - a - c` and `w2 - a - b` are excluded by triangle-freeness, and each of `b`, `c` is a
ring-neighbour of a *candidate* for `a`, which is exactly what forces `a = g 3`. -/
structure RingShapeBData (G : SimpleGraph V) (C D : Finset V) (g : Fin 5 → V) (w1 w2 a b c : V) :
    Prop where
  /-- **THE TWO ORIENTATIONS OF THE EDGE `b - c` IN THE RING.** -/
  pos : (c = g 1 ∧ a = g 3) ∨ (c = g 4 ∧ a = g 2)
  /-- **THE EDGE `b - c` STARTS THE RING.** -/
  mid : g 0 = b
  /-- **THE THREE INSIDE POINTS ARE DISTINCT POINTS OF `C`, THE TWO OUTSIDE POINTS ARE NOT.** -/
  distinct : a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ w1 ∉ C ∧ w2 ∉ C ∧ w1 ≠ w2 ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c
  /-- **`D` IS THE FIVE POINTS, AND THE FIVE ADJACENCIES OF THE SHAPE B HOLD.** -/
  shape : D = {a, b, c, w1, w2} ∧ G.Adj b c ∧ G.Adj a w1 ∧ G.Adj a w2 ∧ G.Adj b w2 ∧ G.Adj c w1
  /-- **`a` IS ADJACENT TO NEITHER `b` NOR `c`**: the triangles `w2 - a - b` and `w1 - a - c`. -/
  notab : ¬ G.Adj a b ∧ ¬ G.Adj a c
  /-- **THE MISSED PAIR OF `D` IS THE PAIR OF RING-NEIGHBOURS OF `a`.** -/
  missed : ∃ j : Fin 5, a = g j ∧ C \ D = {g (cycSucc j), g (cycPred j)}

/-- **A RING NUMBERING WITNESSES THE SHAPE-B DATA OF SOME FIVE-CYCLE.** -/
def RingShapeB (G : SimpleGraph V) (C D : Finset V) (g : Fin 5 → V) (w1 w2 : V) : Prop :=
  ∃ a b c : V, RingShapeBData G C D g w1 w2 a b c

/-- **A SHAPE-B FIVE-CYCLE HAS A RING NUMBERING WITNESSING `RingShapeB`.**

This is `JSP90.exists_shape` of round 159 with the ring positions made explicit: **the missed pair of
a three-intersection five-cycle of shape B is the pair of ring-neighbours of the single point `a` of
`C` which sees both outside vertices**, and `a` is at ring distance two from the unique edge of `D`
inside `C`.  This is the shape-B counterpart of round 160's `JSP90.exists_ringShapeA`. -/
theorem exists_ringShapeB {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) {w1 w2 : V} (h : IsShapeB G C D w1 w2) :
    ∃ (g : Fin 5 → V) (hg : Function.Injective g) (hcycg : ∀ k : Fin 5, G.Adj (g k) (g (cycSucc k)))
      (hmemg : ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, g k = y), RingShapeB G C D g w1 w2 := by
  obtain ⟨a, b, c, ha, hb, hc, habne, hbcne, hacne, hw1, hw2, hw, hDset, hbc, haw1, haw2, hbw2,
    hcw1⟩ := h
  -- the two triangles of the shape B: `w2 - a - b` and `w1 - a - c`
  have habadj : ¬ G.Adj a b :=
    fun hh => no_triangle_of_not_isNClique (a := w2) (b := a) (c := b) htf haw2.symm hbw2.symm hh
  have hacadj : ¬ G.Adj a c :=
    fun hh => no_triangle_of_not_isNClique (a := w1) (b := a) (c := c) htf haw1.symm hcw1.symm hh
  -- the ring of `C`, re-numbered so that `b` is the point `g 0`
  obtain ⟨i, hi⟩ := hmem b |>.mp hb
  set g : Fin 5 → V := ringShift f i with hgdef
  have hg : Function.Injective g := ringShift_inj hf i
  have hcycg : ∀ k : Fin 5, G.Adj (g k) (g (cycSucc k)) := ringShift_adj hcyc i
  have hmemg : ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, g k = y := ringShift_mem hmem i
  have hne : ∀ (k l : Fin 5), k ≠ l → g k ≠ g l := fun k l hkl => five_f_ne hg hkl
  have hg0 : g 0 = b := by
    have h1 : g 0 = f i := rfl
    rw [h1]
    exact hi
  -- the ring adjacencies, read off as literals
  have hs0 : (cycSucc 0 : Fin 5) = 1 := by decide
  have hs1 : (cycSucc 1 : Fin 5) = 2 := by decide
  have hs3 : (cycSucc 3 : Fin 5) = 4 := by decide
  have hs4 : (cycSucc 4 : Fin 5) = 0 := by decide
  have h01 : G.Adj (g 0) (g 1) := by simpa only [hs0] using hcycg 0
  have h12 : G.Adj (g 1) (g 2) := by simpa only [hs1] using hcycg 1
  have h34 : G.Adj (g 3) (g 4) := by simpa only [hs3] using hcycg 3
  have h40 : G.Adj (g 4) (g 0) := by simpa only [hs4] using hcycg 4
  -- `c` is one of the two ring-neighbours of `b`
  have hcpos : c = g 1 ∨ c = g 4 := by
    have h1 := filter_adj_C_eq_ringPair hC hshort hC5 f hf hcyc hmem i
    have hc' : c ∈ AdjIn G b C := mem_adjIn_of_adj hc hbc
    rw [AdjIn, ← hi] at hc'
    rw [h1] at hc'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h | h
    · left
      rw [hgdef, ringShift]
      have h3 := five_iterate_one i
      show c = f ((cycSucc^[1] : Fin 5 → Fin 5) i)
      rw [h3]
      exact h
    · right
      rw [hgdef, ringShift]
      have h3 := five_iterate_four i
      show c = f ((cycSucc^[4] : Fin 5 → Fin 5) i)
      rw [h3, ← cycPred_five]
      exact h
  -- `C ∩ D` is the triple `{a, b, c}`, and `C \ D = C \ {a, b, c}`
  have hinter : C ∩ D = {a, b, c} :=
    inter_D_eq_triple hDset ha hb hc hw1 hw2 hw habne hbcne hacne
  have hsdiff : C \ D = C \ {a, b, c} := sdiff_eq_sdiff_triple hinter
  rcases hcpos with hcposL | hcposR
  · -- the orientation `b = g 0`, `c = g 1`, `a = g 3`, the missed pair `{g 2, g 4}`
    have ha3 : a = g 3 := by
      rcases mem_ring_rest hmemg ha (fun h => habne (hg0 ▸ h)) (fun h => hacne (hcposL ▸ h))
        (fun h => hacadj (h ▸ (hcposL ▸ h12.symm))) with h | h
      · exact h
      · exact absurd h (fun hh => habadj (h ▸ (hg0 ▸ h40)))
    have hmiss : C \ D = {g 2, g 4} := by
      rw [hsdiff, ha3, ← hg0, hcposL]
      exact sdiff_of_card (C := C) (S := {g 3, g 0, g 1}) (T := {g 2, g 4})
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_singleton] at hx
          rcases hx with h | h | h
          · exact mem_C_of_mem hmemg h
          · exact mem_C_of_mem hmemg h
          · exact mem_C_of_mem hmemg h)
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h
          · exact mem_C_of_mem hmemg h
          · exact mem_C_of_mem hmemg h)
        (fun x hx1 hx2 => by
          simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_singleton] at hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
          rcases hx1 with h | h | h <;> rcases hx2 with h2 | h2 <;>
            exact (hne _ _ (by decide)) (h ▸ h2))
        (card_three (hne 3 0 (by decide)) (hne 3 1 (by decide)) (hne 0 1 (by decide)))
        (card_pair (hne 2 4 (by decide)))
        hC5
    refine ⟨g, hg, hcycg, hmemg, a, b, c, ?_⟩
    refine ⟨Or.inl ⟨hcposL, ha3⟩, hg0, ?_, ?_, ?_, ⟨3, ha3, ?_⟩⟩
    · exact ⟨ha, hb, hc, hw1, hw2, hw, habne, hbcne, hacne⟩
    · exact ⟨hDset, hbc, haw1, haw2, hbw2, hcw1⟩
    · exact ⟨habadj, hacadj⟩
    · rw [← (show (cycSucc 3 : Fin 5) = 4 from hs3),
        ← (show (cycPred 3 : Fin 5) = 2 by decide)] at hmiss
      exact (pair_comm_finset (a := g (cycPred 3)) (b := g (cycSucc 3))) ▸ hmiss
  · -- the reversed orientation `b = g 0`, `c = g 4`, `a = g 2`, the missed pair `{g 1, g 3}`
    have ha2 : a = g 2 := by
      rcases mem_ring hmemg ha with h | h | h | h | h
      · exact absurd h (fun hh => habne (hg0 ▸ hh))
      · exact absurd h (fun hh => habadj ((h ▸ (hg0 ▸ h01)).symm))
      · exact h
      · exact absurd h (fun hh => hacadj (h ▸ (hcposR ▸ h34)))
      · exact absurd h (fun hh => hacne (hcposR ▸ hh))
    have hmiss : C \ D = {g 1, g 3} := by
      rw [hsdiff, ha2, ← hg0, hcposR]
      exact sdiff_of_card (C := C) (S := {g 2, g 0, g 4}) (T := {g 1, g 3})
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_singleton] at hx
          rcases hx with h | h | h
          · exact mem_C_of_mem hmemg h
          · exact mem_C_of_mem hmemg h
          · exact mem_C_of_mem hmemg h)
        (fun x hx => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h
          · exact mem_C_of_mem hmemg h
          · exact mem_C_of_mem hmemg h)
        (fun x hx1 hx2 => by
          simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
            Finset.mem_singleton] at hx1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
          rcases hx1 with h | h | h <;> rcases hx2 with h2 | h2 <;>
            exact (hne _ _ (by decide)) (h ▸ h2))
        (card_three (hne 2 0 (by decide)) (hne 2 4 (by decide)) (hne 0 4 (by decide)))
        (card_pair (hne 1 3 (by decide)))
        hC5
    refine ⟨g, hg, hcycg, hmemg, a, b, c, ?_⟩
    refine ⟨Or.inr ⟨hcposR, ha2⟩, hg0, ?_, ?_, ?_, ⟨2, ha2, ?_⟩⟩
    · exact ⟨ha, hb, hc, hw1, hw2, hw, habne, hbcne, hacne⟩
    · exact ⟨hDset, hbc, haw1, haw2, hbw2, hcw1⟩
    · exact ⟨habadj, hacadj⟩
    · rw [← (show (cycSucc 2 : Fin 5) = 3 by decide),
        ← (show (cycPred 2 : Fin 5) = 1 by decide)] at hmiss
      exact (pair_comm_finset (a := g (cycPred 2)) (b := g (cycSucc 2))) ▸ hmiss

/-! ## Part 2 — the missed pair of the shape B is the neighbour set of `a` inside `C` -/

/-- **IN THE SHAPE B, THE MISSED PAIR OF `D` IS `AdjIn G a C`: the two neighbours of the single point
of `C` which sees both outside vertices.**

This is the shape-B counterpart of `JSP90.exists_ringShapeA`, read together with round 152's
`JSP90.filter_adj_C_eq_ringPair`: the missed pair is a pair of *consecutive* points of `C`, and those
are exactly the neighbours of `a` inside `C`.  Hence **the missed pair determines `a`** (the ring
pair determines the point, `JSP90.neighIn_C_inj`), which is the whole input of the uniqueness proof
of Part 5. -/
theorem sdiff_D_eq_adjIn_C_of_ringShapeB {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    {g : Fin 5 → V} (hg : Function.Injective g) (hcycg : ∀ k : Fin 5, G.Adj (g k) (g (cycSucc k)))
    (hmemg : ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, g k = y)
    {w1 w2 a b c : V} (h : RingShapeBData G C D g w1 w2 a b c) : C \ D = AdjIn G a C := by
  obtain ⟨_, _, _, _, _, ⟨j, hja, hmiss⟩⟩ := h
  have hj := filter_adj_C_eq_ringPair hC hshort hC5 g hg hcycg hmemg j
  rw [hja, AdjIn, hj, hmiss]

/-! ## Part 3 — the common neighbour of the two outside vertices is the single point `a` -/

/-- **AN OUTSIDE VERTEX OF A SHORTEST ODD FIVE-CYCLE MEETS IT IN AT MOST TWO POINTS.**

`JSP90.card_inter_neigh_le_two` of `JSPProblem/Fan.lean` bounds the number of *positions* of the ring
which an outside vertex can see; this is the same statement for the neighbour set
`AdjIn G x C`, obtained by pulling the bound back through `g`.  It is the point-form of the fan
lemma, and it is what makes the two-element neighbour sets of Part 3 exact. -/
theorem card_adjIn_C_le_two {C : Finset V}
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    {g : Fin 5 → V} (hg : Function.Injective g) (hcycg : ∀ k : Fin 5, G.Adj (g k) (g (cycSucc k)))
    (hmemg : ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, g k = y) {x : V} (hxC : x ∉ C) :
    (AdjIn G x C).card ≤ 2 := by
  have hS : ∀ (S : Finset (Fin 5)), (∀ k ∈ S, G.Adj x (g k)) → S.card ≤ 2 :=
    card_inter_neigh_le_two (m := 5) hshort (by decide) (by omega) g hg hcycg hmemg hxC
  have hsub : AdjIn G x C
      ⊆ Finset.image g ((Finset.univ : Finset (Fin 5)).filter (fun k => G.Adj x (g k))) := by
    intro z hz
    have hz1 := mem_adjIn.mp hz
    obtain ⟨k, hzk⟩ := hmemg z |>.mp hz1.1
    refine Finset.mem_image.mpr ⟨k, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ k, hzk ▸ hz1.2⟩
    · exact hzk
  have hle := Finset.card_le_card hsub
  have h4 : (Finset.image g ((Finset.univ : Finset (Fin 5)).filter (fun k => G.Adj x (g k)))).card
      ≤ ((Finset.univ : Finset (Fin 5)).filter (fun k => G.Adj x (g k))).card := Finset.card_image_le
  have h2 := hS ((Finset.univ : Finset (Fin 5)).filter (fun k => G.Adj x (g k)))
    (fun k hk => (Finset.mem_filter.mp hk).2)
  have h3 : ((Finset.univ : Finset (Fin 5)).filter (fun k => G.Adj x (g k))).card ≤ 5 :=
    Finset.card_le_univ _
  omega

/-- **IN THE SHAPE B, THE NEIGHBOURS OF AN OUTSIDE VERTEX INSIDE `C` ARE THE POINT `a` WHICH SEES
BOTH OUTSIDE VERTICES AND THE FAR END OF THE EDGE `b - c`.**

`AdjIn G w1 C = {a, c}` and `AdjIn G w2 C = {a, b}`.  The upper bound of `2` is
`JSP90.card_adjIn_C_le_two` above; the lower bound is the two adjacencies of the shape B. -/
theorem adjIn_C_pair_of_ringShapeB {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    {g : Fin 5 → V} (hg : Function.Injective g) (hcycg : ∀ k : Fin 5, G.Adj (g k) (g (cycSucc k)))
    (hmemg : ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, g k = y)
    {w1 w2 a b c : V} (h : RingShapeBData G C D g w1 w2 a b c) :
    AdjIn G w1 C = {a, c} ∧ AdjIn G w2 C = {a, b} := by
  obtain ⟨_, _, hdist, hshape, _, _⟩ := h
  obtain ⟨ha, hb, hc, hw1, hw2, _, habne, hbcne, hacne⟩ := hdist
  obtain ⟨_, _, haw1, haw2, hbw2, hcw1⟩ := hshape
  have hb1 : (AdjIn G w1 C).card ≤ 2 := card_adjIn_C_le_two hshort hC5 hg hcycg hmemg hw1
  have hb2 : (AdjIn G w2 C).card ≤ 2 := card_adjIn_C_le_two hshort hC5 hg hcycg hmemg hw2
  have hsub1 : ({a, c} : Finset V) ⊆ AdjIn G w1 C := by
    intro x hx
    rcases mem_pair_eq.mp hx with h | h
    · exact h ▸ (mem_adjIn_of_adj ha haw1.symm)
    · exact h ▸ (mem_adjIn_of_adj hc hcw1.symm)
  have hsub2 : ({a, b} : Finset V) ⊆ AdjIn G w2 C := by
    intro x hx
    rcases mem_pair_eq.mp hx with h | h
    · exact h ▸ (mem_adjIn_of_adj ha haw2.symm)
    · exact h ▸ (mem_adjIn_of_adj hb hbw2.symm)
  have h2 : (AdjIn G w1 C).card = 2 := by
    have hle : ({a, c} : Finset V).card ≤ (AdjIn G w1 C).card := Finset.card_le_card hsub1
    rw [card_pair (a := a) (b := c) hacne] at hle
    omega
  have h2' : (AdjIn G w2 C).card = 2 := by
    have hle : ({a, b} : Finset V).card ≤ (AdjIn G w2 C).card := Finset.card_le_card hsub2
    rw [card_pair (a := a) (b := b) habne] at hle
    omega
  refine ⟨?_, ?_⟩
  · refine eq_pair_of_card_two h2 (mem_adjIn_of_adj ha haw1.symm)
      (mem_adjIn_of_adj hc hcw1.symm) ?_
    exact hacne
  · refine eq_pair_of_card_two h2' (mem_adjIn_of_adj ha haw2.symm)
      (mem_adjIn_of_adj hb hbw2.symm) ?_
    exact habne

/-- **IN THE SHAPE B, THE TWO OUTSIDE VERTICES HAVE *EXACTLY ONE* COMMON NEIGHBOUR INSIDE `C`, AND IT
IS `a`.**  The shape-B counterpart of round 159's `JSP90.disjoint_adjIn_C_of_shapeA`. -/
theorem inter_adjIn_C_eq_singleton_of_ringShapeB {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    {g : Fin 5 → V} (hg : Function.Injective g) (hcycg : ∀ k : Fin 5, G.Adj (g k) (g (cycSucc k)))
    (hmemg : ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, g k = y)
    {w1 w2 a b c : V} (h : RingShapeBData G C D g w1 w2 a b c) :
    AdjIn G w1 C ∩ AdjIn G w2 C = {a} := by
  obtain ⟨h1, h2⟩ := adjIn_C_pair_of_ringShapeB hC hshort hC5 hg hcycg hmemg h
  obtain ⟨_, _, hdist, _, _, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, hbcne, _⟩ := hdist
  rw [h1, h2]
  exact inter_pair_pair_of_ne hbcne.symm

/-! ## Part 4 — at `|V| ≤ 7` a three-intersection five-cycle is determined by its missed pair -/

/-- **AT `|V| ≤ 7`, TWO THREE-INTERSECTION FIVE-CYCLES WITH THE SAME MISSED PAIR ARE EQUAL.**

So `JSP90.ThreeIntersectionFiveCycleUnique` is exactly the statement that **at most one of the ten
candidate pairs of `C` is realised**; the local structure of rounds 152, 155, 159, 160 and 161
reduces the ten cases to the two shapes. -/
theorem eq_of_sdiff_eq_of_card_le_seven {C D D' : Finset V} (hC5 : C.card = 5) (hD5 : D.card = 5)
    (hD5' : D'.card = 5) (hi : (C ∩ D).card = 3) (hV : Fintype.card V ≤ 7)
    (hmiss : C \ D = C \ D') : D = D' := by
  have hinter : C ∩ D = C ∩ D' := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_inter]
      have hxn : x ∉ C \ D := fun h => absurd hx.2 (Finset.mem_sdiff.mp h).2
      refine ⟨hx.1, ?_⟩
      by_contra hnD
      have h1 : x ∉ C \ D' := fun hmem => hxn (mem_of_mem_congr' hmiss hmem)
      exact h1 (Finset.mem_sdiff.mpr ⟨hx.1, hnD⟩)
    · intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_inter]
      have hxn : x ∉ C \ D' := fun h => absurd hx.2 (Finset.mem_sdiff.mp h).2
      refine ⟨hx.1, ?_⟩
      by_contra hnD
      have h1 : x ∉ C \ D := fun hmem => hxn (mem_of_mem_congr hmiss hmem)
      exact h1 (Finset.mem_sdiff.mpr ⟨hx.1, hnD⟩)
  have hi' : (C ∩ D').card = 3 := by
    rw [← hinter]
    exact hi
  refine eq_of_inter_eq_of_diffC (by rw [Finset.inter_comm, hinter, Finset.inter_comm]) ?_
  exact (diffC_eq_univ_sdiff hC5 hD5 (by rw [Finset.inter_comm]; exact hi) hV).trans
    (diffC_eq_univ_sdiff hC5 hD5' (by rw [Finset.inter_comm]; exact hi') hV).symm

/-! ## Part 5 — THE SHAPE-B HALF OF `JSP90.ThreeIntersectionFiveCycleUnique` -/

/-- **AT `|V| ≤ 7` TWO THREE-INTERSECTION FIVE-CYCLES OF THE SHAPE B WITH THE SAME PAIR OF OUTSIDE
VERTICES ARE EQUAL.**

This is the **shape-B half of `JSP90.ThreeIntersectionFiveCycleUnique`**, proved.  The proof is the
chain of the reduction: both cycles have the same common neighbour `a` of the outside pair
(`JSP90.inter_adjIn_C_eq_singleton_of_ringShapeB`), hence the same missed pair
(`JSP90.sdiff_D_eq_adjIn_C_of_ringShapeB`), hence are equal
(`JSP90.eq_of_sdiff_eq_of_card_le_seven`, which is where `|V| ≤ 7` is used). -/
theorem shapeB_unique {C D D' : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) (hV : Fintype.card V ≤ 7)
    {g : Fin 5 → V} (hg : Function.Injective g) (hcycg : ∀ k : Fin 5, G.Adj (g k) (g (cycSucc k)))
    (hmemg : ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, g k = y)
    {w1 w2 : V} (h : IsShapeB G C D w1 w2) (h' : IsShapeB G C D' w1 w2) : D = D' := by
  obtain ⟨g', hg', hcycg', hmemg', a, b, c, hdata⟩ :=
    exists_ringShapeB hC hshort hC5 htf g hg hcycg hmemg h
  obtain ⟨g'', hg'', hcycg'', hmemg'', a', b', c', hdata'⟩ :=
    exists_ringShapeB hC hshort hC5 htf g hg hcycg hmemg h'
  -- the two common neighbours of the outside pair are equal
  have hinter_a : AdjIn G w1 C ∩ AdjIn G w2 C = {a} :=
    inter_adjIn_C_eq_singleton_of_ringShapeB hC hshort hC5 hg' hcycg' hmemg' hdata
  have hinter_a' : AdjIn G w1 C ∩ AdjIn G w2 C = {a'} :=
    inter_adjIn_C_eq_singleton_of_ringShapeB hC hshort hC5 hg'' hcycg'' hmemg'' hdata'
  have hmem1 : a ∈ AdjIn G w1 C ∩ AdjIn G w2 C := by
    rw [hinter_a]
    exact Finset.mem_singleton.mpr rfl
  have haa : a = a' := Finset.mem_singleton.mp (mem_of_mem_congr hinter_a' hmem1)
  -- hence the two missed pairs are equal
  have hmiss : C \ D = C \ D' := by
    rw [sdiff_D_eq_adjIn_C_of_ringShapeB hC hshort hC5 hg' hcycg' hmemg' hdata,
      sdiff_D_eq_adjIn_C_of_ringShapeB hC hshort hC5 hg'' hcycg'' hmemg'' hdata', haa]
  -- the cardinality of the first cycle, and its intersection with `C`
  obtain ⟨_, _, hdist, hshape, _, _⟩ := hdata
  obtain ⟨ha, hb, hc, hw1, hw2, hw, habne, hbcne, hacne⟩ := hdist
  obtain ⟨hDset, _, _, _, _, _⟩ := hshape
  obtain ⟨_, _, hdist', hshape', _, _⟩ := hdata'
  obtain ⟨ha', hb', hc', hw1', hw2', hw', habne', hbcne', hacne'⟩ := hdist'
  obtain ⟨hDset', _, _, _, _, _⟩ := hshape'
  have haw1 : a ≠ w1 := fun h => hw1 (h.symm ▸ ha)
  have haw2 : a ≠ w2 := fun h => hw2 (h.symm ▸ ha)
  have hbw1 : b ≠ w1 := fun h => hw1 (h.symm ▸ hb)
  have hbw2 : b ≠ w2 := fun h => hw2 (h.symm ▸ hb)
  have hcw1 : c ≠ w1 := fun h => hw1 (h.symm ▸ hc)
  have hcw2 : c ≠ w2 := fun h => hw2 (h.symm ▸ hc)
  have hD5 : D.card = 5 := by
    rw [hDset]
    simp [Finset.card_insert_of_notMem, habne, hacne, haw1, haw2, hbcne, hbw1, hbw2, hcw1, hcw2,
      hw]
  have haw1' : a' ≠ w1 := fun h => hw1' (h.symm ▸ ha')
  have haw2' : a' ≠ w2 := fun h => hw2' (h.symm ▸ ha')
  have hbw1' : b' ≠ w1 := fun h => hw1' (h.symm ▸ hb')
  have hbw2' : b' ≠ w2 := fun h => hw2' (h.symm ▸ hb')
  have hcw1' : c' ≠ w1 := fun h => hw1' (h.symm ▸ hc')
  have hcw2' : c' ≠ w2 := fun h => hw2' (h.symm ▸ hc')
  have hD5' : D'.card = 5 := by
    rw [hDset']
    simp [Finset.card_insert_of_notMem, habne', hacne', haw1', haw2', hbcne', hbw1', hbw2',
      hcw1', hcw2', hw']
  have hi : (C ∩ D).card = 3 := by
    rw [inter_D_eq_triple hDset ha hb hc hw1 hw2 hw habne hbcne hacne]
    exact card_three habne hacne hbcne
  exact eq_of_sdiff_eq_of_card_le_seven hC5 hD5 hD5' hi hV hmiss

/-! ## Part 6 — the two shapes never mix over a fixed pair of outside vertices -/

/-- **OVER A FIXED PAIR OF OUTSIDE VERTICES THE TWO SHAPES ARE MUTUALLY EXCLUSIVE.**

The shape A forces `AdjIn G w1 C ∩ AdjIn G w2 C = ∅` (round 159: a common neighbour would close a
triangle with the edge `w1 - w2` of `D`) and the shape B forces the same set to be a singleton
(`JSP90.inter_adjIn_C_eq_singleton_of_ringShapeB`).  So the two cases of MISSING LEMMA 3 never
interact: the remaining case analysis is the shape-A half alone. -/
theorem shapeA_shapeB_exclusive {C D : Finset V} (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hC5 : C.card = 5) {g : Fin 5 → V} (hg : Function.Injective g)
    (hcycg : ∀ k : Fin 5, G.Adj (g k) (g (cycSucc k)))
    (hmemg : ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, g k = y) {w1 w2 : V}
    (hA : IsShapeA G C D w1 w2) (hB : IsShapeB G C D w1 w2) : False := by
  obtain ⟨g', hg', hcycg', hmemg', a, b, c, hdata⟩ :=
    exists_ringShapeB hC hshort hC5 htf g hg hcycg hmemg hB
  have hne : AdjIn G w1 C ∩ AdjIn G w2 C = ∅ := disjoint_adjIn_C_of_shapeA htf hA
  exact absurd hne (inter_adjIn_C_ne_empty_of_shapeB hB)

end
end JSP90