import JSPProblem.Three

/-!
# JSP-000090, round 160 — `JSPProblem/ThreeRing.lean`: **THE RING POSITIONS OF THE TWO SHAPES**

Attack family 82.  This file takes the concrete next bet of `discovery/JSP-000090/policy.json`
after round 159 — *MISSING LEMMA 3a, "in shape A the neighbour sets `AdjIn G w1 C` and
`AdjIn G w2 C` are singletons"* — shows, machine-checkably, that **that statement is false**, and
proves the correct replacement: the **ring positions** of the points of a three-intersection
five-cycle, which is the data any uniqueness proof has to read off.

## What is proved here (0 placeholders)

* **Part 0 — five points in cycle order.**  `JSP90.cyc5V`, `JSP90.cyc5V_inj`,
  `JSP90.isOddCycle_of_cyc5V`: five pairwise distinct vertices with the five adjacencies in cyclic
  order are an `IsOddCycle` of the five-element set they span (the construction of
  `JSPProblem/Petersen.lean`'s `isOddCycle_delete_cyc5`, at an arbitrary vertex type).
* **Part 1 — the ring arithmetic and the ring positions.**  `JSP90.five_iterate_eq`,
  `JSP90.cycPred_five`, `JSP90.cycPred_three`, `JSP90.five_step_ne`, `JSP90.mem_ring` (a point of `C`
  is one of the five points of the ring), `JSP90.two_neigh_ring` (two distinct neighbours of a point
  of `C` are its two ring-neighbours: the converse direction of round 152's `filter_adj_C_eq_ringPair`),
  `JSP90.path3_ring` (**three points of `C` with `G.Adj a b`, `G.Adj b c`, `a ≠ c` are three
  consecutive points of the ring**), and `JSP90.sdiff_of_card`, `JSP90.card_three`, `JSP90.card_pair`
  (the finset bookkeeping).
* **Part 1 bis — `JSP90.ringShift`: THE RING RE-NUMBERED.**  Every proof below reads positions in the
  ring; `ringShift f j` numbers the ring with `j` as `0`, and then the positions are the *literals*
  `g 0 … g 4`, so that every ring inequality is a `decide` and every ring adjacency a `hcycg` /
  `adj_ringPred` instance.  `ringShift_inj`, `ringShift_adj`, `ringShift_mem` transport injectivity,
  the cyclic adjacency and the membership of the ring across the re-numbering.
* **Part 2 — `JSP90.RingShapeA`, `JSP90.exists_ringShapeA`: THE MISSED PAIR OF A SHAPE-A CYCLE.**
  For `IsShapeA G C D w1 w2` and a cyclic numbering `g` of `C` in which the **middle of the path**
  `a - b - c` is `g 0`:

  ```text
        g 4     g 0     g 1     g 2     g 3
        a ————— b ————— c ————— e ————— d
        |                                    |
        └————————————————————————————————————┘
  ```

  with `w1 ~ c`, `w2 ~ a`, `w1 ~ w2`, and `C \ D = {d, e}`, `G.Adj d e`, **`G.Adj a d`**,
  **`G.Adj c e`**: the missed pair is an **edge** of `C`, the one opposite to the middle of the path,
  and its two points are the ring-neighbours of `a` and of `c` respectively.
* **Part 3 — `JSP90.adjIn_C_subset_of_shapeA`: THE CANDIDATE NEIGHBOUR SETS — the corrected MISSING
  LEMMA 3a.**

  ```lean
  AdjIn G w1 C ⊆ {c, d}   ∧   AdjIn G w2 C ⊆ {a, e}
  ```

  The neighbours of the two outside vertices inside `C` are confined to **two** candidates each, not
  one; the second candidate `d` is exactly the missed point adjacent to `a`.  `JSP90.not_singleton_A`
  is the machine-checked **refutation** of the statement `policy.json` was betting on.
* **Part 4 — what the second candidate means.**  `JSP90.four_intersection_of_shapeA`: if the second
  candidate really occurs (`d ∈ AdjIn G w1 C`), then `w1 - d - a - b - c - w1` is a **four-
  intersection five-cycle** of `G`.  So `e` is always missed (by `D`) while `d` is missed only when
  the extra adjacencies are absent: the two candidates are not symmetric.
* **Part 5 — `JSP90.RingShapeB`, `JSP90.exists_ringShapeB`: THE MISSED PAIR OF A SHAPE-B CYCLE IS
  `AdjIn G a C`.**  For `IsShapeB G C D w1 w2` the three points are `b = g 0`, `c = g 1`,
  `a = g 3` — `a` is the point of the three adjacent to neither `b` nor `c`, because the triangles
  `w1 a c` and `w2 a b` are excluded — the missed pair is the pair at cyclic distance two, and
  **`C \ D = AdjIn G a C`**: the missed pair is determined by the single point `a`, which moreover is
  the **unique** common neighbour of `w1` and `w2` inside `C`
  (`JSP90.inter_adjIn_C_eq_singleton_of_shapeB`).

## The measurement behind the correction (`discovery/JSP-000090/r160.c`, output `r160.log`)

A complete search over all `2^16` graphs on seven vertices with `C` fixed as the five-cycle
`0-1-2-3-4-0` (`202` triangle-free graphs):

| quantity | value |
| --- | --- |
| `max # {D : \|D ∩ C\| = 3}` | **1** (MISSING LEMMA 3 holds at `\|V\| ≤ 7`) |
| `max` number of points of `C` missed by such a `D` | **2** (so *three* points of `C` are transversals) |
| shape A, `(\|N_C(w₁)\|, \|N_C(w₂)\|)` | `(1,1): 10`, `(1,2): 10`, `(2,1): 10`, `(2,2): 10` |
| shape B, `(\|N_C(w₁)\|, \|N_C(w₂)\|)` | `(2,2): 10` |

So **the singleton claim is false for shape A** — all four combinations occur — while shape B always
has exactly two neighbours per outside vertex.  The census also checks, with `0` violations in
`20 + 20` instances, that in shape A the second neighbour of `w1` is the missed point `d` adjacent to
`a` (Part 4), and in all `10` shape-B instances that the missed pair is the two ring-neighbours of `a`
(Part 5).

## What is *not* proved

`JSP90.ThreeIntersectionFiveCycleUnique` itself.  Part 5 reduces its shape-B half to the injectivity of
`c ↦ AdjIn G c C` on the common neighbourhood of the two outside vertices, and Part 3 its shape-A half
to the exclusion of a second shape-A cycle; the remaining case analysis is named at the end of this
file and in `discovery/JSP-000090/policy.json`.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]`.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 4000000

local instance thDecidableAdjRel3 (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

local instance thDecidableEq3 : DecidableEq V := Classical.decEq V

/-! ### The ring, as iterates of the cyclic successor -/

/-- **TWO NUMBERS OF STEPS AROUND A FIVE-CYCLE THAT AGREE MODULO FIVE GIVE THE SAME POINT.** -/
lemma five_iterate_eq (j : Fin 5) {m n : ℕ} (h : m % 5 = n % 5) :
    (cycSucc^[m] : Fin 5 → Fin 5) j = (cycSucc^[n] : Fin 5 → Fin 5) j := by
  refine Fin.ext ?_
  have h1 := cycSucc_pow_val (n := 5) m j
  have h2 := cycSucc_pow_val (n := 5) n j
  simp only [h1, h2]
  have hj := j.2
  omega

/-- **FOUR STEPS AROUND THE RING OF A FIVE-CYCLE ARE ONE STEP BACK.** -/
lemma cycPred_five (j : Fin 5) : (cycPred j : Fin 5) = cycSucc (cycSucc (cycSucc (cycSucc j))) := by
  show (cycSucc^[5 - 1] : Fin 5 → Fin 5) j = _ -- the four steps
  rw [five_iterate_four]

/-- **THREE STEPS BACK AROUND THE RING OF A FIVE-CYCLE ARE TWO STEPS FORWARD.** -/
lemma cycPred_three (j : Fin 5) : cycPred (cycPred (cycPred j)) = cycSucc (cycSucc j) := by
  have h : cycPred (cycPred (cycPred j)) = ((cycSucc^[4 + 4 + 4] : Fin 5 → Fin 5) j) := by
    show ((cycSucc^[4] : Fin 5 → Fin 5) ((cycSucc^[4]) ((cycSucc^[4]) j))) = _
    rw [Function.iterate_add_apply, Function.iterate_add_apply]
  have h2 : ((cycSucc^[2] : Fin 5 → Fin 5) j) = cycSucc (cycSucc j) := five_iterate_two j
  rw [h, ← h2]
  exact five_iterate_eq (m := 4 + 4 + 4) (n := 2) j (by omega)

/-- **TWO DIFFERENT NUMBERS OF STEPS AROUND THE RING GIVE TWO DIFFERENT POINTS.** -/
lemma five_step_ne (j : Fin 5) {k l : ℕ} (hk : k < 5) (hl : l < 5) (hkl : k ≠ l) :
    (cycSucc^[k] : Fin 5 → Fin 5) j ≠ (cycSucc^[l] : Fin 5 → Fin 5) j := by
  intro h
  have hv := congrArg Fin.val h
  have h1 := cycSucc_pow_val (n := 5) k j
  have h2 := cycSucc_pow_val (n := 5) l j
  simp only [h1, h2] at hv
  have hj := j.2
  omega

/-- **TWO DISTINCT POINTS OF THE RING HAVE DISTINCT IMAGES.** -/
lemma five_f_ne {f : Fin 5 → V} (hf : Function.Injective f) {k l : Fin 5} (hkl : k ≠ l) :
    f k ≠ f l := fun he => hkl (hf he)

/-- **THE THREE POINTS NEITHER OF WHICH IS THE STARTING POINT NOR ONE OF ITS TWO SUCCESSORS.** -/
lemma five_mem_rest (j : Fin 5) :
    ∀ k : Fin 5, k ≠ j → k ≠ cycSucc j → k ≠ cycSucc (cycSucc j) →
      k = cycSucc (cycSucc (cycSucc j)) ∨ k = cycSucc (cycSucc (cycSucc (cycSucc j))) := by
  intro k h1 h2 h3
  rcases five_iterate_mem j k h1 h2 with h | h | h
  · exact absurd h.symm h3
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-! ## Part 0 — five points in cycle order are an odd cycle -/

/-- **FIVE NAMED POINTS IN CYCLE ORDER.** -/
def cyc5V (a b c d e : V) : Fin 5 → V := fun j =>
  match j.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | _ => e

theorem cyc5V_inj {a b c d e : V} (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
    c ≠ d ∧ c ≠ e ∧ d ≠ e) : Function.Injective (cyc5V a b c d e) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp only [cyc5V] at hxy ⊢ <;> simp_all

/-- **FIVE PAIRWISE DISTINCT POINTS WITH THE FIVE ADJACENCIES IN CYCLIC ORDER ARE AN ODD CYCLE OF
THE FIVE-ELEMENT SET THEY SPAN.** -/
theorem isOddCycle_of_cyc5V {a b c d e : V} (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧
    b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e) (h1 : G.Adj a b) (h2 : G.Adj b c) (h3 : G.Adj c d)
    (h4 : G.Adj d e) (h5 : G.Adj e a) : IsOddCycle G ({a, b, c, d, e} : Finset V) := by
  refine ⟨5, cyc5V a b c d e, by decide, by decide, cyc5V_inj h, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp only [cyc5V] <;> assumption
  · intro y
    constructor
    · intro hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨0, by omega⟩, by simp [cyc5V]⟩
      · exact ⟨⟨1, by omega⟩, by simp [cyc5V]⟩
      · exact ⟨⟨2, by omega⟩, by simp [cyc5V]⟩
      · exact ⟨⟨3, by omega⟩, by simp [cyc5V]⟩
      · exact ⟨⟨4, by omega⟩, by simp [cyc5V]⟩
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [cyc5V]

/-- **THE CARDINALITY OF THE QUADRUPLE OF FOUR DISTINCT POINTS.** -/
lemma card_four {x y z t : V} (h : x ≠ y ∧ x ≠ z ∧ x ≠ t ∧ y ≠ z ∧ y ≠ t ∧ z ≠ t) :
    ({x, y, z, t} : Finset V).card = 4 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp [h1, h2, h3, h4, h5, h6]

/-- **THE CARDINALITY OF THE TRIPLE OF THREE DISTINCT POINTS.** -/
lemma card_three {x y z : V} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) : ({x, y, z} : Finset V).card = 3 := by
  have hx : x ∉ ({y, z} : Finset V) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim h1 h2
  rw [Finset.card_insert_of_notMem hx]
  have hy : y ∉ ({z} : Finset V) := by rw [Finset.mem_singleton]; exact h3
  rw [Finset.card_insert_of_notMem hy]
  simp

/-- **THE CARDINALITY OF THE PAIR OF TWO DISTINCT POINTS.** -/
lemma card_pair (hne : a ≠ b) : ({a, b} : Finset V).card = 2 := by
  have hn : a ∉ ({b} : Finset V) := by rw [Finset.mem_singleton]; exact hne
  rw [Finset.card_insert_of_notMem hn]
  simp

/-- **A THREE-ELEMENT SUBSET OF A FIVE-ELEMENT SET, TOGETHER WITH THE PAIR OF THE REMAINING TWO
POINTS, SPLITS THE FIVE-ELEMENT SET.** -/
theorem sdiff_of_card {C S T : Finset V} (hS : S ⊆ C) (hT : T ⊆ C)
    (hdisj : ∀ x : V, x ∈ S → x ∈ T → False) (hcardS : S.card = 3) (hcardT : T.card = 2)
    (hcardC : C.card = 5) : C \ S = T := by
  have hsub : T ⊆ C \ S := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hT hx, fun hxs => hdisj x hxs hx⟩
  have hcard : (C \ S).card = 2 := by
    rw [Finset.card_sdiff_of_subset hS]
    omega
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- **A POINT OF THE RING IS IN `C`** — the `hmemg` of a re-numbered ring, read off one position. -/
lemma mem_C_of_mem {C : Finset V} {g : Fin 5 → V} (hmemg : ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, g k = y)
    {x : V} {k : Fin 5} (hx : x = g k) : x ∈ C := by
  subst hx
  exact hmemg (g k) |>.mpr ⟨k, rfl⟩

/-- **MEMBERSHIP TRANSFERRED ALONG AN EQUALITY OF FINSETS.** -/
lemma mem_of_mem_congr {x : V} {s t : Finset V} (h : s = t) (hx : x ∈ s) : x ∈ t := by
  rw [← h]; exact hx

/-- **MEMBERSHIP TRANSFERRED BACK ALONG AN EQUALITY OF FINSETS.** -/
lemma mem_of_mem_congr' {x : V} {s t : Finset V} (h : s = t) (hx : x ∈ t) : x ∈ s := by
  rw [h]; exact hx

/-! ## Part 1 — the ring positions of the points of `C` -/

/-- **A POINT OF `C` IS ONE OF THE FIVE POINTS OF THE RING.** -/
lemma mem_ring {C : Finset V} {f : Fin 5 → V} (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y)
    {j : Fin 5} {y : V} (hy : y ∈ C) :
    y = f j ∨ y = f (cycSucc j) ∨ y = f (cycSucc (cycSucc j)) ∨
      y = f (cycSucc (cycSucc (cycSucc j))) ∨ y = f (cycSucc (cycSucc (cycSucc (cycSucc j)))) := by
  obtain ⟨i, hi⟩ := hmem y |>.mp hy
  have hi' : i ∈ ({j, cycSucc j, cycSucc (cycSucc j), cycSucc (cycSucc (cycSucc j)),
      cycSucc (cycSucc (cycSucc (cycSucc j)))} : Finset (Fin 5)) := by
    rw [← five_univ_eq_iter]
    exact Finset.mem_univ i
  rcases Finset.mem_insert.mp hi' with h | h
  · exact Or.inl (hi.symm.trans (congrArg f h))
  · rcases Finset.mem_insert.mp h with h | h
    · exact Or.inr (Or.inl (hi.symm.trans (congrArg f h)))
    · rcases Finset.mem_insert.mp h with h | h
      · exact Or.inr (Or.inr (Or.inl (hi.symm.trans (congrArg f h))))
      · rcases Finset.mem_insert.mp h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl (hi.symm.trans (congrArg f h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (hi.symm.trans (congrArg f (Finset.mem_singleton.mp h))))))

/-- **A POINT OF THE RING WHICH IS NONE OF THE THREE GIVEN ONES IS ONE OF THE OTHER TWO.** -/
lemma mem_ring_rest {C : Finset V} {f : Fin 5 → V} (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y)
    {j : Fin 5} {y : V} (hy : y ∈ C) (h1 : y ≠ f j) (h2 : y ≠ f (cycSucc j))
    (h3 : y ≠ f (cycSucc (cycSucc j))) :
    y = f (cycSucc (cycSucc (cycSucc j))) ∨ y = f (cycSucc (cycSucc (cycSucc (cycSucc j)))) := by
  rcases mem_ring hmem hy with h | h | h | h | h
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact Or.inl h
  · exact Or.inr h

/-- **THE TWO NEIGHBOURS OF A POINT OF `C` ARE ITS TWO RING-NEIGHBOURS** — the converse direction of
round 152's `filter_adj_C_eq_ringPair`: two *distinct* neighbours `a`, `c` of `b` inside `C` are
`f (cycSucc j)` and `f (cycPred j)`, where `b = f j`. -/
theorem two_neigh_ring {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) {b a c : V} (hb : b ∈ C) (ha : a ∈ C)
    (hc : c ∈ C) (hab : G.Adj a b) (hcb : G.Adj c b) (hac : a ≠ c) :
    ∃ j : Fin 5, b = f j ∧
      ((a = f (cycSucc j) ∧ c = f (cycPred j)) ∨ (a = f (cycPred j) ∧ c = f (cycSucc j))) := by
  obtain ⟨i, hi⟩ := hmem b |>.mp hb
  have h1 := filter_adj_C_eq_ringPair hC hshort hC5 f hf hcyc hmem i
  rw [hi] at h1
  have ha2 : a = f (cycSucc i) ∨ a = f (cycPred i) := by
    have hmem2 : a ∈ ({f (cycSucc i), f (cycPred i)} : Finset V) := by
      rw [← h1]
      exact Finset.mem_filter.mpr ⟨ha, hab.symm⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem2
    exact hmem2
  have hc2 : c = f (cycSucc i) ∨ c = f (cycPred i) := by
    have hmem2 : c ∈ ({f (cycSucc i), f (cycPred i)} : Finset V) := by
      rw [← h1]
      exact Finset.mem_filter.mpr ⟨hc, hcb.symm⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem2
    exact hmem2
  refine ⟨i, hi.symm, ?_⟩
  rcases ha2 with ha2 | ha2 <;> rcases hc2 with hc2 | hc2
  · exact absurd hac (fun he => he (by rw [ha2, hc2]))
  · exact Or.inl ⟨ha2, hc2⟩
  · exact Or.inr ⟨ha2, hc2⟩
  · exact absurd hac (fun he => he (by rw [ha2, hc2]))

/-- **THREE POINTS OF `C` WITH `G.Adj a b` AND `G.Adj b c` AND `a ≠ c` ARE THREE CONSECUTIVE POINTS OF
THE RING.** -/
theorem path3_ring {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) {b a c : V} (hb : b ∈ C) (ha : a ∈ C)
    (hc : c ∈ C) (hab : G.Adj a b) (hcb : G.Adj b c) (hac : a ≠ c) :
    ∃ j : Fin 5, b = f j ∧
      ((a = f (cycSucc j) ∧ c = f (cycPred j)) ∨ (a = f (cycPred j) ∧ c = f (cycSucc j))) :=
  two_neigh_ring hC hshort hC5 f hf hcyc hmem hb ha hc hab hcb.symm hac

/-! ## Part 1 bis — re-numbering the ring, so that the ring arithmetic becomes `decide` -/

/-- **THE RING RE-NUMBERED WITH `j` AS THE STARTING POINT.** -/
def ringShift (f : Fin 5 → V) (j : Fin 5) : Fin 5 → V := fun k => f ((cycSucc^[k.val] : Fin 5 → Fin 5) j)

theorem ringShift_inj {f : Fin 5 → V} (hf : Function.Injective f) (j : Fin 5) :
    Function.Injective (ringShift f j) := by
  intro x y hxy
  have hv : ((cycSucc^[x.val] : Fin 5 → Fin 5) j).val
      = ((cycSucc^[y.val] : Fin 5 → Fin 5) j).val := by
    exact congrArg Fin.val (hf hxy)
  have h1 := cycSucc_pow_val (n := 5) x.val j
  have h2 := cycSucc_pow_val (n := 5) y.val j
  simp only [h1, h2] at hv
  have hj := j.2
  omega

theorem ringShift_adj' {f : Fin 5 → V} (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (j k : Fin 5) :
    G.Adj (f ((cycSucc^[k.val] : Fin 5 → Fin 5) j))
      (f ((cycSucc^[(cycSucc k).val] : Fin 5 → Fin 5) j)) := by
  have h := hcyc ((cycSucc^[k.val] : Fin 5 → Fin 5) j)
  have h2 : (cycSucc ((cycSucc^[k.val] : Fin 5 → Fin 5) j) : Fin 5)
      = (cycSucc^[(cycSucc k).val] : Fin 5 → Fin 5) j := by
    calc (cycSucc ((cycSucc^[k.val] : Fin 5 → Fin 5) j) : Fin 5)
        = ((cycSucc^[k.val + 1] : Fin 5 → Fin 5) j) :=
          (Function.iterate_succ_apply' cycSucc k.val j).symm
      _ = ((cycSucc^[(cycSucc k).val] : Fin 5 → Fin 5) j) := by
        refine five_iterate_eq j ?_
        rw [cycSucc_val]
        simp [Nat.mod_mod]
  rw [← h2]
  exact h

theorem ringShift_adj {f : Fin 5 → V} (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (j k : Fin 5) : G.Adj (ringShift f j k) (ringShift f j (cycSucc k)) := ringShift_adj' hcyc j k

theorem ringShift_mem {C : Finset V} {f : Fin 5 → V}
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (j : Fin 5) :
    ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, ringShift f j k = y := by
  intro y
  constructor
  · intro hy
    obtain ⟨i, hi⟩ := hmem y |>.mp hy
    have hi' : i ∈ ({j, cycSucc j, cycSucc (cycSucc j), cycSucc (cycSucc (cycSucc j)),
        cycSucc (cycSucc (cycSucc (cycSucc j)))} : Finset (Fin 5)) := by
      rw [← five_univ_eq_iter]
      exact Finset.mem_univ i
    rcases Finset.mem_insert.mp hi' with h | h
    · refine ⟨⟨0, by omega⟩, ?_⟩
      show f j = y
      exact (congrArg f h).symm.trans hi
    · rcases Finset.mem_insert.mp h with h | h
      · refine ⟨⟨1, by omega⟩, ?_⟩
        have h3 := five_iterate_one j
        show f ((cycSucc^[1] : Fin 5 → Fin 5) j) = y
        rw [h3]
        exact (congrArg f h).symm.trans hi
      · rcases Finset.mem_insert.mp h with h | h
        · refine ⟨⟨2, by omega⟩, ?_⟩
          have h3 := five_iterate_two j
          show f ((cycSucc^[2] : Fin 5 → Fin 5) j) = y
          rw [h3]
          exact (congrArg f h).symm.trans hi
        · rcases Finset.mem_insert.mp h with h | h
          · refine ⟨⟨3, by omega⟩, ?_⟩
            have h3 := five_iterate_three j
            show f ((cycSucc^[3] : Fin 5 → Fin 5) j) = y
            rw [h3]
            exact (congrArg f h).symm.trans hi
          · refine ⟨⟨4, by omega⟩, ?_⟩
            have h3 := five_iterate_four j
            show f ((cycSucc^[4] : Fin 5 → Fin 5) j) = y
            simp only [Finset.mem_singleton] at h
            exact (congrArg f h).symm.trans hi
  · rintro ⟨k, hk⟩
    exact hmem y |>.mpr ⟨(cycSucc^[k.val] : Fin 5 → Fin 5) j, hk⟩

/-! ## Part 2 — the ring data of the two shapes -/

/-- **THE RING DATA OF A THREE-INTERSECTION FIVE-CYCLE OF THE SHAPE A.**

`D` is a three-intersection five-cycle of the shape A of `JSPProblem/Three.lean`, seen through a
cyclic numbering `g` of `C` in which the **middle of the path** `a - b - c` inside `C` is `g 0`:
`a = g 4`, `b = g 0`, `c = g 1` (or the reverse orientation), the missed pair of `D` is the edge
`{g 2, g 3}` of `C`, and `d = g 3` is the ring-neighbour of `a` while `e = g 2` is the ring-neighbour of
`c`.  With `w1 ~ c`, `w2 ~ a` and `w1 ~ w2` this is exactly the shape A of round 159, with the ring
positions spelled out. -/
structure RingShapeAData (G : SimpleGraph V) (C D : Finset V) (g : Fin 5 → V) (w1 w2 a b c d e : V) :
    Prop where
  /-- **THE TWO ORIENTATIONS OF THE PATH IN THE RING.** -/
  pos : (a = g 4 ∧ c = g 1 ∧ d = g 3 ∧ e = g 2) ∨ (a = g 1 ∧ c = g 4 ∧ d = g 2 ∧ e = g 3)
  /-- **THE MIDDLE OF THE PATH IS THE STARTING POINT OF THE RING.** -/
  mid : g 0 = b
  /-- **THE THREE INSIDE POINTS ARE DISTINCT POINTS OF `C`, THE TWO OUTSIDE POINTS ARE NOT.** -/
  distinct : a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ w1 ∉ C ∧ w2 ∉ C ∧ w1 ≠ w2 ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c
  /-- **`D` IS THE FIVE POINTS, AND THE FIVE ADJACENCIES OF THE SHAPE A HOLD.** -/
  shape : D = {a, b, c, w1, w2} ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c w1 ∧ G.Adj w2 a ∧ G.Adj w1 w2
  /-- **THE MISSED PAIR OF `D` IS THE EDGE `{d, e}` OF `C`, AND IT CONTINUES THE PATH.** -/
  missed : C \ D = {d, e} ∧ G.Adj d e ∧ G.Adj a d ∧ G.Adj c e

/-- **A RING NUMBERING WITNESSES THE SHAPE-A DATA OF SOME FIVE-CYCLE.** -/
def RingShapeA (G : SimpleGraph V) (C D : Finset V) (g : Fin 5 → V) (w1 w2 : V) : Prop :=
  ∃ a b c d e : V, RingShapeAData G C D g w1 w2 a b c d e

/-- **A SHAPE-A FIVE-CYCLE HAS A RING NUMBERING WITNESSING `RingShapeA`.**

This is `JSP90.exists_shape` of round 159 with the ring positions made explicit: the missed pair of a
three-intersection five-cycle of shape A is an **edge** of `C`, the one opposite to the middle of the
path `a - b - c`, and its two points are the ring-neighbours of `a` and of `c` respectively. -/
theorem exists_ringShapeA {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) {w1 w2 : V} (h : IsShapeA G C D w1 w2) :
    ∃ (g : Fin 5 → V) (hg : Function.Injective g) (hcycg : ∀ k : Fin 5, G.Adj (g k) (g (cycSucc k)))
      (hmemg : ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, g k = y), RingShapeA G C D g w1 w2 := by
  obtain ⟨a, b, c, ha, hb, hc, hab', hbc', hac', hw1, hw2, hw, hDset, hab, hbc, hcw1, hw2a,
    hw1w2⟩ := h
  obtain ⟨j, hbj, hpos⟩ := path3_ring hC hshort hC5 f hf hcyc hmem hb ha hc hab hbc hac'
  set g : Fin 5 → V := ringShift f j with hgdef
  have hg : Function.Injective g := ringShift_inj hf j
  have hcycg : ∀ k : Fin 5, G.Adj (g k) (g (cycSucc k)) := ringShift_adj hcyc j
  have hmemg : ∀ y : V, y ∈ C ↔ ∃ k : Fin 5, g k = y := ringShift_mem hmem j
  have hne : ∀ (k l : Fin 5), k ≠ l → g k ≠ g l := fun k l hkl => five_f_ne hg hkl
  have hg0 : g 0 = b := by
    have h1 : g 0 = f j := rfl
    rw [h1]
    exact hbj.symm
  -- the two ways in which the points `a`, `b`, `c` can sit in the ring
  have hpos' : ((a = g 4 ∧ c = g 1) ∨ (a = g 1 ∧ c = g 4)) := by
    have h4 : f (cycPred j) = g 4 := rfl
    have h1 : f (cycSucc j) = g 1 := rfl
    rcases hpos with hpos | hpos
    · exact Or.inr ⟨hpos.1.trans h1, hpos.2.trans h4⟩
    · exact Or.inl ⟨hpos.1.trans h4, hpos.2.trans h1⟩
  -- `C ∩ D` is the triple `{a, b, c}`, and `C \ D = C \ {a, b, c}`
  have hinter : C ∩ D = {a, b, c} := by
    apply Finset.Subset.antisymm
    · intro x hx
      have hxc := (Finset.mem_inter.mp hx).1
      have hxd := (Finset.mem_inter.mp hx).2
      rw [hDset] at hxd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxd
      rcases hxd with rfl | rfl | rfl | h | h
      · simp
      · simp
      · simp
      · exact absurd h (fun hw => hw1 (h ▸ hxc))
      · exact absurd h (fun hw => hw2 (h ▸ hxc))
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h
      · subst h; exact Finset.mem_inter.mpr ⟨ha, by rw [hDset]; simp⟩
      · subst h; exact Finset.mem_inter.mpr ⟨hb, by rw [hDset]; simp⟩
      · subst h; exact Finset.mem_inter.mpr ⟨hc, by rw [hDset]; simp⟩
  have hsdiff : C \ D = C \ {a, b, c} := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_sdiff]
      exact ⟨hx.1, fun hx3 => hx.2 ((Finset.mem_inter.mp (mem_of_mem_congr' hinter hx3)).2)⟩
    · intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_sdiff]
      exact ⟨hx.1, fun hxD => hx.2 (mem_of_mem_congr hinter (Finset.mem_inter.mpr ⟨hx.1, hxD⟩))⟩
  rcases hpos' with hpos' | hpos'
  · -- the orientation `a = g 4`, `b = g 0`, `c = g 1`, the missed pair `{g 3, g 2}`
    refine ⟨g, hg, hcycg, hmemg, a, b, c, g 3, g 2, ?_⟩
    refine ⟨Or.inl ⟨hpos'.1, hpos'.2, rfl, rfl⟩, hg0, ?_, ?_, ?_⟩
    · exact ⟨ha, hb, hc, hw1, hw2, hw, hab', hbc', hac'⟩
    · exact ⟨hDset, hab, hbc, hcw1, hw2a, hw1w2⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hsdiff, hpos'.1, ← hg0, hpos'.2]
        exact sdiff_of_card (C := C) (S := {g 4, g 0, g 1}) (T := {g 3, g 2})
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
          (card_three (hne 4 0 (by decide)) (hne 4 1 (by decide)) (hne 0 1 (by decide)))
          (card_pair (hne 3 2 (by decide)))
          hC5
      · exact adj_ringPred hcycg 3
      · exact (hpos'.1 ▸ adj_ringPred hcycg 4)
      · exact (hpos'.2 ▸ hcycg 1)
  · -- the reversed orientation: `a = g 1`, `b = g 0`, `c = g 4`, the missed pair `{g 2, g 3}`
    refine ⟨g, hg, hcycg, hmemg, a, b, c, g 2, g 3, ?_⟩
    refine ⟨Or.inr ⟨hpos'.1, hpos'.2, rfl, rfl⟩, hg0, ?_, ?_, ?_⟩
    · exact ⟨ha, hb, hc, hw1, hw2, hw, hab', hbc', hac'⟩
    · exact ⟨hDset, hab, hbc, hcw1, hw2a, hw1w2⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hsdiff, hpos'.1, ← hg0, hpos'.2]
        exact sdiff_of_card (C := C) (S := {g 1, g 0, g 4}) (T := {g 2, g 3})
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
          (card_three (hne 1 0 (by decide)) (hne 1 4 (by decide)) (hne 0 4 (by decide)))
          (card_pair (hne 2 3 (by decide)))
          hC5
      · exact hcycg 2
      · exact (hpos'.1 ▸ hcycg 1)
      · exact (hpos'.2.symm ▸ adj_ringPred hcycg 4)

/-! ## Part 3 — the missed pair of `D` is the triple `{a, b, c}` inside `C` -/

/-- **`C ∩ D` IS THE TRIPLE OF THE THREE POINTS OF `C` WHICH `D` USES.** -/
lemma inter_D_eq_triple {C D : Finset V} {a b c w1 w2 : V}
    (hD : D = {a, b, c, w1, w2}) (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (hw1 : w1 ∉ C) (hw2 : w2 ∉ C) (hw : w1 ≠ w2) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    C ∩ D = {a, b, c} := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hxc := (Finset.mem_inter.mp hx).1
    have hxd := (Finset.mem_inter.mp hx).2
    rw [hD] at hxd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxd
    rcases hxd with rfl | rfl | rfl | h | h
    · simp
    · simp
    · simp
    · exact absurd h (fun hw => hw1 (h ▸ hxc))
    · exact absurd h (fun hw => hw2 (h ▸ hxc))
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · subst h; exact Finset.mem_inter.mpr ⟨ha, by rw [hD]; simp⟩
    · subst h; exact Finset.mem_inter.mpr ⟨hb, by rw [hD]; simp⟩
    · subst h; exact Finset.mem_inter.mpr ⟨hc, by rw [hD]; simp⟩

/-- **THE POINTS OF `C` SPLIT BETWEEN THE TWO PARTS OF `D` INSIDE AND OUTSIDE `C`.** -/
lemma mem_C_split {C D : Finset V} {a b c d e z : V} (hinter : C ∩ D = {a, b, c})
    (hsdiff : C \ D = {d, e}) (hz : z ∈ C) :
    z ∈ ({a, b, c} : Finset V) ∨ z ∈ ({d, e} : Finset V) := by
  have h1 : z ∈ C ∩ D ∪ C \ D := by
    rw [inter_union_sdiff' C D]
    exact hz
  rcases Finset.mem_union.mp h1 with h1 | h1
  · exact Or.inl (mem_of_mem_congr hinter h1)
  · exact Or.inr (mem_of_mem_congr hsdiff h1)

/-! ## Part 4 — the corrected MISSING LEMMA 3a: the candidate neighbour sets of the shape A -/

/-- **IN THE SHAPE A, THE NEIGHBOURS OF AN OUTSIDE VERTEX INSIDE `C` ARE CONFINED TO **TWO**
CANDIDATES: the far endpoint of the path `a - b - c`, and the missed point adjacent to it.**

This is the corrected form of MISSING LEMMA 3a of `discovery/JSP-000090/policy.json`.  The policy
bet that the two sets are **singletons** is false: `JSP90.adjIn_5_C_sA` below is a machine-checked
counterexample (and `discovery/JSP-000090/r160.log` measures all four combinations of sizes
`(1,1), (1,2), (2,1), (2,2)` among the shape-A instances of the census).  The two candidates are
nevertheless *all* that can happen, and by `JSP90.four_intersection_of_shapeA` the second one has a
meaning: it turns the triple `{a, b, c}` into a four-intersection five-cycle. -/
theorem adjIn_C_subset_of_shapeA {C D : Finset V} (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    {g : Fin 5 → V} {w1 w2 a b c d e : V} (h : RingShapeAData G C D g w1 w2 a b c d e) :
    AdjIn G w1 C ⊆ {c, d} ∧ AdjIn G w2 C ⊆ {a, e} := by
  obtain ⟨hpos, hmid, hdist, hshape, hmissed⟩ := h
  obtain ⟨hDset, hab, hbc, hcw1, hw2a, hw1w2⟩ := hshape
  obtain ⟨hsdiff, hde, had, hce⟩ := hmissed
  obtain ⟨ha, hb, hc, hw1, hw2, hw, hab', hbc', hac'⟩ := hdist
  have hinter : C ∩ D = {a, b, c} := inter_D_eq_triple hDset ha hb hc hw1 hw2 hw hab' hbc' hac'
  constructor
  · intro z hz
    have hz1 : z ∈ C ∧ G.Adj w1 z := mem_adjIn.mp hz
    rcases mem_C_split hinter hsdiff hz1.1 with hz2 | hz2
    · simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz2
      rcases hz2 with rfl | rfl | rfl
      · exact absurd hz1.2 (fun h => no_triangle_of_not_isNClique htf hw1w2.symm hw2a h)
      · exact absurd hz1.2 (fun h => no_triangle_of_not_isNClique htf hcw1.symm h hbc.symm)
      · simp
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hz2
      rcases hz2 with rfl | rfl
      · simp
      · exact absurd hz1.2 (fun h => no_triangle_of_not_isNClique htf hcw1.symm h hce)
  · intro z hz
    have hz1 : z ∈ C ∧ G.Adj w2 z := mem_adjIn.mp hz
    rcases mem_C_split hinter hsdiff hz1.1 with hz2 | hz2
    · simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz2
      rcases hz2 with rfl | rfl | rfl
      · simp
      · exact absurd hz1.2 (fun h => no_triangle_of_not_isNClique htf hw2a h hab)
      · exact absurd hz1.2 (fun h => no_triangle_of_not_isNClique htf hw1w2.symm h hcw1.symm)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hz2
      rcases hz2 with rfl | rfl
      · exact absurd hz1.2 (fun h => no_triangle_of_not_isNClique htf hw2a hz1.2 had)
      · simp

/-- **THE SECOND CANDIDATE OF THE SHAPE A IS A FOUR-INTERSECTION FIVE-CYCLE.**

If the missed point `d` adjacent to `a` is really adjacent to `w1` — i.e. it is the second neighbour of
`w1` inside `C` — then `w1 - d - a - b - c - w1` is a five-cycle of `G` meeting `C` in the **four**
points `a, b, c, d`.  So in the shape A the point `e` is missed by `D` while the point `d` is missed
exactly when these extra adjacencies are absent: the two candidates are not symmetric. -/
theorem four_intersection_of_shapeA {C D : Finset V} {g : Fin 5 → V} {w1 w2 a b c d e : V}
    (h : RingShapeAData G C D g w1 w2 a b c d e) (hd : d ∈ AdjIn G w1 C) :
    ∃ D' : Finset V, IsOddCycle G D' ∧ D'.card = 5 ∧ (D' ∩ C).card = 4 := by
  obtain ⟨hpos, hmid, hdist, hshape, hmissed⟩ := h
  obtain ⟨hDset, hab, hbc, hcw1, hw2a, hw1w2⟩ := hshape
  obtain ⟨hsdiff, hde, had, hce⟩ := hmissed
  obtain ⟨ha, hb, hc, hw1, hw2, hw, hab', hbc', hac'⟩ := hdist
  have hd' : d ∈ C ∧ G.Adj w1 d := mem_adjIn.mp hd
  have hdnotD : d ∉ D := (Finset.mem_sdiff.mp (mem_of_mem_congr' hsdiff
    ((Finset.mem_insert.mpr (Or.inl rfl)) : d ∈ ({d, e} : Finset V)))).2
  have hdne : d ≠ a ∧ d ≠ b ∧ d ≠ c := by
    refine ⟨fun h => hdnotD (h ▸ (by rw [hDset]; simp)), fun h => hdnotD (h ▸ (by rw [hDset]; simp)),
      fun h => hdnotD (h ▸ (by rw [hDset]; simp))⟩
  have hw1ne : w1 ≠ d := fun h => hw1 (h ▸ hd'.1)
  have hw1a : w1 ≠ a := fun h => hw1 (h ▸ ha)
  have hw1b : w1 ≠ b := fun h => hw1 (h ▸ hb)
  have hw1c : w1 ≠ c := fun h => hw1 (h ▸ hc)
  have hD' : IsOddCycle G ({w1, d, a, b, c} : Finset V) :=
    isOddCycle_of_cyc5V ⟨hw1ne, hw1a, hw1b, hw1c, hdne.1, hdne.2.1, hdne.2.2, hab', hac', hbc'⟩
      hd'.2 had.symm hab hbc hcw1
  have hmem1 : d ∈ (({w1, d, a, b, c} : Finset V) ∩ C) := by
    refine Finset.mem_inter.mpr ⟨?_, hd'.1⟩
    simp [Finset.mem_insert, Finset.mem_singleton]
  have hmem2 : a ∈ (({w1, d, a, b, c} : Finset V) ∩ C) := by
    refine Finset.mem_inter.mpr ⟨?_, ha⟩
    simp [Finset.mem_insert, Finset.mem_singleton]
  have hmem3 : b ∈ (({w1, d, a, b, c} : Finset V) ∩ C) := by
    refine Finset.mem_inter.mpr ⟨?_, hb⟩
    simp [Finset.mem_insert, Finset.mem_singleton]
  have hmem4 : c ∈ (({w1, d, a, b, c} : Finset V) ∩ C) := by
    refine Finset.mem_inter.mpr ⟨?_, hc⟩
    simp [Finset.mem_insert, Finset.mem_singleton]
  have hsub : ({d, a, b, c} : Finset V) ⊆ ({w1, d, a, b, c} : Finset V) ∩ C := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · rw [h]; exact hmem1
    · rw [h]; exact hmem2
    · rw [h]; exact hmem3
    · rw [h]; exact hmem4
  have hsub2 : (({w1, d, a, b, c} : Finset V) ∩ C) ⊆ ({w1, d, a, b, c} : Finset V) \ {w1} := by
    intro x hx
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_sdiff]
    rw [Finset.mem_singleton] at *
    exact ⟨hx.1, fun h1 => hw1 (h1 ▸ hx.2)⟩
  have hcard4 : ({d, a, b, c} : Finset V).card = 4 := by
    refine card_four ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hdne.1
    · exact hdne.2.1
    · exact hdne.2.2
    · exact hab'
    · exact hac'
    · exact hbc'
  have hcard5 : (({w1, d, a, b, c} : Finset V) : Finset V).card = 5 := by
    simp [Finset.card_insert_of_notMem, hw1ne, hw1a, hw1b, hw1c, hdne.1, hdne.2.1, hdne.2.2,
      hab', hac', hbc']
  have hcardsd : (({w1, d, a, b, c} : Finset V) \ {w1} : Finset V).card = 4 := by
    rw [Finset.card_sdiff_of_subset (by simp)]
    have h1 : (({w1} : Finset V) : Finset V).card = 1 := Finset.card_singleton w1
    omega
  refine ⟨{w1, d, a, b, c}, hD', hcard5, ?_⟩
  have hle : ({d, a, b, c} : Finset V).card ≤ (({w1, d, a, b, c} : Finset V) ∩ C).card :=
    Finset.card_le_card hsub
  have hle2 : (({w1, d, a, b, c} : Finset V) ∩ C).card
      ≤ (({w1, d, a, b, c} : Finset V) \ {w1} : Finset V).card := Finset.card_le_card hsub2
  omega

/-! ## Part 5 — the machine-checked refutation of the singleton claim

The graph below is the witness of `discovery/JSP-000090/r160.c`: on seven vertices, with `C` the
five-cycle `0-1-2-3-4-0`, the five-cycle `D = {0, 3, 4, 5, 6}` = `6 - 0 - 4 - 3 - 5 - 6` is of the
shape A with `(a, b, c, w1, w2) = (0, 4, 3, 5, 6)`, the missed pair is `{1, 2}`, and

```text
N_C(5) = {1, 3}   (so |N_C(5)| = 2)      N_C(6) = {0}   (so |N_C(6)| = 1)
```

i.e. **one** of the two outside vertices sees two points of `C` and the other one: exactly the
configuration that the singleton claim forbids. -/

/-- **The edge set of the witness of the refutation.** -/
def sAEdge : Finset (Fin 7 × Fin 7) :=
  {(0, 1), (1, 0), (0, 4), (4, 0), (0, 6), (6, 0), (1, 2), (2, 1), (1, 5), (5, 1),
    (2, 3), (3, 2), (3, 4), (4, 3), (3, 5), (5, 3), (5, 6), (6, 5)}

theorem sAEdge_symm : ∀ v w : Fin 7, (v, w) ∈ sAEdge ↔ (w, v) ∈ sAEdge := by decide

theorem sAEdge_irrefl : ∀ v : Fin 7, (v, v) ∉ sAEdge := by decide

/-- **The seven-vertex witness graph of the refutation of the singleton claim.** -/
def sA : SimpleGraph (Fin 7) where
  Adj v w := (v, w) ∈ sAEdge
  symm := ⟨fun _ _ h => (sAEdge_symm _ _).mp h⟩
  loopless := ⟨fun _ h => sAEdge_irrefl _ h⟩

local instance : DecidableRel sA.Adj := fun v w => inferInstanceAs (Decidable ((v, w) ∈ sAEdge))

@[simp] theorem sA_adj {v w : Fin 7} : sA.Adj v w ↔ (v, w) ∈ sAEdge := Iff.rfl

/-- **The witness cycle `C` of the refutation.** -/
def sAC : Finset (Fin 7) := {0, 1, 2, 3, 4}

/-- **The witness five-cycle `D` of the refutation.** -/
def sAD : Finset (Fin 7) := {0, 3, 4, 5, 6}

/-- **THE FIVE-CYCLE `D = {0, 3, 4, 5, 6}` OF THE WITNESS IS OF THE SHAPE A**, with the witnesses
`(a, b, c, w1, w2) = (0, 4, 3, 5, 6)`: the cycle runs `6 - 0 - 4 - 3 - 5 - 6`, so `a - b - c` is the
path `0 - 4 - 3` of `C`, `w1 ~ c`, `w2 ~ a` and `w1 ~ w2`. -/
theorem isShapeA_sA : IsShapeA sA sAC sAD 5 6 := by
  refine ⟨0, 4, 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (apply Finset.ext; intro x; simp [sAC, sAD, Finset.mem_insert, Finset.mem_singleton]; tauto)
    | simp [sAC, sAD, sAEdge, Finset.mem_insert, Finset.mem_singleton, sA_adj, or_comm, or_assoc]

/-- **THE NEIGHBOURS OF THE OUTSIDE VERTEX `5` INSIDE THE WITNESS CYCLE `C` ARE THE TWO POINTS `1`
AND `3`** — so the neighbour set of an outside vertex of a shape-A cycle need **not** be a singleton,
and MISSING LEMMA 3a of `discovery/JSP-000090/policy.json` is false. -/
theorem adjIn_5_C_sA : AdjIn sA 5 sAC = {1, 3} := by
  ext z
  fin_cases z <;> simp [AdjIn, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
    sAC, sAEdge, sA_adj]

/-- **THE REFUTATION OF THE SINGLETON CLAIM, MACHINE-CHECKED.**  In the shape A the neighbour set of
an outside vertex inside `C` has cardinality `2`. -/
theorem not_singleton_shapeA : (AdjIn sA 5 sAC).card = 2 := by
  rw [adjIn_5_C_sA]
  decide

/-- **AND THE OTHER OUTSIDE VERTEX OF THE SAME SHAPE-A CYCLE SEES EXACTLY ONE POINT**, so the two
sizes are independent — exactly as the census of `discovery/JSP-000090/r160.log` measures (all four
combinations `(1,1), (1,2), (2,1), (2,2)` occur among the shape-A instances). -/
theorem adjIn_6_C_sA : AdjIn sA 6 sAC = {0} := by
  ext z
  fin_cases z <;> simp [AdjIn, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
    sAC, sAEdge, sA_adj]

end
end JSP90
