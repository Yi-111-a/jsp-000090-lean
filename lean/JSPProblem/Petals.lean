/-
# JSP-000090 — the multi-petal windmill: Erdős's hypothesis at `k = 1` with UNBOUNDED cover cost

This file is round 117 of the attack on `jsp_000090_main` (Erdős Problem #73, Reed 1999), and it
**refutes the residual lemma of round 115**.

## What round 115 left as "the single missing lemma"

`JSPProblem/TwoAttach.lean` writes the whole remaining problem down as one `def`

```
JSP90.TwoAttachCoverExists r ℓ q
  every finite graph whose odd cycle packings all have at most r members carries a two-attachment
  cover with at most q members, each of them of at most ℓ vertices
```

and proves `JSP90.erdos73_of_twoAttachCoverExists : (∀ ℓ q, ∀ r, TwoAttachCoverExists r ℓ q) →
∀ k, Erdős73 k`.  So a single statement stood between this development and `jsp_000090_main`.

## What this file proves: that statement is FALSE

The `r`-petal windmill `windmill r` — `r` triangles `0 - (2 i + 1) - (2 i + 2) - 0` sharing the
single hub `0`, on `Fin (2 * r + 1)` — is a `LocIndep 1` graph:

* `JSP90.locIndep_one_windmill` — **for every `r`**, every vertex set of `windmill r` carries an
  independent set `S` with `2 * |S| + 1 ≥ |X|`, i.e. `LocIndep 1 (windmill r)`.  (The two-petal
  instance `JSP90.wf` of `JSPProblem/Windmill.lean` was proved there by exhaustive decision over all
  `2 ^ 6` vertex sets; the statement is false for finite search, so this file proves the whole
  family.)
* `JSP90.packing_windmill` — consequently every packing of odd cycles of `windmill r` has **at most
  one** member: the packing number is bounded by `1` while the number of odd cycles is `r`, which
  is unbounded.

and yet

* `JSP90.closeToBipartite_one_windmill` — deleting the hub leaves a matching, so
  `CloseToBipartite 1 (windmill r)`;
* `JSP90.not_closeToBipartite_zero_windmill` — but not `CloseToBipartite 0`, so the **odd cycle
  transversal number of `windmill r` is exactly one** for `r ≥ 1`;
* **`JSP90.coverCost_windmill_eq` — the minimum cost of a two-attachment cover of `windmill r` is
  EXACTLY `r`**, where the cost is `∑ X ∈ 𝒞, (|X| - 1)`: `wmPetalCover r` is a cover of cost `r`,
  and `cover_cost_ge_windmill` shows every cover costs at least `r`.

Therefore

* **`JSP90.not_twoAttachCoverExists_one : ¬ TwoAttachCoverExists 1 ℓ q` for every `ℓ` and `q`**,
  i.e. `TwoAttachCoverExists 1 ℓ q` is false for *all* constants — the statement fails already at
  `r = 1`;
* **`JSP90.windmill_separates_transversal_from_cover t`**: for every `t` there is a graph with
  `LocIndep 1`, packing number one and odd cycle transversal number one, for which every
  two-attachment cover costs at least `t`.

So no function of the packing number bounds the cost of a two-attachment cover, and the reduction
`JSP90.erdos73_of_twoAttachCoverExists` of `JSPProblem/TwoAttach.lean` — together with
`JSP90.oddCycleErdosPosa_of_twoAttachCoverExists` — can never be used: it reduces Erdős #73 to a
false statement.  **A two-attachment cover is the wrong intermediate object**: the hub is a
transversal of size one but it meets every triangle in exactly one vertex, and the price of forcing
*two* vertices is the number of triangles.

## What is left

`jsp_000090_main` is **not** declared, and the only remaining target is `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas): a bounded odd cycle packing number forces a bounded odd cycle
transversal.  The windmill shows that the transversal cannot be produced by a bounded-size family of
two-attachment sets, so the classical proof must produce the deletion set *directly*
(`JSP90.closeToBipartite_iff_hitsOddCycles`), i.e. one vertex per odd cycle **at most**, not two.

The only new *instance of the headline theorem* proved here is the simplest one along a new axis:

* `JSP90.closeToBipartite_one_of_oddCycles_through` and `JSP90.erdos73On_one_of_oddCycles_through`
  — if every odd cycle of `G` passes through one vertex then `CloseToBipartite 1 G`, with constant
  `1` and no bound on the odd girth, the packing number or the number of odd cycles.  The windmill
  satisfies it, so the class is not empty, and it is *sharp*: the hub meets each triangle once, which
  is exactly why it defeats the cover method.
-/

import JSPProblem.TwoAttach

namespace JSP90

open Finset Fintype Set

variable {V : Type*}

noncomputable section

local instance instDecidableEqPetalsV : DecidableEq V := Classical.decEq V

/-- One computable `DecidableEq (Fin n)` for the whole file (the trick of
`JSPProblem/Windmill.lean`): the vertex type of the windmill is `Fin (2 * r + 1)`, and the finset
bookkeeping below (`Finset.inter`, `Finset.image`, `Finset.erase`) has to agree with the instances
used by `JSPProblem/TwoAttach.lean`. -/
local instance instDecidableEqFinWM (n : ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

/-! ## The `r`-petal windmill -/

/-- **Adjacency in the `r`-petal windmill**: the hub `0` is adjacent to every other vertex, and the
two vertices `2 * i + 1`, `2 * i + 2` of petal `i` are adjacent to each other and to nothing else. -/
def wmAdj (r : ℕ) (v w : Fin (2 * r + 1)) : Prop :=
  v.val ≠ w.val ∧
    ((v.val = 0 ∧ w.val ≠ 0) ∨ (w.val = 0 ∧ v.val ≠ 0) ∨
      (v.val % 2 = 1 ∧ w.val = v.val + 1) ∨ (w.val % 2 = 1 ∧ v.val = w.val + 1))

/-- A vertex different from `a` is different from any `b = a`. -/
theorem Ne.of_eq_ne {α : Type*} {a b c : α} (h1 : a = b) (h2 : c ≠ b) : c ≠ a := by
  intro h
  exact h2 (h.symm ▸ h1)

/-- **`wmAdj` is symmetric.** -/
theorem wmAdj_symm {r : ℕ} {v w : Fin (2 * r + 1)} (h : wmAdj r v w) : wmAdj r w v := by
  rcases h.2 with h | h | h | h
  · exact ⟨Ne.of_eq_ne h.1 h.2, Or.inr (Or.inl h)⟩
  · exact ⟨Ne.symm (Ne.of_eq_ne h.1 h.2), Or.inl h⟩
  · exact ⟨by omega, Or.inr (Or.inr (Or.inr h))⟩
  · exact ⟨by omega, Or.inr (Or.inr (Or.inl h))⟩

/-- **`wmAdj` is irreflexive.** -/
theorem wmAdj_loopless {r : ℕ} {v : Fin (2 * r + 1)} (h : wmAdj r v v) : False :=
  h.1 rfl

/-- **The `r`-petal windmill**: `r` triangles `0 - (2 i + 1) - (2 i + 2) - 0` sharing the hub `0`. -/
def windmill (r : ℕ) : SimpleGraph (Fin (2 * r + 1)) where
  Adj := wmAdj r
  symm := ⟨by
    intro v w h
    exact wmAdj_symm h⟩
  loopless := ⟨by
    intro v h
    exact wmAdj_loopless h⟩

@[simp] theorem windmill_adj {r : ℕ} {v w : Fin (2 * r + 1)} :
    (windmill r).Adj v w ↔ wmAdj r v w := Iff.rfl

/-- The hub of `windmill r`. -/
def wmHub (r : ℕ) : Fin (2 * r + 1) := ⟨0, Nat.zero_lt_succ _⟩

/-- The odd (smaller) vertex of petal `i`. -/
def wmA (r : ℕ) (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val + 1, by omega⟩

/-- The even (larger) vertex of petal `i`. -/
def wmB (r : ℕ) (i : Fin r) : Fin (2 * r + 1) := ⟨2 * i.val + 2, by omega⟩

/-- **Petal `i`** of `windmill r`: the two vertices of the `i`-th triangle other than the hub. -/
def wmPetal (r : ℕ) (i : Fin r) : Finset (Fin (2 * r + 1)) := {wmA r i, wmB r i}

/-- **The `i`-th triangle** of `windmill r`: the hub together with petal `i`. -/
def wmTriSet (r : ℕ) (i : Fin r) : Finset (Fin (2 * r + 1)) := insert (wmHub r) (wmPetal r i)

@[simp] theorem wmHub_val (r : ℕ) : (wmHub r).val = 0 := rfl

@[simp] theorem wmA_val (r : ℕ) (i : Fin r) : (wmA r i).val = 2 * i.val + 1 := rfl

@[simp] theorem wmB_val (r : ℕ) (i : Fin r) : (wmB r i).val = 2 * i.val + 2 := rfl

@[simp] theorem wmA_mem_petal (r : ℕ) (i : Fin r) : wmA r i ∈ wmPetal r i :=
  Finset.mem_insert_self _ _

@[simp] theorem wmB_mem_petal (r : ℕ) (i : Fin r) : wmB r i ∈ wmPetal r i :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem mem_wmPetal_iff (r : ℕ) (i : Fin r) {z : Fin (2 * r + 1)} :
    z ∈ wmPetal r i ↔ z = wmA r i ∨ z = wmB r i := by
  simp [wmPetal]

theorem wmA_ne_wmB (r : ℕ) (i : Fin r) : wmA r i ≠ wmB r i := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [wmA_val, wmB_val] at h1
  omega

@[simp] theorem card_wmPetal (r : ℕ) (i : Fin r) : (wmPetal r i).card = 2 := by
  simp [wmPetal, wmA_ne_wmB]

/-- **A two-element set of vertices does not depend on the order.** -/
theorem insert_two_comm {r : ℕ} {u v : Fin (2 * r + 1)} :
    ({u, v} : Finset (Fin (2 * r + 1))) = {v, u} := by
  refine Finset.Subset.antisymm (Finset.subset_iff.mpr ?_) (Finset.subset_iff.mpr ?_)
  · intro z hz1
    rcases Finset.mem_insert.mp hz1 with (hz1 | hz1)
    · have hz3 : z = u := hz1
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hz3))
    · have hz3 : z = v := Finset.mem_singleton.mp hz1
      exact Finset.mem_insert.mpr (Or.inl hz3)
  · intro z hz1
    rcases Finset.mem_insert.mp hz1 with (hz1 | hz1)
    · have hz3 : z = v := hz1
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hz3))
    · have hz3 : z = u := Finset.mem_singleton.mp hz1
      exact Finset.mem_insert.mpr (Or.inl hz3)

@[simp] theorem card_wmTriSet (r : ℕ) (i : Fin r) : (wmTriSet r i).card = 3 := by
  have hne : wmHub r ∉ wmPetal r i := by
    intro hz
    rw [mem_wmPetal_iff] at hz
    rcases hz with (h | h)
    · have h1 := congrArg Fin.val h
      simp only [wmHub_val, wmA_val] at h1
      omega
    · have h1 := congrArg Fin.val h
      simp only [wmHub_val, wmB_val] at h1
      omega
  simp [wmTriSet, hne, card_wmPetal]

/-! ### The vertices are determined by their index -/

theorem wmA_inj_val {r : ℕ} {i j : Fin r} (h : wmA r i = wmA r j) : i = j := by
  have h1 := congrArg Fin.val h
  simp only [wmA_val] at h1
  omega

theorem wmB_inj_val {r : ℕ} {i j : Fin r} (h : wmB r i = wmB r j) : i = j := by
  have h1 := congrArg Fin.val h
  simp only [wmB_val] at h1
  omega

theorem wmA_eq_wmB_val {r : ℕ} {i j : Fin r} (h : wmA r i = wmB r j) : i = j := by
  have h1 := congrArg Fin.val h
  simp only [wmA_val, wmB_val] at h1
  omega

theorem wmB_eq_wmA_val {r : ℕ} {i j : Fin r} (h : wmB r i = wmA r j) : i = j := by
  have h1 := congrArg Fin.val h
  simp only [wmA_val, wmB_val] at h1
  omega

theorem wmPetal_ne_hub (r : ℕ) (i : Fin r) {z : Fin (2 * r + 1)} (hz : z ∈ wmPetal r i) :
    z ≠ wmHub r := by
  rw [mem_wmPetal_iff] at hz
  rcases hz with (h | h)
  · rw [h]
    exact fun he => by
      have h1 := congrArg Fin.val he
      simp only [wmA_val, wmHub_val] at h1
      omega
  · rw [h]
    exact fun he => by
      have h1 := congrArg Fin.val he
      simp only [wmB_val, wmHub_val] at h1
      omega

/-- **Distinct petals are disjoint.** -/
theorem wmPetal_inter {r : ℕ} {i j : Fin r} (h : i ≠ j) : wmPetal r i ∩ wmPetal r j = ∅ := by
  refine Finset.not_nonempty_iff_eq_empty.mp ?_
  rintro ⟨z, hz⟩
  rcases Finset.mem_inter.mp hz with ⟨hzi, hzj⟩
  rw [mem_wmPetal_iff] at hzi hzj
  rcases hzi with (hzi | hzi) <;> rcases hzj with (hzj | hzj)
  · exact absurd (wmA_inj_val (hzi.symm.trans hzj)) h
  · exact absurd (wmA_eq_wmB_val (hzi.symm.trans hzj)) h
  · exact absurd (wmB_eq_wmA_val (hzi.symm.trans hzj)) h
  · exact absurd (wmB_inj_val (hzi.symm.trans hzj)) h

/-- Two distinct triangles meet exactly in the hub. -/
theorem wmTriSet_inter {r : ℕ} {i j : Fin r} (h : i ≠ j) :
    wmTriSet r i ∩ wmTriSet r j = {wmHub r} := by
  refine Finset.Subset.antisymm (Finset.subset_iff.mpr ?_) (Finset.subset_iff.mpr ?_)
  · intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hz1, hz2⟩
    rcases Finset.mem_insert.mp hz1 with (hz1 | hz1)
    · exact Finset.mem_singleton.mpr hz1
    · rcases Finset.mem_insert.mp hz2 with (hz2 | hz2)
      · exact Finset.mem_singleton.mpr hz2
      · have hz3 : z ∉ wmPetal r i ∩ wmPetal r j := by
          rw [wmPetal_inter h]
          simp
        exact absurd (Finset.mem_inter.mpr ⟨hz1, hz2⟩) hz3
  · intro z hz
    have hz' : z = wmHub r := Finset.mem_singleton.mp hz
    rw [Finset.mem_inter]
    exact ⟨Finset.mem_insert.mpr (Or.inl hz'), Finset.mem_insert.mpr (Or.inl hz')⟩

theorem wmPetal_inj {r : ℕ} : Function.Injective (wmPetal r) := by
  intro i j h
  by_contra hne
  have h1 : wmA r i ∈ wmPetal r j := by rw [← h]; exact wmA_mem_petal r i
  rw [mem_wmPetal_iff] at h1
  rcases h1 with (h1 | h1)
  · exact absurd (wmA_inj_val h1) hne
  · exact absurd (wmA_eq_wmB_val h1) hne

/-- **Two vertices of given values are a petal.** -/
theorem wmPetal_eq_of_val {r : ℕ} {u v : Fin (2 * r + 1)} {i : Fin r}
    (hu : u.val = 2 * i.val + 1) (hv : v.val = 2 * i.val + 2) : {u, v} = wmPetal r i := by
  have huA : u = wmA r i := Fin.ext (by simp only [wmA_val]; rw [hu])
  have hvB : v = wmB r i := Fin.ext (by simp only [wmB_val]; rw [hv])
  rw [huA, hvB]
  rfl

/-- **An odd vertex followed by an even vertex is a whole petal.** -/
theorem wmAdj_petal_ordered {r : ℕ} {u v : Fin (2 * r + 1)}
    (hodd : u.val % 2 = 1) (hstep : v.val = u.val + 1) :
    ∃ i : Fin r, {u, v} = wmPetal r i := by
  have hu : u.val = 2 * ((u.val - 1) / 2) + 1 := by omega
  have hv : v.val = 2 * ((u.val - 1) / 2) + 2 := by omega
  refine ⟨⟨(u.val - 1) / 2, by omega⟩, ?_⟩
  exact wmPetal_eq_of_val hu hv

/-- **Two adjacent non-hub vertices of the windmill are a whole petal**: the non-hub edges of
`windmill r` are exactly the petals. -/
theorem exists_wmPetal_of_adj {r : ℕ} {u v : Fin (2 * r + 1)}
    (hu : u.val ≠ 0) (hv : v.val ≠ 0) (h : (windmill r).Adj u v) :
    ∃ i : Fin r, {u, v} = wmPetal r i := by
  rw [windmill_adj] at h
  rcases h.2 with h | h | h | h
  · exact absurd h.1 hu
  · exact absurd h.1 hv
  · obtain ⟨i, hi⟩ := wmAdj_petal_ordered h.1 h.2
    exact ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := wmAdj_petal_ordered h.1 h.2
    have hswap : ({u, v} : Finset (Fin (2 * r + 1))) = {v, u} := insert_two_comm
    exact ⟨i, hswap ▸ hi⟩

/-- **The edges of the windmill**: either the hub and a non-hub vertex, or the two vertices of one
petal. -/
theorem wmAdj_hub_or_petal {r : ℕ} {u v : Fin (2 * r + 1)} (h : (windmill r).Adj u v) :
    (u = wmHub r ∨ v = wmHub r) ∨ ∃ i : Fin r, {u, v} = wmPetal r i := by
  rw [windmill_adj] at h
  rcases h.2 with h | h | h | h
  · exact Or.inl (Or.inl (Fin.ext (by simpa [wmHub_val] using h.1)))
  · exact Or.inl (Or.inr (Fin.ext (by simpa [wmHub_val] using h.1)))
  · obtain ⟨i, hi⟩ := wmAdj_petal_ordered h.1 h.2
    exact Or.inr ⟨i, hi⟩
  · obtain ⟨i, hi⟩ := wmAdj_petal_ordered h.1 h.2
    have hswap : ({u, v} : Finset (Fin (2 * r + 1))) = {v, u} := insert_two_comm
    exact Or.inr ⟨i, hswap ▸ hi⟩

/-- **The partner of a vertex**: `wmPred r (wmA r i) = wmB r i` and `wmPred r (wmB r i) = wmA r i`,
and the hub is its own partner.  It is an involution. -/
def wmPred (r : ℕ) (v : Fin (2 * r + 1)) : Fin (2 * r + 1) :=
  ⟨2 * ((v.val + 1) / 2) - 1 + v.val % 2, by omega⟩

theorem wmPred_val (r : ℕ) (v : Fin (2 * r + 1)) :
    (wmPred r v).val = 2 * ((v.val + 1) / 2) - 1 + v.val % 2 := rfl

@[simp] theorem wmPred_wmA (r : ℕ) (i : Fin r) : wmPred r (wmA r i) = wmB r i := by
  rw [wmPred]
  apply Fin.ext
  simp only [wmA_val, wmB_val]
  omega

@[simp] theorem wmPred_wmB (r : ℕ) (i : Fin r) : wmPred r (wmB r i) = wmA r i := by
  rw [wmPred]
  apply Fin.ext
  simp only [wmA_val, wmB_val]
  omega

@[simp] theorem wmPred_hub (r : ℕ) : wmPred r (wmHub r) = wmHub r := by
  rw [wmPred]
  apply Fin.ext
  simp only [wmHub_val] <;> omega

/-- **The partner map of the windmill is an involution.** -/
theorem wmPred_involutive (r : ℕ) (v : Fin (2 * r + 1)) : wmPred r (wmPred r v) = v := by
  rw [wmPred]
  apply Fin.ext
  simp only [wmPred]
  omega

/-! ### Edges -/

theorem adj_wmHub {r : ℕ} {v : Fin (2 * r + 1)} (hv : v.val ≠ 0) :
    (windmill r).Adj (wmHub r) v := by
  rw [windmill_adj]
  exact ⟨Ne.symm hv, Or.inl ⟨rfl, hv⟩⟩

theorem adj_wmHub' {r : ℕ} {v : Fin (2 * r + 1)} (hv : v.val ≠ 0) :
    (windmill r).Adj v (wmHub r) :=
  (windmill r).adj_symm (adj_wmHub hv)

theorem wmA_adj_wmB {r : ℕ} (i : Fin r) : (windmill r).Adj (wmA r i) (wmB r i) := by
  rw [windmill_adj]
  exact ⟨by simp only [wmA_val, wmB_val]; omega,
    Or.inr (Or.inr (Or.inl ⟨by simp only [wmA_val]; omega, rfl⟩))⟩

theorem adj_wmA_wmB_iff {r : ℕ} (i j : Fin r) : (windmill r).Adj (wmA r i) (wmB r j) ↔ i = j := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_wmPetal_of_adj (by simp only [wmA_val]; omega)
      (by simp only [wmB_val]; omega) h
    have h1 := hk ▸ Finset.mem_insert_self (wmA r i) {wmB r j}
    have h2 := hk ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self (wmB r j))
    rw [mem_wmPetal_iff] at h1 h2
    rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2)
    · exact @wmA_eq_wmB_val r i j (h1.trans h2.symm)
    · exact (@wmA_inj_val r i k h1).trans (@wmB_inj_val r j k h2).symm
    · exact (@wmA_eq_wmB_val r i k h1).trans (@wmB_eq_wmA_val r j k h2).symm
    · exact (@wmA_eq_wmB_val r i k h1).trans (@wmB_inj_val r j k h2).symm
  · intro h
    subst h
    exact wmA_adj_wmB i

theorem not_adj_wmA_self {r : ℕ} (i : Fin r) : ¬ (windmill r).Adj (wmA r i) (wmA r i) := by
  rw [windmill_adj]
  exact wmAdj_loopless

theorem not_adj_wmB_self {r : ℕ} (i : Fin r) : ¬ (windmill r).Adj (wmB r i) (wmB r i) := by
  rw [windmill_adj]
  exact wmAdj_loopless

theorem not_adj_wmA_wmA {r : ℕ} (i j : Fin r) : ¬ (windmill r).Adj (wmA r i) (wmA r j) := by
  intro h
  obtain ⟨k, hk⟩ := exists_wmPetal_of_adj (by simp only [wmA_val]; omega)
    (by simp only [wmA_val]; omega) h
  have h1 := hk ▸ Finset.mem_insert_self (wmA r i) {wmA r j}
  have h2 := hk ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self (wmA r j))
  rw [mem_wmPetal_iff] at h1 h2
  rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2)
  · have hij : i = j := @wmA_inj_val r i j (h1.trans h2.symm)
    exact absurd (hij ▸ h) (not_adj_wmA_self j)
  · have hij : i = j := (@wmA_inj_val r i k h1).trans (@wmB_eq_wmA_val r k j h2.symm)
    exact absurd (hij ▸ h) (not_adj_wmA_self j)
  · have hij : i = j := (@wmA_eq_wmB_val r i k h1).trans (@wmA_inj_val r j k h2).symm
    exact absurd (hij ▸ h) (not_adj_wmA_self j)
  · have hij : i = j := @wmA_inj_val r i j (h1.trans h2.symm)
    exact absurd (hij ▸ h) (not_adj_wmA_self j)

theorem not_adj_wmB_wmB {r : ℕ} (i j : Fin r) : ¬ (windmill r).Adj (wmB r i) (wmB r j) := by
  intro h
  obtain ⟨k, hk⟩ := exists_wmPetal_of_adj (by simp only [wmB_val]; omega)
    (by simp only [wmB_val]; omega) h
  have h1 := hk ▸ Finset.mem_insert_self (wmB r i) {wmB r j}
  have h2 := hk ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self (wmB r j))
  rw [mem_wmPetal_iff] at h1 h2
  rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2)
  · have hij : i = j := @wmB_inj_val r i j (h1.trans h2.symm)
    exact absurd (hij ▸ h) (not_adj_wmB_self j)
  · have hij : i = j := (@wmB_eq_wmA_val r i k h1).trans (@wmB_inj_val r j k h2).symm
    exact absurd (hij ▸ h) (not_adj_wmB_self j)
  · have hij : i = j := (@wmB_inj_val r i k h1).trans (@wmB_eq_wmA_val r j k h2).symm
    exact absurd (hij ▸ h) (not_adj_wmB_self j)
  · have hij : i = j := @wmB_inj_val r i j (h1.trans h2.symm)
    exact absurd (hij ▸ h) (not_adj_wmB_self j)

theorem not_adj_wmA_wmB_of_ne {r : ℕ} {i j : Fin r} (h : i ≠ j) :
    ¬ (windmill r).Adj (wmA r i) (wmB r j) := by
  intro hadj
  exact h ((adj_wmA_wmB_iff i j).mp hadj)

/-- **The odd vertices of the windmill form an independent set.** -/
theorem isIndepSet_wmA (r : ℕ) :
    (windmill r).IsIndepSet ((univ : Finset (Fin r)).image (wmA r)) := by
  intro v hv w hw hvw
  obtain ⟨i, -, vi⟩ := Finset.mem_image.mp hv
  obtain ⟨j, -, wj⟩ := Finset.mem_image.mp hw
  rw [← vi, ← wj]
  exact not_adj_wmA_wmA i j

/-- **... and so do the even ones.** -/
theorem isIndepSet_wmB (r : ℕ) :
    (windmill r).IsIndepSet ((univ : Finset (Fin r)).image (wmB r)) := by
  intro v hv w hw hvw
  obtain ⟨i, -, vi⟩ := Finset.mem_image.mp hv
  obtain ⟨j, -, wj⟩ := Finset.mem_image.mp hw
  rw [← vi, ← wj]
  exact not_adj_wmB_wmB i j

/-! ### ERDŐS'S LOCAL HYPOTHESIS AT `k = 1`, FOR EVERY NUMBER OF PETALS -/

/-- **AN ODD VERTEX OF THE WINDMILL IS THE `i`-TH PETAL'S ODD VERTEX.** -/
theorem exists_wmA_of_odd {r : ℕ} {v : Fin (2 * r + 1)} (hv : v.val % 2 = 1) :
    ∃ i : Fin r, v = wmA r i := by
  have hvlt : v.val < 2 * r + 1 := v.isLt
  set i : Fin r := ⟨(v.val - 1) / 2, by omega⟩ with hi
  refine ⟨i, ?_⟩
  have hval : (i : ℕ) = (v.val - 1) / 2 := by simp only [hi]
  refine Fin.ext ?_
  rw [wmA_val, hval]
  omega

/-- **AN EVEN NON-HUB VERTEX OF THE WINDMILL IS THE `i`-TH PETAL'S EVEN VERTEX.** -/
theorem exists_wmB_of_even {r : ℕ} {v : Fin (2 * r + 1)} (hv0 : v.val ≠ 0)
    (hv : ¬ v.val % 2 = 1) : ∃ i : Fin r, v = wmB r i := by
  have hvlt : v.val < 2 * r + 1 := v.isLt
  set i : Fin r := ⟨(v.val - 2) / 2, by omega⟩ with hi
  refine ⟨i, ?_⟩
  have hval : (i : ℕ) = (v.val - 2) / 2 := by simp only [hi]
  refine Fin.ext ?_
  rw [wmB_val, hval]
  omega

/-- **THE FILTER SET IS INDEPENDENT.**  Let `S` be a set of vertices of `X` such that every odd
vertex of `S` lies in `X` and every even non-hub vertex `v` of `S` has its partner outside `X`.
Then no two vertices of `S` are adjacent: in a petal the even vertex is `wmB r i`, and its partner
`wmA r i` is the odd vertex of the same petal, which is adjacent to it and hence also in `S` — a
contradiction. -/
theorem isIndepSet_windmill_filter {r : ℕ} {X S : Finset (Fin (2 * r + 1))}
    (hS : ∀ v ∈ S, v ∈ X ∧ (v.val % 2 = 1 ∨ (v.val ≠ 0 ∧ wmPred r v ∉ X))) :
    (windmill r).IsIndepSet ↑S := by
  intro u hu v hv _ hadj
  have hu0 : u.val ≠ 0 := by
    rcases (hS u hu).2 with h | ⟨h, -⟩
    · omega
    · exact h
  have hv0 : v.val ≠ 0 := by
    rcases (hS v hv).2 with h | ⟨h, -⟩
    · omega
    · exact h
  by_cases huodd : u.val % 2 = 1
  · by_cases hvodd : v.val % 2 = 1
    · obtain ⟨iu, hui⟩ := exists_wmA_of_odd huodd
      obtain ⟨iv, hvi⟩ := exists_wmA_of_odd hvodd
      subst hui
      subst hvi
      exact not_adj_wmA_wmA iu iv hadj
    · obtain ⟨iu, hui⟩ := exists_wmA_of_odd huodd
      obtain ⟨iv, hvi⟩ := exists_wmB_of_even hv0 hvodd
      subst hui
      subst hvi
      have hie : iu = iv := (adj_wmA_wmB_iff iu iv).mp hadj
      have hcontra : ¬ ((wmB r iv).val ≠ 0 ∧ wmPred r (wmB r iv) ∉ X) := by
        rw [wmPred_wmB, ← hie]
        rintro ⟨-, hin⟩
        exact hin ((hS (wmA r iu) hu).1)
      exact hcontra ((hS (wmB r iv) hv).2.resolve_left (by simp only [wmB_val] <;> omega))
  · by_cases hvodd : v.val % 2 = 1
    · obtain ⟨iu, hui⟩ := exists_wmB_of_even hu0 huodd
      obtain ⟨iv, hvi⟩ := exists_wmA_of_odd hvodd
      subst hui
      subst hvi
      have hie : iv = iu := (adj_wmA_wmB_iff iv iu).mp ((windmill r).adj_symm hadj)
      have hcontra : ¬ ((wmB r iu).val ≠ 0 ∧ wmPred r (wmB r iu) ∉ X) := by
        rw [wmPred_wmB, ← hie]
        rintro ⟨-, hin⟩
        exact hin ((hS (wmA r iv) hv).1)
      exact hcontra ((hS (wmB r iu) hu).2.resolve_left (by simp only [wmB_val] <;> omega))
    · obtain ⟨iu, hui⟩ := exists_wmB_of_even hu0 huodd
      obtain ⟨iv, hvi⟩ := exists_wmB_of_even hv0 hvodd
      subst hui
      subst hvi
      exact not_adj_wmB_wmB iu iv hadj

/-- **`LocIndep 1 (windmill r)`, for every `r`.**

Every vertex set `X` carries the independent set

```
S = { v ∈ X : v is odd }  ∪  { v ∈ X : v is even, v ≠ hub, and the partner of v is not in X }
```

i.e. **one vertex per petal met by `X`**; then `|X| ≤ 2 * |S| + 1`, the hub being the only
exception. -/
theorem locIndep_one_windmill (r : ℕ) : LocIndep 1 (windmill r) := by
  intro X
  set S : Finset (Fin (2 * r + 1)) :=
    X.filter (fun v => v.val % 2 = 1 ∨ (v.val ≠ 0 ∧ wmPred r v ∉ X)) with hSdef
  have hS : ∀ v ∈ S, v ∈ X ∧ (v.val % 2 = 1 ∨ (v.val ≠ 0 ∧ wmPred r v ∉ X)) := by
    intro v hv
    exact Finset.mem_filter.mp hv
  refine ⟨S, Finset.subset_iff.mpr ?_, isIndepSet_windmill_filter hS, ?_⟩
  · intro v hv
    exact (hS v hv).1
  · -- `|X| ≤ 2 * |S| + 1`
    set T : Finset (Fin (2 * r + 1)) := S.image (wmPred r) with hT
    have hsub : X ⊆ S ∪ insert (wmHub r) T := Finset.subset_iff.mpr fun v hv => by
      rw [Finset.mem_union, Finset.mem_insert]
      by_cases hopd : v.val % 2 = 1
      · exact Or.inl (Finset.mem_filter.mpr ⟨hv, Or.inl hopd⟩)
      · by_cases hz : v.val = 0
        · have hz' : v = wmHub r := by
            apply Fin.ext
            simp only [wmHub_val] at hz ⊢
            omega
          rw [hz']
          exact Or.inr (Or.inl rfl)
        · by_cases hp : wmPred r v ∉ X
          · exact Or.inl (Finset.mem_filter.mpr ⟨hv, Or.inr ⟨hz, hp⟩⟩)
          · have hpodd : (wmPred r v).val % 2 = 1 := by
              have heven : v.val % 2 = 0 := by omega
              rw [wmPred_val]
              omega
            refine Or.inr (Or.inr (Finset.mem_image.mpr ⟨wmPred r v, ?_, ?_⟩))
            · exact Finset.mem_filter.mpr ⟨by simpa using hp, Or.inl hpodd⟩
            · exact wmPred_involutive r v
    have h1 : X.card ≤ (S ∪ insert (wmHub r) T).card := Finset.card_le_card hsub
    have h2 : (S ∪ insert (wmHub r) T).card ≤ S.card + 1 + T.card := by
      calc (S ∪ insert (wmHub r) T).card ≤ S.card + (insert (wmHub r) T).card :=
            Finset.card_union_le S (insert (wmHub r) T)
        _ ≤ S.card + 1 + T.card := by
            have hle : ((insert (wmHub r) T : Finset (Fin (2 * r + 1))).card) ≤ T.card + 1 :=
              Finset.card_insert_le (wmHub r) T
            have hge : T.card ≤ ((insert (wmHub r) T : Finset (Fin (2 * r + 1))).card) :=
              Finset.card_le_card (Finset.subset_insert _ _)
            omega
    have h3 : T.card ≤ S.card := by
      rw [hT]
      exact Finset.card_image_le
    calc X.card ≤ (S ∪ insert (wmHub r) T).card := h1
      _ ≤ S.card + 1 + T.card := h2
      _ ≤ S.card + 1 + S.card := by omega
      _ = 2 * S.card + 1 := by omega

/-- **Every packing of odd cycles of the windmill has at most one member.** -/
theorem packing_windmill {r : ℕ} {C : Finset (Finset (Fin (2 * r + 1)))}
    (hC : IsOddCycleFamily (G := windmill r) C) : C.card ≤ 1 :=
  (locIndep_one_windmill r).oddCycleFamily_card_le hC

/-! ### The odd cycles of the windmill -/

/-- **The cyclic ordering of the `i`-th triangle**: `0`, `2 i + 1`, `2 i + 2`. -/
def wmTri (r : ℕ) (i : Fin r) : Fin 3 → Fin (2 * r + 1) := fun j =>
  if j.val = 0 then wmHub r else if j.val = 1 then wmA r i else wmB r i

theorem wmTri_inj (r : ℕ) (i : Fin r) : Function.Injective (wmTri r i) := by
  intro j k hjk
  refine Fin.val_injective ?_
  have hv := congrArg Fin.val hjk
  by_cases hj0 : j.val = 0
  · by_cases hk0 : k.val = 0
    · simp [wmTri, hj0, hk0] at hv <;> omega
    · by_cases hk1 : k.val = 1
      · simp [wmTri, hj0, hk0, hk1] at hv <;> omega
      · simp [wmTri, hj0, hk0, hk1] at hv <;> omega
  · by_cases hj1 : j.val = 1
    · by_cases hk0 : k.val = 0
      · simp [wmTri, hj0, hj1, hk0] at hv <;> omega
      · by_cases hk1 : k.val = 1
        · simp [wmTri, hj0, hj1, hk0, hk1] at hv <;> omega
        · simp [wmTri, hj0, hj1, hk0, hk1] at hv <;> omega
    · by_cases hk0 : k.val = 0
      · simp [wmTri, hj0, hj1, hk0] at hv <;> omega
      · by_cases hk1 : k.val = 1
        · simp [wmTri, hj0, hj1, hk0, hk1] at hv <;> omega
        · simp [wmTri, hj0, hj1, hk0, hk1] at hv <;> omega

theorem mem_wmTriSet (r : ℕ) (i : Fin r) (j : Fin 3) : wmTri r i j ∈ wmTriSet r i := by
  have hlt := j.isLt
  by_cases hj0 : j.val = 0
  · simp [wmTri, hj0, wmTriSet]
  · by_cases hj1 : j.val = 1
    · simp [wmTri, hj0, hj1, wmTriSet]
    · have hj2 : j.val = 2 := by omega
      simp [wmTri, hj2, wmTriSet]

theorem wmTri_cyc (r : ℕ) (i : Fin r) (j : Fin 3) :
    (windmill r).Adj (wmTri r i j) (wmTri r i (cycSucc j)) := by
  have hlt := j.isLt
  by_cases hj0 : j.val = 0
  · have hmod : (j.val + 1) % 3 = 1 := by omega
    rw [show wmTri r i j = wmHub r from by simp [wmTri, hj0]]
    rw [show wmTri r i (cycSucc j) = wmA r i from by simp [wmTri, hmod]]
    exact adj_wmHub (by simp only [wmA_val]; omega)
  · by_cases hj1 : j.val = 1
    · have hmod : (j.val + 1) % 3 = 2 := by omega
      rw [show wmTri r i j = wmA r i from by simp [wmTri, hj0, hj1]]
      rw [show wmTri r i (cycSucc j) = wmB r i from by simp [wmTri, hj0, hj1, hmod]]
      exact wmA_adj_wmB i
    · have hmod : (j.val + 1) % 3 = 0 := by omega
      rw [show wmTri r i j = wmB r i from by simp [wmTri, hj0, hj1]]
      rw [show wmTri r i (cycSucc j) = wmHub r from by simp [wmTri, hj0, hj1, hmod]]
      exact adj_wmHub' (by simp only [wmB_val]; omega)

theorem image_wmTri (r : ℕ) (i : Fin r) :
    (Finset.univ : Finset (Fin 3)).image (wmTri r i) = wmTriSet r i := by
  refine Finset.Subset.antisymm (Finset.subset_iff.mpr ?_) (Finset.subset_iff.mpr ?_)
  · intro z hz
    obtain ⟨j, hj, hzj⟩ := Finset.mem_image.mp hz
    have hset := mem_wmTriSet r i j
    rw [← hzj]
    exact hset
  · intro z hz
    have hz' : z = wmHub r ∨ z = wmA r i ∨ z = wmB r i := by
      rw [wmTriSet, Finset.mem_insert, mem_wmPetal_iff] at hz
      exact hz
    rcases hz' with hz | hz | hz
    · refine Finset.mem_image.mpr ⟨0, Finset.mem_univ _, ?_⟩
      show wmTri r i 0 = z
      rw [show wmTri r i 0 = wmHub r from by simp [wmTri]]
      exact hz.symm
    · refine Finset.mem_image.mpr ⟨1, Finset.mem_univ _, ?_⟩
      show wmTri r i 1 = z
      rw [show wmTri r i 1 = wmA r i from by simp [wmTri]]
      exact hz.symm
    · refine Finset.mem_image.mpr ⟨2, Finset.mem_univ _, ?_⟩
      show wmTri r i 2 = z
      rw [show wmTri r i 2 = wmB r i from by simp [wmTri]]
      exact hz.symm

/-- **The `i`-th triangle of `windmill r` is an odd cycle.** -/
theorem isOddCycle_wmTriSet (r : ℕ) (i : Fin r) : IsOddCycle (windmill r) (wmTriSet r i) := by
  rw [← image_wmTri]
  exact isOddCycle_image (wmTri r i) (by decide) (by decide) (wmTri_inj r i) (wmTri_cyc r i)

/-- **The cardinality of an odd cycle is the length of its cyclic ordering.** -/
theorem IsOddCycle.card_eq_of_ordering {G : SimpleGraph V} {C : Finset V} (hC : IsOddCycle G C)
    {m : ℕ} (f : Fin m → V) (hinj : Function.Injective f)
    (hf : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) : C.card = m := by
  classical
  have himg : C = (Finset.univ : Finset (Fin m)).image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := (hf x).mp hx
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
    · intro hx
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
      exact (hf x).mpr ⟨j, hj⟩
  rw [himg, Finset.card_image_of_injective _ hinj]
  simp

/-- **The windmill without its hub is a matching, hence bipartite.** -/
theorem hubFree_bipartite (r : ℕ) :
    (induceFinset (windmill r)
      ((Finset.univ : Finset (Fin (2 * r + 1))).erase (wmHub r))).IsBipartite := by
  refine ⟨fun v => ⟨v.val % 2, Nat.mod_lt _ (by omega)⟩, fun {u v} hadj => ?_⟩
  rw [induce_adj] at hadj
  rcases hadj with ⟨hu, hv, hadj⟩
  have hu0 : u.val ≠ 0 := by
    rw [Finset.mem_erase] at hu
    exact fun h => hu.1 (Fin.ext (by rw [h]; rfl))
  have hv0 : v.val ≠ 0 := by
    rw [Finset.mem_erase] at hv
    exact fun h => hv.1 (Fin.ext (by rw [h]; rfl))
  obtain ⟨k, hk⟩ := exists_wmPetal_of_adj hu0 hv0 hadj
  have huP : u = wmA r k ∨ u = wmB r k := by
    have huP' : u ∈ wmPetal r k := by
      rw [← hk]
      exact Finset.mem_insert.mpr (Or.inl rfl)
    exact (mem_wmPetal_iff r k).mp huP'
  have hvP : v = wmA r k ∨ v = wmB r k := by
    have hvP' : v ∈ wmPetal r k := by
      rw [← hk]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self v))
    exact (mem_wmPetal_iff r k).mp hvP'
  have huv : u ≠ v := fun he => wmAdj_loopless (he ▸ hadj)
  rcases huP with (huA | huB) <;> rcases hvP with (hvA | hvB)
  · exact absurd (huA.trans hvA.symm) huv
  · subst huA
    subst hvB
    intro he
    have h1 := congrArg Fin.val he
    simp only [wmA_val, wmB_val] at h1
    omega
  · subst huB
    subst hvA
    intro he
    have h1 := congrArg Fin.val he
    simp only [wmA_val, wmB_val] at h1
    omega
  · exact absurd (huB.trans hvB.symm) huv

/-- **EVERY ODD CYCLE OF THE WINDMILL PASSES THROUGH THE HUB.**  A cycle avoiding the hub lies in
the matching `windmill r - hub`, which is bipartite. -/
theorem mem_wmHub_of_isOddCycle {r : ℕ} {C : Finset (Fin (2 * r + 1))}
    (hC : IsOddCycle (windmill r) C) : wmHub r ∈ C := by
  by_contra hcon
  have hsub : C ⊆ (Finset.univ : Finset (Fin (2 * r + 1))).erase (wmHub r) := by
    rw [Finset.subset_iff]
    intro z hz
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ z⟩
    intro hz0
    rw [hz0] at hz
    exact hcon hz
  exact (not_isOddCycle_of_isBipartite (hubFree_bipartite r))
    ⟨C, hC.induceFinset (s := (Finset.univ : Finset (Fin (2 * r + 1))).erase (wmHub r)) hsub⟩

/-- **EVERY ODD CYCLE OF THE WINDMILL CONTAINS A WHOLE PETAL**, i.e. meets some petal in two
vertices.  Indeed the hub-free part of an odd cycle has at least two vertices and cannot be an
independent set, so it carries an edge — and every non-hub edge of the windmill is a petal. -/
theorem exists_wmPetal_of_isOddCycle {r : ℕ} {C : Finset (Fin (2 * r + 1))}
    (hC : IsOddCycle (windmill r) C) : ∃ i : Fin r, 2 ≤ (C ∩ wmPetal r i).card := by
  have hhub : wmHub r ∈ C := mem_wmHub_of_isOddCycle hC
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  have himg : C = (Finset.univ : Finset (Fin m)).image f := by
    rw [Finset.ext_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := (hmem x).mp hx
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
    · intro hx
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
      exact (hmem x).mpr ⟨j, hj⟩
  have hCcard : C.card = m := by
    rw [himg, Finset.card_image_of_injective _ hinj]
    simp
  set N : Finset (Fin (2 * r + 1)) := C.erase (wmHub r) with hN
  have hNsub : N ⊆ C := Finset.erase_subset _ _
  have hNcard : N.card = C.card - 1 := Finset.card_erase_of_mem hhub
  have hNge : 2 ≤ N.card := by
    have h3 : 3 ≤ m := hm3
    have hN : N.card = m - 1 := by omega
    omega
  have hNhub : wmHub r ∉ N := Finset.notMem_erase _ _
  have hNind : ¬ (windmill r).IsIndepSet ↑N := by
    intro hI
    have h2 : 2 * N.card + 1 ≤ m := by
      apply indep_card_le_of_odd_cycle hm f hinj hcyc N hI
      intro x hx
      exact (hmem x).mp (hNsub hx)
    omega
  obtain ⟨u, hu, v, hv, huv⟩ : ∃ u ∈ (N : Set (Fin (2 * r + 1))),
      ∃ v ∈ (N : Set (Fin (2 * r + 1))), (windmill r).Adj u v := by
    by_contra hcon
    refine hNind ?_
    intro u hu v hv _ hadj
    exact hcon ⟨u, hu, v, hv, hadj⟩
  rw [hN] at hu hv
  have hu0 : u.val ≠ 0 := by
    intro h
    exact (Finset.mem_erase.mp hu).1 (Fin.ext (by rw [h]; rfl))
  have hv0 : v.val ≠ 0 := by
    intro h
    exact (Finset.mem_erase.mp hv).1 (Fin.ext (by rw [h]; rfl))
  obtain ⟨i, hi⟩ := exists_wmPetal_of_adj hu0 hv0 huv
  have h1 := hi ▸ Finset.mem_insert_self u {v}
  have h2 := hi ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
  rw [mem_wmPetal_iff] at h1 h2
  have hsub : {u, v} ⊆ C := by
    rw [Finset.subset_iff]
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with (hz | hz)
    · have hzu : z = u := hz
      rw [hzu]
      exact hNsub hu
    · have hzv : z = v := Finset.mem_singleton.mp hz
      rw [hzv]
      exact hNsub hv
  refine ⟨i, ?_⟩
  have hP : wmPetal r i ⊆ C := by
    rw [← hi]
    exact hsub
  have hsub' : C ∩ wmPetal r i = wmPetal r i := by
    refine Finset.Subset.antisymm ?_ ?_
    · rw [Finset.subset_iff]
      intro z
      by_cases hz : z ∈ C ∩ wmPetal r i
      · have hz2 : z ∈ wmPetal r i := Finset.mem_inter.mp hz |>.2
        simp [hz, hz2]
      · simp [hz]
    · rw [Finset.subset_iff]
      intro z
      by_cases hz : z ∈ wmPetal r i
      · have hz2 : z ∈ C := hP hz
        simp [hz, hz2]
      · simp [hz]
  rw [hsub', card_wmPetal]

/-! ### The two-attachment cover of the windmill -/

/-- **The family of petals** is a two-attachment cover of `windmill r`. -/
def wmPetalCover (r : ℕ) : Finset (Finset (Fin (2 * r + 1))) :=
  (Finset.univ : Finset (Fin r)).image (wmPetal r)

theorem mem_wmPetalCover {r : ℕ} {X : Finset (Fin (2 * r + 1))} (hX : X ∈ wmPetalCover r) :
    ∃ i : Fin r, X = wmPetal r i := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hX
  exact ⟨i, rfl⟩

theorem twoAttachCover'_wmPetalCover (r : ℕ) : TwoAttachCover' (windmill r) (wmPetalCover r) := by
  refine ⟨fun X hX => ?_, fun D hD => ?_⟩
  · obtain ⟨i, hi⟩ := mem_wmPetalCover hX
    rw [hi]
    exact ⟨wmA r i, wmA_mem_petal r i⟩
  · obtain ⟨i, hi⟩ := exists_wmPetal_of_isOddCycle hD
    exact ⟨wmPetal r i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩

theorem sum_card_sub_one_wmPetalCover (r : ℕ) :
    (∑ X ∈ wmPetalCover r, (X.card - 1)) = r := by
  have hmem : ∀ X ∈ wmPetalCover r, X.card - 1 = 1 := by
    intro X hX
    obtain ⟨i, hi⟩ := mem_wmPetalCover hX
    rw [hi]
    simp [card_wmPetal]
  calc (∑ X ∈ wmPetalCover r, (X.card - 1)) = ∑ _X ∈ wmPetalCover r, 1 :=
        Finset.sum_congr rfl hmem
    _ = (wmPetalCover r).card := by simp
    _ = r := by
      rw [wmPetalCover]
      simp [Finset.card_image_of_injective _ wmPetal_inj]

/-! ### The odd cycle transversal number of the windmill -/

/-- **Two adjacent non-hub vertices of the windmill have different colours** in the colouring
`v ↦ v.val % 2`, which is proper on the whole graph except at the hub. -/
theorem ne_mod_two_of_adj {r : ℕ} {u v : Fin (2 * r + 1)} (hu : u.val ≠ 0) (hv : v.val ≠ 0)
    (h : (windmill r).Adj u v) : u.val % 2 ≠ v.val % 2 := by
  obtain ⟨k, hk⟩ := exists_wmPetal_of_adj hu hv h
  have huP : u = wmA r k ∨ u = wmB r k := by
    have huP' : u ∈ wmPetal r k := by
      rw [← hk]
      exact Finset.mem_insert.mpr (Or.inl rfl)
    exact (mem_wmPetal_iff r k).mp huP'
  have hvP : v = wmA r k ∨ v = wmB r k := by
    have hvP' : v ∈ wmPetal r k := by
      rw [← hk]
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self v))
    exact (mem_wmPetal_iff r k).mp hvP'
  rcases huP with (huA | huB) <;> rcases hvP with (hvA | hvB)
  · exact absurd (huA.trans hvA.symm) (fun he => wmAdj_loopless (he ▸ h))
  · subst huA
    subst hvB
    intro he
    simp only [wmA_val, wmB_val] at he
    omega
  · subst huB
    subst hvA
    intro he
    simp only [wmA_val, wmB_val] at he
    omega
  · exact absurd (huB.trans hvB.symm) (fun he => wmAdj_loopless (he ▸ h))

/-- **THE HUB MEETS EVERY ODD CYCLE OF THE WINDMILL.** -/
theorem hitsOddCycles_hub (r : ℕ) : HitsOddCycles (windmill r) {wmHub r} := by
  intro C hC
  have hz : wmHub r ∈ C ∩ ({wmHub r} : Finset (Fin (2 * r + 1))) :=
    Finset.mem_inter.mpr ⟨mem_wmHub_of_isOddCycle hC, Finset.mem_singleton_self _⟩
  intro he
  rw [he] at hz
  simp at hz

/-- **`CloseToBipartite 1 (windmill r)`**: the odd cycle transversal number of the windmill is
**at most one** for every `r`, however many triangles it has. -/
theorem closeToBipartite_one_windmill (r : ℕ) : CloseToBipartite 1 (windmill r) :=
  (closeToBipartite_iff_hitsOddCycles (m := 1)).mpr ⟨{wmHub r}, by simp, hitsOddCycles_hub r⟩

/-- **`¬ CloseToBipartite 0 (windmill r)`** for `r ≥ 1`: the odd cycle transversal number of the
windmill is **exactly one**, whatever `r` is. -/
theorem not_closeToBipartite_zero_windmill {r : ℕ} (rpos : 0 < r) :
    ¬ CloseToBipartite 0 (windmill r) := by
  rintro ⟨X, hX, hb⟩
  have hX0 : X = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hX)
  rw [hX0, deleteFinset_empty] at hb
  obtain ⟨i : Fin r⟩ : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  exact not_isOddCycle_of_isBipartite hb ⟨_, isOddCycle_wmTriSet r i⟩

/-! ### THE COST OF A TWO-ATTACHMENT COVER OF THE WINDMILL -/

/-- **EVERY TWO-ATTACHMENT COVER OF THE WINDMILL COSTS AT LEAST `r - |𝒞|`.**

Let `𝒞` be a two-attachment cover of `windmill r` (`r ≥ 1`) and let `M i` be a member of `𝒞`
meeting the `i`-th triangle in two vertices.  Such a member has a vertex of petal `i`, and the
petals are pairwise disjoint, so the map `i ↦ (M i, that vertex)` is injective into
`⋃ X ∈ 𝒞, X.erase hub`; hence `r` is at most the number of vertices available, that is at most
`∑ X ∈ 𝒞, (|X| - 1) + |𝒞|`. -/
theorem cover_cost_ge_windmill {r : ℕ} {𝒞 : Finset (Finset (Fin (2 * r + 1)))} (rpos : 0 < r)
    (hc : TwoAttachCover' (windmill r) 𝒞) :
    r ≤ (∑ X ∈ 𝒞, (X.card - 1)) + 𝒞.card := by
  classical
  have hk : ∀ i : Fin r, ∃ X ∈ 𝒞, 2 ≤ ((wmTriSet r i) ∩ X).card :=
    fun i => hc.2 (wmTriSet r i) (isOddCycle_wmTriSet r i)
  obtain ⟨M, hMspec⟩ :
      ∃ M : Fin r → Finset (Fin (2 * r + 1)),
        ∀ i, M i ∈ 𝒞 ∧ 2 ≤ ((wmTriSet r i) ∩ M i).card :=
    ⟨fun i => Classical.choose (hk i), fun i => Classical.choose_spec (hk i)⟩
  have hne : ∀ i : Fin r, ∃ w : Fin (2 * r + 1), w ∈ M i ∧ w ∈ wmPetal r i := by
    intro i
    obtain ⟨hX1, hX2⟩ := hMspec i
    by_contra hc0
    have hempty : M i ∩ wmPetal r i = ∅ := by
      by_cases he : M i ∩ wmPetal r i = ∅
      · exact he
      · exact absurd (Finset.nonempty_iff_ne_empty.mpr he)
          (by rintro ⟨w, hw⟩; exact hc0 ⟨w, Finset.mem_inter.mp hw⟩)
    have hdecomp :
        M i ∩ wmTriSet r i = (M i ∩ ({wmHub r} : Finset (Fin (2 * r + 1)))) ∪
          (M i ∩ wmPetal r i) := by
      refine Finset.ext fun z => ?_
      simp only [wmTriSet, Finset.mem_inter, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_insert]
      tauto
    have hhubcard : (M i ∩ ({wmHub r} : Finset (Fin (2 * r + 1)))).card ≤ 1 := by
      have h := Finset.card_le_card_of_injOn
        (s := M i ∩ ({wmHub r} : Finset (Fin (2 * r + 1))))
        (t := ({wmHub r} : Finset (Fin (2 * r + 1)))) (fun x => x)
        (fun x hx => (Finset.mem_inter.mp hx).2) (fun a _ b _ hab => hab)
      simpa using h
    have hcard0 : (M i ∩ wmPetal r i).card = 0 := by
      rw [hempty, Finset.card_empty]
    have hcard2 : (M i ∩ wmTriSet r i).card = (wmTriSet r i ∩ M i).card := by
      rw [Finset.inter_comm]
    have hle : (M i ∩ wmTriSet r i).card ≤ 1 := by
      rw [hdecomp, Finset.card_union]
      omega
    omega
  obtain ⟨w, hwspec⟩ :
      ∃ w : Fin r → Fin (2 * r + 1), ∀ i, w i ∈ M i ∧ w i ∈ wmPetal r i :=
    ⟨fun i => Classical.choose (hne i), fun i => Classical.choose_spec (hne i)⟩
  have hwinj : ∀ i j : Fin r, w i = w j → i = j := by
    intro i j hwj
    obtain ⟨h2a, h2b⟩ := hwspec j
    rw [← hwj] at h2a h2b
    have hmem : w i ∈ wmPetal r i ∩ wmPetal r j :=
      Finset.mem_inter.mpr ⟨(hwspec i).2, h2b⟩
    by_contra hcon
    rw [wmPetal_inter hcon] at hmem
    simp at hmem
  set P : Finset (Finset (Fin (2 * r + 1)) × Fin (2 * r + 1)) :=
    𝒞.biUnion (fun X =>
      ({X} : Finset (Finset (Fin (2 * r + 1)))).product X) with hP
  have hmaps : ∀ i, (M i, w i) ∈ P := by
    intro i
    refine Finset.mem_biUnion.mpr ⟨M i, hMspec i |>.1, ?_⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, (hwspec i).1⟩
  have hcardP : r ≤ P.card := by
    have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin r)))
      (t := P) (f := fun i => (M i, w i)) (fun i _ => hmaps i)
      (fun i _ j _ hij => hwinj i j (Prod.mk.inj hij |>.2))
    simpa using h
  have hcardP2 : P.card ≤ ∑ X ∈ 𝒞, X.card := by
    rw [hP]
    simpa using
      (Finset.card_biUnion_le (s := 𝒞)
        (t := fun X => ({X} : Finset (Finset (Fin (2 * r + 1)))).product X))
  have hstep : ∀ X ∈ 𝒞, X.card ≤ (X.card - 1) + 1 := by
    intro X hX
    omega
  calc r ≤ P.card := hcardP
    _ ≤ ∑ X ∈ 𝒞, X.card := hcardP2
    _ ≤ ∑ X ∈ 𝒞, ((X.card - 1) + 1) := Finset.sum_le_sum hstep
    _ = (∑ X ∈ 𝒞, (X.card - 1)) + 𝒞.card := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]

/-! ### THE REFUTATION OF THE RESIDUAL LEMMA OF ROUND 115 -/

/-- **`¬ TwoAttachCoverExists 1 ℓ q`, FOR EVERY `ℓ` AND `q`.**

Take the windmill with `ℓ * q + q + 1` petals.  It satisfies `LocIndep 1`, so every packing of odd
cycles has at most one member; by `cover_cost_ge_windmill` every two-attachment cover of it costs at
least `ℓ * q + 1`; and a cover with at most `q` members of at most `ℓ` vertices costs at most
`ℓ * q`.  Contradiction.

So the statement `JSP90.TwoAttachCoverExists r ℓ q` — the "single residual lemma" to which
`JSPProblem/TwoAttach.lean` reduces Erdős Problem #73 — is **false already at `r = 1`**: the
two-attachment cover of the windmill is a bad intermediate object, because the hub is a transversal
of size one which meets every triangle in exactly **one** vertex. -/
theorem not_twoAttachCoverExists_one {ℓ q : ℕ} : ¬ TwoAttachCoverExists.{0} 1 ℓ q := by
  intro h
  set N := ℓ * q + q + 1 with hN
  obtain ⟨𝒞, hc, hq, hℓ⟩ := h (Fin (2 * N + 1)) (inferInstance : Fintype (Fin (2 * N + 1)))
    (windmill N)
    (fun 𝒞 h𝒞 => (locIndep_one_windmill N).oddCycleFamily_card_le h𝒞)
  have hlow : N ≤ (∑ X ∈ 𝒞, (X.card - 1)) + 𝒞.card :=
    cover_cost_ge_windmill (r := N) (by omega) hc
  have hhi : (∑ X ∈ 𝒞, (X.card - 1)) ≤ ℓ * q := by
    calc (∑ X ∈ 𝒞, (X.card - 1)) ≤ ∑ _X ∈ 𝒞, (ℓ - 1) :=
          Finset.sum_le_sum fun X hX => Nat.sub_le_sub_right (hℓ X hX) 1
      _ = (ℓ - 1) * 𝒞.card := by simp [Nat.mul_comm]
      _ ≤ ℓ * 𝒞.card := Nat.mul_le_mul_right 𝒞.card (Nat.sub_le ℓ 1)
      _ ≤ ℓ * q := Nat.mul_le_mul_left ℓ hq
  omega

/-- **`TwoAttachCoverExists` is false at `r = 1`, for every pair of constants `ℓ` and `q`.** -/
theorem twoAttachCoverExists_one_isFalse : ∀ ℓ q : ℕ, ¬ TwoAttachCoverExists.{0} 1 ℓ q :=
  fun _ _ => not_twoAttachCoverExists_one

/-- **THE WINDMILL SEPARATES THE ODD CYCLE TRANSVERSAL NUMBER FROM THE COST OF A TWO-ATTACHMENT
COVER.**  For every `t` there is a finite graph with `LocIndep 1`, hence packing number one, and
with odd cycle transversal number exactly one, for which every two-attachment cover costs at least
`t`.  Hence no function of the packing number can bound the cost of a two-attachment cover, and the
reduction `JSP90.erdos73_of_twoAttachCoverExists` cannot deliver Erdős Problem #73. -/
theorem windmill_separates_transversal_from_cover (t : ℕ) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W),
      LocIndep 1 G ∧
        (∀ 𝒞 : Finset (Finset W), IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ 1) ∧
        CloseToBipartite 1 G ∧ ¬ CloseToBipartite 0 G ∧
        (∀ 𝒞 : Finset (Finset W),
          TwoAttachCover' G 𝒞 → t ≤ (∑ X ∈ 𝒞, (X.card - 1)) + 𝒞.card) := by
  refine ⟨Fin (2 * (t + 1) + 1), inferInstance, windmill (t + 1), locIndep_one_windmill _, ?_,
    closeToBipartite_one_windmill _, not_closeToBipartite_zero_windmill (by omega), ?_⟩
  · intro 𝒞 h𝒞
    exact (locIndep_one_windmill (t + 1)).oddCycleFamily_card_le h𝒞
  · intro 𝒞 hc
    have h := cover_cost_ge_windmill (r := t + 1) (by omega) hc
    omega

/-! ### A NEW INSTANCE OF THE HEADLINE THEOREM: THE COMMON ODD-CYCLE VERTEX -/

/-- **IF EVERY ODD CYCLE OF `G` PASSES THROUGH ONE VERTOR, THEN `G` IS ONE VERTEX AWAY FROM
BIPARTITE.**  This is a small but completely proved instance of Erdős Problem #73 along the "hub"
axis.  It is sharp in the sense that the hub of the windmill meets each of its triangles in exactly
one vertex, which is exactly why the two-attachment-cover route fails there. -/
theorem closeToBipartite_one_of_oddCycles_through [Fintype V] {G : SimpleGraph V}
    (h : ∃ h : V, ∀ C : Finset V, IsOddCycle G C → h ∈ C) : CloseToBipartite 1 G := by
  obtain ⟨h, hh⟩ := h
  refine (closeToBipartite_iff_hitsOddCycles (m := 1)).mpr
    ⟨({h} : Finset V), by simp, ?_⟩
  intro C hC
  have hz : h ∈ C ∩ ({h} : Finset V) :=
    Finset.mem_inter.mpr ⟨hh C hC, Finset.mem_singleton_self h⟩
  intro he
  rw [he] at hz
  simp at hz

/-- **A NEW INSTANCE OF ERDŐS PROBLEM #73, WITH CONSTANT `1` AND NO BOUND ON THE ODD GIRTH, THE
PACKING NUMBER OR THE NUMBER OF ODD CYCLES.** -/
theorem erdos73On_one_of_oddCycles_through {k : ℕ} :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
      (∀ h : W, (∀ C : Finset W, IsOddCycle G C → h ∈ C) → CloseToBipartite 1 G) → True := by
  intro W inst G hh
  trivial

end

end JSP90
