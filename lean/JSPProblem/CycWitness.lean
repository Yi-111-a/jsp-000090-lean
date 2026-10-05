/-
# `JSPProblem/CycWitness.lean` — the witness lemma for **any** odd cycle of length `≥ 5`, and the
# EIGHT-VERTEX SEVEN-CYCLE INSTANCE of Erdős #73

Round 171 proved `JSP90.triCaseEight`, the triangle case at `|V| ≤ 8`, and with it the first
eight-vertex instance of the headline theorem
(`JSP90.closeToBipartite_two_of_shortest_three_of_locIndep_one_card_le_eight`).  The two remaining
cases at order eight are the five-cycle case (the residue of a shortest odd five-cycle is three
points, and the round-152–162 counting needs `|V \ C| ≤ 2`) and the **seven-cycle case**.

This file closes the seven-cycle case, and it does so by removing the five-position hypothesis from
rounds 152–162 entirely.

## What was order-bound before

The witness machinery of `lean/JSPProblem/FiveWitness.lean` is stated on `Fin 5`:
`JSP90.WitnessSet`, `JSP90.card_witness_le_one`, `JSP90.filter_adj_C_eq_ringPair`,
`JSP90.filter_adj_eq_of_fiveCycle_singleton` and `JSP90.x_ne_y_of_two_fiveCycles_singleton`.  Only
two things in that chain are really about five:

* `JSP90.five_flip_false` / `JSP90.five_pair_inj'`, pure arithmetic on `Fin 5`;
* `JSP90.card_neighIn_five_eq_two`, which used *triangle-freeness* to make `D = (C \ {c}) u {x}` carry
  no chord.

Neither survives verbatim at length seven, but both are replaceable:

* `JSP90.neigh_eq_of_adj_of_adj` and `JSP90.card_neighIn_C_eq_two` of
  `lean/JSPProblem/Seven.lean` are already **order-free** — "a shortest odd cycle is induced", hence
  every vertex of it has exactly two neighbours inside it.  Since `|D| = |C|` for the cycle `D` of
  this file, `D` is a shortest odd cycle too (`JSP90.hshort_of_card_eq`), so the *same* two lemmas
  apply to `D` and no triangle-freeness hypothesis is needed at all;
* the flip case needs `m ∣ 4`, i.e. `m ≥ 5`; `JSP90.cyc_flip_false_seven` and
  `JSP90.ring_pair_inj_seven` are the `Fin 7` instances, proved by `omega` exactly as
  `JSP90.five_flip_false` / `JSP90.five_pair_inj'` were.

## Part 0–2 — the generic chain

* **`JSP90.hshort_of_card_eq`** — if `C` is a shortest odd cycle and `E.card = C.card` with `E` an odd
  cycle, then `E` is a shortest odd cycle.
* **`JSP90.filter_adj_C_eq_ringPair_of_five_le`** — **for a shortest odd cycle of ANY length
  `≥ 5`, the neighbours of `o.f j` inside the cycle are exactly its two ring-neighbours.**  This is
  round 152's `filter_adj_C_eq_ringPair` with the `5` deleted.
* **`JSP90.filter_adj_eq_of_cycle_singleton`** — **if `(C \ {c}) u {x}` is an odd cycle of the same
  cardinality as the shortest odd cycle `C`, then `x` has exactly the same neighbourhood inside `C`
  as `c`.**  Round 152's `filter_adj_eq_of_fiveCycle_singleton`, with the triangle-freeness hypothesis
  replaced by "a shortest odd cycle is induced" (`|D| = |C| ⟹ D` is shortest) and with `C \ {c}`
  allowed to have `|C| - 1` elements.
* **`JSP90.x_ne_y_of_two_sevenCycles_singleton`** — **THE WITNESS IS INJECTIVE, FOR ANY CYCLE LENGTH
  `≥ 5`**: two different points of `C`, each missed by a cycle of the form `(C \ {·}) u {·}`, are
  missed by cycles with different outside vertices.
* **`JSP90.card_missedSeven_le_card_univ_sdiff`** — **the points of `C` missed that way inject into
  `V \ C`**: `|Missed| ≤ |V \ C|`, order-free.  With `|V \ C| ≤ 2` this recovers round 152's
  `JSP90.card_missed_le_two_of_card_le_seven`.

## Part 3–4 — THE INSTANCE: one point of a shortest odd seven-cycle meets every odd cycle

At `LocIndep 1` and `|V| ≤ 8`, let `C` be a shortest odd cycle with `|C| = 7`.  Every odd cycle `D` of
`G` has `7 ≤ |D|` (shortestness), `|D|` odd and `|D| ≤ 8`, so `|D| = 7`; and `D ≠ C` forces
`D \ C ≠ ∅`, hence `|D \ C| = 1` and `|C \ D| = 1`.  So **every missed point of `C` is missed by a
cycle of the form `(C \ {c}) u {x}`**, i.e. `AllMissed ⊆ Missed`, and Part 2 bounds

```lean
|{c ∈ C : some odd cycle misses c}|  ≤  |V \ C|  =  |V| - |C|  ≤  1  <  7 = |C|
```

so some point of `C` meets every odd cycle:

* **`JSP90.hitsOddCycles_singleton_of_shortest_seven_of_card_le_add_one`**;
* **`JSP90.closeToBipartite_one_of_shortest_seven_of_card_le_add_one` — A NEW INSTANCE OF THE
  HEADLINE THEOREM WITH THE OPTIMAL CONSTANT `1`, for a shortest odd cycle of length seven with
  `|V| ≤ |C| + 1`** (no `LocIndep` hypothesis, no packing hypothesis, no triangle-freeness);
* **`JSP90.closeToBipartite_one_of_shortest_seven_of_card_le_eight`**,
  **`JSP90.closeToBipartite_one_of_locIndep_one_card_le_eight_of_oddGirth_ge_seven` and
  **`JSP90.erdos73On_one_oddGirth_ge_seven_eight` — THE EIGHT-VERTEX ODD-GIRTH-AT-LEAST-SEVEN
  INSTANCE**, with the transversal and `tauOdd` forms and the sharpness of the constant `1`.

## What is *not* proved

The eight-vertex **five-cycle** case: `C` a shortest odd five-cycle and `|V| = 8` leaves a residue of
three points, `Missed` can then have three elements and the three-intersection five-cycle is no
longer unique (measured: up to six of them, and `|AllMissed| = 5` occurs in `110` of the `3 051 680`
measured graphs, so the certificate can no longer be a *single* point of `C`).  The certificate there
is a *pair*, and the measurement says a pair of points of `C` always works
(`discovery/JSP-000090/r172.c`, `0` failures).

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]`.
-/

import JSPProblem.FiveCount

namespace JSP90

universe u

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 4000000

local instance cwDecidableAdjRel (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

local instance cwDecidableEq : DecidableEq V := Classical.decEq V

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Part 0 — an odd cycle of the same cardinality as a shortest one is shortest -/

/-- **AN ODD CYCLE OF THE SAME CARDINALITY AS A SHORTEST ODD CYCLE IS A SHORTEST ODD CYCLE.**

This is what lets the generic chain of Part 2 be applied to `D = (C \ {c}) ∪ {x}`, which has the same
number of vertices as `C` but is a *different* odd cycle: at `|D| = |C|` the two minimality
statements coincide. -/
theorem hshort_of_card_eq {C E : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (hCE : IsOddCycle G E)
    (heq : E.card = C.card) : ∀ D : Finset V, IsOddCycle G D → E.card ≤ D.card := by
  intro D hD
  have h1 := hshort D hD
  omega

/-! ## Part 1 — the neighbours of a point of a shortest odd cycle, at ANY length `≥ 5` -/

/-- **THE NEIGHBOURS OF `o.f j` INSIDE A SHORTEST ODD CYCLE OF LENGTH `≥ 5` ARE EXACTLY ITS TWO
RING-NEIGHBOURS.**

```lean
IsOddCycle G C → C shortest odd → o : CycleOrder G C → 5 ≤ C.card →
  C.filter (fun z => G.Adj (o.f j) z) = {o.f (cycSucc j), o.f (o.prev j)}
```

Round 152's `JSP90.filter_adj_C_eq_ringPair` with the `5` deleted.  The whole content is
`JSP90.card_neighIn_C_eq_two` (every vertex of a shortest odd cycle has exactly two neighbours
inside it — order-free, `lean/JSPProblem/Seven.lean`) together with
`JSP90.neigh_eq_of_adj_of_adj` (two distinct neighbours exhaust that neighbourhood — also
order-free).  Two distinct ring-neighbours is `JSP90.CycleOrder.step_prev_ne`. -/
theorem filter_adj_C_eq_ringPair_of_five_le {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (o : CycleOrder G C)
    (hm5 : 5 ≤ C.card) (j : Fin o.m) :
    C.filter (fun z => G.Adj (o.f j) z) = ({o.f (cycSucc j), o.f (o.prev j)} : Finset V) := by
  have hcardC : C.card = o.m := card_eq_cyclicOrder o.f o.hinj o.hmem
  have hmemC : ∀ k : Fin o.m, o.f k ∈ C := fun k => (o.hmem (o.f k)).mpr ⟨k, rfl⟩
  have hne : o.f (cycSucc j) ≠ o.f (o.prev j) := o.step_prev_ne j
  have hsub : C.filter (fun z => G.Adj (o.f j) z) ⊆ {o.f (cycSucc j), o.f (o.prev j)} := by
    intro z hz
    have hzC : z ∈ C := (Finset.mem_filter.mp hz).1
    have hz' : G.Adj (o.f j) z := (Finset.mem_filter.mp hz).2
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact neigh_eq_of_adj_of_adj hC hshort (hmemC j) (hmemC _) (hmemC _) (o.hcyc j) (o.adj_prev j)
      hne z hzC hz'
  refine Finset.Subset.antisymm hsub ?_
  intro z hz
  rw [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hz | hz
  · rw [hz]; exact Finset.mem_filter.mpr ⟨hmemC _, o.hcyc j⟩
  · rw [hz]; exact Finset.mem_filter.mpr ⟨hmemC _, o.adj_prev j⟩

/-- **THE CARDINALITY OF `(C \ {c}) ∪ {x}`.** -/
theorem card_eq_of_union_sdiff_singleton {C : Finset V} {c x : V} (hc : c ∈ C) (hxn : x ∉ C)
    {D : Finset V} (hsub : (C \ {c}) ∪ {x} = D) : D.card = C.card := by
  have hunion : (C \ {c}) ∪ {c} = C := by
    apply Finset.Subset.antisymm
    · intro z hz
      rw [Finset.mem_union] at hz
      rcases hz with h | h
      · exact (Finset.mem_sdiff.mp h).1
      · rw [Finset.mem_singleton] at h
        subst h
        exact hc
    · intro z hz
      by_cases hzc : z = c
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr hzc))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr
          ⟨hz, fun h => hzc (Finset.mem_singleton.mp h)⟩))
  have hdis : Disjoint (C \ {c}) ({c} : Finset V) := by
    refine Finset.disjoint_left.2 fun z h1 h2 => ?_
    rw [Finset.mem_singleton] at h2
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_singleton.mpr h2)
  have hcard1 : (C \ {c}).card = C.card - 1 := by
    have h1 := Finset.card_union_of_disjoint hdis
    rw [hunion, Finset.card_singleton] at h1
    omega
  have hdisx : Disjoint (C \ {c}) ({x} : Finset V) := by
    refine Finset.disjoint_left.2 fun z h1 h2 => ?_
    rw [Finset.mem_singleton] at h2
    subst h2
    exact hxn (Finset.mem_sdiff.mp h1).1
  have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨c, hc⟩
  have h1 := Finset.card_union_of_disjoint hdisx
  rw [hsub, Finset.card_singleton, hcard1] at h1
  omega

/-! ## Part 2 — the bridge, at ANY cycle length `≥ 5`

`(C \ {c}) u {x}` being an odd cycle of the *same cardinality as* `C` makes `x` see `C` exactly as `c`
does.  The proof is round 152's, with the two order-bound inputs replaced by the order-free
`JSP90.card_neighIn_C_eq_two` applied to `D` (legitimate by `JSP90.hshort_of_card_eq`) and by the
absence of odd cycles shorter than `|C|` in place of triangle-freeness. -/

/-- **THE NEIGHBOURS OF `x` INSIDE `C` ARE THOSE OF `c` INSIDE `C`.**

```lean
IsOddCycle G C → C shortest odd → o : CycleOrder G C → 5 ≤ C.card →
  c ∈ C → x ∉ C → (C \ {c}) ∪ {x} an odd cycle of cardinality C.card →
    C.filter (Adj x) = C.filter (Adj c)
```

So if the `|C|` vertices `(C \ {c}) ∪ {x}` close up into an odd cycle, then `x` is adjacent to
**exactly** the two ring-neighbours of `c` in `C` and to nothing else of `C`. -/
theorem filter_adj_eq_of_cycle_singleton {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (o : CycleOrder G C)
    (hm5 : 5 ≤ C.card) {c x : V} (hc : c ∈ C) (hxn : x ∉ C)
    (hsub : (C \ {c}) ∪ {x} = D) (hD : IsOddCycle G D) (hDcard : D.card = C.card) :
    C.filter (fun z => G.Adj x z) = C.filter (fun z => G.Adj c z) := by
  obtain ⟨o', ho'⟩ := hD.cycleOrder
  have hcardC : C.card = o.m := card_eq_cyclicOrder o.f o.hinj o.hmem
  have hshortD : ∀ E : Finset V, IsOddCycle G E → D.card ≤ E.card :=
    hshort_of_card_eq hshort hD hDcard
  have hm5' : 5 ≤ o'.m := by
    have h1 : D.card = o'.m := card_eq_cyclicOrder o'.f o'.hinj o'.hmem
    rw [← h1, hDcard]
    exact hm5
  have hmemC : ∀ z : Fin o.m, o.f z ∈ C := fun z => (o.hmem (o.f z)).mpr ⟨z, rfl⟩
  have hxD : x ∈ D := by
    rw [← hsub]; exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self x))
  have hx2 : (D.filter (fun z => G.Adj x z)).card = 2 :=
    card_neighIn_C_eq_two hD hshortD hxD
  -- (1) every neighbour of `x` inside the cycle `D` is a neighbour of `c` inside `C`
  have hNx : D.filter (fun z => G.Adj x z) ⊆ C.filter (fun z => G.Adj c z) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyD, hxy⟩ := hy
    have hxy' : x ≠ y := fun h => G.irrefl (h ▸ hxy)
    have hyD' : y ∈ D := hyD
    rw [← hsub] at hyD
    rcases Finset.mem_union.mp hyD with hym | hym
    · have hyC : y ∈ C := (Finset.mem_sdiff.mp hym).1
      rw [Finset.mem_filter]
      refine ⟨hyC, ?_⟩
      obtain ⟨j, hj⟩ : ∃ j : Fin o.m, o.f j = y := (o.hmem y).mp hyC
      obtain ⟨k, hk⟩ : ∃ k : Fin o'.m, o'.f k = y := (o'.hmem y).mp hyD'
      have hy2 : (D.filter (fun z => G.Adj y z)).card = 2 :=
        card_neighIn_C_eq_two hD hshortD (by rw [← hk]; exact (o'.hmem _).mpr ⟨k, rfl⟩)
      by_contra hcon
      have hnc : ¬ G.Adj c y := fun h => hcon h
      have hnp : o.f (cycSucc j) ≠ c := fun h => hnc (by
        rw [← h, ← hj]; exact (o.hcyc j).symm)
      have hnq : o.f (o.prev j) ≠ c := fun h => hnc (by
        rw [← h, ← hj]; exact (o.adj_prev j).symm)
      have hnpq : o.f (cycSucc j) ≠ o.f (o.prev j) := o.step_prev_ne j
      have hset : ({x, o.f (cycSucc j), o.f (o.prev j)} : Finset V)
          ⊆ D.filter (fun z => G.Adj y z) := by
        intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with hz | hz
        · rw [hz]; exact Finset.mem_filter.mpr ⟨hxD, hxy.symm⟩
        · rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with hz | hz
          · rw [hz]
            exact Finset.mem_filter.mpr ⟨by
              rw [← hsub]
              exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hmemC _,
                fun h => hnp (Finset.mem_singleton.mp h)⟩)), by rw [← hj]; exact o.hcyc j⟩
          · rw [hz]
            exact Finset.mem_filter.mpr ⟨by
              rw [← hsub]
              exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr
                ⟨hmemC _, fun h => hnq (Finset.mem_singleton.mp h)⟩)),
              by rw [← hj]; exact o.adj_prev j⟩
      have hxn1 : x ∉ ({o.f (cycSucc j), o.f (o.prev j)} : Finset V) := by
        intro h
        rw [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact hxn (h ▸ hmemC _)
        · exact hxn (h ▸ hmemC _)
      have hxn2 : o.f (cycSucc j) ∉ ({o.f (o.prev j)} : Finset V) := by
        intro h
        rw [Finset.mem_singleton] at h
        exact hnpq h
      have h1 := Finset.card_le_card hset
      rw [Finset.card_insert_of_notMem hxn1, Finset.card_insert_of_notMem hxn2,
        Finset.card_singleton] at h1
      omega
    · rw [Finset.mem_singleton] at hym
      subst hym
      exact False.elim (G.irrefl hxy)
  -- (2) `x` is not adjacent to `c`: with a neighbour of `x` inside `D` that would close a triangle,
  -- and a triangle is an odd cycle shorter than `C`
  have hxnc : ¬ G.Adj x c := by
    intro hxc
    obtain ⟨z, hz⟩ := nonempty_of_card_pos (s := D.filter (fun z => G.Adj x z))
      (by rw [hx2]; omega)
    have hcz : G.Adj c z := (Finset.mem_filter.mp (hNx hz)).2
    have hxz : G.Adj x z := (Finset.mem_filter.mp hz).2
    have hodd : IsOddCycle G ({x, c, z} : Finset V) :=
      isOddCycle_of_isNClique_three (isNClique_three_of_adj_adj_adj hxc hxz hcz)
    have h1 := hshort ({x, c, z} : Finset V) hodd
    have h2 : ({x, c, z} : Finset V).card = 3 := (G.isNClique_iff.mp
      (isNClique_three_of_adj_adj_adj hxc hxz hcz)).2
    omega
  -- (3) neighbours of `x` inside `C` lie in `D`, and back
  have hforth : C.filter (fun z => G.Adj x z) ⊆ D.filter (fun z => G.Adj x z) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    obtain ⟨hzC, hzx⟩ := hz
    refine ⟨?_, hzx⟩
    have hzx' : x ≠ z := fun h => hxn (h ▸ hzC)
    have hzc' : z ≠ c := fun h => hxnc (h ▸ hzx)
    rw [← hsub]
    refine Finset.mem_union.mpr (Or.inl ?_)
    rw [Finset.mem_sdiff]
    exact ⟨hzC, by simpa using hzc'⟩
  have hback : D.filter (fun z => G.Adj x z) ⊆ C.filter (fun z => G.Adj x z) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    obtain ⟨hzD, hzx⟩ := hz
    have hzx' : x ≠ z := fun h => G.irrefl (h ▸ hzx)
    rw [← hsub] at hzD
    rcases Finset.mem_union.mp hzD with h | h
    · exact ⟨(Finset.mem_sdiff.mp h).1, hzx⟩
    · rw [Finset.mem_singleton] at h
      subst h
      exact False.elim (G.irrefl hzx)
  -- (4) both sets have two elements, so they are equal
  have hNcard : (C.filter (fun z => G.Adj c z)).card = 2 := card_neighIn_C_eq_two hC hshort hc
  have hEq : D.filter (fun z => G.Adj x z) = C.filter (fun z => G.Adj c z) :=
    Finset.eq_of_subset_of_card_le hNx (by rw [hNcard, ← hx2])
  refine Finset.Subset.antisymm ?_ ?_
  · intro z hz
    rw [← hEq]
    exact hforth hz
  · intro z hz
    rw [← hEq] at hz
    exact hback hz

/-! ## Part 2b — the two arithmetic lemmas at length seven

These are `JSP90.five_flip_false` and `JSP90.five_pair_inj'` with `5` replaced by `7`; the proof is
verbatim, `omega` closing the modular arithmetic.  The general statement is that the flip case forces
`7 ∣ 4`, i.e. it cannot happen for any cycle of length `≥ 5`. -/

/-- **THE FLIP CASE IMPOSSIBLE ON SEVEN POSITIONS.** -/
theorem cyc_flip_false_seven (i j : Fin 7) (h1 : cycSucc i = cycPred j) (h2 : cycPred i = cycSucc j) :
    False := by
  have hv1 := congrArg Fin.val h1
  have hv2 := congrArg Fin.val h2
  have hi : i.val < 7 := i.2
  have hj : j.val < 7 := j.2
  have hk (t : Fin 7) : (cycPred t).val = (t.val + 6) % 7 := by
    have h4 := cycSucc_pow_val (k := 6) (i := t) (n := 7)
    rw [cycPred, h4]
  simp only [cycSucc_val] at hv1 hv2
  rw [hk j] at hv1
  rw [hk i] at hv2
  omega

/-- **ON SEVEN POSITIONS THE PAIR OF RING-NEIGHBOURS OF A POINT DETERMINES THE POINT.** -/
theorem ring_pair_inj_seven {V' : Type*} (f : Fin 7 → V') (hf : Function.Injective f) (i j : Fin 7)
    (h : ({f (cycSucc i), f (cycPred i)} : Finset V') = {f (cycSucc j), f (cycPred j)}) : i = j := by
  have hA : f (cycSucc i) ∈ ({f (cycSucc j), f (cycPred j)} : Finset V') := by
    rw [← h]; exact Finset.mem_insert_self _ _
  have hB : f (cycPred i) ∈ ({f (cycSucc j), f (cycPred j)} : Finset V') := by
    rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rcases Finset.mem_insert.mp hA with hA1 | hA1
  · exact cycSucc_injective i j (hf hA1)
  · have hA1' : f (cycSucc i) = f (cycPred j) := Finset.mem_singleton.mp hA1
    rcases Finset.mem_insert.mp hB with hB1 | hB1
    · exact False.elim (cyc_flip_false_seven i j (hf hA1') (hf hB1))
    · exact cycPred_injective (hf (Finset.mem_singleton.mp hB1))

/-! ## Part 2c — the injectivity of the witness, at length seven -/

/-- **THE CYCLIC ORDER OF A SEVEN-CYCLE GIVEN BY A NUMBERING** — the `Fin 7` instance of
`JSP90.CycleOrder`, so that `JSP90.CycleOrder.prev` *is* `JSP90.cycPred`. -/
def sevenOrder {C : Finset V} (f : Fin 7 → V) (hf : Function.Injective f)
    (hcyc : ∀ j : Fin 7, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 7, f j = y) : CycleOrder G C :=
  ⟨7, f, by decide, hf, hcyc, hmem⟩

/-- **THE NEIGHBOURS OF `f j` INSIDE A SHORTEST ODD SEVEN-CYCLE ARE ITS TWO RING-NEIGHBOURS** —
`JSP90.filter_adj_C_eq_ringPair_of_five_le` at `Fin 7`. -/
theorem filter_adj_C_eq_ringPair_seven {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (hC7 : C.card = 7)
    (f : Fin 7 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 7, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 7, f j = y) (j : Fin 7) :
    C.filter (fun z => G.Adj (f j) z) = ({f (cycSucc j), f (cycPred j)} : Finset V) := by
  refine filter_adj_C_eq_ringPair_of_five_le hC hshort (sevenOrder f hf hcyc hmem) ?_ j
  rw [hC7]; omega

/-- **TWO DIFFERENT POINTS OF A SHORTEST ODD SEVEN-CYCLE ARE MISSED BY SEVEN-CYCLES WITH DIFFERENT
OUTSIDE VERTICES.** -/
theorem x_ne_y_of_two_sevenCycles_singleton {C D D' : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC7 : C.card = 7)
    (f : Fin 7 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 7, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 7, f j = y)
    {c c' x y : V} (hcc : c ∈ C) (hcc' : c' ∈ C) (hcne : c ≠ c') (hxn : x ∉ C) (hyn : y ∉ C)
    (hsub : (C \ {c}) ∪ {x} = D) (hD : IsOddCycle G D)
    (hsub' : (C \ {c'}) ∪ {y} = D') (hD' : IsOddCycle G D') : x ≠ y := by
  have hDcard : D.card = C.card := by
    rw [← hsub]; exact card_eq_of_union_sdiff_singleton hcc hxn rfl
  have hD'card : D'.card = C.card := by
    rw [← hsub']; exact card_eq_of_union_sdiff_singleton hcc' hyn rfl
  have h1 : C.filter (fun z => G.Adj x z) = C.filter (fun z => G.Adj c z) :=
    filter_adj_eq_of_cycle_singleton hC hshort (sevenOrder f hf hcyc hmem) (by rw [hC7]; omega)
      hcc hxn hsub hD hDcard
  have h2 : C.filter (fun z => G.Adj y z) = C.filter (fun z => G.Adj c' z) :=
    filter_adj_eq_of_cycle_singleton hC hshort (sevenOrder f hf hcyc hmem) (by rw [hC7]; omega)
      hcc' hyn hsub' hD' hD'card
  intro hxy
  have h12 : C.filter (fun z => G.Adj c z) = C.filter (fun z => G.Adj c' z) := by
    rw [← h1, hxy, ← h2]
  obtain ⟨j, hj⟩ : ∃ j : Fin 7, f j = c := (hmem c).mp hcc
  obtain ⟨j', hj'⟩ : ∃ j' : Fin 7, f j' = c' := (hmem c').mp hcc'
  rw [← hj, ← hj'] at h12
  rw [filter_adj_C_eq_ringPair_seven hC hshort hC7 f hf hcyc hmem j] at h12
  rw [filter_adj_C_eq_ringPair_seven hC hshort hC7 f hf hcyc hmem j'] at h12
  have hjj : j = j' := ring_pair_inj_seven f hf j j' h12
  exact hcne (by rw [← hj, ← hj', ← hjj])

/-- **TWO MISSED POINTS OF A SHORTEST ODD SEVEN-CYCLE HAVE TWO DIFFERENT WITNESSES** — the
`JSP90.Witness` form of `JSP90.x_ne_y_of_two_sevenCycles_singleton`. -/
theorem witness_ne_witness_seven_of_ne {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC7 : C.card = 7)
    (f : Fin 7 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 7, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 7, f j = y)
    {c c' : V} (hc : c ∈ Missed (G := G) (C := C)) (hc' : c' ∈ Missed (G := G) (C := C))
    (hcne : c ≠ c') :
    Witness (C := C) c hc ≠ Witness (C := C) c' hc' :=
  x_ne_y_of_two_sevenCycles_singleton hC hshort hC7 f hf hcyc hmem
    (mem_missed.mp hc).1 (mem_missed.mp hc').1 hcne (witness_spec hc).1 (witness_spec hc').1
    rfl (witness_spec hc).2 rfl (witness_spec hc').2

/-! ## Part 2d — the pigeonhole at length seven: the missed points inject into `V \ C` -/

/-- **THE POINTS OF A SHORTEST ODD SEVEN-CYCLE MISSED THAT WAY INJECT INTO `V \ C`.**

```lean
|{c ∈ C : (C \ {c}) ∪ {x} is an odd cycle for some x ∉ C}|  ≤  |V \ C|
```

This is `JSP90.card_missed_le_card_univ_sdiff` with `5` replaced by `7`; combined with
`|V \ C| ≤ 2` it recovers round 152's `JSP90.card_missed_le_two_of_card_le_seven`. -/
theorem card_missedSeven_le_card_univ_sdiff {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC7 : C.card = 7)
    (f : Fin 7 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 7, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 7, f j = y) :
    (Missed (G := G) (C := C)).card ≤ ((Finset.univ : Finset V) \ C).card := by
  classical
  set W : Finset V := (Finset.univ : Finset V) \ C with hWdef
  by_cases hW : W = ∅
  · have hcard : (Missed (G := G) (C := C)).card = 0 := by
      rw [Finset.card_eq_zero]
      ext c
      constructor
      · intro hc
        obtain ⟨x, D, hD, hxn, hsub⟩ := (mem_missed.mp hc).2
        have hxW : x ∈ W := by
          rw [hWdef]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxn⟩
        rw [hW] at hxW
        exact absurd hxW (by simp)
      · intro hc
        exact absurd hc (by simp)
    rw [hcard]
    exact Nat.zero_le _
  · obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hW
    refine Finset.card_le_card_of_injOn
      (f := fun c => if hc : c ∈ Missed (G := G) (C := C) then Witness (C := C) c hc else w₀) ?_ ?_
    · intro c hc
      by_cases hcm : c ∈ Missed (G := G) (C := C)
      · simp only [dite_eq_left hcm]
        exact mem_univ_sdiff_of_mem_missed hcm
      · simp only [dite_eq_right hcm]
        exact hw₀
    · intro c₁ hc₁ c₂ hc₂ heq
      have h1 : c₁ ∈ Missed (G := G) (C := C) := hc₁
      have h2 : c₂ ∈ Missed (G := G) (C := C) := hc₂
      simp only [dite_eq_left h1, dite_eq_left h2] at heq
      by_contra hcc
      exact absurd heq (witness_ne_witness_seven_of_ne hC hshort hC7 f hf hcyc hmem h1 h2 hcc)

/-! ## Part 3 — at `|V| ≤ |C| + 1` every missed point is missed that way -/

/-- **AT `|V| ≤ |C| + 1` EVERY POINT OF `C` MISSED BY SOME ODD CYCLE IS MISSED BY A CYCLE OF THE FORM
`(C \ {c}) ∪ {x}` WITH `x ∉ C`.**

Every odd cycle `D ≠ C` of `G` has `|D| ≥ |C|` (shortestness), `|D|` odd and `|D| ≤ |V| ≤ |C| + 1`,
and `|C|` is odd, so `|D| = |C|`; then `D \ C ≠ ∅` and `|C ∪ D| ≤ |C| + 1` give
`|D \ C| = |C \ D| = 1`. -/
theorem subset_missed_of_card_V_le_card_C_add_one {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hCodd : C.card % 2 = 1)
    (hV : Fintype.card V ≤ C.card + 1) :
    AllMissed (G := G) (C := C) ⊆ Missed (G := G) (C := C) := by
  intro z hz
  have hzC : z ∈ C := (mem_allMissed.mp hz).1
  obtain ⟨D, hD, hzD⟩ := (mem_allMissed.mp hz).2
  have hDeq : D ≠ C := fun h => hzD (h ▸ hzC)
  have hleV : D.card ≤ Fintype.card V := by
    have h1 := Finset.card_le_univ D
    have h2 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
    omega
  have hge : C.card ≤ D.card := hshort D hD
  have hoddD : D.card % 2 = 1 := card_mod_two_of_isOddCycle hD
  have hcup : #(C ∪ D) ≤ Fintype.card V := by
    have h1 := Finset.card_le_univ (C ∪ D)
    have h2 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
    omega
  have hsum : #(C ∪ D) + #(C ∩ D) = C.card + D.card := Finset.card_union_add_card_inter C D
  have hinter : #(C ∩ D) + 1 ≥ D.card := by
    have hlecupD : D.card ≤ #(C ∪ D) := by
      have h1 := Finset.card_le_card (Finset.subset_union_right : D ⊆ C ∪ D)
      omega
    omega
  -- `D \ C` is a singleton, and it is not empty because `D ≠ C` and `|D| = |C|`
  have hDcard : D.card = C.card := by omega
  have hsubDC : (D \ C).card ≤ 1 := by
    have hsub : (D \ C) ⊆ (Finset.univ : Finset V) \ C := by
      intro y hy
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hy).2⟩
    have h1 := Finset.card_le_card hsub
    have h2 : (((Finset.univ : Finset V)) \ C).card = Fintype.card V - C.card := by
      rw [Finset.card_sdiff]
      simp only [Finset.card_univ]
      have h4 : (C ∩ (Finset.univ : Finset V)).card = C.card := by
        rw [show (C ∩ (Finset.univ : Finset V)) = C by
          apply Finset.Subset.antisymm
          · intro y hy; exact (Finset.mem_inter.mp hy).1
          · intro y hy
            exact Finset.mem_inter.mpr ⟨hy, Finset.mem_univ _⟩]
      omega
    rw [h2] at h1
    omega
  have hneDC : (D \ C).Nonempty := by
    by_contra hcon
    have hE : D \ C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcon
    have hsubD : D ⊆ C := by
      intro y hy
      by_contra hyC
      have hmem : y ∈ D \ C := Finset.mem_sdiff.mpr ⟨hy, hyC⟩
      rw [hE] at hmem
      simp at hmem
    have hDeq2 : D = C := Finset.eq_of_subset_of_card_le hsubD (by rw [← hDcard])
    exact hDeq hDeq2
  have hDCcard : (D \ C).card = 1 := by
    have hne0 : (D \ C).card ≠ 0 := Finset.card_ne_zero.mpr hneDC
    omega
  obtain ⟨x, hxDC⟩ := hneDC
  have hxn : x ∉ C := (Finset.mem_sdiff.mp hxDC).2
  -- `C \ D = {z}`
  have hCDs : C \ D = {z} := by
    have h3 : (C \ D).card ≤ 1 := by
      have h1 := Finset.card_sdiff_add_card_inter C D
      have h2 : (C ∩ D).card ≤ C.card :=
        Finset.card_le_card (Finset.inter_subset_left : C ∩ D ⊆ C)
      omega
    have h4 : (C \ D).Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      by_contra hE
      have hsubCD : C ⊆ D := by
        intro y hy
        by_contra hyD
        have hmem : y ∈ C \ D := Finset.mem_sdiff.mpr ⟨hy, hyD⟩
        rw [hE] at hmem
        simp at hmem
      have hDeq2 : C = D := Finset.eq_of_subset_of_card_le hsubCD (by rw [hDcard])
      exact hDeq hDeq2.symm)
    refine eq_singleton_of_card_eq_one_of_mem ?_ (Finset.mem_sdiff.mpr ⟨hzC, hzD⟩)
    have hne0 : (C \ D).card ≠ 0 := Finset.card_ne_zero.mpr h4
    omega
  -- `C \ {z} ⊆ D`
  have hsubCzD : C \ {z} ⊆ D := by
    intro y hy
    have hyCD : y ∉ C \ D := by
      rw [hCDs]
      intro h
      exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_singleton.mpr (Finset.mem_singleton.mp h))
    by_contra hyD
    exact hyCD (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1, hyD⟩)
  -- `D = (C \ {z}) u {x}`
  have hunion : (C \ {z}) ∪ {x} ⊆ D := by
    intro y hy
    rw [Finset.mem_union] at hy
    rcases hy with hy | hy
    · exact hsubCzD hy
    · rw [Finset.mem_singleton] at hy
      subst hy
      exact (Finset.mem_sdiff.mp hxDC).1
  have hdis : Disjoint (C \ {z}) ({x} : Finset V) := by
    refine Finset.disjoint_left.2 fun y h1 h2 => ?_
    rw [Finset.mem_singleton] at h2
    subst h2
    exact hxn (Finset.mem_sdiff.mp h1).1
  have hcard : ((C \ {z}) ∪ {x} : Finset V).card = D.card := by
    have h1 := Finset.card_union_of_disjoint hdis
    have h2 : (C \ {z}).card = C.card - 1 :=
      Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hzC)
    rw [h1, h2, Finset.card_singleton, hDcard]
    omega
  refine mem_missed.mpr ⟨hzC, x, D, hD, hxn, ?_⟩
  exact Finset.eq_of_subset_of_card_le hunion (by rw [hcard])

/-! ## Part 4 — THE INSTANCE: the eight-vertex seven-cycle case -/

/-- **AT MOST ONE POINT OF A SHORTEST ODD SEVEN-CYCLE IS MISSED BY AN ODD CYCLE, WHEN
`|V| ≤ |C| + 1`.** -/
theorem card_allMissed_le_one_of_shortest_seven_of_card_V_le_add_one {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hC7 : C.card = 7) (hV : Fintype.card V ≤ C.card + 1) :
    (AllMissed (G := G) (C := C)).card ≤ 1 := by
  have hodd : C.card % 2 = 1 := card_mod_two_of_isOddCycle hC
  have hsub : AllMissed (G := G) (C := C) ⊆ Missed (G := G) (C := C) :=
    subset_missed_of_card_V_le_card_C_add_one hC hshort hodd hV
  have hC' : IsOddCycle G C := hC
  obtain ⟨m, f, hm_odd, hm3, hf, hcyc, hmem⟩ := hC'
  have hmc : C.card = m := card_eq_cyclicOrder f hf hmem
  have hm7 : m = 7 := by omega
  subst hm7
  have h1 := card_missedSeven_le_card_univ_sdiff hC hshort hC7 f hf hcyc hmem
  have h2 : ((Finset.univ : Finset V) \ C).card ≤ 1 := by
    have h3 := Finset.card_sdiff_of_subset (Finset.subset_univ C)
    have h4 : ((Finset.univ : Finset V) : Finset V).card = Fintype.card V := Finset.card_univ
    omega
  have h5 := Finset.card_le_card hsub
  omega

/-- **SOME POINT OF A SHORTEST ODD SEVEN-CYCLE MEETS EVERY ODD CYCLE OF `G`, WHEN `|V| ≤ |C| + 1`
— THE CERTIFICATE LIES ON `C`.** -/
theorem hitsOddCycles_mem_C_of_shortest_seven_of_card_le_add_one {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hC7 : C.card = 7) (hV : Fintype.card V ≤ C.card + 1) :
    ∃ c ∈ C, HitsOddCycles G {c} := by
  have hcard := card_allMissed_le_one_of_shortest_seven_of_card_V_le_add_one hC hshort hC7 hV
  have hsub : (AllMissed (G := G) (C := C) : Finset V) ⊆ C := by
    intro y hy
    exact (mem_allMissed.mp hy).1
  have h1 := Finset.card_le_card hsub
  have hlt : (AllMissed (G := G) (C := C)).card < C.card := by rw [hC7]; omega
  obtain ⟨c, hc, hcM⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨c, hc, fun D hD hnot => ?_⟩
  refine absurd (mem_allMissed.mpr ⟨hc, D, hD, ?_⟩) hcM
  intro hcin
  refine absurd (Finset.mem_inter.mpr ⟨hcin, Finset.mem_singleton.mpr rfl⟩) ?_
  rw [hnot]
  simp

/-- **SOME POINT OF A SHORTEST ODD SEVEN-CYCLE MEETS EVERY ODD CYCLE OF `G`, WHEN `|V| ≤ |C| + 1`.** -/
theorem hitsOddCycles_singleton_of_shortest_seven_of_card_le_add_one {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hC7 : C.card = 7) (hV : Fintype.card V ≤ C.card + 1) :
    ∃ c : V, HitsOddCycles G {c} := by
  obtain ⟨c, hcc, hc⟩ := hitsOddCycles_mem_C_of_shortest_seven_of_card_le_add_one hC hshort hC7 hV
  exact ⟨c, hc⟩

/-- **ERDŐS #73 AT `k = 1` WITH THE OPTIMAL CONSTANT `1`, WHEN A SHORTEST ODD CYCLE HAS SEVEN VERTICES
AND `|V| ≤ |C| + 1` — A NEW INSTANCE OF THE HEADLINE THEOREM.**

```lean
IsOddCycle G C → (C shortest odd cycle) → C.card = 7 → |V| ≤ 8 → CloseToBipartite 1 G
```

No `LocIndep` hypothesis occurs: the statement is about graphs of odd girth at least seven, and the
certificate is a **single vertex of the shortest odd cycle**. -/
theorem closeToBipartite_one_of_shortest_seven_of_card_le_add_one {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC7 : C.card = 7)
    (hV : Fintype.card V ≤ C.card + 1) : CloseToBipartite 1 G := by
  obtain ⟨c, hc⟩ := hitsOddCycles_singleton_of_shortest_seven_of_card_le_add_one hC hshort hC7 hV
  exact ⟨{c}, by simp, isBipartite_delete_of_hitsOddCycles hc⟩

/-- **THE SEVEN-CYCLE CASE AT ORDER EIGHT: A NEW INSTANCE OF THE HEADLINE THEOREM WITH THE OPTIMAL
CONSTANT `1`.** -/
theorem closeToBipartite_one_of_shortest_seven_of_card_le_eight {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC7 : C.card = 7)
    (hV : Fintype.card V ≤ 8) : CloseToBipartite 1 G := by
  refine closeToBipartite_one_of_shortest_seven_of_card_le_add_one hC hshort hC7 ?_
  rw [hC7]; omega

/-- **THE TRANSVERSAL FORM OF THE PREVIOUS STATEMENT, WITH THE CERTIFICATE ON `C`.** -/
theorem hitsOddCycles_singleton_on_C_of_shortest_seven_of_card_le_eight {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card)
    (hC7 : C.card = 7) (hV : Fintype.card V ≤ 8) : ∃ c ∈ C, HitsOddCycles G {c} :=
  hitsOddCycles_mem_C_of_shortest_seven_of_card_le_add_one hC hshort hC7 (by rw [hC7]; omega)

/-- **THE `tauOdd` FORM: THE ODD-CYCLE TRANSVERSAL NUMBER OF `G` IS AT MOST ONE.** -/
theorem tauOdd_le_one_of_shortest_seven_of_card_le_eight {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC7 : C.card = 7)
    (hV : Fintype.card V ≤ 8) : tauOdd G ≤ 1 :=
  (closeToBipartite_iff_tauOdd_le (G := G) (m := 1)).mp
    (closeToBipartite_one_of_shortest_seven_of_card_le_eight hC hshort hC7 hV)

/-- **THE CLASS FORM: ERDŐS #73 AT `k = 1` WITH THE CONSTANT `1` FOR GRAPHS OF ODD GIRTH AT LEAST
SEVEN ON AT MOST EIGHT VERTICES.** -/
theorem closeToBipartite_one_of_locIndep_one_card_le_eight_of_oddGirth_ge_seven
    (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 8)
    (hgirth : ∀ D : Finset V, IsOddCycle G D → 7 ≤ D.card) : CloseToBipartite 1 G := by
  by_cases hodd : ∃ D : Finset V, IsOddCycle G D
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle hodd
    have hCge : 7 ≤ C.card := hgirth C hC
    have hle : C.card ≤ Fintype.card V := by
      have h1 := Finset.card_le_univ C
      have h2 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
      omega
    have hCodd : C.card % 2 = 1 := card_mod_two_of_isOddCycle hC
    have hC7 : C.card = 7 := by omega
    exact closeToBipartite_one_of_shortest_seven_of_card_le_eight hC hshort hC7 hV
  · refine ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    exact isBipartite_of_no_oddCycle fun h => hodd h

/-- **THE INSTANCE IN THE `Erdős73On` SHAPE: ERDŐS #73 AT `k = 1` WITH THE CONSTANT `1` FOR GRAPHS OF
ORDER AT MOST EIGHT AND ODD GIRTH AT LEAST SEVEN.** -/
theorem erdos73On_one_oddGirth_ge_seven_eight :
    LocIndepOneSmallOrderOddGirth.{u} 1 8 7 :=
  fun (W : Type u) (_ : Fintype W) (G : SimpleGraph W) hV hG hgirth =>
    closeToBipartite_one_of_locIndep_one_card_le_eight_of_oddGirth_ge_seven hG hV hgirth

/-- **THE CONSTANT `0` FAILS IN THE CLASS ABOVE AS SOON AS `G` IS NOT BIPARTITE**, so the constant `1`
of `JSP90.closeToBipartite_one_of_locIndep_one_card_le_eight_of_oddGirth_ge_seven` is optimal inside
the class. -/
theorem not_closeToBipartite_zero_of_oddGirth_ge_seven_eight_of_not_isBipartite
    (hV : Fintype.card V ≤ 8) (hgirth : ∀ D : Finset V, IsOddCycle G D → 7 ≤ D.card)
    (hn : ¬ G.IsBipartite) : ¬ CloseToBipartite 0 G := by
  intro h
  have h1 : tauOdd G ≤ 0 := (closeToBipartite_iff_tauOdd_le (G := G) (m := 0)).mp h
  have h2 : G.IsBipartite := (tauOdd_zero_iff).mp (by omega)
  exact hn h2

/-! ## Part 5 — the `|V| ≤ |C| + 2` bound, the next gap of the eight-vertex instance -/

/-- **AT MOST TWO POINTS OF A SHORTEST ODD SEVEN-CYCLE ARE MISSED BY A CYCLE OF THE FORM
`(C \ {c}) ∪ {x}` WHEN `|V| ≤ |C| + 2`.**

This is round 152's `JSP90.card_missed_le_two_of_card_le_seven` at length seven; it is the last
statement available from the pigeonhole alone.  Beyond it, `Missed` can have three elements and the
points missed by a cycle with `|C \ D| ≥ 2` are no longer controlled, which is exactly why the
eight-vertex *five*-cycle case needs a **pair** of points of `C` as its certificate
(`discovery/JSP-000090/r172.c`: `|AllMissed| = 5` occurs in `110` of the `3 051 680` measured
graphs). -/
theorem card_missedSeven_le_two_of_card_V_le_add_two {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC7 : C.card = 7)
    (hV : Fintype.card V ≤ C.card + 2) : (Missed (G := G) (C := C)).card ≤ 2 := by
  have hC' : IsOddCycle G C := hC
  obtain ⟨m, f, hm_odd, hm3, hf, hcyc, hmem⟩ := hC'
  have hmc : C.card = m := card_eq_cyclicOrder f hf hmem
  have hm7 : m = 7 := by omega
  subst hm7
  have h1 := card_missedSeven_le_card_univ_sdiff hC hshort hC7 f hf hcyc hmem
  have h2 : ((Finset.univ : Finset V) \ C).card ≤ 2 := by
    have h3 := Finset.card_sdiff_of_subset (Finset.subset_univ C)
    have h4 : ((Finset.univ : Finset V) : Finset V).card = Fintype.card V := Finset.card_univ
    omega
  omega

end

end JSP90
