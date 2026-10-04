import JSPProblem.FiveWitness

/-!
# JSP-000090, round 155 — `JSPProblem/FiveCount.lean`: **THE COUNTING LAYER OF THE FIVE-CYCLE CASE**

Attack family 80.  This is the *next bet* named by `discovery/JSP-000090/policy.json` after round 152,
namely parts (a) and (b) of

> *"close the five-cycle case of the seven-vertex instance: (a) the cardinal form of Part 4 of
> `JSPProblem/FiveWitness.lean` — 'the points of `C` missed by a four-intersection five-cycle inject
> into `V \ C`'; (b) the pigeonhole 'some point of `C` is missed by none of them'; then (c)
> MISSING LEMMA 3."*

Round 152 proved the two *structural* facts — `JSP90.card_witness_le_one` (an outside vertex witnesses
at most one point of a five-cycle) and `JSP90.x_ne_y_of_two_fiveCycles_singleton` (two different points
of `C` missed by four-intersection five-cycles are missed by five-cycles with different outside
vertices) — but only *pointwise*, one pair at a time.  Nothing yet counted a **set** of missed points,
so the pigeonhole could not be closed.  This file builds that layer, and with it the reduction of the
five-cycle case to a single remaining statement.

## What is proved here (21 declarations, 0 placeholders)

* **Part 0 — the counted sets.**  `JSP90.MissedFour` (the points of `C` missed by a five-cycle of the
  form `(C \ {c}) ∪ {x}`, for a *fixed* outside vertex `x`), `JSP90.Missed` (the points of `C` missed
  by *any* such five-cycle, the outside vertex varying), `JSP90.Witness` (the choice of that outside
  vertex, with `JSP90.witness_spec` and `JSP90.mem_univ_sdiff_of_mem_missed`), and
  `JSP90.mem_missed` / `JSP90.mem_missedFour`.
* **Part 1 — `JSP90.card_missedFour_le_one`: THE PER-VERTEX COUNT.**  An outside vertex witnesses at
  most one point of `C` — the *set* form of round 152's `JSP90.x_ne_y_of_two_fiveCycles_singleton`,
  proved here through the bridge `JSP90.filter_adj_eq_of_fiveCycle_singleton` and the ring-pair
  arithmetic `JSP90.filter_adj_C_eq_ringPair` + `JSP90.five_pair_inj'`.  Also
  `JSP90.witness_ne_witness_of_ne`, the same content as an injectivity statement.
* **Part 2 — `JSP90.card_missed_le_card_univ_sdiff`: THE PIGEHOLE, IN THE FORM THE COUNTING READS.**
  `JSP90.Missed` is carried injectively by `JSP90.Witness` into `univ \ C`
  (`Finset.card_le_card_of_injOn`), so

  ```lean
  |{c ∈ C : (C \ {c}) ∪ {x} is a five-cycle for some x ∉ C}| ≤ |V \ C|
  ```

  and at `|V| ≤ 7` with `C` a shortest odd five-cycle,
  `JSP90.card_missed_le_two_of_card_le_seven` bounds it by **two**.
* **Part 3 — `JSP90.exists_mem_not_mem_missed`: THE POINT.**  Since `JSP90.Missed ⊆ C` and
  `|Missed| ≤ 2 < 5 = |C|`, some point of `C` is missed by no four-intersection five-cycle.
* **Part 4 — `JSP90.exists_mem_meetsFour` / `JSP90.MeetsFour`: THE INSTANCE.**  For a shortest odd
  five-cycle `C` of a graph on at most seven vertices there is a point `c ∈ C` with

  ```lean
  ∀ D, IsOddCycle G D → 4 ≤ |D ∩ C| → c ∈ D
  ```

  i.e. **`c` meets every odd cycle that meets `C` in at least four points** — the whole
  four-intersection half of the five-cycle case, with the sharp bound `2` on the missed points.  The
  only use of `C` being *shortest* is round 152's bridge "`(C \ {c}) ∪ {x}` a five-cycle means `x`
  witnesses `c`"; no triangle-freeness is needed for this half.
* **Part 5 — `JSP90.mem_C_of_isOddCycle_of_card_eq_seven`,
  `JSP90.isOddCycle_five_or_mem_of_meetsFour`, `JSP90.mem_hits_ge_four_of_meetsFour`: THE
  REDUCTION.**  A seven-cycle spans `V` and so contains `C`; triangle-freeness gives odd girth at
  least five; two five-cycles on at most seven vertices meet in at least `5 + 5 − 7 = 3` points while
  `JSP90.MeetsFour` bounds the intersection at three.  Hence

  > **every odd cycle of `G` either contains `c`, or is a five-cycle meeting `C` in exactly three
  > points** (`JSP90.isOddCycle_five_or_mem_of_meetsFour`), equivalently a point of `C` meets every
  > odd cycle of `G` that is not a three-intersection five-cycle
  > (`JSP90.mem_hits_ge_four_of_meetsFour`).

  So the five-cycle case of the sharp seven-vertex instance
  `JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven` now hinges on **one** statement about
  three-intersection five-cycles, recorded and measured as
  `JSP90.ThreeIntersectionFiveCycleUnique` below.
* **Part 6 — the closure: `JSP90.ThreeIntersectionFiveCycleUnique` really is enough.**
  `JSP90.AllMissed` (the points of `C` missed by *some* odd cycle) and `JSP90.Miss` (an odd cycle
  missing a point) are named; `JSP90.mem_missed_or_three` classifies every missed point (a missed point
  is either missed by a four-intersection five-cycle, Part 2, or missed by a three-intersection
  five-cycle); `JSP90.card_allMissed_le_four_of_unique` puts the total at **four** of the five points,
  and `JSP90.hitsOddCycles_singleton_of_unique` and `JSP90.closeToBipartite_one_of_unique` finish:

  ```lean
  JSP90.closeToBipartite_one_of_unique  --  CloseToBipartite 1 G
  ```

  i.e. **the five-cycle case of `JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven` follows from
  `JSP90.ThreeIntersectionFiveCycleUnique` and nothing else.**  Nothing in Part 6 uses `LocIndep 1`:
  the five-cycle case is a statement about triangle-free graphs on at most seven vertices.

## What is *not* proved (the blocker of this round)

`JSP90.ThreeIntersectionFiveCycleUnique`: **at most one five-cycle of `G` meets a shortest odd
five-cycle `C` in exactly three points.**  It is the only missing input of the reduction of Part 5,
i.e. of the whole remaining content of the five-cycle case: with it, the points of `C` missed by some
odd cycle are the union of a set of at most two points (Part 2, the four-intersection cycles) with the
missed *pair* of a single five-cycle, so at most four of the five points of `C` are missed, some point
meets every odd cycle, and `JSP90.closeToBipartite 1 G` follows at `LocIndep 1` and `|V| ≤ 7`.

### The measurement of this round (`discovery/JSP-000090/r155.c`, 0.5 s)

Over **all** `2^21` graphs on seven vertices, restricted to triangle-free ones with a five-cycle
(`50904` pairs `(G, C)`):

| quantity | value |
| --- | --- |
| **max number of five-cycles `D` with `\|C \ D\| = 2`** (MISSING LEMMA 3) | **`1`** |
| violations of MISSING LEMMA 3 | **`0`** |
| instances of shape A (the two outside vertices adjacent in `D`) | `10080` |
| instances of shape B (not adjacent in `D`) | `2520` |
| shape A with the missed pair not an edge of `C` | `0` |
| shape B with the missed pair not at distance two in `C` | `0` |
| shape B in which a four-intersection five-cycle also exists | `2520 / 2520` |
| max points of `C` missed by an odd cycle (`\|M\|`) | `2` (`0` cases with `\|M\| > 4`) |

Two *bugs* were found and fixed in the measurement program while writing it: `adj` counted a vertex as
adjacent to **itself** (`eidx i i` is a legal bit position), which made every five-cycle look
regular; and the cyclic-order routine could not walk a five-cycle.  Both were caught by the
`NOORDER`/`BADMISS` self-checks of the program.

The shape table is the skeleton of a Lean proof of `ThreeIntersectionFiveCycleUnique`: writing
`C = v₀v₁v₂v₃v₄v₀`, `W = V \ C`, `S = D ∩ C`, `|W| = |S| = 3` for the outside and the inside part,
triangle-freeness says every `N_C(w)` is an **independent** subset of `C` of size at most two, i.e. a
singleton or one of the five ring-pairs `{v_{i-1}, v_{i+1}}`, and:

* **shape A** (`w₁ ~ w₂`): `S` is three *consecutive* vertices of `C`, the middle one has **no**
  neighbour in `W`, `N_C(w₁) ∋ v_{i+2}` and `N_C(w₂) ∋ v_i`, and the missed pair is an **edge** of `C`;
  a second such `D` would need a ring-pair `N_C(·)` disjoint from those and avoiding the middle vertex,
  which closes a triangle;
* **shape B** (`w₁ ≁ w₂`): `|E(S, W)| = 4`, so `N_C(w₁) = N_C(w₂) = ∅` is impossible and the two
  ring-pairs determine `S` uniquely (the pair assignment is forced: `w₁ ~ {a, c}`, `w₂ ~ {b, c}` with
  `a, b, c` three vertices of `C`), so again at most one such `D`.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps reporting
`missing_theorems = ["jsp_000090_main"]`.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 4000000

local instance fcDecidableAdjRel (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

local instance fcDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Part 0 — the counted sets -/

/-- **THE POINTS OF `C` MISSED BY A FIVE-CYCLE OF THE FORM `(C \ {c}) ∪ {x}`, FOR A FIXED OUTSIDE
VERTEX `x`.**  This is the set counted by `JSP90.card_witness_le_one` of round 152, at the level of a
finset rather than one pair at a time. -/
noncomputable def MissedFour {C : Finset V} (x : V) : Finset V := by
  classical
  exact Finset.filter (fun c => ∃ D : Finset V, IsOddCycle G D ∧ (C \ {c}) ∪ {x} = D) C

@[simp] theorem mem_missedFour {C : Finset V} {x c : V} :
    c ∈ MissedFour (G := G) (C := C) x ↔
      c ∈ C ∧ ∃ D : Finset V, IsOddCycle G D ∧ (C \ {c}) ∪ {x} = D := by
  simp only [MissedFour, Finset.mem_filter]

/-- **THE POINTS OF `C` MISSED BY ANY FIVE-CYCLE OF THE FORM `(C \ {c}) ∪ {x}` WITH `x ∉ C`** — the
four-intersection half of the missed points of `C`, in the form the pigeonhole of Part 3 uses. -/
noncomputable def Missed {C : Finset V} : Finset V := by
  classical
  exact Finset.filter
    (fun c => ∃ x : V, ∃ D : Finset V, IsOddCycle G D ∧ x ∉ C ∧ (C \ {c}) ∪ {x} = D) C

@[simp] theorem mem_missed {C : Finset V} {c : V} :
    c ∈ Missed (G := G) (C := C) ↔
      c ∈ C ∧ ∃ x : V, ∃ D : Finset V, IsOddCycle G D ∧ x ∉ C ∧ (C \ {c}) ∪ {x} = D := by
  simp only [Missed, Finset.mem_filter]

/-- **THE WITNESS OF A MISSED POINT**: the vertex outside `C` of the five-cycle
`(C \ {c}) ∪ {·}` which misses `c`.  Only defined when `c` is missed (the proof of membership is an
argument, and it does not matter which proof is used, by proof irrelevance). -/
noncomputable def Witness {C : Finset V} (c : V) (hc : c ∈ Missed (G := G) (C := C)) : V :=
  Classical.choose (mem_missed.mp hc).2

/-- **THE WITNESS OF A MISSED POINT IS OUTSIDE `C`, AND `C` WITHOUT `c` PLUS IT IS A FIVE-CYCLE.** -/
theorem witness_spec {C : Finset V} {c : V} (hc : c ∈ Missed (G := G) (C := C)) :
    Witness (C := C) c hc ∉ C ∧ IsOddCycle G ((C \ {c}) ∪ {Witness (C := C) c hc}) := by
  have hcho : Witness (C := C) c hc = Classical.choose (mem_missed.mp hc).2 := rfl
  obtain ⟨D, hD, hxn, hsub⟩ := Classical.choose_spec (mem_missed.mp hc).2
  refine ⟨hxn, ?_⟩
  rw [hcho]
  exact hsub ▸ hD

/-- **A WITNESS IS A WITNESS.** -/
theorem mem_univ_sdiff_of_mem_missed {C : Finset V} {c : V} (hc : c ∈ Missed (G := G) (C := C)) :
    Witness (C := C) c hc ∈ (Finset.univ : Finset V) \ C :=
  Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (witness_spec hc).1⟩

/-- **TWO MISSED POINTS HAVE TWO DIFFERENT WITNESSES** — round 152's
`JSP90.x_ne_y_of_two_fiveCycles_singleton` at the level of the choice function, which is what makes
the pigeonhole of Part 2 an injection. -/
theorem witness_ne_witness_of_ne {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    {c c' : V} (hc : c ∈ Missed (G := G) (C := C)) (hc' : c' ∈ Missed (G := G) (C := C)) (hcne : c ≠ c') :
    Witness (C := C) c hc ≠ Witness (C := C) c' hc' :=
  x_ne_y_of_two_fiveCycles_singleton hC hshort hC5 f hf hcyc hmem htf
    (mem_missed.mp hc).1 (mem_missed.mp hc').1 hcne (witness_spec hc).1 (witness_spec hc').1
    rfl (witness_spec hc).2 rfl (witness_spec hc').2

/-! ## Part 1 — the per-vertex count

Round 152 proved `JSP90.x_ne_y_of_two_fiveCycles_singleton`: two *different* points of `C` missed by
four-intersection five-cycles are missed by five-cycles with *different* outside vertices.  Read as a
statement about a finset it is a two-element bound. -/

/-- **AN OUTSIDE VERTEX MISSES AT MOST ONE POINT OF `C`.**

```lean
C shortest odd five-cycle, G triangle-free, x ∉ C  →  |{c ∈ C : (C \ {c}) ∪ {x} is a five-cycle}| ≤ 1
```

This is the set form of round 152's `JSP90.x_ne_y_of_two_fiveCycles_singleton`, i.e. the pigeonhole
"`JSP90.card_witness_le_one` counts at most one point" written at the level of a finset. -/
theorem card_missedFour_le_one {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    {x : V} (hxn : x ∉ C) :
    (MissedFour (G := G) (C := C) x).card ≤ 1 := by
  classical
  by_contra hcon
  have h2 : 2 ≤ (MissedFour (G := G) (C := C) x).card := by omega
  obtain ⟨c, hcS, c', hc'S, hccne⟩ := exists_two_of_card_ge_two h2
  have hcC : c ∈ C := (mem_missedFour.mp hcS).1
  have hc'C : c' ∈ C := (mem_missedFour.mp hc'S).1
  obtain ⟨D, hD, hsub⟩ := (mem_missedFour.mp hcS).2
  obtain ⟨D', hD', hsub'⟩ := (mem_missedFour.mp hc'S).2
  have h1 : C.filter (fun z => G.Adj x z) = C.filter (fun z => G.Adj c z) :=
    filter_adj_eq_of_fiveCycle_singleton hC hshort hC5 f hf hcyc hmem htf hcC hxn hsub hD
  have h1' : C.filter (fun z => G.Adj x z) = C.filter (fun z => G.Adj c' z) :=
    filter_adj_eq_of_fiveCycle_singleton hC hshort hC5 f hf hcyc hmem htf hc'C hxn hsub' hD'
  have h12 : C.filter (fun z => G.Adj c z) = C.filter (fun z => G.Adj c' z) := by
    rw [← h1, h1']
  obtain ⟨i, hi⟩ : ∃ i : Fin 5, f i = c := (hmem c).mp hcC
  obtain ⟨i', hi'⟩ : ∃ i' : Fin 5, f i' = c' := (hmem c').mp hc'C
  rw [← hi, ← hi'] at h12
  have hii : i = i' := by
    rw [filter_adj_C_eq_ringPair hC hshort hC5 f hf hcyc hmem i] at h12
    rw [filter_adj_C_eq_ringPair hC hshort hC5 f hf hcyc hmem i'] at h12
    exact five_pair_inj' f hf i i' h12
  refine hccne.elim ?_
  rw [← hi, ← hi', ← hii]

/-! ## Part 2 — the pigeonhole: the missed points inject into `V \ C` -/

/-- **THE POINTS OF `C` MISSED BY A FOUR-INTERSECTION FIVE-CYCLE INJECT INTO `V \ C`.**

```lean
|{c ∈ C : (C \ {c}) ∪ {x} is a five-cycle for some x ∉ C}| ≤ |V \ C|
```

The content is that `JSP90.Missed` is carried injectively by `JSP90.Witness` into `univ \ C` — the
"next bet (a)" of round 152's policy, the cardinal form of Part 4 of
`JSPProblem/FiveWitness.lean`.  No hypothesis beyond round 152's is used: `C` a *shortest* odd
five-cycle of a triangle-free graph and the cyclic numbering of `C`. -/
theorem card_missed_le_card_univ_sdiff {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) :
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
      exact absurd heq (witness_ne_witness_of_ne hC hshort hC5 f hf hcyc hmem htf h1 h2 hcc)

/-- **AT `|V| ≤ 7` AT MOST TWO POINTS OF `C` ARE MISSED BY A FOUR-INTERSECTION FIVE-CYCLE.** -/
theorem card_missed_le_two_of_card_le_seven {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    (hV : Fintype.card V ≤ 7) :
    (Missed (G := G) (C := C)).card ≤ 2 := by
  have h1 := card_missed_le_card_univ_sdiff hC hshort hC5 f hf hcyc hmem htf
  have h2 : ((Finset.univ : Finset V) \ C).card ≤ 2 := by
    have h3 := Finset.card_sdiff_of_subset (Finset.subset_univ C)
    have h4 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
    omega
  omega

/-! ## Part 3 — the point: some point of `C` is missed by none of them -/

/-- **SOME POINT OF `C` IS MISSED BY NO FOUR-INTERSECTION FIVE-CYCLE.**

`JSP90.Missed ⊆ C` and `|Missed| ≤ 2 < 5 = |C|`, so the missed set is a proper subset of `C`.  This is
the pigeonhole ("b") of round 152's next bet. -/
theorem exists_mem_not_mem_missed {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    (hV : Fintype.card V ≤ 7) :
    ∃ c ∈ C, c ∉ Missed (G := G) (C := C) := by
  have hle := card_missed_le_two_of_card_le_seven hC hshort hC5 f hf hcyc hmem htf hV
  have hlt : (Missed (G := G) (C := C)).card < C.card := by rw [hC5]; omega
  obtain ⟨c, hc, hcM⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨c, hc, hcM⟩


/-- **A SEVEN-CYCLE SPANS THE GRAPH, HENCE CONTAINS `C`.** -/
theorem mem_C_of_isOddCycle_of_card_eq_seven {C D : Finset V} (h7 : D.card = 7)
    (hV : Fintype.card V ≤ 7) {c : V} (hc : c ∈ C) : c ∈ D := by
  have hcardle : D.card ≤ Fintype.card V := by
    have h1 := Finset.card_le_univ D
    have h2 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
    omega
  have hsub : D = (Finset.univ : Finset V) := by
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ D) ?_
    rw [Finset.card_univ]
    omega
  rw [hsub]
  exact Finset.mem_univ _

/-! ## Part 4 — the instance: a point of `C` meets every odd cycle meeting `C` in four points -/

/-- **`c` MEETS EVERY ODD CYCLE OF `G` THAT MEETS `C` IN AT LEAST FOUR POINTS.** -/
def MeetsFour (G : SimpleGraph V) {C : Finset V} (c : V) : Prop :=
  ∀ D : Finset V, IsOddCycle G D → 4 ≤ (D ∩ C).card → c ∈ D

/-- **THE FOUR-INTERSECTION HALF OF THE FIVE-CYCLE CASE: A POINT OF A SHORTEST ODD FIVE-CYCLE MEETS
EVERY ODD CYCLE MEETING IT IN AT LEAST FOUR POINTS.**

```lean
LocIndep 1 G → |V| ≤ 7 → C a shortest odd cycle of five vertices →
  ∃ c ∈ C, ∀ D, IsOddCycle G D → 4 ≤ |D ∩ C| → c ∈ D
```

The proof is the pigeonhole of Part 3: the points of `C` missed by such a cycle form a set of at most
`|V \ C| ≤ 2` elements (Part 2), so one point of the five is missed by none of them.  Notice that the
*only* use of `C` being a **shortest** odd cycle is `JSP90.x_ne_y_of_two_fiveCycles_singleton`, i.e.
the bridge "`(C \ {c}) ∪ {x}` a five-cycle means `x` witnesses `c`". -/
theorem exists_mem_meetsFour {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    (hV : Fintype.card V ≤ 7) :
    ∃ c ∈ C, MeetsFour G (C := C) c := by
  obtain ⟨c, hc, hcM⟩ := exists_mem_not_mem_missed hC hshort hC5 f hf hcyc hmem htf hV
  have hcC : c ∈ C := hc
  refine ⟨c, hc, ?_⟩
  intro D hD h4
  have hcardle : D.card ≤ Fintype.card V := by
    have h1 := Finset.card_le_univ D
    have h2 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
    omega
  have hodd := card_mod_two_of_isOddCycle hD
  have hge : 5 ≤ D.card := by
    have h1 := Finset.card_le_card (Finset.inter_subset_left : D ∩ C ⊆ D)
    omega
  have hcases : D.card = 5 ∨ D.card = 7 := by omega
  rcases hcases with hD5 | hD7
  · by_contra hcD
    have hleC : (D ∩ C).card ≤ 5 := by
      have h1 := Finset.card_le_card (Finset.inter_subset_right : D ∩ C ⊆ C)
      rw [hC5] at h1
      omega
    have hne5 : (D ∩ C).card ≠ 5 := by
      intro heq
      refine hcD ?_
      have hceq5 : D ∩ C = C :=
        Finset.eq_of_subset_of_card_le (Finset.inter_subset_right : D ∩ C ⊆ C) (by rw [hC5]; omega)
      have h2' : C ⊆ D := by rw [← hceq5]; exact (Finset.inter_subset_left : D ∩ C ⊆ D)
      exact h2' hcC
    have hcardinter : (D ∩ C).card = 4 := by omega
    have hCd : C \ D = {c} := by
      refine eq_singleton_of_card_eq_one_of_mem ?_ (Finset.mem_sdiff.mpr ⟨hcC, hcD⟩)
      have h3 := Finset.card_sdiff (s := D) (t := C)
      omega
    obtain ⟨x, hxD, hxn⟩ : ∃ x, x ∈ D ∧ x ∉ C := by
      by_contra hcon
      have hsub : D ⊆ C := fun z hz => by
        by_contra hzC
        exact hcon ⟨z, hz, hzC⟩
      have hDeq : D = C := Finset.eq_of_subset_of_card_le hsub (by rw [hC5]; omega)
      exact hcD (hDeq ▸ hcC)
    have hDsing : D \ C = {x} := by
      refine eq_singleton_of_card_eq_one_of_mem ?_ (Finset.mem_sdiff.mpr ⟨hxD, hxn⟩)
      have hsym : (C ∩ D).card = 4 := by rw [Finset.inter_comm]; exact hcardinter
      have h3 := Finset.card_sdiff (s := C) (t := D)
      omega
    have hDsub : D ⊆ (C \ {c}) ∪ {x} := by
      intro z hz
      rw [Finset.mem_union]
      by_cases hzDC : z ∈ D \ C
      · refine Or.inr ?_
        refine Finset.mem_singleton.mpr ?_
        rw [hDsing] at hzDC
        exact Finset.mem_singleton.mp hzDC
      · have hzC : z ∈ C := by
          by_contra hzC
          exact hzDC (Finset.mem_sdiff.mpr ⟨hz, hzC⟩)
        refine Or.inl (Finset.mem_sdiff.mpr ⟨hzC, ?_⟩)
        intro hzc
        rw [Finset.mem_singleton] at hzc
        subst hzc
        exact hcD hz
    have hsub : (C \ {c}) ∪ {x} = D := Finset.Subset.antisymm (by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.mp hz
        have hzD : z ∈ D := by
          by_contra hzn
          have hzDC : z ∈ C \ D := Finset.mem_sdiff.mpr ⟨hz1, hzn⟩
          rw [hCd] at hzDC
          exact hz2 hzDC
        exact hzD
      · rw [Finset.mem_singleton] at hz
        exact hz ▸ hxD) hDsub

    exact hcM (mem_missed.mpr ⟨hcC, x, D, hD, hxn, hsub⟩)
  · exact mem_C_of_isOddCycle_of_card_eq_seven hD7 hV hcC

/-! ## Part 5 — the reduction: what is left is the three-intersection five-cycles -/

/-- **THE FIVE-CYC⟨E CASE, ⟩EDUCED TO THE TH⟩EE-INTE⟩SECTION FIVE-CYC⟨ES.**

```lean
C a shortest odd five-cycle of a triangle-free graph on at most seven vertices, c ∈ C meeting every
odd cycle meeting C in at least four points  →  ∀ D, IsOddCycle G D → c ∈ D ∨ (D.card = 5 ∧ |D ∩ C| = 3)
```

Every odd cycle has five or seven vertices (triangle-freeness gives odd girth at least five and the
order bound gives at most seven); a seven-cycle is `univ` and contains `c`; so an odd cycle avoiding
`c` is a five-cycle, and two five-cycles on at most seven vertices meet in at least
`5 + 5 - 7 = 3` points while `JSP90.MeetsFour` bounds the intersection at three. -/
theorem isOddCycle_five_or_mem_of_meetsFour {C : Finset V} (hC5 : C.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) (hV : Fintype.card V ≤ 7)
    {c : V} (hc : c ∈ C) (hmeet : MeetsFour G (C := C) c)
    {D : Finset V} (hD : IsOddCycle G D) :
    c ∈ D ∨ (D.card = 5 ∧ (D ∩ C).card = 3) := by
  by_cases hcn : c ∈ D
  · exact Or.inl hcn
  · have h4 : ¬ 4 ≤ (D ∩ C).card := by
      intro h
      exact hcn (hmeet D hD h)
    have hle : (D ∩ C).card ≤ 3 := by omega
    have h5 := card_ge_five_of_isOddCycle_of_triangleFree htf hD
    have hcardle : D.card ≤ Fintype.card V := by
      have h1 := Finset.card_le_univ D
      have h2 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
      omega
    have hmod := card_mod_two_of_isOddCycle hD
    have h7ne : D.card ≠ 7 := fun h => hcn (mem_C_of_isOddCycle_of_card_eq_seven h hV hc)
    have h5eq : D.card = 5 := by omega
    have hge3 : 3 ≤ (D ∩ C).card := by
      have hsym : (D ∩ C).card = (C ∩ D).card := by rw [Finset.inter_comm]
      have h1 := Finset.card_union_add_card_inter C D
      have h2 := Finset.card_le_univ (C ∪ D)
      have h3 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
      omega
    exact Or.inr ⟨h5eq, by omega⟩

/-- **THE INSTANCE, IN THE T⟩ANSVE⟩SA⟨ SHAPE OF ⟩OUND 151: A POINT OF `C` MEETS EVE⟩Y ODD CYC⟨E OF `G`
THAT IS NOT A TH⟩EE-INTE⟩SECTION FIVE-CYC⟨E.** -/
theorem mem_hits_ge_four_of_meetsFour {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    (hV : Fintype.card V ≤ 7) :
    ∃ c : V, c ∈ C ∧ ∀ D : Finset V, IsOddCycle G D → ¬ (D.card = 5 ∧ (D ∩ C).card = 3) → c ∈ D := by
  obtain ⟨c, hc, hmeet⟩ := exists_mem_meetsFour hC hshort hC5 f hf hcyc hmem htf hV
  refine ⟨c, hc, ?_⟩
  intro D hD hD'
  rcases isOddCycle_five_or_mem_of_meetsFour hC5 htf hV hc hmeet hD with
    h | h
  · exact h
  · exact absurd h hD'

/-! ## The blocker of this round: MISSING ⟨EMMA 3

Named exactly, as the `def` the remaining proof of the five-cycle case consumes.  It is **not** proved;
it is measured in `discovery/JSP-000090/r155.c` (max one such five-cycle over all `50904` relevant
pairs `(G, C)`, `0` violations) together with the two shapes such a five-cycle can take. -/

/-- **MISSING ⟨EMMA 3 OF ⟩OUNDS 152–154, NAMED: AT MOST ONE FIVE-CYC⟨E OF `G` MEETS A SHO⟩TEST ODD
FIVE-CYC⟨E `C` IN EXACT⟨Y TH⟩EE POINTS.**

This is the single remaining input of `JSP90.isOddCycle_five_or_mem_of_meetsFour`: with it, the set of
points of `C` missed by *some* odd cycle is the union of a set of at most two points (Part 2) with the
missed pair of a single five-cycle, hence has at most four of the five points of `C`, so one point of
`C` meets every odd cycle and `JSP90.closeToBipartite 1 G` follows.  **Not proved here.** -/
def ThreeIntersectionFiveCycleUnique (C D D' : Finset V) : Prop :=
  IsOddCycle G C ∧ (∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) ∧ C.card = 5 ∧
    IsOddCycle G D ∧ IsOddCycle G D' ∧ D.card = 5 ∧ D'.card = 5 ∧
    (D ∩ C).card = 3 ∧ (D' ∩ C).card = 3 → D = D'

/-! ## Part 6 — the closure: `JSP90.ThreeIntersectionFiveCycleUnique` really is enough

Parts 2 to 5 leave exactly one missing statement.  This part writes the mechanical consequence, so
that the remaining work of the five-cycle case is *only* `JSP90.ThreeIntersectionFiveCycleUnique`. -/

/-- **THE POINTS OF `C` MISSED BY *SOME* ODD CYCLE OF `G`** — the whole missed set, the set that has to
be smaller than `C`. -/
noncomputable def AllMissed {C : Finset V} : Finset V := by
  classical
  exact Finset.filter (fun c => ∃ D : Finset V, IsOddCycle G D ∧ c ∉ D) C

@[simp] theorem mem_allMissed {C : Finset V} {c : V} :
    c ∈ AllMissed (G := G) (C := C) ↔
      c ∈ C ∧ ∃ D : Finset V, IsOddCycle G D ∧ c ∉ D := by
  simp only [AllMissed, Finset.mem_filter]

/-- **AN ODD CYCLE WHICH MISSES A POINT.** -/
noncomputable def Miss {C : Finset V} (c : V) (hc : c ∈ AllMissed (G := G) (C := C)) : Finset V :=
  Classical.choose (mem_allMissed.mp hc).2

theorem miss_spec {C : Finset V} {c : V} (hc : c ∈ AllMissed (G := G) (C := C)) :
    IsOddCycle G (Miss (C := C) c hc) ∧ c ∉ Miss (C := C) c hc :=
  Classical.choose_spec (mem_allMissed.mp hc).2

/-- **EVERY MISSED POINT IS EITHER A FOUR-INTERSECTION MISS OR THE MISS OF A THREE-INTERSECTION
FIVE-CYCLE.**

```lean
C shortest odd five-cycle, |V| ≤ 7, G triangle-free, c ∈ C with MeetsFour c, z missed by some odd cycle
  →  z ∈ Missed C  ∨  ∃ D, IsOddCycle G D ∧ D.card = 5 ∧ |D ∩ C| = 3 ∧ z ∉ D
```

The second case is `JSP90.isOddCycle_five_or_mem_of_meetsFour` plus the two counting facts: a five-cycle
meets `C` in at least three points (`|C ∪ D| ≤ 7`) and a triangle is excluded, so an odd cycle meeting
`C` in at most three points *is* a three-intersection five-cycle. -/
theorem mem_missed_or_three {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    (hV : Fintype.card V ≤ 7) {c : V} (hc : c ∈ C) (hmeet : MeetsFour G (C := C) c)
    {z : V} (hz : z ∈ AllMissed (G := G) (C := C)) :
    z ∈ Missed (G := G) (C := C) ∨
      ∃ D : Finset V, IsOddCycle G D ∧ D.card = 5 ∧ (D ∩ C).card = 3 ∧ z ∉ D := by
  set D : Finset V := Miss (C := C) z hz with hDdef
  have hD : IsOddCycle G D := by rw [hDdef]; exact (miss_spec hz).1
  have hzD : z ∉ D := by rw [hDdef]; exact (miss_spec hz).2
  have hzC : z ∈ C := (mem_allMissed.mp hz).1
  by_cases h4 : 4 ≤ (D ∩ C).card
  · left
    have hcn : c ∈ D := hmeet D hD h4
    have hne : z ≠ c := by
      intro h
      exact hzD (h ▸ hcn)
    have hcardle : D.card ≤ Fintype.card V := by
      have h1 := Finset.card_le_univ D
      have h2 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
      omega
    have hodd := card_mod_two_of_isOddCycle hD
    have hleC : (D ∩ C).card ≤ 5 := by
      have h1 := Finset.card_le_card (Finset.inter_subset_right : D ∩ C ⊆ C)
      rw [hC5] at h1
      omega
    have hne5 : (D ∩ C).card ≠ 5 := by
      intro heq
      refine hzD ?_
      have hceq5 : D ∩ C = C :=
        Finset.eq_of_subset_of_card_le (Finset.inter_subset_right : D ∩ C ⊆ C) (by rw [hC5]; omega)
      have h2' : C ⊆ D := by rw [← hceq5]; exact (Finset.inter_subset_left : D ∩ C ⊆ D)
      exact h2' hzC
    have hD5 : D.card = 5 := by
      have hge : 5 ≤ D.card := by
        have h1 := Finset.card_le_card (Finset.inter_subset_left : D ∩ C ⊆ D)
        omega
      have hne7 : D.card ≠ 7 :=
        fun h => hzD (mem_C_of_isOddCycle_of_card_eq_seven h hV hzC)
      omega
    have hcardinter : (D ∩ C).card = 4 := by omega
    have hCd : C \ D = {z} := by
      refine eq_singleton_of_card_eq_one_of_mem ?_ (Finset.mem_sdiff.mpr ⟨hzC, hzD⟩)
      have h3 := Finset.card_sdiff (s := D) (t := C)
      omega
    obtain ⟨x, hxD, hxn⟩ : ∃ x, x ∈ D ∧ x ∉ C := by
      by_contra hcon
      have hsub : D ⊆ C := fun y hy => by
        by_contra hyC
        exact hcon ⟨y, hy, hyC⟩
      have hDeq : D = C := Finset.eq_of_subset_of_card_le hsub (by rw [hC5]; omega)
      exact hzD (hDeq ▸ hzC)
    have hDsing : D \ C = {x} := by
      refine eq_singleton_of_card_eq_one_of_mem ?_ (Finset.mem_sdiff.mpr ⟨hxD, hxn⟩)
      have hsym : (C ∩ D).card = 4 := by rw [Finset.inter_comm]; exact hcardinter
      have h3 := Finset.card_sdiff (s := C) (t := D)
      omega
    have hceq : D ∩ C = C \ {z} := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro y hy
        have hyi := Finset.mem_inter.mp hy
        refine Finset.mem_sdiff.mpr ⟨hyi.right, ?_⟩
        intro hyz
        rw [Finset.mem_singleton] at hyz
        subst hyz
        exact hzD hyi.left
      · intro y hy
        obtain ⟨hy1, hy2⟩ := Finset.mem_sdiff.mp hy
        have hyD : y ∈ D := by
          by_contra hyn
          have hyDC : y ∈ C \ D := Finset.mem_sdiff.mpr ⟨hy1, hyn⟩
          rw [hCd] at hyDC
          exact hy2 hyDC
        exact Finset.mem_inter.mpr ⟨hyD, hy1⟩
    have hDsub : D ⊆ (C \ {z}) ∪ {x} := by
      intro y hy
      rw [Finset.mem_union]
      by_cases hyDC : y ∈ D \ C
      · refine Or.inr (Finset.mem_singleton.mpr ?_)
        rw [hDsing] at hyDC
        exact Finset.mem_singleton.mp hyDC
      · have hyC : y ∈ C := by
          by_contra hyC
          exact hyDC (Finset.mem_sdiff.mpr ⟨hy, hyC⟩)
        refine Or.inl (Finset.mem_sdiff.mpr ⟨hyC, ?_⟩)
        intro hyz
        rw [Finset.mem_singleton] at hyz
        subst hyz
        exact hzD hy
    refine mem_missed.mpr ⟨hzC, x, D, hD, hxn, ?_⟩
    exact Finset.Subset.antisymm (by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨hy1, hy2⟩ := Finset.mem_sdiff.mp hy
        have hyD : y ∈ D := by
          by_contra hyn
          have hyDC : y ∈ C \ D := Finset.mem_sdiff.mpr ⟨hy1, hyn⟩
          rw [hCd] at hyDC
          exact hy2 hyDC
        have hy' : y ∈ D ∩ C := hceq ▸ hy
        exact (Finset.mem_inter.mp hy').1
      · rw [Finset.mem_singleton] at hy
        exact hy ▸ hxD) hDsub
  · right
    have hcardle : D.card ≤ Fintype.card V := by
      have h1 := Finset.card_le_univ D
      have h2 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
      omega
    have hsum : #(C ∪ D) + #(C ∩ D) = 5 + D.card := by
      have h1 := Finset.card_union_add_card_inter C D
      rw [hC5] at h1
      exact h1
    have hcup : #(C ∪ D) ≤ 7 := by
      have h2 := Finset.card_le_univ (C ∪ D)
      have h3 : ((Finset.univ : Finset V)).card = Fintype.card V := Finset.card_univ
      omega
    have hsym : (C ∩ D).card = (D ∩ C).card := by rw [Finset.inter_comm]
    have hle5 : D.card ≤ 5 := by
      have h3 : (D ∩ C).card ≤ 3 := by omega
      have h3' : (C ∩ D).card ≤ 3 := by rw [Finset.inter_comm]; exact h3
      omega
    have hodd := card_mod_two_of_isOddCycle hD
    have hne3 : D.card ≠ 3 := by
      intro heq
      refine htf D ?_
      exact isNClique_three_of_isOddCycle hD heq
    have hge3 : 3 ≤ D.card := isOddCycle_card_ge_three hD
    have hcases : D.card = 3 ∨ D.card = 5 := by omega
    have hD5 : D.card = 5 := by
      rcases hcases with h | h
      · exact absurd h hne3
      · exact h
    have hsum' : #(C ∪ D) + #(C ∩ D) = 10 := by rw [hsum, hD5]
    have hle : #(C ∪ D) + #(C ∩ D) ≤ 7 + (C ∩ D).card := Nat.add_le_add_right hcup _
    refine ⟨D, hD, hD5, ?_, hzD⟩
    omega

/-- **THE THREE-INTERSECTION FIVE-CYCLES OF `C`.** -/
noncomputable def ThreeCycles (G : SimpleGraph V) (C : Finset V) : Finset (Finset V) := by
  classical
  exact (Finset.univ : Finset (Finset V)).filter
    (fun D : Finset V => IsOddCycle G D ∧ D.card = 5 ∧ (D ∩ C).card = 3)

@[simp] theorem mem_threeCycles {C D : Finset V} :
    D ∈ ThreeCycles G C ↔ IsOddCycle G D ∧ D.card = 5 ∧ (D ∩ C).card = 3 := by
  simp only [ThreeCycles, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **THE MISSED POINTS OF `C` NUMBER AT MOST FOUR — GIVEN THAT THE THREE-INTERSECTION FIVE-CYCLE IS
UNIQUE.**

Every missed point is either missed by a four-intersection five-cycle (at most two of them, Part 2) or
missed by a three-intersection five-cycle, and by `huniq` there is at most one such five-cycle, which
misses exactly two points.  So at most four of the five points of `C` are missed. -/
theorem card_allMissed_le_four_of_unique {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    (hV : Fintype.card V ≤ 7)
    (huniq : ∀ D D' : Finset V, IsOddCycle G D → IsOddCycle G D' → D.card = 5 → D'.card = 5 →
      (D ∩ C).card = 3 → (D' ∩ C).card = 3 → D = D') :
    (AllMissed (G := G) (C := C)).card ≤ 4 := by
  obtain ⟨c, hc, hmeet⟩ := exists_mem_meetsFour hC hshort hC5 f hf hcyc hmem htf hV
  have htwo : (Missed (G := G) (C := C)).card ≤ 2 :=
    card_missed_le_two_of_card_le_seven hC hshort hC5 f hf hcyc hmem htf hV
  by_cases hne : (ThreeCycles (G := G) C).Nonempty
  · obtain ⟨D₀, hD₀mem⟩ := hne
    have hD₀ : IsOddCycle G D₀ ∧ D₀.card = 5 ∧ (D₀ ∩ C).card = 3 := mem_threeCycles.mp hD₀mem
    have hsub : AllMissed (G := G) (C := C) ⊆ Missed (G := G) (C := C) ∪ (C \ D₀) := by
      intro z hz
      rw [Finset.mem_union]
      rcases mem_missed_or_three hC hshort hC5 f hf hcyc hmem htf hV hc hmeet hz with h | h
      · exact Or.inl h
      · obtain ⟨D, hD, hD5, hinter, hzD⟩ := h
        have hzC : z ∈ C := (mem_allMissed.mp hz).1
        have hDeq : D = D₀ := huniq D D₀ hD hD₀.1 hD5 hD₀.2.1 hinter hD₀.2.2
        have hzD' : z ∉ D₀ := by rw [hDeq] at hzD; exact hzD
        exact Or.inr (Finset.mem_sdiff.mpr ⟨hzC, hzD'⟩)
    have hpair : (C \ D₀).card = 2 := by
      have hinter : #(C ∩ D₀) = 3 := by rw [Finset.inter_comm]; exact hD₀.2.2
      have h1 := Finset.card_sdiff_add_card_inter C D₀
      omega
    have h1 := Finset.card_le_card hsub
    have h2 : ((Missed (G := G) (C := C)) ∪ (C \ D₀)).card
        ≤ (Missed (G := G) (C := C)).card + (C \ D₀).card :=
      Finset.card_union_le _ _
    omega
  · have hempty : ThreeCycles G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hsub : AllMissed (G := G) (C := C) ⊆ Missed (G := G) (C := C) := by
      intro z hz
      rcases mem_missed_or_three hC hshort hC5 f hf hcyc hmem htf hV hc hmeet hz with h | h
      · exact h
      · obtain ⟨D, hD, hD5, hinter, hzD⟩ := h
        refine absurd (mem_threeCycles.mpr ⟨hD, hD5, hinter⟩) ?_
        rw [hempty]
        simp
    have h1 := Finset.card_le_card hsub
    omega

/-- **THE FIVE-CYCLE CASE, CLOSED GIVEN `JSP90.ThreeIntersectionFiveCycleUnique`: THE ODD CYCLES OF `G`
HAVE A COMMON VERTEX.** -/
theorem hitsOddCycles_singleton_of_unique {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    (hV : Fintype.card V ≤ 7)
    (huniq : ∀ D D' : Finset V, IsOddCycle G D → IsOddCycle G D' → D.card = 5 → D'.card = 5 →
      (D ∩ C).card = 3 → (D' ∩ C).card = 3 → D = D') :
    ∃ c : V, HitsOddCycles G {c} := by
  have hcard := card_allMissed_le_four_of_unique hC hshort hC5 f hf hcyc hmem htf hV huniq
  have hsub : (AllMissed (G := G) (C := C) : Finset V) ⊆ C := by
    intro y hy
    exact (mem_allMissed.mp hy).1
  have h1 := Finset.card_le_card hsub
  have hlt : (AllMissed (G := G) (C := C)).card < C.card := by rw [hC5]; omega
  obtain ⟨c, hc, hcM⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨c, fun D hD hnot => ?_⟩
  refine absurd (mem_allMissed.mpr ⟨hc, D, hD, ?_⟩) hcM
  intro hcin
  refine absurd (Finset.mem_inter.mpr ⟨hcin, Finset.mem_singleton.mpr rfl⟩) ?_
  rw [hnot]
  simp

/-- **ERD\u0151S #73 AT `k = 1` WITH THE CONSTANT `1` FOR A SHORTEST ODD FIVE-CYCLE, GIVEN
`JSP90.ThreeIntersectionFiveCycleUnique`.**  With `huniq` instantiated at
`JSP90.ThreeIntersectionFiveCycleUnique C D D'`, this is
`JSP90.closeToBipartite 1 G` at `|V| \u2264 7` and `LocIndep 1`: the missing statement of
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven` is *exactly* `huniq`. -/
theorem closeToBipartite_one_of_unique {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    (hV : Fintype.card V ≤ 7)
    (huniq : ∀ D D' : Finset V, IsOddCycle G D → IsOddCycle G D' → D.card = 5 → D'.card = 5 →
      (D ∩ C).card = 3 → (D' ∩ C).card = 3 → D = D') :
    CloseToBipartite 1 G := by
  obtain ⟨c, hc⟩ := hitsOddCycles_singleton_of_unique hC hshort hC5 f hf hcyc hmem htf hV huniq
  exact ⟨{c}, by simp, isBipartite_delete_of_hitsOddCycles hc⟩

end
end JSP90
