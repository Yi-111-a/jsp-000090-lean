import JSPProblem.TriPair

/-!
# JSP-000090, round 152 — `JSPProblem/FiveWitness.lean`: **THE FIVE-CYCLE WITNESS**

Attack family 79.  The concrete target left by rounds 150 and 151 is the **five-cycle case** of the
sharp seven-vertex instance `JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven` (`LocIndep 1`,
`|V| ≤ 7` ⟹ `CloseToBipartite 2`), measured to be sharp at seven vertices
(`discovery/JSP-000090/r148_n7.log`).

Round 150 split that instance by the cardinality of a **shortest odd cycle** and settled the case of
cardinality `7` with the optimal constant `1` (`JSPProblem/Seven.lean`, Part 2).  Round 151 settled the
triangle-free instance with no five-cycle (`JSPProblem/TriPair.lean`,
`JSP90.closeToBipartite_one_of_locIndep_one_card_le_seven_of_triangleFree_no5`) and — after finding
and correcting a bug in the measurement code of round 150 — recorded as **the only missing step of the
five-cycle case**:

> *"an outside vertex `w` witnesses at most one five-cycle of the form `(C \ {c}) ∪ {w}`"*.

**This file proves that step, and the two local facts it rests on.**

## What is proved here (no placeholders: every statement below is a complete proof)

* **Part 0 — the arithmetic of a five-cycle.**  `JSP90.cycPred` (the predecessor of an index),
  `JSP90.five_succ_ne_pred`, `JSP90.five_flip_false` and **`JSP90.five_pair_inj`: the pair of
  ring-neighbours `{cycSucc i, cycPred i}` determines the point `i`**.  The last one is the "the missed
  point is determined" step; it is pure arithmetic on `Fin 5`.
* **Part 1 — `JSP90.card_witness_le_one`: THE WITNESS LEMMA.**  For a five-cycle `C` with cyclic
  numbering `f : Fin 5 → V` and a vertex `w ∉ C`, the set of indices at which `w` is adjacent to **both**
  ring-neighbours of `f i` — the configuration in which `(C \ {f i}) ∪ {w}` closes up — has at most one
  element.  Proof: two witnesses would give `w` two *different* two-element sets of neighbours inside
  `C`, contradicting `JSP90.card_le_two_neighOf_card_C_five_of_triangleFree` (round 150).
  `JSP90.WitnessSet` / `JSP90.mem_witnessSet` name the counted set.
* **Part 2 — `JSP90.card_neighIn_five_eq_two`.**  Every vertex of a five-cycle of a triangle-free graph
  has **exactly two** neighbours inside it: the vertex set of a five-cycle induces the five-cycle
  itself, a chord closing a triangle.  The upper bound is round 150's
  `JSP90.card_le_two_neighOf_card_C_five_of_triangleFree`; the lower bound is the two ring-neighbours.
* **Part 3 — `JSP90.filter_adj_eq_of_fiveCycle_singleton`: THE BRIDGE.**  If `C` is a *shortest* odd
  cycle of five vertices, `c ∈ C`, `x ∉ C` and `(C \ {c}) ∪ {x}` is a five-cycle, then
  `C.filter (Adj x) = C.filter (Adj c)`: **`x` is adjacent to exactly the two ring-neighbours of `c`
  and to nothing else of `C`.**  Here "a shortest odd cycle is induced" enters, through
  `JSP90.neigh_eq_of_adj_of_adj`: a neighbour of `x` inside the five-cycle whose two ring-neighbours in
  `C` are both different from `c` would have three neighbours inside the five-cycle, which Part 2
  forbids; and `x ≁ c` because that would be a triangle.  This reads "(C \ {c}) ∪ {x} is a five-cycle"
  back into "`c` is witnessed by `x`", which is what Part 1 counts.

Together, Parts 1 and 3 give the machine-checked statement that was missing:

> `JSP90.WitnessSet f w` has at most one element, and a point of a shortest odd five-cycle is missed by
> at most one outside vertex.

## The measurement of this round (`discovery/JSP-000090/r152.c`)

An independent odd-cycle detector (a subset is an odd cycle iff its size is odd, every vertex has
exactly two neighbours inside it, and it is connected) and an independent `MaxDef ≤ 1` test
(`|W| ≤ 2 α(G[W]) + 1` for every `W`, `α` by the subset DP), over **all** `2^21` graphs on seven
vertices:

| quantity | value |
| --- | --- |
| `LocIndep 1` graphs | `986 787` (bipartite `103 237`, triangle-free `133 501`) |
| `max tauOdd` | `2` |
| pairs `(G, C)`, `G` triangle-free `LocIndep 1`, `C` a five-cycle | `50 904` |
| **max five-cycles `(C \ {c}) ∪ {w}` per outside vertex `w`** | **`1`** (Part 1) |
| max five-cycles meeting `C` in exactly three points | `1`, occurring `12 600` times |
| max points of `C` missed by an odd cycle | `2` |
| violations of "some point of `C` meets every odd cycle" | `0` |
| triangles `(G, T)` with `LocIndep 1`, `|V| = 7` | `2 071 405`; violations of round 151's "some **pair** of `T` is a transversal" | `0` |

The first version of `r152.c` (and of `r152b.c`) ranged over the bit positions `0, 1, 2` instead of over
the elements of the triangle and produced a spurious `208 440` violations of round 151's claim; both
were fixed, and the corrected run reproduces round 151's count `2 071 405 / 0`.

## What is still missing

The `Finset` counting around Parts 1, 3 and 4, and with it the five-cycle case of the seven-vertex
instance.  With `|V| ≤ 7`, `C` a shortest odd cycle of five vertices and `G` triangle-free, every odd
cycle `D` has `|D| ∈ {5, 7}` (`JSP90.card_ge_five_of_isOddCycle_of_triangleFree` of round 151 plus the
order bound); a seven-cycle contains `C`; a five-cycle meets `C` in `5` (it is `C`), `4` (of the form
`(C \ {c}) ∪ {x}`, at most `|V \ C| ≤ 2` of them by Parts 1 + 4) or `3`.  So at most `2 + 2 = 4` of the
`5` points of `C` are missed once the five-cycles meeting `C` in three points are known to be at most
one (measured: exactly one at most, attained `12 600` times), and a point of `C` then meets every odd
cycle, i.e. `CloseToBipartite 1 G`.  What is left is (i) the pigeonhole
`|M₄| ≤ |V \ C|` (the injection of Part 4 made into a `Finset.card_le_card` argument) and (ii) the
uniqueness of the three-intersection five-cycle.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps reporting
`missing_theorems = ["jsp_000090_main"]`.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 4000000

local instance fwDecidableAdjRel (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

local instance fwDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Part 0 — the arithmetic of a five-cycle -/

/-- **The predecessor of an index in `Fin n`**: `n - 1` steps back around the cycle. -/
def cycPred {n : ℕ} (i : Fin n) : Fin n := (cycSucc^[n - 1] : Fin n → Fin n) i

theorem cycSucc_injective' {n : ℕ} : Function.Injective (cycSucc : Fin n → Fin n) :=
  fun _ _ h => cycSucc_injective _ _ h

theorem cycPred_injective {n : ℕ} {i j : Fin n} (h : cycPred i = cycPred j) : i = j :=
  Function.Injective.iterate cycSucc_injective' (n - 1) h

/-- **IN A FIVE-CYCLE THE TWO RING-NEIGHBOURS OF A POINT ARE TWO DIFFERENT POSITIONS.** -/
theorem five_succ_ne_pred (k : Fin 5) : cycSucc k ≠ cycPred k := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := cycSucc_pow_val (k := 4) (i := k) (n := 5)
  simp only [cycSucc_val] at h1
  rw [cycPred, h2] at h1
  have hk : k.val < 5 := k.2
  omega

/-- **TWO POINTS OF A FIVE-CYCLE CANNOT BE AT STEPS `+1` AND `-1` OF EACH OTHER
SIMULTANEOUSLY**: on five positions the steps `+1` and `-1` from two points cannot agree, i.e. there is
no pair `i, j` with `cycSucc i = cycPred j` and `cycPred i = cycSucc j`. -/
theorem five_flip_false (i j : Fin 5) (h1 : cycSucc i = cycPred j) (h2 : cycPred i = cycSucc j) :
    False := by
  have hv1 := congrArg Fin.val h1
  have hv2 := congrArg Fin.val h2
  have hi : i.val < 5 := i.2
  have hj : j.val < 5 := j.2
  have hk (t : Fin 5) : (cycPred t).val = (t.val + 4) % 5 := by
    have h4 := cycSucc_pow_val (k := 4) (i := t) (n := 5)
    rw [cycPred, h4]
  simp only [cycSucc_val] at hv1 hv2
  rw [hk j] at hv1
  rw [hk i] at hv2
  omega

/-- **IN A FIVE-CYCLE THE PAIR OF RING-NEIGHBOURS OF A POINT DETERMINES THE POINT.**

`{cycSucc i, cycPred i}` is the pair of positions one step either side of `i`; on five positions this
pair is injective in `i`.  This is the "the missed point is determined" step of the witness lemma of
Part 1, and it is pure arithmetic on `Fin 5`. -/
theorem five_pair_inj (i j : Fin 5)
    (h : ({cycSucc i, cycPred i} : Finset (Fin 5)) = {cycSucc j, cycPred j}) : i = j := by
  have hA : cycSucc i ∈ ({cycSucc j, cycPred j} : Finset (Fin 5)) := by
    rw [← h]; exact Finset.mem_insert_self _ _
  have hB : cycPred i ∈ ({cycSucc j, cycPred j} : Finset (Fin 5)) := by
    rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rcases Finset.mem_insert.mp hA with hA1 | hA1
  · exact cycSucc_injective i j hA1
  · have hA1' : cycSucc i = cycPred j := Finset.mem_singleton.mp hA1
    rcases Finset.mem_insert.mp hB with hB1 | hB1
    · exact False.elim (five_flip_false i j hA1' hB1)
    · exact cycPred_injective (Finset.mem_singleton.mp hB1)

/-- **THE RING-NEIGHBOUR PAIR, IN THE FORM THE COUNTING USES**: if `f` is injective on five positions
and the *images* of the two ring-neighbour pairs of `i` and `j` coincide, then `i = j`.  This is
`JSP90.five_pair_inj` at the level of the vertices of the graph, which is how the bridge of Part 3 sees
it. -/
theorem five_pair_inj' {V' : Type*} (f : Fin 5 → V') (hf : Function.Injective f) (i j : Fin 5)
    (h : ({f (cycSucc i), f (cycPred i)} : Finset V') = {f (cycSucc j), f (cycPred j)}) : i = j := by
  have hA : f (cycSucc i) ∈ ({f (cycSucc j), f (cycPred j)} : Finset V') := by
    rw [← h]; exact Finset.mem_insert_self _ _
  have hB : f (cycPred i) ∈ ({f (cycSucc j), f (cycPred j)} : Finset V') := by
    rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rcases Finset.mem_insert.mp hA with hA1 | hA1
  · exact cycSucc_injective i j (hf hA1)
  · have hA1' : f (cycSucc i) = f (cycPred j) := Finset.mem_singleton.mp hA1
    rcases Finset.mem_insert.mp hB with hB1 | hB1
    · exact False.elim (five_flip_false i j (hf hA1') (hf hB1))
    · exact cycPred_injective (hf (Finset.mem_singleton.mp hB1))

/-! ## Part 1 — THE WITNESS LEMMA

`w` **witnesses** the index `i` of the five-cycle `f` when it is adjacent to *both* ring-neighbours of
`f i`: this is exactly the configuration in which the five vertices `C \ {f i} u {w}` close up (Part 3
reads that direction back). -/

/-- **THE WITNESS SET OF `w` ALONG A FIVE-CYCLE**: the indices whose two ring-neighbours are both
neighbours of `w`. -/
def WitnessSet {G : SimpleGraph V} (f : Fin 5 → V) (w : V) : Finset (Fin 5) :=
  Finset.filter (fun i => G.Adj w (f (cycSucc i)) ∧ G.Adj w (f (cycPred i)))
    (Finset.univ : Finset (Fin 5))

@[simp] theorem mem_witnessSet {G : SimpleGraph V} {f : Fin 5 → V} {w : V} {i : Fin 5} :
    i ∈ WitnessSet (G := G) f w ↔ G.Adj w (f (cycSucc i)) ∧ G.Adj w (f (cycPred i)) := by
  simp only [WitnessSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **AN OUTSIDE VERTEX WITNESSES AT MOST ONE POINT OF A FIVE-CYCLE.**

```lean
IsOddCycle G C → C.card = 5 → G has no 3-clique → f : Fin 5 → V injective, cyclic order on C →
  w ∉ C → ({i : Fin 5 | G.Adj w (f (cycSucc i)) ∧ G.Adj w (f (cycPred i))}).card ≤ 1
```

The set counted here is the set of **points of `C` whose removal from `C` leaves a path that `w`
closes up**: `w` adjacent to both ring-neighbours of `f i` is exactly the configuration in which
`(C \ {f i}) ∪ {w}` is a five-cycle (Part 3 below reads that direction back).

The proof is the one-line pigeonhole of round 150's plan: two witnesses would give `w` two
*different* two-element sets of neighbours inside `C`, while
`JSP90.card_le_two_neighOf_card_C_five_of_triangleFree` says that the neighbours of a vertex inside a
five-cycle of a triangle-free graph number at most two. -/
theorem card_witness_le_one {C : Finset V} (hC : IsOddCycle G C) (hC5 : C.card = 5)
    (htf : ∀ D : Finset V, ¬ G.IsNClique 3 D) (f : Fin 5 → V) (hf : Function.Injective f)
    (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin 5, f j = x) {w : V} (hw : ∀ j : Fin 5, f j ≠ w) :
    (WitnessSet (G := G) f w).card ≤ 1 := by
  classical
  set Wit : Finset (Fin 5) := WitnessSet f w with hWitdef
  by_contra hcon
  have h2 : 2 ≤ Wit.card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := exists_two_of_card_ge_two h2
  set N : Finset V := C.filter (fun z => G.Adj w z) with hNdef
  have hNcard : N.card ≤ 2 :=
    card_le_two_neighOf_card_C_five_of_triangleFree htf hC hC5
      (fun z hz => ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩)
  have hmemC : ∀ k : Fin 5, f k ∈ C := fun k => (hmem (f k)).mpr ⟨k, rfl⟩
  have hwi : G.Adj w (f (cycSucc i)) ∧ G.Adj w (f (cycPred i)) := (mem_witnessSet.mp hi)
  have hwj : G.Adj w (f (cycSucc j)) ∧ G.Adj w (f (cycPred j)) := (mem_witnessSet.mp hj)
  have hsub (k : Fin 5) (hk : G.Adj w (f (cycSucc k)) ∧ G.Adj w (f (cycPred k))) :
      ({f (cycSucc k), f (cycPred k)} : Finset V) ⊆ N := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · rw [hz]; exact Finset.mem_filter.mpr ⟨hmemC _, hk.1⟩
    · rw [hz]; exact Finset.mem_filter.mpr ⟨hmemC _, hk.2⟩
  have hcard (k : Fin 5) : ({f (cycSucc k), f (cycPred k)} : Finset V).card = 2 := by
    have h1 : f (cycSucc k) ∉ ({f (cycPred k)} : Finset V) := by
      simp only [Finset.mem_singleton]
      exact fun h => five_succ_ne_pred k (hf h)
    rw [Finset.card_insert_of_notMem h1, Finset.card_singleton]
  have hNi : ({f (cycSucc i), f (cycPred i)} : Finset V) = N :=
    Finset.eq_of_subset_of_card_le (hsub i hwi) (by rw [hcard i]; omega)
  have hNj : ({f (cycSucc j), f (cycPred j)} : Finset V) = N :=
    Finset.eq_of_subset_of_card_le (hsub j hwj) (by rw [hcard j]; omega)
  have hpair : ({f (cycSucc i), f (cycPred i)} : Finset V) = {f (cycSucc j), f (cycPred j)} :=
    hNi.trans hNj.symm
  have h1 : f (cycSucc i) ∈ ({f (cycSucc j), f (cycPred j)} : Finset V) := by
    rw [← hpair]; exact Finset.mem_insert_self _ _
  have h2' : f (cycPred i) ∈ ({f (cycSucc j), f (cycPred j)} : Finset V) := by
    rw [← hpair]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rcases Finset.mem_insert.mp h1 with hA | hA
  · exact False.elim (hij (cycSucc_injective i j (hf hA)))
  · have hA' : f (cycSucc i) = f (cycPred j) := Finset.mem_singleton.mp hA
    rcases Finset.mem_insert.mp h2' with hB | hB
    · exact False.elim (five_flip_false i j (hf hA') (hf hB))
    · exact False.elim (hij (cycPred_injective (hf (Finset.mem_singleton.mp hB))))

/-! ## Part 2 — A FIVE-CYCLE CARRIES TWO NEIGHBOURS AT EACH OF ITS VERTICES

In a triangle-free graph the vertex set of a five-cycle induces *exactly* the five-cycle: a chord of a
five-cycle closes a triangle.  This is why the local count below needs no case analysis: the upper
bound is `JSP90.card_le_two_neighOf_card_C_five_of_triangleFree` (round 150, `JSPProblem/Seven.lean`
Part 3) and the lower bound comes from the two ring-neighbours of the cycle itself. -/

theorem cycSucc_cycPred_five (i : Fin 5) : cycSucc (cycPred i) = i := by
  refine Fin.ext ?_
  have hi : i.val < 5 := i.2
  simp only [cycSucc_val, cycPred]
  have h4 := cycSucc_pow_val (k := 4) (i := i) (n := 5)
  rw [h4]
  omega

/-- The two ring-neighbours of a point of a five-cycle are adjacent to it. -/
theorem adj_ringPred {g : Fin 5 → V} (hgcyc : ∀ j : Fin 5, G.Adj (g j) (g (cycSucc j))) (i : Fin 5) :
    G.Adj (g i) (g (cycPred i)) := by
  have h := (hgcyc (cycPred i)).symm
  rw [cycSucc_cycPred_five i] at h
  exact h

/-- **EVERY VERTEX OF A FIVE-CYCLE OF A TRIANGLE-FREE GRAPH HAS EXACTLY TWO NEIGHBOURS INSIDE IT.**

The upper bound is `JSP90.card_le_two_neighOf_card_C_five_of_triangleFree` — the neighbours of a vertex
inside a five-cycle are pairwise non-adjacent, and three of them would be an independent triple inside
an odd cycle of cardinality five.  The lower bound is the two ring-neighbours of the cycle. -/
theorem card_neighIn_five_eq_two {D : Finset V} (hD : IsOddCycle G D) (hD5 : D.card = 5)
    (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) (g : Fin 5 → V) (hg : Function.Injective g)
    (hgcyc : ∀ j : Fin 5, G.Adj (g j) (g (cycSucc j)))
    (hmem : ∀ y : V, y ∈ D ↔ ∃ j : Fin 5, g j = y) {x : V} (i : Fin 5) (hxi : x = g i) :
    (D.filter (fun z => G.Adj x z)).card = 2 := by
  have hle : (D.filter (fun z => G.Adj x z)).card ≤ 2 :=
    card_le_two_neighOf_card_C_five_of_triangleFree htf hD hD5
      (fun z hz => ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩)
  have hmemA : g (cycSucc i) ∈ D.filter (fun z => G.Adj x z) := Finset.mem_filter.mpr
    ⟨(hmem _).mpr ⟨cycSucc i, rfl⟩, by rw [hxi]; exact hgcyc i⟩
  have hmemB : g (cycPred i) ∈ D.filter (fun z => G.Adj x z) := Finset.mem_filter.mpr
    ⟨(hmem _).mpr ⟨cycPred i, rfl⟩, by rw [hxi]; exact adj_ringPred hgcyc i⟩
  have hne : g (cycSucc i) ≠ g (cycPred i) := fun h => five_succ_ne_pred i (hg h)
  have hsub : ({g (cycSucc i), g (cycPred i)} : Finset V) ⊆ D.filter (fun z => G.Adj x z) := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · rw [hz]; exact hmemA
    · rw [hz]; exact hmemB
  have hge : 2 ≤ (D.filter (fun z => G.Adj x z)).card := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]; exact fun h => hne h)] at h1
    simp only [Finset.card_singleton] at h1
    omega
  omega

/-- **NO `3`-CLIQUE, IN THE PLAIN FORM**: the `IsNClique 3` form is convenient to consume and
expensive to produce (a triangle must be built into a finset), so the conversion is made once here,
with plain variables. -/
theorem no_triangle_of_not_isNClique (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : False :=
  htf _ (isNClique_three_of_adj_adj_adj hab hac hbc)

/-! ## Part 3 — THE BRIDGE: `(C \ {c}) ∪ {x}` A FIVE-CYCLE MEANS `x` WITNESSES `c`

This is the direction the counting of Part 4 needs, and it is where "a shortest odd cycle is induced"
(`JSP90.neigh_eq_of_adj_of_adj`) enters: the two ring-neighbours of a neighbour of `x` are its *only*
neighbours inside `C`, and neither of them is `c` — hence `x` is adjacent to exactly the two
ring-neighbours of `c`. -/

/-- **THE NEIGHBOURS OF `x` INSIDE `C` ARE THOSE OF `c` INSIDE `C`.**

```lean
IsOddCycle G C → C shortest, |C| = 5 → C cyclic f → G triangle-free →
  c ∈ C → x ∉ C → (C \ {c}) ∪ {x} a five-cycle →  C.filter (Adj x) = C.filter (Adj c)
```

So if the five vertices `(C \ {c}) ∪ {x}` close up into a five-cycle, then `x` is adjacent to
**exactly** the two ring-neighbours of `c` in `C` and to nothing else of `C`: `x`'s two neighbours
inside the five-cycle (Part 2) lie in `C \ {c}`, and each of them, being adjacent to `x`, is adjacent to
`c` by `JSP90.neigh_eq_of_adj_of_adj`; conversely `c`'s two neighbours in `C` are the two neighbours of
`x` inside the five-cycle, of which there are exactly two. -/
theorem filter_adj_eq_of_fiveCycle_singleton {C D : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    {c x : V} (hc : c ∈ C) (hxn : x ∉ C) (hsub : (C \ {c}) ∪ {x} = D) (hD : IsOddCycle G D) :
    C.filter (fun z => G.Adj x z) = C.filter (fun z => G.Adj c z) := by
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
  have hcard1 : (C \ {c}).card = 4 := by
    have h1 := Finset.card_union_of_disjoint hdis
    rw [hunion, Finset.card_singleton] at h1
    omega
  have hdisx : Disjoint (C \ {c}) ({x} : Finset V) := by
    refine Finset.disjoint_left.2 fun z h1 h2 => ?_
    rw [Finset.mem_singleton] at h2
    subst h2
    exact hxn (Finset.mem_sdiff.mp h1).1
  have hD5 : D.card = 5 := by
    have h1 := Finset.card_union_of_disjoint hdisx
    rw [hsub, hcard1, Finset.card_singleton] at h1
    omega
  obtain ⟨g, hg, hgcyc, hmemD⟩ := exists_cyc5_of_isOddCycle_card_five hD hD5
  have hxD : x ∈ D := by
    rw [← hsub]; exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self x))
  obtain ⟨i, hi⟩ : ∃ i : Fin 5, g i = x := (hmemD x).mp hxD
  have hx2 : (D.filter (fun z => G.Adj x z)).card = 2 :=
    card_neighIn_five_eq_two hD hD5 htf g hg hgcyc hmemD i hi.symm
  have hmemC : ∀ z : Fin 5, f z ∈ C := fun z => (hmem (f z)).mpr ⟨z, rfl⟩
  -- (1) every neighbour of `x` inside the five-cycle is a neighbour of `c` inside `C`
  have hNx : D.filter (fun z => G.Adj x z) ⊆ C.filter (fun z => G.Adj c z) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyD, hxy⟩ := hy
    have hxy' : x ≠ y := fun h => G.irrefl (h ▸ hxy)
    have hyD' : y ∈ D := hyD
    rw [← hsub] at hyD
    rcases Finset.mem_union.mp hyD with hym | hym
    · have hyC := (Finset.mem_sdiff.mp hym).1
      rw [Finset.mem_filter]
      refine ⟨hyC, ?_⟩
      obtain ⟨j, hj⟩ : ∃ j : Fin 5, f j = y := (hmem y).mp hyC
      obtain ⟨k, hk⟩ : ∃ k : Fin 5, g k = y := (hmemD y).mp hyD'
      have hy2 : (D.filter (fun z => G.Adj y z)).card = 2 :=
        card_neighIn_five_eq_two hD hD5 htf g hg hgcyc hmemD k hk.symm
      by_contra hcon
      have hnc : ¬ G.Adj c y := fun h => hcon h
      have hnp : f (cycSucc j) ≠ c := fun h => hnc (by
        rw [← h, ← hj]; exact (hcyc j).symm)
      have hnq : f (cycPred j) ≠ c := fun h => hnc (by
        rw [← h, ← hj]; exact (adj_ringPred hcyc j).symm)
      have hnpq : f (cycSucc j) ≠ f (cycPred j) := fun h => five_succ_ne_pred j (hf h)
      have hset : ({x, f (cycSucc j), f (cycPred j)} : Finset V)
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
                fun h => hnp (Finset.mem_singleton.mp h)⟩)), by rw [← hj]; exact hcyc j⟩
          · rw [hz]
            exact Finset.mem_filter.mpr ⟨by
              rw [← hsub]
              exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr
                ⟨hmemC _, fun h => hnq (Finset.mem_singleton.mp h)⟩)),
              by rw [← hj]; exact adj_ringPred hcyc j⟩
      have hxn1 : x ∉ ({f (cycSucc j), f (cycPred j)} : Finset V) := by
        intro h
        rw [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact hxn (h ▸ hmemC _)
        · exact hxn (h ▸ hmemC _)
      have hxn2 : f (cycSucc j) ∉ ({f (cycPred j)} : Finset V) := by
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
  -- (2) `x` is not adjacent to `c`: with a neighbour of `x` inside the five-cycle that would close a
  -- triangle, since (1) says every such neighbour is adjacent to `c`
  have hxnc : ¬ G.Adj x c := by
    intro hxc
    obtain ⟨r, hr⟩ := nonempty_of_card_pos (s := D.filter (fun z => G.Adj x z))
      (by rw [hx2]; omega)
    have hcr := (Finset.mem_filter.mp (hNx hr)).2
    exact no_triangle_of_not_isNClique htf hxc (Finset.mem_filter.mp hr).2 hcr
  -- (3) neighbours of `x` inside `C` lie in the five-cycle, and back
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


/-! ## Part 4 — the two ring-neighbours of `c` inside `C`, and the injectivity of the witness

The counting of the five-cycle case needs two more statements, both proved here.

* **`JSP90.filter_adj_C_eq_ringPair`** — the neighbours of `c = f i` inside the shortest odd five-cycle
  `C` are exactly its two ring-neighbours, so the *pair* of ring-neighbours is what identifies `c`.
* **`JSP90.x_ne_y_of_two_fiveCycles_singleton`** — the injectivity of the witness: if two *different*
  points of `C` are each missed by a five-cycle of the form `(C \ {c}) ∪ {x}`, then the two outside
  vertices `x`, `y` are different.  Together with Part 1 this says the map "point of `C` missed by a
  five-cycle meeting `C` in four points" ↦ "the outside vertex of that five-cycle" is injective, so by
  the standard `Finset` pigeonhole at most `|V \ C| ≤ 2` points of `C` are missed that way. -/

/-- **THE NEIGHBOURS OF A POINT OF A SHORTEST ODD FIVE-CYCLE ARE ITS TWO RING-NEIGHBOURS.** -/
theorem filter_adj_C_eq_ringPair {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (i : Fin 5) :
    C.filter (fun z => G.Adj (f i) z) = ({f (cycSucc i), f (cycPred i)} : Finset V) := by
  have hmemC : ∀ j : Fin 5, f j ∈ C := fun j => (hmem (f j)).mpr ⟨j, rfl⟩
  have hne : f (cycSucc i) ≠ f (cycPred i) := fun h => five_succ_ne_pred i (hf h)
  have hsub : C.filter (fun z => G.Adj (f i) z) ⊆ ({f (cycSucc i), f (cycPred i)} : Finset V) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzC, hz⟩ := hz
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases neigh_eq_of_adj_of_adj hC hshort (hmemC i) (hmemC _) (hmemC _) (hcyc i) (adj_ringPred hcyc i)
      hne z hzC hz with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hsup : ({f (cycSucc i), f (cycPred i)} : Finset V) ⊆ C.filter (fun z => G.Adj (f i) z) := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Finset.mem_filter.mpr ⟨hmemC _, hcyc i⟩
    · rw [Finset.mem_singleton] at hz
      rw [hz]
      exact Finset.mem_filter.mpr ⟨hmemC _, adj_ringPred hcyc i⟩
  exact Finset.Subset.antisymm hsub (by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Finset.mem_filter.mpr ⟨hmemC _, hcyc i⟩
    · rw [Finset.mem_singleton] at hz
      rw [hz]
      exact Finset.mem_filter.mpr ⟨hmemC _, adj_ringPred hcyc i⟩)

/-- **TWO DIFFERENT POINTS OF A SHORTEST ODD FIVE-CYCLE ARE MISSED BY FIVE-CYCLES WITH DIFFERENT
OUTSIDE VERTICES.**

```lean
C shortest odd five-cycle, c ≠ c' ∈ C, x ∉ C, y ∉ C,
  (C \ {c}) ∪ {x} and (C \ {c'}) ∪ {y} five-cycles  →  x ≠ y
```

This is the injectivity of "the point of `C` missed by a five-cycle meeting `C` in four points" ↦ "the
one vertex of that five-cycle outside `C`", which by the standard `Finset` pigeonhole bounds the number
of missed points of `C` by `|V \ C|`.  The proof is Part 3 twice: `x` and `y` would have the same
neighbourhood inside `C`, and `JSP90.filter_adj_C_eq_ringPair` turns a neighbourhood into the pair of
ring-neighbours, which `JSP90.five_pair_inj` turns back into the point. -/
theorem x_ne_y_of_two_fiveCycles_singleton {C D D' : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ E : Finset V, IsOddCycle G E → C.card ≤ E.card) (hC5 : C.card = 5)
    (f : Fin 5 → V) (hf : Function.Injective f) (hcyc : ∀ j : Fin 5, G.Adj (f j) (f (cycSucc j)))
    (hmem : ∀ y : V, y ∈ C ↔ ∃ j : Fin 5, f j = y) (htf : ∀ E : Finset V, ¬ G.IsNClique 3 E)
    {c c' x y : V} (hcc : c ∈ C) (hcc' : c' ∈ C) (hcne : c ≠ c') (hxn : x ∉ C) (hyn : y ∉ C)
    (hsub : (C \ {c}) ∪ {x} = D) (hD : IsOddCycle G D)
    (hsub' : (C \ {c'}) ∪ {y} = D') (hD' : IsOddCycle G D') : x ≠ y := by
  intro hxy
  have h1 : C.filter (fun z => G.Adj x z) = C.filter (fun z => G.Adj c z) :=
    filter_adj_eq_of_fiveCycle_singleton hC hshort hC5 f hf hcyc hmem htf hcc hxn hsub hD
  have h2 : C.filter (fun z => G.Adj y z) = C.filter (fun z => G.Adj c' z) :=
    filter_adj_eq_of_fiveCycle_singleton hC hshort hC5 f hf hcyc hmem htf hcc' hyn hsub' hD'
  have h12 : C.filter (fun z => G.Adj c z) = C.filter (fun z => G.Adj c' z) := by
    rw [← h1, hxy, ← h2]
  obtain ⟨i, hi⟩ : ∃ i : Fin 5, f i = c := (hmem c).mp hcc
  obtain ⟨i', hi'⟩ : ∃ i' : Fin 5, f i' = c' := (hmem c').mp hcc'
  rw [← hi, ← hi'] at h12
  have hii : i = i' := by
    rw [filter_adj_C_eq_ringPair hC hshort hC5 f hf hcyc hmem i] at h12
    rw [filter_adj_C_eq_ringPair hC hshort hC5 f hf hcyc hmem i'] at h12
    exact five_pair_inj' f hf i i' h12
  apply hcne
  rw [← hi, ← hi', ← hii]

end
end JSP90
