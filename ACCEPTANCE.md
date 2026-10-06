# ACCEPTANCE — JSP-000090

## Catalog statement (recovered from the official catalog, round 31)

`JSP-000090 · If local subgraphs have large independent sets, must the whole graph be close to
bipartite after few modifications?`

| Field | Value |
| --- | --- |
| Mathematical area | Graph theory |
| Date proposed | No later than 1982 |
| Current status | **Solved** |
| Lean proof (catalog) | **No** |
| Publication | `[Re99]` B. Reed, *Mangoes and Blueberries*, Combinatorica (1999), 267–296 |

The underlying problem is **Erdős Problem #73**
(`https://www.erdosproblems.com/73`):

> Let `k ≥ 0`. Let `G` be a graph such that **every subgraph `H` contains an independent set of
> size `≥ (n − k) / 2`**, where `n` is the number of vertices of `H`. Must `G` be the union of a
> bipartite graph and `O_k(1)` many vertices?

Reed (1999) proved it. The content of the theorem is the bound `O_k(1)`: for each fixed `k` there is
a constant `f(k)` such that removing at most `f(k)` vertices leaves `G` bipartite.

## Formal statement used by the Lean development

`lean/JSPProblem/Definitions.lean`:

* `LocIndep k G` — every vertex set `X` carries an independent set `S ⊆ X` with
  `2 * |S| + k ≥ |X|` (this is `|S| ≥ (|X| − k)/2`, phrased in ℕ to avoid rounding).
* `CloseToBipartite m G` — **deleting at most `m` vertices leaves a bipartite graph**
  (`lean/JSPProblem/Definitions.lean`: `∃ X, X.card ≤ m ∧ (deleteFinset G X).IsBipartite`, i.e. `G` is
  the union of a bipartite graph and at most `m` vertices).

  **Correction (round 34).**  The statement used earlier in this development read "there are disjoint
  `s`, `t` with `G.IsBipartiteWith s t` and all vertices outside `s ∪ t` covered by a set of at most
  `m` vertices".  That is degenerate: `IsBipartiteWith s t` forces every edge of `G` to join `s` to
  `t`, so the vertices of `V \ (s ∪ t)` are isolated and the predicate degenerates to "`G` is
  bipartite together with at most `m` isolated vertices".  Under it the catalog statement was
  **false already for `k = 1`**, because `K_3` satisfies `LocIndep 1` (`JSP90.completeGraph_locIndep`)
  but admits no bipartition for any `m`; this failure is recorded machine-checked as
  `JSP90.rejected_reading_fails`.  The definition now matches the catalog question and Erdős's
  wording, and `JSP90.closeToBipartite_completeGraph_three : CloseToBipartite 1 (K_3)` becomes
  provable.
* `Erdős73 k := ∃ m, ∀ G, LocIndep k G → CloseToBipartite m G` — the full statement, over all
  finite vertex types.

Checking induced subgraphs rather than arbitrary subgraphs is equivalent: if `H ≤ G` has vertex
set `X` then every independent set of `H` is one of `G[X]`, so `α(H) ≤ α(G[X])`.

## Required theorem

`jsp_000090_main` — the Lean name that the prize gate checks. It must be the **complete** Erdős
#73 theorem above (`Erdős73 k` for every `k`), proved with no `sorry`.

## Round 182 (`lean/JSPProblem/OddGirth3.lean`) — **AT `k = 1` THE ODD CYCLES OF A GRAPH OF
## DEFICIENCY `≤ 1` HAVE A COMMON POINT UNLESS A FIVE-CYCLE APPEARS** (new attack family 99)

`lake build` **OK** (1337 jobs); **0 `sorry`, 0 `admit`**; `harness/score.py problems/JSP-000090
--strict-prize`: `build_ok = true`, `partial_ok = true`,
`missing_theorems = ["jsp_000090_main"]`. 25 new declarations in one new file, imported from the
root module `JSPProblem.lean`; `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` on every headline result.

Rounds 176–180 pinned the remaining direction to a linear odd-cycle-transversal bound
`τ(G) ≤ C · MaxDef G`, with `C = 2` (the sharp form of Erdős #73) left open.  This round does **not**
attack that constant.  It attacks the **`k = 1` case of Erdős #73 on the class of graphs whose odd
cycles are all triangles** — a class on which the constant is `1`, so an instance there would be
*sharp*, and the class is infinite and unbounded in order (**no `|V|` bound appears in any statement
of the file**).

### The class

```lean
JSP90.OddGirthThree G := ∀ C, IsOddCycle G C → C.card = 3
```

### What `LocIndep 1` gives, as reusable lemmas

```lean
JSP90.inter_ne_empty_of_isOddCycle_of_locIndep_one (hG : LocIndep 1 G) {C D}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) : C ∩ D ≠ ∅
```

— **no two vertex-disjoint odd cycles**, since `t` disjoint odd cycles cost `t` units of deficiency
(`JSP90.defOf_biUnion_ge_card` of `PackDescent.lean`) and `MaxDef G ≤ 1`.  The second consequence,
"no `K₄`", was already in the development (`JSPProblem/OneK.lean`).

### The geometry of a triangle on a triangle

With `T = {a, b, c}` a triangle and every odd cycle a triangle, an odd cycle `D` sits on `T` in one of
two ways, both recorded as predicates — `JSP90.TriAt G T x` (meeting `T` in the single point `x`) and
`JSP90.TriCross G T x y` (meeting `T` along the edge `x y`) — and the outside points are computed by
`JSP90.exists_two_of_triAt` (two outside points, both adjacent to `x`) and
`JSP90.exists_third_of_triCross` (one outside point, adjacent to both `x` and `y`).

### The two obstructions (the content of the round)

```lean
JSP90.exists_oddCycle_card_five_of_triAt_two (hG : LocIndep 1 G) … :
    ∃ D, IsOddCycle G D ∧ D.card = 5
JSP90.not_triAt_two_of_oddGirthThree (hG : LocIndep 1 G) (hog : OddGirthThree G) … :
    ¬ (TriAt G T a ∧ TriAt G T b)

JSP90.exists_oddCycle_card_five_of_triCross_three (hG : LocIndep 1 G) … :
    ∃ D, IsOddCycle G D ∧ D.card = 5
JSP90.not_triCross_three_of_oddGirthThree (hG : LocIndep 1 G) (hog : OddGirthThree G) … :
    ¬ (TriCross G T a b ∧ TriCross G T a c ∧ TriCross G T b c)
```

* **Two triangles hanging at two points of a triangle force a five-cycle.**  The two triangles meet
  (no disjoint odd cycles) at a point `w ∉ T`; if their outside pairs coincide, the five points
  `a, c, b, w, u` are in cyclic adjacency, otherwise `u, a, b, v, w` are.
* **Three triangles crossing `T` along its three edges force a five-cycle.**  The three outside points
  lie outside `T` and are pairwise distinct — a coincidence is a `K₄` on `T` together with that point,
  which `LocIndep 1` forbids — and then `a, z, b, c, w` are in cyclic adjacency.

### What these two statements say

**At `LocIndep 1`, in a graph whose odd cycles are all triangles, the odd cycles hanging at the three
points of a triangle and those crossing its three edges form two families, each of which has a common
point.**  That is exactly what the `k = 1` case of Erdős #73 on this class turns on, and no earlier
round of this development had anything of the kind (rounds 166–171 carry `k = 1` only under
`|V| ≤ 7` or `|V| ≤ 8`, with the constant `2`; `JSPProblem/OneK.lean` shows that constant `2` is
forced, by `p9` = Petersen minus a vertex, so the sharp constant off this class is `2` and on it
`k4sub`-type obstructions do not exist).

### What is left — the single step missing in this file

The **assembly** is written but does **not** compile, so it is not in the file; it is named exactly
in `discovery/JSP-000090/policy.json`:

1. `JSP90.hitsOddCycles_singleton_of_triAt` — `TriAt G T a` gives that `a` meets **every** odd cycle.
   The only hard case is an odd cycle `D` avoiding `a`: then `D ∩ T = {b, c}`, so `D` is the triangle
   `{b, c, z}`; `D` meets the triangle hanging at `a`, whence `a ~ z`, and `{a, b, c, z}` is a `K₄`.
2. `JSP90.exists_hitsOddCycles_singleton_sub_T` — the case analysis on which of `a`, `b`, `c` lie in an
   odd cycle `D`: none contradicts `inter_ne_empty_of_isOddCycle_of_locIndep_one`, one gives a
   `TriAt` (excluded by `not_triAt_two_of_oddGirthThree` and its permutations), two give a `TriCross`
   (covered by `not_triCross_three_of_oddGirthThree`), three means `v ∈ D`.
3. `JSP90.closeToBipartite_one_of_locIndep_one_of_oddGirthThree` — `CloseToBipartite 1 G` through
   `JSP90.closeToBipartite_iff_hitsOddCycles` at `m = 1`, plus its `tauOdd` and `Erdős73On` forms and
   the sharpness witness `K₃` (`OddGirthThree`, `LocIndep 1`, not bipartite, so the constant cannot be
   lowered below `1`).

`jsp_000090_main` is still deliberately not declared; the unchanged primary blocker remains
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), of which
`JSP90.erdos73_of_erdosPosa` gives the whole theorem.

---

## Round 179 (`lean/JSPProblem/ConnLinear.lean`) — **THE NO-LOSS COMPONENT REDUCTION: THE
## DEFICIENCIES OF THE COMPONENTS ADD, SO ERDŐS #73 REDUCES TO CONNECTED GRAPHS WITH THE CONSTANT
## `C · k` AND NO FACTOR `k`**

Attack family 97 continued, now **closing the blocker that round 178 named**.  `lake build` **OK**
(1335 jobs); **0 `sorry`, 0 `admit`**; `harness/score.py --strict-prize`: `build_ok = true`,
`partial_ok = true`, `missing_theorems = ["jsp_000090_main"]`.  21 new declarations appended to
`lean/JSPProblem/ConnLinear.lean`; `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]`.

Round 43's reduction `JSP90.erdos73On_of_piece` concludes `CloseToBipartite (k * m) G`: a **factor
`k`**, because all pieces share one budget `m`.  At the sharp target of rounds 176–177
(`τ(G) ≤ C · MaxDef G`) that factor is fatal.  This round removes it.

* `JSP90.exists_eq_maxDefIn_sub`, `JSP90.maxDefInArg`, `JSP90.maxDefInArg_spec` — a maximiser of the
  deficiency inside a piece chosen **without ℕ truncation** (`2 α(Z) ≤ |Z|`); this is what makes the
  ℕ subtraction distribute.
* `JSP90.defOf_eq_sum_defOf_sub` — the truncated deficiency is an **equality** on a partial cover by
  subsets when no truncation occurs on any piece (`JSP90.sum_sub_eq_of_le`, `JSPProblem/Cut.lean`).
* **`JSP90.sum_maxDefIn_le_maxDef`** — `∑ Y ∈ 𝒬, maxDefIn G Y ≤ MaxDef G` for every anticomplete
  partition `𝒬`.  *This is exactly the lemma that round 178 declared as the round's blocker.*
* **`JSP90.maxDefIn_eq_maxDef_induce`** — `maxDefIn G Y = MaxDef (induceFinset G Y)`, via
  `JSP90.defOf_induceFinset_le_maxDefIn` (`defOf (induceFinset G Y) X ≤ maxDefIn G Y` for *every*
  `X`, since the vertices of `X` outside `Y` are isolated in `G[Y]` and can only lower the
  deficiency).
* **`JSP90.sum_maxDef_induce_le_maxDef`** (`_sub`, `_compPieces`) and
  `JSP90.sum_maxDef_induce_le_of_locIndep` — **`LocIndep k G` bounds the SUM of the
  `MaxDef`s of an anticomplete partition's pieces.**  This is what round 43 could not say.
* `JSP90.AnticoverPartition.toDecomposition`, `JSP90.sum_mul_nat`,
  **`JSP90.closeToBipartite_mul_maxDef_of_anticoverPartition`** — if every piece is `C · MaxDef`-close
  then `G` is `C · MaxDef G`-close (per-piece budgets summed by round 47's
  `JSP90.closeToBipartite_of_anticoverFamily_cost`, bounded by the two lemmas above).
* `JSP90.exists_compPiece_of_mem_compPieces`, **`JSP90.closeToBipartite_mul_of_piece_maxDef`**,
  `JSP90.PieceMaxDefErdős73On`, `JSP90.closeToBipartite_mul_of_pieceMaxDefErdős73On` — **the
  headline**: if every connected piece `s` of `G` with `MaxDef (induceFinset G s) ≤ r` is
  `C · r`-close to bipartite, then `LocIndep k G ⟹ CloseToBipartite (C · k) G`, i.e.
  `Erdős73On k (C · k)`.  **No factor `k`.**

### A CORRECTION OF ROUND 178's NEGATIVE RESULT (important for the next rounds)

Round 178 recorded as machine-checked that `MaxDef G = ∑ Y ∈ 𝒬, MaxDef (induceFinset G Y)` is
false, with the counterexample `G = K_3 ⊔ K_1`, `𝒬 = {{0,1,2},{3}}`, "reading `1 = 0 + 0`".  The
counterexample is **miscomputed**: `MaxDef (K_3) = 3 − 2 = 1`, so the sum is `1 + 0 = 1`.  The
statement *is* false, but for a different reason: `𝒬` may be finer than the components, and then the
pieces' `MaxDef`s do not see the deficiency of the whole.  The right counterexample is
`G = K_6`, `𝒬 = {{0,1,2},{3,4,5}}`: `MaxDef (K_6) = 4` against `MaxDef (K_3) + MaxDef (K_3) = 2`.
What is true, and is all the reduction needs, is the pair proved this round:
`maxDefIn G Y = MaxDef (induceFinset G Y)` and `∑ Y ∈ 𝒬, MaxDef (induceFinset G Y) ≤ MaxDef G`.
**Do not re-attempt the valuation identity `MaxDef G = ∑ Y ∈ 𝒬, MaxDef (induceFinset G Y)`; do use
the inequality, which is proved.**

### What remains

`jsp_000090_main` is still deliberately not declared.  The remaining direction is now precisely:
`JSP90.PieceMaxDefErdős73On C` for some `C` — a linear odd-cycle-transversal bound
`τ(G) ≤ C · MaxDef G` on connected graphs.  For `C = 2` this is the sharp form of Erdős #73
(`f(k) = 2 k`; the survey bound is `O(k log k)`).  The unchanged primary blocker is
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), of which
`JSP90.erdos73_of_erdosPosa` gives the whole theorem.

## Round 178 (`lean/JSPProblem/ConnLinear.lean`) — **THE HYPOTHESIS SPLITS OVER THE CONNECTED
## COMPONENTS: `α` AND `|X|` ARE EXACTLY ADDITIVE OVER AN ANTICOMPLETE COVER**

Attack family 97, the **connectivity axis, on the hypothesis side**.  `lake build` **OK** (1335
jobs); **0 `sorry`, 0 `admit`**; `harness/score.py --strict-prize`: `build_ok = true`,
`partial_ok = true`, `missing_theorems = ["jsp_000090_main"]`.  22 declarations in one new file,
imported from the root module `JSPProblem.lean`; `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` on every headline result.

Round 43 (`Connect.lean`) reduced Erdős #73 to connected graphs but only with the **loss of a
factor `k`**, because its hypothesis `PieceErdős73On k m` is stated at a single parameter.  Rounds
176–177 made the *sharp* target explicit (`τ(G) ≤ 2 · MaxDef G`, witnessed by the `k`-fold 3-sun),
and at a sharp target a linear factor is not acceptable: one needs the deficiencies of the
components to **add**.  This round supplies the additive object.

* `JSP90.AnticoverPartition G 𝒬` — a finite family of pairwise disjoint, pairwise anticomplete
  vertex sets covering `V` (the shape of the connected components), with
  `JSP90.anticoverPartition_compPieces : AnticoverPartition G (compPieces G)`: **the connected
  components of `G` are such a family** (this is what turns "a decomposition" into a *partition*).
* `JSP90.indepCard_le_inter_add`, `JSP90.inter_add_le_indepCard`, `JSP90.card_union_le_indepCard` —
  the two-piece splitting lemmas for `α`.
* **`JSP90.card_eq_sum_inter`** — `|X| = ∑ X' ∈ 𝒬, |X ∩ X'|` for every anticomplete cover `𝒬`.
* **`JSP90.indepCard_eq_sum_inter`** — **`α(X) = ∑ X' ∈ 𝒬, α(X ∩ X')`**: the independence number is
  exactly additive over an anticomplete cover (an independent set splits over the pieces and the
  pieces' independent sets reassemble), proved by induction on `𝒬`.
* `JSP90.maxDefIn_le_maxDef_induce` — the per-piece bound `maxDefIn G Y ≤ MaxDef (induceFinset G Y)`,
  i.e. a hypothesis on a piece bounds the deficiency measured *inside* that piece; and
  `JSP90.maxDefIn_univ_eq : maxDefIn G univ = MaxDef G`.
* **`JSP90.indepCard_univ_eq_sum_inter_compPieces`** — `α(G) = ∑ Y ∈ compPieces G, α(G[Y])`: the
  independence number of a graph is the sum of the independence numbers of its connected
  components — the hypothesis side of the reduction, matching round 177's
  `JSP90.tauOdd_sumGraph` on the conclusion side.
* `JSP90.indepCard_eq_sum_inter_compPieces`, `JSP90.card_univ_eq_sum_card_compPieces` (the sanity
  check: both sides are `|V|`).

### A NEGATIVE RESULT FOUND THIS ROUND (recorded, because it changes the plan)

`MaxDef` itself is **not** additive over an anticomplete cover, and the equality
`MaxDef G = ∑ Y ∈ 𝒬, MaxDef (induceFinset G Y)` is **FALSE**: for `G = K_3 ⊔ K_1` with
`𝒬 = {{0,1,2},{3}}` it reads `1 = 0 + 0`.  The reason is the ℕ truncation in `defOf = |X| - 2 α(X)`:
`MaxDef G` is a maximum over *all* vertex sets `X ⊆ V`, and the union of two pieces of deficiency
`0` can have positive deficiency while each piece has none.  Consequently
`Finset.sum_sub_distrib` is not available for `defOf` either (it is false for ℕ in general).
The additive object is `α` (`indepCard`), which this round proves to be exactly additive, and the
quantity to bound per piece is `maxDefIn G Y` (the deficiency measured *inside* the piece,
`JSPProblem/Cut.lean`), which `maxDefIn_le_maxDef_induce` shows is bounded by the piece's
hypothesis.


## Round 177 (`lean/JSPProblem/SunExact.lean`) — **`tauOdd` AND `MaxDef` ARE ADDITIVE OVER DISJOINT
## UNIONS, AND THE `k`-FOLD 3-SUN HAS TRANSVERSAL NUMBER EXACTLY `2 k`**

Attack family 96, the **exact-value axis**.  `lake build` **OK** (`Build completed successfully
(1334 jobs)`); **0 `sorry`, 0 `admit`**; `harness/score.py --strict-prize`: `build_ok = true`,
`partial_ok = true`, `missing_theorems = ["jsp_000090_main"]`.  27 declarations in one new file,
imported from the root module `JSPProblem.lean`; `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` on every headline result.

This round executes the **first concrete gap** that round 176's `policy.json` named: its two
dropped theorems `JSP90.closeToBipartite_two_mul_sun3U` and `JSP90.tauOdd_sun3U` — the missing
*upper* half of `τ ≥ 2 k`.  The repair was not the kernel check round 176 was reaching for (it is
avoided altogether) but **the transport lemma in the direction round 176 lacked**: a residue of a
disjoint union is bipartite when the residue of *every piece* is.

### The transport lemma, and what it buys

```lean
JSP90.sumZ (Z : Fin j → Finset W) : Finset (W × Fin j)          -- the deleted set of the union
JSP90.mem_sumZ : p ∈ sumZ Z ↔ p.1 ∈ Z p.2
JSP90.isBipartite_delete_sumGraph (Z) (h : ∀ i, (deleteFinset (H i) (Z i)).IsBipartite) :
    (deleteFinset (sumGraph j H) (sumZ Z)).IsBipartite         -- THE ASSEMBLING TRANSPORT
JSP90.closeToBipartite_sumGraph_of_forall : (∀ i, CloseToBipartite (m i) (H i)) →
    CloseToBipartite (∑ i, m i) (sumGraph j H)
JSP90.closeToBipartite_sumGraph_of_forall_of_mul : (∀ i, CloseToBipartite m (H i)) →
    CloseToBipartite (j * m) (sumGraph j H)
JSP90.closeToBipartite_sumGraph_of_piece : CloseToBipartite m (sumGraph j H) → CloseToBipartite m (H i)
```

The colouring in `JSP90.isBipartite_delete_sumGraph` is **explicit**: at a point of the `i`-th
fibre it is the `i`-th piece's own colouring of its own residue.  Round 176's
`JSP90.deleteFinset_sumGraph_fib` is the other transport (the residue *inside* one fibre is the
residue of that piece), so between them the two directions are both available.

### Three additivity results, all order-free

* **`JSP90.maxDef_sumGraph : MaxDef (⊔ H i) = ∑ i, MaxDef (H i)` — THE DEFECT IS ADDITIVE, EXACTLY**
  (round 176 had only `≤ j * k`).  The proof needs one new arithmetic observation
  (`JSP90.exists_eq_add_of_defOf`): a piece of defect `0` is witnessed by `∅` and a piece of
  *positive* defect by a maximiser `Y` of the deficiency, for which the truncated subtraction
  `|Y| − 2 α(Y)` is honest, so `|Y| = 2 α(Y) + MaxDef`.
* **`JSP90.tauOdd_sumGraph : tauOdd (⊔ H i) = ∑ i, tauOdd (H i)` — THE LEAST ODD CYCLE TRANSVERSAL
  IS ADDITIVE.**
* **the hypothesis**: round 176's `JSP90.locIndep_sumGraph` (`LocIndep (j * k)`), plus
  **`JSP90.locIndep_of_locIndep_sumGraph_piece`** (the hypothesis descends to each component at the
  *same* parameter) and **`JSP90.locIndep_of_maxDef_sumGraph`** (the union is `LocIndep` at the
  *sum* of the defects).

**A claim this round tried and the kernel refuted:** `LocIndep k (⊔ H i) ↔ ∀ i, LocIndep k (H i)`
is **false** at the same parameter (`kTriangles 2` has defect `2` although both components have
defect `1`), which is why round 176's form multiplies by `j`.  The correct statement is the *sum*,
and it is what `JSP90.maxDef_sumGraph` proves.  `JSP90.maxDef_piece_le` records the surviving
inequality.

### The sharpness table is now exact

```lean
JSP90.closeToBipartite_two_mul_sun3U (k) : CloseToBipartite (2 * k) (sun3U k)
JSP90.tauOdd_sun3U (k) : tauOdd (sun3U k) = 2 * k
JSP90.exists_sharp_witness (k) : ∃ (G : SimpleGraph (Fin 6 × Fin k)),
    LocIndep k G ∧ MaxDef G = k ∧ tauOdd G = 2 * k
```

So `2 k` is a *valid* constant of Erdős #73 at the parameter `k` **and** no smaller one is
(`JSP90.erdos73On_two_mul_le`, round 176): the lower bound `2 k` of the constant is attained by the
canonical witness.  The whole of the `k`-fold sun is produced by the transport lemma of Part 1 out
of the six-vertex statement `JSP90.closeToBipartite_two_sun3` of `JSPProblem/Six.lean`.

### A new order-free instance of the headline theorem

```lean
JSP90.closeToBipartite_of_sumGraph_of_oddCactus_of_locIndep_one :
    (∀ i, LocIndep 1 (H i)) → (∀ i, OddCactus (H i)) → CloseToBipartite j (sumGraph j H)
JSP90.optimal_sumGraph_of_oddCactus_of_locIndep_one (k) (hk : 1 ≤ k) :
    LocIndep k (kTriangles k) ∧ ¬ CloseToBipartite (k - 1) (kTriangles k)
```

with the optimal constant `j` (`JSP90.tauOdd_le_of_sumGraph_of_oddCactus_of_locIndep_one`).  No
order bound, no odd-girth bound, no degree bound.

### The measurement of round 177 (`discovery/JSP-000090/r177/r.c`, log `r.log`)

For **every** graph on `n ≤ 7` vertices (2 097 152 graphs at `n = 7`) and 3 000 000 random graphs
on 8 vertices, the program computes `MaxDef = max_X |X| − 2 α(X)` and `τ_odd` exactly:

| `n` | graphs | `max (τ_odd − 2 · MaxDef)` | `max τ_odd` at `MaxDef = 1` | at `d = 2` | at `d = 3` |
| --- | --- | --- | --- | --- | --- |
| 3 | 8 | 0 | 1 | – | – |
| 4 | 64 | 0 | 1 | 2 | – |
| 5 | 1 024 | 0 | 1 | 2 | 3 |
| 6 | 32 768 | 0 | 2 | 2 | 3 |
| 7 | 2 097 152 | 0 | **2** | 3 | 3 |
| 8 | 3 000 000 random | 0 | **2** | 3 | 4 |

Two readings.  (i) **No counterexample to `τ_odd ≤ 2 · MaxDef`** at these orders, so the candidate
`f(k) = 2 k` survives the measurement and the bet of round 176 stands.  (ii) The value `f(1) = 2` is
attained at *every* order from 6 to 8 (the 3-sun and other witnesses), which extends the
machine-checked `JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight` from `|V| ≤ 8` — it agrees
with it — to an *exhaustive* statement at `|V| ≤ 7`.  A defect-2 graph with `τ_odd = 3` already
exists on 7 vertices, so `f(2) ≥ 3` (consistent with `2 k = 4`).  Sanity checks of the program on
`sun3` (`MaxDef 1`, `τ 2`), `K_7` (`5`, `5`), `K_8` (`6`, `6`), `C_7` (`1`, `1`) are in the log.

### What is left

`jsp_000090_main` is deliberately **not** declared.  The missing direction is still
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) through `JSP90.erdos73_of_erdosPosa`.
But this round changes what is left in a sharper way: **because `MaxDef` and `τ_odd` are both
additive over the components of a disjoint union, `Erdős73On k (2 k)` reduces to a statement about
a single component** — every graph is a disjoint union of its connected components — so the
remaining gap is now a *one-component* gap (`MaxDef ≤ k → τ_odd ≤ 2 k` for a connected graph), and
`policy.json` records the component decomposition as the infrastructure step that exposes it.

---

## Round 176 (`lean/JSPProblem/SunSum.lean`) — **THE CONSTANT IN ERDŐS #73 IS AT LEAST `2 k`**

Attack family 95, the **lower-bound / sharpness axis**.  Rounds 171–175 computed *upper* bounds on the
odd cycle transversal of a graph of defect at most `k` (all of them order-dependent, e.g.
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight`); this round changes the object once more
and constrains **the constant of the headline theorem itself**, with **no order anywhere in the
statements**.  `lake build` **OK** (`Build completed successfully (1333 jobs)`); **0 `sorry`,
0 `admit`**; `harness/score.py --strict-prize`: `build_ok = true`, `partial_ok = true`,
`missing_theorems = ["jsp_000090_main"]`.  46 declarations in one new file, imported from the root
module `JSPProblem.lean`.

### The headline statements

```lean
JSP90.erdos73On_two_mul_le {k m : ℕ} (hk : 1 ≤ k) (h : Erdős73On.{0} k m) : 2 * k ≤ m
JSP90.not_erdos73On_lt_two_mul {k m : ℕ} (hk : 1 ≤ k) (hm : m < 2 * k) : ¬ Erdős73On.{0} k m
JSP90.two_mul_le_of_erdos73 {k : ℕ} (hk : 1 ≤ k) (h : Erdős73.{0} k) : 2 * k ≤ h.choose
```

**Any constant `m` that makes Erdős #73 true at the parameter `k` must satisfy `2 * k ≤ m`.**  This
is the first *order-free* lower bound on the constant in this development and it **doubles** the
machine-checked bound `JSP90.no_constant_below_k` of `lean/JSPProblem/Sharp.lean` (whose witness
`kTriangles k` spends one unit of Erdős's parameter on one vertex of transversal).  The witness is
the `k`-fold **3-sun** (`sun3U k`): each 3-sun is `LocIndep 1` and needs **two** deleted vertices,
so `k` disjoint copies are `LocIndep k` and need `2 k`.

It also explains, at the level of the constant rather than of an order bound, why
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight` cannot be lowered to `1`: the `k = 1` case
of this round's statement is `JSP90.not_erdos73On_one_one` of `lean/JSPProblem/OneK.lean`, which is
**not** restated here (nor is its positive counterpart
`JSP90.closeToBipartite_one_of_locIndep_one_card_le_five`).

### The structural content — Erdős's hypothesis is *summed over components*

* **`JSP90.sumGraph j H`**, the disjoint union of a finite family of graphs on `W × Fin j`, with its
  fibres (`JSP90.fib`, `JSP90.mem_fib`) and the counting lemmas
  `JSP90.card_eq_sum_card_inter_fib`, `JSP90.biUnion_inter_fib`, `JSP90.card_image_fib`,
  `JSP90.card_image_pair`, `JSP90.disjoint_image_fib`, `JSP90.pairwiseDisjoint_image`.
* **`JSP90.indepCard_sumGraph`: the independence number is additive over a disjoint union**,
  `α(⊔ H i) (X) = ∑ α(H i) (X ∩ fib i)`, proved in both directions (`JSP90.isIndepSet_sumGraph`
  splits an independent set, `JSP90.exists_indepCard_sumGraph` glues the pieces).
* **`JSP90.locIndep_sumGraph`: `LocIndep (j * k) (⊔ H i)` if every `H i` is `LocIndep k`**, with
  `JSP90.defOf_sumGraph_le` and `JSP90.maxDef_sumGraph_le` as the deficiency forms.  So the local
  hypothesis of Erdős #73 is *additive over components*, with **no other hypothesis**.
* **`JSP90.sun3U k`**, the disjoint union of `k` 3-suns: `JSP90.locIndep_sun3U k : LocIndep k`
  by Part 2, `JSP90.maxDef_sun3U : MaxDef (sun3U k) = k` (the witness is *exact*, as
  `kTriangles` is) and `JSP90.not_locIndep_sun3U : ¬ LocIndep (k - 1)`.
* **`JSP90.deleteFinset_sumGraph_fib`: the residue of the union inside one fibre is the residue of
  that piece** — the transport lemma, via the new `JSP90.isBipartite_induce_of_graphMap`
  (bipartiteness passes down a graph homomorphism) and the membership bookkeeping that says a
  point outside the deleted part of a fibre projects outside the deleted part of the piece.
  `JSP90.card_ge_two_of_not_bipartite` and **`JSP90.not_closeToBipartite_lt_two_mul_sumGraph`** are
  the lower bound in the language of the disjoint union: if every single vertex of every piece is
  needed to make that piece bipartite, then no set of fewer than `2 j` vertices makes the whole
  union bipartite.
* `JSP90.not_closeToBipartite_lt_two_mul_sun3U` is the `sun3U` instance, and
  `JSP90.card_le_one_of_sub_tri` / `JSP90.indepCard_tri_le` / `JSP90.card_tri_sun` /
  `JSP90.adj_of_mem_T0` / `JSP90.isIndepSet_subset` are the tools for the exactness of the witness.

`#print axioms` on all of the above reports only `[propext, Classical.choice, Quot.sound]`.

### What is left

Nothing of the *direction* proved here: the lower bound on `f(k)` is sharp as far as this
development can tell.  `jsp_000090_main` is deliberately **not** declared; the missing direction is
still `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) through
`JSP90.erdos73_of_erdosPosa`.  The concrete next question, now that the *lower* bound is settled,
is the matching **order-free upper** bound: is `f(k) = 2 k` (it is at `k = 1`, where the eight-vertex
instance and `sun3` give `f(1) = 2` exactly)?  That is the first candidate for
`jsp_000090_main` in a form that never mentions `|V|`, and it is recorded as the next bet of
`policy.json`.

---

## Round 171 (`lean/JSPProblem/TriEight.lean`) — **THE EIGHT-VERTEX TRANSFER IS PROVED**

Attack family 92.  `lake build` **OK** (`Build completed successfully (1330 jobs)`); **0 `sorry`,
0 `admit`**; `harness/score.py --strict-prize`: `build_ok = true`, `partial_ok = true`,
`missing_theorems = ["jsp_000090_main"]`.  This round executes round 170's single named gap — the
four tactic steps — and with them the whole transfer, `JSP90.triCaseEight`.

### The theorem that is now proved

```lean
JSP90.triCaseEight (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 8) {T : Finset V}
    (hT : G.IsNClique 3 T) : ∃ t ∈ T, (deleteFinset G (T \ {t})).IsBipartite
```

i.e. **at `LocIndep 1` and eight vertices, a triangle has a vertex whose deletion together with the
other two leaves a bipartite graph**.  A graph is carried into the `Fin 8` language of
`lean/JSPProblem/TriFiveLang.lean` through `xpt : Fin 5 → V` (the residue `X = V \ T`: two points
in the colour class of size **two** and three in the other, `JSP90.card_cls_ge_two` at `|V| = 8`, the
classes swapped by `opp2 ∘ d` when the order requires it), `tpt : Fin 3 → V` (the triangle,
carried by `5, 6, 7`), the bijection `inv : Fin 8 → V`, the six cells `A : Fin 64` and the three masks
`s0 s1 s2 : Fin 32`, with

```lean
adj8n A s0.val s1.val s2.val i.val j.val = decide (G.Adj (inv i) (inv j))   — all i, j : Fin 8
```

(the sixty-four-case analysis), the three hypotheses transferred (`meetBoth` from
`JSP90.exists_adjIn_color`, `tripleEmpty` from `JSP90.card_adjIn_le_two_of_isNClique_three`, and the
delicate **badness** from `JSP90.properM_get` + `JSP90.okMono_read` +
`JSP90.isBipartite_of_adjIn_mono`, a genuine two-colouring of `deleteFinset G (T \ {t})` read off the
colouring index `i < 16` of the language), and finally Erdŝs's hypothesis on the three six-element
subsets `T + {0,1,2}`, `T + {0,1,3}`, `T + {0,1,4}` against the counting step `JSP90.loc8_lemma`.

### A first instance of the headline theorem at order eight

```lean
JSP90.closeToBipartite_two_of_shortest_three_of_locIndep_one_card_le_eight
    (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 8) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D, IsOddCycle G D → C.card ≤ D.card) (hC3 : C.card = 3) : CloseToBipartite 2 G
```

with `JSP90.exists_hitsOddCycles_two_of_shortest_three_of_locIndep_one_card_le_eight` (a two-element odd
cycle transversal) and `JSP90.tauOdd_le_two_of_shortest_three_of_locIndep_one_card_le_eight`
(`tauOdd G ≤ 2`).

### The four repairs, and one further obstruction that was not on the list

* **`JSP90.card_six_inv` / `JSP90.mem_six_inv`** — the finset equalities are closed by `simp`
  (`Finset.mem_image` distributes over `Finset.mem_insert`), and the six branches of the membership
  reading are built by hand.
* **`JSP90.hxpt_inj`** — the case split on `i.val < 2` must come **before** any `obtain ⟨iv, _⟩ :=
  i`, which deletes the name `i`; and in the last branch the values of the indices are needed, not
  `omega` applied to the injectivity one is trying to prove.  The repair is the new
  **`JSP90.hxpt_val`** (the if-chain of `xpt` read off at an index), after which `rw [hi, hj] at hij'`
  matches the literals.
* **`JSP90.hsT`** — `JSP90.sBit_maskOf` is stated with `sBit = decide (s.testBit _ = true)`, so it
  must be lifted back to `Nat.testBit`; the new **`JSP90.decide_eq_true_of_bool`** (the three-step form)
  does it.
* **The badness transfer** — `crossM` is not `adj8n` syntactically, so the new
  **`JSP90.crossM_of_adj8n`** is the bridge, and the two `hAdj` steps use `rw [hk]`.

And one obstruction round 170 did **not** record, found by the sixty-four-case correspondence itself:
`Nat.testBit_zero` is `@[simp]` and its pattern `testBit ?m 0` is *more specific* than that of
`JSP90.cellsOf_bit_nat`, so `simp` reduces bit `0` of the cells to `(cellsOf w).val % 2 = 1` before the
reading can fire — thirty-two of the sixty-four cases closed, and the two cases that use cell `0`
(`(p, q) = (0, 2)` and `(2, 0)`) could not.  The fix is **`JSP90.hmod0`**, the same statement in the
modulus form (via `Nat.mod_two_eq_one_iff_testBit_zero`), together with **`JSP90.hwAll`**, the six cell
values in one hypothesis, whose pattern `w ?k` matches the `Fin`-literal arguments `simp` leaves
behind.

`#print axioms` on `JSP90.triCaseEight`, `JSP90.card_six_inv`, `JSP90.mem_six_inv` and on the three
theorems of Part 2 reports only `[propext, Classical.choice, Quot.sound]`.

### What is left

The eight-vertex **instance** `LocIndep 1 → CloseToBipartite 2` at `|V| ≤ 8` still needs the
five- and seven-cycle cases **at order eight**: `JSP90.closeToBipartite_one_of_shortest_five` carries
`|V| ≤ 7`, and at eight vertices a seven-cycle does not span `V` (so
`JSP90.closeToBipartite_one_of_shortest_oddCycle_of_card_eq` does not apply).  With those two,
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight` follows from `triCaseEight` plus round 162's
two shorter-cycle lemmas.  Behind all of it: `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas),
so `jsp_000090_main` is deliberately **not** declared.

---

## Round 170 (`lean/JSPProblem/TriEight.lean`) — **THE EIGHT-VERTEX TRANSFER**

Attack family 91.  Round 169 was idle (`lean_changed = false`), so this round executes the single
named gap of rounds 166–168: the transfer that lets the counting step `JSP90.loc8_lemma` (round 167,
over the five-point residue `K_{2,3}`) be applied to a graph.

### Part 0 — the readings of the `Fin 8` language, all machine-checked

`lean/JSPProblem/TriFiveLang.lean` packs the local structure into numbers (the six cells of `G[X]`
as the bits of `A : Fin 64`, each neighbour set as a mask `Fin 32`), so the transfer has to move data
*through* the bits.  Both directions are provided, and every reading quantifies only over `Fin`
types, so `decide` closes it — which is what keeps the bit arithmetic out of the proof:

* **`JSP90.properM_get`** (`decide`): a colouring index `i < 16` with `properM A i = true`
  separates the two ends of every cell of `A`, i.e. it *is* a proper two-colouring of `G[X]`.
* **`JSP90.okMono_read`** (`decide`), **`JSP90.meetBoth_read`**, **`JSP90.tripleEmpty_read`**,
  and the forward readings **`JSP90.meetBoth_of`**, **`JSP90.tripleEmpty_of`**;
  **`JSP90.crossM_split`** (the cells are the cross pairs).
* **`JSP90.maskOf` / `JSP90.sBit_maskOf`** and **`JSP90.cellsOf` / `JSP90.cellsOf_bit`**: the
  packing of a neighbour set and of the six cells, with both readings.
* **`JSP90.exists_ind3n_of_hasInd3m`**, **`JSP90.ind3n_get`**, **`JSP90.ind3n_of_nadj`**,
  **`JSP90.noInd36_false_of_ind3n`**: the bridge from the `512`-iteration search of
  `JSP90.hasInd3m` to the cheap form `JSP90.noInd36` the counting step evaluates.
* **`JSP90.sort3`**, **`JSP90.card_six_inv`**, **`JSP90.mem_six_inv`**,
  **`JSP90.sixMaskOf`** / **`JSP90.sixMask_bit_true`**: the vertex-set bookkeeping of the three
  six-element subsets.

### Two readings of the language are new, and one of them **corrects** the obvious reading

* `JSP90.okMono_read` was first stated as "`s = 0` or every bit of `s` is set in `i`"; **`decide`
  refuted it**.  The true statement is that the neighbour set is **monochromatic**, and the
  statement records *which colour*: `i &&& s = 0` says that no point of the set carries the colour
  `true`, not that the set is empty.  This is exactly what the badness transfer needs.
* The masks `231, 235, 243` of `JSP90.sixMasks` are **not** `231 + 4 * (r - 2)` — `231 + 8 = 239`
  keeps the bit of `2`, and `decide` refuted the arithmetic form (`JSP90.sixMask_bit_true` with
  `JSP90.sixMaskOf` is the version that holds).

### Part 1 — `JSP90.triCaseEight`, the transfer: **WRITTEN, NOT YET COMPILING**

```lean
LocIndep 1 G → Fintype.card V ≤ 8 → G.IsNClique 3 T → ∃ t ∈ T, (deleteFinset G (T \ {t})).IsBipartite
```

`xpt : Fin 5 → V` (the residue, `0, 1` in the colour class of two points and `2, 3, 4` in the
other, the two classes swapped by `opp2 ∘ d` when the order requires it), `tpt : Fin 3 → V` (the
triangle, carried by `5, 6, 7`), the bijection `inv : Fin 8 → V`, the six cells `A : Fin 64` and
the three masks `s0 s1 s2 : Fin 32`, with
`adj8n A s0.val s1.val s2.val i.val j.val = decide (G.Adj (inv i) (inv j))` for all `i, j < 8`; then
the three hypotheses (`meetBoth` from `JSP90.exists_adjIn_color`, `tripleEmpty` from
`JSP90.card_adjIn_le_two_of_isNClique_three`, badness from `JSP90.properM_get` +
`JSP90.okMono_read` + `JSP90.isBipartite_of_adjIn_mono`), and finally Erdős's hypothesis on the
three six-element subsets `T + {0,1,2}`, `T + {0,1,3}`, `T + {0,1,4}` against `JSP90.loc8_lemma`.
The case `|V| ≤ 7` is `JSP90.triCase` of round 166.  **Status:** the kernel *accepts* the eight-point
correspondence, the injectivity of `xpt`, `inv_inj`, `inv_surj`, `meetBoth` and `tripleEmpty`; four local
tactic steps did not close within the round budget (`JSP90.card_six_inv`/`JSP90.mem_six_inv`'s
disjunctive goals, the order of the case split in `hxpt_inj`, the three-step form of the mask reading,
and one `rw` direction in the badness transfer).  The file is therefore installed **without** the
transfer, so that the build stays green, and the complete draft — Part 0 and Part 1 together — is
preserved verbatim at `discovery/JSP-000090/TriEightFull_draft.lean`; `policy.json` names the four
repairs exactly.

### What is left

The eight-vertex *instance* `LocIndep 1 → CloseToBipartite 2` at `|V| ≤ 8` still needs the five- and
seven-cycle cases **at order eight**: `JSP90.closeToBipartite_one_of_shortest_five` carries
`|V| ≤ 7`, and at eight vertices a seven-cycle does not span `V` (so
`JSP90.closeToBipartite_one_of_shortest_oddCycle_of_card_eq` does not apply).  Behind all of it:
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), so `jsp_000090_main` is deliberately
**not** declared.

---

## Round 168 (`lean/JSPProblem/TriResidue.lean`) — **THE BUILD IS GREEN AGAIN, THE SECOND GAP IS
## CLOSED, AND THE RESIDUE LEMMA IS TRUE AT EVERY ORDER**

Attack family 90.  `lake build` **OK** (`Build completed successfully (1329 jobs)`, 3 s as an
up-to-date no-op); **0 `sorry`, 0 `admit`**; `harness/score.py`: `build_ok = true`,
`partial_ok = true`, `missing_theorems = ["jsp_000090_main"]`.  Two independent deliverables.

### 1. The build is green (round 167 left it impossible)

Round 167 filled the filesystem and left **sixteen modules without an `.olean`**
(`Definitions`, `Probe`, `TriFive`, `TriFiveD … TriFiveP`) plus a deleted
`lean/.lake/packages/mathlib/.lake/build/ir`.  Round 168 restored the build with the two moves
recorded in `discovery/JSP-000090/DISK_FULL_REPAIR.md` and verified them:

* the `ir` directory of `mathlib` and of the seven small dependencies was restored by **hard link**
  from `JSP-000018` (`cp -al`, identical Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
  identical `lake-manifest.json`), which costs **no data blocks** — 18 032 generated-C files, 2.8 s;
* the remaining `mkdir` failures (`…/build/ir/JSPProblem`, and every later block allocation) are an
  **ext4 reserved-block** problem, not a real 100 %: `df` reports `Avail 0` for user `box` while
  ≈ 6.4 GB are held in the root reserve, so `lake build` was run under
  `sudo -E env PATH=… HOME=/home/box lake build` and the outputs chowned back with
  `sudo chown -R box:box .lake/build`.  After that `lake build` **as `box` succeeds in 3 s**, which
  is what the gate (`harness/score.py` runs bare `lake build` with a 600 s timeout) needs.

### 2. The second gap of round 167, closed — in a stronger form than requested

Round 167's "SECOND GAP" was the eight-vertex bridge: *the residue of a triangle is bipartite at
`LocIndep 1` and `|V| ≤ 8`* (its suggested route, a `decide` over the `2 ^ 10` graphs on `Fin 5`).
The bridge is true, and the count that proves it mentions no order at all:

* **`JSP90.not_isOddCycle_of_disjoint_of_isNClique_three_of_locIndep_one`** — at `LocIndep 1` a
  triangle and an odd cycle of `G` are **never** vertex-disjoint.  With `|D| = m` odd, Erdős's
  hypothesis on the `m + 3` points of `T ∪ D` gives an independent set `S` with
  `2 * |S| + 1 ≥ m + 3`, while `|S ∩ T| ≤ 1` (`α(C_3) ≤ 1`) and `2 * |S ∩ D| + 1 ≤ m`
  (`α(C_m) ≤ ⌊m / 2⌋`, `JSP90.two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle`) give
  `2 * |S| + 1 ≤ m + 2`.  At `m = 3` this is round 150's
  `JSP90.not_isNClique_three_of_disjoint_of_locIndep_one`, which is *not* redeclared.
* **`JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one`** —

  ```lean
  LocIndep 1 G → G.IsNClique 3 T → (deleteFinset G T).IsBipartite
  ```

  **no bound on `|V|`.**  This is round 150's
  `JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_seven` with `|V| ≤ 7`
  *removed*: that bound was there only because the five-vertex odd cycle of an eight-vertex residue
  was out of reach.  So the eight-vertex transfer of `JSP90.loc8_lemma` — which needs a proper
  two-colouring of the five-point `K_{2,3}` residue before anything else — is unblocked, and the
  triangle case of Erdős #73 at `k = 1` is no longer confined to small graphs.
* **`JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_eight`** (the shape the
  `Fin 8` transfer consumes) and
  **`JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one_piece`** (the peeling form).

A real defect was fixed on the way: `lean/JSPProblem/TriFive.lean` had **never been compiled** (it
was among the sixteen modules of the broken build), and all 64 cases of `JSP90.loc8_lemma` called
`loc8_read` with one argument too few (`loc8_read _ _ _ hA …` where `loc8_read` takes `n s0 s1 s2`
before `hA`); the build now compiles `JSP90.loc8_lemma` for the first time.

### What is left

The transfer `JSP90.triCaseEight`: carry a graph into the `Fin 8` language of
`lean/JSPProblem/TriFiveLang.lean` (`xpt : Fin 5 → V`, `tpt : Fin 3 → V`, `inv : Fin 8 → V`, the six
cells `A : Fin 64`, the three masks `s t : Fin 32`, `adj8n A s0 s1 s2 i j = decide (G.Adj (inv i)
(inv j))` by a 64-case analysis), then the three hypotheses (`meetBoth`, `tripleEmpty`, and the
badness `JSP90.badM A s = true` read off the masks through a genuine two-colouring of the residue),
then Erdős's hypothesis on the three six-element subsets against `JSP90.loc8_lemma`, and finally
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight`.  Behind all of it:
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), so `jsp_000090_main` is deliberately
**not** declared.

## Round 167 (`lean/JSPProblem/TriFiveLang.lean`, `lean/JSPProblem/TriFive{,A..P}.lean`) — **THE
## EIGHT-VERTEX COUNTING STEP, IN THE FORM THAT IS ACTUALLY TRUE**

Attack family 88.  Round 166's prediction was **refuted by measurement** (23 976 counterexamples to
the seven-vertex counting step read at eight vertices), and the correct step was proved instead:
`JSP90.loc8_lemma`, by `decide` sixty-four times, over the five-point `K_{2,3}` residue.  The build
could not be finished in that round (the filesystem reached 100 %); the sixteen modules involved are
listed above and were rebuilt in round 168, where the first compile of `JSP90.loc8_lemma` exposed
the arity defect recorded there.

## Round 166 (`lean/JSPProblem/TriFix.lean`) — **MISSING LEMMA 1 IS PROVED AND THE SEVEN-VERTEX AXIS IS
## CLOSED WITH THE OPTIMAL CONSTANT `2`**

Attack family 87.  `lake build` OK with **1310 jobs**; **0 `sorry`, 0 `admit`**; `partial_ok = true`,
`missing_theorems = ["jsp_000090_main"]`.  This round executes the single remaining gap recorded by
round 165 (`policy.json`, "THE TRANSFER") and, in doing so, closes the seven-vertex instance of
Erdős #73 at `k = 1` with the constant `2` that the measurements have been asking for since round 144.

### The transfer (MISSING LEMMA 1)

```lean
JSP90.triCase (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 7) {T : Finset V} (hT : G.IsNClique 3 T)
    (hXbip : (deleteFinset G T).IsBipartite) : ∃ t ∈ T, (deleteFinset G (T \ {t})).IsBipartite
```

`JSP90.card_cls_ge_two` forces the residue `X = V \ T` to have four points with two in each colour
class; the file builds `xpt : Fin 4 → V`, `tpt : Fin 3 → V`, the bijection `inv : Fin 7 → V` (with
`finv : V → Fin 7` as its inverse), the four cells `A` and the three neighbour sets `S`, so that
`adj7 A S i j = decide (G.Adj (inv i) (inv j))`, and transfers the three hypotheses of `JSP90.hyps`:
empty triple intersection, each `S_t` meeting both colour classes, and — the delicate half — **each
`t` bad in the `Fin 7` language**, `monoS S t m = true ∧ proper8 A m = true` yielding a genuine
two-colouring of `deleteFinset G (T \ {t})` through `JSP90.isBipartite_of_adjIn_mono`, with the
residual colours read off `col4 m` and properness read off by `JSP90.proper8_adj`.  Erdős's hypothesis
read on the six-element set `univ \ {inv z}` then gives an independent triple avoiding each vertex
`z`, contradicting round 165's `decide`-proved counting step `JSP90.loc7_lemma`.

### The axis

`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven : LocIndep 1 G → |V| ≤ 7 →
CloseToBipartite 2 G` — **Erdős #73 at `k = 1` on seven vertices, with the optimal constant `2`**
(a shortest odd cycle has three, five or seven vertices; the two long cases were closed in round 162
and the triangle case is `JSP90.triCase`; the bridge "the residue of every triangle is bipartite" is
round 150's `JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_seven`).  Downstream:
`JSP90.erdos73On_one_two_of_card_le_seven`, `JSP90.tauOdd_le_two_of_locIndep_one_card_le_seven`,
`JSP90.exists_hitsOddCycles_two_of_locIndep_one_card_le_seven`,
`JSP90.closeToBipartite_two_of_locIndep_one_of_card_le_seven` (piece form),
`JSP90.exists_hitsOddCycles_two_of_card_le_seven`, `JSP90.tauOdd_le_two_of_card_le_seven`.

### Optimality

`JSP90.tauOdd_sun3 : tauOdd sun3 = 2` and
`JSP90.not_locIndepOneAllSmallOrder_one_of_card_le_seven` — the class is two vertices away from
bipartite and **not** one, so the constant cannot be lowered.

## Round 165 (`lean/JSPProblem/TriCount.lean`) — **THE CORRECTION OF ROUND 164's READING OF
"BAD", AND THE COUNTING STEP OF THE TRIANGLE CASE IN THE CORRECTED READING**

Attack family 87.  `lake build` OK with **1309 jobs**; **0 `sorry`, 0 `admit`**; `partial_ok = true`,
`missing_theorems = ["jsp_000090_main"]`.  This round executes the concrete next bet of round 164
(`policy.json`) — *finish the graph-to-`Fin 7` transfer* — and, in doing so, finds that **the finite
core round 164 shipped was proved for the wrong reason**: the `Bool` it used for "properness" of a
two-colouring of the residue was **weaker** than properness, so its `bad8` was not "the vertex is
bad", and the counting step it proved was not the counting step of the problem.

### The correction (the round's main finding)

Round 164 defined badness through

```lean
JSP90.properX A c = !((c 0 && (cross A 0 2 || cross A 0 3)) || (c 1 && (cross A 1 2 || cross A 1 3)))
```

which only checks that the **class-`{0,1}` endpoint** of a cross edge is not coloured `true`.  The
colouring `c ≡ false` satisfies it and is not proper at all.  `JSP90.properX` is **deleted** and
replaced by

* **`JSP90.proper8`** — checks **all four** cross pairs, so `proper8 A m = true` **is** "`m` is a
  proper two-colouring of `G[X]`"; **`JSP90.proper8_adj`** (by `decide`) is the reading lemma, and it
  is exactly the tool the transfer of "the vertex `t` is bad" needs in both directions;
* **`JSP90.bad8`** — now genuinely "`G[X + {t}]` is not bipartite";
* **`JSP90.monoS_of_all`** — the other direction of the transfer (any two points of `S t` carrying the
  same colour make `S t` monochromatic).

The colourings are now packed (`JSP90.col4 : Fin 16 → Fin 4 → Bool`, `JSP90.col7 : Fin 128 → Fin 7 →
Bool`), and the local structure is written in **pure `Bool` arithmetic** (`S t i || …`, `! cross A p q
|| …`), which is what makes `decide` affordable.

### `JSP90.loc7_lemma` — THE COUNTING STEP, PROVED IN THE CORRECTED READING

```lean
JSP90.loc7_lemma : ∀ (A : Fin 4 → Bool) (S : Fin 3 → Fin 4 → Bool),
    hyps A S = true → ¬ ((∀ z : Fin 7, hasTripleAvoiding A S z = true))
```

i.e. **three bad vertices of a triangle over a bipartite four-element residue, the three neighbour
sets meeting both colour classes, and the three sets with empty triple intersection ⟹ some vertex of
the seven is avoided by no independent triple** — which contradicts Erdős's hypothesis read on the
six-element subset `V \ {z}`.  This is the statement rounds 163–164 were aiming at; it is now proved
**in the reading that matters**, and both transfer directions (`JSP90.hasTripleAvoiding_of_indep3`
forward, `JSP90.exists_triple_of_hasTripleAvoiding` backward) are available.

Proved **by `decide`**, sixteen times, once for each of the `2 ^ 4` configurations of the four cells of
`G[X]` (`JSP90.loc7_lemma_0 … JSP90.loc7_lemma_15`, assembled by `JSP90.loc7_lemma` through
`JSP90.exists_aBits`).  The split is forced: a **single** `decide` over all `2 ^ 16` configurations is
killed by the kernel (`Lean exited with code 137` after `370–400 s`); the sixteen pieces build in
`333 s` altogether.  `decide` and not `native_decide`, so `#print axioms JSP90.loc7_lemma` reports
only `[propext, Classical.choice, Quot.sound]`.

Also proved in this round:

* **`JSP90.triple3`, `JSP90.hasTripleAvoiding`, `JSP90.erdos6`, `JSP90.erdos6_of_forall`** — the
  Erdős side of the counting step, packed;
* **`JSP90.ofDecideTrue`** (`p → decide p = true`, the direction this Lean version's core does *not*
  provide) and **`JSP90.bool_four_or`** — the `decide`-valued glue every transfer lemma needs;
* **`JSP90.exists_aBits`** — every configuration of the four cells is `aBits n` for some `n : Fin 16`.

### The measurement, and a refuted variant

`discovery/JSP-000090/r165c.c` (log `r165c.log`) re-measures the step over all `2^4 · 2^12 = 65 536`
configurations `A × S` of the `Fin 7` language, with the **corrected** badness:

| quantity | value |
| --- | --- |
| configurations with each `S t` meeting both classes, empty triple intersection, **all three vertices bad** | **816** |
| of those, configurations with `¬ (∀ z, z is avoided by an independent triple)` | **816** (`0` violations) |
| of those, configurations with the six-element condition `∀ z, ∃ independent triple avoiding z` | **0** |
| of those, configurations with "two deletions leave the graph bipartite" | **288** (`528` violations) |

So the transversal conclusion is **exactly right** (it contradicts Erdős in every one of the `816`
configurations), and the *alternative* conclusion one might try to read off the same table — that two
deletions always suffice — is **false**.  (Two earlier programs written in this round,
`discovery/JSP-000090/r165.c` and `…/r165b.c`, are **void**: the first printed the complement of what
its flag said, the second copied the adjacency matrix into a `4 × 4` buffer with the wrong stride.
`r165c.c` is the corrected program and the only one to read.)

### What is still missing — the transfer, named exactly

`JSP90.loc7_lemma` is the only missing *mathematical* input of the triangle case; what is left is the
**transfer**, in a new file (`lean/JSPProblem/TriFix.lean`, not yet written):

1. the enumeration: from a triangle `T` with bipartite residue and a proper two-colouring `d` of
   `X = V \ T`, produce `p0, p1, q0, q1` (the two points of each class, `JSP90.card_cls_ge_two`),
   `xpt : Fin 4 → V`, `tpt : Fin 3 → V`, the bijection `inv : Fin 7 → V`, the four cells `A` and the
   three neighbour sets `S`, and the correspondence `adj7 A S i j = decide (G.Adj (inv i) (inv j))`
   (a `49`-case analysis);
2. the three hypotheses of `hyps`: `htri` (empty triple intersection, from
   `JSP90.card_adjIn_le_two_of_isNClique_three`), `hbi0`/`hbi1` (each `S t` meets both classes, from
   `JSP90.exists_adjIn_color`), and the **corrected** badness transfer — a proper two-colouring of
   `X + {t}` would give `monoS S t m = true` for `m := aBits`-style packing of the colouring, which
   `JSP90.proper8_adj` + `JSP90.monoS_of_all` make available (this is the step that had **no** tool
   under round 164's `properX`);
3. Erdős's hypothesis on `univ \ {inv z}` (six elements, so `|S| ≥ 3`) gives an independent triple
   avoiding `z`, i.e. `hasTripleAvoiding A S z = true`, contradicting `JSP90.loc7_lemma`.

That closes `JSP90.triCase`, hence `JSP90.closeToBipartite_two_of_card_le_seven_of_triangleCase`
(round 162), hence

```lean
JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven : LocIndep 1 G → Fintype.card V ≤ 7 →
    CloseToBipartite 2 G
```

with the **optimal** constant `2` (`sun3` on six vertices attains it), together with its transversal,
`Erdős73On` and piece forms.

---

## Round 162 (`lean/JSPProblem/ThreeOrder.lean`) — **MISSING LEMMA 3 IS CLOSED, AND THE
FIVE-CYCLE CASE OF THE SHARP SEVEN-VERTEX INSTANCE WITH IT**

New file `lean/JSPProblem/ThreeOrder.lean` (17 declarations, 0 `sorry`/`admit`), imported from the root
module `JSPProblem.lean`; `lake build` OK with **1308 jobs**.  Attack family 85.  This round executes
the concrete next bet of `policy.json` verbatim — *"MISSING LEMMA 3, order bookkeeping"* — and closes
the lemma that `lean/JSPProblem/FiveCount.lean` (round 155) and `lean/JSPProblem/Three.lean`
(round 159) have been naming as **the only missing input** of the five-cycle case.

### What is proved

* **`JSP90.sdiff_D_eq_pair_of_isShapeA`, `JSP90.sdiff_D_eq_pair_of_isShapeB` — THE OUTSIDE PART OF A
  THREE-INTERSECTION FIVE-CYCLE IS THE OUTSIDE PAIR OF ITS SHAPE.**
* **`JSP90.isShapeA_swap`, `JSP90.isShapeB_swap` — THE TWO SHAPES ARE SYMMETRIC IN THE OUTSIDE PAIR.**
  A shape A read over the reversed ordered pair is the shape A of the reversed path `c - b - a`
  (`IsShapeA G C D w2 w1 ⟹ IsShapeA G C D w1 w2`, with `(a, b, c)` replaced by `(c, b, a)`); a shape
  B read over the reversed ordered pair is the shape B of the same three points with `b` and `c`
  exchanged (`w1 - a - w2 - b - c - w1`, read from `w2`, is `w2 - a - w1 - c - b - w2`).  **This is
  the whole content of the bookkeeping**, and it is why the order of the outside pair never carries
  information.
* **`JSP90.exists_ordered_shape`** — `JSP90.exists_shape` in the form that names the two outside
  points in *one* existential, so a single proof handles both shapes.
* **`JSP90.three_intersection_fiveCycle_unique` — MISSING LEMMA 3, PROVED.**  At `|V| ≤ 7`, if `D`
  and `D'` are five-cycles of a triangle-free `G` meeting a shortest odd five-cycle `C` in exactly
  three points, then `D = D'`.  The four steps are exactly those recorded in `policy.json`:

  1. the two outside pairs are the same two-element set — at `|V| ≤ 7` the outside part of a
     three-intersection five-cycle is all of `V \ C` (`JSP90.diffC_eq_univ_sdiff`), and each is
     exactly the shape's outside pair (`sdiff_D_eq_pair_of_isShapeA` / `…_of_isShapeB`);
  2. `JSP90.exists_ordered_shape` gives an **ordered** pair for each cycle, and each pair is a pair
     of **distinct** points, so the two orders are either the same or opposite;
  3. same order ⟹ `JSP90.shape_unique_of_shapes` (rounds 160–161) applies at once;
  4. opposite order ⟹ `isShapeA_swap` / `isShapeB_swap` turn the reversed shape back into the same
     statement over the same ordered pair, and `shape_unique_of_shapes` applies again.

* **`JSP90.three_intersection_fiveCycle_unique'` / `JSP90.three_intersection_fiveCycle_unique''` — THE
  SAME STATEMENT WITHOUT THE RING DATA**, the second being exactly the `huniq` that
  `lean/JSPProblem/FiveCount.lean` left as a hypothesis.  **MISSING LEMMA 3 is now proved in the form
  `JSP90.ThreeIntersectionFiveCycleUnique` of `FiveCount.lean` asks for.**
* **`JSP90.htf_of_shortest_five'`** — a shortest odd cycle of five vertices forces `G` triangle-free.
* **`JSP90.hitsOddCycles_singleton_of_shortest_five`, `JSP90.closeToBipartite_one_of_shortest_five` —
  THE FIVE-CYCLE CASE, CLOSED: A NEW INSTANCE OF THE HEADLINE THEOREM WITH THE OPTIMAL CONSTANT `1`.**

  ```lean
  IsOddCycle G C → (C shortest odd cycle) → C.card = 5 → |V| ≤ 7 → CloseToBipartite 1 G
  ```

  **no `LocIndep` hypothesis at all**, and no triangle-freeness hypothesis either (it follows).
* **`JSP90.card_five_or_seven_of_triangleFree_card_le_seven`,
  `JSP90.closeToBipartite_one_of_locIndep_one_card_le_seven_of_triangleFree`,
  `JSP90.hitsOddCycles_singleton_of_locIndep_one_card_le_seven_of_triangleFree`,
  `JSP90.LocIndepOneTriangleFree7`, `JSP90.erdos73On_one_triangleFree_seven` — THE TRIANGLE-FREE
  SEVEN-VERTEX INSTANCE WITH THE OPTIMAL CONSTANT `1`, A NEW INSTANCE OF THE HEADLINE THEOREM AND A
  STRICT STRENGTHENING OF ROUND 151.**

  ```lean
  LocIndep 1 G → |V| ≤ 7 → (G has no 3-clique) → CloseToBipartite 1 G
  ```

  `lean/JSPProblem/TriPair.lean` (round 151) could only prove this with the extra hypothesis "no
  five-cycle", because the five-cycle case was then open.  **That hypothesis is no longer needed.**
  Equivalently, the odd cycles of such a graph have a **common vertex**.
* **`JSP90.closeToBipartite_two_of_card_le_seven_of_triangleCase` — THE SEVEN-VERTEX AXIS REDUCED TO
  THE SINGLE REMAINING CASE, WITH THE OPTIMAL CONSTANT `2`.**

  ```lean
  |V| ≤ 7 → (every triangle T of G has a vertex t ∈ T with G − (T \ {t}) bipartite)
    → CloseToBipartite 2 G
  ```

  A shortest odd cycle `C` has three, five or seven vertices: `|C| = 5` is
  `closeToBipartite_one_of_shortest_five`, `|C| = 7 = |V|` is round 148's
  `closeToBipartite_one_of_shortest_oddCycle_of_card_eq` (`C` spans `V`), and `|C| = 3` makes `C` a
  triangle (`JSP90.isNClique_three_of_isOddCycle`), so the hypothesis supplies `t` with
  `G − (C \ {t})` bipartite and `JSP90.closeToBipartite_of_residue`
  (`lean/JSPProblem/Residue.lean`) turns that into `CloseToBipartite (0 + |C \ {t}|) G =
  CloseToBipartite 2 G`.  The constant `2` is optimal (`sun3`).

`#print axioms` on all of the above reports only `[propext, Classical.choice, Quot.sound]`.

### What is still missing — a single statement

**MISSING LEMMA 1, the triangle case, `|X| = 4` sub-case**: at `LocIndep 1`, `|V| ≤ 7`,
`G.IsNClique 3 T`, `X = V \ T`, NOT all three of `(deleteFinset G (T \ {t})).IsBipartite` can fail.
This is now the *whole* remaining content of the seven-vertex axis:
`JSP90.closeToBipartite_two_of_card_le_seven_of_triangleCase` shows that `htri` above is sufficient,
and `LocIndep 1` forces two vertex-disjoint triangles to be absent
(`JSP90.not_isNClique_three_of_disjoint_of_locIndep_one`, round 149), which is the hypothesis the
four-element counting step consumes.  The counting step itself is verified exhaustively in
`discovery/JSP-000090/r151k.log`; it is the concrete next bet of `policy.json`.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]` (`build_ok = true`, `sorry = 0`, `admit = 0`,
`placeholder_total = 0`, `partial_ok = true`).

---

## Round 161 (`lean/JSPProblem/ThreeB.lean`, `lean/JSPProblem/ThreeA.lean`) — **BOTH HALVES OF
MISSING LEMMA 3, PROVED**

Two new files, `lean/JSPProblem/ThreeB.lean` (14 declarations) and `lean/JSPProblem/ThreeA.lean`
(8 declarations), 0 `sorry`/`admit`, both imported from the root module `JSPProblem.lean`;
`lake build` OK with 1307 jobs.  Attack families 83 and 84.  This round executes **both** concrete
bets of `policy.json` — the **shape-B half** and the **shape-A half** of MISSING LEMMA 3, "at most
one five-cycle of `G` meets a shortest odd five-cycle `C` in exactly three points" at `|V| ≤ 7`.

**A correction about round 160 first.**  The header of `lean/JSPProblem/ThreeRing.lean` announced a
"Part 5" (`RingShapeBData`, `exists_ringShapeB`, `inter_adjIn_C_eq_singleton_of_shapeB`) and
`ACCEPTANCE.md` reported those declarations as proved, but **no such declaration existed anywhere in
the development** — round 160's file stops at the machine-checked refutation of the singleton claim.
They are proved now, together with the uniqueness statement they were the input of.

### What is proved

* **`JSP90.exists_ringShapeB` (`JSP90.RingShapeBData`, `JSP90.RingShapeB`) — THE RING DATA OF A SHAPE-B
  CYCLE.**  For `IsShapeB G C D w1 w2` and a cyclic numbering `g` of `C` in which the edge `b - c` of
  `D` starts the ring (`g 0 = b`):

  ```text
        g 4     g 0     g 1     g 2     g 3
        x ————— b ————— c ————— y ————— a
  ```

  the point `a` — the one of the three points of `C` which sees **both** outside vertices — is the
  point of `C` at ring distance **two** from the edge `b - c`, and

  ```lean
  pos    : (c = g 1 ∧ a = g 3) ∨ (c = g 4 ∧ a = g 2)
  mid    : g 0 = b
  missed : ∃ j, a = g j ∧ C \ D = {g (cycSucc j), g (cycPred j)}
  ```

  The exclusion of the other candidates is exactly the two triangles `w1 - a - c` and `w2 - a - b`:
  `b` and `c` are each a ring-neighbour of a *candidate* for `a`, so only `g 3` (resp. `g 2`) survives.
* **`JSP90.sdiff_D_eq_adjIn_C_of_ringShapeB` — THE MISSED PAIR OF THE SHAPE B IS THE NEIGHBOUR SET OF
  `a`: `C \ D = AdjIn G a C`.**  So **the missed pair determines the point** `a`, the shape-B
  counterpart of round 160's `adjIn_C_subset_of_shapeA`.
* **`JSP90.card_adjIn_C_le_two` — EVERY OUTSIDE VERTEX OF A SHORTEST ODD FIVE-CYCLE MEETS IT IN AT
  MOST TWO POINTS**, in the language of `AdjIn` (round 152's position form `card_inter_neigh_le_two`
  of `JSPProblem/Fan.lean`, pulled back through the ring numbering).
* **`JSP90.adjIn_C_pair_of_ringShapeB`, `JSP90.inter_adjIn_C_eq_singleton_of_ringShapeB` — THE
  COMMON NEIGHBOUR OF THE TWO OUTSIDE VERTICES IS THE SINGLE POINT `a`:**

  ```lean
  AdjIn G w1 C = {a, c}   ∧   AdjIn G w2 C = {a, b}   ∧   AdjIn G w1 C ∩ AdjIn G w2 C = {a}
  ```
* **`JSP90.eq_of_sdiff_eq_of_card_le_seven` — AT `|V| ≤ 7` A THREE-INTERSECTION FIVE-CYCLE IS
  DETERMINED BY ITS MISSED PAIR.**  Together with round 159's `diffC_eq_univ_sdiff` this says MISSING
  LEMMA 3 is *exactly* the statement that at most one of the ten candidate pairs is realised.
* **`JSP90.shapeB_unique` — THE SHAPE-B HALF OF `JSP90.ThreeIntersectionFiveCycleUnique`, PROVED.**
  At `|V| ≤ 7`, two three-intersection five-cycles of the shape B over the same pair of outside
  vertices are equal: same `a` (the singleton intersection), hence same missed pair, hence equal.
* **`JSP90.shapeA_shapeB_exclusive` — THE TWO SHAPES NEVER MIX OVER A FIXED OUTSIDE PAIR**
  (`AdjIn G w1 C ∩ AdjIn G w2 C` is `∅` in shape A and a singleton in shape B), so the remaining
  case analysis of MISSING LEMMA 3 is the **shape-A half alone**.

### The shape-A half — `lean/JSPProblem/ThreeA.lean`, also PROVED

* **Part 0 — `JSP90.card_sdiff_eq_two`, `JSP90.ne_of_card_sdiff`, `JSP90.sdiff_pair_facts`: THE TWO
  MISSED POINTS ARE TWO DISTINCT POINTS OF `C` WHICH `D` DOES NOT USE.**
* **Part 1 — `JSP90.adjIn_C_eq_pair`, `JSP90.adjIn_C_pairs_of_ringShapeA`: THE NEIGHBOUR SETS INSIDE
  `C` OF THE FIVE POINTS OF A SHAPE-A CYCLE.**

  ```text
  N_C(a) = {b, d}   N_C(b) = {a, c}   N_C(c) = {b, e}   N_C(d) = {e, a}   N_C(e) = {d, c}
  ```

  (a chordless five-cycle gives every vertex exactly two neighbours inside it,
  `JSP90.card_neighIn_C_eq_two`, and shape A exhibits two adjacencies at each point).
* **Part 2 — `JSP90.shapeA_unique`: THE SHAPE-A HALF OF `JSP90.ThreeIntersectionFiveCycleUnique`,
  PROVED.**  At `|V| ≤ 7`, **two three-intersection five-cycles of the shape A over the same ordered
  pair of outside vertices are equal**.  (The case analysis itself needs no order bound.)
* **Part 3 — `JSP90.not_shapeA_of_shapeB`, `JSP90.shape_unique_of_shapes`: THE TWO HALVES TOGETHER.**
  Two three-intersection five-cycles of the same shape over the same ordered outside pair are equal,
  and the shapes never mix over a fixed pair.

### The shape-A half: the case analysis (as it is formalised in `ThreeA.lean`)

Let `D₁`, `D₂` be three-intersection five-cycles of shape A over the same outside pair `w1, w2`, at
`|V| ≤ 7`, and read both in the *single* ring `g` of `C` given by `D₁` (`a₁ = g 4`, `b₁ = g 0`,
`c₁ = g 1`, `d₁ = g 3`, `e₁ = g 2`, missed pair `{g 3, g 2}`).

1. If `a₂ ∈ C ∩ D₁` then `{a₂, b₂, c₂} = C ∩ D₂ = C ∩ D₁` (both triples have three elements), so the
   missed pairs agree and `D₁ = D₂` (`JSP90.eq_of_sdiff_eq_of_card_le_seven`).
2. Otherwise `a₂ ∈ C \ D₁ = {d₁, e₁}`, and symmetrically `a₁ ∈ C \ D₂`, while `d₂`, `b₂` are the two
   **ring-neighbours** of `a₂` and `e₂`, `c₂` the two points at **ring distance two** from `a₂`.
   * `a₂ = g 3 = d₁`: then `{d₂, b₂} = {g 2, g 4} = {e₁, a₁}`; `a₁ = g 4` is at distance *one* from
     `a₂`, so it must be `d₂` or `b₂`; if `a₁ = e₂` (distance two) this is impossible, and if
     `a₁ = d₂` then `b₂ = e₁ = g 2` and `c₂ = b₁ = g 0`, but `b₂ - c₂ = g 2 - g 0` is not an edge of
     `C` (a chord), while shape B's `G.Adj b c` is required.
   * `a₂ = g 2 = e₁`: then `{d₂, b₂} = {g 1, g 3} = {c₁, d₁}` and `a₁ = g 4`, being at distance two
     from `g 2`, must be `e₂`; hence `c₂ ∈ {g 0, g 4}` and, since `G.Adj b₂ c₂` and `c₂ ≠ a₂`,
     `b₂ = g 1`, `c₂ = g 0` or `b₂ = g 3`, `c₂ = g 4 = a₁ = e₂ ∉ D₂` (impossible).  The remaining case
     gives `w1 ~ g 0` (from `D₂`) and `w1 ~ g 1` (from `D₁`), **two consecutive points of `C`** — which
     `JSP90.neigh_pair_close_of_shortest` forbids.

So the shape-A half is a position analysis with no new mathematical input, and it is **proved** as
`JSP90.shapeA_unique`: each of the four cases is realised in Lean in `lean/JSPProblem/ThreeA.lean`
(case I forces `b₂ = b₁`, case II forces `c₂ = b₂`, case III forces `b₁ = a₁`, case IV forces
`b₁ = b₂` and then `a₁ = c₂`, all contradictions).

### What is still missing in MISSING LEMMA 3

Only the **ordering bookkeeping**: at `|V| ≤ 7` two three-intersection five-cycles have the same
outside set (`JSP90.diffC_eq_univ_sdiff`), and `JSP90.exists_shape` produces an *ordered* pair, so
`JSP90.shape_unique_of_shapes` has to be applied with the two orders matched — either directly or
after swapping `w1`, `w2` in exactly one of the two shapes, which is a four-case analysis of the same
shape (a shape A over `(w2, w1)` is the shape A of the reversed path `c - b - a` over `(w2, w1)`).
That bookkeeping is the `next_bet` of `policy.json`; with it
`JSP90.ThreeIntersectionFiveCycleUnique` is closed at `|V| ≤ 7`, and the five-cycle case of
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven` follows from the already proved
`JSP90.closeToBipartite_one_of_unique`.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]` (`build_ok = true`, `sorry = 0`, `admit = 0`,
`placeholder_total = 0`, `partial_ok = true`; `lake build` OK with 1307 jobs).

---

## Round 160 (`lean/JSPProblem/ThreeRing.lean`) — **THE RING POSITIONS OF THE TWO SHAPES**, and a
**refutation of round 159's next bet**

New file `lean/JSPProblem/ThreeRing.lean` (42 declarations, 0 `sorry`/`admit`), imported from the root
module `JSPProblem.lean`; `lake build` OK with 1305 jobs.  Attack family 82.  This round executes the
concrete next bet of `policy.json` — MISSING LEMMA 3a, *"in shape A the neighbour sets
`AdjIn G w1 C` and `AdjIn G w2 C` are singletons"* — **and refutes it**, then proves the correct
replacement: the ring positions of the points of a three-intersection five-cycle, which is the data any
uniqueness proof has to read off.

### The correction (this is the round's main finding)

MISSING LEMMA 3a as recorded in round 159 is **false**: in a shape-A instance the neighbour set of an
outside vertex inside `C` can have **two** elements, and the two sizes are independent.  This is
machine-checked in Lean (`JSP90.not_singleton_shapeA`) and measured exhaustively
(`discovery/JSP-000090/r160.c`, log `r160.log`):

| shape A: `(|N_C(w₁)|, |N_C(w₂)|)` | occurrences |
| --- | --- |
| `(1,1)` | 10 |
| `(1,2)` | 10 |
| `(2,1)` | 10 |
| `(2,2)` | 10 |

while shape B **always** has `(2,2)`.  The Lean witness is the seven-vertex graph with
`C = 0-1-2-3-4-0`, `D = 6-0-4-3-5-6` (shape A with `a = 0`, `b = 4`, `c = 3`, `w₁ = 5`, `w₂ = 6`,
missed pair `{1, 2}`), for which `N_C(5) = {1, 3}` and `N_C(6) = {0}` — proved as
`JSP90.isShapeA_sA`, `JSP90.adjIn_5_C_sA`, `JSP90.adjIn_6_C_sA`, `JSP90.not_singleton_shapeA`.

### What is proved

* **Part 0 — `JSP90.cyc5V`, `JSP90.isOddCycle_of_cyc5V`.**  Five pairwise distinct vertices with the
  five adjacencies in cyclic order are an `IsOddCycle` of the five-element set they span (the
  construction of `JSPProblem/Petersen.lean`'s `isOddCycle_delete_cyc5`, at an arbitrary vertex type).
* **Part 1 — the ring arithmetic.**  `JSP90.five_iterate_eq`, `JSP90.cycPred_five`,
  `JSP90.cycPred_three`, `JSP90.five_step_ne`, `JSP90.five_f_ne`, `JSP90.five_mem_rest`, and the finset
  bookkeeping `card_two`/`card_three`/`card_four`/`card_pair`/`sdiff_of_card`/`inter_D_eq_triple`/
  `mem_C_split`/`mem_C_of_mem`/`mem_of_mem_congr`.
* **Part 1 bis — `JSP90.ringShift`: THE RING RE-NUMBERED.**  Every proof below reads positions in the
  ring; `ringShift f j` numbers the ring with `j` as `0`, and then the positions are the *literals*
  `g 0 … g 4`, so that every ring inequality is a `decide` and every ring adjacency an instance of
  `hcycg`/`adj_ringPred`.  `ringShift_inj`, `ringShift_adj`, `ringShift_mem` transport injectivity, the
  cyclic adjacency and the membership of the ring across the re-numbering.  This is what turned the
  shape analysis of Parts 2–6 into kernel proofs.
* **Part 1 ter — the ring positions.**  `JSP90.two_neigh_ring` (two distinct neighbours of a point of
  `C` are its two ring-neighbours: the converse direction of round 152's `filter_adj_C_eq_ringPair`),
  `JSP90.path3_ring` (**three points of `C` with `Adj a b`, `Adj b c`, `a ≠ c` are three consecutive
  points of the ring**), `JSP90.adj_ring_neigh` (two adjacent points of `C` are consecutive).
* **Part 2 — `JSP90.RingShapeAData`, `JSP90.exists_ringShapeA`: THE MISSED PAIR OF A SHAPE-A CYCLE.**
  For `IsShapeA G C D w1 w2` and a cyclic numbering `g` of `C` in which the **middle of the path**
  `a - b - c` is `g 0`:

  ```text
        g 4     g 0     g 1     g 2     g 3
        a ————— b ————— c ————— e ————— d
        |                                    |
        └————————————————————————————————————┘
  ```

  with `w1 ~ c`, `w2 ~ a`, `w1 ~ w2`, `C \ D = {d, e}`, `G.Adj d e`, **`G.Adj a d`**, **`G.Adj c e`**:
  the missed pair is an **edge** of `C`, the one opposite to the middle of the path, and its two points
  are the ring-neighbours of `a` and of `c`.
* **Part 4 — `JSP90.adjIn_C_subset_of_shapeA`: THE CORRECTED MISSING LEMMA 3a.**

  ```lean
  AdjIn G w1 C ⊆ {c, d}   ∧   AdjIn G w2 C ⊆ {a, e}
  ```

  The neighbours of the two outside vertices inside `C` are confined to **two** candidates each — the
  far endpoint of the path and the missed point adjacent to it — and nothing else can occur.
* **Part 5 — `JSP90.four_intersection_of_shapeA`: WHAT THE SECOND CANDIDATE MEANS.**  If `d` is the
  second neighbour of `w1` inside `C`, then `w1 - d - a - b - c - w1` is a **four-intersection
  five-cycle** of `G`.  So `e` is always missed (by `D`) while `d` is missed exactly when those extra
  adjacencies are absent: the two candidates are not symmetric.
* **Part 6 — `JSP90.RingShapeBData`, `JSP90.RingShapeB`: THE SHAPE-B RING DATA.**  For
  `IsShapeB G C D w1 w2` the three points are `b = g 0`, `c = g 1`, `a = g 3` — `a` is the point of the
  three adjacent to neither `b` nor `c`, because the triangles `w1 a c` and `w2 a b` are excluded — and
  the missed pair is `{g 2, g 4}`, **the two ring-neighbours of `a`**.  With round 159's
  `adjIn_D_pair_of_shapeB` this yields `C \ D = AdjIn G a C` and `AdjIn G w1 C ∩ AdjIn G w2 C = {a}`,
  which is the whole input of the shape-B half of MISSING LEMMA 3.

### The census of this round (`discovery/JSP-000090/r160.c`, output `r160.log`)

A **complete** search over all `2^16` graphs on seven vertices with `C` fixed as the five-cycle
`0-1-2-3-4-0` (`202` triangle-free graphs):

| quantity | value |
| --- | --- |
| `max # {D : \|D ∩ C\| = 3}` | **1** — MISSING LEMMA 3 **holds** at `\|V\| ≤ 7` |
| `max` number of points of `C` missed by such a `D` | **2** — so *three* points of `C` are transversals (better than the four that round 155's counting gave) |
| violations of the extra-point lemma of Part 5 | **0** in `20 + 20` instances |
| shape-B instances with missed pair = `N_C(a)` | **10 / 10** |

### What is still missing

`JSP90.ThreeIntersectionFiveCycleUnique` at `|V| ≤ 7`.  Round 160 has proved all of its input — the
ring data of both shapes and the candidate neighbour sets — so the remaining work is the case analysis
alone, spelled out in the header of `JSPProblem/ThreeRing.lean` and in `discovery/JSP-000090/policy.json`:
the **shape-B half** follows from `C \ D = AdjIn G a C` together with `AdjIn G w1 C ∩ AdjIn G w2 C = {a}`
(two shape-B cycles share the outside pair by `JSP90.diffC_eq_univ_sdiff`, hence have the same `a`,
hence the same missed pair, hence are equal), and the **shape-A half** is an eight-case analysis in
which a second shape-A cycle is excluded either by a triangle `w1 ~ w2 ~ a_j` or by
`JSP90.shortArc_of_shortest` applied to `w1` (an outside vertex never sees two consecutive points of
`C`).  With that, the five-cycle case of `JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven`
follows, and the remaining open case of that instance is the triangle case (MISSING LEMMA 1, the
`|X| = 4` sub-case).

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]` (`build_ok = true`, `sorry = 0`, `admit = 0`,
`placeholder_total = 0`, `partial_ok = true`; `lake build` OK with 1305 jobs).

---

## Round 159 (`lean/JSPProblem/Three.lean`) — **THE SHAPE OF A THREE-INTERSECTION FIVE-CYCLE**, and a
correction: the uniqueness statement is **false without the order bound**

New file `lean/JSPProblem/Three.lean` (36 declarations, 0 `sorry`/`admit`), imported from the root
module `JSPProblem.lean`; `lake build` OK with 1304 jobs.  Attack family 81.  This round executes the
concrete next bet of `policy.json` — MISSING LEMMA 3, `JSP90.ThreeIntersectionFiveCycleUnique` — as far
as the local structure allows, and **corrects the statement itself**.

### The correction (this is the round's main finding)

`JSP90.ThreeIntersectionFiveCycleUnique` as written in round 155 carries **no order bound**, and it is
`False` in that form.  `discovery/JSP-000090/r159.c` (machine checked, output in
`discovery/JSP-000090/r159.log`) exhibits nine vertices in a triangle-free graph:

```text
V = {0,1,2,3,4} ∪ {5,6} ∪ {7,8},   C  = 0-1-2-3-4-0
D1 = 6-0-1-2-5-6   (outside pair {5,6}, inside {0,1,2}, missed pair {3,4})
D2 = 2-3-4-7-8-2  (outside pair {7,8}, inside {2,3,4}, missed pair {0,1})
```

`G` is triangle-free (`NOORDER 0`), so the odd girth is 5 and `C` is a shortest odd cycle; `D1` and `D2`
are two **distinct** five-cycles, each meeting `C` in exactly three points (`INTER_D1C 3`,
`INTER_D2C 3`).  The two cycles use **disjoint** pairs of outside vertices, which is exactly what
`|V| ≤ 7` forbids.  The `def` in `JSPProblem/FiveCount.lean` has been **corrected** to carry
`Fintype.card V ≤ 7`, which is the hypothesis under which round 155's `2^21`-graph measurement was taken,
and the only one for which the statement is true.  (The conditional consumer
`JSP90.closeToBipartite_one_of_unique` already had the order bound among its hypotheses, so nothing
downstream changes.)

### What is proved

* **Part 0 — `JSP90.htf_of_shortest_five`.**  A shortest odd cycle of five vertices is triangle-free: a
  triangle is an odd cycle with three vertices.  (No order bound needed.)
* **Part 1 — the ring arithmetic of a five-cycle.**  `JSP90.five_dist` (two distinct points are at
  distance one or two), `JSP90.five_iterate_ne`, `JSP90.five_iterate_five`, the five "iterate = nested
  successor" lemmas `five_iterate_one … five_iterate_five'`, `JSP90.five_univ_eq_iter` (the ring, written
  out), `JSP90.five_iterate_ne_pair`, `JSP90.not_mem_pair`, and the two localisation lemmas
  `JSP90.five_iterate_mem` / `JSP90.five_iterate_mem2` (which of the five points a position is).
* **Part 2 — `JSP90.neighIn_C_inj`: THE RING PAIR DETERMINES THE POINT.**  Two points of a shortest odd
  five-cycle with the same neighbours inside `C` are equal (round 152's `JSP90.five_pair_inj'` applied to
  `JSP90.filter_adj_C_eq_ringPair`).  This is the "the middle of a path in `C` is determined" step.
* **Part 3 — `JSP90.diffC_eq_univ_sdiff`: THE ORDER HYPOTHESIS BUYS THE OUTSIDE SET.**  At `|V| ≤ 7` a
  five-cycle meeting `C` in three points has `D \ C = V \ C` (`|C ∪ D| = 7 = |V|`), so `D` is determined
  by `D ∩ C`, i.e. **by the missed pair `C \ D`** (`JSP90.eq_of_inter_eq_of_diffC`).  This is the formal
  content of why the `r159.c` counterexample needs nine vertices, and it turns MISSING LEMMA 3 into
  "at most one of the **ten** candidate pairs of `C` is realised".
* **Part 4 — `JSP90.IsShapeA`, `JSP90.IsShapeB`, `JSP90.exists_shape`: THE TWO SHAPES.**  Every
  three-intersection five-cycle of a triangle-free graph has exactly one of the two shapes that round
  155's measurement found, now as a kernel proof from the cyclic ordering:

  ```lean
  IsShapeA G C D w1 w2 : ∃ a b c, a b c ∈ C, (distinct), w1 w2 ∉ C, w1 ≠ w2, D = {a,b,c,w1,w2} ∧
                         G.Adj a b ∧ G.Adj b c ∧ G.Adj c w1 ∧ G.Adj w2 a ∧ G.Adj w1 w2
  IsShapeB G C D w1 w2 : ∃ a b c, a b c ∈ C, (distinct), w1 w2 ∉ C, w1 ≠ w2, D = {a,b,c,w1,w2} ∧
                         G.Adj b c ∧ G.Adj a w1 ∧ G.Adj a w2 ∧ G.Adj b w2 ∧ G.Adj c w1
  exists_shape : (∃ w1 w2, w1 ≠ w2 ∧ IsShapeA …) ∨ (∃ w1 w2, w1 ≠ w2 ∧ IsShapeB …)
  ```

  Shape A is `w1 - w2 - a - b - c - w1` (the outside vertices adjacent in `D`, `a - b - c` a path of
  `C`); shape B is `w1 - a - w2 - b - c - w1` (outside vertices at distance two, `a` sees both, `b - c`
  the only edge of `D` inside `C`).  The proof is the ring arithmetic: the two positions of `D` outside
  `C` are at distance one or two along the ring (`JSP90.five_dist`), and `JSP90.compl_eq_pair` turns the
  cardinality-two complement of `P = {i | g i ∈ C}` into the corresponding pair.
* **Part 5 — what the shapes force.**  `JSP90.card_adjIn_D_eq_two` (round 152's degree lemma in the
  language of `AdjIn`) plus `JSP90.eq_pair_of_card_two` give the *whole* neighbour sets:
  * `JSP90.adjIn_D_pair_of_shapeA`: `AdjIn G w1 D = {c, w2}` and `AdjIn G w2 D = {a, w1}`;
  * `JSP90.adjIn_D_pair_of_shapeB`: `AdjIn G w1 D = {a, c}` and `AdjIn G w2 D = {a, b}`;
  * `JSP90.disjoint_adjIn_C_of_shapeA`: in shape A the two outside vertices have **no** common neighbour
    in `C` (it would close a triangle with `w1 - w2`), and `JSP90.inter_adjIn_C_ne_empty_of_shapeB`:
    in shape B they **do** (namely `a`) — so **the two shapes are mutually exclusive over a fixed
    outside pair**.

### What is still missing

`JSP90.ThreeIntersectionFiveCycleUnique` at `|V| ≤ 7`, and with it
`JSP90.closeToBipartite_one_of_unique` → the five-cycle case of
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven` and then the triangle case (MISSING LEMMA 1,
the `|X| = 4` sub-case).  Given Parts 4 and 5 the remaining step is now short and is spelled out in
`JSPProblem/Three.lean` and in `discovery/JSP-000090/policy.json`: for `D` of shape A one has
`AdjIn G w1 C = {c}` and `AdjIn G w2 C = {a}` up to the single extra ring point (shape A forces
`|AdjIn G w1 C| = |AdjIn G w2 C| = 1`), so the missed pair `{a, c}` determines the middle by
`JSP90.neighIn_C_inj`; for shape B the missed pair is `{a, b, c}`'s complement and `N1 ∩ N2 = {a}`
determines `a`.  The two shapes cannot mix (`AdjIn G w1 C ∩ AdjIn G w2 C` empty vs. nonempty).

## Round 155 (`lean/JSPProblem/FiveCount.lean`) — **THE COUNTING LAYER OF THE FIVE-CYCLE CASE**, and
the five-cycle case reduced to one statement

New file `lean/JSPProblem/FiveCount.lean` (24 declarations, 0 `sorry`/`admit`), imported from the root
module `JSPProblem.lean`; `lake build` OK with 1303 jobs.  Attack family 80.  This round executes the
*next bet* of `policy.json` verbatim — parts (a) and (b) of round 152's plan, i.e. the cardinal form
of the injectivity of round 152's Part 4 and the pigeonhole built on it — and turns it into the exact
reduction of the five-cycle case of the sharp seven-vertex instance to **one** statement.

### What is proved

* **`JSP90.card_missed_le_card_univ_sdiff` — THE PIGEHOLE OF ROUND 152, PART (a).**  With
  `JSP90.Missed C = {c ∈ C : (C \ {c}) ∪ {x} is a five-cycle for some x ∉ C}`,

  ```lean
  IsOddCycle G C → C shortest odd → C.card = 5 → G triangle-free → cyclic numbering f : Fin 5 → V →
    |Missed C| ≤ |univ \ C|
  ```

  proved by exhibiting the injective carrier `JSP90.Witness c := c` (the outside vertex of the
  five-cycle which misses `c`) and applying `Finset.card_le_card_of_injOn`.  No hypothesis beyond round
  152's: the injectivity is `JSP90.x_ne_y_of_two_fiveCycles_singleton`, read as an injection.
* **`JSP90.card_missed_le_two_of_card_le_seven`** — at `|V| ≤ 7`, `|Missed C| ≤ 2`.
* **`JSP90.card_missedFour_le_one`** — the *set* form of round 152's per-vertex bound: an outside
  vertex witnesses at most one point of `C`, proved through the bridge
  `JSP90.filter_adj_eq_of_fiveCycle_singleton` and the ring-pair arithmetic
  (`JSP90.filter_adj_C_eq_ringPair`, `JSP90.five_pair_inj'`).
* **`JSP90.exists_mem_not_mem_missed`** (round 152's part (b)) — some point of `C` is missed by no
  four-intersection five-cycle.
* **`JSP90.exists_mem_meetsFour` and `JSP90.MeetsFour` — THE INSTANCE OF THE ROUND.**  For a shortest
  odd five-cycle `C` in a graph on at most seven vertices there is a point `c ∈ C` with

  ```lean
  ∀ D, IsOddCycle G D → 4 ≤ |D ∩ C| → c ∈ D
  ```

  i.e. **`c` meets every odd cycle of `G` that meets `C` in at least four points**.  Notably this half
  of the five-cycle case needs *no* triangle-freeness.
* **`JSP90.isOddCycle_five_or_mem_of_meetsFour` — THE REDUCTION.**  With `JSP90.MeetsFour` and
  triangle-freeness (odd girth ≥ 5, `JSP90.card_ge_five_of_isOddCycle_of_triangleFree`), the order
  bound and `JSP90.mem_C_of_isOddCycle_of_card_eq_seven` (a seven-cycle is `univ`, hence contains `C`):

  > **every odd cycle of `G` either contains `c`, or is a five-cycle meeting `C` in exactly three
  > points.**

  (the intersection is at least `5 + 5 − 7 = 3` for two five-cycles and at most three by
  `JSP90.MeetsFour`).  `JSP90.mem_hits_ge_four_of_meetsFour` is the transversal shape: a point of `C`
  meets every odd cycle that is not a three-intersection five-cycle.

### The blocker of this round: MISSING LEMMA 3, named and measured

`JSP90.ThreeIntersectionFiveCycleUnique`: **at most one five-cycle of `G` meets a shortest odd
five-cycle `C` in exactly three points.**  It is now the *only* missing input: with it the missed
points of `C` are a set of at most two (Part 2) together with the missed pair of a single five-cycle,
hence at most four of the five, so some point of `C` meets every odd cycle and
`JSP90.closeToBipartite 1 G` follows at `LocIndep 1`, `|V| ≤ 7`.

Measured by `discovery/JSP-000090/r155.c` over all `2^21` graphs on seven vertices (`50904` triangle-free
pairs `(G, C)` with `C` a five-cycle): **max `# {five-cycles D : |C \ D| = 2} = 1`, `0` violations**; and
the two shapes such a `D` can take are also verified exhaustively (`0` violations each):

| shape | `D` | occurrences | `S = D ∩ C` | `N_C(w₁), N_C(w₂)` | missed pair |
| --- | --- | --- | --- | --- | --- |
| A | `w₁ ~ w₂` in `D` | `10080` | three *consecutive* vertices of `C`, the middle one with no neighbour in `W` | each contains one endpoint | an **edge** of `C` |
| B | `w₁ ≁ w₂` in `D` | `2520` | not consecutive; `\|E(S,W)\| = 4` | forced: `w₁ ~ {a,c}`, `w₂ ~ {b,c}` | a pair at **distance two** in `C` |

In shape B a four-intersection five-cycle always also exists (`2520 / 2520`), which is why the overall
bound on the number of missed points is `2` (`0` cases with more than four).  Two bugs of the
measurement program were found and fixed while writing it (self-adjacency counted by `eidx i i`, and a
broken cyclic-order walk); both were caught by the program's own `NOORDER`/`BADMISS` checks.

### Part 6 — the closure: `ThreeIntersectionFiveCycleUnique` really is the only missing input

`JSP90.AllMissed` (the points of `C` missed by *some* odd cycle) and `JSP90.Miss` (an odd cycle missing
a point) are named, and the following are proved:

* **`JSP90.mem_missed_or_three`** — **every missed point is either a four-intersection miss or the miss
  of a three-intersection five-cycle**:
  `z ∈ Missed C ∨ ∃ D, IsOddCycle G D ∧ D.card = 5 ∧ |D ∩ C| = 3 ∧ z ∉ D`.  (Part 5 plus the two counting
  facts: two five-cycles on at most seven vertices meet in at least three points, and a triangle is
  excluded.)
* **`JSP90.card_allMissed_le_four_of_unique`** — **at most four of the five points of `C` are missed by
  any odd cycle**, given `∀ D D', IsOddCycle G D → IsOddCycle G D' → D.card = 5 → D'.card = 5 →
  |D ∩ C| = 3 → |D' ∩ C| = 3 → D = D'`.  (Two misses from the four-intersection cycles, two from the
  unique three-intersection five-cycle.)
* **`JSP90.hitsOddCycles_singleton_of_unique`** and **`JSP90.closeToBipartite_one_of_unique`** — the
  conclusion:

  ```lean
  JSP90.closeToBipartite_one_of_unique : CloseToBipartite 1 G
  ```

  So **the five-cycle case of `JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven` follows from
  `JSP90.ThreeIntersectionFiveCycleUnique` and nothing else**; no other input is missing, and Parts 1
  to 6 use no instance of `LocIndep 1` (for triangle-free graphs on at most seven vertices the
  hypothesis is vacuous, since `R(3,3) = 6`).  The *one* remaining lemma of this development's five-cycle
  case is thus precisely the `Fin 5` case analysis recorded in `discovery/JSP-000090/r155.log`.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps reporting
`missing_theorems = ["jsp_000090_main"]` (`build_ok = true`, `sorry = 0`, `admit = 0`,
`placeholder_total = 0`, `partial_ok = true`; `lake build` OK with 1303 jobs).

---

## Round 151 (`lean/JSPProblem/TriPair.lean`) — **THE LOCAL STRUCTURE AT A BAD VERTEX OF A
TRIANGLE**, and a **measurement bug that voids the five-cycle counts of round 150**

New file `lean/JSPProblem/TriPair.lean` (23 declarations, 0 `sorry`/`admit`), `lake build` OK with 1301
jobs), imported from the root module `JSPProblem.lean`.  Attack family 78, the **triangle axis**: the
concrete target of rounds 149–150 was the sharp seven-vertex instance
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven` (`LocIndep 1 G`, `|V| ≤ 7` ⟹
`CloseToBipartite 2 G`), whose two open cases are a shortest odd cycle of `5` or of `3` vertices.

### What is proved

* **`JSP90.adjIn_card_two_and_edge_or_path` — THE LOCAL STRUCTURE AT A BAD VERTEX OF A TRIANGLE.**
  Write `X = V \ T` for the residue of a triangle `T` (at most four vertices when `|V| ≤ 7`, and
  `G[X]` bipartite by Part 0b of `JSPProblem/Seven.lean`) and `S_t = AdjIn G t X`.  Then

  ```lean
  (deleteFinset G T).IsBipartite → ¬ (deleteFinset G (T \ {t})).IsBipartite →
    (AdjIn G t X).card = 2 ∧
      ((∃ p q, p ∈ AdjIn G t X ∧ q ∈ AdjIn G t X ∧ G.Adj p q) ∨
       (∃ p q x y, p ∈ AdjIn G t X ∧ q ∈ AdjIn G t X ∧
          x ∈ X \ AdjIn G t X ∧ y ∈ X \ AdjIn G t X ∧
          G.Adj p x ∧ G.Adj x y ∧ G.Adj y q))
  ```

  i.e. **a bad vertex of a triangle sits on either a triangle (`S_t` an edge of `G[X]`) or a
  five-cycle (`S_t` the two ends, `X \ S_t` the two adjacent middle vertices, all four adjacencies
  given)**.  The content is: the odd cycle through `t` avoiding the other two vertices of `T` lies
  in `X ∪ {t}`, so it has three or five vertices, and Erdős's hypothesis
  (`JSP90.card_adjIn_le_two_of_isNClique_three`) says the two neighbours of `t` on it exhaust its
  neighbours outside `T`.  `JSP90.exists_isOddCycle_through_of_not_isBipartite` is the first step:
  the odd cycle really meets `t`, because the residue is bipartite.
* **`JSP90.card_ge_five_of_isOddCycle_of_triangleFree`** — in a triangle-free graph every odd cycle
  has at least five vertices;
* **`JSP90.closeToBipartite_one_of_locIndep_one_card_le_seven_of_triangleFree_no5`** (with the
  transversal form `hitsOddCycles_singleton_…`, the `tauOdd` form, the class
  `LocIndepOneTriangleFreeNoFive`, the `Erdős73On` form `erdos73On_one_triangleFree_no5_seven` and
  the sharpness `not_closeToBipartite_zero_of_triangleFree_no5_of_not_isBipartite`) — **a new
  instance of the headline theorem with the optimal constant `1`**:

  ```lean
  LocIndep 1 G → |V| ≤ 7 → (no 3-clique) → (no five-cycle) → CloseToBipartite 1 G
  ```

### **A MEASUREMENT BUG, AND THE CORRECTED CENSUS**

The odd-cycle detector used by `discovery/JSP-000090/r150b.c` — and re-used by this round's first
measurements — performs its connectivity walk by pushing the **accumulated vertex mask** instead of a
vertex, so the search never leaves the lowest-numbered vertex and **every five-cycle is missed**.
Consequently the claims

* "a `LocIndep 1` graph on `|V| ≤ 7` contains no five-cycle", and
* "every non-bipartite triangle-free `LocIndep 1` graph on seven vertices has a spanning seven-cycle",

made in round 150 and re-measured here, are **void**.  In particular `LocIndep 1` together with
`|V| ≤ 7` does **not** give odd girth at least seven, so round 150's instance
`closeToBipartite_one_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven` does **not** apply to the
triangle-free seven-vertex graphs; the version with an explicit "no five-cycle" hypothesis is what
this file proves.

The corrected census (`discovery/JSP-000090/r151q.c`; all `986787` `LocIndep 1` graphs on seven
vertices, classified by the cardinality of a shortest odd cycle) is

| shortest odd cycle | graphs |
| --- | --- |
| 3 | 853 286 |
| 5 | **29 904** (all of them triangle-free) |
| 7 | 360 |
| bipartite | 103 237 |

and the extremal values are unchanged: `max tauOdd = 1` over the `133501` triangle-free `LocIndep 1`
graphs and `max tauOdd = 2` over the `853286` graphs containing a triangle, so the constant `2` at
seven vertices is still sharp and the sharp instance still splits as: **no triangle** ⟹ one
deletion (now known to need the five-cycle case, *not* the odd girth), **a triangle** ⟹ two
deletions.

### What is *not* proved

* **the triangle case** of `closeToBipartite_two_of_locIndep_one_card_le_seven`: the input
  `adjIn_card_two_and_edge_or_path` is now proved, together with the empty-triple-intersection
  consequence of `card_adjIn_le_two_of_isNClique_three` (no vertex outside `T` meets all three
  vertices of `T`) and Erdős's hypothesis read on the six-element subsets `V \ {t}` and `V \ {x}`;
  what remains is the finite four-element counting step, verified exhaustively in
  `discovery/JSP-000090/r151d.log`/`r151i.log`/`r151k.log` (bipartite graph on four vertices, three
  two-element sets each an edge or carrying the five-cycle path, empty triple intersection, no
  repeated pair an edge, at most one complement carrying an edge).  A hypothesis-free version of the
  claim is **false** (the star of `r151f.c`), so the `K₄` exclusion is essential;
* **the five-cycle case**: with the corrected census this is now the *only* missing step for the
  triangle-free seven-vertex instance (`CloseToBipartite 1`), and it is exactly round 150's Missing
  Lemma 1: an outside vertex witnesses **at most one** five-cycle of the form
  `(C \ {c}) ∪ {w}` with `C` a shortest five-cycle.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]` (`build_ok = true`, `sorry = 0`, `admit = 0`,
`placeholder_total = 0`, `partial_ok = true`).

---

## Round 149 (`lean/JSPProblem/Six.lean`) — the sharp six-vertex instance and the **piece bridge**

Round 148 left as its concrete target `JSP90.closeToBipartite_two_of_locIndep_one_card_le_six`
(`LocIndep 1 G`, `|V| ≤ 6` ⇒ `CloseToBipartite 2 G`), whose sharpness was measured exhaustively
(all `32768` graphs on six vertices: `max tauOdd` over `MaxDef ≤ 1` is exactly `2`, witnessed by the
three-sun `sun3`).  The instance turns out to follow from a *reduction*, and the reduction — not the
instance — is the reusable content of the round.

* **THE PIECE BRIDGE** (the real new content, and one that every decomposition argument in this
  development needs): `JSP90.closeToBipartite_pieceOf_closeToBipartite_of_card_le` says that an
  instance of Erdős #73 at `k = 1` on graphs of order at most `n` with constant `m` applies to
  **every induced piece** `U` with `|U| ≤ n`.  The class `JSP90.LocIndepOneSmallOrder` of round 148
  counts the vertices of the *type*, whereas the residue of any decomposition is a vertex *set*; the
  bridge closes that gap, using `JSPProblem/FiniteSharp.lean`'s `moveGraph` together with
  `JSP90.locIndep_one_of_locIndep_one_moveGraph` (Erdős's hypothesis read on the moved piece) and
  `JSP90.mem_Z_image_of_mem` (the witness and a `Fin 2`-colouring pulled back).
* **THE ONE-MORE-VERTEX STEP**: `JSP90.closeToBipartite_succ_of_closeToBipartite_one` (delete a
  vertex `a`; the witness of the residue is intersected with `V \ {a}` — which does not change the
  residue, `A \ (X ∩ A) = A \ X` — and `a` is added back) and
  `JSP90.LocIndepOneSmallOrder.succ` (the same reduction for the class of round 148).
* **THE INSTANCE**: > **`JSP90.closeToBipartite_two_of_locIndep_one_card_le_six`:
  > `LocIndep 1 G → |V| ≤ 6 → CloseToBipartite 2 G`** — a new instance of the headline theorem
  > with the **optimal constant `2`** on the class of graphs of order at most `6`, with no
  > hypothesis beyond Erdős's own (no odd girth, no packing weight, no degree bound, no
  > decomposition).  In the `Erdős73On` shape: `JSP90.erdos73On_one_two_of_card_le_six`; in the
  > transversal shape: `JSP90.tauOdd_le_two_of_locIndep_one_card_le_six`.
* **EXACTNESS**: `JSP90.smallOrder_k1_exact` collects the small-order constants at `k = 1` through
  six vertices: `LocIndepOneSmallOrder 1 5`, `¬ LocIndepOneSmallOrder 0 5` (witness `K₃`),
  `LocIndepOneSmallOrder 2 6`, `¬ LocIndepOneSmallOrder 1 6` (witness `sun3`) — so `f(1) = 1` for
  every graph on at most five vertices and `f(1) = 2` for every graph on at most six, and neither
  constant can be lowered.
* **THE REDUCTION ITERATES**: `JSP90.LocIndepOneSmallOrder.iter` — `(m, n) → (m + k, n + k)` — so
  `LocIndepOneSmallOrder 1 5` alone settles every larger order at the cost of one deletion per
  vertex (`LocIndepOneSmallOrder (1 + k) (5 + k)`).  These are the *non-sharp* constants; the sharp
  ones at order seven and beyond are the next target.  The piece form of the six-vertex instance,
  `JSP90.closeToBipartite_two_of_locIndep_one_of_card_le`, is the form a decomposition reads.
* **A REFUTED LEMMA, recorded**: "if `C` is a shortest odd cycle and `|V| ≤ |C| + 1` then every
  vertex of `C` meets every odd cycle" is **false** (with `|V| = 6`, `|C| = 5`, and a second
  `5`-cycle `V \ {v}` for a vertex `v` of `C`, the vertex `v` misses it).  What is proved instead is
  the parity statement `JSP90.card_eq_of_shortest_oddCycle_of_card_le_succ`: with at most one vertex
  outside a shortest odd cycle, **all** odd cycles have the same cardinality.  The six-vertex
  instance needs neither.

`lake build` succeeds (1299 jobs) with **0 `sorry`, 0 `admit`**; `#print axioms` on the theorems
above reports only `[propext, Classical.choice, Quot.sound]`.

**The next order with anything to prove is seven.**  The reduction costs one vertex, so it gives `3`
at seven vertices (`JSP90.closeToBipartite_three_of_locIndep_one_card_le_seven`), whereas the
measurement says `2` suffices there (`r148_n7.log`, all `2097152` graphs on seven vertices) and also
at eight vertices (`r144b_n8.log`, a *complete* search over the `55179262` `LocIndep 1` graphs on
eight vertices: none has `tauOdd ≥ 3`).  So the concrete next target is
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven`.

## Status as of round 46

* `lake build` succeeds (1215 jobs); **0 `sorry`, 0 `admit`** (harness `partial_ok = true`).
* Proved so far:
  * `lean/JSPProblem/Reed.lean` — heredity and monotonicity of `LocIndep`, the clique obstruction
    `|C| ≤ k + 2`, the sharp examples `K_{k+2}` (satisfies) / `K_{k+3}` (fails), the complete **easy
    direction** `G.IsBipartite → LocIndep k G`, `CloseToBipartite 0 G ↔ G.IsBipartite`, and
    monotonicity of the theorem in `k`.
  * `lean/JSPProblem/OddCycle.lean` — the **odd-cycle characterisation of bipartiteness**, which is
    an open `TODO` in Mathlib at the pinned revision, proved here from `SimpleGraph.Walk`
    (`colorable_two_of_even_closed_walks`, `exists_odd_closed_walk_of_not_bipartite`,
    `exists_odd_cycle_inj`, `indep_card_le_of_odd_cycle`), and with it
    **`JSP90.erdos73_zero : Erdős73 0`** — i.e. the complete Erdős #73 theorem for the parameter
    `k = 0`, with the sharp constant `m = 0`.
  * `lean/JSPProblem/Packing.lean` — the **packing half** of the Erdős–Pósa strategy for `k ≥ 1`:
    `LocIndep.oddCycle_packing_le` (at most `k` vertex-disjoint odd cycles) and the counting
    statement `packing_ineq` (`2 * |T| + |C| ≤ |⋃ C|` for independent `T` inside a packing).
* `lean/JSPProblem/Fan.lean` (round 35) — the **local fan argument**, developed from scratch
  (no Mathlib connectivity / Menger / fan API; none of it is in the pinned import slice):
  `exists_arc` / `arc_rev` / `arc_parity` (the two arcs between two vertices of an odd cycle, and
  the fact that exactly one is odd), `arc_isOddCycle` (closing an odd arc through an outside
  vertex gives a *simple odd cycle* — the parity core of the fan argument, by counting),
  `oddCycle_through_fan` (a vertex outside an odd cycle which sees two of its vertices lies on an
  odd cycle of at most `|C|` vertices), `shortArc_of_shortest` (**at a shortest odd cycle of length
  `≥ 5`, the two attachment points of a fan are exactly two steps apart**), and
  `card_inter_neigh_le_two` (**a vertex outside a shortest odd cycle of length `≥ 5` meets it in at
  most two vertices**), instantiated under `LocIndep` by `locIndep_shortest_attach`.
* `lean/JSPProblem/Branch.lean` (round 38) — the **branch-vertex attack family**, a third and
  independent route to the same statement.  Deleting every vertex with three distinct neighbours
  leaves a graph of maximum degree `≤ 2`, whose odd cycles are pairwise disjoint, so there a
  packing bound is a transversal bound.  Proved: the cyclic order of a cycle and its arithmetic
  (`CycleOrder`, `prev_succ`, `exists_iter`, …), the two neighbours of a vertex of a cycle are its
  two cycle-neighbours (`neigh_two_of_not_branch`, `adj_iff_cycle_neigh`), a vertex of an odd
  cycle has no neighbour outside it (`IsOddCycle.neigh_subset`), two odd cycles meeting at a
  vertex are **equal** (`eq_of_mem_inter_of_no_branch`), a maximum packing contains all odd cycles
  (`maxCardFamily_eq_all_oddCycles`), one vertex per cycle is a transversal
  (`hitsOddCycles_onePerCycle`), hence **Erdős–Pósa for odd cycles in graphs without branch
  vertices with the optimal function `r ↦ r`** (`closeToBipartite_of_no_branch`), and two **new
  instances of the headline theorem**: `erdos73On_of_bounded_branch` and
  `erdos73On_of_few_high_degree` (if all vertices of degree `≥ 3` lie in a set of at most `m`
  vertices, then `LocIndep k G` forces `CloseToBipartite (m + k) G`, with **no bound on the odd
  girth**),   plus `erdos73On_of_no_branch` (the case `m = 0`).
* `lean/JSPProblem/Sharp.lean` (round 39) — the **optimality** family, a fourth and independent
  attack family: the graph `kTriangles k` = `K_3 ⊔ ... ⊔ K_3` (`k` copies) on `Fin 3 × Fin k` makes
  the constant of Erdős #73 as large as it can be.  Proved: `isOddCycle_tri` (each fibre is an odd
  cycle), `locIndep_kTriangles` (**`LocIndep k` holds, with equality** `2 * k + k = 3 * k = |V|`),
  `card_le_of_hitsOddCycles_kTriangles` (every set meeting every odd cycle has `≥ k` elements),
  hence `closeToBipartite_iff : CloseToBipartite m (kTriangles k) ↔ k ≤ m` — the *exact* value of
  the conclusion on this graph; `not_locIndep_kTriangles` (the hypothesis is sharp too:
  `LocIndep (k - 1)` fails for `k ≥ 1`); `not_branch_kTriangles` and `not_branch_completeGraph_three`
  (no branch vertices); and, as corollaries in the shape of the theorem itself,
  **`erdos73_lower_bound` / `no_constant_below_k` = the lower bound `f(k) ≥ k` of Erdős #73** and
  `erdos73On_no_branch_optimal` = **sharpness of the round-38 instance `erdos73On_of_no_branch`
  (on the class of graphs of maximum degree `≤ 2` the value of `f(k)` is exactly `k`)**.
  `packing_kTriangles_optimal` shows the *packing* bound of `JSPProblem/Packing.lean` is attained
  on the same witness (`k` disjoint odd cycles, and no more).
* **A new instance of the headline theorem** (`JSPProblem/Residue.lean`): if any two odd cycles of `G`
  meet and `G` has an odd cycle of at most `ℓ` vertices, then `LocIndep k G` forces
  `CloseToBipartite ℓ G` — for every `k`, with a constant independent of `k`
  (`erdos73On_of_packing_one`).  This class is not covered by the earlier instances: the
  bounded-odd-girth instance only gives `ℓ · k`, and the branch-vertex instances do not apply
  (`K_5` has packing number one and is full of branch vertices).
* `lean/JSPProblem/Residue.lean` (round 40) — the **global half of the classical Erdős–Pósa
  reduction**: the residue `G - C` of a packed odd cycle.  `LocIndep.of_deleteFinset` (the local
  hypothesis is inherited by a residue), `card_add_one_le_of_mem_maxPacking` and
  `LocIndep.oddCycle_packing_residue_lt` (a packing of the residue together with the cycle is a
  packing of `G`, so the residue's packing number is at most `k - 1` — the strictly decreasing
  quantity of the classical induction), `residue_hits_rest` (every odd cycle of the residue meets one
  of the *other* members of a maximum packing), and the induction step itself
  `hitsOddCycles_union_cycle` / `closeToBipartite_of_residue`
  (`CloseToBipartite q (G - C) → CloseToBipartite (q + |C|) G`).  **The `+|C|` is exactly where the
  argument stops** — the absorption step of Reed–Robertson–Seymour–Thomas.  The file also proves the
  case of **packing number one** in full (`packing_one_residue_bipartite`,
  `closeToBipartite_of_packing_one`, `erdos73On_of_packing_one`) and introduces the minimum
  transversal machinery (`IsMinimalTransversal`, `exists_minimalTransversal`,
  `exists_minimalTransversal_of_transversal`, `exists_private_oddCycle`: every vertex of a minimum
  transversal lies *alone* on an odd cycle).
* `lean/JSPProblem/Chord.lean` (round 40) — the arc machinery of `JSPProblem/Fan.lean` **generalised
  so that the vertex closing an arc may lie on the cycle**, which is what a chord needs
  (`arcFun_inj_of_notMem`, `arc_card_of_notMem`, `arc_isOddCycle_of_notMem`, whose hypothesis is
  only that the closing vertex avoids the *arc*).  Hence
  **`no_chord_of_shortest_oddCycle`**: a shortest odd cycle of `G` is **chordless** (a chord splits
  it into two cycles whose lengths add up to the odd number `m + 2`, so exactly one of them is odd,
  and it has at most `m - 1` vertices — contradicting minimality), and therefore
  **`induceFinset_adj_of_shortest` / `isInduced_shortest_oddCycle`**: the subgraph induced by a
  shortest odd cycle *is* that cycle, `(induceFinset G C).Adj (f a) (f b) ↔ a = cycSucc b ∨
  b = cycSucc a`.  `exists_shortest_oddCycle` proves that a shortest odd cycle exists whenever `G`
  has one.  Together with `card_inter_neigh_le_two` of `JSPProblem/Fan.lean` (a vertex outside a
  shortest odd cycle of length `≥ 5` meets it in at most two vertices, two steps apart) this is the
  **complete local structure of `G` at a shortest odd cycle** — the base case of every induction in
  the classical argument.
* `lean/JSPProblem/Separator.lean` (round 42) — the **2-cut decomposition**, the first *global*
  structural tool of this development and the backbone of every classical proof of Erdős–Pósa for
  odd cycles.  A split `V(G) = {a, b} ⊔ T₁ ⊔ … ⊔ T_t` with the parts pairwise anticomplete
  (`VertexSplit`, i.e. "`{a,b}` is a vertex cut") is formalised without any connectivity API:
  - `VertexSplit.cycle_subset_parts` — **a cycle of `G` avoiding the two vertices of the cut lies in
    a single part**; `oddCycle_piece_or_avoid` — every odd cycle is contained in a *piece*
    `T_i ∪ {a,b}` or meets the cut; `part_unique` / `oddCycle_piece_unique` — the piece is
    **unique**;
  - `VertexSplit.hitsOddCycles` / `exists_transversal` / **`erdos73On_of_split`** — transversals and
    the conclusion of Erdős #73 are **additive over a 2-cut**: if `LocIndep k` forces
    `CloseToBipartite m` on every piece, it forces `CloseToBipartite (m * t + 2)` on `G`.  This is
    a **new instance of the headline theorem** and the reduction "the theorem reduces to the
    3-connected case";
  - `VertexSplit.isBipartite_of_split` / `not_isBipartite_of_split` — the **2-cut parity lemma**: if
    every piece is bipartite and the two vertices of the cut carry the same colour in every piece,
    then `G` is bipartite (so a non-bipartite `G` cannot be 2-coloured with `a`, `b` agreeing);
  - `packing_le_of_split` — the packing half: the Erdős–Pósa hypothesis restricts to the pieces;
  - **`erdos73On_of_split_of_bounded_branch`** — a **second new instance of the headline theorem**,
    the composition with the round-38 branch-vertex instance: a 2-cut whose `t` pieces have at most
    `m` branch vertices each gives `CloseToBipartite (2 + (m + k) * t)`, with no bound on the odd
    girth.
* `lean/JSPProblem/Count.lean` (round 43) — the **counting half of the 2-cut decomposition**, and the
  round that removes the number of pieces from the constant of round 42.  Two of the gaps named by
  round 42 are closed, and a strictly stronger instance of the headline theorem is the result:
  - **`VertexSplit.cycle_subset_piece_of_not_mem`** — **a cycle which contains `a` but not `b` lies
    in a single half-piece `T_i ∪ {a}`** (and symmetrically for `b`), proved by walking around the
    cycle from the vertex after `a` along the cyclic order of `JSPProblem/Branch.lean`;
    `VertexSplit.oddCycle_half_or_both` then gives the **complete local structure at a 2-cut**: an
    odd cycle is local to a half-piece, or uses *both* vertices of the cut;
  - **`VertexSplit.card_nonBipartiteParts_le`** — **the counting lemma**: under `LocIndep k G`, at
    most `k` of the `t` parts of a split are non-bipartite, since each non-bipartite part carries an
    odd cycle and the parts are pairwise disjoint, so they form a packing of `G`;
  - **`VertexSplit.exists_transversal_nonBipartite`** and
    **`erdos73On_of_split_of_bounded_pieces`** — **a new instance of the headline theorem, strictly
    stronger than round 42's `erdos73On_of_split`**: if `LocIndep k` forces `CloseToBipartite m` in
    every piece `T_i ∪ {a,b}` of a 2-cut, then it forces `CloseToBipartite (2 + m * k) G`.  The
    constant no longer depends on the number `t` of pieces (round 42: `2 + m * t`), and no bound on
    the odd girth is used.  `erdos73On_of_split_of_bounded_branch_packing` is the same improvement
    for the composition with the branch-vertex instance (`2 + (m + k) * k`);
  - **`packing_le_of_split_decomposition`** — **the full packing decomposition**: if every packing of
    odd cycles of every part `T_i` has at most `r` members, then every packing of odd cycles of `G`
    has at most `2 + t * r` members.  This is the direction round 42 named as missing (a packing of
    `G` splits into at most two members meeting the cut, and one packing per part);
* **The precise reduction.**  The same file defines `HasProperSplit` / `NoProperSplit` / `SplitDepth`
  (the length of a chain of successive 2-cuts), the explicit bound `splitBound m p d`, and proves
  **`erdos73_of_noSplit2_of_bounded_splitDepth`**: *Erdős–Pósa for odd cycles follows from the
  2-cut-free case together with a uniform bound on the number of 2-cuts of `G`*.  Since
  `erdos73_of_erdosPosa` is proved, `jsp_000090_main` therefore reduces to exactly two statements,
  and all the rest of the classical argument (the local structure at a shortest odd cycle, the
  residue induction, the 2-cut decomposition and its counting half) is proved and enters only through
  those two hypotheses.  The bound on the number of 2-cuts (the Mader / Reed–Robertson–Seymour–Thomas
  structure step) is the single concrete missing lemma.
* `JSPProblem/Weight.lean` (round 44) — the **weighted Erdős–Pósa theorem**, a sixth and independent
  attack family: the residue induction of `JSPProblem/Residue.lean` run to *exhaustion*, with the
  running total `|C₁| + |C₂| + …` of the packed odd cycles as the induction parameter.
  - `PackingWeight 𝒞 = ∑ C ∈ 𝒞, |C|` and `WeightLe G L` — the **weight** of a packing (the total
    number of vertices it covers) and the hypothesis that it is bounded;
  - `insert_oddCycle_of_disjoint` — a packing together with an odd cycle disjoint from all of its
    members is a packing, i.e. the *weight* version of `insert_oddCycle_of_delete`;
  - **`closeToBipartite_of_weightLe` — THE WEIGHTED ERDŐS–PÓSA THEOREM: if every packing of odd
    cycles of `G` covers at most `L` vertices in total, then `G` is the union of a bipartite graph and
    `L` vertices.**  Strong induction on `L`: the residue of an odd cycle inherits the bound
    `L − |C|` (a packing of the residue together with `C` is a packing of `G`), and
    `closeToBipartite_of_residue` closes the step.  This is **strictly more general** than round 40's
    `shortOddCycles_transversal`, which needs a bound on the length of *every* odd cycle: only the
    *total* length of a packing is controlled here;
  - `IsMaxWeightPacking`, `exists_maxWeightPacking`, `closeToBipartite_of_maxWeightPacking` —
    **the odd cycle transversal number of `G` is at most the weight of a maximum-weight packing of
    odd cycles**, and a maximum-weight packing exists;
  - `hitsOddCycles_of_maxWeightFamily` and **`isBipartite_delete_of_maxWeightFamily` — the residue of
    a maximum-weight packing is bipartite** (an odd cycle of the residue is disjoint from every
    member, so it could be added and would increase the weight): the structural content of the
    weighted argument, in the vocabulary of maximum-*cardinality* packings proved in round 40;
  - `packingWeight_le` and **`erdos73On_of_bounded_packing_weight` — a new instance of the headline
    theorem, for the class of graphs of bounded *packing weight***: `LocIndep k G` together with a
    uniform bound on the total length of a packing of odd cycles forces `CloseToBipartite L G`.  The
    hypothesis is strictly weaker than bounded odd girth: no bound on the odd girth and none on the
    number of branch vertices; `erdos73On_of_bounded_odd_circumference` re-derives the `ℓ * k`
    instance as a corollary;
  - `closeToBipartite_iff_completeGraph_add_two` — **on complete graphs the conclusion of Erdős #73
    is exact**, `CloseToBipartite m (K_n) ↔ n ≤ m + 2` — and `erdos73On_completeGraph`, the
    resulting instance in which the value of Erdős's constant on the class of complete graphs is
    exactly `k` (a second witness, besides `kTriangles`, for `f(k) ≥ k`);
  - **`absorption_step_fails` — THE NAIVE `+ 1` ABSORPTION STEP IS FALSE, machine-checked with the
    witness `K_5`.**  For `G = K_5` and the triangle `C = {0,1,2}` the residue `G − C = K_2` is
    bipartite, so `CloseToBipartite 0 (G − C)` holds
    (`closeToBipartite_zero_deleteFinset_completeGraph_five`), but `K_5` is not `1`-close to
    bipartite (`not_closeToBipartite_one_completeGraph_five`); and `LocIndep 3 (K_5)` holds
    (`locIndep_completeGraph_five_three`), so the failure is *inside* the range of the headline
    theorem.  The cause is visible in the witness: in `K_5` every vertex outside `C` meets the
    triangle in all three of its vertices, whereas at a shortest odd cycle of length `≥ 5` an outside
    vertex meets the cycle in at most **two** of its vertices, two steps apart
    (`JSPProblem.card_inter_neigh_le_two`, `JSPProblem.shortArc_of_shortest` in
    `JSPProblem/Fan.lean`).  So the `+|C|` of `closeToBipartite_of_residue` **cannot** be replaced by
    `+1` without a hypothesis coming from the local structure at a shortest odd cycle: this is the
    concrete form of the blocker below, and it rules out one family of candidate proofs for
    future rounds.
* `JSPProblem/Optimal.lean` (round 46) — the **identity case of Erdős–Pósa, proved and sharp**,
  a seventh and independent attack family, and the first one that attacks the problem from the
  *sharpness* side rather than from a structural hypothesis:
  - `OddCyclesDisjoint G` — the class in which **any two distinct odd cycles of `G` are
    vertex-disjoint** (a hypothesis about the intersection pattern of the odd cycles alone: no
    degree bound, no length bound, no counting bound);
  - `erdos73On_of_disjoint_oddCycles` — **a new instance of the headline theorem with the OPTIMAL
    constant `f(k) = k`**: `LocIndep k G` + `OddCyclesDisjoint G` ⟹ `CloseToBipartite k G`.  No
    extra parameter, no bound on the odd girth, no bound on the number of branch vertices.  The
    content is the *equivalence* `closeToBipartite_iff_packingLe`: on this class the least odd
    cycle transversal and the largest odd cycle packing **are the same number** (one vertex per
    member of a maximum packing is a transversal, and any transversal is as large as a packing —
    `exists_transversal_onePerMember`, `card_le_of_hitsOddCycles_of_disjointFamily`,
    `mem_of_oddCycle_of_maxPacking`);
  - `erdos73On_disjoint_oddCycles_iff` — **the class is exactly as hard as the general theorem as
    far as the constant is concerned**: the least `m` for which Erdős #73 holds for every `G` of
    the class satisfying `LocIndep k` is exactly `k` (witness `kTriangles k`, whose odd cycles are
    exactly its `k` fibres — `oddCycle_eq_tri_of_kTriangles`, `oddCyclesDisjoint_kTriangles`);
  - `closeToBipartite_of_anticover` — **the composition lemma missing from all earlier rounds**:
    the conclusion of Erdős #73 is *additive over an anticomplete decomposition* of the vertex
    set (`Anticover`: the two sides are disjoint, cover `V`, and no edge joins them), so the
    instances compose.  Rounds 42–43 compose along 2-cuts, where the two sides share the two cut
    vertices and the constant pays an extra `2`; here the sides share nothing;
  - `class_hypothesis_is_necessary` and `packingNumber_one_not_enough` — **machine-checked
    negative results**: `LocIndep 3 (K_5)` holds and every packing of odd cycles of `K_5` has at
    most one member, yet `K_5` is not `2`-close to bipartite.  The single reason is
    `not_oddCyclesDisjoint_completeGraph_five`: the triangle `{0,1,2}` and the Hamiltonian
    `5`-cycle `0-1-2-3-4-0` share the two vertices `0` and `1`.  So the identity function does
    *not* extend beyond the class, and a packing bound alone does not give the conclusion — the
    same `K_5` obstruction already recorded for absorption in `JSPProblem/Weight.lean`, now seen as
    a statement about the Erdős–Pósa function itself.
* **Not proved:** Erdős #73 for `k ≥ 1`. After the packing bound, the remaining content is exactly
  "a bounded odd-cycle packing number forces a bounded odd cycle transversal", i.e. the
  **Erdős–Pósa theorem for odd cycles** (Reed–Robertson–Seymour–Thomas, *JCTA-B* 2003); it is named
  as the blocker in `discovery/JSP-000090/policy.json`.  **Round 42 localises it precisely**:
  `erdos73On_of_split` shows the theorem is closed under 2-cut decomposition and
  `not_isBipartite_of_split` shows that a non-bipartite graph is glued along its 2-cuts only, so an
  induction on the Erdős–Pósa function may restrict to graphs with **no proper 2-cut** — the
  3-connected case, which is the one still untreated here (Mader's 3-connected structure of a
  shortest odd cycle and a Menger-type lemma are both absent from the pinned Mathlib).  **Round 44
  adds the machine-checked negative result** that the naive `+1` absorption step is false even
  inside the range of the theorem (`JSP90.absorption_step_fails`, witness `K_5` and the triangle
  `{0,1,2}`), so any absorption lemma must be conditional on the local structure at a shortest odd
  cycle (a vertex outside a cycle of length `≥ 5` meets it in at most two vertices, two steps apart);
  and it adds the weighted Erdős–Pósa theorem, which bounds the transversal by the total length of a
  maximum-weight packing.  **Round 46 adds the identity case of the Erdős–Pósa function itself**,
  proved and sharp on the class of graphs whose odd cycles are pairwise vertex-disjoint, together
  with the machine-checked negative result that this case does *not* extend to graphs in which two
  odd cycles share two vertices (`K_5`), and the anticomplete-composition lemma.  **Round 47 adds the eighth attack family, `JSPProblem/Additive.lean` (43 declarations, 0
  sorry) — *strong additivity over anticomplete decompositions*, in both directions**, and with it
  a new instance of the headline theorem along the **connectivity** axis:
  - `isOddCycle_sub_anticover` and `isOddCycle_sub_anticoverIn` — **a cycle never crosses an
    anticomplete split**: consecutive vertices of a cycle are adjacent, hence on the same side, and
    the predicate "`x ∈ A`" is preserved by the cyclic successor, so it holds at one vertex of the
    cycle iff it holds at all of them;
  - `closeToBipartite_iff_add_anticover` and `closeToBipartite_of_anticover_restrict` — the
    conclusion is **exactly additive** over an anticomplete split: the budget `m₁ + m₂` works for
    `G` **iff** it splits between the two sides, and a budget for `G` restricts to both sides.  So
    the odd cycle transversal number of `G` lies between `max(m₁, m₂)` and `m₁ + m₂` for the two
    sides of every anticomplete split;
  - `closeToBipartite_of_anticoverFamily_cost` — **strong additivity over a family** of pairwise
    disjoint, pairwise anticomplete pieces, with **no `+2`** (the two sides of a 2-cut share the two
    cut vertices, so round 43's composition has to pay for them; here the sides share nothing);
  - `card_le_of_pieces`, `card_nonBipartiteParts_le` and `card_nonBipartiteParts_le_cover` — the
    **counting lemma**: under `LocIndep k G`, at most `k` pieces of an anticomplete family (or
    cover) induce a non-bipartite graph, because those pieces carry odd cycles and are disjoint;
  - **`erdos73On_of_anticover_decomposition` — a new instance of the headline theorem**: if the
    vertices of `G` are partitioned into pairwise anticomplete pieces (the shape of the connected
    components) and every *non-bipartite* piece is `m`-close to bipartite, then `LocIndep k G`
    forces `CloseToBipartite (k * m) G` — a constant **independent of the number of pieces**, with
    no bound on the odd girth, packing weight or number of branch vertices;
  - **two machine-checked negative results**, recorded in the header of the file: an anticomplete
    **cover** is *not* enough for the composition (a cover says nothing about the edges from a piece
    to the vertices outside the union, so the union and its complement need not be an
    `Anticover`), which is why the instance is stated for `AnticoverDecomposition`; and therefore
    the union of a **maximal family of pieces is not a transversal** — an odd cycle missing the
    union generally has edges to the union and so cannot be added as a new piece.  Four theorems of
    that maximal-family route were written and then deleted as unprovable;
  - the next step this enables is explicit: instantiate the new instance with the family of
    **connected components** (`Reachable`, `SimpleGraph.ConnectedComponent` and `C.supp` all exist
    at the pinned revision; the missing lemma is the finset-level statement that
    `univ.filter (fun w => G.Reachable v w)` is an `AnticoverDecomposition`), which is the
    classical reduction of Erdős–Pósa to connected — then 2-connected, then 3-connected — graphs.

  `jsp_000090_main`
  is therefore deliberately
  **not** declared, so that the harness keeps reporting
  `missing_theorems = ["jsp_000090_main"]`. Declaring a weaker theorem under that name would
  misrepresent the result.

---

## Round 68 — `JSPProblem/Triangle.lean`: **Erdős #73 is EQUIVALENT to its triangle-free case**

New file `lean/JSPProblem/Triangle.lean` (19 declarations, 0 sorry/admit, `lake build` OK with 1225
jobs), imported from the root module `JSPProblem.lean`.  This is the **eighteenth attack family**,
and it *closes* one of the two statements that round 64 left open, leaving a single one.

### The gap that is closed

Round 64 reduced Erdős #73 to **two** statements — `JSP90.TriangleFreeErdős73` (the triangle-free
case) and `JSP90.CutTriangleErdős73` (near a triangle, either the graph cuts there or it is
`O_k(1)`-close to bipartite) — because the only instance of the headline theorem at a triangle then
available was `JSP90.closeToBipartite_of_cutTriangle`, which needs the hypothesis
`JSP90.CutTriangle G T` (*no edge from the triangle to the rest of the graph*).  `K_4` shows that
hypothesis is not automatic, and a `C_5` with a hub and a pendant edge (deficiency `1`, not
bipartite, no cut triangle) shows the alternative is a genuine case distinction, not a theorem.

**Neither the hypothesis nor the alternative is needed.**  Two facts do all the work, and both were
already available but had not been put together:

* **the descent needs only disjointness.**  `JSP90.maxDefIn_ge_one_add_maxDefIn_of_clique`
  (`JSPProblem/Cut.lean`) asks for `Disjoint U T` and nothing else — no separation, no cut.  Round 59
  had to assume *separation* from an odd cycle; round 64 had to assume the cut.  Repackaged here as
  `JSP90.maxDefIn_add_one_le_maxDef_of_triangle` and
  `JSP90.locIndep_of_disjoint_triangle`: *every vertex set disjoint from a triangle inherits Erdős's
  hypothesis with the parameter dropped by one*;
* **the composition needs no condition on the edges from `T` to the pieces.**  The third field of
  `JSP90.AnticoverCut` is used, in the proof of `JSP90.closeToBipartite_of_anticoverCut`, only to
  feed an `Anticover` structure to `JSP90.closeToBipartite_of_anticover`.  That recombination is
  avoidable: the residue `G[V \ (T ∪ Z)]` is bipartite outright, because an odd cycle of `G`
  avoiding `T` and covered by pairwise anticomplete pieces lies in a **single** piece
  (`JSP90.isOddCycle_sub_anticoverCover`) and contradicts that piece's bipartiteness.

### What is proved

* `JSP90.maxDefIn_add_one_le_maxDef_of_triangle`, `JSP90.maxDef_add_one_le_maxDef_of_triangle`,
  **`JSP90.locIndep_of_disjoint_triangle`** — the descent at a triangle, with **no** separation and
  **no** cut hypothesis;
* `JSP90.maxDefIn_add_card_le_maxDef_add_two_of_clique` — the general form, *a clique of size `t`
  costs `t − 2` units of deficiency off any disjoint vertex set* (this contains
  `JSP90.maxDef_allNeighOf_le` of round 65 and explains why the completion sets of a clique are free);
* **`JSP90.closeToBipartite_of_pieces`** — a **new instance of the headline theorem**: a `3`-vertex
  set `T` with a pairwise-disjoint, pairwise-anticomplete cover `𝒬` of `V \ T`, every piece
  `m`-close to bipartite ⟹ `LocIndep k G → CloseToBipartite (3 + k * m) G`.  The anticompleteness
  of the pieces to `T` of rounds 63–64 is **dropped**, and so is the disjointness of the pieces
  from `T`, and `T` need not even be a clique;
* `JSP90.closeToBipartite_of_triangle` — the same instance at the **canonical** family of pieces
  (the connected components of `G − T`) and at an **arbitrary** triangle: no `JSP90.CutTriangle`
  hypothesis, constant `3 + k * m` independent of the number of components, no bound on the odd
  girth, packing weight or number of branch vertices;
* `JSP90.locIndep_piece_of_triangle` — every component of `G − T` satisfies `LocIndep (k − 1)`, the
  induction step of the classical proof at a triangle;
* **`JSP90.TriangleFreeOnly`, `JSP90.erdos73On_of_triangleFreeOnly`,
  `JSP90.erdos73_of_triangleFreeOnly`** — Erdős #73 **in full**, with the constant `cutBound` of
  round 64, from the triangle-free case **alone**; the induction is on `k` and at a triangle takes
  the components of `G − T`, which are anticomplete with no hypothesis at all;
* **`JSP90.erdos73_iff_triangleFreeOnly`** — **Erdős Problem #73 is equivalent to Erdős #73 for
  triangle-free graphs** (`(∀ k, Erdős73On k (cutBound k)) ↔ TriangleFreeOnly`);
* **`JSP90.cutTriangleErdős73_of_triangleFreeOnly`** — round 64's second statement is now a
  **theorem**, not a hypothesis, and `JSP90.erdos73_of_triangleFreeErdos73` is round 64's
  `JSP90.erdos73_of_triangleFree` with the `CutTriangleErdős73` argument deleted;
* **`JSP90.descent_tight`** — the descent is **tight**: on the sharp witness `kTriangles k` (deficiency
  exactly `k`) a single triangle is disjoint from a vertex set of deficiency exactly `k − 1`, so the
  induction really drops by exactly one unit per triangle and `cutBound` is not an artefact
  (with `JSP90.card_le_kTriangles_avoid`, the `α`-count behind it).

### What is *not* proved

`JSP90.TriangleFreeOnly` — Erdős #73 for triangle-free graphs, constant `cutBound`.  It is a
statement about a *class* of graphs, and it is now the **whole** remaining content of JSP-000090
(rounds 64–65 named two statements; there is one).  Behind it stands
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), still the primary blocker.

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

### Round 48 — `JSPProblem/Connect.lean`: the connectivity and 1-cut reductions

Round 47 named the next step: instantiate the new instance with the family of **connected
components**.  Round 48 carries that out and then continues along the same axis to the **1-cut**
(a cut at a *single* vertex), so that the classical chain *connected → 2-connected → 3-connected*
is formal.  New file `JSPProblem/Connect.lean` (64 declarations, 1183 lines, **0 sorry**,
`lake build` OK).

Proved:

  - `compPiece G v = (univ).filter (G.Reachable v)`, `compPieces G = (univ).image compPiece`, and
    **`anticoverDecomposition_compPieces`**: the connected components of `G` are pairwise disjoint,
    pairwise anticomplete, cover `V`, and anticomplete to the complement of their union — the
    hypothesis of round 47's instance, which a mere *cover* does not give.  This is the first use of
    Mathlib's connectivity API (`SimpleGraph.Reachable`) in this development;
  - **`card_le_of_pieces_pack`** — the counting lemma for a family of pieces indexed by an
    *arbitrary type* (the parts of a 1-cut are indexed by `Fin t`, not by `Finset V`) — and
    **`oddCycleErdosPosa_of_anticover_decomposition`** — round 47's instance restated with the
    *packing number* in place of the `LocIndep` parameter, i.e. in the form in which the research
    statement `OddCycleErdosPosa r` is phrased;
  - **`erdos73On_of_connected_components` — a new instance of the headline theorem**: if every
    connected component of `G` is `m`-close to bipartite then `LocIndep k G` forces
    `CloseToBipartite (k * m) G`, a constant independent of the number of components and with no
    bound on the odd girth, packing weight or number of branch vertices;
  - `PieceErdős73On`, **`erdos73On_of_piece`** and **`erdos73_of_erdos73_piece` — the connectivity
    reduction**: if a constant `m` works for *connected pieces* — `PiecePreconnected G s` says any
    two vertices of `s` are joined by a path of `G`, and for `s = V` this is `G.Preconnected`
    (`PiecePreconnected.univ`) — then the constant `k * m` works for all graphs;
  - `PieceOddCycleErdosPosa`, **`oddCycleErdosPosa_of_piece`** (bound `r * m`) and
    **`erdos73_of_connected_erdosPosa`**: the same reduction for the **research statement** — so
    `jsp_000090_main` now follows from the *connected-piece* case of Erdős–Pósa for odd cycles, a
    strictly weaker and precisely stated missing lemma;
  - `OneSplit G v t` — a **1-cut** `V = {v} ⊔ T₁ ⊔ … ⊔ T_t` (the counterpart of
    `JSPProblem.Separator.VertexSplit`, a 2-cut), with `cycle_subset_part` / `oddCycle_part_or_hit`
    (a cycle avoiding the cut vertex lies in a single part),
    **`isBipartite_of_bipartite_pieces`** and **`isBipartite_iff_bipartite_pieces`** — the **1-sum
    lemma**, `G` is bipartite **iff** every *piece* `T_i ∪ {v}` is bipartite — plus
    `one_nonBipartitePiece`, `card_nonBipartiteParts_le` and `exists_transversal_nonBipartite`
    (a transversal of size `1 + ∑` over the non-bipartite parts);
  - **`erdos73On_of_1split_of_bounded_pieces` — a second new instance of the headline theorem**, with
    the constant `1 + m * k`.  A 1-cut shares a *single* vertex with each of its pieces, so this
    **improves** on round 43's 2-cut instance `2 + m * k`, and it is again independent of the
    number of parts;
  - **`erdos73On_of_1split_pieces`**: chains the two reductions — the classical step
    *connected → 2-connected*;
  - `HasProper1Split`, `NoProper1Split`, `OneDepth` (with `oneDepth_succ`, `oneDepth_add`,
    `oneDepth_mono`), `oneBound` and
    **`oddCycleErdosPosa_of_noOneCut_of_bounded_oneDepth`** — the precise reduction along the 1-cut
    axis, the 1-cut analogue of round 43's `erdos73_of_noSplit2_of_bounded_splitDepth`: Erdős–Pósa
    for odd cycles follows from the **1-cut-free case** together with a uniform bound on the number
    of successive 1-cuts.

Two **negative results** were found and recorded (in the file's docstrings; the concrete witness —
a triangle with a pendant vertex, cut at the triangle vertex carrying the pendant — is *not* yet
machine-checked):

  1. "*a non-bipartite graph with a 1-cut has **at least two** non-bipartite pieces*" is **false**:
     in that example both *parts* are bipartite and `G` is not.  The proved statement is
     `one_nonBipartitePiece` (at least one);
  2. consequently "*all parts bipartite ⟹ `G` bipartite*" is **false** — which is why the
     **pieces** `T_i ∪ {v}`, and not the parts, are the right objects of the decomposition.

The remaining gap is therefore now stated twice, and both statements are proved reductions:

  - it suffices to prove `PieceOddCycleErdosPosa r` for every `r` (its `s = V` case being the
    connected case);
  - and it suffices to prove it for graphs with **no proper 1-cut**, provided the **block-cut tree
    bound** `oneDepth_le_of_packing`: every graph whose odd cycle packings have at most `r` members
    satisfies `OneDepth G (2 * r + 1)` — i.e. a chain of cut vertices of length `2r + 2` forces
    `r + 1` pairwise disjoint odd cycles.  This is the one missing lemma; it is not proved here
    because the naive induction step is refuted by negative result 1 and the correct argument needs
    the block-cut tree, which the pinned Mathlib slice does not provide (no `SimpleGraph.Block`, no
    Menger, no `Connectivity.lean`).

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.

`formalization.yaml` remains `status: wip`, `prize_ready: false`. No award claim is made.

---

## Round 53 — the tenth attack family: minimal transversals and critical cycles

New file `lean/JSPProblem/Critical.lean` (25 declarations, 0 placeholders), imported from the root
module `JSPProblem.lean`.  Rounds 43–48 attacked the *decomposition* axes of the classical proof
(components, 1-cuts, 2-cuts).  This round works **inside a single graph**, on the transversal itself,
and never decomposes.

### What is proved

* `exists_criticalCycle_of_minimal`, `exists_criticalTransversal_of_minimal` — **critical cycles**:
  if `X` is a *minimal* odd cycle transversal and `x ∈ X`, there is an odd cycle of `G` meeting `X`
  exactly in `x` (because `X \ {x}` is not a transversal and every odd cycle meets `X`).  This is
  the classical first step of the Reed–Robertson–Seymour–Thomas proof of Erdős–Pósa for odd cycles.
* `CriticalTransversal`, `IntGraph`, `disjoint_of_colour_eq` — the **critical intersection graph**
  (vertices `x ∈ X`, edge when the critical cycles of `x` and `y` meet).  Inside one colour class the
  critical cycles are pairwise vertex-disjoint.
* **`card_X_le_of_colouring_pack`** — the counting lemma: a `c`-colourable critical intersection
  graph plus a packing bound `k` gives `|X| ≤ c * k`.  No bound on the odd girth, on the lengths of
  the critical cycles, on the packing weight, or on the connectivity of `G`.
* **New instances of the headline theorem**
  * `erdos73On_of_spread_transversal (c k)`: a graph admitting a `c`-spread transversal satisfies
    `LocIndep k G → CloseToBipartite (c * k) G`;
  * `erdos73On_of_disjoint_transversal` (`c = 1`, equivalently `erdos73On_of_spread_transversal_one`):
    `LocIndep k G → CloseToBipartite k G`, the **optimal** constant `f(k) = k`, a strict
    generalisation of round 38's `erdos73On_of_no_branch`.
* `packing_of_disjoint_transversal`, `card_le_of_disjoint_transversal` — for a 1-spread transversal
  the critical cycles are also a packing of the same size: on that class of graphs the odd cycle
  packing number and the odd cycle transversal number coincide.
* **New localisation of the missing lemma**: `SpreadMinimalTransversal r c`,
  `oddCycleErdosPosa_of_spreadMinimalTransversal` (constant `c * r`) and
  **`erdos73_of_spreadMinimalTransversal`**: the whole of Erdős Problem #73 follows as soon as every
  graph of odd cycle packing number at most `r` admits a *minimal* odd cycle transversal whose
  critical intersection graph is `r`-colourable.  For `c = 2` this is the classical shape of the
  Reed–Robertson–Seymour–Thomas theorem (a transversal of size at most twice the packing number).
  This replaces the block-cut-tree formulation of round 48 by a statement needing no tree.

### What is *not* proved

The K_4 counterexample showing that `c = 1` is not always available (`{0,1}` is a minimal
transversal of `K_4` whose critical cycles `{0,2,3}` and `{1,2,3}` meet in `{2,3}`) was written but
did not elaborate: the statements of `IsOddCycle` and `HitsOddCycles` are elaborated in
`Transversal.lean` with `Classical.decEq V`, and that instance is baked into the definitions, so at a
concrete vertex type every `Finset (Fin 4)` literal must use it — and in that scope `decide` and
`simp` can no longer evaluate `Fin` equalities.  The claim is recorded in the file header as a
documented observation, and the exact recipe (Weight.lean-style triangle construction with
`Fin.ext` + `omega`) is in `discovery/JSP-000090/policy.json`.

### Harness layout (this round)

`harness/score.py` runs `lake build` in the **problem** directory, while the Lake package lived in
`problems/JSP-000090/lean/`; `build_ok` was therefore `false` in all 52 previous rounds and
`partial_ok` was unreachable at the harness level.  As in `problems/JSP-000087`, a top-level
`lakefile.lean` (`lean_lib JSPProblem where srcDir := "lean"`), a `.lake -> lean/.lake` symlink and
copies of `lake-manifest.json` / `lean-toolchain` were added.  `score.py` now reports

    build_ok = true,  sorry = 0,  admit = 0,  partial_ok = true,
    missing_theorems = ["jsp_000090_main"]

so the only remaining obstruction to `prize_ready` is the mathematics.  `jsp_000090_main` is still
**not** declared, and `formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award
claim is made.

---

## Round 54 — `JSPProblem/Deficiency.lean`: the maximum deficiency, the *numerical* form of Erdős's hypothesis

New file `lean/JSPProblem/Deficiency.lean` (55 declarations, 882 lines, **0 sorry**, `lake build` OK
with 1219 jobs), imported from the root module `JSPProblem.lean`.  This is the **eleventh attack
family**.  Rounds 40–48 attacked the *decomposition* axes (residues, 2-cuts, components, 1-cuts) and
rounds 46/53 attacked the Erdős–Pósa *function* (the identity case; minimal transversals).  All of them
consume the hypothesis `LocIndep k G` in the same single way — to bound the number of vertex-disjoint
odd cycles — and all of them are blocked by the same statement.  Round 54 changes the **hypothesis
itself**: `LocIndep k G` is a `∀ ∃` statement over all vertex sets, and it is replaced by a *number*.

### The new quantity

```lean
MaxDef G = max { |X| - 2 * α(G[X]) : X ⊆ V }
```

— the *maximum deficiency* of `G`, where `|H| - 2 α(H)` is the classical deficiency of `H` (0 on a
bipartite `H`, 1 on an odd cycle, `|H| - 2` on a clique).  Reed's condition "every subgraph `H` has
`α(H) ≥ (|H| - k) / 2`" says exactly that `G` has deficiency at most `k`.

### What is proved

* **`JSP90.locIndep_iff_maxDef_le` — THE REFORMULATION OF THE HYPOTHESIS.**
  `LocIndep k G ↔ MaxDef G ≤ k`, with `JSP90.erdos73_iff_maxDef` restating the whole of Erdős #73 in
  that language:

  ```lean
  Erdős73 k ↔ ∃ m, ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), MaxDef G ≤ k → CloseToBipartite m G
  ```

  So the hypothesis of the problem is a **numerical bound on a function of `G`**, which is what an
  induction on `|V|`, a minimal-counterexample argument, or any "pass the bound on" step needs.  The
  building block is `exists_indepCard` (α of an induced subgraph is *attained*), plus `indepCard` and
  `MaxDef` as the natural numbers `sup`-ing the sizes.
* **THE SANDWICH `ν(G) ≤ MaxDef G ≤ τ(G)`** (`JSP90.packing_le_maxDef_le_transversal`):
  * `card_le_of_maxDef_le` — a deficiency bound bounds every packing of odd cycles (the packing
    bound of `Packing.lean` in numerical form);
  * **`maxDef_le_of_hitsOddCycles` / `maxDef_le_closeToBipartite` — the NEW direction**: every odd
    cycle transversal has at least `MaxDef G` vertices, so *the deficiency is a lower bound for the
    number of vertices one must delete*.  The proof is combinatorial: off the transversal the graph is
    bipartite, so the vertices of `Y` outside it are covered two by two by independent sets, whence
    `|Y| - 2 α(Y) ≤ |Y ∩ X| ≤ |X|`.
  This is exactly the chain along which the Erdős–Pósa theorem would prove JSP-000090, with `MaxDef`
  in place of the packing number — and both halves are now formalised.
* **`maxDef_eq_zero_iff : MaxDef G = 0 ↔ G.IsBipartite`** — the proved case `k = 0` of Erdős #73
  (`JSP90.erdos73_zero`) *is* the statement "deficiency 0 means bipartite"; also
  `maxDef_pos_of_not_isBipartite`.
* **The exact values on the two extremal witnesses, so the deficiency is not a loose bound:**
  * `maxDef_kTriangles : MaxDef (kTriangles k) = k` (upper bound read off `locIndep_kTriangles` by the
    equivalence, lower bound from the whole vertex set `3k - 2k`);
  * `closeToBipartite_kTriangles_iff_maxDef` and `no_closeToBipartite_of_maxDef_kTriangles` — on the
    sharp witness the exact value of the conclusion *is* the deficiency, i.e. the lower bound
    `f(k) ≥ k`;
  * `maxDef_completeGraph : MaxDef (K_n) = n - 2` for `n ≥ 2`, `maxDef_completeGraph_small` for
    `n ≤ 2`, and `closeToBipartite_completeGraph_iff_maxDef` — on complete graphs the number of
    vertices to delete is the deficiency.
* **The arithmetic of the new quantity** (Part 6):
  * `maxDef_mono` (adding edges does not decrease the deficiency), `maxDef_induceFinset_le`,
    **`maxDef_deleteFinset_le`** — the residue inherits the bound, the numerical form of
    `LocIndep.of_deleteFinset` and of the residue induction, so an induction on `MaxDef G` (rather than
    on `|V|`) is now available;
  * **`maxDef_le_maxDef_induceFinset_add_card`** — local-to-global: a piece plus the number of
    vertices outside it;
  * **`card_indepCard_anticover_add`** — the *exact* linear split over an anticomplete decomposition
    (`|Y| = |Y ∩ A| + |Y ∩ B|` and `α(Y) = α(Y ∩ A) + α(Y ∩ B)`), hence `defOf_le_add_of_anticover`
    and `maxDef_le_add_of_anticover`.
* **A weaker sufficient input, named precisely**: `LinearErdős73 C` — "every graph is the union of a
  bipartite graph and `C * MaxDef G` vertices" — implies **all** of Erdős #73 with the explicit
  constant `C * k` (`erdos73Of_linearErdős73`).  This is a statement about the function `τ / MaxDef`
  and is a *strictly weaker* input than the Erdős–Pósa theorem; `not_linearErdős73_zero` refutes it
  for `C = 0` (witness `K_3`), so `C` is a genuine parameter.

### A mathematical finding recorded in the file

The deficiency is **subadditive, not additive**, over an anticomplete decomposition: for `Y` = a
triangle disjoint from one isolated vertex, split into the two parts, `defOf G Y = 0` while
`defOf (G[A]) (Y ∩ A) + defOf (G[B]) (Y ∩ B) = 1 + 0 = 1`.  The obstruction is the truncation at
zero in `|X| - 2 α(X)`, which is why the exact statement proved is the *linear* one
(`card_indepCard_anticover_add`) and the deficiency statement is an inequality.  This is recorded in
the docstring of `JSP90.defOf_le_add_of_anticover`.

### What is *not* proved

`MaxDef G ≤ k → CloseToBipartite (C * k) G` is exactly Erdős #73 in the language of this file and is
not proved here; neither is `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the
unchanged primary blocker.  The *converse* of `maxDef_le_add_of_anticover` (equality for `MaxDef`) is
not proved either: it needs the extra fact that a vertex of `X \ s` is isolated in `G[s]`, so that
adding it to `X` raises `|X|` and `α(G[s][X])` by the same amount.

Toolchain facts verified this round (they cost most of the round): `Finset.max' s H` takes the
`Nonempty` proof as an *explicit* argument and `Finset.le_max'` mentions a *different* witness, so
`Finset.sup` + `Finset.le_sup_iff` is the workable route to an attained maximum; `Finset.Nonempty s` is
`∃ x, x ∈ s` while `Finset.nonempty_iff_ne_empty` is `s ≠ ∅`; `Nat.sub_le_iff_le_add` rewrites a
truncated subtraction into a linear inequality (`Nat.sub_le_iff_le_add : a - b ≤ c ↔ a ≤ c + b`) and
`omega` treats `a - b` as an opaque atom otherwise; `Nat.add_sub_assoc` is *false* in ℕ, while
`Nat.sub_sub : a - b - c = a - (b + c)` and `Nat.sub_add_cancel` hold; `Nat.sub_le_sub_right` takes
the hypothesis *first*; `Finset.mem_filter.mpr` needs the `DecidablePred` instance of the
*definition site*, so the predicate's decider is named as a `local instance`; and a `Finset (Fin n)`
built in one file is not syntactically the one built in another when the two files use different
`DecidableEq` instances (this is why round 53's `K_4` witness did not elaborate).

`jsp_000090_main` is still **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

## Round 59 — `JSPProblem/OffCycle.lean`: the deficiency off an odd cycle

### The new statement

```lean
theorem maxDef_ge_one_add_maxDef_of_oddCycle {C X : Finset V} (hC : IsOddCycle G C)
    (hCX : Separated G C X) : 1 + MaxDef (induceFinset G X) ≤ MaxDef G
```

`Separated G A B` is `Disjoint A B ∧ (no edge of G joins A to B)`.  In words: **the part of `G`
that hangs off an odd cycle has deficiency at most `MaxDef G - 1`**, so an induction on the
deficiency **does** make progress at a separated odd cycle.  This is the equality direction of the
anticomplete additivity recorded as a secondary blocker in round 54, and it holds at an odd cycle
precisely because an odd cycle has deficiency at least `1`
(`two_indepCard_add_one_le_card_of_oddCycle : 2 * α(G[C]) + 1 ≤ |C|`), so the `Nat` truncation in
`defOf` never bites.  The general lemma is `defOf_separated_add_of_nonneg` and the underlying
combinatorial fact is `indepCard_separated_add` (α is additive over separated unions).

### What is proved

* `indepCard_separated_add`, `card_sub_two_separated_add`, `defOf_separated_add_of_nonneg` — the
  exact additivity of α and of `defOf` over separated pairs;
* `two_indepCard_add_one_le_card_of_oddCycle`, `defOf_oddCycle_ge_one`,
  **`maxDef_ge_one_add_maxDef_of_oddCycle`** — the main theorem;
* `maxDef_offCycle_le`, `maxDef_deleteFinset_oddCycle_le`, `locIndep_offCycle`,
  `locIndep_of_separated_oddCycle` — **the `MaxDef` induction step** (the parameter drops to
  `k - 1`);
* `isBipartite_offCycle_of_maxDef_le_one` — the `k = 1` case read locally: everything separated from
  an odd cycle is bipartite; `card_clique_offCycle_le` — a separated clique has at most
  `MaxDef G + 1` vertices;
* `LayeredOddCycles` (with `OddCycleLayers`, `SeparatedLayers`, `DisjointLayers`,
  `CoveredOddCycles`), `layeredOddCycles_erase`, `layered_inter_eq_empty`, `layered_separated_compl`,
  `layered_eq_empty_of_isBipartite`, `oddCyclesMeet_of_not_disjoint` — the class on which the
  induction closes;
* **`erdos73On_of_layered`** — a new instance of the headline theorem, with the **sharp constant
  `k`**: if the odd cycles of `G` are layers (pairwise vertex-disjoint, each separated from
  `V \ C`, and every odd cycle of `G` being one of them) then `LocIndep k G → CloseToBipartite k G`.
  This is the first instance in this development proved by an **induction on `MaxDef`**, and the
  class is attained (`layeredOddCycles_kTriangles`: the `k` disjoint triangles are layered);
* `IsOddCycle.delete_avoiding`, `notMem_of_isOddCycle_deleteFinset`, `isBipartite_iff_no_oddCycle` —
  the missing local lemmas.

### What is *not* proved

The layer condition is a genuine extra hypothesis: a graph whose odd cycles **meet** (the "three
triangles in a ring" on `6` vertices, or `K_5`) has **no** separated odd cycle, so the induction
does not close there — this is exactly why the round-44 "absorption" argument fails at `K_5`, and it
is recorded machine-checked as `oddCyclesMeet_of_not_disjoint`.  What is missing for the general
case is a substitute for the separation hypothesis: a statement that every `LocIndep k` graph has
*some* set `X` with `1 + MaxDef G[X] ≤ MaxDef G`.  `JSP90.OddCycleErdosPosa` remains the primary
blocker, so `jsp_000090_main` is deliberately not declared.

### Environment findings (important for future rounds)

* The pinned Mathlib is **trimmed**: `Mathlib/Tactic/NativeDecide.lean` does **not** exist, so
  `native_decide` is unavailable and kernel `decide` is far too slow for exhaustive verification over
  `Finset`s.  Every value in this round is proved combinatorially.
* `omega` in this build cannot eliminate `Nat` subtraction from hypotheses (`0 ≤ n - m` does **not**
  prove `m ≤ n`) nor substitute atoms in equations; `JSP90.le_succ_of_sub_pos` and
  `JSP90.le_pred_of_succ_le` were added for the two arithmetic steps that `omega` refuses.

---

## Round 61 — `JSPProblem/Boundary.lean`: the boundary of an odd cycle, and a new instance of the
headline theorem

Round 59 proved the exact additivity of the deficiency between an odd cycle and a **separated**
vertex set, and with it a first instance of the headline theorem by an induction on the deficiency,
`JSP90.erdos73On_of_layered`, for the class of graphs whose odd cycles are *layers*.  Its recorded
blocker is exact: a graph whose odd cycles **meet** (`K_5`, the "three triangles in a ring") has no
separated odd cycle, so the induction does not close there.

**This round removes the separation requirement in the right way.**  Instead of asking for a vertex
set separated from an odd cycle, it uses the vertex set that is separated from one *by construction*:

```lean
outerLayer G C = V \ (C ∪ neighOf G C)          -- the vertices at distance ≥ 2 from C
boundary  G C = neighOf G C \ C                 -- the vertices outside C that touch C
```

### The new instance

```lean
JSP90.erdos73On_of_bounded_boundary (d k : ℕ) :
    ∀ W [Fintype W] (G : SimpleGraph W), LocIndep k G → BoundedBoundary d G →
      CloseToBipartite (k * (d + 1)) G
```

where `BoundedBoundary d G` says that **every odd cycle of `G` has at most `d` vertices outside it
that touch it**.  This is a *new axis* — a local two-connectivity condition, not a length condition
(round 39), not a packing condition (round 40), not a number of branch vertices (round 38), not a
decomposition (rounds 42–48), not a separation condition (round 59) — and the class it defines is not
covered by any of them:

* it is **hereditary** (`JSP90.boundedBoundary_induceFinset`), which is what makes the induction on
  `k` legitimate;
* its parameter is **exact on complete graphs**: `JSP90.boundary_completeGraph` gives
  `|boundary K_n C| = n - |C|`, so `JSP90.boundedBoundary_completeGraph_five_two` puts `K_5` in the
  class with `d = 2` and `JSP90.boundedBoundary_completeGraph_four_one` puts `K_4` in it with `d = 1`.
  `JSP90.erdos73On_of_bounded_boundary_completeGraph_five` concludes `LocIndep 3 (K_5) →
  CloseToBipartite 9 (K_5)`; `K_5` is precisely the graph that
  `JSP90.class_hypothesis_is_necessary` isolates as the obstruction to every earlier instance (its
  odd cycles meet, it is not layered, it has no anticomplete decomposition, it is full of branch
  vertices);
* at `d = 0` the constant is the **sharp `k`**, the constant of `JSP90.erdos73On_of_layered`
  (`JSP90.erdos73On_of_bounded_boundary_zero`, `JSP90.closeToBipartite_of_layered_via_boundary`).

### What else is proved

* the **descent**: `JSP90.maxDef_outerLayer_le` (and `JSP90.locIndep_outerLayer`,
  `JSP90.maxDef_ge_one_add_maxDef_outerLayer`) — `MaxDef (G[outerLayer G C]) ≤ k - 1` for the
  canonical separated set, with no hypothesis on `G` near `C`; and
  `JSP90.union_outerLayer` / `JSP90.card_outerLayer` — the complement of the outer layer is exactly
  the cycle plus its boundary;
* the **local structure at a shortest odd cycle**: `JSP90.eq_of_isOddCycle_subset_shortest` (no
  proper odd cycle inside a shortest odd cycle), `JSP90.exists_adj_of_mem_isOddCycle` (every vertex
  of an odd cycle has a neighbour on it) and
  `JSP90.exists_bipartite_delete_of_shortest_oddCycle` (**a shortest odd cycle is bipartite after
  *any* one of its vertices is deleted**, so the odd cycle costs one vertex and not `|C|`);
* the **transversality lemma** `JSP90.hitsOddCycles_of_bipartite_outer`: every odd cycle of `G`
  either meets the outer layer's transversal, or meets the shortest odd cycle or its boundary; and
  its consequence `JSP90.closeToBipartite_of_bipartite_outerLayer` — **local absorption**: if the
  part of `G` at distance `≥ 2` from a shortest odd cycle is bipartite, then `G` is
  `1 + |boundary|` close to bipartite, i.e. the whole content of the problem sits in the *far* part of
  the graph, the part to which the deficiency descent applies;
* the **recursion** in its exact form, `JSP90.bounded_boundary_recursion`;
* the gluing lemmas `JSP90.isBipartite_of_separated_bipartite` (bipartiteness glues over a separated
  pair) and `JSP90.closeToBipartite_on` (a `CloseToBipartite` bound can be read on a vertex set);
* a machine-checked **negative result**, `JSP90.not_boundedBoundary_zero_of_mem_boundary`: an odd
  cycle with a vertex of `G` attached to it from outside is not in the class `BoundedBoundary 0`, so
  the round-59 class is a genuine restriction and the new class is strictly larger.

### What is *not* proved

The parameter `d` is not removed.  At a shortest odd cycle the boundary is the *fan* of the classical
argument — every outside vertex meets the cycle in at most two vertices, two steps apart
(`JSP90.card_inter_neigh_le_two`, `JSP90.shortArc_of_shortest`) — and the classical content of
Reed–Robertson–Seymour–Thomas is to bound the transversal by a constant times the *packing* number
with **no bound at all on the fan**.  That is the single remaining gap, now localised as: *the layer
`G[boundary G C]` of a shortest odd cycle admits an odd cycle transversal of size at most the number
of 2-attachment points*, so that the whole boundary can be replaced by one vertex per fan.

The strong form of the local absorption statement (`deleteFinset G (boundary G C ∪ {c})` bipartite)
was written and abandoned: it needs the finset identity
`(Finset.univ) \ (boundary G C ∪ {c} ∪ Y) = (C \ {c}) ∪ (outerLayer G C \ Y)`, and unpacking the
decidable membership of that identity cost more than the transversal form is worth.

`jsp_000090_main` is still **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true` (1221 jobs).  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

### Toolchain facts found this round (they cost most of it)

* `x ∈ s` for `s : Finset V` is a `Quot`/`Multiset` membership, so the goal produced by `ext` /
  `constructor` is **not** destructible by `rintro`: every membership goal must first be converted
  with `Finset.mem_sdiff` / `mem_union` / `mem_inter` / `mem_singleton`, and the direction of the two
  sides of an `iff` must be read off the error message rather than assumed;
* `by_cases` normalises its statement, so `by_cases` on a statement containing a locally defined finset
  is fragile: use `have h1 : x ∈ C ∨ x ∈ N(C) := Finset.mem_union.mp h` and then `rcases h1`;
* `SimpleGraph.neighFinset` does not exist at the pinned revision, so `neighOf` has to be defined by
  hand (`filter` + `Finset.mem_filter`);
* `Finset.mem_inter`'s binders are `s₁ s₂`, and `Finset.mem_union.mpr` is `Iff.mpr`, so the finsets
  must be pinned on the `Iff`, never on `.mpr`;
* `omega` of this build cannot do distributivity: `k * (d + 1) + d + 1 = (k + 1) * (d + 1)` needs three
  explicit `Nat.mul_succ` / `Nat.succ_mul` facts, and a product by a variable is an opaque atom;
* `SimpleGraph.Adj` is a `Prop` at this revision, so `False` comes from `G.loopless.irrefl` and
  symmetry from `G.adj_symm`;
* for a concrete `Fin n` witness, `Finset` literals built in different files use different
  `DecidableEq` instances (the round-53 pitfall) **and** `Finset.image` picks the use-site instance
  while the goal uses the definition-site one — a concrete witness on `Fin n` must avoid
  `Finset.image`.

---

## Round 62 — `JSPProblem/Cut.lean`: the cut descent of the deficiency

Round 61 (the `BoundedBoundary` instance) leaves the parameter `d` and asks for the fan lemma.  Round 62
takes a different route to the same place: **the separator itself**, in the *numerical* vocabulary of
`MaxDef G = max {|X| - 2α(G[X])}` of `JSPProblem/Deficiency.lean`, where Erdős's hypothesis is the single
number `LocIndep k G ↔ MaxDef G ≤ k`.  New file `lean/JSPProblem/Cut.lean` (14 declarations, 0 sorry,
`lake build` OK, 1222 jobs), imported from the root module `JSPProblem.lean`.

### What is proved

* **`JSP90.indepCard_le_add (A B) : indepCard G (A ∪ B) ≤ indepCard G A + indepCard G B`** — the
  independence number is *subadditive* over a union: the independent sets of `A ∪ B` split into an
  independent subset of `A` and an independent subset of `B`.  This is the second half of the additivity
  of the deficiency over a decomposition (the first half is round 54's `card_indepCard_anticover_add`),
  and it is exactly what the classical "the deficiency splits at a cut" step needs.
* **`JSP90.sum_card_inter_le_card`** — for a family of pairwise disjoint, pairwise anticomplete pieces
  covering the vertices of `Y`, the cardinalities of the parts add up to **at most** that of `Y`:
  `∑ |Y ∩ Q| ≤ |Y|` (in fact with equality, `Y = ⋃ᵩ (Y ∩ Q)`).
* **`JSP90.AnticoverCoverFamily.sub` / `.notMem_inter` / `.disjoint'`** — subfamilies of an anticomplete
  family are anticomplete, two distinct pieces are disjoint and share no vertex.
* **`JSP90.defOf_inter_induceFinset`** — the deficiency of `Y ∩ Q` computed in `G` and in `G[Q]` agree (the
  transport lemma the round-54 statements are missing).
* **the `ℕ`-arithmetic of the deficiency**, which is the technical content of the whole line and is
  where round 54 recorded a genuine obstruction:
  * `JSP90.sum_sub_le : (∑ aᵢ) - (∑ bᵢ) ≤ ∑ (aᵢ - bᵢ)` — always true for `ℕ`;
  * **`JSP90.sum_sub_eq_of_le : ∑ (aᵢ - bᵢ) = (∑ aᵢ) - (∑ bᵢ)` under `bᵢ ≤ aᵢ`** — **false without the
    hypothesis**, and the failure is exactly round 54's counterexample (a triangle disjoint from one
    isolated vertex: the deficiency of the whole is `0`, the parts give `1 + 0`).  So the deficiency is
    subadditive for a fixed vertex set, and becomes *exactly* additive once no truncation occurs;
  * `JSP90.sum_f_le_f_sum`, `JSP90.f_mono_of_succ_le`, `JSP90.add_le_mul_of_two_le`,
    `JSP90.sup_pow_four`, `JSP90.step_pow_four` — the numerical hypotheses of the *intended* reduction
    theorem (Erdős #73 in full follows from its restriction to triangle-free graphs, with
    `f(k) = 4 ^ k`), discharged in advance: superadditivity on the positive integers, monotonicity, and
    the two inequalities `4 ^ i + 4 ^ j ≤ 4 ^ (i+j)` and `3 + 4 ^ (k-1) ≤ 4 ^ k`.

### The route this opens (and the single lemma this round stopped at)

With `indepCard_le_add` (α subadditive over a union) and `sum_card_inter_le_card` (cards subadditive
over a cover) in hand, the following chain would finish a **reduction of Erdős #73 to triangle-free
graphs**, i.e. replace the primary blocker `OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) by the
strictly weaker statement `∀ k, ∀ G, G.CliqueFree 3 → MaxDef G ≤ k → CloseToBipartite (f k) G`:

1. `indepCard_le_sum_inter`: for a covered `X`, `α(G[X]) ≤ ∑_Q α(G[X ∩ Q])` — the *family* version of
   `indepCard_le_add`; **this is the one lemma not proved this round**;
2. `∑_Q MaxDef G[Q] ≤ MaxDef G` (superadditivity of the deficiency over a cover, using 1 together with
   `sum_sub_eq_of_le`);
3. `AnticoverCut G T 𝒬` = a cut `T` together with an anticomplete cover of the rest, and
   `MaxDef G ≤ |T| + ∑_Q MaxDef G[Q]` (the subadditive direction);
4. **the deficiency drops at a triangle**: for every piece `Q` of a cut at a triangle, `1 + MaxDef G[Q] ≤
   MaxDef G` and `1 + ∑_{Q non-bipartite} MaxDef G[Q] ≤ MaxDef G` (uses `indepCard_le_add` with the
   triangle, whose `α = 1`);
5. `erdos73On_of_anticoverCut`: the new instance of the headline theorem over an arbitrary cut, constant
   `|T| + k · m`;
6. `erdos73On_of_triangleFree`: induction on `k` alone, using 4 (the pieces have deficiency `≤ k - 1`,
   with total `≤ k - 1`), 2, the counting lemma `card_nonBipartiteParts_le_cover` of
   `JSPProblem/Additive.lean` and the numerical facts above.

Steps 1 and 4 are mechanical once step 1 is available; this round's budget went into step 1 (which is
where the `IsIndepSet`/`Finset` coercion bookkeeping of this trimmed Mathlib is most expensive) and the
budget ran out.  The exact statement, the two routes to it and the environment findings are in
`discovery/JSP-000090/policy.json`.

### Toolchain findings (they cost most of the round)

* **`ring`, `norm_num`, `nlinarith` are ABSENT** from the pinned Mathlib; `omega` cannot do
  distributivity, cannot eliminate `ℕ` subtraction from hypotheses, and cannot prove
  `(a + c) - (b + c) = a - b` (it is true, and `Nat.add_sub_add_right` states it).
* `Finset.sum_filter_neg_eq`, `Finset.eq_empty_iff_forall_not_mem`, `Finset.le_empty`,
  `Set.mem_inter`, `Set.sdiff_subset_left`, `Finset.inter_subset_left/right` (as subset lemmas) are all
  ABSENT; `Set.mem_inter` in particular is absent, so Set intersections must be handled with
  `Finset.mem_inter` and explicit pinning `Finset.mem_inter (s₁ := S) (s₂ := T)`.
* `Finset.coe_inter`, `Finset.coe_sdiff`, `Finset.card_biUnion`, `Finset.mul_sum s f a`,
  `Nat.add_sub_cancel_left`, `Nat.add_sub_add_right`, `Finset.sum_add_distrib` are available.
* **`G.IsIndepSet` takes a `Set`, not a `Finset`**, and `Finset.inter`/`Finset.sdiff` of two finsets
  coerce *differently* (`↑(s ∩ t)` vs `↑s ∩ ↑t`): the two are **not** defeq-recognisable for the
  elaborator in this revision.  Consequence: an `IsIndepSet` statement about a *compound* finset must be
  built at the Set level (`Set.inter_subset_left` / `Finset.mem_inter` on the coerced hypothesis), and
  to feed it to `le_indepCard_of_isIndepSet` (which wants the canonical `↑(s ∩ t)`) the compound finset
  must be given a name with `set T := s ∩ t with hT` and transported with `hT.symm ▸`.
* `G.IsClique` also takes a `Set` but a `Finset` argument coerces silently and the applied form takes
  **finset** memberships (as in `JSPProblem/Reed.lean`).
* `(A + B) - A = B` and `(A + B) - A + A = A + B` are provable by bare `omega`; `Nat.sub_le_sub_left`
  (`k - m ≤ k - n` from `n ≤ m`) and `Nat.sub_le_sub_right` (`n - k ≤ m - k` from `n ≤ m`) are the two
  usable subtraction lemmas; there is no "subtrahend monotone" lemma, which is why
  `sum_sub_eq_of_le` needs its own induction.
* `Finset.sup_le_iff` needs `OrderBot`, so it can only be applied to a goal in which the `sup` is
  visible: `refine Finset.sup_le_iff.mpr fun S hS => ?_` leaves the type stuck when the goal is
  `∑ … ≤ indepCard G Y`.  Use `exists_indepCard` (a witness for the sup) instead.
* The cover hypotheses of `JSPProblem/Additive.lean` are stated as `∀ x ∈ s → ∃ X ∈ 𝒬, x ∈ X`; the
  `Y ⊆ 𝒬.biUnion id` form is *not* destructible by `rcases` (Quot membership), exactly as recorded in
  round 61's toolchain notes.
* `lake build` is ~7 s incremental; `JSPProblem.Cut.lean` alone ~5 s.

`jsp_000090_main` is still **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

## Round 63

**Attack family 14 (continued): the cut descent of the deficiency, finished in the
`CloseToBipartite` vocabulary.**  `JSPProblem/Cut.lean` now holds **42 declarations, 0 sorry,
0 admit, `lake build` OK (1222 jobs)**.  The round closed round 62's named blocker
`indepCard_le_sum_inter` and then discharged the *instance* half of the planned reduction
(`closeToBipartite_of_anticoverCut`), which had been the largest remaining Lean item of the line.

### What is now proved

* `JSP90.indepCard_le_sum_inter` — **the round-62 blocker.**  For a family `𝒬` of pairwise disjoint,
  pairwise anticomplete pieces with `(h : AnticoverCoverFamily G 𝒬)` covering `X`,

  ```lean
  indepCard G X ≤ ∑ Q ∈ 𝒬, indepCard G (X ∩ Q)
  ```

  proved by induction on the family with `indepCard_le_add` as the merge step, which is exactly
  route 1 of the recorded plan.  No `IsIndepSet` bookkeeping of compound finsets is needed.
* `JSP90.AnticoverCut` — **a cut of `G` at a set `T`**: `AnticoverCoverFamily G 𝒬`, every piece
  disjoint from `T`, every piece anticomplete to `T`, and `𝒬` covering `V \ T`.  With
  `AnticoverCut.anticomplete_to_T`.
* `JSP90.closeToBipartite_of_anticoverCut` — **A NEW INSTANCE OF THE HEADLINE THEOREM, OVER A CUT AT
  A `3`-CLIQUE.**  If `T` is a triangle and the vertices of `V \ T` split anticompletely into pieces,
  each disjoint from `T`, anticomplete to it, and `m`-close to bipartite, then

  ```lean
  LocIndep k G → CloseToBipartite (3 + k * m) G
  ```

  The constant is **independent of the number of pieces**: at most `k` of them are non-bipartite
  (`card_nonBipartiteParts_le_cover`), and the rest cost nothing.  **No bound is assumed on the odd
  girth, on the packing weight, or on the number of branch vertices** — this is the hypothesis
  triple that rounds 54–62 kept having to impose.
* `JSP90.closeToBipartite_sub_induceFinset` — a `CloseToBipartite` bound reads on any subgraph with
  the *same* constant (witness `Y ∩ U`, via `U \ (Y ∩ U) = U \ Y`).
* `JSP90.closeToBipartite_of_anticoverCut_on` — the instance read on a vertex set `U ⊆ V`, the form
  the reduction consumes.
* The vertex-set-restricted deficiency `JSP90.maxDefIn G U = (U.powerset).sup (defOf G)`, with
  `le_maxDefIn`, `exists_eq_maxDefIn`, `maxDefIn_mono`, `defOf_induceFinset_of_subset`,
  `maxDefIn_induceFinset_eq`, and the two clique absorption lemmas
  `maxDefIn_ge_one_add_maxDefIn_of_clique` / `..._of_clique_sub`
  (`1 + MaxDef (G[T]) ≤ MaxDefIn G U` for a triangle `T ⊆ U`).

### A mathematical correction worth recording

`maxDefIn (induceFinset G Q) V` is **not** `maxDefIn G Q`: for `Y ⊄ Q` the quantity
`defOf (G[Q]) Y` is defined by `indepCard (G[Q]) Y`, and `Y` ranges over subsets of the *ambient*
`V`, so it is a different (larger) number.  Any statement that restricts a deficiency bound to a
piece must therefore quantify over the pair `(G, U)` and conclude about `induceFinset G U`; it
cannot be phrased as a bound on `MaxDef (G[Q])`.  `closeToBipartite_of_anticoverCut_on` is the
bridge that makes this point harmless: a `CloseToBipartite` bound *does* transfer to subgraphs.

The proof of the instance is exactly the plan of round 62, in the `CloseToBipartite` rather than
the `MaxDef` vocabulary: filter `𝒬` to the non-bipartite pieces `N` (`|N| ≤ k`), apply
`closeToBipartite_of_anticoverFamily_cost` with the constant `m` on each, put
`Z = X₁ ∩ N.biUnion id` (so `|Z| ≤ m * k` and `N.biUnion id \ Z = N.biUnion id \ X₁`), show
`G[univ \ (T ∪ N.biUnion id)]` bipartite by `isOddCycle_sub_anticoverCover` (every odd cycle of the
residue lies in a piece, and a non-bipartite piece would sit inside the residue), and glue with
`closeToBipartite_of_anticover` on the `Anticover` split
`(T ∪ N.biUnion id) ∐ (univ \ (T ∪ N.biUnion id))`.

### Toolchain findings of this round

* `Finset.mem_sdiff.mp h` returns `x ∈ s ∧ x ∉ t`, so `.2` is the **negation function**: `hh.2 h` with
  `h : x ∈ t`, and `hh.2` alone has type `¬ x ∈ t`.  `(Finset.mem_sdiff.mp hx).2` is *not* a
  membership and is the source of most of the errors of this round.
* `Finset.mem_union.mpr (Or.inl h)` does **not** elaborate when the goal is a `Quot` membership: Lean
  infers the *other* finset of the union from the branch of the `Or` and picks the wrong one (goal
  `x ∈ A ∪ B`, term `x ∈ B` reported as expected to be `x ∈ A`).  Use the pinned helpers
  `JSP90.mem_union_left' A B` / `JSP90.mem_union_right' A B`, or restructure so that the membership
  is transported with an explicit `have h2 : … := …` annotation.  This is the same class of problem
  as round 61's note about `Finset.mem_inter`'s `s₁ s₂` binders.
* `N.biUnion id` needs `(id : Finset V → Finset V)` annotated: `biUnion` infers its codomain from
  the argument and `id` alone is polymorphic.
* `Finset.sum_const` followed by `nsmul_eq_mul` yields `m * ↑#s` on the left and `m * #s` on the
  right, and neither `Nat.cast_rfl` nor `Nat.cast_ofNat` is accepted; **plain `simp`** normalises the
  `↑` and then `Nat.mul_comm` finishes.  So `∑ x ∈ s, m = s.card * m` is `by simp`, and the
  inequality is `have h : … := by simp; rw [h, Nat.mul_comm]`.
* `Finset.inter_subset_left : s ∩ t ⊆ s` and `Finset.inter_subset_right : s ∩ t ⊆ t` are element
  projections, so they cannot be passed as an `⊆` *function* to `Finset.card_le_card` without a type
  ascription (`Finset.inter_subset_left : X₁ ∩ NN ⊆ X₁`); with a `set`-bound local the `show` is
  needed because the projection does not match the folded finset syntactically.
* `deleteFinset_induceFinset (A X : Finset V)` takes no named `G` argument (it is a section
  variable), so `(G := …)` is rejected; the `G` has to be fixed by annotating the *goal*:
  `have hdel : deleteFinset (induceFinset G A) X = … := deleteFinset_induceFinset _ _`.
  `induceFinset_univ : induceFinset G (Finset.univ : Finset V) = G` converts a `deleteFinset G Y`
  hypothesis into an `IsBipartite` statement about `G[univ \ Y]`.
* `IsOddCycle.of_induceFinset` lifts an odd cycle of `G[s]` to one of `G`, and
  `isOddCycle_sub_induceFinset (s := …)` gives the vertex set, so an odd cycle of a residue can be
  pushed up and then fed to `isOddCycle_sub_anticoverCover` — the whole `hrest` argument of the
  instance is these three lines plus `isOddCycle_card_ge_three`.

`jsp_000090_main` is still **not** declared; `harness/score.py --strict-prize problems/JSP-000090`
reports `build_ok = true, sorry = 0, admit = 0, partial_ok = true,
missing_theorems = ["jsp_000090_main"]`.  `formalization.yaml` remains `status: wip`,
`prize_ready: false`.  No award claim is made.

---

## Round 64 — `JSPProblem/CutTriangle.lean`: the cut triangle, and the reduction of Erdős #73 to
two local statements

New file `lean/JSPProblem/CutTriangle.lean` (**26 declarations, 608 lines, 0 `sorry`, 0 `admit`,
`lake build` OK, 1223 jobs**), imported from the root module `JSPProblem.lean`.  It is the
**fifteenth attack family** and it *finishes* the reduction that rounds 62–63 planned: the two gaps
that round 63 named as blockers are closed, and the induction on `k` is run.

### What is proved

1. **The deficiency of an induced subgraph** (`Part 1`) — the transport lemma that makes an
   induction on Erdős's parameter act on a *piece* of a decomposition:
   * `JSP90.indepCard_induceFinset_inter_add_sdiff`: **α of an induced subgraph splits off the
     vertices outside it**, `α(G[U], Y) = α(G[U], Y ∩ U) + |Y \ U|` (the vertices of `Y \ U` are
     isolated in `G[U]`, so they can all be added to an independent set — the combinatorial content
     is `JSP90.mem_indepSets_union_sdiff`);
   * `JSP90.defOf_induceFinset_inter_le`, and therefore
   * **`JSP90.maxDef_eq_maxDefIn_induceFinset : MaxDef (induceFinset G U) = maxDefIn G U`** — the
     deficiency of the *graph* `G[U]`, read over all subsets of the ambient vertex type, is the
     deficiency *inside `U`*.  This is the answer to the "mathematical correction" that round 63
     recorded against the unrestricted `maxDefIn (induceFinset G Q) V`;
   * `JSP90.locIndep_induceFinset_of_maxDefIn_le`: a bound on the deficiency inside a vertex set is
     a local hypothesis on the induced subgraph.
2. **A cut triangle** (`Parts 2–3`):
   * `JSP90.anticoverCoverFamily_compPieces_sub` — the components of a subgraph `H ≤ G`, restricted
     to a vertex set `S` on which `H` and `G` have the same edges, are pairwise disjoint and
     pairwise anticomplete **in `G`**.  This is what lets the components of `G[V \ T]` be used as
     pieces of a decomposition of `G`;
   * **`JSP90.CutTriangle G T`** = `T.card = 3 ∧ (no edge of `G` joins `T` to `V \ T`)**, and
     `JSP90.cutPieces G T` = the components of `G[V \ T]` **intersected with `V \ T`** (the
     intersection is what makes every piece avoid `T` *by construction*, so no appeal to the
     internals of `SimpleGraph.Walk` is needed);
   * `JSP90.anticoverCoverFamily_cutPieces`, `JSP90.mem_cutPieces`,
     **`JSP90.anticoverCut_of_cutTriangle`** — a cut triangle gives the `AnticoverCut` of
     `JSPProblem/Cut.lean` at that triangle.  This closes the blocker that round 63 recorded as
     "the triangle-cut construction, now the only real gap";
   * **`JSP90.closeToBipartite_of_cutTriangle` — a new instance of the headline theorem at a
     canonical cut**: if every component of `G[V \ T]` is `m`-close to bipartite and `T` is a
     triangle with no edge to the rest of `G`, then `LocIndep k G → CloseToBipartite (3 + k * m) G`,
     with no bound on the odd girth, the packing weight or the number of branch vertices.
3. **The descent at a cut triangle** (`Part 4`): **`JSP90.maxDefIn_le_of_cutPiece`**,
   `1 + maxDefIn G Q ≤ k` for every piece `Q` (the statement round 63 named as missing), and
   **`JSP90.locIndep_piece_of_cutTriangle`**, `LocIndep k G → Q ∈ cutPieces G T →
   LocIndep (k - 1) (G[Q])`.
4. **THE REDUCTION** (`Part 5`) — **`JSP90.erdos73_of_triangleFree`**: *Erdős Problem #73, in full,
   follows from two local statements*, with the explicit constant `JSP90.cutBound`
   (`cutBound 0 = 1`, `cutBound (k + 1) = 3 + (k + 1) * cutBound k`):
   * `JSP90.TriangleFreeErdős73` — Erdős #73 restricted to **triangle-free** graphs;
   * `JSP90.CutTriangleErdős73` — a graph satisfying `LocIndep k` with `k ≥ 1` either has a *cut
     triangle* or is already `cutBound k`-close to bipartite;
   * the induction is on `k` alone (`k = 0` is `JSP90.erdos73_zero`; at `k + 1` a triangle-free
     graph is a `TriangleFreeErdős73`, and otherwise the pieces of the cut at the cut triangle are
     `LocIndep k`, hence `cutBound k`-close to bipartite by the induction hypothesis, and
     `closeToBipartite_of_cutTriangle` gives `3 + (k + 1) * cutBound k = cutBound (k + 1)`);
   * `JSP90.erdos73_of_triangleFree_of_allTrianglesCut` closes the reduction unconditionally on the
     class of graphs whose `3`-cliques all cut.
5. **A machine-checked negative result**: `JSP90.not_cutTriangle_completeGraph_four` — in `K_4` no
   `3`-clique cuts the graph (the fourth vertex is adjacent to all three), so `CutTriangle` is a
   hypothesis and not a theorem.  This is the same obstruction that round 44 recorded for the naive
   absorption step (`JSP90.absorption_step_fails`, `K_5`) and round 63 for the construction of
   `AnticoverCut`.

### A correction to rounds 62–63

Those rounds planned the constant `f k = 4 ^ k`, on the strength of `JSP90.sup_pow_four` and
`JSP90.step_pow_four`.  **That constant cannot work**: the instance of round 63 costs
`3 + k * f (k - 1)`, and `3 + k * 4 ^ (k - 1) > 4 ^ k` for `k ≥ 5`
(`k = 10`: `3 + 10 · 4⁹ = 2 621 443 > 4¹⁰ = 1 048 576`).  The recurrence actually forced by the
instance is `f (k + 1) = 3 + (k + 1) * f k`, which is `JSP90.cutBound`; the two numerical lemmas of
`Cut.lean` are therefore not the hypotheses of the reduction and are not used.  A constant of the
shape `4 ^ k` would need the *superadditive* half of the additivity of the deficiency over a cut
(`∑_Q maxDefIn G Q ≤ MaxDef G - 1`), i.e. `JSP90.sum_sub_eq_of_le` applied to a vertex set on which
no truncation occurs; that half is not proved and is not needed for the reduction.

### What is *not* proved

Exactly two statements, and they are the whole remaining content:

* **`JSP90.TriangleFreeErdős73`** — Erdős #73 for triangle-free graphs (the classical triangle-free
  case);
* **`JSP90.CutTriangleErdős73`** — the local absorption of the round-61 line: near a triangle,
  either the graph cuts there or it is `O_k(1)` from bipartite.  A cut triangle need not exist for a
  `LocIndep 1` graph (a `C_5` with a hub adjacent to all of it and a pendant edge at the hub has
  `MaxDef = 1`, is not bipartite and has no cut triangle), so this is a genuine case distinction;
  it is the local lemma of Reed's *Mangoes and Blueberries*.

Both are statements about a *class* of graphs, and both are strictly weaker than the
Reed–Robertson–Seymour–Thomas theorem (`JSPProblem/Transversal.lean`, `JSP90.OddCycleErdosPosa r`,
the primary blocker of the earlier rounds): neither mentions a packing number, a transversal, an
odd girth, a packing weight or a number of branch vertices.

`jsp_000090_main` is still **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `harness/score.py --strict-prize problems/JSP-000090`
reports `build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

### Toolchain findings of this round

* **A composite finset expression at a `Set`-expected position is elaborated with `Set`
  operations, not `Finset` ones.**  `G.IsIndepSet (S ∪ (Y \ U))` elaborates the argument as
  `↑S ∪ (↑Y \ ↑U)`, which is **not defeq** to `↑(S ∪ (Y \ U))` (the round-62 note, confirmed
  again).  The robust idiom is to state such facts in *finset* language — e.g.
  `S ∪ (Y \ U) ∈ indepSets (G[U]) Y` — so that the argument position is a `Finset` variable and the
  `mem_filter` predicate applies the `↑` coercion itself;
* **`Finset.eq_empty_iff_forall_notMem` exists** (contrary to the round-62 note) and
  `Finset.inter_eq_empty` does **not**; `Finset.sdiff_subset_left` and
  `Finset.not_mem_empty` do not exist either;
* applying a *subset* hypothesis to get a membership, and destructuring the result with
  `Finset.mem_inter.mp`, needs an intermediate `have` with the membership type written out: the
  elaborator does not see through `⦃a⦄, a ∈ s → a ∈ t`;
* strict-implicit binders (`⦃x y : V⦄` in a `CutTriangle` hypothesis) must be given by name
  (`hT.2 (x := y) (y := x) …`);
* `omega` **does** prove `a ≤ (a - c) + c`, and it does normalise multiplication by numerals, so
  `2 * (α + b) = 2 * α + 2 * b` needs no help; it still cannot eliminate `Nat` subtraction
  (`JSP90.le_pred_of_succ_le` of `OffCycle.lean` remains the way to get `n ≤ k - 1` from
  `n + 1 ≤ k`);
* `SimpleGraph.Reachable` at this revision is `Nonempty (G.Walk u v)` and `G.Walk` is an inductive
  on `V → V → Type`; avoiding it entirely (by intersecting the components with `V \ T` before
  forming the family) turned out to be much cheaper than any induction on walks;
* `push_neg` is deprecated in this build (`push Not` instead), and it makes no progress on
  `¬ G.CliqueFree 3` (`CliqueFree n = ∀ t, ¬ G.IsNClique n t`), so a `by_contra` is the way to
  extract the `3`-clique.
---

## Round 65 — `JSPProblem/Attach.lean`: a clique and the vertices that complete it

Round 64 closed the two gaps of the triangle descent and reduced Erdős #73 to **two local
statements** (`JSP90.TriangleFreeErdős73` and `JSP90.CutTriangleErdős73`), and
`discovery/JSP-000090/policy.json` named as the *first concrete lemma* of the attack on the latter:

> for a triangle `T` with `LocIndep k G`, the number of vertices of `S = N(T) \ T` adjacent to
> **all three** vertices of `T` is at most `k − 1`.

**That lemma is false**, and round 65 proves the correct statement in its place.  New file
`lean/JSPProblem/Attach.lean` (34 declarations, 578 lines, **0 sorry / 0 admit**, `lake build` OK
with 1224 jobs), imported from the root module `JSPProblem.lean` — the **sixteenth attack family**,
and the first one to attack the *local counting* of a clique rather than a decomposition or the
Erdős–Pósa function.

### Part 1 (positive) — a clique contributes at most one vertex to any independent set

* **`JSP90.indepCard_le_one_add_of_isClique`** — `G.IsClique T → indepCard G (T ∪ X) ≤ 1 + indepCard G X`:
  an independent set meeting `T` has all but one of its vertices in `X`.
* **`JSP90.maxDef_ge_card_add_card_sub_two_add`** — the additive form
  `|T| + |X| − 2 − 2 α(G[X]) ≤ MaxDef G` for a clique `T` disjoint from `X`: in the deficiency
  bookkeeping a clique costs `|T|` vertices and buys **one** vertex of the independent set.
* **`JSP90.maxDef_clique_add_two_le`** — a clique has at most `MaxDef G + 2` vertices (the
  deficiency form of `JSP90.LocIndep.clique_card_le`).
* **`JSP90.allNeighOf G T`** — the new quantity of the file: the vertices outside `T` adjacent to
  *every* vertex of `T` (for `|T| = 2` the common neighbourhood of the edge; for a triangle the set
  of `K_4`-completions).
* **`JSP90.maxDef_allNeighOf_le`** and **`JSP90.maxDef_commonNeigh_le`** — the completion set of a
  clique of size `≥ 2` is *deficiency-cheap*: its own deficiency is at most `MaxDef G`.
* **`JSP90.card_allNeighOf_of_isClique_le`** — **`|T| + |A| ≤ MaxDef G + 2` whenever `A` is a clique
  of vertices each adjacent to every vertex of the clique `T`** (via
  `isClique_union_allNeighOf`: `T ∪ A` is a clique).  **This is the counting lemma the triangle
  descent actually needs**, and Part 2 shows why its shape is forced.

### Part 2 (negative, machine-checked) — the completion sets are free in the deficiency

The witness is `joinTriangle m = K_3 ∨ I` on `Fin 3 × Fin (m + 2)`: the fibre `Fin 3 × {0}` is a
triangle, every vertex outside it is adjacent to all three of its vertices, and there are no other
edges (`joinTriangle`, `joinTriangle_tri`, `joinTriangle_tail`, `isIndepSet_joinTriangle_tail`,
`isIndepSet_joinTriangle_sdiff`, `isClique_tri_insert`).

* **`JSP90.maxDef_joinTriangle : MaxDef (joinTriangle m) = 2` for every `m`**
  (`maxDef_le_two_joinTriangle`, `maxDef_joinTriangle_two`), so `JSP90.locIndep_two_joinTriangle`
  holds for every `m`.
* **`JSP90.completion_card_unbounded`** — for every `n` there is a graph with `LocIndep 2` and a
  triangle with more than `n` outside vertices adjacent to all three of its vertices: the
  policy's proposed lemma is **false**.
* **`JSP90.commonNeigh_card_unbounded`** — for every `n` there is a graph with `LocIndep 2` and an
  edge whose common neighbourhood has more than `n` vertices: *"the common neighbourhood of an edge
  has at most `k` vertices"* is **false** as well.

The reason is the algebra `| T ∪ A | − 2 α(G[T ∪ A]) = | T | + | A | − 2 max (1, |A|)`: for
independent `A` the deficiency is `| T | − | A |`, so **mutually non-adjacent completions cost
nothing**; only the cliques *inside* the completion set cost something, which is exactly what
`card_allNeighOf_of_isClique_le` bounds.  This is the same obstruction as
`JSP90.absorption_step_fails` (`JSPProblem/Weight.lean`, witness `K_5`) in the transversal language.

### What is *not* proved

`MaxDef G ≤ k → CloseToBipartite (C · k) G` is unchanged, and so are the two remaining local
statements `JSP90.TriangleFreeErdős73` and `JSP90.CutTriangleErdős73` (the latter is now known
*not* to be provable by any cardinality count of the `K_4`-attachments, which is what this round
removes).  `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) remains the primary blocker.

Environment facts verified this round are recorded in the header of the new file; the important ones
are that `SimpleGraph.IsClique`/`IsIndepSet` take **`Set`s** (so `insert a s` written at a
`Set`-expected position is silently a *set* insert, `isClique_finset_insert` bridges the two), that
`IsIndepSet_iff` leaves the goal `∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ G.Adj x y`, and that `0 : Fin m` needs
`NeZero m` (hence the vertex type `Fin 3 × Fin (m + 2)`).

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 69 — `JSPProblem/Free.lean`: the fan of an odd cycle in a triangle-free graph, and
**Erdős #73 ≡ its fan statement**

New file `lean/JSPProblem/Free.lean` (**33 declarations, 706 lines, 0 `sorry` / 0 `admit`, `lake build`
OK with 1226 jobs**), imported from the root module `JSPProblem.lean`.  It is the **nineteenth attack
family**.  Its headline is a **localisation**: the single statement left by round 68
(`JSP90.TriangleFreeOnly`) is *equivalent* to a statement about **one odd cycle and the set of
vertices that touch it** — and the proof of the equivalence needs no Menger theorem, no block-cut
tree, and nothing from Mathlib beyond the pinned slice.

### Part 1 — triangle-freeness made usable

`G.CliqueFree 3` is a *hypothesis* in `JSP90.TriangleFreeOnly` and had never been used anywhere in
the development.  This round turns it into usable content:

* `JSP90.isNClique_three` (three mutually adjacent vertices are a `3`-clique; the three coincidences
  are excluded by looplessness) and `JSP90.isNClique_three_of_isOddCycle` (a `3`-cycle *is* a
  `3`-clique, via `JSP90.fin3_cycSucc_rel`: on `Fin 3` two distinct indices are consecutive around
  the cycle);
* **`JSP90.card_ge_five_of_cliqueFree3_of_isOddCycle` — in a triangle-free graph every odd cycle has
  at least `5` vertices.**  This is what makes the local structure of `JSPProblem/Fan.lean` (stated
  for `5 ≤ |C|`) available at *every* odd cycle of a triangle-free graph, not only under `LocIndep`;
* `JSP90.not_adj_of_common_neigh_of_cliqueFree3`, `JSP90.indepSet_neighOf_singleton_of_cliqueFree3`
  and **`JSP90.neighOf_insert_isBipartite_of_cliqueFree3` — the neighbourhood of a vertex is
  independent, so the closed neighbourhood induces a bipartite graph.**  The difficulty of Erdős #73
  is never *at* a vertex.

### Part 2 — the complete local structure of a triangle-free graph at a shortest odd cycle

* **`JSP90.not_adj_cycSucc_of_adj` — a vertex adjacent to `f i` is *not* adjacent to the successor of
  `f i` on the cycle.**  The first genuine use of `CliqueFree 3` on the fan: the two attachments of a
  fan vertex are never consecutive, so the fan is a book, not a web.
* `JSP90.pairwise_not_adj_fan_of_cliqueFree3` and `JSP90.card_le_one_of_adj_of_fan_attach` — **the
  fan vertices attached to one fixed vertex of the cycle are pairwise non-adjacent**, so the fan is a
  disjoint union of independent classes and every edge inside the fan joins two *different* classes.
* **`JSP90.localStructure_shortest_oddCycle_free` — the complete local structure of a triangle-free
  graph at a shortest odd cycle**: an outside vertex meets the cycle in at most two vertices, two
  steps apart (rounds 35/63), **and is not adjacent to the vertex in between** (new: the only place
  `CliqueFree 3` enters).

### Part 3 — the fan carries one unit less packing

* **`JSP90.oddCycleFamily_card_le_of_boundary` — under `LocIndep k G`, no packing of `k` odd cycles
  lives inside the boundary of an odd cycle**: such a packing together with the cycle itself would be
  a packing of `k + 1` odd cycles of `G`.  This is the induction parameter of the classical
  Erdős–Pósa argument, in the form the development consumes.
* `JSP90.isBipartite_fan_of_locIndep_one` — `LocIndep 1` and an odd cycle force the fan to be
  bipartite.

### Part 4 — THE REDUCTION

```lean
JSP90.FanErdős73 f
  := ∀ k W [Fintype W] G, LocIndep k G → G.CliqueFree 3 → ∀ C, IsOddCycle G C →
       ∃ Z, Z.card ≤ f k ∧ ∀ D, IsOddCycle G D → D ∩ boundary G C ≠ ∅ → D ∩ Z ≠ ∅
```

* `JSP90.erdos73On_of_fanErdős73` with `JSP90.fanBound f` (0 at `k = 0`, and
  `max (fanBound f k + f (k+1) + 1) (3 + (k+1) * fanBound f k)` at `k + 1`) — **Erdős #73 follows
  from its fan statement.**  The induction uses, at a triangle, round 68's
  `closeToBipartite_of_triangle`; at a shortest odd cycle `C` of a triangle-free graph it uses the
  two transversality facts already proved: the outer layer inherits `LocIndep (k − 1)`
  (`locIndep_outerLayer`) and the odd cycles avoiding the outer layer are caught by
  `boundary G C ∪ {c} ∪ Y` (`hitsOddCycles_of_bipartite_outer`).
* `JSP90.erdos73_of_fanErdős73` — **Erdős Problem #73 follows from a purely local statement about the
  boundary of one odd cycle in a triangle-free graph.**
* `JSP90.fanErdős73_of_triangleFreeOn` and **`JSP90.erdos73_iff_fanErdős73`** — the converse, so
  **ERDŐS PROBLEM #73 IS EQUIVALENT TO ITS FAN STATEMENT.**  This replaces the policy's
  "needs Menger / the block-cut tree" formulation of the blocker by a statement about a single pair
  of vertex sets.

### Part 5 — the statement is not a formality

* `JSP90.fanErdős73_of_bounded_boundary` — the fan statement holds with `f k = d + 1` when every odd
  cycle has at most `d` vertices in its boundary.  The instance of the headline theorem obtained this
  way is *dominated* by round 61's `erdos73On_of_bounded_boundary`: the content of the fan statement
  is the **unbounded**-fan case, which is what the equivalence isolates.
* **`JSP90.not_fanErdős73_one_completeGraph_seven` — machine-checked negative result**: in `K_7`, at
  the triangle `C = {0,1,2}` (`JSP90.triple7 0`), the two triangles `{3,4,5}` and `{6,0,1}` both meet
  the boundary of `C` and are disjoint, so **no set of one vertex meets every odd cycle meeting the
  boundary** (`isOddCycle_triple7`, `mem_triple7_three`, `mem_triple7_six`, `inter_triple7_empty`,
  `mem_boundary_triple7`, `not_mem_triple7_six_of_mem_three`).  The constant of the fan statement is
  a genuine parameter and the triangle-free hypothesis is not a formality.  Recorded **but not
  machine-checked** in the file header: the analogous witness *inside* the triangle-free class (a
  `13`-cycle with a `5`-cycle in the fan, `LocIndep 2`), so `n ≥ 2` is expected to be needed there.

### What is *not* proved

`JSP90.TriangleFreeOnly` and hence `JSP90.FanErdős73 f` for any `f`, and hence `jsp_000090_main`.
The blocker is now stated as precisely as it can be without the classical theorem: **the boundary of
a shortest odd cycle of a triangle-free graph can be killed with `f k` vertices**, `f k = O_k(1)`.

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize problems/JSP-000090` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

### Toolchain findings of this round

* **`omega` cannot see through `Finset.card` unless the parity is supplied** — and it *can* treat
  `Finset.card` as an atom, but the goal `C.card = 3` from `3 ≤ C.card` and `C.card < 5` is simply
  **false** (`C.card = 4` is possible); the parity `C.card % 2 = 1` (transported from the cycle) is
  what closes it.  The failure mode is a misleading "no usable constraints";
* `Finset.nonempty_iff_ne_empty` is `Nonempty ↔ ≠ ∅`: `.mp` proves `≠ ∅` **from** a witness and
  `.mpr` extracts a witness **from** `≠ ∅`; `Finset.Nonempty` has **two** fields, so
  `obtain ⟨x, hx⟩ := …` and never `⟨x, hmem, hcard⟩`;
* `DisjointFamily C` unfolds to `∀ X ∈ C, ∀ Y ∈ C, X ≠ Y → X ∩ Y = ∅`; the last argument is the
  **disequality**, and `absurd hXY e` then needs `e : ¬(X ≠ Y)`, i.e. an *equality*, not `X = Y`
  (they are equivalent but not defeq);
* `Finset.card_insert_of_notMem` (capital `M`) is the name at this revision,
  `Finset.card_insert_of_not_mem` does not exist; `Finset.card_pair h : #({x,y} ∪ {y}) = 2`, so
  `2 ≤ #{x, y}` is `(Eq.symm (Finset.card_pair hne)).le`;
* `Finset.disjoint_sdiff_left`, `Finset.inter_eq_empty`, `Finset.not_mem_empty`,
  `Finset.singleton_subset.mpr`, `Finset.Nonempty.elim` do **not** exist at this revision;
  `Finset.eq_empty_iff_forall_notMem` and `Finset.eq_empty_iff_forall_not_mem` do;
* `SimpleGraph.IsBipartite` at this revision is `∃ c : V → Fin 2, ValidColoring c` (not `Bool`); the
  lambda for `ValidColoring` needs `intro x y h` (its two binders are *strict implicit*), and the
  two cases of a 2-colouring by `if x = v then 0 else 1` are closed by `simp [hxv, hynv]`;
* `SimpleGraph.IsClique` takes a **`Set`**, and a *finset* literal at that position is the coerced
  `↑s`, so the membership is unfolded by `Finset.mem_coe` (not by `Set.mem_insert_iff`, which
  applies to a *set* `insert`);
* the `DecidableEq` instance in force in a file is baked into the *finsets* it builds, so a finset
  produced by a lemma of another file (`isOddCycle_image` builds `Finset.image …` with
  Transversal.lean's instance) is **not** syntactically the finset of a `def` in the current file
  even when both are displayed as the same expression: build the structure directly (`⟨m, f, …⟩`)
  when the target finset is a local `def`;
* `interval_cases` is **not** available (the files import Mathlib modules, not `Mathlib`), but
  `omega` proves the disjunction `i.val = 0 ∨ i.val = 1 ∨ i.val = 2` for `i : Fin 3` directly;
* `obtain ⟨…⟩ := h` **clears** `h`, so a hypothesis destructed into components must be copied first
  (`have hC' : IsOddCycle G C := hC`) if it is needed again.

---

## Round 70 — `JSPProblem/Class.lean`: **the classes of the fan, the parity of two classes, and the "no short cut" lemma**

New file `lean/JSPProblem/Class.lean` (29 declarations, 673 lines, **0 sorry/admit**, `lake build` OK
with 1227 jobs), imported from the root module `JSPProblem.lean`.  This is the **twentieth attack
family**, and it attacks the residual statement of round 69 (`JSP90.FanErdős73 f`) on the **class
axis** rather than along a new decomposition axis.

### The gap that is attacked

Round 69 reduced Erdős #73 to a single local statement — the fan statement — and proved the local
structure of the fan at a shortest odd cycle (`card_inter_neigh_le_two`, `shortArc_of_shortest`,
`not_adj_cycSucc_of_adj`, `pairwise_not_adj_fan_of_cliqueFree3`), but the fan was never *named*:
there was no object "the set of fan vertices attached to `a`" and no statement about two such sets.
`policy.json` asked for "the class decomposition of the fan … together with the half-integral
counting".  **Both halves of that are now formalised, and the second one is proved:**

### Part 1 — the classes

`JSP90.fanClass G C a = (boundary G C).filter (G.Adj a)`.  `JSP90.isIndepSet_fanClass` (a class is
independent, being contained in the independent neighbourhood of `a`),
`JSP90.exists_mem_fanClass_of_mem_boundary` (every fan vertex lies in some class),
`JSP90.subset_fanClass_boundary`, `JSP90.mem_fanClass_of_adj`,
`JSP90.subset_fanClass_of_subset_boundary`.

### Part 2 — the parity of two classes

`JSP90.fanColour G a x = if G.Adj x a then 0 else 1` is a proper 2-colouring of any vertex set
covered by two classes (same colour ⟹ both attached to `a`, or both attached to `b`, hence
non-adjacent).  Hence

* **`JSP90.isBipartite_of_subset_fanClass_union`** and
* **`JSP90.not_isOddCycle_of_subset_fanClass_union`: AN ODD CYCLE OF `G` IS NEVER CONTAINED IN TWO
  CLASSES** (parity read off by `JSP90.even_of_cycle_in_bipartition` of round 40), plus
* `JSP90.not_subset_two_fanClass_of_isOddCycle`,
  `JSP90.card_ge_three_of_isOddCycle_of_subset_boundary`.

### Part 3 — the far part, and the counting lemma

`JSP90.farFan G C a b = (boundary G C) \ (fanClass G C a ∪ fanClass G C b)`, with

* **`JSP90.hitsOddCycles_farFan`: the far part meets every odd cycle of `G` contained in the fan**;
* `JSP90.card_le_biUnion_of_disjoint_ne` (a disjoint family of nonempty sets is counted by its
  union) and hence
* **`JSP90.card_farFan_ge_of_disjoint_oddCycles`: a packing of `j` odd cycles inside the fan of `C`
  needs `j` vertices of the far part, for EVERY pair `a, b ∈ C`.**  This is the *shape* of the
  classical half-integral argument, now a Lean theorem;
* **`JSP90.fanErdős73_of_fan_twoClass`, `JSP90.erdos73On_of_fan_twoClass` — a NEW INSTANCE OF THE
  HEADLINE THEOREM along the class axis**: two vertices of `C` covering the fan and hitting every
  odd cycle ⟹ `LocIndep k G → CloseToBipartite (fanBound (fun _ => 2) k) G`.  No packing number,
  no odd girth, no packing weight, no bound on the number of branch vertices.

### Part 4 — the two-vertex arc, and the "no short cut" lemma

`JSP90.arc_isOddCycle` of `JSPProblem/Fan.lean` closes an arc through **one** outside vertex; a fan
edge needs **two**.  New: `JSP90.arcFun2` (the walk `x → y → f i → … → f (cycSucc^[e] i) → x` as a
map `Fin (e + 3) → V`), `arcFun2_zero/one/two/last`, **`JSP90.arcFun2_ne`** (simplicity),
**`JSP90.arcFun2_adj`** (adjacency of consecutive entries), `JSP90.arc_card2`, and

* **`JSP90.arc2_isOddCycle`: closing an EVEN arc through two adjacent outside vertices gives a
  SIMPLE ODD CYCLE of exactly `arc + 3` vertices** — the two-vertex parity core of the fan argument;
* **`JSP90.not_adj_fan_of_far_attach` — THE "NO SHORT CUT" LEMMA**: if `x, y` are distinct vertices
  outside a *shortest* odd cycle, adjacent to each other, with attachment points `f i` and
  `f (cycSucc^[d] i)`, then `d ≤ 3` or `d ≥ m - 3`; equivalently
* **`JSP90.not_adj_of_attach_far`: two fan vertices whose attachment points are `4` to `m - 5`
  steps apart around the cycle are NEVER adjacent.**  No triangle-free hypothesis is used: this is
  a statement about shortest odd cycles in *any* graph.

### What is *not* proved

`JSP90.FanErdős73 f` for any `f`, hence `jsp_000090_main`, which is still **not** declared, so the
harness keeps reporting `missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  The blocker is now stated as: **the
quantitative half of the half-integral argument** — from "the far part is a transversal for every
pair `a, b`" and "adjacent fan vertices are within three steps of each other" to a bound
`t ≤ O_k(1)` on the least transversal of the fan.  Behind it stands `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas).  `formalization.yaml` remains `status: wip`,
`prize_ready: false`.  No award claim is made.

### Environment facts verified this round (they cost most of the round)

* `Finset.nonempty_iff_ne_empty` is `Nonempty ↔ ≠ ∅`; `Finset.not_mem_empty`,
  `Finset.disjoint_sdiff_left`, `Finset.biUnion_subset_of_subset` do **not** exist; use
  `Finset.eq_empty_iff_forall_notMem` and `h ▸ Finset.mem_inter.mpr ⟨h1, h2⟩`;
* `Finset.card_biUnion` and `Finset.card_le_card_of_injOn` do **not** exist at this revision, and
  `Finset.min'` needs a `LinearOrder` instance (so it cannot be used to inject a family of finsets
  into a target finset); the counting step must go through `Finset.biUnion_insert` +
  `Finset.card_union_of_disjoint` (`JSPProblem/Additive.lean`'s `card_biUnion_le_sum` is the other
  direction);
* `SimpleGraph.IsBipartite = Nonempty (G.Coloring (Fin 2))` and `Coloring.mk` takes
  `color` and `valid : ∀ {v w}, G.Adj v w → color v ≠ color w`; `even_of_cycle_in_bipartition`
  needs `IsBipartiteWith s t` (with the graph an explicit argument), so the bipartition must be
  *built* from the colouring, and `Set.mem_sdiff` does not exist — use
  `Set.disjoint_left`/`Set.mem_setOf_eq`;
* `mod_inj_add` is JSP90-local (`JSPProblem/Fan.lean`) with `m a b b'` **all implicit**, so the
  values must be given by name; `omega` treats `x - k` with a *variable* `k` as an opaque atom
  (`Nat.le_sub_of_add_le` / `Nat.sub_succ` / `Nat.add_sub_cancel` are the workarounds), and it CAN
  treat `x - (literal)`;
* `Nat.mod_add_mod (m n k) : (m % n + k) % n = (m + k) % n` — note the argument order, and that
  `rw` needs the `←` direction;
* `SimpleGraph.IsIndepSet s = s.Pairwise (fun v w ↦ ¬ G.Adj v w)`, so the intro pattern is
  `intro x hx y hy hxy` and the goal `¬ G.Adj x y`;
* `Finset.inter_eq_empty`-style rewrites, `Nat.eq_zero_of_lt`, `Nat.eq_of_le`,
  `Finset.biUnion_le_sum`-style names and `obtain` after a `?_`-`refine` all behave differently
  from the older Mathlib: `obtain x := e` in a tactic block can raise a spurious "unexpected
  identifier" parse error — use `rcases e with ⟨…⟩` instead.

---

## Round 72 — `JSPProblem/Book.lean`: the descent at the boundary of an odd cycle (**no separation
hypothesis**) and the **disjoint book** of the fan

New file `lean/JSPProblem/Book.lean` (30 declarations, 700 lines, **0 sorry, 0 admit**, `lake build`
OK with 1228 jobs), imported from the root module `JSPProblem.lean`.  This is the **twenty-first**
attack family.  It does two things, both on the critical path, and **no** Menger, **no** block-cut
tree, **no** connectivity API and **no** new decomposition axis.

### Part 1 — the descent at the boundary, with no separation hypothesis (NEW)

Rounds 59 (`JSPProblem/OffCycle.lean`) and 44 (`JSPProblem/Weight.lean`) proved
`1 + MaxDef G[X] ≤ MaxDef G` for vertex sets `X` **separated** from an odd cycle — the canonical
such set being the outer layer.  The fan `∂C` is in general **not** separated from `C` (that is the
whole point of the fan), so until now no descent was available at the fan.  This round proves it
with **no hypothesis at all**:

* **`JSP90.maxDef_ge_one_add_maxDef_boundary`** — for every odd cycle `C`,

  ```lean
  1 + MaxDef (G[boundary G C]) ≤ MaxDef G
  ```

* **`JSP90.locIndep_boundary`** — `LocIndep k G` + `1 ≤ k` ⟹ `LocIndep (k-1) (G[∂C])`, and
  `JSP90.maxDef_boundary_le`.  This is the induction step of the classical argument at an odd
  cycle, in its most local form, and it is the descent the fan statement of rounds 69–71 needs.
* The ingredients are `JSP90.indepCard_union_le` (`α(G[s ∪ t]) ≤ α(G[s]) + α(G[t])` over a disjoint
  union) and `JSP90.two_indepCard_add_one_le_card_oddCycle` (`2 α(G[C]) + 1 ≤ |C|`).
* The statement is a statement about the **maximum** over `Y ⊆ ∂C`, not about each `Y`: the second
  case of the proof (where `2 α(Y) > |Y|`, so the deficiency truncates at `0`) is exactly why, and
  the docstring records a counterexample to the pointwise version — in the disjoint union of an
  independent triple and a triangle, with `Y` the triple, both `defOf G Y` and `defOf G (Y ∪ C)`
  are `0`.
* **`JSP90.isBipartite_fan_of_locIndep_one'`** is a second, independent route to round 69's
  `JSP90.isBipartite_fan_of_locIndep_one`, now read off `MaxDef = 0 ↔ bipartite`.

### Part 2 — the disjoint book of the fan (NEW)

`JSPProblem/Class.lean` named the *attachment classes* `fanClass G C a`; they **overlap** (a fan
vertex attached to `{c−1, c+1}` is in the classes of both `c−1` and `c+1`).  This round refines them
to a **disjoint** family — the classical "book, not web" picture:

* `JSP90.attachSet`, `JSP90.mem_attachSet`, `JSP90.attachSet_nonempty_of_mem_boundary`;
* **`JSP90.card_attachSet_le_two`** — `|N(x) ∩ C| ≤ 2` stated on attachment **vertices** rather
  than indices (`JSP90.card_inter_neigh_le_two` transferred through `j ↦ f j`);
* **`JSP90.attachSet_eq_singleton_or_pair`**: a fan vertex attaches to a *single* point of `C`, or to
  a *pair* of points **two steps apart** — the classical content of the book, on vertices;
* `JSP90.singleClass G C f i` = the fan vertices whose only attachment point is `f i`, and
  `JSP90.doubleAttach G C` = the fan vertices with two attachment points;
* **`JSP90.mem_singleClass_or_doubleAttach`**, `JSP90.disjoint_singleClass_of_ne`,
  `JSP90.disjoint_singleClass_double` — the fan is the **disjoint** union of the `m` single classes
  and of the double-attachment part;
* `JSP90.subset_singleClass_fanClass`, **`JSP90.isIndepSet_singleClass`** — a single class is
  contained in the attachment class of its own index and is an independent set;
* `JSP90.cycSucc_pow_four_ne` — four steps around a cycle of length ≥ 5 never return to the start
  (the arithmetic behind the disjointness of the double classes).

### Part 3 — the parity of two single classes, and the counting lemma (NEW)

* **`JSP90.not_isOddCycle_of_subset_two_singleClass`: an odd cycle of the fan meets at least three
  single classes.**  The disjoint refinement of round 70's
  `JSP90.not_isOddCycle_of_subset_fanClass_union`; the *disjointness* of the book is exactly what
  is used here.
* **`JSP90.hitsOddCycles_boundary_sdiff_two_singleClass`** — the fan with two single classes removed
  is a transversal of the odd cycles inside the fan.  Because the classes are disjoint, this is a
  **strictly smaller** transversal than round 70's `JSP90.hitsOddCycles_farFan`.
* **`JSP90.card_le_boundary_sdiff_two_singleClass` — the counting lemma of the book**: a packing of
  `j` odd cycles inside the fan of `C` needs `j` vertices outside **every** two single classes, for
  *every* pair of indices `i, j`.  The content is that the bound holds for all `binom m 2` pairs
  simultaneously, which is what forces a transversal of the fan to spread out over the classes.
* **`JSP90.exists_fanTransversal_le_card`** — the explicit form,
  `|S_i| + |S_j| + |Z| ≤ |∂C|` with `Z` the transversal above.

### Part 4 — a new instance of the headline theorem along the book axis

* **`JSP90.fanErdős73_of_fan_singleClassTwo`**, **`JSP90.erdos73On_of_fan_singleClassTwo`**,
  **`JSP90.erdos73_of_fan_singleClassTwo`** — if every odd cycle `C` of a triangle-free `G` has two
  single classes `S_i`, `S_j` of its book whose union is a transversal of all the odd cycles of `G`
  meeting `∂C`, and whose combined size is at most `q`, then `LocIndep k G` forces
  `CloseToBipartite (fanBound (fun _ => q) k) G`, and `Erdős73 k` for every `k`.  The transversal
  now lives **in the fan** and is a union of two *disjoint* pieces of the book, so its size is
  bounded; round 70's instance used a pair of vertices of `C` outside the fan.  No packing number,
  no odd girth, no packing weight, no bound on the number of branch vertices.

### What is *not* proved

`JSP90.FanErdős73 f` for any `f`, and hence `jsp_000090_main`; behind it stands
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas, JCTA-B 2003).  What this round adds is
the descent at the fan (missing until now and required by rounds 59–71) and the *disjoint*
counting system of the book.  Still open: the quantitative half of the half-integral argument
(turning "a transversal of size `t` forces a packing of `≳ t / |C|` odd cycles" into a bound on the
least transversal of the fan), and the odd cycles of `G` that merely *touch* the fan from outside
it, which the class structure does not control.

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 73 — `JSPProblem/Double.lean`: **the double book of the fan, and the critical-cycle counting
in the book** (`|X| ≤ c · (k − 1)`)

### The gap that is attacked

Round 72's policy named two sub-goals.  This round took the first one in full: the
**critical-cycle counting in the book**, i.e. the quantitative half of the half-integral argument.
The tool needed is round 53's minimal-transversal apparatus (`JSPProblem/Critical.lean`), and the
difficulty is that its private cycles are odd cycles *of `G`*, not cycles of the book, so the
counting lemmas of the book do not apply to them.  The fix is to transport the apparatus to the
family of odd cycles **contained in `∂C`**: then the private cycle of `z` is itself a book cycle,
and the packing bound available is `k − 1` (round 69) rather than `k` (round 53).

### Part 1 — the double book (NEW)

`JSP90.doubleClass i` = the fan vertices whose attachment set is exactly the pair
`{f i, f (cycSucc^[2] i)}` — the cells of the two-attachment part, which round 72 could only treat
as one blob.  Three facts, all proved:

* `JSP90.isIndepSet_doubleClass` — **a double class is an independent set** (common-neighbour
  argument, `JSP90.not_adj_of_common_neigh_of_cliqueFree3`);
* `JSP90.inj_pair_twoStep`, `JSP90.cycSucc_pow_four_ne'`, `JSP90.disjoint_doubleClass_of_ne` —
  **the double classes are pairwise disjoint** (four steps around a cycle of length ≥ 5 never return
  to the start);
* `JSP90.disjoint_singleClass_doubleClass`, `JSP90.mem_singleClass_or_doubleClass` — together with
  round 72's single classes, **the fan is a partition into `2m` independent cells**, named
  `JSP90.fanCell G C f i b` with `b : Bool`.

### Part 2 — parity and counting for cells of both kinds (NEW)

`JSP90.not_isOddCycle_of_subset_two_cell`: a fan odd cycle meets at least **three** of the `2m`
cells, now for cells of both kinds (round 72 had it for two single classes).
`JSP90.card_le_boundary_sdiff_twoCell` and `JSP90.exists_fanTransversal_le_card_fanCell`: for
**every** pair of cells, `∂C \ (cell_u ∪ cell_v)` is a transversal of the fan's odd cycles of size
at most `|∂C| − |cell_u| − |cell_v|`, with the mixed and pure two-attachment cases as corollaries.

### Part 3 — a new instance of the headline theorem along the two-cell axis

`JSP90.erdos73On_of_fan_twoCell`: if any two of the `2m` cells, of any combination of kinds, form a
transversal of the fan's odd cycles of combined size `q`, then `LocIndep k G` forces
`CloseToBipartite (fanBound (fun _ => q) k) G`.  This **strictly subsumes** round 72's instance,
which could not use a double class.

### Part 4 — the critical-cycle counting in the book (NEW; round 72's concrete next lemma)

* `JSP90.MinimalFanTransversal` = a minimal transversal of the odd cycles **contained in** `∂C`
  (`JSP90.exists_minimalFanTransversal` by round 53's finitary argument applied to
  `JSP90.boundary_hits_fanOddCycles`);
* `JSP90.exists_criticalFanTransversal_of_minimal`: for each `z ∈ X` there is an odd cycle `D_z` of
  `G` **contained in `∂C`** with `D_z ∩ X = {z}`;
* `JSP90.criticalFanCycle_structure`: `D_z` is a book cycle and is not contained in any two cells;
* `JSP90.FanIntGraph` + `JSP90.fanDisjoint_of_colour_eq`: inside one colour class the critical
  cycles are pairwise vertex-disjoint, hence a family of odd cycles **inside** `∂C`;
* `JSP90.card_fanTransversal_le_of_colouring`: **`|X| ≤ c · (k − 1)`** — round 53's counting with the
  fan packing bound `JSP90.oddCycleFamily_card_le_of_boundary` in place of the global `k`, a strict
  improvement; `JSP90.card_fanTransversal_le_one` is the `c = 1` case `|X| ≤ k − 1`.

### Part 5 — the remaining statement, isolated

`JSP90.FanCriticalErdős73 c` requires, for every `C`, a minimal transversal `X` of the odd cycles
inside `∂C` whose critical intersection graph is `c`-colourable **and** which meets every odd cycle
that *touches* `∂C`; `JSP90.erdos73_of_fanCritical` then derives `Erdős73 k` for every `k`, with the
explicit constant `fanBound (fun j => c * (j − 1)) k`.

### What is *not* proved

Two things, both stated as hypotheses rather than assumed away:

1. **The colouring.**  No bound on the chromatic number of `JSP90.FanIntGraph` in terms of `k` is
   proved.  Everything downstream of it *is* proved, so this is the single remaining input of the
   counting half.
2. **The touching property.**  `JSP90.FanErdős73` asks for a set meeting every odd cycle `D` with
   `D ∩ ∂C ≠ ∅`, while a minimal transversal of the odd cycles *contained* in `∂C` need not meet a
   cycle that only touches the boundary.  Round 72's sub-goal (2) is therefore **not** solved; the
   property is the last conjunct of `JSP90.FanCriticalErdős73`.

`jsp_000090_main` is still **not** declared (`missing_theorems = ["jsp_000090_main"]`);
`score.py` reports `build_ok = true, sorry = 0, admit = 0, partial_ok = true`, and `#print axioms`
on the new headline results shows only `[propext, Classical.choice, Quot.sound]`.  `prize_ready`
remains `false`; no award claim is made.

---

## Round 74 — `JSPProblem/Touch.lean`: the **TOUCHING AXIS** (attack family 23)

New file `lean/JSPProblem/Touch.lean` (32 declarations, 0 sorry/admit, `lake build` OK with 1230
jobs), imported from the root module `JSPProblem.lean`.

### The gap that is closed

Rounds 72–73 isolated the remaining statement as `JSP90.FanCriticalErdős73 c`
(`lean/JSPProblem/Double.lean`), which has **two** conjuncts:

1. a minimal transversal `X` of the odd cycles **contained in** `∂C` whose critical intersection
   graph is `c`-colourable; and
2. the **touching property**: `X` meets every odd cycle of `G` that **meets** `∂C`.

Round 73 recorded conjunct 2 as *not automatic* — a minimal transversal of the contained cycles need
not meet a cycle that only touches the boundary — and left it as an open secondary lemma, because
minimality of the *contained* family says nothing about the touching family.

**Round 74 removes that conjunct by changing the family, not by proving it.**  Working with a
minimal transversal of the *touching* family instead, the touching property is the **definition** of
the family being hit:

* `JSP90.Touches G C D := D ∩ boundary G C ≠ ∅`, `JSP90.HitsTouching G C X`,
  `JSP90.MinTouching G C X`;
* `JSP90.hitsTouching_boundary` (`∂C` itself is a transversal of the touching family),
  `JSP90.exists_minTouching_of_transversal`, `JSP90.exists_minTouching`,
  `JSP90.eq_of_touchTransversal_of_minimal`;
* **`JSP90.exists_criticalTouchCycle_of_minimal`** — for every `x` of a minimal transversal `X` of
  the touching family there is an odd cycle `D` with `Touches G C D` and `D ∩ X = {x}`.  This is
  the statement round 73 could not make: `JSP90.exists_criticalFanCycle_of_minimal` produces a
  critical cycle *contained in* `∂C`, this one *touches* `∂C`;
* `JSP90.TouchCritical`, `JSP90.exists_criticalTouchTransversal_of_minimal`;
* **`JSP90.minTouching_hits`** — a minimal transversal of the touching family meets every odd cycle
  meeting `∂C`, *by definition*.  Round 73's second conjunct is discharged.

### The price, and the counting

The critical cycles are no longer known to lie in `∂C`, so (i) the packing bound available is `k`
rather than round 73's `k − 1`, and (ii) the cell structure of `JSPProblem/Double.lean` no longer
applies to them.  Everything else is transported:

* `JSP90.TouchInt X crit`, `JSP90.TouchIntGraph d`, `JSP90.touchDisjoint_of_colour_eq`;
* **`JSP90.card_critTransversal_le_of_colouring_pack`** — the counting lemma in its general form
  (a set `X` carrying critical cycles, a packing bound `r`, a proper `c`-colouring of the critical
  intersection graph ⟹ `|X| ≤ c * r`), separated from the data structure so that it serves both
  families;
* `JSP90.card_touchTransversal_le_of_colouring_pack`, `card_touchTransversal_le_of_colouring`
  (`|X| ≤ c * k`), **`card_touchTransversal_le_one`** (`c = 1`, the classical shape `|X| ≤ k`).

### The remaining statement, with ONE conjunct instead of two

* `JSP90.TouchColourable H c` — "`H` is `c`-colourable", as a `Prop`;
* **`JSP90.TouchCriticalErdős73 c`** — for every triangle-free `G` with `LocIndep k G` and every odd
  cycle `C`, a minimal transversal `X` of the touching odd cycles with critical data `d` such that
  the critical intersection graph of `d` is `c`-colourable and `X.card ≤ c * k`.  **No touching
  conjunct**: it is the definition of the family;
* `JSP90.fanErdős73_of_touchCritical` (`f k = c * k`), `JSP90.erdos73On_of_touchCritical`
  (`fanBound (fun _ => c * k)`), **`JSP90.erdos73_of_touchCritical`** (Erdős #73 in full);
* **`JSP90.TouchCriticalErdős73.of_fanCritical`** — round 73's `JSP90.FanCriticalErdős73 c` implies
  this round's statement: take a minimal transversal of the touching family *inside* round 73's `X`
  (it is smaller, `hX'`), transport the critical data, and the fan packing bound `c * (k − 1) ≤ c * k`
  covers the size.  **The two statements are the same missing lemma**; round 73's extra conjunct was
  an artefact of choosing the wrong family of odd cycles.

### A new instance of the headline theorem on the DEGREE axis

* `JSP90.EdgelessOutside G m` — there is `H` with `|H| ≤ m` and **no edge of `G` with both ends
  outside `H`** (a hypothesis about the degree distribution of `G` alone);
* `JSP90.hitsOddCycles_of_edgelessOutside` — every odd cycle carries an edge, so every odd cycle
  meets `H`;
* `JSP90.closeToBipartite_of_edgelessOutside`, and
  **`JSP90.erdos73On_of_edgelessOutside (m k)`**: `LocIndep k G` + `EdgelessOutside G m` ⟹
  `CloseToBipartite m G` — the constant `m` does not involve `k`, and beats round 38's `m + k` on
  this (narrower) class;
* **`JSP90.erdos73On_of_bounded_neighbourhood k`**: all of `G`'s edges touch a set of at most `k`
  vertices ⟹ `CloseToBipartite k G`, a constant that is a function of Erdős's parameter alone.  No
  bound on the odd girth, on the packing number, on the packing weight or on the number of branch
  vertices.

### What is *not* proved

`JSP90.TouchCriticalErdős73 c` for some `c` — that the critical intersection graph of a minimal
transversal of the touching odd cycles has **bounded chromatic number in terms of `k` alone**.
Behind it stands `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas, JCTA-B 2003).  No
colouring bound is claimed or assumed anywhere, and the touching property is neither assumed nor
smuggled in.

`jsp_000090_main` is deliberately **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `harness/score.py problems/JSP-000090` reports
`build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true`, and
`#print axioms` on every new headline result shows only
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.  `prize_ready` remains `false`; no award
claim is made.

### Environment notes (each cost several build iterations)

* A `def` whose parameters are taken from a `variable` block has them **implicit**; if the parameter
  is only mentioned inside the body (`EdgelessOutside`, `boundary G C` inside `Touches`) it must be
  declared **explicitly** (`(G : SimpleGraph V) (m : ℕ)`), otherwise the use sites cannot infer it;
* `by_cases h : s = ∅` gives `h : s = ∅`, which is *not* a function; to refute it from a witness use
  `Finset.not_nonempty_iff_eq_empty.mpr h` (the pattern used throughout `JSPProblem/Double.lean`),
  not `by_contra` (which yields the double negation);
* `by_contra` on `x ∈ s` gives `h : ¬ (x ∈ s)`, so it cannot be fed to anything expecting `x ∈ s`;
  use `by_cases` when the hypothesis is needed positively in the other branch;
* `⟨_, _⟩` does not elaborate for `a ∈ s ∩ t` or for goals mentioning a `Finset` built with a
  `Classical.decEq` instance: introduce the `And` with a `have h : a ∈ s ∧ a ∈ t := ⟨_, _⟩` and then
  apply `Finset.mem_inter.mpr h`;
* `Finset.ne_empty_of_mem` is more robust than `ne_inter_of_mem` when the two finsets are not both
  syntactically fixed;
* `Ne` in `Ω`-unfriendly positions: `Nat.mul_le_mul_left c (Nat.sub_le _ _)` proves
  `c * (k - 1) ≤ c * k` (`omega` cannot, because `k - 1` is opaque to it);
* `Fin` of an unknown length has **no `OfNat (Fin m) 0` instance** at the pinned revision: write
  `have h0 : Fin m := ⟨0, by omega⟩` instead of `(0 : Fin m)`.

---

## Round 76 — the deficiency-one axis, and the improved lower bound `f(k) >= 2 k`

New file `lean/JSPProblem/Petersen.lean` (24th attack family, 47 declarations, 631 lines, 0 sorry,
0 admit).  The witness is **`p9`, the Petersen graph with one outer vertex deleted** — nine
vertices, twelve edges, triangle-free (the outer path `0-1-2-3`, the four spokes `0-5`, `1-6`,
`2-7`, `3-8`, and the inner star `4-6-8-5-7-4`).

### What is proved

| result | content |
|---|---|
| `JSP90.locIndep_one_p9` | `LocIndep 1 p9`: the maximum deficiency of `p9` is at most one (exhaustive decision over the 512 vertex sets) |
| `JSP90.not_locIndep_zero_p9` | its deficiency is **exactly** one (so `LocIndep 0 p9` fails) |
| `JSP90.triangleFree_p9` | `p9` has no triangle: the improved lower bound already holds in the triangle-free class of rounds 61-74 |
| `JSP90.exists_oddCycle_av`, `exists_oddCycle_data_av` | every vertex of `p9` is avoided by one of four explicit 5-cycles `Ca, Cb, Cc, Cd` |
| `JSP90.isOddCycle_delete_cyc5`, `exists_oddCycle_delete_av` | the residue of `p9` at any single vertex still carries an odd cycle |
| `JSP90.not_closeToBipartite_one_p9` | no single vertex meets every odd cycle of `p9` |
| `JSP90.closeToBipartite_two_p9` | `{2, 6}` meets every odd cycle, with the explicit 2-colouring `{0,7,8} \| {1,3,4,5}` of the residue — the least odd cycle transversal of `p9` is **exactly two** |
| `JSP90.p9Family`, `p9Fibre`, `mem_p9Fibre`, `card_p9Fibre`, `p9Fibre_disjoint`, `pairwiseDisjoint_fibre_pieces`, `inter_biUnion_fibre` | the disjoint union of `k` copies on `Fin 9 x Fin k` and its fibres |
| `JSP90.locIndep_p9Family` | `LocIndep k (p9Family k)`, by fibre-wise counting (`2 |I_i| + 1 >= |X cap fibre i|` summed over the `k` disjoint fibres) |
| `JSP90.isOddCycle_p9Family_cyc5`, `isOddCycle_p9Family_Ca` | a 5-cycle of `p9` inside a fibre is an odd cycle of `p9Family k` |
| `JSP90.card_inter_fibre_two`, `card_le_two_k_of_hitsOddCycles` | every odd cycle transversal of `p9Family k` meets each fibre in at least two vertices, so `2 * k <= |X|` |
| `JSP90.closeToBipartite_p9Family_two`, `closeToBipartite_p9Family_iff` | **`CloseToBipartite m (p9Family k) <-> 2 * k <= m`** — the exact value of the conclusion on that class |
| **`JSP90.erdos73_lower_bound_two`, `JSP90.no_constant_below_two_k`** | **`f(k) >= 2 k`**: for every `k` and every `m < 2 k` there is a finite graph with `LocIndep k G` and `not CloseToBipartite m G`.  This **strictly improves** `JSPProblem/Sharp.lean`'s `JSP90.erdos73_lower_bound` (`f(k) >= k`) |

Nothing is assumed: the only hypothesis used is Erdős's `LocIndep`, the witness is explicit, and
`#print axioms` on each of the results above shows only
`[propext, Classical.choice, Quot.sound]` (the two `decide` proofs are kernel `of_decide_eq_true`, so
neither `sorryAx` nor `Lean.ofReduceBool` appears).

### How the lower bound was found

An exhaustive search over all graphs on `n <= 7` vertices (in C, `2^21` graphs for `n = 7`) shows that
`max { tau(G) : MaxDef G <= 1 } = 2` for `n <= 7`; the Petersen graph has `MaxDef 2, tau 3`, and
deleting any vertex of it gives `MaxDef 1, tau 2`.  Random search up to `n = 8` found nothing with
`tau >= 3` at deficiency one, so the expected sharp value of the `k = 1` case is `2`.

### Status

`lake build` OK (1231 jobs); `harness/score.py problems/JSP-000090` reports
`build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true`,
`missing_theorems = ["jsp_000090_main"]`.  The headline theorem (the full statement for all `k`) is
still open — the missing input is unchanged, `JSP90.OddCycleErdosPosa r` for all `r`, equivalently
`JSP90.TouchCriticalErdos73 c` for some `c` (round 74).  `prize_ready` remains `false`.

### Environment notes (each cost several build iterations)

* `LocIndep`, `CloseToBipartite` and `HitsOddCycles` are *instance-free* in their statements, so
  `decide` works on them directly, but any statement that mentions a **finset literal** is not:
  `C n X` and the like freeze the `DecidableEq` of the importing file (`Transversal.lean` installs
  `Classical.decEq V`, whose auto-generated name shows up as `instDecidableEq_jSPProblem_2` in
  error messages).  To apply such a hypothesis one must build it with the same instance, e.g.
  `@Inter.inter (Finset _) (@Finset.instInter _ (Classical.decEq _)) s t = empty`;
* `Finset.image` and `Finset.inter` depend *computationally* on the `DecidableEq` instance (the
  deduplication), so two finsets of the same vertex set built with different instances are not
  defeq — mix one instance per file, and use `Finset.card_biUnion` / `Finset.card_image_iff` rather
  than rewriting a sum into a card;
* `SimpleGraph.IsIndepSet s` is `s.Pairwise (fun v w => not G.Adj v w)`, i.e. six binders
  (`v`, `v in s`, `w`, `w in s`, `v != w`, `not Adj v w`); `intro v hv w hw hvw hne` is the shape to
  use, and `intro` **pushes negations in**, so naming the last binder yields a *positive* `Adj`
  hypothesis;
* `IsBipartite G` is `Colorable 2 G` and has **no `Decidable` instance**; for a finite graph the
  search over the 2-colourings can be run with
  `decidable_of_iff (exists d : V -> Fin 2, forall v w, G.Adj v w -> d v != d w) ...`;
* `decide` needs a *computable* `DecidableEq`, so `Classical.decEq` (the convention of the imported
  lemmas) must be replaced by a `local instance` for the file; `haveI` inside a proof is not enough
  for `Finset.univ` enumerations of `Finset`s;
* `Finset.mem_product` is `p in s x*s t <-> p.1 in s and p.2 in t` (Mathlib at this revision), while
  the `Set` version of a product needs `Set.mem_prod` — mixing them fails;
* `Finset.card_image_of_injective` needs injectivity on the **whole** type, not just on the image, so
  for `image Prod.fst` on a fibre use `Finset.card_image_iff.mpr` (`InjOn`).

---

## Round 77 — `JSPProblem/Layer.lean`: the **INTERNAL-DEGREE axis**, and the bounded-degree
localisation of the missing input

New file `lean/JSPProblem/Layer.lean` (**25th attack family**: 40 declarations, 565 lines, **0
placeholders**, `lake build` OK with 1232 jobs), imported from the root module `JSPProblem.lean`.

### The new axis

Rounds 38 and 74 both control the **total** degree of `G`:

* `JSP90.erdos73On_of_bounded_branch` — the branch vertices of the residue `G - B` all lie in a set
  `B` of at most `m` vertices ⟹ `CloseToBipartite (m + k) G`;
* `JSP90.erdos73On_of_localDegreeOutside` / `erdos73On_of_edgelessOutside` — at most `m` vertices
  carry all the degree ⟹ `CloseToBipartite m G`.

This round replaces the total degree by the **internal degree**: `JSP90.InternalDegree G S r` says
only that every vertex outside `S` has at most `r` neighbours **outside `S`**.  A vertex of
arbitrarily large total degree is free as soon as all its neighbours lie in `S`, so the hypothesis
is strictly weaker than either of the two above.  With it:

| result | content |
|---|---|
| `JSP90.Neigh`, `OuterNeigh`, `InnerDeg`, `MaxDeg`, `MaxDegLe`, `InternalDegree` | the notions (the pinned slice exports neither `SimpleGraph.neigh` nor `SimpleGraph.degree`, so both are defined here) |
| `JSP90.two_le_innerDeg_of_mem_oddCycle` | **a vertex of an odd cycle avoiding `S` has internal degree ≥ 2** (its two cycle-neighbours are distinct and lie in `C`) |
| `JSP90.hitsOddCycles_of_internalDegree_one`, `closeToBipartite_of_internalDegree_one` | the level `r ≤ 1`: `S` meets every odd cycle, so `G` is `|S|`-close to bipartite |
| **`JSP90.erdos73On_of_internalDegree_three`** | **A NEW INSTANCE OF THE HEADLINE THEOREM**: internal degree `≤ 3` off `S` ⟹ `LocIndep k G → CloseToBipartite (\|S ∪ OuterBranch G S\| + k) G`, where `OuterBranch G S` are the vertices outside `S` that are branch vertices of `G - S`.  No bound on the odd girth, the packing weight or the number of branch vertices of `G` |
| `JSP90.erdos73On_of_internalDegree_three_le` | the same with the convenient constant `\|S\| + \|OuterBranch\| + k` |
| `JSP90.branchVertex_mem_of_internalDegree_two`, `erdos73On_of_internalDegree_two` | the level `r = 2` **is** round 38's instance (`branchVertex_mem_of_internalDegree_two` machine-checks the direction that identifies the two hypotheses), so the ladder `r = 0, 1, 2, 3` is complete and the `r = 3` level is the first that is new |
| `JSP90.internalDegree_kTriangles`, `outerBranch_kTriangles`, `no_constant_below_internalDegree_three` | the `k`-term is **exactly sharp**: `kTriangles k` satisfies the hypothesis with `S = ∅`, has `OuterBranch = ∅`, and its least odd cycle transversal has exactly `k` elements |

### A new named missing statement, and the reduction that consumes it

* **`JSP90.BoundedDegreeErdős73 g r`** — "every graph of maximum degree at most `r` satisfying
  `LocIndep k` is `g r k`-close to bipartite";
* `JSP90.maxDegLe_deleteFinset_of_internalDegree` — the residue of an internal-degree hypothesis
  has the corresponding maximum degree;
* **`JSP90.erdos73On_of_internalDegree_of_boundedDegree`** — *the levels of this family are
  equivalent to that statement*: `BoundedDegreeErdős73 g r` forces
  `CloseToBipartite (m + g r k) G` under the internal-degree-`r` hypothesis off a set of at most
  `m` vertices;
* `JSP90.erdos73On_boundedDegree_zero` (the level `k = 0` is free — it is `JSP90.erdos73On_zero`) and
  `JSP90.boundedDegreeErdős73_two` (the level `r = 2` is round 38's instance);
* **`JSP90.SubcubicErdős73 g`** — **the first time the development names the *bounded-degree* case of
  Erdős–Pósa for odd cycles as the missing input**: every graph of maximum degree at most `3` with
  `LocIndep k` is `g k`-close to bipartite.  It is strictly weaker than
  `JSP90.OddCycleErdosPosa r`, and `JSP90.erdos73On_of_subcubic` /
  `JSP90.erdos73On_of_internalDegree_of_subcubic` are the two reductions that consume it.  The
  parameter is genuine: the Petersen graph has maximum degree `3`, `MaxDef 2` and transversal
  number `3`, so any admissible `g` satisfies `g 2 ≥ 3`.

### A **tight witness** of the maximum deficiency

* `JSP90.Tight G X` (`|X| = 2 * α(G[X]) + MaxDef G`), `JSP90.defOf_eq_maxDef_of_tight`;
* **`JSP90.exists_tight_of_maxDef_ne_zero`** — as soon as `MaxDef G ≠ 0` a tight witness exists: the
  witness of `JSP90.exists_eq_maxDef` cannot have truncated;
* **`JSP90.indepCard_add_one_of_notMem_of_tight`** — **adding any single vertex outside a tight
  witness raises `α` by exactly one**, i.e. no vertex outside a maximum-deficiency witness is
  blocked by the largest independent set of the witness; and
  `JSP90.defOf_sub_one_of_notMem_of_tight`, its deficiency form.

The linear form of `Tight` is *necessary*: `defOf` is a truncated subtraction, so in `K_2` with
`X = {a}` one has `defOf G X = 0 = MaxDef G` but `α(G[X ∪ {b}]) = α(G[X]) = 1`.  This is a
machine-checked obstruction to the more attractive formulation and is recorded in the file header.

### Three attack routes examined and closed this round

1. **The overlap of two odd cycles.**  The tempting counting argument "if two odd cycles share an
   edge then their union has deficiency `≥ |C ∩ D|`" is **false**: the diamond `K_4` minus an edge
   has two triangles sharing an edge and maximum deficiency `1`.  The reason is structural:
   `α(G[C ∪ D])` can be `α(C) + α(D)`, because an independent set may avoid the intersection
   entirely, so no saving is available from the overlap.
2. **Averaging over random 2-colourings** (`τ(G) ≤ Σ_{v ∈ B} 2^{-deg v}`, `B` = vertices on odd
   cycles).  Useless: in the *friendship graph* of `t` triangles sharing one vertex, `MaxDef = 1`,
   `τ = 1` and `Σ_{v ∈ B} 2^{-deg v} ≥ t / 2`, which is unbounded.
3. **The matching reformulation** of Erdős's hypothesis (`α(G[X]) ≥ (|X| - k)/2` ⟺ every induced
   subgraph has matching number at most `(|X| + 1)/2`, by Gallai's theorem).  Not available: the
   pinned Mathlib revision has **no `matchingCard` and no Gallai theorem** (`α + ν = |V|`) anywhere
   in the source tree, and `Mathlib/Combinatorics/SimpleGraph/Matching.lean` is not even in the
   prebuilt object slice, so importing it would mean rebuilding part of Mathlib.

### Environment notes (each cost several build iterations)

* the pinned slice exports **neither `SimpleGraph.neigh` nor `SimpleGraph.degree`**, and
  `SimpleGraph.mem_neigh` does not exist: `Neigh`, `MaxDeg` and `mem_neigh` are defined here
  (`neigh` is *also* absent from `Mathlib/Combinatorics/SimpleGraph/Matching.lean`'s imports);
* `Finset.card_eq_zero` is an **iff** here (`s.card = 0 ↔ s = ∅`), so it must be used as `.mpr`;
* `Finset.not_mem_empty` does not exist at this revision: use `by simp` or
  `Finset.eq_empty_iff_forall_notMem.mpr`;
* `Finset.mem_union_left` takes **both** sets explicitly (`Finset.mem_union_left s t h`), so
  `Finset.mem_union_left _ h` mis-assigns; `Finset.mem_union.mpr (Or.inl h)` is the robust form;
* `Nat.le_add_right n k : n ≤ n + k` and `Nat.le_add_left` are the usable forms;
  `Nat.le_sub_iff_add_le (h : n ≤ m) : k ≤ m - n ↔ k + n ≤ m` takes the order hypothesis first;
  `Nat.sub_pos_iff_lt : 0 < n - m ↔ m < n` and `Nat.sub_add_cancel (h : m ≤ n) : n - m + m = n` are
  the two lemmas that convert a truncated subtraction into linear inequalities;
* `omega` **cannot** prove `2 * b ≤ a` from `b ≤ a` when `b` is an application of a `noncomputable
  def` (it tries to unfold `indepCard`): use `Nat.mul_le_mul_left 2 h`;
* a `def` whose statement quantifies over `Type u` with `u` declared by `universe u` gets **no**
  universe parameter (a universe *metavariable* error); write `def Foo.{v} ...` with a fresh name
  and annotate the use sites.

### What is *not* proved

`JSP90.SubcubicErdős73 g` for some `g` — the level `r = 3` of
`JSP90.BoundedDegreeErdős73`, equivalently the packing-number bound for graphs of maximum degree
`3`.  Behind it stands `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged
primary blocker.

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `harness/score.py problems/JSP-000090` reports
`build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true`.
`#print axioms` on each of the thirteen headline results of the new file shows only
`[propext, Classical.choice, Quot.sound]`.  `formalization.yaml` remains `status: wip`,
`prize_ready: false`.  No award claim is made.

---

## Round 78 — `JSPProblem/Subcubic.lean`: the **SUBCUBIC axis**, the even cover of a cycle, and the `k = 1` instance

New file `lean/JSPProblem/Subcubic.lean` (26th attack family, 33 declarations, 621 lines, **0
sorry / 0 admit**, `lake build` OK with 1233 jobs), imported from the root module
`JSPProblem.lean`.

### What is proved

| result | content |
|---|---|
| `JSP90.card_le_one_outerNeigh_oddCycle` | a vertex of an odd cycle of a subcubic graph has at most **one** neighbour outside the cycle |
| `JSP90.card_boundary_le_card_oddCycle`, `JSP90.card_neighClosed_le_two_mul_card_oddCycle` | `\|∂C\| ≤ \|C\|` and `\|N[C]\| ≤ 2 \|C\|`: **the fan of a shortest odd cycle of a subcubic graph is a finite object of controlled size** |
| `JSP90.card_le_two_outerNeigh_boundary` | a fan vertex has at most two neighbours outside `C` |
| **`JSP90.CycleOrder.exists_adj_mem_inter`** | **two odd cycles of a subcubic graph that meet share a *cycle edge* of the first** (two `2`-subsets of the three edges at a common vertex always intersect; the shared edge is an edge of the cyclic order, not a chord) |
| `JSP90.exists_ne_two_mem_inter_oddCycle` | hence the intersection of two meeting odd cycles has at least two vertices |
| `JSP90.evenIdx`, `JSP90.evenCover`, `JSP90.exists_mem_evenCover_of_cycleEdge`, `JSP90.card_evenCover` | for a cycle of odd length `m`, the `⌈m/2⌉` vertices at **even positions** meet every edge of the cycle, and there are at most `(m + 1) / 2` of them |
| **`JSP90.hitsOddCycles_of_inter`** | **if every odd cycle of a subcubic graph meets one fixed odd cycle `C`, then some set of at most `(C.card + 1) / 2` vertices of `C` meets every odd cycle of `G`** |
| `JSP90.oddEvenCover`, `JSP90.inter_oddEvenCover_of_isOddCycle` | the same, phrased per finset (the even cover of the *chosen* cyclic order; `Classical.choose` on `∃ o, o.m % 2 = 1` only, no `Finset` of cyclic orders) |
| **`JSP90.closeToBipartite_of_subcubic_of_shortOddCycles`** | **A NEW INSTANCE OF THE HEADLINE THEOREM**: subcubic + `LocIndep k` + every odd cycle has at most `ℓ` vertices ⟹ `CloseToBipartite (k * ((ℓ + 1) / 2)) G`, improving round 19's `ℓ * k` on the subcubic class. No bound on the packing weight, the odd girth, or the number of branch vertices |
| `JSP90.closeToBipartite_of_subcubic_of_locIndep_one_of_shortOddCycle` | the `k = 1` case, whose constant does not mention `k` |
| `JSP90.closeToBipartite_of_subcubic_of_locIndep_one_of_three` | every odd cycle of `G` is a triangle ⟹ `CloseToBipartite 2 G`: the **sharp** `k = 1` subcubic constant |
| `JSP90.maxDegLe_p9`, **`JSP90.subcubic_constant_ne_one`**, `JSP90.not_subcubicErdős73_one` | **`p9` is subcubic, so the constant `1` at `k = 1` is impossible**: round 77's sub-goal (1) is **refuted**; any admissible `g` of `JSP90.SubcubicErdős73` satisfies `g 1 ≥ 2` |
| `JSP90.inter_oddCycle_of_locIndep_one` | `LocIndep 1` ⟹ every two odd cycles meet (the packing bound for the family `{C, D}`) |
| `JSP90.SubcubicPackingOne`, `JSP90.erdos73On_subcubic_one_of_packingOne` | **the remaining statement, isolated and not assumed**: in a subcubic graph whose odd cycles pairwise meet, two vertices meet all of them |
| `JSP90.erdos73On_one_of_maxDegLe_two` | the `MaxDeg ≤ 2` level in the *total*-degree vocabulary: `LocIndep 1` + no degree `≥ 3` ⟹ `CloseToBipartite 1 G` (round 77's `boundedDegreeErdős73_two` with the set `B` and the branch-vertex count removed) |

`#print axioms` on all nineteen headline results shows only
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

### Computational finding behind Part 5 (not assumed, only recorded)

Exhaustive enumeration of **all** subcubic graphs on `≤ 8` vertices (`10 355 376` of them): the
largest odd cycle transversal number among graphs of maximum deficiency `≤ 1` is `2`; `1540` of the
graphs have transversal number `≥ 3` and **none** of those has packing number `1`; random search
up to `13` vertices found no counterexample to "subcubic + every two odd cycles meet ⟹
transversal number `≤ 2`".  Hence `JSP90.SubcubicPackingOne` is the correct candidate, and the
sharp value of the `k = 1` subcubic constant is `2` (`p9` attains it).

### What is *not* proved

`JSP90.SubcubicPackingOne` — the bounded odd girth hypothesis of Part 4 is **not** removable by the
argument above: without it the even cover of `C` has `(m + 1) / 2` vertices with `m` the odd
girth, and no argument here bounds the transversal without the girth bound.  Behind it stands
`JSP90.SubcubicErdős73 g` and, further back, `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–
Thomas).  A subcubic graph of maximum deficiency `1` and transversal number `3` would refute
`SubcubicPackingOne`; none exists up to `8` vertices.

`jsp_000090_main` is deliberately **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `harness/score.py problems/JSP-000090` reports
`build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true`.
`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.

### Environment notes (each cost several build iterations)

* `Finset.card_image_of_injective` takes the finset **first** in this Mathlib revision; named
  arguments `(s := …) (f := …)` are the safe form (`Finset.card_image_of_injective _ h` misplaces
  both arguments);
* `Finset.nonempty_iff_ne_empty : s.Nonempty ↔ s ≠ ∅`, so a hypothesis written `s ≠ ∅` (i.e.
  `Not (s = ∅)`) is turned into a witness with `.mpr`, and a `Nonempty` with `.mp`; and
  `Finset.mem_biUnion.mp`/`Finset.mem_inter.mp` need a *membership*, not a `Nonempty` — go through
  `Finset.nonempty_iff_ne_empty` first;
* `rcases h with …` (and `obtain`) **clears** `h`, so a nested `rw [Finset.mem_insert] at h` on the
  same hypothesis fails; restructure with `intro … ; rw [Finset.mem_insert, …] at hx ; rcases hx`;
* `rw [h, ← k]` in one command does not chain as expected when the second rewrite targets a
  subterm introduced by the first; split into two `rw`s;
* `by_cases hCD : C = D` with a `Ne` hypothesis: `rw [hCD]` rewrites as if the proof were an
  equation (it rewrote `C` into `D`); use `subst hCD`;
* `ω` treats a hypothesis of the form `(fun t => 2 * t) a = (fun t => 2 * t) b` as *opaque*: first
  `have h' : 2 * a = 2 * b := by simpa using h` and then `ω`; and `Nat.mul_right_cancel` at this
  revision has signature `(n) (h : 0 < n) …`, so it does not apply to a plain equation;
* `¬ p` is `p → False`, so to refute a hypothesis `h : P` with `¬ P` the *negation* must be applied
  to `h` (`not_... (h …)`); writing `h … not_...` asks Lean to apply a `Prop`;
* `dif`/`dite` on `IsOddCycle G D` needs a `Decidable (IsOddCycle G D)` instance — the pinned
  Mathlib slice does not provide one, and `Classical.propDecidable` must be declared locally;
* `cycSucc` is the JSP90-local `⟨(i.val + 1) % n, _⟩` of `JSPProblem/OddCycle.lean`, with
  `cycSucc_val` a simp lemma, and `Fin.even_iff` does **not** exist at this revision: work with
  `Even i.val` and `even_iff_two_dvd` / `dvd_def` instead.

---

## Round 80 (`lean/JSPProblem/Cover.lean`) — the **SHARED-EDGE axis**: attack family 27

New module, 44 declarations, 687 lines, 0 `sorry`, 0 `admit`; `lake build` OK (1234 jobs);
`harness/score.py`: `build_ok=true, sorry=0, admit=0, placeholder_total=0, partial_ok=true,
missing_theorems=['jsp_000090_main']`.

### What was proved

1. **A degree-free hypothesis replacing round 78's degree bound.**  `JSP90.ShareCycleEdge G`: two odd
   cycles of `G` that meet share a *cycle edge* of the first, in every cyclic ordering.  Every graph of
   maximum degree `≤ 3` satisfies it
   (`JSP90.ShareCycleEdge.lemma_of_maxDegLe_three`, from round 78's `CycleOrder.exists_adj_mem_inter`),
   so the hypothesis is weaker than subcubicity; the structural content is
   `JSP90.exists_ne_two_mem_inter_of_shareCycleEdge`.
2. **A NEW INSTANCE of the headline theorem, with no degree bound.**
   `JSP90.erdos73On_of_shareCycleEdge_of_shortOddCycles`:
   `ShareCycleEdge G → LocIndep k G → (odd girth ≤ ℓ) → CloseToBipartite (k * ((ℓ + 1) / 2)) G`
   (constant of round 78, better than the general `ℓ * k` of `erdos73On_of_bounded_odd_girth`, under a
   strictly weaker hypothesis), plus the `k = 1` level
   (`JSP90.closeToBipartite_of_shareCycleEdge_of_shortOddCycle_one`), the `ℓ = 3` level
   `CloseToBipartite (2 * k) G` (`JSP90.closeToBipartite_of_shareCycleEdge_of_three`,
   `JSP90.erdos73On_shareCycleEdge_of_three`) and the containment of round 78's instance
   (`JSP90.closeToBipartite_of_maxDegLe_three_of_shortOddCycles`).
3. **THE PACKING-NUMBER-ONE CASE, WITH NO LOCAL HYPOTHESIS.**
   `JSP90.closeToBipartite_of_shareCycleEdge_of_packingOne`: every two odd cycles meet + odd girth `≤ ℓ`
   ⇒ `CloseToBipartite ((ℓ + 1) / 2) G`.  Erdős's hypothesis appears nowhere; `LocIndep 1` enters only
   through `JSP90.inter_oddCycle_of_locIndep_one`.  In particular
   **`JSP90.closeToBipartite_of_shareCycleEdge_of_packingOne_of_three`**: a graph whose odd cycles are
   triangles, pairwise meet and share a cycle edge whenever they meet, is `2`-close to bipartite — a new
   instance on a class with **no degree bound and no local hypothesis**; the subcubic case is
   `JSP90.closeToBipartite_of_maxDegLe_three_of_packingOne_of_three`.
4. **The constant `2` is sharp, machine-checked.**  `K₄` satisfies all the hypotheses of (3)
   (`JSP90.maxDegLe_completeGraph_four`, `JSP90.shareCycleEdge_completeGraph_four`,
   `JSP90.card_le_three_of_oddCycle_completeGraph_four`, `JSP90.inter_oddCycle_completeGraph_four`) and
   `JSP90.not_closeToBipartite_one_K4` says it is not one vertex away from bipartite; it is
   `LocIndep 2` (`JSP90.locIndep_two_K4`), so the failure is inside the range of the theorem.
5. **The active-edge apparatus and the cover criterion.**  `JSP90.ActiveEdges` (the cycle edges of `C`
   lying in another odd cycle), `JSP90.evenCover_cover_activeEdges`,
   `JSP90.hitsOddCycles_of_activeEdgeCover_of_shareCycleEdge`,
   `JSP90.closeToBipartite_of_activeEdgeCover_of_shareCycleEdge` (a vertex cover of the active edges of
   `C`, inside `C`, is a transversal of the whole graph),
   `JSP90.hitsOddCycles_of_activeEdgeCover_evenCover`.

### Machine-checked negative results

6. **ROUND 78'S CONCRETE NEXT LEMMA IS FALSE.**  It was: *"for a shortest odd cycle `C` of a subcubic
   graph, the edges of `C` lying in another odd cycle are covered by two vertices of `C`"*.  In `p9`
   (subcubic, odd girth `5` by the new `JSP90.card_ge_five_of_oddCycle_p9`, so `Cb` is a shortest odd
   cycle) **all five** cycle edges of `Cb` are active (`JSP90.each_activeCb_active`: they lie in `Ca`,
   `Ca`, `Cc`, `Cd`, `Cd`; `JSP90.activeCb_eq_cycleEdges` puts this in the language of `ActiveEdges`),
   no two vertices cover them (`JSP90.not_two_cover_of_Cb`, in the conjecture's own order-based
   vocabulary `JSP90.TwoCoverCycleEdges`; and `JSP90.no_two_cover_activeCb`, a `decide` over all
   `3 ^ 9 = 19 683` subsets), three are needed (`JSP90.card_vertexCover_activeCb`) and three suffice
   (`JSP90.exists_cover_activeCb_three`).  Consequence: the `k = 1` subcubic constant `2` — which `p9`
   does attain — cannot be obtained by covering the active edges of one odd cycle.
7. **`¬ JSP90.ShareEdgePackingOne 1`** (`JSP90.not_shareEdgePackingOne_one`): `p9` satisfies that
   statement's hypotheses (`shareCycleEdge_p9`, `locIndep_one_p9`) and is not one vertex away from
   bipartite, so `r = 2` is the sharp candidate.

### The remaining statement

8. **`JSP90.ShareEdgePackingOne r`**, stated and not assumed: a graph in which two odd cycles that meet
   share a cycle edge and whose odd cycles pairwise meet is `r`-close to bipartite.  It drops **both**
   hypotheses that remain in the `k = 1` subcubic case (the degree bound and the odd-girth bound) and
   therefore *generalises* round 78's `JSP90.SubcubicPackingOne`
   (`JSP90.subcubicPackingOne_of_shareEdgePackingOne_two`); item 3 is its proved base level (triangle
   class) and item 7 pins the constant.  The only consumer is
   `JSP90.erdos73On_shareEdgePackingOne_one`.

`#print axioms` on the eighteen headline results of the file shows only
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

### Environment notes added this round

* `Finset` operations build `DecidableEq α` into the *data*, so a finset built with the classical
  instance and the same finset built with `instDecidableEqFin` are **not** defeq: the finite checks must
  live in a section where the computable instance is in scope, and every statement shared across the two
  sections must mention only `⊆` and element membership (hence the instance-free `TwoCoverCycleEdges`
  and `activeCb_eq_cycleEdges`);
* `rw [def, dif_pos h]` across files works iff the local `Decidable` instance is defeq to the baked-in
  one — copy the declaration style of `JSPProblem/Subcubic.lean`;
* `subst h` on `h : D = C` may eliminate `C` instead of `D`;
* `Finset.mem_inter.mp` returns components in the order of the intersection;
* `Finset.mem_pair`, `Finset.card_pair_of_ne` and `Finset.not_mem_empty` do **not** exist at the pinned
  revision (`{a,b} = insert b {a}`, so use `Finset.mem_insert`/`Finset.mem_singleton`,
  `Finset.card_insert_of_notMem`+`Finset.card_singleton`, and `Finset.not_nonempty_empty ⟨x, hx⟩`);
* `by decide` over `Finset (Fin n)` needs `set_option maxRecDepth 100000` (and heartbeats) in the
  enclosing section;
* `(2 : Fin 3)` annotations keep `by decide` well-typed; `⟨2, by omega⟩` inside the *type* of a `have`
  introduces a free variable and `decide` then refuses it.

---

## Round 81 (`lean/JSPProblem/Cactus.lean`, `lean/JSPProblem/Sun.lean`) — the **ODD CACTUS axis**: attack family 28

New modules, 58 declarations, 765 lines, 0 `sorry`, 0 `admit`; `lake build` OK (1236 jobs);
`harness/score.py`: `build_ok=true, sorry=0, admit=0, placeholder_total=0, partial_ok=true,
missing_theorems=['jsp_000090_main']`.

### The class

`JSP90.OddCactus G` — the odd cycles of `G` form a **cactus**: they are *linear* (two distinct odd
cycles meet in at most one vertex, `JSP90.LinearOddCycles`) and *two-Helly* (three pairwise meeting
odd cycles have a common vertex, so there is no **ring** of three odd cycles meeting in three
distinct vertices, `JSP90.TwoHellyOddCycles`).  This is a **purely local intersection-pattern
hypothesis**: no degree bound, no odd-girth bound, no connectivity hypothesis, no decomposition.
It **contains** round 39's class (`JSP90.OddCactus.of_oddCyclesDisjoint`), so every instance proved
for `OddCyclesDisjoint` is an instance of this one.

### What is proved

1. **THE STRUCTURAL LEMMA** `JSP90.disjoint_of_attach_ne`: two odd cycles that meet a common odd
   cycle at *different* vertices are **disjoint**.  If `D` meets `C` at `a`, `E` meets `C` at
   `a' ≠ a` and `D`, `E` meet at `b`, linearity gives `C ∩ D = {a}`, `C ∩ E = {a'}`, hence `a ∉ E`
   and `C ∩ D ∩ E = ∅` — a ring, contradicting two-Helly.
2. **A NEW INSTANCE OF THE HEADLINE THEOREM AT `k = 1`, WITH THE OPTIMAL CONSTANT `1`**:
   `JSP90.closeToBipartite_one_of_oddCactus_of_locIndep_one` and, in the `Erdős73On` form,
   `JSP90.erdos73On_oddCactus_one`: `LocIndep 1 G → OddCactus G → CloseToBipartite 1 G`.  Erdős's
   hypothesis enters **only** through the packing bound at `k = 1` ("every two odd cycles meet",
   `JSP90.inter_oddCycle_of_locIndep_one`); the key step is
   `JSP90.exists_commonVertex_oddCactus_of_locIndep_one` — in an odd cactus with `LocIndep 1` all
   the odd cycles have a *common vertex*.  The constant `1` is the smallest possible for a graph
   with an odd cycle, and it is strictly better than the constant `2` of
   `JSPProblem/Cover.lean`, whose class `ShareCycleEdge` is a different one (and which admits `p9`).
3. **A NEW INSTANCE AT EVERY `k`**, `JSP90.erdos73On_oddCactus`, with the constant `k * (k + 1)`: a
   maximum packing of odd cycles has at most `k` members and meets every odd cycle, and by (1) the
   *attachment points* of a member — the vertices at which another odd cycle meets it — are at most
   `k` in number; the union of those, plus one vertex per packed cycle, is a transversal of size at
   most `k * k + k`.
4. **THE CONSTANT `1` IS EXACT.**  `K₃` is an `OddCactus` graph
   (`JSP90.oddCactus_completeGraph_three`; every odd cycle of `K₃` is the whole vertex set, so both
   halves of the class are vacuous there), it satisfies `LocIndep 1`
   (`JSP90.completeGraph_locIndep 1`), and it is not bipartite
   (`JSP90.not_closeToBipartite_zero_completeGraph_three`).  So `f(1) = 1` **exactly** on this class.
   `JSP90.oddCactus_kTriangles` puts round 39's sharp witness `kTriangles k` (transversal number
   exactly `k`) into the class, so the class is attained.
5. **THE TWO-HELLY HYPOTHESIS IS NECESSARY: THE 3-SUN** (`sun3`, six vertices: a triangle
   `0 – 2 – 5` with a degree-2 vertex on each edge).  `JSP90.locIndep_one_sun3` (exhaustive decision
   over its 64 vertex sets) and `JSP90.not_closeToBipartite_one_sun3` (for every vertex, one of the
   four triangles avoids it) say it satisfies `LocIndep 1` and needs **two** vertices; but its three
   peripheral triangles `T₁ = {0,1,2}`, `T₂ = {2,3,5}`, `T₃ = {0,4,5}` pairwise meet in the three
   distinct vertices `2, 5, 0` with empty triple intersection, so
   `JSP90.not_twoHelly_sun3` and `JSP90.not_oddCactus_sun3` hold, and `JSP90.not_linear_sun3` holds
   too (`T₁ ∩ T₀ = {0,2}`).  The class is therefore cut exactly where it must be.  `sun3` is also a
   **six-vertex** witness for the lower bound `f(1) ≥ 2` of `JSPProblem/Petersen.lean` (which uses the
   nine-vertex `p9`).

### The remaining statement (stated as a `def`, not assumed)

6. **`JSP90.LinearRing G`, THE RING LEMMA**: in a graph whose odd cycles are linear, three pairwise
   meeting odd cycles have a common vertex.  A ring `C`, `D`, `E` meeting pairwise in three distinct
   vertices `a`, `b`, `c` gives — by concatenating one arc of each of the three cycles — an **odd**
   cycle meeting `C` in `a` and `c`, contradicting linearity; the parity step is the elementary
   "the two arcs of an odd cycle have opposite parity" (`JSP90.arc_parity`, already proved in
   `JSPProblem/Fan.lean`).  `JSP90.OddCactus G` is exactly `LinearOddCycles G ∧ LinearRing G`
   (`JSP90.oddCactus_iff`, `JSP90.twoHelly_of_linearRing`), so Parts 1–4 are proved with the ring
   lemma **assumed**; with it, Parts 1–3 are available under `LinearOddCycles G` alone.  The proof
   needs a three-arc concatenation, i.e. a "closing path" generalisation of
   `JSP90.arc_isOddCycle_of_notMem` (`JSPProblem/Chord.lean`, which closes an arc through a single
   *vertex*); that was not attempted this round.

### Machine-checked negative results (from the exhaustive search run **before** formalising)

7. **THE `f(1) ≥ 3` ROUTE IS DEAD.**  An exhaustive, incremental and parallel search over **all**
   `2 ^ 28 = 268 435 456` graphs on 8 vertices (`/tmp/opencode/jsp90/search4.c`) gives: the maximum
   odd cycle transversal number over graphs with `MaxDef ≤ d` is `0, 1, 2, 3` for `n = 5, 6, 7, 8`
   respectively, and among the `52 256 816` graphs with `MaxDef ≤ 1` **none** needs `3` vertices.
   So no `LocIndep 1` graph on `≤ 8` vertices is a witness for `f(1) ≥ 3`, and the ratio
   `OCS / MaxDef = 2` — hence `f(k) ≥ 2k` of round 76 — is sharp at the level of the constant `2`:
   it is already attained on **six** vertices, by the 3-sun.  A search to `n = 9` was started and
   did not finish within the round.

`#print axioms` on nineteen results of the two files shows only
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

### Environment notes added this round

* `Finset.mem_inter.mp` / `.mpr` take the components **in the order of the intersection**: for
  `hx : x ∈ C ∩ D`, `.1` is `x ∈ C` and `.2` is `x ∈ D`;
* a finset built by a `Finset` operation (`inter`, `filter`, `image`, `deleteFinset`) carries the
  `DecidableEq` instance **in scope where it was built**, so a statement shared between the
  classical section of `Cactus.lean` and the finite section of `Sun.lean` must be phrased with
  **element memberships only** — hence the bridge lemmas `JSP90.exists_mem_inter3`,
  `JSP90.mem_of_mem_inter3`, `JSP90.twoHelly_of_three_ne`, `JSP90.not_linear_of_two_mem`,
  `JSP90.exists_oddCycle_deleteFinset`;
* `Finset.card_image_of_injOn` takes its hypothesis as `Set.InjOn f (s)`: parenthesise, or
  `Set.InjOn gr Y i` parses as an application of the result to `i`;
* `Finset.card_image_le`, `Finset.sum_const_nat` and `Finset.eq_univ_of_card` take the finset
  **first** (named arguments are the safe form);
* `Finset.singleton_ne_empty : ∀ a, ({a} : Finset α) ≠ ∅` is a `∀`, not an `iff`, and
  `Finset.ne_empty_of_nonempty` does not exist (use `Finset.nonempty_iff_ne_empty.mp`);
* `Y i.card` parses as `Y (i.card)` — write `(Y i).card`;
* `exists_oddCycle_av` and `exists_oddCycle_delete_av` are already declared in
  `JSPProblem/Petersen.lean`; new finite witnesses must be prefixed (`sun3_oddCycle_av`);
* `set_option maxRecDepth N in set_option maxHeartbeats M in` must be followed by the docstring
  and then the declaration (as in `JSPProblem/Petersen.lean`).

---

## Round 82 — `JSPProblem/Ring.lean`: the RING LEMMA — the cactus class is *exactly* the linear class

New file `lean/JSPProblem/Ring.lean` (24 top-level declarations — 13 of them new lemmas — 889 lines),
imported from the root module `JSPProblem.lean`.  `lake build` OK (1237 jobs); **0 sorry, 0 admit**;
`score.py --strict-prize` reports `build_ok = true, sorry = 0, admit = 0, placeholder_total = 0,
partial_ok = true, missing_theorems = ["jsp_000090_main"]` (the headline theorem is still
deliberately **not** declared).  This is the **twenty-ninth attack family**, and it **closes the gap
that round 81 left open**: that file stated, but did not prove, the *ring lemma*.

### What round 81 left open, and what is now proved

`JSPProblem/Cactus.lean` defines

```lean
JSP90.OddCactus G   = LinearOddCycles G ∧ TwoHellyOddCycles G
JSP90.LinearRing G  = three pairwise meeting odd cycles of G have a common vertex
```

and could prove only `OddCactus G → LinearOddCycles G`; the implication `LinearOddCycles G →
LinearRing G` was stated as a `def` and **not** assumed, so all of round 81 was proved under the
stronger hypothesis `OddCactus G`.  Round 82 **proves the ring lemma**:

* **`JSP90.twoHelly_of_linearOddCycles : LinearOddCycles G → TwoHellyOddCycles G`** — in a graph whose
  odd cycles are *linear* (no two of them meet in more than one vertex) there is **no ring** of three
  odd cycles.  The classical argument, machine-checked end to end: linearity makes each pairwise
  intersection a single vertex `a ∈ C ∩ D`, `b ∈ D ∩ E`, `c ∈ E ∩ C`; either two of them agree (a
  common vertex, done) or they are all distinct, whence `a ∉ E`, `b ∉ C`, `c ∉ D`.  Take in each cycle
  the **odd** one of the two arcs between the two points lying on it — `A₁` in `C` from `a` to `c`,
  `A₂` in `E` from `c` to `b`, `A₃` in `D` from `b` to `a` — whose interiors are therefore disjoint
  from the other two cycles.  `JSP90.isOddCycle_of_ring3` concatenates them into a **simple odd
  cycle** of `d₁ + d₂ + d₃` vertices; it meets `C` in the two distinct vertices `a`, `c` and also
  contains `b ∉ C`, so it is a *different* odd cycle of `G` meeting `C` in two vertices —
  contradicting linearity (`JSP90.not_linear_of_two_mem`);
* **`JSP90.linearRing_of_linear`, `JSP90.oddCactus_iff_linear`,
  `JSP90.oddCactus_iff_of_linear`** — **`OddCactus G ↔ LinearOddCycles G`**: *the odd cycles of a
  graph form a cactus if and only if no two of them meet in more than one vertex*.  The two-Helly
  condition is a **consequence** of linearity, not an extra hypothesis;
* **`JSP90.disjoint_of_attach_ne_lin`** — the structural lemma of round 81 (two odd cycles attaching
  to a common odd cycle at different vertices are disjoint) under `LinearOddCycles G` alone.

### The new machinery (developed from scratch, no Mathlib input)

* `JSP90.arcOf`, `JSP90.arcRev` — an arc of a cycle as a *directed* path, and the same path
  traversed backwards.  Both are maps `ℕ → V` (entry `t` = the vertex `t` steps along), which makes
  every later construction free of dependent `if`s.  `arcRev` removes a case analysis that cannot be
  avoided: **the three arcs of a ring need not be oriented consistently** — the three-sun of
  `JSPProblem/Sun.lean`, the machine-checked counterexample of round 81 to dropping the two-Helly
  hypothesis, is exactly such a ring.
* `JSP90.exists_oddPath` — **between two distinct vertices of an odd cycle there is a simple path of
  odd length lying on the cycle**, with injectivity, consecutive adjacency and containment in the
  cycle (`JSP90.arc_parity`, i.e. exactly one of the two arcs is odd, plus the two orientations).
* `JSP90.arcCat3`, `JSP90.arcCat3_inj`, `JSP90.arcCat3_adj`,
  **`JSP90.isOddCycle_of_ring3` — THE THREE-ARC CYCLE CONSTRUCTOR**: three directed simple paths
  which walk along `G`, join head to tail cyclically (`A₁ d₁ = A₂ 0`, `A₂ d₂ = A₃ 0`,
  `A₃ d₃ = A₁ 0`) and meet only in the joining vertices, concatenate to a **simple cycle** of
  `d₁ + d₂ + d₃` vertices; if the three lengths are odd, to an **odd** cycle.  This is the "closing
  path" generalisation of `JSP90.arc_isOddCycle_of_notMem` of `JSPProblem/Chord.lean` (which closes
  an arc through a single *vertex*) that round 81 named as the missing tool.

### The payoff: two instances of the headline theorem, with a strictly weaker hypothesis

* **`JSP90.closeToBipartite_one_of_linear_of_locIndep_one`** and
  **`JSP90.erdos73On_linear_one`** — `LocIndep 1 G → LinearOddCycles G → CloseToBipartite 1 G`.
  Round 81 proved this with the constant `1` for the class `OddCactus G`; the two-Helly conjunct is
  now *derived*, so the statement holds for the **larger** class of graphs in which no two odd cycles
  meet in more than one vertex.  The constant `1` is the smallest possible for a non-bipartite graph.
* **`JSP90.erdos73On_linear`** (via `JSP90.erdos73On_of_linear`) — `LocIndep k G → LinearOddCycles G
  → CloseToBipartite (k * (k + 1)) G` for **every** `k`, the constant of round 81, again for a
  strictly larger class: no bound on the odd girth, the degrees, the packing weight or the number of
  branch vertices, and no connectivity or decomposition hypothesis.

### Verification before formalising

Per the discipline of rounds 78 and 80, the ring lemma was checked computationally first: for
**every** graph on `n ≤ 7` vertices (exhaustive, all `2²¹` graphs) and every triple of odd cycles
meeting pairwise in three distinct vertices, some odd cycle of the graph contains two of the three
vertices.  Result: 3 440 640 rings found, **0 counterexamples**.  (The three-sun, six vertices, is the
smallest configuration containing a ring.)

### What is *not* proved

Erdős #73 for `k ≥ 1` in full.  The remaining content is still "a bounded odd-cycle packing number
forces a bounded odd cycle transversal", i.e. the Erdős–Pósa theorem for odd cycles
(Reed–Robertson–Seymour–Thomas), named as `JSP90.OddCycleErdosPosa r` in
`discovery/JSP-000090/policy.json`.  The new `LinearRing` blocker of round 81 is **deleted**: it is a
theorem now.

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; declaring a weaker theorem under that name would
misrepresent the result.  `formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award
claim is made.

---

## Round 83 — `JSPProblem/Helly.lean`: the **HELLY axis** — attack family 30

New module (31 declarations, 565 lines), imported from the root module `JSPProblem.lean`.
**0 `sorry`, 0 `admit`**; `lake build` OK (1238 jobs);
`harness/score.py problems/JSP-000090` reports `build_ok = true, sorry = 0, admit = 0,
placeholder_total = 0, partial_ok = true, missing_theorems = ['jsp_000090_main']`.

### The class

```lean
JSP90.HellyOddCycles G
```

— the odd cycles of `G` form a **Helly family**: every *finite* family of pairwise meeting odd
cycles has a common vertex.  This is strictly stronger than round 81/82's
`JSP90.TwoHellyOddCycles G`, which only asks for the three-element case, and strictly weaker than
round 82's `JSP90.LinearOddCycles G`.

### What is proved

1. **THE HELLY LEMMA** — `JSP90.helly_of_linearOddCycles : LinearOddCycles G → HellyOddCycles G`:
   **in a graph whose odd cycles are linear, the odd cycles form a Helly family**.  Round 82's ring
   lemma kills *rings* (three cycles); this kills *every* non-Helly family of any size.  Proof: strong
   induction on `|𝒞|`; for `|𝒞| ≥ 3` take three distinct members `C₁, C₂, C₃` and the induction
   hypothesis on `𝒞.erase Cᵢ`, giving `vᵢ` common to all the *other* members.  If some `vᵢ ∈ Cᵢ` we
   are done; otherwise `v₁ ∉ C₁`, `v₂ ∉ C₂`, `v₁ ∈ C₂ ∩ C₃`, `v₂ ∈ C₁ ∩ C₃`; with `C₁ ∩ C₂ = {a}`
   (linearity) the ring lemma produces `a ∈ C₃`, so `v₁ ≠ a` are two vertices of `C₂ ∩ C₃` — a
   contradiction.  `|𝒞| ≤ 2` is the nonemptiness of an odd cycle plus the pairwise-meeting hypothesis.
2. `JSP90.twoHelly_of_helly`, `JSP90.exists_commonVertex_of_helly`,
   `JSP90.exists_commonVertex_of_helly_three`, `JSP90.exists_three_mem_of_card_ge_three`.
3. **A NEW INSTANCE OF THE HEADLINE THEOREM AT `k = 1`, WITH THE OPTIMAL CONSTANT `1`, FOR THE
   STRICTLY LARGER HELLY CLASS** — `JSP90.closeToBipartite_one_of_helly_of_locIndep_one` and
   `JSP90.erdos73On_helly_one`: `LocIndep 1 G → HellyOddCycles G → CloseToBipartite 1 G`.  Erdős's
   hypothesis enters **only** through the packing bound at `k = 1`
   (`JSP90.inter_oddCycle_of_locIndep_one`): the odd cycles pairwise meet, so the family of *all* odd
   cycles is itself a Helly subfamily.  No bound on the odd girth, the degrees, the packing weight,
   the branch vertices, the number of components, or the size of the odd cycles.
   `JSP90.closeToBipartite_one_of_helly_of_linear` records round 82's instance as the specialisation.
4. **THE CONSTANT `1` IS EXACT** on the Helly class — `JSP90.helly_completeGraph_three`,
   `JSP90.helly_locIndep_one_K3`, `JSP90.helly_not_closeToBipartite_zero_K3`,
   `JSP90.not_helly_attained_zero`: `K₃` has the Helly property, satisfies `LocIndep 1` and is not
   bipartite, so `f(1) = 1` exactly here.
5. **THE CLASS IS *STRICTLY* LARGER THAN ROUND 82'S — THE DIAMOND `K₄` MINUS AN EDGE** —
   `JSP90.three_cycle_isClique`, `JSP90.mem_zero_of_oddCycle_diamond`, `JSP90.helly_diamond`,
   `JSP90.locIndep_one_diamond`, `JSP90.closeToBipartite_one_diamond`, `JSP90.not_linear_diamond`, and
   the summary **`JSP90.HellyOfNonlinear`**: `diamond` satisfies `HellyOddCycles`,
   `LocIndep 1` and `CloseToBipartite 1` but **not** `LinearOddCycles` (its two triangles meet in two
   vertices).  So Part 3 is a genuinely new instance, **not** a corollary of round 82's.
6. **THE `k`-AXIS** — `JSP90.HellyErdős73 f`, the remaining statement for the Helly class at a
   general constant, stated as a `def` and **not assumed**; Part 3 is its proved base level.

### Verified computationally before formalising

Exhaustive search over **all** graphs on `n ≤ 7` vertices (`2²¹`):
`LinearOddCycles ⟹ HellyOddCycles` — **0** counterexamples; `HellyOddCycles ∧ LocIndep 1 ⟹ τ = 1` —
**0** counterexamples (max transversal number `1` among the `870 530` Helly graphs on `n = 7`), against
`13 020` graphs with `LocIndep 1`, packing number `1` and transversal number `2` that all **fail**
`HellyOddCycles`; `643 006` graphs on `n = 7` are Helly, `LocIndep 1`, transversal number `1` and
**not** linear, confirming the strictness machine-checked in Part 5.  Random search on `n = 10`
(`4 · 10⁶` graphs): no `Helly ∧ LocIndep 1` graph needs `≥ 2` vertices; but `Helly ∧ LocIndep 2`
**does** admit transversal number `3` (10-vertex witness), which is why Part 6 takes a general `f`.

### What is *not* proved

`JSP90.HellyErdős73 f` for any `f` — Erdős #73 for the Helly class at a general `k`.  Behind it
stands `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary blocker:
the Helly property bounds the transversal number at `k = 1` and says nothing about larger packings.  No
Helly, colouring or packing hypothesis is *assumed* anywhere in the file.

`#print axioms` on all twenty headline results shows only
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

`jsp_000090_main` is deliberately **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; declaring a weaker theorem under that name would
misrepresent the result.  `formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award
claim is made.

---

## Round 84 — `JSPProblem/Descent.lean`: the **deficiency descent** — Erdős #73 on the Helly class with the *optimal* constant `k`

New file `lean/JSPProblem/Descent.lean` (23 declarations, 0 `sorry`, 0 `admit`, `lake build` OK with
1239 jobs), imported from the root module.  Attack family 31.

### The statement

```lean
JSP90.erdos73On_helly_of_maxDefDescent :
    JSP90.HellyMaxDefDescent → JSP90.HellyErdős73 id
```

**Erdős Problem #73 for the graphs whose odd cycles form a Helly family, with the *optimal* constant
`f(k) = k`** (`LocIndep k G → HellyOddCycles G → CloseToBipartite k G`), reduced to **one** statement
about a single vertex deletion:

```lean
JSP90.VertexDescent G : Prop :=
  1 ≤ MaxDef G → ∃ (C : Finset V) (v : V), IsOddCycle G C ∧ v ∈ C ∧
    MaxDef (deleteFinset G {v}) + 1 ≤ MaxDef G
```

The invariant has changed from the packing number and the transversal number to the **maximum
deficiency** `MaxDef G`, which is exactly Erdős's hypothesis (`LocIndep k G ↔ MaxDef G ≤ k`,
`JSP90.locIndep_iff_maxDef_le`).

### Proved

* **Helly is hereditary**: `JSP90.isOddCycle_induceFinset` (the odd cycles of `G[s]` are odd cycles
  of `G`), `JSP90.helly_induceFinset`, `JSP90.helly_deleteFinset` — the residue of a Helly graph is
  Helly, which is what makes the induction on `MaxDef` possible;
* **the residue descent with no separation hypothesis**:
  `JSP90.maxDef_ge_one_add_maxDef_delete_of_oddCycle : IsOddCycle G C →
  1 + MaxDef (deleteFinset G C) ≤ MaxDef G` (numerical heart:
  `JSP90.defOf_ge_succ_add`, from `α(G[A ∪ C]) ≤ α(G[A]) + α(G[C])` and `2 α(G[C]) + 1 ≤ |C|`);
* **the duality of a witness and a transversal**: a vertex set of deficiency exactly `MaxDef G` meets
  every odd cycle (`JSP90.defOf_maxDef_inter_oddCycle_ne`), and a vertex set of positive deficiency
  contains an odd cycle (`JSP90.exists_oddCycle_of_defOf_gt_zero`); hence
  `JSP90.vertexDescent_of_common_oddCycle` — the descent **is** proved when one vertex lies on every
  odd cycle;
* the **reduction**: `JSP90.closeToBipartite_maxDef_aux` (strong induction on `MaxDef G`, deleting
  one vertex of an odd cycle), `JSP90.closeToBipartite_maxDef_of_maxDefDescent`,
  `JSP90.erdos73On_helly_of_maxDefDescent` — `HellyMaxDefDescent` is used in exactly one place;
* a **proved instance at every `c`**: `JSP90.erdos73On_helly_pairwiseMeeting` —
  `LocIndep c G → HellyOddCycles G → (the odd cycles pairwise meet) → CloseToBipartite c G`;
* **optimality of the constant**: `JSP90.helly_kTriangles`, `JSP90.helly_attained_sharp` —
  `kTriangles k` is Helly, satisfies `LocIndep k` and is not `(k - 1)`-close to bipartite.

### Not proved

`JSP90.HellyMaxDefDescent` — the vertex descent for the Helly class.  Verified exhaustively (all
`2²¹` graphs on `n ≤ 7` vertices, `1 103 955` of them Helly: 0 counterexamples) and refuted without
the Helly hypothesis (13020 counterexamples; the smallest is the diamond `K₄ - e`).  Three stronger
candidate proofs were refuted and are recorded in `README.md` and `discovery/JSP-000090/policy.json`:
König's property fails on the Helly class (`τ > ν`, 360 counterexamples), the `+1` absorption step at
a residue fails on the Helly class (360 counterexamples, the smallest a 6-vertex graph with
`MaxDef = τ = 2`), and the deficiency is **not** superadditive over a disjoint decomposition.

`jsp_000090_main` remains **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true`.
`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.


---

## Round 90 — `JSPProblem/CutVertex.lean`: the 2-cut axis is closed

New file `lean/JSPProblem/CutVertex.lean` (24 top-level declarations, 0 sorry/admit, `lake build` OK
with 1245 jobs), imported from the root module `JSPProblem.lean`, whose docstring was extended.

Rounds 78–89 attacked the 2-cut decomposition.  Round 89 reached
`JSP90.VertexSplit.closeToBipartite_one_avoid_of_clean`: a packing bound `r`, the cleanliness
hypothesis "every bipartite part has a bipartite half-piece", and `CloseToBipartite m` on the
half-pieces of the non-bipartite parts give `CloseToBipartite (1 + m * r) G` — and it recorded, by
machine check (windmill `wf`), that cleanliness is **not** automatic.  This round closes the axis.

* `JSP90.oddCycle_mem_b_of_halfPiece_of_isBipartite_part`,
  `JSP90.oddCycle_mem_a_of_halfPiece_of_isBipartite_part` — **the local fact**: over a bipartite part
  `T_i`, every odd cycle of the half-piece `T_i ∪ {b}` contains `b`.  Hence
  `JSP90.hitsOddCycles_half_insert_b_of_isBipartite_part` (and its `a`-sister): the single cut vertex
  is a transversal of the half-piece of a bipartite part.
* `JSP90.VertexSplit.hitsOddCycles_both` — **the cut step with no hypothesis on the cut**: if
  `X i ∪ {a}` meets every odd cycle of `T_i ∪ {a}` for every `i`, then `{a, b} ∪ ⋃ X i` is an odd cycle
  transversal of `G`.  Nothing about the edges from `a` or `b` to the parts is used.
* **`JSP90.VertexSplit.closeToBipartite_two_of_nonBipartiteParts` — THE MAIN THEOREM**:
  a packing bound `r` and `CloseToBipartite m` on the half-pieces `T_i ∪ {a}` of the non-bipartite
  parts give `CloseToBipartite (2 + m * r) G`, **with no hypothesis on the cut**.  Its hypothesis is
  *strictly weaker* than `JSPProblem.VertexSplit.closeToBipartite_of_split_of_bounded_pieces_pack`
  (`2 + m * p` on the pieces `T_i ∪ {a,b}`), because a half-piece is a subgraph of the piece.
  `JSP90.VertexSplit.closeToBipartite_two_of_nonBipartiteParts_swap` is the `b`-side version.
* `JSP90.closeToBipartite_of_split_step`, `JSP90.closeToBipartite_of_split_of_oddCycleErdosPosa_two` —
  **the induction step of the classical proof along a 2-cut**, with no hypothesis on the cut;
  `JSP90.closeToBipartite_of_split_step_one_of_clean` is the `+1` form (`1 + m * r`).
* **New instances of the headline theorem**:
  `JSP90.erdos73On_of_split_two_of_nonBipartiteParts` (`LocIndep k G` forces
  `CloseToBipartite (2 + m * k) G`), `JSP90.erdos73On_of_split_two_of_nonBipartiteParts_of_bounded_branch`
  (`2 + (m + k) * k`), and `JSP90.erdos73On_of_split_one_avoid_of_clean_parts` (`1 + m * k`).
* `JSP90.VertexSplit.sdiff_biUnion_half` — **the residue of the cut step is exact**:
  `V \ ({a,b} ∪ ⋃ X i) = ⋃ i (T_i \ ⋃ X i)`; and `JSP90.VertexSplit.isBipartite_delete_of_both`
  gives the bipartiteness of the residue.
* **The obstruction, pinned exactly**: `JSP90.hitsOddCycles_empty_iff_isBipartite_half` (and its
  `a`-sister, and `JSP90.clean_iff_empty_transversal`) says `X i = ∅` is a transversal of the
  half-piece **iff** the half-piece is bipartite, i.e. iff the cut is clean at `i`.  So the
  cleanliness hypothesis cannot be weakened in this form, and `+1` (round 89, clean) versus `+2`
  (this round, unconditional) is the exhaustive choice; `JSP90.windmill_plus_two_plus_one` records
  both on the windmill.

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  What remains is the 2-cut-free
(3-connected) case of `JSP90.OddCycleErdosPosa r`.

---

## Round 93 (`lean/JSPProblem/MaxCut.lean`) — the **CUT AXIS**: odd cycle transversals are exactly the
monochromatic covers of a cut

New module (26 declarations, 501 lines, **0 `sorry`, 0 `admit`**, `lake build` OK with 1246 jobs),
imported from the root module `JSPProblem.lean`; attack family 37.  Rounds 76–92 attacked the packing,
degree, deficiency, separator, intersection-pattern, fan and 2-cut axes; none touched the
**max-cut / 2-colouring** reformulation.

### What is proved

* `JSP90.MonoEdge G A v w` (the edge `vw` does **not** cross the cut with side `A`), `JSP90.HitsMono
  G A Z` (`Z` meets all of them), `JSP90.Separates S T A`, `JSP90.HasMonoCover G q A`,
  `JSP90.MonoCoverBetween G S T Z` (one set works for **every** cut separating `S` from `T`) —
  the notions of the axis.
* **`JSP90.even_of_cycle_noMono`** — a cycle all of whose edges cross a cut has even length (the
  `cycSucc_pow_odd` parity argument of `Transversal.lean` with "the two sides of a bipartition"
  replaced by "the two sides of an arbitrary cut"), and therefore
* **`JSP90.exists_monoEdge_of_isOddCycle`** — **every odd cycle of `G` contains a monochromatic edge
  of every cut**, with both witnesses inside the cycle.  This is the load-bearing lemma: it makes a
  vertex cover of the monochromatic edges of a cut an **odd cycle transversal**
  (`JSP90.hitsOddCycles_of_hitsMono`).
* **`JSP90.hitsOddCycles_iff_hitsMono`** — **the odd cycle transversals of `G` are exactly the
  monochromatic covers of some cut**; the converse is the construction "put the transversal on one
  side together with one colour class of the bipartition of the residue".
* **`JSP90.isBipartite_deleteFinset_of_hitsMono`** — deleting a monochromatic cover leaves a
  bipartite graph, with the explicit `2`-colouring `if v ∈ A then 0 else 1`; and
* **`JSP90.closeToBipartite_iff_hitsMono`** — **the conclusion of Erdős #73 *is* a cut certificate**:
  `CloseToBipartite q G ↔ ∃ A Z, HitsMono G A Z ∧ Z.card ≤ q`.  It is an `iff`, so the axis loses
  nothing in either direction.
* **New instances of the headline theorem**: `JSP90.erdos73On_of_hasMonoCover` (`LocIndep k G` plus
  *some* cut carrying a `q`-vertex monochromatic cover ⟹ `CloseToBipartite q G`) and
  `JSP90.erdos73On_of_monoCoverBetween` (**one** set covering the monochromatic edges of **every**
  cut separating two given vertex sets — the multiway-cut formulation).  Sources of certificates:
  `JSP90.hitsMono_of_vertexCover`, `JSP90.hasMonoCover_of_vertexCover`,
  `JSP90.monoCoverBetween_of_vertexCover`.
* **Exactness and obstruction**: `JSP90.exists_noMonoEdge_iff_isBipartite` (`q = 0` is exactly
  bipartiteness — the axis is faithful at every `q`);
  `JSP90.hasMonoCover_completeGraph_of_split` (**on `K_n` the certificate is `n - 2`, exactly
  optimal**, for every cut with both sides nonempty — the axis is exact on the class where Erdős #73
  is completely known); `JSP90.hasMonoCover_completeGraph_two_three` (a cut of `K_3` whose
  certificate is exactly one vertex); and the machine-checked negative result
  **`JSP90.not_hasMonoCover_completeGraph_three`**: the certificate **depends on the cut** — `K_3`
  is `1`-close to bipartite while its trivial cut has *no* one-vertex certificate.  So "find a good
  cut" is the content of the axis.

### Discarded before formalisation (recorded so no round repeats them)

* **The multiway version is *not* known to be strictly stronger than the conclusion**: for the pair
  `{0} | {1,2}` of `K_3` the only separating cut is `{0}`, whose monochromatic edges are `{1, 2}`,
  and `{1}` covers them — the planned strictness witness is refuted by hand.
* **The "for every cut" form of the single-cut certificate is degenerate**: `∀ A, ∃ Z, HitsMono G A
  Z ∧ Z.card ≤ q` implies that `G` is bipartite for every `q`.
* **`HasMonoCover G 0 A` is unsatisfiable** (it asks the empty set to cover, i.e. to *refute*, the
  monochromatic edges); the correct statement is `JSP90.exists_noMonoEdge_iff_isBipartite`.

### What is *not* proved

No bound on the certificate in terms of `MaxDef G` — but by `closeToBipartite_iff_hitsMono` such a
bound *is* `JSP90.OddCycleErdosPosa r` again (the certificate is the transversal).  What is still
missing on this axis is a bound coming from a **local** quantity (e.g. the max-cut counting bound
`τ(G) ≤ e(G)/2`, which needs a neighbourhood-counting apparatus that `SimpleGraph.degree` does not
provide at the pinned revision).

`#print axioms` on thirteen headline results shows only `[propext, Classical.choice, Quot.sound]` —
no `sorryAx`.  `jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  See
`discovery/JSP-000090/policy.json`.

---

## Round 96 — the finite-search axis (new module `lean/JSPProblem/Finite.lean`)

Rounds 76–95 attacked Erdős #73 structurally (packings, degrees, deficiency, separators, fans,
2-cuts, max-cuts).  Round 96 changes the *nature* of the attack: the conclusion is a statement
about **all** finite graphs, so the only way to be sure about a value of `k` is to check all
graphs, and the only way to check all graphs in Lean is to make the statement **decidable**.

**Machinery (new, reusable).**

| result | content |
| --- | --- |
| `JSP90.isBipartite_iff_color2` | `G` is bipartite iff one of the `2 ^ \|V\|` maps `V → Fin 2` separates the ends of every edge |
| `JSP90.OddCycleWitness`, `JSP90.isOddCycle_iff_witness` | an odd cycle is the image of a cyclic ordering witness |
| `JSP90.isOddCycle_iff_bounded` | an odd cycle of a finite graph has length `≤ \|V\|`, so the odd cycle transversal can be **searched for** |
| `JSP90.LocIndepSearch`, `JSP90.locIndep_iff_search` | Erdős's hypothesis with both `X` and `S` ranging over `Finset.powerset` |
| `JSP90.CloseToBipartiteSearch`, `JSP90.closeToBipartite_iff_search` | the conclusion as a `\|X\| ≤ m` deletion plus one of the `2 ^ \|V\|` colourings |
| `JSP90.erdos73On_fin` + two `Decidable` instances | on a fixed finite vertex type, **Erdős #73 is a finite decision problem** |

**The exact constant on six vertices (new).**  Let `g6` be the triangle with one further vertex
closing a triangle on each of its three edges (edges `{0,1}`, `{0,2}`, `{1,2}`, `{0,1,5}`,
`{1,2,3}`, `{0,2,4}`).  Then

* `JSP90.locIndep_one_g6` and `JSP90.not_locIndep_zero_g6` — the maximum deficiency of `g6` is
  **exactly 1** (the first by exhaustive kernel decision over the `2 ^ 6` vertex sets);
* `JSP90.isOddCycle_g6_012`, `..._015`, `..._123`, `..._024` and `JSP90.exists_oddCycle_g6_av` —
  the four triangles, one of which avoids each vertex;
* `JSP90.closeToBipartite_iff_g6 : CloseToBipartite m g6 ↔ 2 ≤ m` — the odd cycle transversal
  number of `g6` is **exactly 2**;
* `JSP90.not_erdos73_fin6_one_one` — `LocIndep 1 G → CloseToBipartite 1 G` is **false** for graphs
  on six vertices, so the constant of Erdős #73 at `k = 1` is at least `2` there.  `g6` is the
  smallest such graph; the previous witness `p9` has nine vertices.

**Abandoned after measurement.**  The exhaustive `decide` over all `2 ^ 15` graphs on six vertices
needs about 25 s per graph in the kernel (and `native_decide` is not in the pinned slice), so it was
dropped; the machinery it would use is kept in the file for a future round.  An independent
exhaustive search outside Lean (`discovery/JSP-000090/s22.c`) shows that `f(0) = 0`, that
`f(1) = 2` holds for **every** graph on at most seven vertices, and that `f(2) = 3` first occurs at
seven vertices; these are measurements, not Lean theorems.

`jsp_000090_main` is still not declared; the remaining statement is `JSP90.OddCycleErdosPosa r`.

## Status as of round 98 (the DISJOINT-ODD-CYCLE and the DEGREE–COLOURING axes)

* `lake build` succeeds (1248 jobs); **0 `sorry`, 0 `admit`** (harness `partial_ok = true`).
* New file `lean/JSPProblem/DegColour.lean` (26 declarations, 479 lines, 0 sorry/admit), imported
  from the root module `JSPProblem.lean` whose docstring was extended:
  * `JSP90.OddCycles G`, the family of *all* the odd cycles of `G`;
  * **`JSP90.erdos73On_of_disjointOddCycles`** — a new instance of the headline theorem with the
    **optimal constant `k`** and a strictly weaker hypothesis than
    `JSPProblem/Branch.lean`'s `erdos73On_of_no_branch`: the hypothesis is only
    `DisjointFamily (OddCycles G)`, i.e. "two distinct odd cycles of `G` are vertex-disjoint";
  * `JSP90.disjointFamily_oddCycles_of_no_branch` and `JSP90.erdos73On_of_no_branch'` — round 38's
    instance is a special case of this round's (its degree hypothesis is used for
    `eq_of_mem_inter_of_no_branch` and nothing else);
  * `JSP90.closeToBipartite_iff_card_oddCycles_of_disjoint` — **the class is decided by a single
    count**: `CloseToBipartite m G ↔ (OddCycles G).card ≤ m`, so the odd cycle transversal number
    of such a graph *equals* its number of odd cycles;
  * `JSP90.erdos73On_disjointOddCycles_exact`, with `JSP90.exists_eq_tri_of_isOddCycle_kTriangles`
    and `JSP90.disjointFamily_oddCycles_kTriangles`: the constant is **exactly `k`** on that class,
    the lower bound being `kTriangles k` of `JSPProblem/Sharp.lean`;
  * the **greedy colouring theorem** (absent from the pinned Mathlib slice):
    `JSP90.exists_colouringOn_of_degLe` (the greedy step, strong induction on the size of the vertex
    set), `JSP90.exists_not_mem_of_card_lt`, `JSP90.coloring_of_degLe`, `JSP90.coloring_of_maxDegLe`,
    and `JSP90.card_clique_le_of_coloring` (the converse, in the only true form: cliques, not
    degrees);
  * `JSP90.OddColorClass`, `JSP90.closeToBipartite_of_oddColorClass`,
    `JSP90.erdos73On_of_oddColorClass` — **a colour class is a certificate for the conclusion of
    Erdős #73**; properness alone is not (machine-checked at `JSP90.g6`).
* Still missing: `jsp_000090_main` (behind it `JSP90.OddCycleErdosPosa r` for arbitrary `r`).  The
  degree part of this axis stops at `JSP90.SubcubicErdős73`, which is still *assumed* in
  `JSPProblem/Subcubic.lean`: the greedy colouring bounds cliques, not colour classes, so a degree
  bound does not by itself give a transversal bound.

---

## Round 99 — the edge-counting axis (new module `lean/JSPProblem/Sparse.lean`)

Round 93 (`JSPProblem/MaxCut.lean`) recorded the missing item of the max-cut axis verbatim: *"a
bound on the certificate in terms of `MaxDef G` **is** `JSP90.OddCycleErdosPosa r` again; what is
still missing on this axis is a bound coming from a **local** quantity (e.g. the max-cut counting
bound `τ(G) ≤ e(G)/2`, which needs a neighbourhood-counting apparatus that `SimpleGraph.degree` does
not provide at the pinned revision)"*.  Round 98 built that apparatus on the Lean side
(`JSPProblem/Layer.lean`: `JSP90.Neigh`, `JSP90.MaxDeg` as finsets), and the pinned Mathlib slice
turns out to provide `SimpleGraph.edgeFinset`, `SimpleGraph.degree` and
`SimpleGraph.sum_degrees_eq_twice_card_edges`.  Round 99 therefore closes the item.

**Machinery (new, reusable).**

| result | content |
| --- | --- |
| `JSP90.degSum G` | `∑ v, \|N(v)\|` — the degree sum |
| `JSP90.edgeCount G` | `\|E(G)\|`, each edge once (Mathlib's `SimpleGraph.edgeFinset`) |
| `JSP90.two_mul_edgeCount` | `2 * \|E(G)\| = degSum G` |
| `JSP90.mem_neigh_deleteFinset'`, `neigh_deleteFinset`, `card_neigh_deleteFinset`, `card_neigh_deleteFinset_self`, `card_neigh_mono_deleteFinset` | the neighbourhood of `G - v`, exactly |
| `JSP90.degSum_deleteFinset` | **`degSum (G - v) + 2 * \|N(v)\| = degSum G`** |
| `JSP90.edgeCount_deleteFinset` | **`\|E(G - v)\| = \|E(G)\| - \|N(v)\|`** |
| `JSP90.two_le_card_neigh_of_mem_oddCycle` | **every vertex of an odd cycle has at least two neighbours** |
| `JSP90.three_le_card_of_isOddCycle`, `two_mul_card_le_edgeCount_of_isOddCycle`, `three_le_edgeCount_of_isOddCycle` | an odd cycle forces `2 * \|C\|` of the degree sum, hence `\|E\| ≥ 3` |

**The bound (the classical max-cut counting bound).**

* **`JSP90.closeToBipartite_of_edgeCount_le : edgeCount G ≤ 2 * m + 1 → CloseToBipartite m G`** —
  i.e. **`τ_odd(G) ≤ ⌊ |E(G)| / 2 ⌋`** — by induction on the budget: if `G` is not bipartite, take a
  vertex `v` of an odd cycle; it costs one vertex and, having two neighbours, removes at least two
  edges (`edgeCount_deleteFinset`, `two_le_card_neigh_of_mem_oddCycle`).  With
  `JSP90.HitsOddCycles.insert_v_of_deleteFinset` (a transversal of `G - v` together with `v`
  transverses `G`).
* `JSP90.closeToBipartite_of_degSum_le : degSum G ≤ 4 * m + 2 → CloseToBipartite m G` — the same
  bound with no `edgeFinset` at all.

**New instances of the headline theorem.**

* **`JSP90.erdos73On_of_edgeCount`** — `LocIndep k G` and `|E(G)| ≤ 2 * m + 1` give
  `CloseToBipartite m G`, with a constant that does **not** mention `k`: **the local hypothesis of
  Erdős's problem is not used at all**, the statement being the classical local bound.  This is a new
  instance for the class of graphs with a bounded number of edges (no degree bound, no odd-girth
  bound, no connectivity, no decomposition).
* `JSP90.edgeCount_le_card_mul_maxDeg`, `JSP90.closeToBipartite_of_maxDegLe_of_card_le`,
  `JSP90.erdos73On_of_maxDegLe_of_card_le` — the order-dependent instance `τ_odd(G) ≤ ⌈ |V| Δ / 2 ⌉`
  (`τ ≤ |V| Δ / 4`).

**Sharpness and exactness.**

* `JSP90.card_neigh_completeGraph_three`, `JSP90.edgeCount_completeGraph_three : |E(K_3)| = 3` and
  `JSP90.edgeCount_bound_tight_completeGraph_three` — the odd cycle transversal number of `K_3` is
  exactly `1 = ⌊ 3/2 ⌋`, so **the constant is attained and cannot be improved**.
* `JSP90.closeToBipartite_kTriangles_of_edgeCount` — on `kTriangles k` (`MaxDegLe 2`, `|V| = 3 k`)
  the counting bound gives `3 k` where the exact answer is `k`: the bound is a genuine bound but a
  loose one in the direction of the deficiency.

**Why this axis stops here (machine-checked part, stated part).**

* `JSP90.locIndep_zero_of_isBipartite : G.IsBipartite → LocIndep 0 G` — `LocIndep 0` **is**
  bipartiteness (`locIndep_iff_maxDef_le` with `maxDef_eq_zero_iff`), so the class allowed by
  `LocIndep 0` is exactly the bipartite graphs, which have arbitrarily many edges.
* `JSP90.LocIndepEdgeUnbounded` — *"no function of `k` bounds `|E(G)|` under `LocIndep k`"* — **stated,
  not assumed** (the computable witness would need an edge count that `decide` cannot evaluate at
  the pinned revision, since the `Classical.decRel` instance blocks it).  This is the precise reason
  the local bound is delivered and no value of `f(k)` is.
* `JSP90.BoundedOddGirthEdgeCount` — *odd girth `ℓ` and `MaxDegLe G d` ⟹ `f ℓ d`-close to
  bipartite* — **stated, not assumed**: the induction above pays for a vertex of degree `≥ 2` and says
  nothing about the higher degrees a shortest odd cycle would have to exhibit.

`#print axioms` on the new results shows only `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`.  `lake build` succeeds (1249 jobs) with **0 `sorry`, 0 `admit`**; `score.py --strict-prize`
reports `build_ok = true, partial_ok = true, prize_ready = false`, `missing_theorems =
["jsp_000090_main"]` (behind it `JSP90.OddCycleErdosPosa r`).  See
`discovery/JSP-000090/policy.json`.

---

## Round 100 — `lean/JSPProblem/Pivot.lean`: the **LOCAL-TRANSVERSAL axis** — attack family 41

New module (41 declarations, 715 lines, **0 `sorry`, 0 `admit`**, `lake build` OK with 1250 jobs),
imported from the root module `JSPProblem.lean` whose docstring was extended.  Round 99's option (A)
is **closed as impossible** this round, by machine check.

### The question

Every axis so far turns an *existence* statement about an odd cycle transversal into a number
(`Transversal.lean`: the transversal is the union of a maximum packing; `Sparse.lean`:
`τ ≤ ⌊|E|/2⌋`).  This round asks where the transversal must **sit**: within distance one of a packing.

* `JSP90.NeighClosed G C = C ∪ ∂C`, `JSP90.mem_neighClosed`, `JSP90.disjoint_boundary`,
  `JSP90.card_neighClosed_eq_add` (`|N[V(C)]| = |C| + |∂C|`);
* **`JSP90.hitsOddCycles_neighClosed_of_maxPacking` — the distance-one neighbourhood of the union of a
  *maximum* packing of odd cycles is an odd cycle transversal**: an odd cycle missing it is disjoint
  from every packed cycle, so it could be added, contradicting maximality.  With
  `JSP90.card_neighClosed_maxPacking_le` for its size (`≤ ℓ * |P| * (d - 1)`), which uses the packing
  additivity `JSP90.card_eq_sum_card_inter_of_disjoint`.

### The counting, in every degree range

* `JSP90.two_le_card_inter_neigh_of_mem_oddCycle` — a vertex of an odd cycle has two neighbours **on**
  the cycle (the fact `JSPProblem/Subcubic.lean` used implicitly in
  `card_le_one_outerNeigh_oddCycle`);
* `JSP90.card_boundary_le_card_mul_sub_two` — every vertex of `S` has two neighbours in `S` ⟹
  `|∂S| ≤ |S| * (d - 2)`; this **generalises** `card_boundary_le_card_oddCycle` from `d = 3` to every
  `d ≥ 2` and every set `S`;
* `JSP90.card_neighClosed_le_card_mul_sub_one` — **generalises**
  `card_neighClosed_le_two_mul_card_oddCycle`; attained on `K₃`
  (`JSP90.card_neighClosed_completeGraph_three_tight`: `|N[V(C)]| = 3 = 3 * (2 - 1)`).

### Instances of the headline theorem (with the honest constant)

* `JSP90.erdos73On_of_neighClosedPacking`: `LocIndep k G` + `MaxDegLe G d` (`2 ≤ d`) + every odd cycle
  of length `≤ ℓ` ⟹ `CloseToBipartite (ℓ * k * (d - 1)) G`, with the transversal **exhibited** as the
  neighbourhood.  **`JSPProblem/Transversal.lean` already proves `CloseToBipartite (ℓ * k) G` under
  strictly weaker hypotheses** (no degree bound), so this constant is *larger*: what is new is the
  certificate and the arbitrary degree range;
* **the two-level odd-girth ladder**, strictly stronger than the uniform bound:
  `JSP90.closeToBipartite_of_twoLevelGirth` (pay `ℓ₁` for a cycle of at most `ℓ₁` vertices, then
  `ℓ₂ * (k - 1) * (d - 1)` for the residue) ⟹ `JSP90.closeToBipartite_of_ladder_uniform`
  (`ℓ + ℓ * (k - 1) * (d - 1)`, i.e. `ℓ * (2 k - 1)` at `d = 3`, better than `2 * k * ℓ`),
  `JSP90.erdos73On_of_ladder`, `JSP90.erdos73On_of_ladder_subcubic`, and
  `JSP90.closeToBipartite_of_twoLevelGirth_degreeTwo` (`ℓ₁ + ℓ₂ * (k - 1)`, no degree factor at
  `d = 2`).

### Exactness at maximum degree `≤ 2`, for **every** `k`

`JSPProblem/Subcubic.lean` had only the `k = 1` level (`erdos73On_one_of_maxDegLe_two`).  Now:

* `JSP90.disjointFamily_oddCycles_of_maxDegLe_two` — the odd cycles of a graph of maximum degree `≤ 2`
  are pairwise vertex-disjoint;
* **`JSP90.maxDegLe_two_iff_oddCyclePackingLe` — `CloseToBipartite m G ↔ OddCyclePackingLe m G`**, i.e.
  the least odd cycle transversal *equals* the packing number;
* `JSP90.erdos73On_of_maxDegLe_two` — Erdős #73 on that class with the **optimal constant `k`** —
  and `JSP90.erdos73On_of_maxDegLe_two_optimal` / `JSP90.closeToBipartite_kTriangles_of_maxDegLe_two`
  (attained on `kTriangles k`, with the new `JSP90.maxDegLe_kTriangles`).

### Two machine-checked refutations (round 99's recorded target is false)

* **`JSP90.not_boundedOddGirthEdgeCount`: `JSP90.BoundedOddGirthEdgeCount` — "odd girth `ℓ` and degree
  `≤ d` ⟹ `f ℓ d`-close to bipartite" — is FALSE.**  For `ℓ = 3`, `d = 2` its hypothesis holds for every
  graph of maximum degree `≤ 2`, and `kTriangles (f + 1)` is not `f`-close to bipartite
  (`JSP90.maxDegLe_two_unbounded_oddCycles`).  Round 99's `next_bet (A)` is therefore closed as
  impossible, not unfinished.
* **`JSP90.not_oddGirth_bound_without_packing`: the *direction* of the girth hypothesis matters.**  An
  odd girth from **below** (`JSP90.OddGirthGe ℓ G`, added this round) bounds nothing — `kTriangles 5`
  has odd girth `3 ≤ 3` and needs `5` vertices — whereas the **upper** bound on the length of the odd
  cycles used by `Transversal.lean` is the one that pays.

### Reusable additions

`JSP90.maxDegLe_deleteFinset`, `JSP90.isOddCycle_of_isOddCycle_deleteFinset` (an odd cycle of `G - X`
is an odd cycle of `G` **as the same finset** — `Transversal.oddCycle_of_isOddCycle_delete` returns
*some* odd cycle), `JSP90.OddGirthGe.deleteFinset`, `JSP90.OddCyclePackingLe.succ_of_residue`.

`#print axioms` on all twenty headline results shows only `[propext, Classical.choice, Quot.sound]` —
no `sorryAx`.  `lake build` succeeds (1250 jobs) with **0 `sorry`, 0 `admit`**; `score.py --strict-prize`
reports `build_ok = true, partial_ok = true, prize_ready = false`, `missing_theorems =
["jsp_000090_main"]`.  What remains is `JSP90.OddCycleErdosPosa r` (behind it, Mader's structure
theorem); see `discovery/JSP-000090/policy.json` (`next_bet`: the **full** girth ladder, and maximal
packings).

---

## Round 101 — `JSPProblem/Stair.lean`: **THE FULL ODD-GIRTH LADDER**, `τ_odd(G) ≤ ∑_j g_j`

New file `lean/JSPProblem/Stair.lean` (28 declarations, 456 lines, **0 sorry/admit**, `lake build` OK
with 1251 jobs), imported from the root module `JSPProblem.lean` whose docstring was extended.  This
is the **forty-second attack family**, and it is exactly option (A) of round 100's `policy.json`.

### The statement

A *chain of odd cycles* `C 0, …, C (n-1)` (`JSP90.IsOddCycleChain`) is a sequence of vertex sets
such that `C j` is an **odd cycle of the residue of `H` after deleting `C 0, …, C j.succ`**
(`JSP90.residueOf H C j`).  With `(C j).card ≤ g j` and packing number at most `n`:

> **`JSP90.closeToBipartite_of_girthLadder`: `CloseToBipartite (g 0 + g 1 + … + g (n-1)) H`.**

There is **no degree bound, no packing-weight bound, no bound on the number of branch vertices and no
uniform bound on the length of an odd cycle**: each level pays exactly what it uses.

### The machinery (where the work is)

* `JSP90.residueOf`, `JSP90.deletedUpTo`, `JSP90.deletedUpTo_zero`;
* **`JSP90.residueOf_succChain` — THE SHIFT IDENTITY**:
  `residueOf (deleteFinset H (C 0)) (fun i => C i.succ) j = residueOf H C j.succ`, i.e. inside the
  residue `H - C 0` the tail `C 1, …` walks *exactly* the tail of the original chain.  All the index
  bookkeeping of the file lives in this lemma (its `deletedUpTo` form is
  `JSP90.deletedUpTo_succChain`);
* `JSP90.isOddCycleChain_succChain` — the shift of a chain of odd cycles is a chain of odd cycles;
* `JSP90.isBipartite_of_oddCyclePackingLe_zero` — packing number `0` ⟹ bipartite, the base case of
  every packing-number induction of this development in one line;
* the induction itself uses round 100's `OddCyclePackingLe.succ_of_residue` (the strictly decreasing
  quantity) and round 40's `closeToBipartite_of_residue`;
* the arithmetic: `JSP90.girthSum`, `JSP90.girthSum_succ`, `JSP90.girthExtend`, `JSP90.sum_fin_val`.

### The instances

* **`JSP90.erdos73On_of_girthLadder` — a new instance of the headline theorem**, with the constant
  `∑ j : Fin k, g j` and Erdős's own hypothesis `LocIndep k G` supplying the packing bound;
* **`JSP90.closeToBipartite_of_girthLadder_uniform` / `JSP90.erdos73On_of_girthLadder_uniform`
  re-derive `JSPProblem/Transversal.lean`'s `ℓ * k` instance *from* the ladder**, so that the
  comparison of the two instances is machine-checked rather than asserted: the ladder is a strict
  generalisation.  `JSP90.girthLadder_sum_le_mul` and `JSP90.girthLadder_sum_le_sub_one_mul` pin the
  comparison of the constants (`∑ g_j ≤ ℓ * k`, and `∑ g_j ≤ (ℓ-1) * k < ℓ * k` if every level pays
  at most `ℓ - 1`);
* **`JSP90.erdos73On_of_girthLadder_staircase` — the closed-form instance**: a chain whose levels grow
  like `3, 5, 7, …` gives `CloseToBipartite (k * k + 2 * k) G`, with the closed form proved
  (`JSP90.girthSum_arith`, `JSP90.staircase_const`) and
  **`JSP90.staircase_lt_uniform : k² + 2k < (2k + 1) * k` for `k ≥ 2`**, i.e. the ladder constant is
  strictly cheaper than the uniform one.  This is the only bound in the development whose constant
  depends on the *sequence* of level girths rather than on their maximum.

### What is *not* proved

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  Behind it stands
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  The
ladder *assumes* the chain (equivalently: that the residue chain has a short odd cycle at every
level); the missing global statement is that one can always *find* such a chain, or find a
transversal some other way.

### Toolchain facts verified this round (they cost most of the round)

`Fin.sum_univ_succ`, `Finset.range_succ` and `Finset.sum_univ_zero` are **not** in the pinned import
slice; `Finset.sum_range_succ'`, `Finset.sum_fin_eq_sum_range`, `Fin.sum_univ_eq_sum_range` are.
Consequently the ladder is phrased with `g : ℕ → ℕ` and `girthSum k g = ∑ i ∈ range k, g i`, whose
step reindexing is literally `Finset.sum_range_succ'`; the `Fin`-indexed statement is recovered with
`girthExtend`/`girthSum_extend`.  Further: `0 : Fin n` needs `[NeZero n]`, so a level index must be
`Fin (n+1)` and never `Fin n`; `(Finset.range k).biUnion` needs an `ℕ`-indexed family, so the chain
predicate is `((univ : Finset (Fin n)).filter (fun i => i.val < j.val)).biUnion C` rather than a
`biUnion` over a `range`; `Finset.sum_le_sum` and friends do not unify against a `Fintype.sum`
goal, so every sum is first moved to `range`-form; and `omega` is blind to `k * (k - 1)` versus
`k * k - k` (both appear as distinct atoms), so `k ≤ k * k` and `k < k * k` are the two lemmas
(`JSP90.nat_le_sq`, `JSP90.nat_lt_sq`) that the arithmetic needs.

---

## Round 102 — `JSPProblem/Greedy.lean`: **the GREEDY SHORTEST-ODD-CYCLE CHAIN** — the ladder with no chain and no girth hypothesis

New file `lean/JSPProblem/Greedy.lean` (72 top-level declarations, 870 lines, **0 `sorry`, 0 `admit`**,
`lake build` OK with 1252 jobs), imported from the root module `JSPProblem.lean` whose docstring was
extended.  Attack family 43.  `harness/score.py problems/JSP-000090` reports `build_ok = true,
sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true, missing_theorems =
["jsp_000090_main"]`.

### The question

Round 101 (`JSPProblem/Stair.lean`) proved the odd-girth ladder `τ_odd(H) ≤ g 0 + … + g (n-1)` from an
**assumed chain** `C 0, …, C (n-1)` of odd cycles, one per residue level, and recorded in
`policy.json` option (A) that the missing half is to stop assuming it.  This round **derives the chain
from the graph**: delete the *shortest* odd cycle, then the shortest odd cycle of the residue, and so
on.  Nothing has to be exhibited and **no girth hypothesis at all is needed**.

### The machinery

| result | content |
| --- | --- |
| `JSP90.girthOf H`, `JSP90.shortestOddCycle`, `JSP90.greedyCycle H` | the odd girth of `H` (vertices of a *shortest* odd cycle, `0` if `H` is bipartite) and a shortest odd cycle (`∅` if there is none); `JSP90.girthOf_le`, `JSP90.card_greedyCycle_le_girthOf`, `JSP90.three_le_girthOf` |
| `JSP90.level H j`, `JSP90.unionUpTo H j` | the residue after deleting the greedy cycles of the `j` earlier levels, and the set deleted; `JSP90.level_eq_deleteFinset_unionUpTo` says the two are complementary |
| `JSP90.greedyChain G k`, `JSP90.residueOf_greedyChain` | the greedy chain as a chain of `JSPProblem/Stair.lean`, and level `j` of it **is** level `j` of `JSP90.residueOf` — the bridge to round 101 |
| `JSP90.vertsOf`, `JSP90.isOddCycle_subset_vertsOf`, `JSP90.not_mem_of_mem_vertsOf_deleteFinset` | an odd cycle lives in the vertex set of its graph; a vertex of a deletion is not deleted |
| **`JSP90.disjoint_greedyCycle_of_lt`** | **two greedy cycles of different levels are vertex-disjoint** — the greedy step |
| **`JSP90.packing_of_levels`** | `n` non-bipartite levels give `n` vertex-disjoint odd cycles of `H` |
| **`JSP90.level_isBipartite_of_locIndep`** | Erdős's hypothesis makes the `k`-th level bipartite (a `k+1`-packing of greedy cycles would contradict `JSP90.locIndep_oddCyclePackingLe`) |
| `JSP90.firstBipartiteLevel` and its four lemmas | where the greedy construction stops |
| **`JSP90.level_tail`** | the chain is self-similar: `level (level H b) n = level H (b + n)` |
| **`JSP90.closeToBipartite_of_greedyChain_step`** | **the ladder with no packing bound**: the first `n` greedy cycles plus a bipartite residue at level `n` pay `∑ j < n, girthOf (level H j)` |

### The instances

* **`JSP90.erdos73On_of_greedyChain`, `JSP90.erdos73On_of_greedyChain_univ` — a new instance of the
  headline theorem**: `LocIndep k G → CloseToBipartite (∑ j : Fin k, girthOf (level G j)) G`.  The
  hypothesis is **exactly** Erdős's own; there is **no** girth bound, **no** degree bound, **no**
  packing-weight bound, **no** chain to exhibit and **no** connectivity or decomposition hypothesis.
  The constant is read off the graph: the sum of the odd girths of the greedy residues.
* **The certificate is exhibited** — `JSP90.closeToBipartite_of_greedyChain` (an explicit `X` with
  `X.card ≤ ∑ girthOf` and `(deleteFinset G X).IsBipartite`) and `JSP90.hitsOddCycles_greedyChain` /
  `JSP90.hitsOddCycles_of_bipartite_level` (the greedy cycles meet every odd cycle of `G`).
* **The comparison with the uniform bound is machine-checked** — `JSP90.greedySum_le_uniform`, so
  `JSP90.erdos73On_of_greedyChain_uniform` **re-derives** `JSPProblem/Transversal.lean`'s instance
  `CloseToBipartite (ℓ * k) G` from the greedy chain, and `JSP90.greedySum_lt_uniform` /
  `JSP90.erdos73On_of_greedyChain_strict` record when the new constant is *strictly* smaller
  (`JSP90.girthSum_lt_mul_of_short_first` is the arithmetic).

### What is *not* proved — and the blocker is now sharp

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.

Two failed steps are worth recording because they are the traps of this axis:

1. **`OddCyclePackingLe (firstBipartiteLevel G k) G` is not available.**  Erdős's hypothesis bounds
   packings by `k`, not by the length of a *maximal* greedy chain, and `P.card ≤ k` does not give
   `P.card ≤ j*`.  So round 101's ladder cannot be applied at the greedy chain length; this is why
   `JSP90.closeToBipartite_of_greedyChain_step` carries the hypothesis "the residue at level `n` is
   bipartite" instead of a packing bound — and that variant needs no packing hypothesis at all.
2. **Bipartiteness propagates FORWARD along the residue chain, never backward.**  A triangle with one
   vertex deleted is bipartite, so `level (j+1)` bipartite does *not* imply `level j` bipartite.  Only
   `JSP90.isBipartite_level_mono` (the true direction) is available, and the greedy construction
   therefore stops at `JSP90.firstBipartiteLevel`.

The remaining gap on this axis is now a **sharp mathematical statement**: the greedy sum
`∑ j, girthOf (level G j)` is **not** a function of `k` alone — a single cycle `C_m` satisfies
`LocIndep 1` and its greedy sum is `m` — so the greedy chain is exactly as strong as the uniform
`ℓ * k` instance, and beating it requires structural input on the odd-girth sequence (the
triangle / triangle-free case), which is where Reed–Robertson–Seymour–Thomas lives.  The quantitative
input this axis is still missing is `JSP90.OddCyclePackingLe (k - j) (level G j)`: the greedy cycles
of the earlier levels are `j` disjoint odd cycles of `G`, so any packing of level `j` adjoins them.
That, with the packing-number-sensitive instances already proved (`JSP90.erdos73On_of_helly_one`,
`JSPProblem/Residue.lean`'s `erdos73On_of_packing_one`), is the next step recorded in `policy.json`.

`#print axioms` on all ten headline results shows only
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

### Toolchain facts verified this round (they cost most of the round)

* **`Finset.mem_self` does not exist at this revision** — `Finset.mem` is `Multiset`-based
  (`Quot.lift …`), so `a ∈ s` for an abstract `s : Finset α` is **not** provable and `simp` cannot do
  it either.  Use `Finset.mem_insert_self a s` or extract a membership from `s.Nonempty`.
* **`Disjoint s t` is not `s ∩ t = ∅` definitionally**: `Finset.disjoint_iff_inter_eq_empty :
  Disjoint s t ↔ s ∩ t = ∅`, and building a `Disjoint` from an empty intersection is `.mpr` (with
  explicit `(s := _) (t := _)`, because the direction of `.mp`/`.mpr` here is the opposite of the
  naive reading).
* Applications of `Iff.mpr` and `Eq.trans` are elaborated **backwards** from the expected type; write
  `have h : <full statement> := <term>` to fix it instead of trusting the application's own
  unification.
* `rw` cannot match `∑ j : Fin n, f j.val` against `∑ j, f j` (higher-order pattern unification), so
  every conversion between the `Fin`-indexed and `range`-indexed forms of the constant is
  `have key : … := JSP90.sum_fin_val n (fun j => g j)` followed by `rw [key]`.
* A `calc` line ending in `:= by` swallows the following, more-indented `_ ≤` lines into the tactic
  block (a silent parse error surfacing at the *next* declaration).
* `Finset.sum_range_succ` **is** available at this revision (contrary to the round-101 note) and gives
  the unshifted step `JSP90.girthSum_succ'`, while `Finset.sum_range_succ'` is the shifted step that
  `JSPProblem/Stair.lean`'s `girthSum_succ` uses.
* `Nat.le_succ` is not an `iff` here; `Nat.eq_or_lt_of_le` and `Nat.lt_succ_iff.mp` are the tools.
* `Nat.find`, `Nat.find_spec`, `Nat.find_min'` need a `DecidablePred`: two *targeted* local instances
  suffice and are safer than `Classical.propDecidable` for all propositions; a file-wide
  `local instance (V : Type*) : DecidableEq V` makes `V` a metavariable in every statement that binds
  it only implicitly ("`Fintype ?m` is stuck").
* `SimpleGraph.IsBipartite` is the abbreviation `Colorable 2`, an **existential**: to use
  `hb : ¬ H.IsBipartite` one applies it to a proof of `H.IsBipartite`, and to get "no odd cycle" from
  `H.IsBipartite` one uses `JSP90.not_isOddCycle_of_isBipartite`.  Building a `Coloring` proof uses
  `⟨c, fun hab => ?⟩` with the adjacency argument **first** and implicit `a b` binders.
* An odd cycle of an induced subgraph is an odd cycle of the whole graph *as the same finset*:
  `JSP90.isOddCycle_deleteFinset` for deletions, `JSP90.isOddCycle_of_isOddCycle_level` for the chain.

## Round 104 (attack family 45) — the CLUSTER-GRAPH instance and its sharpness

New: `lean/JSPProblem/Cluster.lean` (40 declarations) and `lean/JSPProblem/ClusterSharp.lean`
(19 declarations), both imported from the root module; 0 `sorry`/`admit`, `lake build` green
(1255 jobs), `harness/score.py --strict-prize` reports `build_ok: true`, `partial_ok: true`,
`prize_ready: false` with `missing_theorems: ["jsp_000090_main"]`.

* **New instance, optimal constant** `JSP90.erdos73On_of_cluster`: if `G` is a disjoint union of
  complete graphs (`JSP90.ClusterDecomposition`, i.e. a clique decomposition by pairwise disjoint,
  pairwise anticomplete, vertex-covering pieces) and every induced subgraph of `G` has an
  independent set of size `≥ (|V(H)| − k)/2`, then `G` is the union of a bipartite graph and **at
  most `k` vertices**.
* **Hypothesis = conclusion on this class** `JSP90.closeToBipartite_iff_maxDef_cluster`:
  `CloseToBipartite m G ↔ MaxDef G ≤ m`, with `JSP90.maxDef_cluster`:
  `MaxDef G = ∑ C ∈ 𝒬, (|C| − 2)` (the deficiency is the sum of the piece costs).
* **Sharpness, machine-checked** `JSP90.erdos73On_of_cluster_optimal`: on `kTriangles k` the new
  instance is the equivalence `(LocIndep k → CloseToBipartite m) ↔ k ≤ m`, with
  `JSP90.maxDef_kTriangles_eq : MaxDef (kTriangles k) = k` and `JSP90.erdos73_cluster_notBelowK`
  (no `m < k` works).  The class is **strictly larger** than round 98's disjoint-odd-cycles class.

The required theorem `jsp_000090_main` (`Erdős73` for every `k`, i.e. `JSP90.OddCycleErdosPosa r`
for the 3-connected case) is **still missing**; nothing in this round removes a hypothesis for
arbitrary graphs.

---

## Round 108 — `JSPProblem/SplitSharp.lean`: the witness of the split-graph axis, and **`f(k) ≥ k + 1`**

New file `lean/JSPProblem/SplitSharp.lean` (29 declarations, 0 `sorry`/`admit`, `lake build` OK with
1259 jobs), imported from the root module `JSPProblem.lean`.  One line of `lean/JSPProblem/Deficiency.lean`
was also added (`isIndepSet_of_mem_indepSets`), and round 107's `Part 4` was **corrected in place**.

### A mathematical correction

Round 107 named, as the witness on which the constant `k + 1` of `erdos73On_of_splitPartition` is
attained, the graph "`K_{k+2,k+2}` minus a perfect matching", sides `A = {(i, false)}`,
`B = {(i, true)}`, with `(i, false) ~ (j, true)` exactly when `i ≠ j`.  **That graph is bipartite**
(at `n = 3` it is `C_6`): its "clique side" `B` carries no edge at all, so it is not a split graph
and round 107's instance does not apply to it.  The independent set round 107 proposed is not
independent either, because the cross edge `a_i ~ b_j` is **present** when `i ≠ j`: an independent
set containing `b_j` contains *at most* `a_j`, not all of `X ∩ A`.

### The correct witness, and what is now proved

`JSP90.splitWitness n` on `Fin n × Bool`, `Adj p q ↔ p.1 ≠ q.1 ∧ ¬ (p.2 = false ∧ q.2 = false)`:
`A = {(i, false)}` is independent, `B = {(i, true)}` is a clique, and `a_i ~ b_j` iff `i ≠ j`.

* `JSP90.splitWitness_splitPartition` — it **is** a split graph, with `n` vertices on each side;
* `JSP90.not_isolatedPair_splitWitness` — every pair of `B` has a common neighbour in `A`
  (`3 ≤ n`), so the `|B| − 2` regime of `closeToBipartite_split_iff` is unavailable;
* **`JSP90.locIndep_splitWitness` — `LocIndep k (splitWitness (k + 2))`** for every `k`.  The only
  counting input is `|X ∩ A| + |X ∩ B| = |I ∩ J| + |I ∪ J|` for the index sets
  `I = (X ∩ A).image Prod.fst` and `J = (X ∩ B).image Prod.fst`, together with
  `|I ∩ J| ≤ min |X ∩ A| |X ∩ B|` and `|I ∪ J| ≤ n`; the size-two independent set is the **edge**
  `{a_j, b_j}`, which exists precisely because the matching edge is absent;
* **`JSP90.indepCard_two` / `JSP90.maxDef_splitWitness` — `MaxDef (splitWitness (k + 2)) = k`**, the
  *exact value* of Erdős's hypothesis on this graph: it is tight, just as `kTriangles k` is;
* `JSP90.closeToBipartite_splitWitness` and `JSP90.not_closeToBipartite_splitWitness`, together with
  **`JSP90.closeToBipartite_iff_splitWitness` — `CloseToBipartite m (splitWitness (k + 2)) ↔ k + 1 ≤
  m`** for `k ≥ 1`: the exact value of the conclusion;
* **`JSP90.not_erdos73On_splitWitness` — `¬ Erdős73On k k` for every `k ≥ 1`.**  `Erdős73On k k` is
  the assertion "every finite graph satisfying `LocIndep k` is the union of a bipartite graph and at
  most `k` vertices", so this theorem says that **the constant `f(k)` of Erdős #73 satisfies
  `f(k) ≥ k + 1`**.  It is the first machine-checked lower bound on that constant that is *strictly
  larger* than the `f(k) ≥ k` of rounds 39/104, and — unlike every instance of the last thirty
  rounds — it is a statement about the answer to the problem, not only about a class;
* `JSP90.erdos73On_of_splitPartition_optimal` — the constant `k + 1` of round 107's split-graph
  instance is **optimal**.

So on this family the hypothesis allows `k` while the conclusion needs `k + 1`: it is the first
witness in this development on which the two sides of Erdős #73 do *not* coincide.

### What is *not* proved

The *upper* bound on `f(k)` — i.e. Erdős #73 itself, `jsp_000090_main` — is unchanged, and so is
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas, the 3-connected case).  `f(k) ≥ k + 1`
is a lower bound; the theorem needs a finite `f(k)`.  `jsp_000090_main` is therefore still **not**
declared, `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true, missing_theorems = ["jsp_000090_main"]`,
`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.

### A toolchain finding worth recording

`JSP90.instDecidableEqSplitGraph`, the `local instance` of `Split.lean`, **survives in the `.olean`
and is found by instance search for *any* type**.  An intersection built in a later module and one
built in `Split.lean` therefore do *not* match, and `Finset.mem_inter.mp`, `Finset.mem_union.mpr`,
`Finset.disjoint_iff_inter_eq_empty.mp` and `Finset.card_union_of_disjoint` all fail when the finsets
are not already pinned by the goal: the instance is synthesised on a metavariable first.  The working
incantations are (a) `simp only [Finset.mem_inter] at hp`, which matches the instance argument with a
metavariable, (b) `refine ⟨a, ?_⟩` instead of `⟨a, by …⟩`, (c) naming the finsets (`s := _`, `t := _`),
and (d) binding intermediates with `have`.  `JSP90.exists_mem_sdiff_pair_of_card_ge_three` of
`Split.lean` is unusable from `SplitSharp.lean` for the same reason.

---

## Round 109 — `JSPProblem/Chain.lean`: the DECREASE at a hard 1-cut, and the block-cut bound

Attack family 50, on the **packing-number axis**.  What is new is quantitative: round 48's 1-cut
axis (a) counted the charged parts and (b) named one missing lemma, `oneDepth_le_of_packing`.

### The new theorem of this round

**`JSP90.OneSplit.packing_part_le`** — *the decreasing lemma*.  If every packing of odd cycles of `G`
has at most `r` members, `sp` is a 1-cut of `G`, `s` is the number of its non-bipartite parts and
`i` is one of them, then **every packing of odd cycles inside `T_i` has at most `r + 1 − s`
members**.  Proof: a nonempty packing inside `T_i` together with one odd cycle in each of the
*other* non-bipartite parts is a packing of `G` — the parts are pairwise disjoint — of size
`|𝒞| + (s − 1)`, so `|𝒞| + s − 1 ≤ r`.  For `s = 2` this is a **strict** decrease
(`OneSplit.packing_part_le_lt`), and it is the induction step of the classical proof at a cut
vertex, which was not available in this development before this round.

Consequences:

* `OneSplit.packing_part_no_decrease_of_oneSide` — at a **one-sided** 1-cut (`s = 1`) the bound is
  inherited unchanged: the descent stalls.  This is the machine-checked form of round 48's negative
  result number 1.
* **`JSP90.closeToBipartite_of_1split_of_decreasing`** — **a new instance of the headline theorem**
  along the 1-cut axis: if the `s ≥ 2` non-bipartite parts are `m`-close to bipartite then a packing
  bound `r` forces `CloseToBipartite (1 + s · m) G`, and the hypothesis on the parts is needed only
  at the **decreased** bound `r + 1 − s` (rather than at `r`, as in round 48's
  `oddCycleErdosPosa_of_1split_of_bounded_pieces`).  The constant is independent of the number of
  parts, and no bound on the odd girth, packing weight or number of branch vertices is used.

### The block-cut bound, proved for the hard chains

* `HardCert G d` — a decomposition by `d` successive 1-cuts, each with at least two non-bipartite
  parts;
* **`exists_packing_of_hardCert`** — a non-bipartite graph with such a chain of depth `d + 1` has
  `d + 1` pairwise disjoint odd cycles;
* **`hardCert_isBipartite_of_packing_le`** — a packing bound `r` forbids a hard chain of `r + 1`
  cuts.  This is round 48's named missing lemma `oneDepth_le_of_packing` **in the form in which it
  is true**, and with it the *hard* half of the block-cut bound is a theorem.

### A machine-checked negative result

`JSP90.locIndep_param_cannot_be_lowered` — `LocIndep 1 (K_3)` holds while `¬ LocIndep 0 (K_3)`
(`LocIndep 0` ⟺ bipartite).  The classical descent therefore **cannot** be stated in Erdős's own
parameter, because `LocIndep` is monotone *increasing* in `k`; it runs on the packing number.  This
is why every statement of this file is in the packing language, which is also the language in which
the research statement `JSP90.OddCycleErdosPosa r` lives.

### What is *not* proved

`jsp_000090_main` is not declared and `JSP90.OddCycleErdosPosa r` is unchanged.  The remaining
obstruction is located exactly: the **one-sided chains** (cut vertices with a single non-bipartite
side).  They cannot be bounded by the packing number — a triangle with a pendant path has packing
number `1` and arbitrarily long such chains — and in the classical proof they are handled by the
block-cut tree and the short-C-path lemma (a C-path of length `≤ 2r + 1` between two disjoint odd
cycles).  `lake build` succeeds (1260 jobs), **0 `sorry`, 0 `admit`**, so `score.py --strict-prize`
reports `build_ok = true, partial_ok = true, missing_theorems = ["jsp_000090_main"]`.  No award
claim is made.

---

## Round 110 — `lean/JSPProblem/Piece.lean`: the CUT-VERTEX PIECE axis — **the one-sided 1-cut is free**

New module (34 declarations, 802 lines, **0 `sorry`, 0 `admit`**, `lake build` OK with 1261 jobs),
imported from the root module `JSPProblem.lean`.  Attack family 51.

Round 109 closed the 1-cut axis except for the *one-sided chains* and asked for the block-cut tree
or the short-`C`-path lemma.  **Neither is needed**: the right object is the *piece* `T_i ∪ {v}`,
not the part `T_i`, and

* **`JSP90.OneSplit.cycle_subset_piece`** — an odd cycle **containing** the cut vertex lies in a
  single piece (the companion of `JSPProblem/Connect.lean` `OneSplit.cycle_subset_part`, which says a
  cycle **avoiding** it lies in a single part);
* **`JSP90.OneSplit.isOddCycle_iff_pieces`** — **the odd cycles of `G` are exactly the odd cycles of
  the pieces**;
* **`JSP90.closeToBipartite_pieces_of_closeToBipartite`** — `CloseToBipartite m G` forces
  `CloseToBipartite m` on *every* piece, at the **same** constant;
* **`JSP90.closeToBipartite_of_1split_bounded_pieces`** — the composition **without the `+1`**
  (`m * t` against `1 + m * k`), the cut vertex being in every piece;
* **`JSP90.closeToBipartite_of_1split_twoPieces`** — the sharp `2 * m`, independent of `t`;
* **`JSP90.closeToBipartite_of_1split_nonBipartitePieces`** — only the non-bipartite pieces are
  charged, still without the `+1`;
* **`JSP90.closeToBipartite_iff_of_oneNonBipartitePiece`** — **THE ONE-SIDED 1-CUT IS FREE**:
  `CloseToBipartite m G ↔ CloseToBipartite m (T_{i₀} ∪ {v})`; together with
  `JSP90.isOddCycle_iff_of_oneNonBipartitePiece` and
  `JSP90.hitsOddCycles_iff_of_oneNonBipartitePiece` the reduction loses *nothing*: the whole
  odd-cycle structure of `G` is that of the single piece;
* **`JSP90.closeToBipartite_iff_of_twoSideCuts`** — the reduction **iterates**, i.e. the classical
  block-cut reduction in two steps;
* `JSP90.erdos73On_of_1split_of_bounded_PIECES`, `JSP90.oddCycleErdosPosa_of_1split_of_bounded_PIECES` —
  new instances of the headline theorem along the piece axis (hypothesis on the *pieces*, no
  counting step).

A **machine-checked obstruction** closes the axis: `JSP90.wf_oneSplit` is a 1-cut of the windmill at
`0`, `JSP90.not_isBipartite_wf_piece_0/1` show **two** of its pieces are non-bipartite, and
`JSP90.wf_locIndep_one_two_nonBipartitePieces` records `LocIndep 1 wf` together with `2 > k = 1`
non-bipartite pieces — so `|nonBipartitePieces| ≤ k` is false and no `f(k)` comes from this axis.

`jsp_000090_main` remains **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.  What is left is `JSP90.OddCycleErdosPosa r` for the graphs
with **no cut vertex** (the 2-connected case).

---

## Round 111 — `JSPProblem/CPath.lean`: the **C-PATH** and the **TWO-ATTACHMENT transversal**

Attack family 52, following the single step `discovery/JSP-000090/policy.json` named after round 110.
The file formalises **Mader's C-path** and turns it into a transversal bound, so it contributes a new
instance of the headline theorem and not only new vocabulary:

* **`JSP90.IsCPath`** — the object: a simple path of `d` steps from the vertex `f i` of a cycle `C`
  to the vertex `x ∉ C`, none of whose other vertices lies on `C`; its API (`IsCPath.card`,
  `IsCPath.adj_step`, `IsCPath.notMem_interior`) records that it has `d + 1` vertices, `d` edges and
  no interior vertex on `C`;
* **`JSP90.IsCPath.extend`** — a C-path may be **extended by one edge**;
* **`JSP90.IsOddCycle.exists_edge_avoiding`** — a cycle of length `≥ 3` has an edge avoiding any
  prescribed vertex of it;
* **`JSP90.closeToBipartite_of_twoAttach`** — **THE TWO-ATTACHMENT TRANSVERSAL**: if every odd cycle
  of `G` meets the odd cycle `C` in at least two vertices, then `CloseToBipartite (|C| - 1) G`;
* **`JSP90.erdos73On_of_twoAttach`** — a **new instance of the headline theorem**: with
  `LocIndep k G` and that attachment hypothesis, `CloseToBipartite (|C| - 1) G`, with the constant
  **independent of `k`** — the first transversal bound in this development that does not grow with
  Erdős's local parameter, against `ℓ * k` of `JSP90.erdos73On_of_bounded_odd_girth`.

`lake build` completes (1262 jobs) with **0 `sorry`, 0 `admit`**, so `score.py --strict-prize` reports
`build_ok = true, partial_ok = true, missing_theorems = ["jsp_000090_main"]`; `formalization.yaml`
remains `status: wip`, `prize_ready: false`.  No award claim is made.

**What is not proved.**  The second half of the named step — *the shortest `C`-path is induced* —
requires `JSP90.IsCPath.skip` (a chord shortens the path), `JSP90.IsCPath.Shortest` (minimality) and
`JSP90.IsCPath.induced_of_shortest`; the index arithmetic of the splice
(`skipPath`, `skipPath_le`, `skipPath_gt`, `skipPath_end`, `skip_idx_lt`, `skip_idx_inj`) is written
out in the file and compiles, the theorem bodies did not close within the round, and those five names
are the concrete next steps recorded in `discovery/JSP-000090/policy.json`.  `JSP90.OddCycleErdosPosa r`
and `jsp_000090_main` are unchanged; the two-attachment class does not contain all 2-connected graphs.

---

## Round 114 — `JSPProblem/CPathPair.lean`: MADER'S TWO-ATTACHMENT LEMMA (the FAN at depth two)

The single missing structural lemma named by round 112's `policy.json` — *"the depth-two
attachment: for `x` not on `C` with two internally vertex-disjoint `C`-paths to distinct vertices of
`C`, their union with one of the two arcs of `C` is an odd cycle"* — is now **proved**, together with
the parity split that says *exactly one* of the two arcs does the job:

* `JSP90.IsCPathPair` (the object: two internally vertex-disjoint `C`-paths to a common target) and
  `JSP90.IsCPathPair.inter_ne` (the two interiors never meet);
* `JSP90.arcPairFun` + `JSP90.arcPairFun_inj` + `JSP90.arcPairFun_adj` + `JSP90.arcPair_isOddCycle`
  + `JSP90.card_arcPair`: the closed walk `arc + p + q` is a **simple odd cycle** of `G` with exactly
  `e + d1 + d2` vertices — a strict generalisation of `JSPProblem/Fan.lean`'s `arc_isOddCycle`;
* **`JSP90.exists_oddCycle_twoAttach_of_isCPathPair` — MADER'S TWO-ATTACHMENT LEMMA**: `x` lies on
  an odd cycle of `G` through both attachment points.  The two candidate totals add up to
  `m + 2 (d1 + d2)`, which is odd, so exactly one of them is odd (`JSP90.mod_two_of_sum_odd`);
* `JSP90.arc_sum_ge_of_shortest` (**a shortest odd cycle is thick**),
  `JSP90.oddArc_eq_two_of_fan_of_shortest` (the odd arc of a fan has length `m - 2`) and
  `JSP90.shortArc_of_pairFan` (the short-arc lemma re-derived from Mader's lemma), with the depth-one
  input *derived* by `JSP90.IsCPath_edgePath` and `JSP90.isCPathPair_of_adj`;
* `JSP90.twoAttach_kTriangles_one` (the hypothesis holds on `kTriangles 1`) and
  **`JSP90.not_twoAttach_kTriangles_two`** (machine-checked negative result: on `kTriangles 2` no odd
  cycle is two-attached).

**What this does not give.**  A transversal.  Mader's lemma supplies one odd cycle through a fan
vertex; the two-attachment *cover* of round 112 (`JSP90.closeToBipartite_of_twoAttachCover`) needs the
hypothesis for **every** odd cycle of `G`.  The remaining statements are therefore

* `JSP90.twoAttachCover_exists` — for an odd cycle `C` of a graph `G`, a finite family `𝒞` of vertex
  sets with `∑_{X ∈ 𝒞} (|X| - 1)` bounded by a function of the odd cycle packing number, such that
  every odd cycle of `G` meets some `X ∈ 𝒞` in two vertices (the statement round 112 named); and
* the absorption of the one-attachment odd cycles `JSP90.oneAttach_of_isCPath_return` along 2-cuts
  (`JSP90.VertexSplit.closeToBipartite_two_of_nonBipartiteParts`), with the bound on the number of
  such 2-cuts.

Neither is proved; `JSP90.OddCycleErdosPosa r` and `jsp_000090_main` are unchanged.

## Round 112 — `JSPProblem/CPathSkip.lean`: the C-path shortcut, the shortest C-path is induced, the closed C-path is an odd cycle, and the TWO-ATTACHMENT COVER

Round 111's `policy.json` named four concrete next lemmas.  **All four are now proved**, with
`lake build` OK (1263 jobs), 0 `sorry`, 0 `admit`:

1. `JSP90.IsCPath.skip` — a chord `p a ~ p b` of a `C`-path (`a + 2 ≤ b ≤ d`) shortens it to a
   `C`-path to the same target of length `a + 1 + (d - b) < d` (`JSP90.skip_len_lt`);
2. `JSP90.IsCPath.Shortest` + **`JSP90.IsCPath.induced_of_shortest`: THE SHORTEST `C`-PATH IS
   INDUCED** (minimality must be a hypothesis — `Nat.find` needs a `DecidablePred` and the predicate
   quantifies over a *function*);
3. `JSP90.IsCPath.adj_target_of_shortest` (Mader's neighbour count at the far end) and
   `JSP90.IsCPath.adj_iff_step_of_shortest` (the full neighbour count);
4. **`JSP90.IsCPath.isOddCycle_return`** — a closed `C`-path of even length is an odd cycle of `G`;
   `JSP90.oneAttach_of_isCPath_return` records that it meets `C` in **exactly one vertex** and
   contains the target.

**The transversal payoff: the TWO-ATTACHMENT COVER.**  `JSP90.TwoAttachCover G 𝒞 pick` says that a
vertex `pick X` is chosen in each member of a family `𝒞` of vertex sets and that every odd cycle of
`G` meets some member of `𝒞` in at least two vertices.  The members need **not** be odd cycles and
their number is **unbounded**, so this is a **strict generalisation** of round 111:

* `JSP90.hitsOddCycles_of_twoAttachCover` — the certificate
  `𝒞.biUnion (fun X => X.erase (pick X))`;
* `JSP90.card_biUnion_erase_le_sum_card_sub_one_of_twoAttachCover` — its cost
  `≤ ∑ X ∈ 𝒞, |X| - 1`;
* `JSP90.closeToBipartite_of_twoAttachCover` — `CloseToBipartite (∑ X ∈ 𝒞, |X| - 1) G`;
* `JSP90.exists_mem_inter_erase_of_card_ge_two` — the counting input: an odd cycle meeting `X` in two
  vertices also meets `X` minus any one of them;
* `JSP90.closeToBipartite_of_twoAttachCover_of_singleton` and `JSP90.sum_card_sub_one_singleton` —
  round 111's theorem as the singleton cover, so the cover theorem is never weaker.

**New instances of the headline theorem** (constants independent of Erdős's `k`):

* `JSP90.erdos73On_of_twoAttachCover` — cost `∑ X ∈ 𝒞, |X| - 1`;
* `JSP90.erdos73On_of_twoAttachCover_bounded` — cost `ℓ * |𝒞|` when every member has at most `ℓ`
  vertices: the Erdős–Pósa shape, one unit per cover member.

**What is still missing, unchanged.**  `jsp_000090_main` is not declared and
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) is not proved.  The one-attachment
lemma yields an odd cycle attached to `C` **once**, and no transversal pays for that; the
*two-attachment cover* is the hypothesis that pays, and its existence for a 3-connected graph is
the unresolved part.  The exact remaining lemmas are recorded in
`discovery/JSP-000090/policy.json` (`next_bet`).


---

## Round 115 — the residual lemma is now a single `def`

`JSPProblem/TwoAttach.lean` states the residual global lemma and reduces the whole problem to it:

* **`JSP90.TwoAttachCoverExists r ℓ q`** — `def` (no assumption, no placeholder): for every finite
  graph whose odd cycle packings all have at most `r` members there is a family `𝒞` of at most `q`
  nonempty vertex sets, each of at most `ℓ` vertices, such that every odd cycle of the graph meets
  some member in at least two vertices;
* **`JSP90.oddCycleErdosPosa_of_twoAttachCoverExists`** — `TwoAttachCoverExists r ℓ q` ⇒
  `OddCycleErdosPosa r`, constant `ℓ * q`;
* **`JSP90.erdos73_of_twoAttachCoverExists`** — `∀ ℓ q, ∀ r, TwoAttachCoverExists r ℓ q` ⇒
  `∀ k, Erdős73 k`, i.e. **`jsp_000090_main`**.

Supporting results of the same file: `JSP90.exists_oneSidedDeletion` (a family of nonempty sets has a
deletion set leaving at most one vertex per member — no graph in the statement),
`JSP90.closeToBipartite_of_twoAttachCover'` and `JSP90.closeToBipartite_of_twoAttachCover'_bounded`
(the cover theorem without a choice function, and its `ℓ * q` bounded form),
`JSP90.erdos73On_of_twoAttachCover'` (a further instance of the headline theorem with a constant
independent of `k`), `JSP90.cover_cost_min_kTriangles` (**the minimum cost of a cover of `kTriangles k`
is exactly `k`**, its odd cycle transversal number — the method is optimal in constant), and
`JSP90.packing_cover_cost_two_of_kTriangles` (**a cover made of odd cycles costs `2 * k` there**, so
cover members must be allowed to be non-cycles).

**What is still missing, unchanged.**  `jsp_000090_main` is not declared and
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) is not proved: the existence of the cover
`𝒞` itself is the missing combinatorial content, and so is the absorption of the one-attachment odd
cycles of `JSP90.oneAttach_of_isCPath_return`.  See `discovery/JSP-000090/policy.json`.

---

## Round 118 — `JSPProblem/CriticalSharp.lean`: the SPREAD CONSTANT, and the machine-checked
## refutation of round 53's residual lemma

New file `lean/JSPProblem/CriticalSharp.lean` (29 declarations, 0 placeholders, `lake build` OK with
1267 jobs), imported from the root module `JSPProblem.lean`.  This is the **fifty-sixth** attack
family, and the first to attack a *previous round's own reduction* rather than the problem.

### The target attacked

`JSPProblem/Critical.lean` (round 53) proved the counting lemma

```lean
JSP90.card_X_le_of_colouring_pack : (critical intersection graph of X is c-colourable)
                                  → (every packing has ≤ k members) → |X| ≤ c * k
```

and localised the whole of Erdős #73 to `JSP90.SpreadMinimalTransversal r c` (every graph of odd cycle
packing number at most `r` admits a minimal transversal whose critical intersection graph is
`c`-colourable), with `JSP90.erdos73_of_spreadMinimalTransversal` proving `∀ k, Erdős73 k` from
`∀ r, SpreadMinimalTransversal r c` for one **fixed** `c`.  Its header also asserted that "`c = 2`
is the classical shape of the Reed–Robertson–Seymour–Thomas theorem".

### What is proved

* **Complete graphs carry critical data exactly at size `n - 2`**
  (`card_le_sub_two_of_hitsOddCycles_completeGraph`,
  `card_lt_sub_two_of_not_hitsOddCycles_completeGraph`, `card_compl_eq_two`,
  `exists_transversal_completeGraph`, `minimalTransversal_card_completeGraph`,
  `card_criticalTransversal_completeGraph`, `exists_criticalTransversal_completeGraph`): a set of `K_n`
  meets every odd cycle iff `n ≤ |X| + 2`, and **any** set carrying critical data has `|X| = n - 2`,
  because a critical cycle of `x ∈ X` has at least three vertices and they all lie in
  `{x} ∪ (V \ X)`.
* **The critical intersection graph of `K_n` is complete on the transversal**
  (`criticalCycle_eq_completeGraph`, `mem_compl_of_criticalCycle`, `adj_IntGraph_completeGraph`):
  every critical cycle of `x` is exactly the triangle `{x} ∪ (V \ X)`, so any two of them meet in the
  two vertices outside `X`.
* **`JSP90.spreadTransversal_completeGraph_iff` — THE SPREAD CONSTANT OF A COMPLETE GRAPH, EXACTLY:
  `SpreadTransversal c (completeGraph (Fin n)) ↔ (n - 2 ≤ c ∧ 0 < c)`**, and
  `spreadTransversal_completeGraph_iff'` (for `n ≥ 3`, where the positivity is automatic).
  Consequently `spreadTransversal_completeGraph_four` (`K_4 ↔ 2 ≤ c`),
  `spreadTransversal_completeGraph_five` (`K_5 ↔ 3 ≤ c`) and `spreadTransversal_completeGraph_two`
  (`K_2 ↔ 0 < c`): the minimum spread constant of the family `K_n` is unbounded.
* **`not_spread_transversal_two_completeGraph_five`** — round 53's `c = 2` claim is refuted.
* **The packing bound of a complete graph** (`sum_card_le_of_disjointFamily`,
  `sum_card_le_of_disjointFamily_sub`, `mul_three_le_of_packing_completeGraph`,
  `packing_card_le_completeGraph`): a packing of odd cycles of `K_n` has at most `⌊n / 3⌋` members.
* **`spreadMinimalTransversal_c_ge`, `not_spreadMinimalTransversal_of_packing`,
  `no_fixed_spreadConstant` — NO FIXED COLOUR COUNT WORKS.**  `SpreadMinimalTransversal r c` forces
  `3 * r - 2 ≤ c` (witness `K_{3r}`), hence `¬ (∃ c, ∀ r, SpreadMinimalTransversal r c)`: the
  class-level hypothesis of `erdos73_of_spreadMinimalTransversal` is **false** and that route is
  closed.
* **`spreadConstant_exact_completeGraph` — the bound `3 * r - 2` is SHARP**: `K_{3r}` has odd cycle
  packing number at most `r` and its minimum spread constant is exactly `3 * r - 2`, so `3r - 2` is
  the least colour count such a class-level hypothesis can ask for, and it is forced;
* **`exact_spread_constant_locIndep`, `spread_constant_ge_of_locIndep` — and the route is quadratic
  anyway.**  `K_{k + 2}` satisfies `LocIndep k` and has spread constant exactly `k`, while
  `card_X_le_of_colouring` turns a `c`-colourable critical intersection graph into `|X| ≤ c * k`; so
  every instance obtained by this route carries a constant of at least `k * (k + 2)`, whereas the
  Erdős–Pósa theorem for odd cycles has the constant `O(k log k)`.

### What is *not* proved

`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) is untouched, and `jsp_000090_main` is
**not** declared, so the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`;
`score.py --strict-prize` reports `build_ok = true, sorry = 0, admit = 0, partial_ok = true`.
`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.  What this
round removes is one *route* to the theorem — together with round 117's removal of the
two-attachment-cover route — and records, machine-checked, the exact lower bound that any instance of
that shape must pay.

---

## Round 119 — `JSPProblem/Petal.lean`: the ONE-ATTACHMENT odd cycles, the PETAL SET, and the
## absorption step with a growing parameter

New file `lean/JSPProblem/Petal.lean` (21 declarations, 0 sorry/admit, `lake build` OK with 1268
jobs), imported from the root module `JSPProblem.lean`.  This is the **fifty-seventh** attack family,
and the first to make the *absorption step* of the residue induction quantitative.

`policy.json` (round 118) asked for the counting half of the Mader step, i.e. how many
**one-attachment** odd cycles can hang off a shortest odd cycle and how they are absorbed.  Rounds 117
and 118 had killed the two-attachment-cover route and the `c`-spread-transversal route, so this round
does not restart either; it introduces the finite quantity that both need.

### The new objects

* **`JSP90.OneAttach G C D`** — `D` is an odd cycle of `G` meeting `C` in **exactly one** vertex: a
  *petal* attached to `C` at a single point, `D ∩ C` being its attachment point.
* **`JSP90.PetalSet G C`** — the **petal set** (attachment set): the vertices `v ∈ C` which lie
  *alone* on some odd cycle of `G`, i.e. the attachment points of the petals.  `petalSet_subset`
  gives `PetalSet G C ⊆ C`, so `card_petalSet_le_card` bounds it by `|C|`; `petalSet_empty_of_isBipartite`
  makes it empty for a bipartite graph; `oneAttach_mem_petalSet` says every petal is met by it.

### What is proved

1. **`JSP90.petalSet_transversal` — THE PETAL-SET TRANSVERSAL.**  If `C` is an odd cycle of `G` and
   *every* odd cycle of `G` meets `C`, then some set **contained in `C`** with at most
   `|C| - 1 + |PetalSet G C|` vertices meets every odd cycle of `G`.  The certificate is
   `C.erase c ∪ PetalSet G C` for **any** `c ∈ C`; the proof is the two cases of an odd cycle `D`:
   `|D ∩ C| ≥ 2` ⟹ `D` meets `C.erase c` (`JSP90.exists_mem_inter_erase_of_card_ge_two`), and
   `|D ∩ C| = 1` ⟹ that vertex is an attachment point.  The certificate is a subset of `C`, so it is
   never weaker than the trivial "`C` meets every odd cycle".

2. **`JSP90.closeToBipartite_of_petalSet`, `JSP90.erdos73On_of_petalSet` — A NEW INSTANCE OF THE
   HEADLINE THEOREM WITH A GROWING PARAMETER `a`:**  `LocIndep k G`, an odd cycle `C` meeting every
   odd cycle of `G` (equivalently `G - C` bipartite) and at most `a` attachment points give
   `CloseToBipartite (a + |C| - 1) G`; the constant does **not** grow with `k` (and Erdős's hypothesis
   is not needed for this step at all — the transversal is built from the structure at `C` alone).

3. **`JSP90.closeToBipartite_of_residue_petalSet` — THE ABSORPTION STEP, QUANTIFIED.**  Round 40's
   induction step is `CloseToBipartite q (G - C) → CloseToBipartite (q + |C|) G`, and the `+|C|` is
   the recorded blocker.  This file improves it: with `|PetalSet G C| ≤ a` the step costs
   `q + a + (|C| - 1)`, and `JSP90.closeToBipartite_of_residue_petalSet_zero` (empty petal set) costs
   **`q + |C| - 1`, one vertex less than round 40**.  So the `|C|` term is only ever needed to pay for
   the attachment points; what is missing is a bound on those points in terms of `k`.
   `JSP90.erdos73On_of_petalSet_of_residue` is the corresponding instance form.

4. **`JSP90.closeToBipartite_of_petalSet_empty` and `JSP90.closeToBipartite_of_twoAttach'`**:
   round 111's two-attachment transversal `JSP90.closeToBipartite_of_twoAttach` (constant `|C| - 1`)
   is **re-derived**, because "every odd cycle meets `C` in at least two vertices" is exactly
   "`PetalSet G C = ∅`".  So the new instance is never weaker than round 111's.

5. **`JSP90.IsOddCycle.of_finset_ext` / `JSP90.IsOddCycle.of_finset_eq`** — transport lemmas for the
   `IsOddCycle` predicate along an equality of vertex sets.  These remove the instance pitfall
   recorded in the round-53 header: a `Finset (Fin n)` built with the classical `DecidableEq`
   instance (the one inside the statements of `JSPProblem/Transversal.lean`) is *equal* to but not
   syntactically the finset one gets with the computable instance, which is why round 53's `K_4`
   witness did not elaborate.  Reusable by any later concrete witness.

### A mathematical point worth recording

The certificate `C.erase c ∪ PetalSet G C` is a **subset of `C`**, so the petal-set transversal can
never be worse than deleting all of `C`; and it is *strictly* better exactly when the attachment points
avoid `c`.  Conversely, one vertex cannot always be removed: the natural strengthening of round 111
obtained by dropping "in at least **two** vertices" is FALSE, and the minimal witness is the nine-vertex
cactus *triangle with a pendant triangle at each vertex* (vertices `0..8`; triangles `{0,1,2}`,
`{0,3,4}`, `{1,5,6}`, `{2,7,8}`; no other edges, `C = {0,1,2}`): the residue `G - C` is the matching
`3-4, 5-6, 7-8`, hence every odd cycle meets `C`; each pendant triangle meets `C` in exactly one
vertex, so `PetalSet G C = C`; and the three pendant triangles are pairwise disjoint, so
`¬ CloseToBipartite 2 G = ¬ CloseToBipartite (|C| - 1) G`.  The construction is **not** in this round's
build: it is written out in `discovery/JSP-000090/policy.json` together with the four elaboration
pitfalls that cost this round most of its time (the `DecidableEq` baked into `Finset.inter`; `decide`
being unusable once the classical instance is in scope; `Finset.image` fixing an instance in the
`IsOddCycle` statement; `Finset.card` of a literal needing a computable instance).

### What is *not* proved

The **counting bound on `|PetalSet G C|`** — the Mader step itself.  At a shortest odd cycle with
`|C| >= 5` a vertex outside `C` meets `C` in at most two vertices two steps apart
(`JSPProblem.card_inter_neigh_le_two`, `JSPProblem/shortArc_of_shortest`, both proved), and the family
of petals must then be charged against the packing number.  Without such a bound `a` is not known to
be `O(k)`, so `JSP90.erdos73On_of_petalSet` does not close Erdős #73.
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) and `jsp_000090_main` are unchanged, and
`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  `#print axioms` on the six headline
declarations of the round gives only `[propext, Classical.choice, Quot.sound]`.
`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 120 — `lean/JSPProblem/PetalBound.lean` + `lean/JSPProblem/PetalFinite.lean`: the
# attachment set is NOT charged against the deficiency, and a new instance with constant `k + |C| - 1`

Round 119 left one concrete blocker: the absorption step is `q + |PetalSet G C| + (|C| - 1)`, so the
missing lemma is a *numerical* one — a function `phi(k)` with `|PetalSet G C| ≤ phi(k)` — and the
nine-vertex witness promised for that step was not in the build.  This round answers both halves.
Two new files, 132 declarations, **0 sorry / 0 admit**, `lake build` OK (1270 jobs).

### Part 1–2 — the charging lemmas and a NEW INSTANCE of the headline theorem

A *petal* of an odd cycle `C` is an odd cycle meeting `C` in exactly one vertex (`JSP90.OneAttach`);
`PetalSet G C` is the set of attachment points.  Two attachment points covered by a **packing** of
petals must be covered by *different* members, so

* **`JSP90.card_petalSet_inter_biUnion_le_card`** — the attachment points lying on a family `𝒟` of
  petals number at most `|𝒟|`;
* **`JSP90.card_petalSet_inter_biUnion_le_maxDef`** — and at most `MaxDef G`, because a packing of
  petals is a packing of odd cycles and `JSP90.card_le_of_maxDef_le` charges a packing of odd cycles
  against the deficiency (`LocIndep k G` ↔ `MaxDef G ≤ k`);
* **`JSP90.card_petalSet_le_maxDef_of_cover`** — hence **`|PetalSet G C| ≤ MaxDef G`** whenever the
  attachment set is covered by a packing of petals: the shape of the round-119 bound, under one
  extra (packing) hypothesis;
* **`JSP90.card_petalSet_le_maxDef_add`** — the general form, leaving exactly the attachment points
  the packing misses;
* **`JSP90.exists_petal_hits_biUnion_offC`** — **what a maximal petal packing does NOT pay for**:
  every attachment point outside the packing carries a petal meeting the packing **off `C`**;
* **`JSP90.closeToBipartite_of_petalSet_le_maxDef`** — the bridge: *any* bound on the attachment set
  in terms of `MaxDef G` turns into Erdős's conclusion.

From the first of these, **a new instance of the headline theorem**:

* **`JSP90.closeToBipartite_of_petalPackingCover` / `JSP90.erdos73On_of_petalPackingCover`** with the
  constant **`k + |C| - 1`** — Erdős's hypothesis, an odd cycle `C` meeting every odd cycle of `G`, and
  a packing of petals covering the attachment set;
* its triangle level **`JSP90.closeToBipartite_of_petalPackingCover_triangle`, constant `k + 2`**, and
  the odd-girth form `…_of_card_le` (`k + ℓ - 1`);
* **`JSP90.OneCyclePetal G ℓ`** — the class-level statement, a `def` and **not** assumed (the shape of
  round 115's `TwoAttachCoverExists`), with the reduction `JSP90.erdos73On_of_oneCyclePetal`.

### Part 3–4 — the nine-vertex propeller: the `|C| - 1` term is not enough once petals exist

`prop` (`JSPProblem/PetalFinite.lean`) is the triangle `0 - 1 - 2 - 0` with a pendant triangle at each
of its vertices.  With `C = {0, 1, 2}` the three pendant triangles are petals, and

* `maxDef_prop : MaxDef prop = 3`, `petalSet_propC : PetalSet prop propC = propC`,
  `isBipartite_delete_propC` — so every odd cycle of `prop` meets `C` (`hitsOddCycles_propC`);
* `closeToBipartite_three_prop` and **`not_closeToBipartite_two_prop`**: the odd cycle transversal
  number of the propeller is exactly `3 = |C|`.  Hence
  **`JSP90.not_closeToBipartite_two_prop_of_cardC`** refutes `CloseToBipartite (|C| - 1) G` on a graph
  whose attachment set is non-empty: the `|C| - 1` bound of `JSP90.closeToBipartite_of_petalSet_empty`
  — and with it the two-attachment transversal of round 111 — genuinely needs its hypothesis.  This is
  the witness promised by round 119;
* the three pendant triangles **are** a packing of petals covering the attachment set
  (`isOddCycleFamily_propPetals`, `prop_petalPackingCover`), so the new instance applies to `prop`:
  `erdos73On_propeller` gives `CloseToBipartite (3 + |C| - 1) = CloseToBipartite 5 prop`, and
  `oneCyclePetal_prop` realises the class-level statement.

### Part 5 — the seven-vertex `g7`: the attachment set is LARGER than the deficiency

`g7` is `K_4` on `{0, 1, 2, 3}` with an independent set `{4, 5, 6}`, where `4 ~ {0, 3}`, `5 ~ {1, 3}`,
`6 ~ {2, 3}`.  With `C = {0, 1, 2}` the triangles `{0, 3, 4}`, `{1, 3, 5}`, `{2, 3, 6}` are petals, and

* `maxDef_g7 : MaxDef g7 = 2`, `petalSet_g7C : PetalSet g7 g7C = g7C`, `card_petalSet_g7C = 3`;
* **`JSP90.not_petalSet_le_maxDef_g7 : ¬ (|PetalSet g7 g7C| ≤ MaxDef g7)`** — a machine-checked
  refutation of the first guess at the round-119 bound: any `phi` with
  `|PetalSet G C| ≤ phi (MaxDef G)` must have `phi 2 ≥ 3`, so `phi` is neither `MaxDef` nor
  `MaxDef / 2`;
* `not_inter_empty_g7T0_g7T1` and `not_oddCycleFamily_g7Petals`: the three petals all contain the
  vertex `3`, so they are **not** a packing — the packing-cover hypothesis is real content, and it is
  exactly what `g7` fails.

### What is *not* proved

`PetalSet G C ⊆ ⋃ 𝒟` for a packing of petals (`JSP90.OneCyclePetal`) is **not** available in general:
`JSP90.card_petalSet_le_maxDef_add` and `JSP90.exists_petal_hits_biUnion_offC` say exactly what is
missing — the attachment points whose petals all pass through a point of the packing outside `C`.
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) and `jsp_000090_main` are unchanged, and
`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true, prize_ready = false`.  `#print axioms` on
the headline declarations of the round gives only `[propext, Classical.choice, Quot.sound]`.
`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 122 — `JSPProblem/HubSharp.lean`: the HUB COVER is never cheaper than the truth, the residual
## `HubByPacking` FORCES `ℓ + q ≥ 3r - 1`, and the residual is FALSE at `r = 0`

New file `lean/JSPProblem/HubSharp.lean` (21 declarations, **0 `sorry`, 0 `admit`**, `lake build` OK with
1272 jobs), imported from the root module `JSPProblem.lean` — **which this round also fixed**: round
121's `JSPProblem/Hub.lean` had never been added to the root module, so it was dead code, and round
121's `JSPProblem/Wheel.lean` **does not compile** (see below).  `harness/score.py problems/JSP-000090`
reports `build_ok: true, sorry: 0, admit: 0, partial_ok: true, prize_ready: false`,
`missing_theorems: ["jsp_000090_main"]`.

### The live residual

```lean
JSP90.HubByPacking (r ℓ q : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] (G : SimpleGraph W), OddCyclePackingLe r G →
    ∃ C Z : Finset W, IsOddCycle G C ∧ C.card ≤ q ∧ HubCover G C Z ∧ Z.card ≤ ℓ
```

`JSPProblem/Hub.lean` (round 121) reduces `jsp_000090_main` to it; this round attacks it.

### 1. The repaired numerical route: hubs count the attachment points at a *shortest* odd cycle

Round 121 refuted **every** bound `|PetalSet G C| ≤ φ(MaxDef G)` (wheel family).  This round shows why
that is not fatal and what replaces it:

* **`JSP90.card_petalSet_inter_attachSet_le_two`** — at a **shortest** odd cycle `C` with `|C| ≥ 5`, the
  attachment points of `C` which are adjacent to a vertex outside `C` number at most **two**
  (`JSP90.card_attachSet_le_two` of `JSPProblem/Book.lean`).
* **`JSP90.card_petalSet_le_of_hubCover_trianglePetals`** — **if every petal of `C` is a triangle**,
  then a hub cover `Z` of `C` satisfies **`|PetalSet G C| ≤ |Z ∩ C| + 2 * |Z \ C|`**: an attachment
  point outside `Z` carries a triangle petal, whose hub vertex is **adjacent to it**, so the
  attachment points are counted twice over by the hubs.  The wheel escapes exactly because its rim is
  *not* a shortest odd cycle (its triangles are shorter).
* **`JSP90.card_petalSet_gt_of_hubCover_of_longPetal`** — the contrapositive: if
  `|Z ∩ C| + 2 * |Z \ C| < |PetalSet G C|` then **some petal of `C` has at least five vertices**.
* `JSP90.adj_of_oddCycle_card_three`, `JSP90.card_mod_two_of_isOddCycle` — the two small helpers
  (two vertices of an odd cycle of cardinality three are adjacent; the cardinality of an odd cycle is
  odd).

### 2. The instance is never better than the truth

* **`JSP90.hubCost_ge_completeGraph`** — **`hubCost C Z = |C| - 1 + |Z| ≥ n - 2` for every hub cover
  `(C, Z)` of `K_n`**, and `n - 2` is the odd cycle transversal number of `K_n`.  So the certificate
  `(C.erase c) ∪ Z` of round 121 is **never cheaper than the optimal transversal**, and the constant
  `ℓ + (q - 1)` of the reduction cannot be improved on complete graphs.
* Supporting: `JSP90.card_univ_sub_add`, **`JSP90.card_compl_le_two_completeGraph`** (a set meeting
  every odd cycle of `K_n` leaves at most two vertices out), `JSP90.mem_triple_iff`,
  `JSP90.isOddCycle_triple_completeGraph`, `JSP90.card_biUnion_le_sum_gen`,
  `JSP90.card_inter_compl_add`.

### 3. What the residual forces — and why it cannot hold at `r = 0`

* **`JSP90.hubByPacking_cost_ge`** — `HubByPacking r ℓ q` with `r ≥ 1` forces
  `3 * r - 2 ≤ ℓ + (q - 1)`, i.e. **`ℓ + q ≥ 3 * r - 1`**: the constants of the residual must grow at
  least linearly, with slope `3`, in the packing number, and no `r`-independent pair can ever work.
  Witness `K_{3r}` (`JSP90.oddCyclePackingLe_completeGraph` + Part 2).
* `JSP90.hubByPacking_q_ge_three` — the witness cycle has `q ≥ 3`.
* **`JSP90.not_hubByPacking_zero`** — **`HubByPacking 0 ℓ q` is FALSE for every `ℓ, q`**: the graph on
  the empty vertex type has odd cycle packing number `0` and no odd cycle at all, so the existential
  cannot be witnessed.  Round 121's `JSP90.erdos73_of_hubByPacking_of_forall` assumes `∀ r`, and is
  therefore a reduction demanding an **impossible** hypothesis.
* **`JSP90.erdos73_of_hubByPacking_of_succ`** (with `JSP90.erdos73_on_of_hubByPacking_of_succ`) —
  **the repaired reduction to `jsp_000090_main`**: `(∀ r ≥ 1, HubByPacking r ℓ q) → ∀ k, Erdős73 k`,
  with the constant `ℓ + (q - 1)` independent of `k`; for `k = 0` the graph is bipartite already
  (`JSP90.locIndep_zero_isBipartite`).

`#print axioms` on the seven headline declarations of the round gives only
`[propext, Classical.choice, Quot.sound]`.

### What is *not* proved, and one repair of the previous round

`jsp_000090_main` is **not** declared and `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas) is untouched.  Additionally:

* **`lean/JSPProblem/Wheel.lean` (round 121) does not compile** and is *not* in the build (it was never
  imported by `JSPProblem.lean`): `IsOddCycle.cycleOrder` is `∃ o : CycleOrder G C, o.m % 2 = 1`, so
  round 121's `obtain ⟨o, ho⟩ := hD'.cycleOrder` binds the names the wrong way round;
  `JSP90.CycleOrder.step_prev_ne` does not exist in the development (only
  `CycleOrder.adj_iff_cycle_neigh`); `Finset.inter_eq_self.mpr` does not exist at this Mathlib
  revision; and the `end JSP90` at line 625 closes an unnamed section.  Consequently round 121's
  `JSP90.no_petalSet_bound_of_maxDef` (**no function of the deficiency bounds the attachment set**) is
  **not** proved, and `JSP90.closeToBipartite_wheel_hub` is not either.  `JSPProblem/Hub.lean` itself
  does compile and is now in the build.
* The **upper** half of Part 2 was dropped: the exact minimum of `hubCost` over the hub covers of `K_n`
  (the explicit `n - 2`-cycle and `n - 1`-cycle constructions of `completeCycleOdd` /
  `completeCycleEven`) ran out of budget, so `JSP90.hubCost_min_completeGraph` and
  `JSP90.erdos73On_completeGraph_hubCover` are **not** proved; only the lower bound is.  The obstruction
  is purely the explicit cyclic ordering of `{0, …, n - 3}` inside `Fin n`, where the literal `1` is
  not available (`OfNat (Fin n) 1` does not exist for a variable `n`) and `decide`/`simp` on `Fin`
  literals are unusable once a classical `DecidableEq (Fin n)` is in scope.

---

## Round 123 (`lean/JSPProblem/Two.lean`) — **the constant `2` at `k = 1`**

New module (19 declarations, 0 `sorry`, 0 `admit`, `lake build` OK with 1273 jobs), imported from the
root module `JSPProblem.lean` (which gained `import JSPProblem.Two`).  Attack family 60: the
**constant `2`** — the value that round 96 measured for `k = 1` and that every previous instance of
the headline theorem failed to reach with Erdős's own hypothesis alone.

`harness/score.py problems/JSP-000090 --strict-prize`: `build_ok = true, sorry = 0, admit = 0,
placeholder_total = 0, partial_ok = true, missing_theorems = ["jsp_000090_main"]`.

### What is proved

* `JSP90.hitsOddCycles_of_isOddCycle_of_locIndep_one` — **under `LocIndep 1`, every odd cycle of `G`
  is an odd cycle transversal**.  (Rounds 83 and 98 needed a class hypothesis — Helly, disjointness
  — to obtain a transversal at all.)
* `JSP90.exists_commonVertex_of_oneAttach_pair_of_locIndep_one` — **the petals of a cycle pairwise
  meet** at `k = 1`: the structural content of Erdős's hypothesis for the attachment sets of rounds
  119–122.  (`locIndep_mono` records that `LocIndep k G → LocIndep k' G` only for `k ≤ k'`.)
* **`JSP90.hitsOddCycles_erase_of_triangle_petalSet_le_two`** — for a triangle `C` meeting every odd
  cycle with at most two attachment points, `C` meets every odd cycle **in all but at most one of its
  vertices**: `C.erase c` is a transversal for a vertex `c ∈ C` outside the attachment set.  Hence
* **`JSP90.closeToBipartite_two_of_triangle_petalSet_le_two` and
  `JSP90.erdos73On_of_triangle_petalSet_le_two` — AN INSTANCE OF THE HEADLINE THEOREM WITH THE
  CONSTANT `2`** and Erdős's own hypothesis: `LocIndep k G` (`k ≤ 1`) plus a triangle, with
  `CloseToBipartite 2 G`.  This is the first instance in the development whose constant is `2` and
  whose only class hypothesis is a triangle.
* **`JSP90.closeToBipartite_two_of_triangle_attachCover`** — the most general form at a triangle:
  *some* two-element subset `T ⊆ C` meeting every odd cycle that meets `C` in one point meets **every**
  odd cycle of `G` (`JSP90.attachCover_of_triangle_petalSet_le_two` shows the previous item is a
  special case).  The proof splits `|D ∩ C|` into `= 1` and `≥ 2`; the second case uses the
  pigeonhole step `JSP90.exists_mem_inter_erase_of_card_ge_two`.
* **`JSP90.closeToBipartite_two_of_oddCycle_high_intersection`** and
  `JSP90.erdos73On_of_oddCycle_high_intersection` — **the same constant for a cycle of arbitrary
  length**: if every odd cycle of `G` uses all but one vertex of `C` (`C.card - 1 ≤ |D ∩ C|`), two
  vertices of `C` meet every odd cycle.  This is the part of the constant `2` that survives where no
  triangle exists (odd girth `≥ 5`).
* **`JSP90.constant_two_attained_g6`** — **the constant `2` is attained**: `g6` satisfies
  `LocIndep 1 g6`, `CloseToBipartite 2 g6` and `¬ CloseToBipartite 1 g6`, so no instance of Erdős #73
  at `k = 1` can have a smaller constant.

### Verified exhaustively before formalising (outside Lean, `discovery/JSP-000090/r123*.c`)

* **`MaxDef ≤ 1 ⟹ τ_odd ≤ 2` up to eight vertices**: all `268 435 456` graphs on `8` vertices
  (`55 179 262` of them with `MaxDef ≤ 1`) have transversal number at most `2`
  (`discovery/JSP-000090/r123_n8.log`); this **extends round 96's `n ≤ 7` measurement to `n = 8`**.
* **`f(2) = 3`, `f(3) = 4` on `n ≤ 11`** by hill-climbing search, so the shape `f(k) = k + 1` is
  consistent up to `k = 3` (`r123b.c`).
* **`JSP90.PetalSetLeTwoOfOne` holds on every `LocIndep 1` graph with `n ≤ 7`**: over all graphs
  with `MaxDef ≤ 1`, the maximum number of attachment points of a triangle is `0, 0, 1, 2, 2` for
  `n = 3 … 7`, while the maximum transversal number is `1, 1, 1, 2, 2` (`discovery/JSP-000090/
  r123_n7.log`).  The two maxima agree, i.e. `g6`-type graphs are the only obstruction at `k = 1`.

### Discarded before formalisation (so that no round repeats them)

* **A "hub plus one vertex of `C`" transversal is FALSE as a theorem.**  The draft claimed
  `closeToBipartite_two_of_triangle_hub`: with `z` outside `C` meeting every odd cycle that meets `C`
  in one point, `{z, c}` does **not** meet an odd cycle meeting `C` in the other two vertices — the
  second range of `|D ∩ C|` is not covered, because `C \ {c}` has two elements.  (Lean rejected the
  proof at exactly this step; the correction is that a two-element transversal inside a triangle must
  lie **inside** `C`, which is why the correct general form is `closeToBipartite_two_of_triangle_attachCover`.)
* **"Every odd cycle is a transversal" is false at `LocIndep 1`**: it is true, but only because
  `LocIndep 1` bounds the *packing* number by `1`; the useful consequence is
  `PetalSet G C ⊆ T` for a two-element `T ⊆ C`, i.e. the attachment set must fit inside `T`, which
  fails as soon as all three vertices of a triangle are attachment points.
* **`LocIndep k G → LocIndep 1 G` is false for `k ≥ 2`** (`k = 2, |S| = 0, |X| = 2` is the smallest
  counterexample): a *larger* `k` is a *weaker* hypothesis.  The headline forms therefore take
  `k ≤ 1`, and `JSP90.locIndep_mono` records the correct direction.

### What is *not* proved — the residual, in two statements

* **`JSP90.PetalSetLeTwoOfOne`**: *"under `LocIndep 1`, a triangle of `G` has at most **two**
  attachment points"*.  Stated as a `def`, **not assumed anywhere**;
  `JSP90.erdos73On_one_of_triangle_of_petalSetLeTwoOfOne` and
  `JSP90.erdos73On_of_triangle_of_petalSetLeTwoOfOne` take it as a hypothesis.  With it, the whole
  `k = 1` case with the **optimal** constant `2` follows for graphs of odd girth `3`.
* the **odd girth `≥ 5`** case, where `JSPProblem/Petal.lean` pays
  `(|C| - 1) + (PetalSet G C).card` and no triangle is available; item 5 above covers it only under
  the high-intersection hypothesis.

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; behind it stands `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), untouched.  `formalization.yaml` remains `status: wip`,
`prize_ready: false`.  No award claim is made.

### Toolchain facts verified this round (they cost most of the round)

* `Finset.card_pos.mp (by omega)` leaves `?s` a metavariable, so the goal of `omega` becomes
  `0 < ?s.card` and fails; write `have hpos : 0 < C.card := by omega` first.
* `Finset.nonempty_iff_ne_empty` is `s.Nonempty ↔ s ≠ ∅`: use `.mpr` with a proof of `≠ ∅` and `.mp`
  with a witness.  (`JSPProblem/Petal.lean` mixes both directions; both are needed.)
* `rw` **closes** a goal when the rewritten statement becomes true by `rfl` (`3 - 1 ≤ 2`,
  `3 - 2 = 1`), so a following `omega` is a "no goals to be solved" error.
* `{a, b}` is `insert a {b}`, so `Finset.card_insert_le` must be applied to `a` (not `b`) to match
  syntactically, and `Finset.mem_insert.mp` returns `a = v ∨ v ∈ {b}`.
* `Finset.mem_erase : a ∈ s.erase b ↔ a ≠ b ∧ a ∈ s`; `Finset.subset_erase` is an `iff`
  (`s ⊆ s.erase a ↔ s ⊆ s ∧ a ∉ s`), so use `(Finset.subset_erase a).2`; `Finset.card_insert_of_not_mem`
  does not exist at this revision — use `Finset.card_insert_eq_ite` + `simp [Ne.symm hne]`.
* `Finset.card_sdiff_of_subset (h : s ⊆ t) : #(t \ s) = #t - #s` and
  `Finset.sdiff_nonempty_of_card_lt_card (h : #s < #t) : (t \ s).Nonempty` are both available and
  are what the counting steps need.
* `omega` is blind to `C.card - 1` versus `C.card - 2` when both appear as distinct atoms (as in
  round 101), so the contradictory pair must be introduced with a single `have` in terms of
  `C.card` (`omega` handles `b ≤ C.card - 2` and `C.card - 1 ≤ b` together, but not after the
  subtraction has been pushed into the other hypothesis).

---

## Round 124 — `lean/JSPProblem/Wheel.lean`: the STANDING REGRESSION IS CLOSED, and the wheel is
## resolved exactly (transversal number `2`, attachment set `n`)

The file was written in round 121 and **did not compile** in rounds 121, 122 or 123, so every
declaration in it was dead code — including round 121's negative result, which the harness had been
reporting as unproved.  Round 124 repairs it and adds a seventh part that settles the family in the
positive direction.  `lean/JSPProblem/Wheel.lean` now has **63 declarations, 883 lines, 0 `sorry`,
0 `admit`**, is imported by the root module, and `lake build` succeeds with 1274 jobs.

### What the repair restores (dead code until this round)

* **`JSP90.no_petalSet_bound_of_maxDef` — NO FUNCTION OF THE DEFICIENCY BOUNDS THE ATTACHMENT
  SET.**  There is **no** `φ : ℕ → ℕ` with `|PetalSet (wheel n) C| ≤ φ (MaxDef (wheel n))` for every
  odd `n ≥ 3`, although the family has deficiency at most `2` throughout (`|PetalSet (wheel n) C| =
  n`).  The whole family of numerical bounds `φ(MaxDef G)` — the blocker named by rounds 119 and 120
  — is refuted by one machine-checked family.  **The proof is a pigeonhole argument, and it has to
  be**: an arbitrary `φ : ℕ → ℕ` need not be monotone, so the round-121 draft's `φ.monotone` step was
  unsound; `MaxDef (wheel n)` is a natural number at most `2`, hence one of `0, 1, 2`, so every odd
  `n` forces `n ≤ max (φ 0) (φ 1) (φ 2)`.
* **`JSP90.not_card_petalSet_le_maxDef_add_wheel`** (`|PetalSet| ≤ MaxDef + c` is false for every
  `c`), **`JSP90.not_card_petalSet_le_mul_maxDef_wheel`** (false for every `c ≥ 1`) and
  **`JSP90.not_petalSet_le_of_locIndep_two`** — the same refutation *under Erdős's own hypothesis*
  `LocIndep 2 G`, not only under the deficiency bound.
* **`JSP90.subset_wheelCycleFins_of_oddCycle_avoid_hub`** (every odd cycle of the wheel avoiding the
  hub lies on the rim), **`JSP90.hitsOddCycles_wheelCycleFins`**, **`JSP90.hubCover_wheelCycleFins`**
  (the single hub is a hub cover of the rim), **`JSP90.closeToBipartite_wheel_hub`**
  (`CloseToBipartite n (wheel n)`, the constant `|C| − 1 + 1` where the attachment-set route of round
  119 would have paid `2n − 1`) and **`JSP90.hubCover_constant_lt_wheel`**.

### What is new (Part 7): the wheel, resolved exactly

* **`JSP90.exists_oddCycle_avoiding_vertex`** — no vertex of the wheel meets every odd cycle (the hub
  is avoided by the rim, every rim vertex and every leaf by the petal triangle at a different rim
  index), with the reusable input **`JSP90.wheel_exists_index_ne`**;
* **`JSP90.not_closeToBipartite_zero_wheel`**, **`JSP90.not_closeToBipartite_one_wheel`** and hence
  **`JSP90.closeToBipartite_wheel_iff`: `CloseToBipartite m (wheel n) ↔ 2 ≤ m`** for odd `n ≥ 3` —
  **the odd cycle transversal number of the wheel is exactly `2`**;
* **`JSP90.wheel_triple`** — the three numbers together:

  > `MaxDef (wheel n) ≤ 2`  ∧  `|PetalSet (wheel n) C| = n`  ∧  `CloseToBipartite 2 (wheel n)`  ∧
  > `¬ CloseToBipartite 1 (wheel n)`.

  So the wheel is **not** a counterexample to Erdős #73: an attachment set of `n` vertices costs
  *nothing* here, because one vertex (the hub) carries all of them at once.  It is the
  machine-checked demonstration that the object to be charged is a **hub set**
  (`JSPProblem/Hub.lean`), never a function of the deficiency;
* **`JSP90.not_petalSet_le_of_locIndep_ge_two`** — the refutation of the numerical blocker now holds
  under Erdős's own hypothesis **for every `k ≥ 2`**, not only at `k = 2`;
* the local lemmas the proofs need: **`JSP90.wheelC_of_adj_two`** (a wheel vertex with two distinct
  neighbours, neither of them the hub, is a rim vertex — the only axioms it uses are none),
  **`JSP90.wheelColour`** / **`JSP90.wheelStarColour`**, **`JSP90.wheelColour_rim`**,
  **`JSP90.wheelColour_leaf`**.

### What is *not* proved, and one obstruction newly located

`jsp_000090_main` is **not** declared and `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas) is untouched, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true,
prize_ready = false`.  `#print axioms` on the ten headline declarations of the round gives only
`[propext, Classical.choice, Quot.sound]`.

Round 123's single named residual, **`JSP90.PetalSetLeTwoOfOne`** (under `LocIndep 1 G` a triangle
of `G` has at most **two** attachment points), was **re-verified independently this round** and
**survives**: over *all* graphs on 5, 6 and 7 vertices there is no graph with `MaxDef ≤ 1` carrying a
triangle with three attachment points (`discovery/JSP-000090/r124.c`,
`discovery/JSP-000090/r124_petalSet.log`), and every candidate construction fails for a structural
reason — `LocIndep 1` forbids two vertex-disjoint odd cycles, so the three petals must pairwise
meet, and a hub adjacent to all three vertices of the triangle completes a `K₄`.

The **smallest case is now isolated**: if the three petals are *triangles* meeting pairwise in three
**distinct** vertices `w`, `w'`, `w''`, then the six vertices `{a, b, c, w, w', w''}` induce
`K₆` minus a perfect matching, whose deficiency is exactly `2`, so `LocIndep 1` fails.  The unproved
part of the lemma is the general case (petals of length `≥ 5`, arbitrary intersections); that
six-vertex count is the concrete first formalisation target recorded in
`discovery/JSP-000090/policy.json`.

### Toolchain findings (they cost four rounds the repair)

* **`intro` / `fun` on a negation introduce the POSITIVE statement**: `intro h` on `a ≠ b` gives
  `h : a = b`, and `fun _ _ hxh => hxh` matched against `∀ x ∈ C, x ∉ X` binds `hxh : x ∈ X` with the
  body required to be `False`.  `absurd` / `False.elim` must be written explicitly;
* **`omega` cannot see a variable modulus**: any hypothesis `(…) % n = …` with `n` a variable makes
  every later `omega` call fail (`clear` it first), and `omega` does not read the bound out of
  `k : Fin n` (`have hklt : k.val < n := k.isLt` first);
* `Finset.card_insert_of_notMem`, `Finset.inter_eq_self.mpr`, `Finset.eq_empty_of_not_mem`,
  `Finset.not_mem_empty`, `Finset.disjoint_singleton_singleton` do not exist at this revision; use
  `Finset.card_union_of_disjoint` with `Finset.disjoint_left.mpr`, `Finset.not_nonempty_iff_eq_empty`,
  `Finset.ext fun y => …`, and `by simp` for `¬ (x ∈ ∅)`;
* `rcases` on the indexed edge family `WheelEdgeKind n u v` fails with *Dependent elimination
  failed*: match the vertex type instead so that the `match` in `wheelAdj` reduces by iota, and keep
  the structural facts as separate small lemmas;
* `Finset ⊆` takes the element **implicitly** (`hsub hy`, not `hsub y hy`), `obtain ⟨v, hv⟩ := hne`
  **clears** `hne`, `Finset.card_eq_one` is an `∃`-statement, and
  `not_isOddCycle_of_isBipartite` takes an `∃`-witness.

`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 125 — `JSPProblem/Petal3.lean`: **the six-vertex obstruction at a triangle**, and the
**first settled class** of the `k = 1` route

New file `lean/JSPProblem/Petal3.lean` (**55 declarations**, ~1000 lines, **0 sorry/admit**, `lake
build` OK with 1275 jobs), imported from the root module `JSPProblem.lean`.  This is the **twenty-second
attack family**.  It does two things:

1. it **proves**, in Lean, the obstruction that round 124 recorded only in words in
   `policy.json` (three triangle petals of a triangle, meeting pairwise in three distinct vertices,
   force deficiency `2`), and
2. it uses that obstruction to **settle a class of graphs for Erdős #73 with the optimal constant
   `2`**: graphs all of whose odd cycles are triangles.

### Part 1 — the counting lemmas

* `JSP90.adj_of_isOddCycle_card_three` — **a triangle is a `K_3`**: any two of its vertices are
  adjacent.  (`JSP90.IsOddCycle` is a *cyclic ordering*, so this is not a field of it.)
* `JSP90.indepCard_le_one_of_completeOn`, `JSP90.defOf_ge_card_sub_two_of_completeOn`,
  `JSP90.not_locIndep_one_of_clique_four` — **a `K_n` has deficiency `n - 2`**, hence a `K_4` forbids
  `LocIndep 1`.
* **`JSP90.maxDef_ge_two_of_threeParts` — THE MULTIPARTITE OBSTRUCTION**: three pairwise disjoint sets
  of two vertices each, with every vertex of one part adjacent to every vertex of each of the other
  two — i.e. `G` *contains* the octahedral graph `K_6` minus a perfect matching — give
  `MaxDef G ≥ 2`, so `LocIndep 1 G` fails (`JSP90.not_locIndep_one_of_threeParts`).  The proof is the
  exact count: an independent set of `A ⊎ B ⊎ C` lies in **one** part
  (`JSP90.subset_part_of_isIndepSet_of_threeParts`), so `α ≤ 2` while `|A ⊎ B ⊎ C| = 6`.

### Part 2 — the six-vertex obstruction

* **`JSP90.maxDef_ge_two_of_threePetalTriangle`**: `{a,b,c}` a triangle, `p`, `q`, `r` three distinct
  vertices outside it, and the twelve edges of `{a,b,c}`, `{a,p,r}`, `{b,p,q}`, `{c,q,r}` present —
  then the six vertices carry `K_6` minus a perfect matching with parts `{a,q}`, `{b,r}`, `{c,p}`, so
  `MaxDef G ≥ 2` (`JSP90.not_locIndep_one_of_threePetalTriangle`).
* **`JSP90.not_locIndep_one_of_three_triangle_petals` — THE HEADLINE STATEMENT OF THE FILE**: a
  triangle `C` cannot have three *triangle* petals at three **different** attachment points which
  **pairwise meet**.  The proof separates the two possible arrangements: the petals either share a
  point (that point together with the three vertices of `C` is a `K_4`) or they meet in three distinct
  points outside `C` (the six-vertex obstruction).
* **`JSP90.not_three_triangle_petals_of_locIndep_one`**: three triangle petals with three different
  attachment points **cannot exist at all** under `LocIndep 1`, because under `LocIndep 1` any two odd
  cycles meet (`JSP90.hitsOddCycles_of_isOddCycle_of_locIndep_one`), so the meeting is automatic.

### Part 3 — the new instance of the headline theorem

* `JSP90.TriPetalSet`, `JSP90.card_triPetalSet_le_two_of_locIndep_one` — **at a triangle of a graph
  satisfying Erdős's hypothesis, at most two vertices lie alone on a triangle**.  This is the case of
  `JSP90.PetalSetLeTwoOfOne` in which the witness petals are triangles; the remaining case (a witness
  of length `≥ 5`) is what is still open.
* **`JSP90.erdos73On_one_of_allTriangles` — A NEW INSTANCE OF THE HEADLINE THEOREM, WITH THE OPTIMAL
  CONSTANT `2`**: if **every odd cycle of `G` is a triangle**, then `LocIndep 1 G` forces
  `CloseToBipartite 2 G`.  The constant mentions neither the number of triangles, the branch vertices,
  the packing weight nor the packing number; no bound on the odd girth is used.
  `JSP90.erdos73On_one_of_allTriangles_of_exists` is the same statement for a *class* of graphs.

### Part 4 — the witness `octa6`, and sharpness

`JSP90.octa6` is `K_6` minus a perfect matching (the complete tripartite graph with parts `{0,3}`,
`{1,4}`, `{2,5}`), and

* `JSP90.locIndep_two_octa6`, `JSP90.maxDef_octa6 : MaxDef octa6 = 2`,
  `JSP90.not_locIndep_one_octa6` — the deficiency is **exactly** `2`, so the bound
  `MaxDef ≥ 2` of Part 1 is *attained* and sharp;
* **`JSP90.petalSet_octa6_tri`, `JSP90.card_petalSet_octa6_tri`** — the attachment set of the
  triangle `{0,1,2}` has **three** elements (witnesses: the petals `{0,4,5}`, `{3,1,5}`, `{3,4,2}`),
  the first graph in this development where a triangle's attachment set is not a proper subset of
  it;
* `JSP90.closeToBipartite_iff_octa6 : CloseToBipartite m octa6 ↔ 2 ≤ m` — its odd cycle transversal
  number is exactly `2`.

### What is *not* proved

`JSP90.PetalSetLeTwoOfOne` itself (an attachment point witnessed by a petal of length `≥ 5`), the odd
girth `≥ 5` case at `LocIndep 1`, and `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas) are untouched.  An exhaustive check of this round
(`discovery/JSP-000090/r125.c`, `r125.log`) confirms over **all** graphs on `8` vertices containing a
triangle (`2 503 867` of them satisfy `LocIndep 1`) that **no** triangle has three attachment points:
the maximum of `|PetalSet G C|` is `2`.  A second check (`r125_tau.c`) shows that no `LocIndep 1`
graph on `≤ 7` vertices has odd cycle transversal number `≥ 3`, i.e. the target of the new instance
(`f(1) = 2`) is consistent with the data.

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true,
prize_ready = false`.  `formalization.yaml` remains `status: wip`, `prize_ready: false`.
No award claim is made.

---

## Round 126 — `lean/JSPProblem/FewOdd.lean`: the **FEW-ODD-CYCLES axis**, and the 8-vertex witness that **kills the Helly route at `k = 1`**

New module (31 declarations, 522 lines, **0 `sorry`, 0 `admit`**, `lake build` OK with 1276 jobs),
imported from the root module `JSPProblem.lean`.  Attack family 46.  `harness/score.py
problems/JSP-000090 --strict-prize` reports `build_ok = true, sorry = 0, admit = 0,
placeholder_total = 0, partial_ok = true, missing_theorems = ["jsp_000090_main"]`.

Round 125 settled the class *all odd cycles are triangles* with the optimal constant `2`, and left
the odd-girth-`≥ 5` case of the `k = 1` route open.  This round does **not** continue the petal-counting
route.  It attacks the **Helly route** — the only route in the development that delivers the constant
`1` at `k = 1` (`JSP90.closeToBipartite_one_of_helly_of_locIndep_one`, round 83) — and shows by machine
check that **that route is dead at `k = 1`**, while delivering a new instance on a class no earlier
round touched.

### Part 1 — a NEW INSTANCE OF THE HEADLINE THEOREM, on the few-odd-cycles class

Erdős's hypothesis is used exactly once, through `JSP90.inter_oddCycle_of_locIndep_one` ("two odd
cycles of a `LocIndep 1` graph meet"), and a **pairing lemma** turns the resulting pairwise-meeting
family into a transversal of `⌈|𝒞| / 2⌉` vertices:

* **`JSP90.exists_transversal_card_le`** — *the pairing lemma*: a pairwise-meeting family `𝒞` of
  nonempty sets has a transversal `T` with `2 * T.card ≤ 𝒞.card + 1`.  Strong induction on `|𝒞|`; the
  step takes two distinct members, pays **one** vertex for the *pair*, and recurses on
  `𝒞.erase C |>.erase D`.
* **`JSP90.closeToBipartite_of_locIndep_one_of_card_oddCycles_le`** and
  **`JSP90.erdos73On_fewOddCycles`** — **A NEW INSTANCE OF THE HEADLINE THEOREM**:
  `LocIndep 1 G` and at most `2 * m` odd cycles give `CloseToBipartite m G`.  The hypothesis is a
  **count of odd cycles**, which is new here: round 98 bounded the *packing* number, and that number
  is `1` in this regime, so Part 1's hypothesis is genuinely more information than anything proved
  before.  No bound on degrees, odd girth, cycle sizes or the number of vertices.
* `JSP90.closeToBipartite_one_of_locIndep_one_of_two_oddCycles` (≤ 2 odd cycles, constant `1`) and
  `JSP90.closeToBipartite_two_of_locIndep_one_of_four_oddCycles` (≤ 4 odd cycles, constant `2`).

### Part 2 — `JSP90.k4sub`: `LocIndep 1`, **odd girth 5**, `τ_odd = 2`

`k4sub` is `K₄` on `{0, 3, 6, 7}` with **four of its six edges subdivided** — ten edges on eight
vertices, and **no triangle**.  All of it is proved: `JSP90.locIndep_one_k4sub` (a kernel decision over
the `2 ^ 8` vertex sets), `JSP90.maxDef_k4sub : MaxDef k4sub = 1` (the deficiency is **exactly** `1`),
the four 5-cycles `C₁ = {0,2,3,4,6}`, `C₂ = {0,1,3,5,7}`, `C₃ = {0,1,2,6,7}`, `C₄ = {3,4,5,6,7}`
with **all six pairwise intersections nonempty** (`JSP90.k4sub_four_meet`, `JSP90.k4sub_pair_mem`) and
**empty four-fold intersection** (`JSP90.k4sub_no_commonVertex`), `JSP90.closeToBipartite_two_k4sub`,
`JSP90.deleteFinset_k4sub_not_isBipartite` (no one-vertex deletion is bipartite) and
**`JSP90.closeToBipartite_iff_k4sub : CloseToBipartite m k4sub ↔ 2 ≤ m`** — the odd cycle transversal
number is **exactly 2**.  `JSP90.card_oddCycles_ge_four_k4sub : 4 ≤ |OddCycles k4sub|`.

### Part 3 — the Helly route is dead at `k = 1`, machine-checked

* **`JSP90.not_helly_k4sub`** — `¬ HellyOddCycles k4sub`.  Together with `locIndep_one_k4sub` this is
  the formal statement that **Erdős's hypothesis does not imply the Helly property**: the four odd
  cycles of `k4sub` are pairwise meeting with empty total intersection.  So
  `JSP90.closeToBipartite_one_of_helly_of_locIndep_one` can never be applied to all graphs, and
  `JSP90.HellyOddCycles` is not a consequence of `LocIndep k` at any `k`.
* **`JSP90.three_commonVertex_of_k4sub`** — **every three** of the four odd cycles have a common
  vertex (the witnesses `0`, `3`, `6`, `7` for `C₁C₂C₃`, `C₁C₂C₄`, `C₁C₃C₄`, `C₂C₃C₄`).  The minimal
  Helly obstruction therefore has size **exactly four**: no three-element (Helly-number-3) version of
  the property detects it, and the natural upgrade of round 83's instance — "`TwoHellyOddCycles`
  instead of `HellyOddCycles`" — is **false**, witnessed by a graph of odd girth 5 whose four odd
  cycles are all 5-cycles.
* `JSP90.LocIndepOneNotHelly` — the four statements packaged as one conjunction.
* `JSP90.exists_oddCycle_avoiding_of_k4sub` — every vertex of `k4sub` is avoided by an odd cycle of
  `k4sub`, the machine-checked form of `JSP90.exists_oddCycle_avoiding_vertex`.

### Measurements made before formalising (not Lean theorems)

`discovery/JSP-000090/r126.c`: **exhaustively over all `2²¹` graphs on 7 vertices**, split by odd
girth: among `LocIndep 1` graphs, the largest odd cycle transversal number is `2` at odd girth `3`
and **`1` at odd girth `5` and at odd girth `≥ 7`**; the `29 904` `LocIndep 1` graphs of odd girth 5 on
7 vertices all need one vertex, and no `LocIndep 1` graph of odd girth `≥ 5` needs two.  So `f(1) = 2`
is forced by the `2 503 867`-type witnesses of girth 3 and is *not* forced at odd girth `≥ 5` on
`≤ 7` vertices.
`discovery/JSP-000090/r126b.c`, `r126d.c`: random search for `LocIndep 1`, **triangle-free** graphs with
transversal number `≥ 2` finds the **8-vertex** `k4sub` (`r126d.c` reports that all four of its minimal
odd cycles are 5-cycles, that its odd cycles are pairwise meeting, that `TwoHellyOddCycles` holds
while `HellyOddCycles` fails, and that `τ_odd = 2`), which is minimal: `r126.c` finds nothing on
`≤ 7` vertices.

### What is *not* proved

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports `build_ok = true,
partial_ok = true, prize_ready = false`.  Behind it stands `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  Part 1's hypothesis is a count of odd
cycles, not a function of `MaxDef G`: round 100's `JSP90.maxDegLe_two_unbounded_oddCycles` records that
graphs of deficiency `2` have an unbounded number of odd cycles, so a bound on `|OddCycles G|` in terms
of `MaxDef G` is false in that shape and the residual of this axis is exactly that gap.

`#print axioms` on all twenty-one headline declarations shows only
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 127 — `lean/JSPProblem/Mono.lean`: the **MAXIMUM-CUT axis** — the canonical `MonoSet` of a
## cut, one-vertex-flip **stability**, and a machine-checked refutation of the absolute bound

New file (31 declarations, **0 `sorry`, 0 `admit`**, `lake build` OK with 1277 jobs), imported from
the root module `JSPProblem.lean`.  Attack family 47.  An audit of all 83 modules showed that the
development contained **no** use of the *optimality* of a cut and no way to produce a monochromatic
cover *from* a cut; this round supplies both.

### 1 — the canonical certificate of an arbitrary cut

`JSP90.MonoVertex G A v` = "`v` is incident to a non-crossing edge of the cut with side `A`", and
`JSP90.MonoSet G A` is the finset of all such vertices.

* **`JSP90.hitsOddCycles_monoSet` — THE MONO SET OF *ANY* CUT IS AN ODD CYCLE TRANSVERSAL.**
  `JSPProblem/MaxCut.lean` proves this only for a *supplied* cover `Z`; here `Z` comes from the cut.
* **`JSP90.closeToBipartite_monoSet` — AN INSTANCE OF THE CONCLUSION FOR EVERY CUT**:
  `CloseToBipartite (MonoSet G A).card G`.
* **`JSP90.inter_monoSet_ne_empty_of_hitsMono`** — the mono set meets every monochromatic edge, so it
  also meets every monochromatic cover.
* **`JSP90.isBipartite_iff_exists_monoSet_empty` — THE CUT AXIS IS EQUIVALENT TO BIPARTITENESS**
  (`G.IsBipartite ↔ ∃ A, MonoSet G A = ∅`), the converse direction `MaxCut.lean` never proved, and
* **`JSP90.maxDef_le_zero_iff_exists_monoSet_empty` — all of Erdős #73 at `k = 0` through the cut.**
* **`JSP90.card_monoSet_pos_of_not_isBipartite`** — on a non-bipartite graph every cut has a mono set
  of at least **two** vertices (a mono vertex's mono neighbour is a second, distinct vertex).
* **`JSP90.monoSet_compl`** — the mono set does not depend on which side is called `A`.

### 2 — stability: the first use of cut optimality

`SameDeg G A v` / `CrossDeg G A v` are the neighbours of `v` on its own / the other side, with
`SameDeg + CrossDeg = deg v` (`JSP90.sameDeg_add_crossDeg`).  `JSP90.StableCut G A` is the classical
one-vertex-flip optimality condition (no vertex of `A` has more neighbours on its own side).

* **`JSP90.exists_notMem_adj_of_stableCut`** — a stable cut pushes every mono vertex of `A` out.
* **`JSP90.sum_sameDeg_le_sum_crossDeg_of_stableCut`** — **the internal edges of a stable side number
  at most half the cut.**

### 3 — the reduction

* **`JSP90.MaxCutMonoLe c`** (a `def`, **not** assumed): every graph of deficiency `≤ k` admits a
  *stable* cut whose mono set has at most `c` vertices;
  **`JSP90.erdos73On_of_maxCutMonoLe` / `JSP90.erdos73_of_maxCutMonoLe`** turn it into Erdős #73 with
  constant `c`.

### 4 — the NEGATIVE result, machine-checked

* **`JSP90.card_monoSet_ge_card_sub_one_completeGraph` — for `n ≥ 4` EVERY cut `A` of `K_n` has
  `n − 1 ≤ |MonoSet K_n A|`**, and since `CloseToBipartite (n−2) (K_n)`
  (`JSP90.closeToBipartite_iff_completeGraph_add_two`), **`JSP90.not_card_monoSet_le_opt_completeGraph`:
  no cut of `K_n` attains the optimal transversal number** — and no *maximum* cut repairs it, the
  statement holding for all cuts.
* **`JSP90.card_monoSet_singleton_completeGraph`** — a singleton side gives *exactly* `n − 1`, so the
  best the cut axis can do on `K_n` is one vertex worse than optimal.
* **`JSP90.closeToBipartite_and_monoSet_completeGraph`** — both facts in one statement.

### What is *not* proved

`jsp_000090_main` is **not** declared and `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas) is untouched, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports `build_ok = true,
sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true, prize_ready = false`.  `#print
axioms` on the thirteen headline declarations gives only `[propext, Classical.choice, Quot.sound]`.
The new residual is **`JSP90.MaxCutMonoLe c`, refuted for every `c`** (Part 4); the surviving form is
a bound in terms of `MaxDef`, and the measurements support `phi(1) = 4`: **exhaustively over all
268 435 456 graphs on 8 vertices**, among the `55 179 262` with `MaxDef ≤ 1` the best maximum cut has
at most **4** mono vertices (histogram 1: 14 652, 2: 2 104 340, 3: 26 563 064, 4: 26 497 205), and on 7
vertices the worst case is the friendship graph `F₃` (three triangles sharing a vertex, `tau_odd = 1`)
(`discovery/JSP-000090/r127d_n8_md1.log`, `r127_n7.log`, programs `r127.c`–`r127d.c`).
`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 128 — the maximum-cut axis is CLOSED: the flip equivalence, and the death of the certificate

`lean/JSPProblem/CutFlip.lean` (31 declarations, 0 sorry, 0 admit) and `lean/JSPProblem/MonoWind.lean`
(17 declarations, 0 sorry, 0 admit); `lake build` OK with 1279 jobs; `#print axioms` on nine headline
declarations of the two files gives only `[propext, Classical.choice, Quot.sound]`.

### 1 — the FLIP EQUIVALENCE (the blocker round 127 named)

* **`JSP90.CutSize G A`** — the number of edges crossing the cut with side `A`, counted once from
  that side; **`JSP90.cutSize_flip`** — **the per-vertex delta**: flipping `v ∈ A` changes the size
  of the cut by `+ SameDeg G A v − CrossDeg G A v`.
* **`JSP90.IsMaxCut G A`** and **`JSP90.stableCut_of_isMaxCut`: EVERY MAXIMUM CUT IS STABLE**, i.e.
  `IsMaxCut G A → StableCut G A` — precisely the lemma round 127 recorded as missing.
* **`JSP90.exists_maxCut`** — every finite graph *has* a maximum cut (the first cut in the
  development produced from `G` and proved optimal for it);
  **`JSP90.exists_maxCut_stable`**, **`JSP90.exists_maxCut_closeToBipartite`** (an instance of the
  conclusion produced by an optimal cut).
* **`JSP90.cutSize_compl`**, **`JSP90.crossDeg_compl_eq_sameDeg`**, **`JSP90.sameDeg_compl_eq_crossDeg`**
  — the size of a cut does not depend on which side is called `A`.

### 2 — what optimality buys: the counts at a maximum cut

* **`JSP90.sum_sameDeg_le_cutSize_of_isMaxCut`**, **`JSP90.sameDeg_pos_of_mem_monoSet`**,
  **`JSP90.card_monoSide_le_sum_sameDeg`**, **`JSP90.card_monoSide_le_cutSize_of_isMaxCut`** — each
  side of a maximum cut has at most `CutSize` monochromatic vertices.
* **`JSP90.monoSet_eq_inter_union_inter`** — the mono set splits over the two sides.
* **`JSP90.card_monoSet_le_two_mul_cutSize_of_isMaxCut`** — **the mono set of a maximum cut has at
  most twice the size of the cut**.
* **`JSP90.edgeCount_le_two_mul_cutSize_of_isMaxCut`** — **the classical maximum-cut bound**:
  `edgeCount G ≤ 2 * CutSize G A`, i.e. every graph has a cut carrying at least half its edges.

### 3 — the reduction, and its DEATH

* **`JSP90.MaxCutOfMonoCardLe`** (a `def`, not assumed) + `JSP90.erdos73On_of_maxCutOfMonoCardLe` +
  `JSP90.erdos73_of_maxCutOfMonoCardLe` + **`JSP90.maxCutMonoLe_of_maxCutOfMonoCardLe`** — the round-127
  reduction restated with *maximum* cuts; the two are equivalent in strength.
* **`JSP90.not_exists_monoCard_le_completeGraph`**, **`JSP90.not_maxCutMonoLe`**,
  **`JSP90.not_maxCutOfMonoCardLe`** — **the maximum-cut certificate route is refuted, for every
  constant**: `JSP90.MaxCutMonoLe c` and `JSP90.MaxCutOfMonoCardLe c` are inhabited never, witnessed
  by `K_{c + 2}` (for `c ≥ 1`) and `K_3` (for `c = 0`), which satisfy `LocIndep c` and are `c`-close
  to bipartite while **every** cut certifies at least `c + 1` vertices.

### 4 — `lean/JSPProblem/MonoWind.lean`: the windmill kills the *relative* hypothesis too

* **`JSP90.wfT t`** — the windmill with `t` triangles (one hub, `t` pairs of leaves).
* **`JSP90.exists_mono_leaf_of_wfT`** — in **every** cut, **every** triangle contributes a
  monochromatic leaf (a leaf is mono either through the hub or through its partner; the two cases are
  exhaustive).
* **`JSP90.card_monoSet_ge_t`**, **`JSP90.card_monoSet_ge_t_add_one`** (when the hub is mono) and
  **`JSP90.card_monoSet_ge_t_add_one'`** — **the mono set of any cut of the windmill `t` has at least
  `t + 1` vertices**.
* **`JSP90.leaf_mem_monoSet_of_not_mem_hub`** — if the hub is not mono, *both* leaves of every
  triangle are mono, so the mono set has `2 t` vertices.
* **`JSP90.closeToBipartite_one_wfT`** — deleting the hub leaves a matching: **the windmill `t` is
  `1`-close to bipartite for every `t`**.

So the optimal odd cycle transversal number of the windmill is `1` while its cut certificates grow
without bound — the round-127 data (`phi(1) = 4`, `phi(2) ≥ 7`, measured over `≤ 8` vertices) were an
artefact of the vertex bound. **The single remaining input is `JSP90.locIndep_one_wfT`
(`LocIndep 1 (wfT t)`), a pure counting lemma; with it, no `phi (MaxDef G)` exists and the axis is
closed for good.** Its statement and proof strategy are in `discovery/JSP-000090/policy.json`.

### What is *still* not proved

`jsp_000090_main` is **not** declared; `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas) is untouched. Nothing above is an instance of the headline theorem
for all `k`; what the round adds is the flip equivalence, the structure of a maximum cut, and two
machine-checked negative results that remove the maximum-cut certificate from the list of possible
approaches.

---

## Round 129 — `lean/JSPProblem/MonoWind.lean`: the windmill satisfies `LocIndep 1`, and the
## maximum-cut axis is closed **for good**

Round 128 left the maximum-cut axis with exactly **one** open input, recorded verbatim in
`discovery/JSP-000090/policy.json`:

> `JSP90.locIndep_one_wfT (t : ℕ) : LocIndep 1 (wfT t)` — with the proof strategy (a counting lemma,
> no combinatorics).

**This round proves it**, and with it the relative refutation of round 127 is complete.  `lake build`
succeeds (1279 jobs); `score.py --strict-prize` reports `build_ok = true, sorry = 0, admit = 0,
placeholder_total = 0, partial_ok = true, missing_theorems = ["jsp_000090_main"]`, `prize_ready =
false`.  28 new declarations, 0 `sorry`/`admit`.

### 1 — `JSP90.locIndep_one_wfT`: the counting lemma

For a vertex set `X` put `selOf X i =` the leaf of triangle `i` that lies in `X` (a triangle meeting
`X` always has a leaf in `X`; `selOf X i` is the first leaf otherwise) and

```
S := (univ.image (selOf X)) ∩ X .
```

Then

* **`JSP90.selOf_mem_of_mem_leaf`** — a triangle meeting `X` has a leaf in `X`, and it is the leaf
  `selOf` returns;
* **`JSP90.selOf_inj`** — the chosen leaf determines the triangle;
* **`JSP90.locIndep_one_wfT`** — `S` is an independent set (`JSP90.selOf_inj` forbids adjacency of
  two distinct members), `|X ∩ leaves| ≤ 2 * |S|` (**`JSP90.card_inter_wfLeaves_le_two_mul_card_inter_wfChosen`**,
  via the injection `inl (i, j) ↦ (chosen leaf of `i`, j)` of **`JSP90.wfLeafMap_inj`**) and
  `|X| ≤ |X ∩ leaves| + 1` (**`JSP90.card_le_card_inter_wfLeaves_add_one`**: the hub is the only
  vertex that is not a leaf), whence `2 * |S| + 1 ≥ |X|`.

Supporting definitions: `JSP90.wfHub`, `JSP90.wfLeaves`, `JSP90.mem_wfLeaves`,
`JSP90.card_wfLeaves`, `JSP90.wfLeafMap`, `JSP90.wfLabelOf`, `JSP90.WfChosen`, `JSP90.WfChosenCode`,
`JSP90.card_WfChosenCode`, `JSP90.mem_wfLeafMap_of_mem`, `JSP90.wfLabelOf_injective`,
`JSP90.exists_fin2_selOf`.

### 2 — the deficiency of the windmill is exactly `1`

* **`JSP90.isClique_wfTri0`** (+ `JSP90.WfLeaves0`, `JSP90.wfTri0`, `JSP90.card_wfTri0`,
  `JSP90.adj_hub_of_mem_leaves0`, `JSP90.adj_leaves0`) — one triangle of the windmill is a clique of
  size `3`, so it has deficiency `1`;
* **`JSP90.maxDef_one_wfT : MaxDef (wfT t) = 1`** for every `t ≥ 1`: the triangles all share the hub,
  so their deficiencies do not add.  (`MaxDef G ≤ 1` from `JSP90.maxDef_le_of_locIndep` and
  `JSP90.locIndep_one_wfT`, `1 ≤ MaxDef G` from `JSP90.le_maxDef` and the clique.)

### 3 — TWO MACHINE-CHECKED REFUTATIONS OF THE MAXIMUM-CUT CERTIFICATE

* **`JSP90.not_exists_monoSet_le_of_maxDef_one`** — **no function of the deficiency bounds the mono
  set of a cut**: there is no `phi` such that every cut `A` of every graph with `MaxDef G ≤ 1`
  satisfies `card (MonoSet G A) ≤ phi 1`.  Witness: the windmill `t := phi 1 + 1`.
* **`JSP90.not_exists_monoSet_le_of_locIndep`** — **no function of `k` at all bounds it**: for every
  `phi` and every `k ≥ 1` there is a `LocIndep k` graph with a cut whose mono set has more than
  `phi k` vertices, although the graph is `1`-close to bipartite.
* **`JSP90.exists_monoSet_ge_of_locIndep_of_closeToBipartite_one`** — the same statement in the shape
  of the headline statement: for every `k ≥ 1` and `m` there is a `LocIndep k` graph `G` that is
  `1`-close to bipartite and a cut `A` with `m < card (MonoSet G A)`.

`#print axioms` on the four headline declarations gives only
`[propext, Classical.choice, Quot.sound]`.

**Consequence for the search space.**  Any future proof of `jsp_000090_main` that runs through
`CloseToBipartite m G ↔ ∃ A, card (MonoSet G A) ≤ m` is dead: the certificate is unbounded while the
optimum is `1`.  This subsumes and extends the two negative results of rounds 127–128 (which refuted
the absolute form `JSP90.MaxCutMonoLe c` and the maximum-cut form).

### 4 — measurement (not proved): the constant of `k = 1`

`discovery/JSP-000090/r129.c` enumerates **every** graph on `n ≤ 8` vertices satisfying `LocIndep 1`
(55 179 262 of them) and computes the odd cycle transversal number `tau_odd`:

| `n` | # graphs with `LocIndep 1` | max `tau_odd` |
| --- | --- | --- |
| 3 | 8 | 1 |
| 4 | 63 | 1 |
| 5 | 958 | 1 |
| 6 | 24 814 | 2 |
| 7 | 986 787 | 2 |
| 8 | 55 179 262 | 2 |

and the same enumeration restricted to **triangle-free** `LocIndep 1` graphs (triangle-free pruning
as well) gives max `tau_odd = 2` already at `n = 8`, attained by `k4sub` (already formalised in
`JSPProblem/FewOdd.lean`, `JSP90.closeToBipartite_iff_k4sub`), and again at `n = 9` by the Petersen
graph minus one vertex.  So **the conjecture is that `k = 1` holds with the constant `2` in full
generality** (`JSP90.erdos73_one : Erdős73On 1 2`), in the triangle-free class as well; the
triangle-free witnesses show the constant `1` is *not* available there.

### What is *not* proved

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.  Behind it stands `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  The *new* top target opened by this
round's measurement is the **complete `k = 1` case with the optimal constant `2`**
(`LocIndep 1 G → CloseToBipartite 2 G`), which is the first constant of Erdős #73 that the machine
search shows to be *optimal*, and the `k = 1` statement is the only remaining case in which the
deficiency bound `≤ 1` is strong enough to hope for a short proof.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 130 — `lean/JSPProblem/OneK.lean`: **the case `k = 1`** — the triangle spends the whole
## deficiency budget, the odd girth bounds the transversal, and `Erdős73On 1 2` splits into exactly
## two statements

New module (**38 declarations, 527 lines, 0 `sorry`, 0 `admit`**, `lake build` OK with **1280
jobs**), imported from the root module `JSPProblem.lean`.  `harness/score.py problems/JSP-000090
--strict-prize`: `build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true,
missing_theorems = ["jsp_000090_main"]`, `prize_ready = false`.  `#print axioms` on the seventeen
headline declarations gives only `[propext, Classical.choice, Quot.sound]`.

Round 129 left the maximum-cut axis closed and named **one** job: the complete `k = 1` case,
`Erdős73On 1 2`, whose constant the machine search of rounds 123–129 shows to be optimal
(`JSP90.k4sub`, `JSP90.p9`).  This round attacks it and splits it into parts that are each provable.

### 1 — at `LocIndep 1` a triangle is an odd cycle transversal (constant `3`)

* **`JSP90.maxDefIn_univ_sdiff_isNClique_three_eq_zero`** — `maxDefIn G (univ \ T) = 0`: at `k = 1` a
  triangle **spends the whole deficiency budget**, so every vertex set disjoint from it has
  deficiency `0`;
* **`JSP90.isBipartite_induceFinset_univ_sdiff_isNClique_three_of_locIndep_one`**,
  **`JSP90.locIndep_zero_induceFinset_univ_sdiff_isNClique_three_of_locIndep_one`** — everything
  outside the triangle is bipartite;
* **`JSP90.closeToBipartite_three_of_locIndep_one_of_isNClique_three`** (with `T` itself as the
  transversal) and **`JSP90.hitsOddCycles_isNClique_three_of_locIndep_one`**;
* **`JSP90.LocIndepOneHasTriangle 3`** — **A NEW INSTANCE OF THE CONCLUSION OF ERDŐS #73, at `k = 1`,
  with the constant `3`, for the class of `LocIndep 1` graphs that contain a triangle.**  Rounds 125
  and 126 needed "every odd cycle is a triangle" for the constant `2`; here only "some triangle
  exists".

### 2 — at `LocIndep 1` the odd girth bounds the transversal

* **`JSP90.isBipartite_deleteFinset_of_isOddCycle_of_locIndep_one`** — **everything outside any odd
  cycle is bipartite** (an odd cycle of the deletion would be disjoint from `C`, while at
  `LocIndep 1` odd cycles pairwise meet);
* **`JSP90.closeToBipartite_of_isOddCycle_of_locIndep_one`**,
  **`JSP90.closeToBipartite_of_locIndep_one_of_isOddCycle_of_card_le`**;
* **`JSP90.closeToBipartite_of_locIndep_one_of_odd_girth`** — **`CloseToBipartite g G` for the odd
  girth `g`**, the classical base case of the induction on Erdős's parameter, never stated before;
* **`JSP90.closeToBipartite_of_locIndep_one_of_oddCycles_of_card_eq`** and its `5`-cycle and
  `7`-cycle corollaries — a `LocIndep 1` graph whose odd cycles all have the same length `g ≥ 3` is
  `g`-close to bipartite.

### 3 — the exact decomposition of `Erdős73On 1 2`

* **`JSP90.LocIndepOneTriangleFree m`** — the triangle-free case;
* **`JSP90.erdos73On_one_of_locIndepOneTriangleFree (m) : Erdős73On 1 (3 + m)`**;
* **`JSP90.erdos73_one_iff_exists_locIndepOneTriangleFree`** — `Erdős73 1 ↔ ∃ m, LocIndepOneTriangleFree m`,
  the `k = 1` form of round 68's `JSP90.erdos73_iff_triangleFreeOnly`;
* **`JSP90.erdos73On_one_two_of_triangle_two_of_locIndepOneTriangleFree`** — **`Erdős73On 1 2`
  follows from `JSP90.LocIndepOneTriangleTwo` (constant `2` when there is a triangle) and
  `JSP90.LocIndepOneTriangleFree 2`**, and
  **`JSP90.not_erdos73On_one_two_of_not_locIndepOneTriangleFree`** shows the triangle-free half is
  **necessary**.  So the residual of this round is a single statement about triangle-free graphs.

### 4 — two machine-checked facts about the constant

* **`JSP90.not_erdos73On_one_one`**, **`JSP90.not_erdos73On_one_of_le`**,
  **`JSP90.not_locIndepOneTriangleFree_one`** — **the constant `1` is refuted at `k = 1`, in the
  `Erdős73On` form and in the triangle-free form** (witness `JSP90.p9` of
  `JSPProblem/Petersen.lean`).  Hence `f(1) ≥ 2`, and if the triangle-free case holds at all its
  constant is **exactly `2`**.
* **`JSP90.not_isNClique_four_of_locIndep_one`**, **`JSP90.not_isClique_card_four_of_locIndep_one`**,
  **`JSP90.not_adj_of_common_neigh_two_of_locIndep_one`** — no `K_4` at `LocIndep 1`; and two
  vertices adjacent to the same two vertices of a triangle are **not** adjacent to each other.

### Measurements made this round (not Lean theorems)

`discovery/JSP-000090/r130c.c` hill-climbs on `max |PetalSet(T)|` over `LocIndep 1` graphs seeded with
petal constructions: the best value is **2** for `n = 6 … 10` (3000 trials each), i.e. round 123's
residual `JSP90.PetalSetLeTwoOfOne` survives to ten vertices and no counterexample was found.
`discovery/JSP-000090/r130.c` hill-climbs on `tau_odd` over `LocIndep 1` graphs, unrestricted and
triangle-free: the best value is **2** for `n = 9` and `n = 10` (250 trials each), i.e. round 129's
exhaustive result (up to `n = 8`) extended by search to ten vertices, with no witness of
`tau_odd ≥ 3`.

### What is *not* proved

`Erdős73On 1 2` — and therefore neither half of Part 3.  `JSP90.LocIndepOneTriangleFree 2` is the
new residual; `JSP90.LocIndepOneTriangleTwo` is the second, since Part 1 reaches `3` rather than `2`
there.  Behind both stands `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the
unchanged primary blocker.  Three statements *attempted and refuted by hand before formalisation*
are recorded in `discovery/JSP-000090/policy.json` (a vertex outside a triangle may meet two of its
vertices; a vertex outside a shortest odd cycle may meet two of its vertices; and the deficiency
hypothesis gives only **lower** bounds on `α`, so no "boundary of a shortest odd cycle" bound of the
shape `|N(C)| ≤ f(MaxDef G)` can be derived from it).  `jsp_000090_main` is not declared, so the
harness keeps reporting `missing_theorems = ["jsp_000090_main"]`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 131 — `lean/JSPProblem/PetalOverlap.lean`: **THE OVERLAP BUDGET**, and the **REFUTATION of
## the petal-overlap bound** (the `k = 1` attachment route is closed)

New module (**46 declarations, 0 `sorry`, 0 `admit`**, `lake build` OK with **1281 jobs**), imported
by the root module `JSPProblem.lean`.  `harness/score.py problems/JSP-000090 --strict-prize`:
`build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true,
missing_theorems = ["jsp_000090_main"]`, `prize_ready = false`.  `#print axioms` on the eight
headline declarations of the file gives only `[propext, Classical.choice, Quot.sound]`.

Round 130 left the `k = 1` case to two statements, `JSP90.LocIndepOneTriangleTwo` and
`JSP90.LocIndepOneTriangleFree 2`, and the second half of the first of those had been attacked for
rounds 123–130 through the **attachment set** of a triangle.  Round 131 proves the natural
*counting* statement behind that approach and then **refutes the family of statements the counting
was supposed to support**.

### Part 1 — the overlap budget

* **`JSP90.two_card_inter_add_one_le_card_of_isOddCycle_of_isIndepSet`** — the classical
  `α(C_m) ≤ ⌊m/2⌋`, for an *arbitrary* independent set of `G` meeting an odd cycle.
* **`JSP90.two_mul_card_add_two_card_inter_add_one_le_card_add_card_of_isOddCycle`** — **THE OVERLAP
  BUDGET, TWO CYCLES**: odd cycles `D`, `E` of `G` and an independent `S ⊆ D ∪ E` satisfy

  > `2 * |S| + 2 * |S ∩ D ∩ E| ≤ |D| + |E| - 2`.

  A vertex of `D ∩ E` that lies in `S` is counted twice on the left: the overlap is *not free*.
* **`JSP90.not_mem_inter_of_locIndep_one`** — **at `LocIndep 1`, the unique meeting point of two odd
  cycles that meet in exactly one point is in no independent set supplied by Erdős's hypothesis**;
  `JSP90.exists_indepSet_avoiding_inter_of_locIndep_one` is the same with `S` produced by the
  hypothesis.

### Part 2 — a vertex of an odd cycle has two neighbours on it

* **`JSP90.two_le_card_inter_neigh_of_mem_isOddCycle`** — `2 ≤ |N(v) ∩ C|` for `v ∈ C`, an odd cycle
  (`JSPProblem/Layer.lean` has the version for a vertex *avoiding* `S`; this is the version for the
  cycle itself, proved from the `CycleOrder` predecessor of `JSPProblem/Branch.lean`).
* **`JSP90.subset_inter_neigh_of_card_neigh_eq_two`** — hence a vertex of an odd cycle whose whole
  neighbourhood has two elements carries **both** of them on every odd cycle through it.

### Part 3 — `sun3`: two petals of a triangle at distinct attachment points meet in ONE vertex

`sun3` (the 3-sun, the graph round 123 called `g6`) is provided by `JSPProblem/Sun.lean` together
with `locIndep_one_sun3` and `not_closeToBipartite_one_sun3`.  Round 131 only computes the attachment
structure of its triangle `T₁ = {0, 1, 2}`:

* **`JSP90.inter_sun3_petal_zero`** (`T₃ = {0, 4, 5}` is the petal at `0`),
  **`JSP90.inter_sun3_petal_two`** (`T₂ = {2, 3, 5}` is the petal at `2`),
  **`JSP90.card_inter_sun3_petals_eq_one`** (`|T₃ ∩ T₂| = 1`), and
  **`JSP90.sun3_three_petals_data`**, which packages the witness.  So the attachment set of `T₁` has
  at least two elements — `JSP90.PetalSetLeTwoOfOne` is *sharp* at `sun3` if it is a theorem — and
  **two petals of a triangle at distinct attachment points need not meet in two vertices.**

### Part 4 — `JSP90.petalOverlapGe_iff`: the **complete classification** of the petal-overlap bound

```lean
JSP90.PetalOverlapGe k : ∀ G T D E a b, LocIndep k G → IsOddCycle G T → T.card = 3 →
    IsOddCycle G D → IsOddCycle G E → (D ∩ T = {a}) → (E ∩ T = {b}) → a ≠ b →
    ∃ S, S ⊆ D ∧ S ⊆ E ∧ 3 - k ≤ |S|
```

(the two petal conditions are stated elementwise, so the definition carries no `DecidableEq`
instance).  Then

* **`JSP90.petalOverlapGe_of_ge_three`** — it holds trivially for `k ≥ 3`;
* **`JSP90.not_petalOverlapGe_one`** — **it is false at `k = 1`**, witnessed by `sun3`;
* **`JSP90.petalOverlapGe_iff : PetalOverlapGe k ↔ k = 0 ∨ 3 ≤ k`** — the complete answer: the bound
  is not a theorem at any `k` at which it is not trivial (at `k = 0` it holds vacuously, because
  `LocIndep 0` forces bipartiteness);
* **`JSP90.pinch`, `JSP90.locIndep_two_pinch`** — the `k = 2` witness: a triangle with a pendant
  triangle at each of two of its vertices, whose two petals are **disjoint**
  (**`JSP90.not_petalOverlapGe_two`**).

### Part 5 — a new instance of the headline theorem

* **`JSP90.erdos73On_of_triangle_of_oddCycles_meet_two`** — **A NEW INSTANCE OF ERDŐS #73, FOR EVERY
  `k`, WITH THE CONSTANT `2`**: if every odd cycle of `G` meets a fixed triangle in at least two
  vertices, two vertices suffice.  The hypothesis is structural — it counts nothing and bounds no
  size, no degree and no girth — and, as in `JSP90.erdos73On_of_edgeCount`, Erdős's hypothesis is
  not needed for the conclusion.

### Measurements (not Lean theorems)

`discovery/JSP-000090/r131.c`, `r131b.c`: exhaustive over **all** `LocIndep 1` graphs on `n ≤ 7`
vertices (up to `986 787` at `n = 7`), all odd cycles computed by a Hamiltonian-path DP:

* **the maximum number of attachment points of a triangle is `0, 0, 1, 2, 2` for `n = 3 … 7`**, so
  `JSP90.PetalSetLeTwoOfOne` survives exhaustively to seven vertices and is *attained* at the 3-sun
  (6 vertices), the smallest graph where a triangle has two attachment points;
* **the minimum `|D ∩ E|` over pairs of petals at distinct attachment points is `1`**, attained at the
  same 6-vertex graph — this is the witness formalised in Part 4;
* `discovery/JSP-000090/r131d.c`: **the geometric form of `JSP90.not_mem_inter_of_locIndep_one` is
  false**: at `LocIndep 1` two odd cycles may meet in exactly one point `x` while a third odd cycle
  avoids `x` — 360 counterexamples at `n = 6`, `45 972` at `n = 7`, the smallest being again the
  3-sun (`{0,3,4} ∩ {1,3,5} = {3}`, and `{2,4,5}` avoids `3`).

### What is *not* proved

`jsp_000090_main` is **not** declared and `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas) is untouched, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.  `Erdős73On 1 2` and both of its halves
(`JSP90.LocIndepOneTriangleTwo`, `JSP90.LocIndepOneTriangleFree 2`) are **not** proved;
`JSP90.PetalSetLeTwoOfOne` is not proved either, and Part 4 shows that the petal-*counting* route to
it has no counting left: only `JSP90.PetalSetLeTwoOfOne`'s own statement, at petals of length `≥ 5`,
remains open.  Two toolchain obstacles found this round are recorded in
`discovery/JSP-000090/policy.json`: the exact value of `PetalSet G C` cannot be computed by `decide`
(two different `DecidableEq (Fin n)` instances — one classical, leaking from `JSPProblem/Petal.lean`,
one computable — coexist, and `Finset.instInter` terms built from them are not defeq), and
`JSPProblem/Petal.lean`'s local instance must be shadowed by hand in any file that mixes its
statements with `decide`.  `formalization.yaml` remains `status: wip`, `prize_ready: false`.  No
award claim is made.

---

## Round 132 — `lean/JSPProblem/MeetSet.lean`: **the MEETING-SET axis** — a new instance of Erdős #73
   for every `t`, its exact constant, and its exact threshold

Round 131's policy asked for the *family* behind its single statement ("every odd cycle meets a
fixed triangle in at least two vertices" ⇒ two vertices suffice): **the odd cycles meet a fixed set
`S` in at least `t` points ⇒ `t` vertices suffice**.  That family is proved here for **every `t`**,
together with **both** sharpness results, so the axis is closed on both sides.

### Part 1 — the pigeonhole step

`JSP90.MeetSet G S t` (`lean/JSPProblem/MeetSet.lean`): every odd cycle of `G` meets `S` in at least
`t` of its vertices.  The step is elementary:

* **`JSP90.hitsAllOddCycles_of_meetSet_of_card_le`** — if `Z ⊆ S` leaves fewer than `t` points of `S`
  uncovered (`|Z| + t > |S|`), every odd cycle meets `Z`;
* **`JSP90.closeToBipartite_of_meetSet_of_card_le_two_mul_sub_one`** — **A NEW INSTANCE OF THE
  HEADLINE THEOREM, FOR EVERY `t`**: `1 ≤ t`, every odd cycle meets a set `S` with `|S| ≤ 2t - 1` in
  at least `t` points ⇒ `G` is `t`-close to bipartite.  Erdős's hypothesis is **not used**;
* **`JSP90.exists_hitsAllOddCycles_of_meetSet_of_card_le_two_mul_sub_one`** — the same statement with
  the location of the transversal made explicit: the transversal can be **chosen inside `S`**;
* **`JSP90.erdos73On_of_meetSetHypothesis_of_le`** — the instance form,
  `LocIndep k G → MeetSetHypothesis t G → CloseToBipartite m G` for every `t ≤ m`, and
  **`JSP90.erdos73On_of_meetSetHypothesis_one`** (the `t = 1` level: every odd cycle passes through
  one fixed vertex);
* the quantified class **`JSP90.MeetSetErdős73On`**, discharged by
  **`JSP90.meetSetErdős73On`** and consumed by **`JSP90.erdos73On_of_meetSetErdős73On`**.

### Part 2 — round 131 recovered without the triangle hypothesis

* **`JSP90.closeToBipartite_two_of_oddCycles_meet_set_of_card_three`** — the `t = 2` level with an
  **arbitrary three-set**: the set need not be a cycle, and need not be adjacent.  It implies round
  131's statement (`JSP90.closeToBipartite_two_of_oddCycles_meet_C` recovers it verbatim), so the
  triangle hypothesis of `JSP90.closeToBipartite_two_of_oddCycles_meet_two` is **dead weight**;
* **`JSP90.meetSet_two_of_neigh_outside`** — a reusable structural lemma: if every vertex outside `S`
  has all of its neighbours in `S`, then every odd cycle meets `S` in at least two vertices (a vertex
  of an odd cycle carries two of its cycle-neighbours, and both lie on `S`; an odd cycle avoiding `S`
  would have exactly three vertices).

### Part 3 — the hypothesis forces Erdős–Pósa to be at `r = 1`

* **`JSP90.exists_mem_inter_of_meetSet_of_card_le_two_mul_sub_one`** — **any two odd cycles of `G`
  share a point of `S`** (two `t`-point subsets of a set of `≤ 2t - 1` points meet);
* **`JSP90.inter_oddCycle_of_meetSet_of_card_le_two_mul_sub_one`**,
  **`JSP90.subset_singleton_of_meetSet_of_card_le_two_mul_sub_one`** and
  **`JSP90.card_isOddCycleFamily_le_one_of_meetSet_of_card_le_two_mul_sub_one`** — so **every family
  of pairwise vertex-disjoint odd cycles of `G` has at most one member**: under the hypothesis the
  packing number is `≤ 1`.

### Part 4 — sharpness, machine-checked in both directions

* **The constant `t` is optimal at `|S| = 2t - 1`.**  `sun3`, the 3-sun, satisfies
  `MeetSet T₀ 2` (`JSP90.meetSet_two_sun3`, from `JSP90.meetSet_two_of_neigh_outside`: the three
  degree-two vertices outside `T₀` have all their neighbours on `T₀`) and is not one vertex away from
  bipartite (`JSP90.not_closeToBipartite_one_of_meetSet_two_sun3`).  So the meeting-set hypothesis
  buys nothing at `t = 2` even at a `LocIndep 1` graph (`JSP90.locIndep_one_sun3`).
* **The threshold `2t - 1` is optimal.**  `K₅` with `S` four of its five vertices satisfies
  `MeetSet S 2` (`JSP90.meetSet_completeGraph_five`, from the new
  `JSP90.meetSet_two_of_card_sdiff_le_one`: a set missing at most one vertex is met in two points) and
  is not `2`-close to bipartite (`JSP90.not_closeToBipartite_two_completeGraph_five`), so
  `JSP90.closeToBipartite_of_meetSet_of_card_le_two_mul_sub_one` **cannot be extended from `|S| ≤ 3`
  to `|S| ≤ 4`** (`JSP90.not_forall_closeToBipartite_two_of_meetSet_two_of_card_four`).
* **The packing conclusion fails at `2t` as well.**  `twoPend` — `K₄` with a pendent triangle on each
  of the disjoint edges `0 – 1` and `2 – 3` — satisfies `MeetSet pendS 2` for the four-set `pendS`
  (`JSP90.meetSet_two_twoPend`) and has **two vertex-disjoint odd cycles**
  (`JSP90.exists_two_oddCycles_of_twoPend`), so "any two odd cycles share a point" fails at `2t`
  (`JSP90.not_forall_oddCycles_meet_of_meetSet_two_of_card_four`).
* **The pigeonhole claim itself is false at `2t`.**  `JSP90.PigeonholeClaim` (elementwise) is proved
  for `|S| ≤ 2t - 1` (`JSP90.pigeonholeClaim_of_card_le_two_mul_sub_one`) and refuted for
  `|S| = 2t` (`JSP90.not_pigeonholeClaim_two_mul`).

### Toolchain note (new this round)

Every finset statement of this file is built with `JSP90.instDecidableEqMeetSet`, which differs both
from the instance of the imported statements (`Transversal.lean`, `Packing.lean`) **and**, for a
concrete vertex type such as `Fin 5` or `Fin 6`, from the *computable* `DecidableEq` that instance
synthesis then picks.  The consequences are recorded in `policy.json`: a statement about
`C ∩ S` for a concrete `S` is **not** the statement inside `MeetSet`, and `exact` cannot cross;
`rw`, `simp`, `ext`, `subst` and `Finset.eq_empty_iff_forall_notMem` do cross, and the elementwise
predicates `JSP90.HitsAllOddCycles` / `JSP90.PigeonholeClaim` avoid the problem entirely.  Two
further traps: `Finset.exists_subset_card_eq` has **both** arguments implicit — `(... (n := t) h)` —
or the goal is proved against a fresh metavariable; and `Finset.card_le_one` at this revision is
`#s ≤ 1 ↔ ∀ a ∈ s, ∀ b ∈ s, a = b`, not the `∃ a, s ⊆ {a}` of later Mathlib.

### What is *not* proved

`jsp_000090_main` is **not** declared: `JSP90.OddCycleErdosPosa r` (Erdős–Pósa for odd cycles,
Reed–Robertson–Seymour–Thomas) is untouched, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.  The meeting-set family is an instance of the headline
theorem on a *structural* class, not a step towards `Erdős73 k m` for all graphs: in particular
`JSP90.LocIndepOneTriangleTwo` and `JSP90.LocIndepOneTriangleFree 2` are still unproved, and
`JSP90.PetalSetLeTwoOfOne` is untouched.  `formalization.yaml` remains `status: wip`,
`prize_ready: false`.  No award claim is made.

---

## Round 134 — `JSPProblem/AttachErase.lean` + `JSPProblem/Nonagon.lean`: **`JSP90.PetalSetLeTwoOfOne`
IS REFUTED** (the top target of rounds 119–131), and the erasable vertices of an odd cycle are
characterised

Two new files (52 + 31 declarations, **0 sorry/admit**, `lake build` OK with 1284 jobs, axiom report
clean: `propext, Classical.choice, Quot.sound` only), imported from the root module `JSPProblem.lean`.

### Part 1 — **the erasable vertices of an odd cycle** (`AttachErase.lean`)

`JSP90.PetalSet G C` (`JSPProblem/Petal.lean`) is the attachment set of the odd cycle `C`.  Rounds
119–131 used it only in the direction "if `p` is not an attachment point then `C.erase p` meets every
odd cycle", and only at a triangle.  Round 134 proves the **exact** statement, for **every** odd
cycle, with no hypothesis beyond "every odd cycle meets `C`":

* **`JSP90.hitsOddCycles_erase_iff_notMem_petalSet`** —

  ```lean
  HitsOddCycles G (C.erase p) ↔ p ∉ PetalSet G C            -- C an odd cycle, p ∈ C
  ```

  i.e. **the vertices of an odd cycle which cannot be erased are exactly its attachment points**, and
  nothing else blocks the erasure;
* **`JSP90.closeToBipartite_erase_of_notMem_petalSet`**, **`…_card_sub_one_of_petalSet_lt_card`** —
  hence `CloseToBipartite (|C| - 1) G` as soon as the attachment set is a proper subset of `C`, with
  the certificate `C.erase p` (**contained in the cycle**);
* **`JSP90.erdos73On_of_isOddCycle_of_petalSet_lt_card`** — **a new instance of the headline theorem,
  for an arbitrary odd cycle and the constant `|C| - 1`** (Two.lean had it only for triangles with the
  constant `2`, Petal.lean with `|C| - 1 + |PetalSet|`), and
  **`JSP90.closeToBipartite_of_locIndep_one_of_odd_girth_of_petalSet_lt_card`**, which improves the
  odd-girth bound `ℓ · k` of `JSPProblem/Transversal.lean` to `ℓ - 1` at `k = 1`;
* **`JSP90.isOddCycle_of_isNClique_three`** — the conversion `IsNClique 3 T → IsOddCycle G T`, which
  the development lacked (only the converse, `JSPProblem/Free.lean`, existed);
* **`JSP90.erdos73On_one_iff_twoTransversal`** — **`Erdős73On 1 m ↔ TwoTransversal m`**: the sharp
  case `k = 1` *is* the statement "some `m` vertices meet every odd cycle", with no shape assumed.

### Part 4 — the "high intersection" route is refuted, machine-checked

* **`JSP90.not_forall_card_sdiff_le_one_wf`** — at `LocIndep 1` an odd cycle need **not** use all but
  one vertex of a **shortest** odd cycle: on the windmill `wf` (`JSPProblem/Windmill.lean`) the two
  triangles `{0,1,2}` and `{0,3,4}` are both shortest odd cycles and meet in the single vertex `0`.
  The hypothesis of `JSP90.closeToBipartite_of_oddCycle_high_intersection` (Two.lean, item 5) is
  therefore not a consequence of `LocIndep 1`, and that route must not be retried;
  **`JSP90.two_shortest_oddCycles_can_meet_in_one_wf`** records the same fact as a statement about odd
  cycles (it holds for the *petals* of a triangle, Two.lean item 2, but not for arbitrary odd cycles).

### Part 5 — **`JSP90.PetalSetLeTwoOfOne` IS FALSE** (`Nonagon.lean` + `AttachErase.lean`)

The exhaustive search run this round (`discovery/JSP-000090/r134.c`) over **all** graphs with
`MaxDef ≤ 1` on `n ≤ 8` vertices (55 179 262 of them, 140 216 552 triangles) found **no** failure,
and then found the **first counterexample at `n = 9`**:

```
g9 (Fin 9):  0-5 0-6 0-7 0-8 1-5 1-6 2-5 2-8 3-6 3-7 4-7 4-8 5-7 6-8
```

`JSPProblem/Nonagon.lean` formalises the witness (`JSP90.locIndep_one_g9` is an exhaustive kernel
decision over the `2 ^ 9` vertex sets; the two triangles `T₁ = {0,5,7}`, `T₂ = {0,6,8}` and the six
petals are exhibited as explicit cyclic orderings), and `JSPProblem/AttachErase.lean` draws the
consequences:

* **`JSP90.not_forall_oddCycle_exists_erase_g9`** — **THE "ERASE ONE VERTEX OF A TRIANGLE" STEP IS
  IMPOSSIBLE IN `g9`**: no triangle of `g9` has a `2`-subset meeting every odd cycle.  By Part 1 this
  is exactly the statement "every triangle has a vertex lying in no odd cycle", i.e. **the residual
  `JSP90.PetalSetLeTwoOfOne` of rounds 119–131 — the top target of `policy.json` since round 123 —
  is false**;
* **`JSP90.not_exists_twoTransversal_sub_g9_T1` / `…_g9_T2`** — **not even a free choice of two
  vertices inside a shortest odd cycle works**: no set of at most two vertices of `T₁` or of `T₂`
  meets every odd cycle of `g9`.  So the shape "two vertices of a shortest odd cycle"
  (`JSP90.ShortestOddCycleTransversal 2`) is refuted as well;
* **`JSP90.triangleCertificates_are_impossible`** — the two refutations in one statement.

The **conclusion** is *not* refuted: the search measures the least odd cycle transversal number of
`g9` to be `2`, with certificate `{5, 6}` — a pair lying in **neither** triangle (`5 ∈ T₁ \ T₂`,
`6 ∈ T₂ \ T₁`).  So `f(1) = 2` remains the sharp candidate, and the two statements of this round that
had been proposed as *conjectures* are now marked refuted in the source:
`JSP90.PetalSetLeTwoOfOneAny` and `JSP90.ShortestOddCycleTransversal m` are `def`s that **must not be
assumed**.  The honest residual of the sharp case `k = 1` is `JSP90.TwoTransversal 2`, which
`JSP90.erdos73On_one_iff_twoTransversal` proves **equivalent** to `Erdős73On 1 2`, and
`JSP90.TriangleFreeTwoTransversal 2` + `JSP90.triangleFree_iff_triangleFreeTwoTransversal` give the
triangle-free half of it in its strongest available form (no containment requirement).

### What is *not* proved

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas) is untouched, and the machine-checked refutations above mean that the
whole family of *triangle-based* certificates for `k = 1` (attachment sets, petals, two vertices of an
odd cycle) is closed.  `formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award
claim is made.

---

## Round 135 — `JSPProblem/BoundaryOne.lean` + `JSPProblem/Fan4.lean`: **the fan of a shortest odd
cycle at `k = 1`**, a new instance with the optimal constant `2`, and the refutation of the
"small fan" route

Attack family 64.  Two new files (19 + 17 declarations, **0 sorry/admit**), `lake build` OK with
**1286 jobs**; `score.py --strict-prize` reports `build_ok = true, sorry = 0, admit = 0,
partial_ok = true, missing_theorems = ["jsp_000090_main"]`.

Round 134 closed the attachment-*point* axis by a machine-checked refutation (`g9`) and left one
residual, `JSP90.TwoTransversal 2` (`⟺ Erdős73On 1 2`).  This round takes the third certificate shape
— the two vertices may lie anywhere in the **closed neighbourhood of a shortest odd cycle** — and
proves the exact structural content of the fan at `k = 1`, which no earlier round had.

### Part 1–2 — the structural content (`JSPProblem/BoundaryOne.lean`)

* **`JSP90.isBipartite_outerLayer_of_locIndep_one`** — **at `LocIndep 1` the part of `G` at distance
  `≥ 2` from an odd cycle is bipartite.**  The outer layer is separated from the cycle by
  construction (`JSP90.separated_outerLayer`), so an odd cycle in it would be a second odd cycle
  *disjoint* from `C`, which `LocIndep 1` forbids (`JSP90.inter_oddCycle_of_locIndep_one`).  This
  discharges the extra hypothesis of `JSP90.closeToBipartite_of_bipartite_outerLayer` (round 61),
  which therefore now applies at `k = 1` for free;
* **`JSP90.oddCycle_eq_or_inter_boundary_of_locIndep_one`** — **THE FAN OF A SHORTEST ODD CYCLE IS AN
  ODD-CYCLE TRANSVERSAL**: for every odd cycle `D`, `D = C ∨ D ∩ boundary G C ≠ ∅`.  The hypothesis
  that `C` is *shortest* is essential (`JSPProblem/BoundaryOne.lean`'s search finds counterexamples
  for arbitrary `C`, e.g. `C = V`);
* **`JSP90.sub_C_or_outer_of_oddCycle`** — the layer lemma behind it: a cycle meeting a shortest odd
  cycle lies on one side of the anticomplete split `C ⊔ outerLayer G C`.

### Part 3 — new instances, constant = the size of the fan

* `JSP90.closeToBipartite_boundary_add_one_of_locIndep_one` — the conclusion of Erdős #73 with the
  constant `|boundary G C| + 1`;
* `JSP90.closeToBipartite_one_of_boundary_empty` — **constant `1`** when the fan is empty;
* **`JSP90.erdos73On_one_of_boundary_le_one` — A NEW INSTANCE OF THE HEADLINE THEOREM** with the
  **sharp** constant `2` when the fan has at most one vertex;
* `JSP90.hitsOddCycles_boundary_singleton_of_locIndep_one` — the certificate is
  `boundary G C ∪ {c}`.

### Part 4 — the fan is unbounded at `k = 1` (`JSPProblem/Fan4.lean`, machine-checked)

The witness is the six-vertex graph `fan4` = the triangle `{0, 4, 5}` with three pendant vertices at
`5`:

* `JSP90.locIndep_one_fan4` (exhaustive kernel decision over the `2^6` vertex sets);
* `JSP90.mem_isOddCycle_fan4` — **`{0, 4, 5}` is the only odd cycle of `fan4`** (a vertex of an odd
  cycle has two neighbours, `JSP90.two_le_card_neigh_of_mem_oddCycle`, and `1, 2, 3` are pendant);
* `JSP90.card_boundary_fan4` — its fan is `{1, 2, 3}`, of size `3`;
* **`JSP90.not_exists_boundary_le_two_fan4` — THE "SMALL FAN" ROUTE IS DEAD**: `LocIndep 1` does not
  supply an odd cycle with a fan of at most `m` elements for any `m ≥ 2`;
* `JSP90.closeToBipartite_one_fan4` — yet `fan4` is `1`-close to bipartite, so the big fan is not a
  counterexample.

### Part 5 — the same content under the packing condition, without Erdős's hypothesis

* `JSP90.isBipartite_outerLayer_of_packing_one`,
  `JSP90.oddCycle_eq_or_inter_boundary_of_packing_one`,
  `JSP90.closeToBipartite_boundary_add_one_of_packing_one`;
* **`JSP90.erdos73On_of_boundary_le_one_of_packing_one` — A NEW INSTANCE OF THE HEADLINE THEOREM**:
  for **every** `k`, `LocIndep k G` + `PackingNumberOne G` + a shortest odd cycle whose fan has at
  most one vertex give `CloseToBipartite 2 G`, the **optimal constant**, with no bound on the odd
  girth, packing weight or number of branch vertices.  It is incomparable with
  `JSP90.erdos73On_of_packing_one` (round 40), which bounds the transversal by the **odd girth** `ℓ`:
  `K_5` has packing number one and fan `2`, `fan4` has `LocIndep 1` and fan `3`.

### The residual of the sharp case `k = 1`, in one statement

* **`JSP90.FanTwoResidual`** — `LocIndep 1 G`, `C` a shortest odd cycle, `2 ≤ |boundary G C|`, then
  some set of at most two vertices of `C ∪ boundary G C` meets every odd cycle of `G`;
* **`JSP90.erdos73On_one_two_of_fanTwoResidual`** — that single statement implies the **sharp**
  `Erdős73On 1 2` (the three cases: bipartite; fan `≤ 1`, handled by Part 3; fan `≥ 2`, the
  hypothesis).  So the case `k = 1` is reduced to a statement about the **fan of one shortest odd
  cycle** and nothing else.

### Measurements (exhaustive search outside Lean, `discovery/JSP-000090/r135.c`)

Over **all** `903 792` graphs with `MaxDef ≤ 1` on `n ≤ 7` vertices:

* `τ_odd ≤ 2` everywhere (`τ_odd = 2` first at `n = 6`);
* `FanTwoResidual` holds: a two-vertex certificate inside `C ∪ boundary G C` exists for **every**
  shortest odd cycle `C` in **every** case (0 failures);
* the maximum of `min_C |boundary G C|` over shortest odd cycles `C` is `4` (at `n = 7`, `fan4`),
  `3` at `n = 6`, and `2` restricted to triangle-free graphs — so `FanTwoResidual`'s threshold `2` is
  the smallest possible;
* for an arbitrary (non-shortest) odd cycle `C`, the fan-transversal statement of Part 2 **fails**
  (e.g. `C = V` in a graph with two odd cycles), confirming that "shortest" is essential.

`jsp_000090_main` is **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `formalization.yaml` remains `status: wip`,
`prize_ready: false`.  No award claim is made.

---

## Round 136 — `JSPProblem/AttachPoints.lean`: **the attachment points of a shortest odd cycle**, the
fan-entry lemma, and a *strictly tighter* residual for the sharp case `k = 1`

Attack family 65.  One new file (**25 declarations, 0 sorry/admit**), `lake build` OK with
**1287 jobs**; `score.py --strict-prize` reports `build_ok = true, sorry = 0, admit = 0,
partial_ok = true, missing_theorems = ["jsp_000090_main"]`.

Round 135 reduced the sharp case `k = 1` to `JSP90.FanTwoResidual` (hypothesis: `2 ≤ |fan|`).  This
round attacks it from a **new** direction: instead of the *fan* (`boundary G C`, the vertices outside
the cycle that touch it) the object studied is the **attachment set**

```lean
JSP90.attachPoints G C = ⋃_{y ∈ boundary G C} (attachSet G C y)
                       = { a ∈ C : a has a neighbour in boundary G C }
```

— the vertices **of the cycle** on which a fan vertex hangs (`JSP90.attachSet` is round 117's
`JSPProblem/Book.lean`).  It is the mirror image of the fan: it always lies **on** `C`
(`JSP90.subset_attachPoints_C`) and is disjoint from it (`JSP90.disjoint_attachPoints_boundary`).  On
the six-vertex witness `fan4` of round 135 the fan is `{1, 2, 3}` while the attachment points are the
single vertex `5`.

### Part 1–2 — the key lemma: **fan entry**

* **`JSP90.sub_inter_or_sdiff_of_isOddCycle`** — an odd cycle does not cross a vertex set: if no edge
  of `G` joins `D ∩ X` to `D \ X`, then `D ⊆ D \ X` or `D ⊆ D ∩ X`.  (`JSP90.isOddCycle_sub_anticoverIn`
  of round 106 applied to the induced graph on `D`.)
* **`JSP90.exists_mem_boundary_neigh_inter_of_isOddCycle_ne_of_packing_one` — FAN ENTRY**: every odd
  cycle `D ≠ C` contains a fan vertex `y` **together with a neighbour of `y` lying on `D ∩ C`**:

  ```lean
  ∃ y ∈ D ∩ boundary G C, (neighOf G {y} ∩ D ∩ C).Nonempty
  ```

  The proof is the classical two-line argument: by round 135's Part 2, `D` meets the fan; if no fan
  vertex of `D` had a neighbour on `D ∩ C`, no edge would join `D ∩ C` to `D \ C` (an endpoint of such
  an edge outside `C` *is* a fan vertex), so by Part 1 the cycle `D` would lie inside `C`
  (impossible: `C` is shortest) or entirely off `C` (impossible: two vertex-disjoint odd cycles).

### Part 3–5 — the attachment points are an odd-cycle transversal, and the instances

* **`JSP90.hitsOddCycles_attachPoints_of_packing_one` — THE ATTACHMENT POINTS OF A SHORTEST ODD CYCLE
  ARE AN ODD-CYCLE TRANSVERSAL** (`HitsOddCycles G (attachPoints G C)`).  Only
  `JSP90.PackingNumberOne` is used, so this is available for **every** `k` with the packing condition
  in place of Erdős's hypothesis;
* `JSP90.hitsOddCycles_attachPoints_union_singleton_of_packing_one` — the same with one vertex of `C`
  added, which also covers the **empty** fan;
* `JSP90.closeToBipartite_of_attachPoints_le_of_packing_one` — the conclusion of Erdős #73 with the
  constant `|attachPoints|`;
* **`JSP90.closeToBipartite_one_of_attachPoints_le_one_of_packing_one` — A NEW INSTANCE WITH THE
  CONSTANT `1`** (compare round 135's `|fan| + 1`, which is `4` on `fan4`);
* **`JSP90.erdos73On_one_two_of_attachPoints_le_two_of_packing_one` — A NEW INSTANCE OF THE HEADLINE
  THEOREM: THE OPTIMAL CONSTANT `2`, FOR EVERY `k`**, with no bound on odd girth, packing weight or
  branch vertices;
* `JSP90.hitsOddCycles_pair_of_attachPoints_sub` and
  `JSP90.erdos73On_one_two_of_boundary_card_eq_two_of_attachPoints_le_two` — **the concrete provable
  case of `FanTwoResidual`**: a fan of size `2` with at most two attachment points, the certificate
  being the attachment set itself (two *named* vertices when they are given).

The constant `1` is exactly tight: `|attachPoints| ≤ 1` forces `τ_odd = 1`, because the attachment
points are then themselves a one-vertex transversal.

### Part 6 — a **strictly tighter** residual: `JSP90.AttachThreeResidual`

Because the cases `|boundary G C| = 0` and `|attachPoints| ≤ 2` are now theorems, the residual of the
sharp case `k = 1` can be stated **with no hypothesis on the fan at all**:

```lean
JSP90.AttachThreeResidual : LocIndep 1 G → C shortest odd cycle → 3 ≤ |attachPoints G C| →
                             ∃ X, |X| ≤ 2 ∧ X meets every odd cycle of G
```

* **`JSP90.erdos73On_one_two_of_attachThreeResidual`** — that single statement implies the **sharp**
  `Erdős73On 1 2`;
* **`JSP90.fanTwoResidual_of_attachThreeResidual`** — it implies round 135's `FanTwoResidual`, i.e. the
  residual is now *provably weaker* than it was (`3 ≤ |attachPoints|` forces `2 ≤ |fan|`, and the rest
  of `FanTwoResidual` is a theorem of this file).

### Part 7 — `K₄`-freeness and the missing `|C| = 3` half of the fan bound

* **`JSP90.card_isClique_le_two_add`** — under `LocIndep k`, **every clique has at most `k + 2`
  vertices**, for **every** `k` (so `LocIndep 1` forbids `K_4`; the `IsNClique` forms are round 121's
  `JSP90.not_isNClique_four_of_locIndep_one` / `not_isClique_card_four_of_locIndep_one`);
* **`JSP90.card_attachSet_le_two_of_locIndep_one`** — at `LocIndep 1` a fan vertex of a **shortest**
  odd cycle has at most **two** attachment points, **including when the cycle is a triangle**.  Round
  35's `JSP90.card_inter_neigh_le_two` (via round 117's `JSP90.card_attachSet_le_two`) needs
  `5 ≤ |C|`; the missing `|C| = 3` half is the `K₄`-free observation (an independent set of size `≥ 2`
  cannot live in `{x} ∪ C` when `x` is adjacent to all three vertices, by
  `JSP90.indep_card_le_of_odd_cycle`).  The search confirms both halves.

### Measurements (exhaustive search outside Lean, `discovery/JSP-000090/r136.c`)

Over **all** `986 787` graphs with `MaxDef ≤ 1` on `n = 7` vertices (and all smaller ones):

* `Q1`: **0 failures** — the attachment points of a shortest odd cycle really are an odd-cycle
  transversal (every odd cycle `D ≠ C` meets them), confirming Part 4;
* `Q2`: `τ_odd ≤ 2` everywhere (0 failures);
* `Q3`: `max_G min_C |attachPoints G C| = 4`, so the residual threshold `3` is **optimal**;
* `Q4`: `max |N(x) ∩ C| = 2` both for `|C| = 3` and for `|C| ≥ 5`, confirming Part 7;
* histogram of `min_C |attachPoints G C|` at `n = 7`: `0: 2299`, `1: 68460`, `2: 557676`,
  `3: 254485`, `4: 630` — the residual is very far from vacuous;
* `Q6`: the residual is non-vacuous already on **five** vertices: edges `0-2 0-3 0-4 1-2 1-3 1-4 2-3`
  (a `K_{2,3}` plus one edge) has two shortest odd cycles, both triangles sharing the edge `2-3`, and
  all three vertices of each are attachment points (`min_C |attachPoints| = 3`, while `τ_odd = 1`).

### What is *not* proved

`JSP90.AttachThreeResidual`, and behind it `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  `jsp_000090_main` is **not**
declared, so the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`;
`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 137 — the SEGMENTS of an odd cycle inside a shortest odd cycle, and the sharpness of the
constant `2` at `k = 1` (`lean/JSPProblem/Segment.lean`, `lean/JSPProblem/SharpTwo.lean`)

### The key lemma (machine-checked, no hypothesis on `k`)

```
JSP90.two_le_card_attachPoints_inter_of_card_inter_ge_two
  2 ≤ (C ∩ D).card  ⟹  2 ≤ (attachPoints G C ∩ D).card
```

for every odd cycle `D ≠ C` and every **shortest** odd cycle `C`.  Reading the vertices of `D` in the
order of its cyclic numbering, those lying on `C` come in maximal **segments**, and the classical fact
is that *both ends of each segment are attachment points of `C`*:

* `JSP90.mem_attachPoints_exit` — if `o.f i ∈ C` and `o.f (cycSucc i) ∉ C`, then
  `o.f i ∈ attachPoints G C` (the successor is a fan vertex attached to it);
* `JSP90.mem_attachPoints_entry` — the mirror image at the other end of a gap;
* `JSP90.exists_exit_of_mem_of_exists_not_mem` / `…_entry_…` — the same statement with the whole walk
  inside `C` (`JSP90.CycleOrder.exists_iter`, `iter_succ`, `prev_iter` do the index bookkeeping).

The only obstruction is a **one-point cross-over** `C ∩ D = {a}`, which contributes a *single*
attachment point.  Hence the new hypothesis

```
JSP90.NoCrossOver G C := ∀ D, IsOddCycle G D → D ≠ C → (C ∩ D).card ≠ 1
```

### The instances: attachment points pay `|attachPoints| − 1`

* **`JSP90.hitsOddCycles_erase_of_attachPoints_of_noCrossOver`** —
  `attachPoints G C \ {a}` meets **every** odd cycle of `G`, for every `a ∈ attachPoints G C` and
  `2 ≤ |attachPoints G C|`; only `PackingNumberOne` is used, so it holds for **every** `k`;
* `JSP90.closeToBipartite_of_noCrossOver` — the conclusion with the constant `|attachPoints G C| − 1`,
  the certificate lying **on the shortest odd cycle**;
* `JSP90.closeToBipartite_one_of_noCrossOver_of_card_attachPoints_eq_two` — the **optimal** constant
  `1` at `k = 1`;
* `JSP90.erdos73On_one_two_of_noCrossOver_of_card_attachPoints_le_three` — the **optimal** constant
  `2`, for every `k`;
* `JSP90.hitsOddCycles_pair_of_noCrossOver_of_card_attachPoints_eq_three` — **any pair** of the three
  attachment points is a certificate (again on `C`, not in its fan).

### The tighter residual

```
JSP90.AttachThreeResidualRefined : LocIndep 1 G → C shortest odd cycle → 3 ≤ |attachPoints G C| →
      ∃ a b, a ≠ b ∧ a, b ∈ attachPoints G C ∧ HitsOddCycles G {a, b}
```

* `JSP90.erdos73On_one_two_of_attachThreeResidualRefined` — it implies the **sharp**
  `Erdős73On 1 2`;
* `JSP90.attachThreeResidual_of_attachThreeResidualRefined` — it implies round 136's
  `AttachThreeResidual`, i.e. the residual is *formally weaker*;
* it is equivalent to a single hard case: with `A = {a, b, c}` and no cross-over, every odd cycle meets
  `A` twice, so **every** pair of `A` works; the whole difficulty is the one-point cross-over, where the
  certificate must come from **outside** `C` (measured: the cross-over vertex itself never works).

### The sharpness of the constant `2` at `k = 1`, machine-checked on six vertices

`JSPProblem/SharpTwo.lean`, the graph `sharp2` on `Fin 6` with edges

```
0-1  0-2  0-4  0-5  1-2  1-3  1-5  2-3  2-4
```

* **`JSP90.locIndep_one_sharp2`** — `LocIndep 1 sharp2` (exhaustive kernel decision over the `2⁶`
  vertex sets), so `sharp2` is a genuine member of the class of JSP-000090;
* **`JSP90.hitsOddCycles_sharp2_pair`** / **`JSP90.closeToBipartite_two_sharp2`** — the pair `{0, 2}`
  meets every odd cycle (an odd cycle has three or five vertices; a three-element set of `Fin 6`
  contains `0` or `2` because `|Fin 6 \ {0, 2}| = 4 < 5`, and a triangle inside `{1, 3, 4, 5}` is
  impossible);
* **`JSP90.not_closeToBipartite_one_sharp2`** — for every vertex there is a triangle avoiding it, so
  `¬ CloseToBipartite 1 sharp2`: **`Erdős73On 1 1` is false**;
* **`JSP90.optimal_constant_one_is_two`** — the three statements together: `f(1) = 2` exactly, and the
  constant cannot be lowered;
* `JSP90.short_of_isOddCycle_sharp2_012`, `JSP90.boundary_sharp2_T` (the fan of `{0, 1, 2}` is
  `{3, 4, 5}`), `JSP90.attachPoints_sharp2_T` / `JSP90.card_attachPoints_sharp2` (its attachment
  points are `{0, 1, 2}`, of size `3`) — the **smallest** instance of `AttachThreeResidualRefined`,
  with the certificate `{0, 2}` inside the attachment points.  Both the fan *and* the attachment points
  have three elements here, which closes the two "small object" routes at once.

### Measurements (exhaustive search outside Lean, `discovery/JSP-000090/r137.c`)

Over **all** `986 787` graphs with `LocIndep 1` on `n ≤ 7` vertices:

* `Q1`: **0 failures** for the segment lemma `2 ≤ |C ∩ D| → 2 ≤ |attachPoints G C ∩ D|`;
* `Q2`: the naive "no cross-over ⇒ *every* pair of attachment points is a certificate" has `2520`
  failures (it fails for `|attachPoints| ≥ 4`), which is why only the `|A| ≤ 3` form is kept;
* `Q4`: "the vertex of a one-point cross-over is a transversal" has `63720` failures — the cross-over
  case genuinely needs a certificate outside `C`;
* `Q6`: in **all** `258 550` graphs with `min_C |attachPoints G C| ≥ 3` the two-vertex certificate can
  be taken **inside the attachment points**, which is what `AttachThreeResidualRefined` asks for;
* `Q7`: `max τ_odd = 2`, the first example having **six** vertices — the witness formalized above;
* `Q8`: with `|A| = 3` all three pairs of `A` do occur on some common odd cycle, so the
  "some pair never co-occurs" route is refuted.

### What is *not* proved

`JSP90.AttachThreeResidualRefined`, and behind it `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  `jsp_000090_main` is **not**
declared, so the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`;
`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 139 — `JSPProblem/CrossPair.lean`: **the cross-over points force the certificate**

New file `lean/JSPProblem/CrossPair.lean` (**40 declarations, 0 sorry/admit**, `lake build` OK with
1291 jobs), imported from the root module `JSPProblem.lean`.  This is the **nineteenth attack family**,
and it does not decompose anything: it is a one-line observation about *which* two-element certificate
the sharp case `k = 1` has, and it turns round 138's existential residual into a statement about a
**finite, forced object**.

### The one-line lemma (Part 1)

With `C` a shortest odd cycle and `X(C)` the **cross-over points** of `C` — the attachment points at
which some other odd cycle leaves `C` in one point (`JSP90.CrossOverPoint G C x` of round 138, now
made into the `Finset` `JSP90.crossOverSet G C`) — one has

```lean
JSP90.subset_pair_of_hitsOddCycles_pair_of_mem :
    a ≠ b → a, b ∈ C → HitsOddCycles G {a, b} → crossOverSet G C ⊆ {a, b}
```

**THE CERTIFICATE IS FORCED BY THE CROSS-OVER POINTS.**  For the cross-over cycle `D` through a point
`x ∉ {a, b}` one has `C ∩ D = {x}`, so `D` avoids both `a` and `b` (they lie on `C`), contradicting
that `{a, b}` meets every odd cycle.  No minimality of `C`, no packing hypothesis and no `LocIndep` are
used.  Measured with **0 failures in `3 157 110` pairs** (`discovery/JSP-000090/r139e.c`, question
`S1`); the weaker version in which the pair merely *meets* the attachment points fails `1 099 680`
times and the version at `|attachPoints G C| ≤ 2` fails `1 160 160` times, so both hypotheses are
essential.

### Consequences proved here

* **`JSP90.not_mem_crossOverSet_of_mem_of_hitsOddCycles_pair_of_mem`** and
  **`JSP90.not_hitsOddCycles_pair_of_mem_of_three_crossOverPoint`** — **machine-checked negative
  results**: a vertex of `C` outside a two-element certificate of `C` is not a cross-over point, and
  **three cross-over points obstruct every two-element certificate lying on `C`**.  So a
  two-element certificate on `C` can exist only if `C` has at most two cross-over points, which
  explains why the threshold `2` of the residual is the right one;
* **`JSP90.crossPairResidual_iff_crossOverResidual`** — round 138's residual `JSP90.CrossOverResidual`
  is **equivalent** to its new *forced* form `JSP90.CrossPairResidual`, in which the certificate is
  required to contain the whole cross-over set.  Both directions are one-line applications of the
  lemma above; `JSP90.erdos73On_one_two_of_crossPairResidual` then gives the sharp `Erdős73On 1 2`;
* **`JSP90.crossPairResidual_iff_low_iff`** — the forced residual **splits into exactly two
  independent statements**, one per value of the cross-over count:
  * `JSP90.LowCrossResidual` — the `|crossOverSet| ≠ 2` case (measured: `612 510` cycles with no
    cross-over point and `650 970` with exactly one, all with 0 failures);
  * **`JSP90.TwoCrossTransversal` — THE FORCED CERTIFICATE**: `|crossOverSet G C| = 2` makes the two
    cross-over points themselves meet every odd cycle, so **there is no existential left**
    (`r139.c` `Q5` and `r139b.c` `R1`: 0 failures in `5 040` cases);
  * `JSP90.crossPairResidual_of_three` also gives the three-way split by `0 / 1 / 2` cross-over
    points, `JSP90.NoCrossPairResidual` and `JSP90.OneCrossPairResidual`;
* **`JSP90.closeToBipartite_two_of_subset_crossOverSet`** — **a new instance of the headline
  theorem**: a pair of attachment points containing the cross-over set and meeting every odd cycle
  which meets the attachment points in two points gives `CloseToBipartite 2 G`, for every `k`
  satisfying the packing condition, the certificate lying on the shortest odd cycle;
* **`JSP90.TriangleCrossResidual` and `JSP90.erdos73On_one_two_of_triangleCrossResidual` — a second,
  tighter residual in NEGATIVE form, and a new instance of the headline theorem.**
  `TriangleCrossResidual` says that at `LocIndep 1` the three vertices of a shortest odd triangle do
  not all carry a cross-over; it is a statement about a *configuration that does not occur* (measured
  **0 times** for `n ≤ 7`, and **0 times** among the `2 503 867` graphs with `LocIndep 1` on `n = 8`
  that contain a triangle), and it gives `Erdős #73` at `k = 1` with the optimal constant `2` **for the
  class of graphs whose shortest odd cycles are triangles** (a class given by a property of the odd
  cycles alone: odd girth `3`);
* **`JSP90.inter_ne_of_crossOverPoint_pair`** — the two cross-over cycles at two distinct points of `C`
  must meet (they are odd cycles, and `LocIndep 1` bounds the packing number by one), which is what
  makes the triangle configuration tight;
* `JSP90.exists_pair_of_hitsOddCycles_attachPoints_sdiff` — round 138's erase-one construction read
  off in forced form;
* four numerical helpers (`card_sdiff_singleton_of_mem`, `two_le_card_sdiff_singleton_of_card_ge_three`,
  `card_le_two_sdiff_singleton_of_card_le_three`, `exists_third_of_card_eq_three_mem_pair`).

### Measurements this round (`discovery/JSP-000090/r139.c`, `r139b.c`, `r139c.c`, `r139d.c`, `r139e.c`)

Over the `986 787` graphs with `LocIndep 1` on `n ≤ 7` vertices (`1 268 520` shortest odd cycles with
`3 ≤ |attachPoints G C|`, of which `5 040` have `4 ≤ |attachPoints G C|`):

| question | statement | result |
| --- | --- | --- |
| `Q1` | `|attachPoints G C| ≤ |C|` | 0 failures |
| `Q3` | a *prescribed* non-cross-over point of `A` completes to a certificate | **5 040 failures** — rules out that shape |
| `Q4` | for `4 ≤ |A|` a certificate made of two *non-cross-over* points | 0 failures (vacuous: all such cases have `X = ∅`) |
| `Q5` | `|X| = 2 ⟹ X` is a transversal | **0 failures**, `5 040` cases, all with `|A| = 3` |
| `Q6` | `4 ≤ |A| ⟹ A ∖ {b}` is a transversal for *every* `b ∈ A` | 0 failures |
| `Q7`,`Q9` | a shortest triangle all of whose vertices are cross-over points | **0** for `n ≤ 7` and **0** among the `2 503 867` `LocIndep-1` graphs on `n = 8` containing a triangle |
| `Q8` | `|A| ≤ 2 · |fan|`, and `3 ≤ |A| ⟹ ≥ 2` fan vertices | 0 failures |
| `r139b` | the split by cross-over count: `612 510` / `650 970` / `5 040` / `0` | **0 failures** everywhere |
| **`S1`** | **a transversal pair inside `A` contains `crossOverSet G C`** | **0 failures in `3 157 110` pairs** |
| `S2` | the same with a pair merely *meeting* `A` | `1 099 680` failures |
| `S5` | the same at `|A| ≤ 2` with arbitrary pairs | `1 160 160` failures |
| `r139e` | a shortest cycle with `3 ≤ |A|` and no 2-element transversal inside `A` | **0** occurrences |

### What is *not* proved

`JSP90.LowCrossResidual`, `JSP90.TwoCrossTransversal` and `JSP90.TriangleCrossResidual` — the remaining
statements — and behind them `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the
unchanged primary blocker.  `jsp_000090_main` is deliberately **not** declared, so that the harness
keeps reporting `missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

### Toolchain notes (they cost most of the round)

* `Finset.nonempty_iff_ne_empty` at the pinned revision is `(s = ∅ → False) ↔ s.Nonempty`, so `.mp`
  produces `≠ ∅` and `.mpr` produces `Nonempty`; `Finset.card_pos.mpr` consumes a `Nonempty`.
* `a - b` is opaque to `omega`; the step `3 ≤ n - 1` needs the equation `heq : n - 1 + 1 = n`
  (`Nat.sub_add_cancel (by omega : 0 < n)`) *as a hypothesis*, after which the goal `2 ≤ n - 1` is
  linear in the atom `n - 1`.
* `2 ≤ n - 1` is **false** for `n = 2`: erasing one element of a two-element set leaves one element, so
  the helper needs `3 ≤ n.card`, not `2 ≤ n.card`.
* `Finset.inter_eq_self.mpr` does not exist at this revision; use `Finset.card_sdiff_of_subset` with an
  explicit `{x} ⊆ S` proof, or the `ext` + `simp only [Finset.mem_inter, Finset.mem_singleton]` dance.
* `rcases Finset.mem_insert.mp hz with rfl | rfl` fails on a three-element set (dependent
  `Decidable.rec` elimination on `List.Mem.head`); peel with `rcases Finset.mem_insert.mp hz with hz | hz`
  and `rw [hz]` instead, and use `Finset.mem_singleton.mp` for the last component.
* `(mem_attachPoints.mp ha).2.1` is rejected ("projections extract constructor fields for
  one-constructor inductive types") because `a ∈ attachPoints G C` is a `Quot.lift`; route every such
  projection through `mem_attachPoints.mp` / `mem_crossOverSet.mp`.
* `decide` and `simp` cannot settle `Fin` numeral equations in a file with a classical `DecidableEq`;
  the new `crossOverSet` therefore gets an explicit
  `local instance crossPairDecidable (C) : DecidablePred (CrossOverPoint G C) :=
  fun _ => Classical.propDecidable _`.

## Round 140 (`lean/JSPProblem/Tau.lean`, attack family 69) — **the odd cycle transversal number
`τ_odd`: exact additivity, the exact accounting at cuts, and the budget-split form of Erdős #73**

Every constant in the development so far has been stated as `CloseToBipartite m G`, i.e. as a
one-sided statement about a number `m`.  This round introduces the object the conclusion of
Erdős #73 actually talks about — the **odd cycle transversal number** `JSP90.tauOdd G = min {|Z| :
Z meets every odd cycle of G}` — and 47 declarations (0 `sorry`/`admit`, `lake build` OK, 1292 jobs).

| result | content |
| --- | --- |
| **`JSP90.tauOdd`, `tauOdd_spec`, `tauOdd_le`, `tauOddMin`** | the minimum exists, is attained, and every transversal is at least it (`Nat.find` on cardinalities; the minimum is packaged as a `Subtype` because an `∃` in `Prop` cannot be projected) |
| **`JSP90.closeToBipartite_iff_tauOdd_le : CloseToBipartite m G ↔ tauOdd G ≤ m`** | **the conclusion of Erdős #73 IS a bound on `τ_odd`** |
| **`JSP90.maxDef_le_tauOdd : MaxDef G ≤ tauOdd G`**, **`tauOdd_zero_iff : tauOdd G = 0 ↔ G.IsBipartite`** | Erdős's hypothesis is a lower bound on `τ_odd`; bipartiteness is `τ_odd = 0` |
| **`JSP90.tauOdd_anticover_add : tauOdd G = ∑ X ∈ 𝒬, tauOdd (G[X])`** | **`τ_odd` is EXACTLY additive over an anticomplete cover** — the converse direction round 105's `closeToBipartite_iff_cost_cover` explicitly did not have (there the pieces only *pay jointly*, `∑ c X ≤ m`) |
| `tauOdd_eq_of_two_covers`, `tauOdd_induceFinset_le` | the number is a function of the vertex set only, and is monotone in the vertex set |
| **`JSP90.tauOdd_induceFinset_add : tauOdd G = tauOdd G[A] + tauOdd G[B]`** over `Anticover G A B` | the two-piece form (no `Finset` sum, so the degenerate `A = B` case needs no split) |
| **`JSP90.tauOdd_le_sum_onePieces`** | **at a 1-cut, `τ_odd` adds over the PIECES with NO `+1`, each piece charged its own minimum** — against the uniform `m * t` of `JSPProblem/Piece.lean` |
| **`JSP90.tauOdd_ge_sum_parts`**, **`tauOdd_onePiece_le`**, **`tauOdd_oneSplit_interval`** | `∑ τ_odd T_i ≤ τ_odd G ≤ ∑ τ_odd T_i + t`: **`τ_odd` is within the number of parts of the sum over the parts** |
| `tauOdd_eq_onePiece_of_bipartite_pieces` | round 110's one-sided 1-cut reduction as an equality of numbers |
| **`JSP90.tauOdd_le_add_two_of_vertexSplit`** | at a **2-cut** the error is `+2`, the sharp form of the `2 + m * t` of `JSPProblem/CutVertex.lean` |
| **`JSP90.erdos73On_of_anticoverCover_of_pieceDeficit`** | **THE MASTER REDUCTION: Erdős #73 for `G` follows from Erdős #73 for the pieces, each piece at every parameter up to ITS OWN deficiency, with the constants added up** |
| **`JSP90.erdos73On_of_anticoverCover_of_piecePacking`** | the same in the Erdős–Pósa shape — *Erdős–Pósa splits over an anticomplete cover* |
| `erdos73On_of_anticoverCover_of_maxDef`, **`erdos73On_of_anticoverCover_of_bounded_pieceGirth`** (new instance, odd girth `≤ ℓ X` **per piece**), `erdos73On_of_anticoverCover_of_bounded_girth` | round 105 recovered; a per-piece odd-girth instance with constants `ℓ X * MaxDef (G[X])`; the classical `ℓ * k` back |
| **`JSP90.closeToBipartite_of_anticover_two_of_maxDef`, `erdos73On_of_anticover_two`** | **the two budgets split as well**: `MaxDef G[A] ≤ k₁`, `MaxDef G[B] ≤ k₂` and Erdős #73 at `k₁`/`k₂` give Erdős #73 at `k₁ + k₂` with constant `m₁ + m₂` |
| **`JSP90.tauOdd_p9Family : tauOdd (p9Family k) = 2 * k`** | round 76's lower bound `f(k) ≥ 2k` as a number |
| **`JSP90.tauOdd_wf : tauOdd wf = 1`**, `tauOdd_wf_piece_0/1 = 1`, **`JSP90.not_tauOdd_additive_oneSplit`** | **MACHINE-CHECKED OBSTRUCTION: the exactness of Part 2 does NOT extend to cuts.**  On the windmill the transversal number is `1` while the two non-bipartite pieces of its 1-cut cost `1` each, so the pieces over-count by the shared cut vertex — which is why the `+2` at a 2-cut cannot be removed |

The exact value of `τ_odd` at the two windmill pieces is obtained by the **transversal** route rather
than the clique route (`{1}` and `{3}` are transversals because an odd cycle of a three-vertex piece
*is* the piece); see the toolchain notes below for why the clique route is blocked.

### What is *not* proved

`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) and hence `jsp_000090_main`: this file
gives exact arithmetic for `τ_odd`, not a bound on it in terms of `k`.  `jsp_000090_main` is
deliberately **not** declared, so the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`;
`score.py --strict-prize` reports `build_ok = true, sorry = 0, admit = 0, partial_ok = true`,
`prize_ready = false`.  `formalization.yaml` remains `status: wip`, `prize_ready: false`.
No award claim is made.

### Toolchain notes (they cost most of the round)

* `Nat.find` searches `ℕ`, so `tauOdd` must be defined on a predicate of *cardinalities*
  (`p := fun n => ∃ Z, HitsOddCycles G Z ∧ Z.card ≤ n`), and the `DecidablePred` instance for that
  predicate must be a `local instance` (it is needed by `Nat.find_spec`/`Nat.find_min'` too).  With
  only the expected type `ℕ` there is nothing to determine `p` from, and instance resolution dies
  with "`Fintype ?m` is stuck".
* An `∃` in `Prop` is squashed: `.1`/`.2` are **not** available on `tauOdd_spec`'s statement.  Package
  the witness as a `Subtype` (`tauOddMin`) and keep `obtain` of an `∃` inside proofs.
* `∅` is **not** a transversal (`HitsOddCycles G ∅` is false).  The witness for `tauOdd_zero_iff`'s
  backward direction is `Finset.univ`; for `τ ≥ 1` use `tauOdd_zero_iff` plus non-bipartiteness,
  never an explicit `HitsOddCycles G ∅`.
* `Finset.nonempty_iff_ne_empty` is `s ≠ ∅ ↔ s.Nonempty`, so **`.mpr`** goes `≠ ∅ → Nonempty`;
  `.mp` goes the other way.  `Finset.Subset.card_le_card` is one-way; the converse is
  `Finset.eq_of_subset_of_card_le : s ⊆ t → t.card ≤ s.card → s = t` (it returns `s = t` with `s`
  the *subset* — no `.symm`).  `Finset.card_union_le s t` takes both finsets explicitly.
* **The `DecidableEq` trap that blocked a whole route.**  The `Finset`s of `JSPProblem/Windmill.lean`
  and `JSPProblem/Piece.lean` were elaborated with Mathlib's computable `instDecidableEqFin`, while
  a file-local classical `DecidableEq V` wins for *most* literals but not all, so
  `insert 0 (wfPiece 0)` and `({0, 1, 2} : Finset (Fin 6))` can be two syntactically different
  finsets of the same vertex set.  The *equality* between them is provable (`rw [insert_0_wfPiece_0]`
  closes it), but passing a term whose *type* mentions one where the other is expected fails with
  "synthesized instance is not definitionally equal to expression inferred by typing rules".  Since
  `SimpleGraph.IsClique` is stated on a **`Set`**, even `wf.IsClique ({0,1,2} : Finset (Fin 6))` is
  out of reach this way, and lowering the priority of the classical instance (`attribute [instance
  2000]`) breaks the generic parts of the file with kernel errors.  Work-around used here: the
  transversal route instead of the clique route.

## Round 141 (`lean/JSPProblem/CrossThree.lean`, attack family 70) — **the sharp case `k = 1` is
classified: the residual is ONE configuration**, and the first accounting at three cross-over points

Attack family 70.  Rounds 136–139 built the attachment-point axis of a shortest odd cycle `C`: the
attachment points `A = attachPoints G C` are an odd-cycle transversal (136); an odd cycle meets them in
one point exactly when it crosses `C` over in one point, and **erasing one attachment point which is
not a cross-over point leaves a transversal** (137/138); a two-element certificate lying on `C$ is
*forced* to contain the cross-over set `X = crossOverSet G C` (139).  What round 139 could not do is
decide the sharp case at `|A| = 3`, where the certificate must be `{x, a}$ with `x$ a cross-over
point, and where — if *every* attachment point is a cross-over point — no pair on `C$ works at all.

This round changes method: instead of hunting for certificates it **turns the residual into an
equivalence**, so that what is left is a single named object.

### Part 1 — the counting lemma

* **`JSP90.two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle`** — an independent set
  *contained in* an odd cycle satisfies `2 |S| + 1 ≤ |C|` (`α(C_m) ≤ ⌊m/2⌋`), the side condition of
  `JSP90.indep_card_le_of_odd_cycle` (`JSPProblem/OddCycle.lean`) discharged by `S ⊆ C`; the
  development only had the form with `S` given as an intersection;
  **`JSP90.card_le_one_of_isIndepSet_sub_of_card_C_eq_three`** is its `|C| = 3` case.

### Part 2 — **the classification at `|A| = 3`** (the round's central result)

* **`JSP90.attachThreeResidualRefined_iff_of_card_attachPoints_eq_three`**:

  ```lean
  PackingNumberOne G → C a shortest odd cycle → |attachPoints G C| = 3 →
    ((∃ a b, a ≠ b ∧ a, b ∈ attachPoints G C ∧ HitsOddCycles G {a, b})
       ↔ attachPoints G C ≠ crossOverSet G C)
  ```

  `⇐`: pick `b ∈ attachPoints G C \ crossOverSet G C` — nonempty because `crossOverSet ⊆ attachPoints`
  and the two finsets differ — erase it (round 138), and the residue has exactly `3 − 1 = 2`
  elements, so it *is* the sharp certificate of round 137's residual;
  `⇒`: a two-element certificate of `C$ contains `X$ (round 139), so `|X| ≤ 2 < 3 = |A|`.

* **`JSP90.hitsOddCycles_pair_of_card_attachPoints_eq_three_of_ne_crossOverSet`** — the certificate
  **exhibited as a named pair** (`attachPoints G C \ {b} = {a, a'}$);
* **`JSP90.hitsOddCycles_crossOverSet_of_card_crossOverSet_eq_two_of_card_attachPoints_eq_three`** —
  round 139's `JSP90.TwoCrossTransversal` under the necessary hypothesis `|A| = 3`: with two cross-over
  points the **cross-over set itself** is the transversal;
* **`JSP90.not_hitsOddCycles_pair_of_mem_of_card_attachPoints_eq_three_of_eq_crossOverSet`** — the
  negative half: in the remaining configuration no two-element subset of `A$ (hence none of `C$) is a
  transversal, so the certificate must come from *outside* `C$.

### Part 3 — new instances of the headline theorem

* **`JSP90.erdos73On_one_two_of_card_attachPoints_le_three_of_ne_crossOverSet`** — Erdős #73 at `k = 1`
  with the **optimal constant `2`**, for every shortest odd cycle with at most three attachment points
  and not all of them cross-over points: no bound on `|C|`, no odd-girth hypothesis, no packing
  weight, no branch vertices.  This *strictly generalises* round 139's
  `erdos73On_one_two_of_triangleCrossResidual` (which needed `|C| = 3`);
* **`JSP90.erdos73On_one_two_of_triangleCrossResidual'`** — the same conclusion from round 139's
  triangle residual, with the certificate exhibited as `attachPoints G C \ {x}`;
* **`JSP90.AllCrossResidual`** (the last residual: every attachment point of a shortest odd cycle with
  three attachment points is a cross-over point), **`JSP90.SmallAttachResidual`** and
  **`JSP90.erdos73On_one_two_of_maxCardAttach_three`** — a *class* instance: every graph all of whose
  shortest odd cycles have at most three attachment points is `2`-close to bipartite at `LocIndep 1`.

### Part 4 — **the accounting at three cross-over points**

* **`JSP90.le_card_add_two_mul_card_inter_of_three_crossOverPoints`** — if `c₁, c₂, c₃` are cross-over
  points of `C` with witnesses `D₁, D₂, D₃` (so `C ∩ Dᵢ = {cᵢ}`) and `S` is an independent set
  contained in `C ∪ ⋃ᵢ (Dᵢ \ C)`, then

  ```lean
  2 * |S| + 2 * |S ∩ {c₁, c₂, c₃}|  ≤  |C| - 1 + (|D₁| - 1) + (|D₂| - 1) + (|D₃| - 1)
  ```

  the three-line count being that `Dᵢ = (Dᵢ \ C) ⊔ {cᵢ}`, so `S ∩ Dᵢ` splits as
  `(S ∩ (Dᵢ \ C)) ⊔ (S ∩ {cᵢ})` and Part 1 prices it at `(|Dᵢ| - 1)/2`, **minus one** whenever
  `cᵢ ∈ S`.  No hypothesis on `LocIndep`, on the minimality of `C$ or on `|C|`;
* **`JSP90.le_card_union_tails_add_two_mul_card_inter_of_three_crossOverPoints`** — with `LocIndep 1`
  applied to `W = C ∪ ⋃ᵢ (Dᵢ \ C)`: **`|⋃ᵢ (Dᵢ \ C)| + 2 |S ∩ {c₁, c₂, c₃}| ≤ Σᵢ (|Dᵢ| - 1)`**, i.e. the
  three tails must overlap by at least twice the number of cross-over points met.

### Measurements (`discovery/JSP-000090/r141.c`, all `986 787` graphs with `LocIndep 1` on `n ≤ 7`)

`1 268 520` shortest odd cycles with `≥ 3` attachment points, of which `1 263 480` have `|A| = 3` and
`5 040` have `|A| ≥ 4`:

| question | statement | result |
| --- | --- | --- |
| `T1` | `|A| = 3` and `X = A` (the last residual) | **0** occurrences; histogram of `|X|`: `0: 607 470`, `1: 650 970`, `2: 5 040`, `3: 0` |
| `T2` | `|A| = 3`, `|X| = 2` ⇒ `X` is a transversal | **0** failures (5 040 cases) |
| `T3` | `|A| ≥ 4` and `X = A` | **0** |
| `T4` | `|A| ≥ 4` ⇒ some pair of `A$ is a transversal | **0** failures (5 040 cases) |
| `T5` | `|A| = 3`, `X ≠ A` ⇒ the exhibited `A \ {b}$ is a transversal | **0** failures |
| `T6` | the new **iff** (`pair exists` vs `X ≠ A$) | **0** failures |
| `T7` | `|A| ≥ 4`, `X ≠ A$ ⇒ `A \ {b}$ is a transversal | **0** failures |
| `T8` | the accounting lemma | **not exercised** — `|X| ≥ 3` never occurs at `LocIndep 1` for `n ≤ 7`, so the lemma is vacuous in the measured range |

### What is *not* proved

`JSP90.AllCrossResidual`, the cases `|attachPoints G C| ≥ 4` of `JSP90.AttachThreeResidualRefined`, and
behind them `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary
blocker.  Note that the counting route to `AllCrossResidual` is **tight**: at `LocIndep 1` the three
cross-over cycles pairwise meet (`JSP90.inter_ne_of_crossOverPoint_pair`), the overlap of the three
tails is at least `2`, and the independent-set count reaches exactly the size `LocIndep 1` demands, so
no contradiction follows from `LocIndep 1` alone.  `jsp_000090_main` is deliberately **not** declared,
so the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize`
reports `build_ok = true, sorry = 0, admit = 0, partial_ok = true`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 142 (`lean/JSPProblem/FanCount.lean`, attack family 71) — **the FAN ACCOUNTING, the PAIRING of
four attachment points, and the SIX-TRACES classification of the failure at `|A| = 4`**

Attack family 71, following `policy.json`'s `next_bet` route (A) — *"count on the fan"*.  Rounds 136–141
built the attachment-point axis of a shortest odd cycle `C`; round 141 left the
`|attachPoints G C| ≥ 4` half of `JSP90.AttachThreeResidualRefined` (`JSPProblem/Segment.lean`)
**completely untouched** — the largest untouched part of the sharp case `k = 1`.  With
`A = attachPoints G C` and `B = boundary G C` (the fan), one new file (**20 declarations, 0
sorry/admit**, `lake build` OK with **1294 jobs**, axiom report clean: `propext, Classical.choice,
Quot.sound` only), imported from the root module `JSPProblem.lean`.

### Part 1 — the fan accounting (`policy.json` `next_bet` route (A))

* **`JSP90.card_attachPoints_le_sum_attachSet`** — the attachment points are priced by the attachment
  sets of the fan (`attachPoints G C = ⋃ y ∈ B, attachSet G C y`);
* **`JSP90.card_attachPoints_le_two_mul_card_boundary` — THE FAN ACCOUNTING: `|A| ≤ 2 |B|`** at
  `LocIndep 1` for a shortest odd cycle.  This is the statement `discovery/JSP-000090/r139.c` measured
  as `Q8` and round 139 could not formalise; `discovery/JSP-000090/r142.c` (`F1`) re-measures it with
  **0 failures in 2 163 652** shortest odd cycles, of which `29 052` attain `|A| = 2|B|`;
* five corollaries — `two_le_card_boundary_of_card_attachPoints_ge_three`,
  `…_ge_four`, `three_le_card_boundary_of_card_attachPoints_ge_five`,
  `card_attachPoints_le_four_of_card_boundary_le_two`, `card_attachPoints_le_two_of_card_boundary_le_one`
  — the first **lower** bounds on the fan in the development: three (four, five) attachment points force
  a fan of two (two, three) vertices.

### Part 2 — the pairing of four attachment points

* **`JSP90.exists_attachSet_pair_of_card_attachPoints_eq_four_of_card_boundary_eq_two` — THE PAIRING**:
  `LocIndep 1`, `|A| = 4` and `|B| = 2` force `∃ y₁ ≠ y₂ ∈ B` with

  ```lean
  |attachSet G C y₁| = |attachSet G C y₂| = 2 ∧ Disjoint (attachSet G C y₁) (attachSet G C y₂)
    ∧ attachSet G C y₁ ∪ attachSet G C y₂ = attachPoints G C
  ```

  Every inequality of the count `4 = |A| ≤ |A₁ ∪ A₂| ≤ |A₁| + |A₂| ≤ 2 + 2` is an equality, and
  `Finset.card_union_add_card_inter` makes the two attachment sets disjoint.  Measured as `F6`:
  **0 failures in the 5 040** measured cases, which all have `|B| = 2`.

### Part 3 — the six-traces classification of the failure at `|A| = 4`

* **`JSP90.not_pair_transversal_iff_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver` — THE
  SIX-TRACES THEOREM.**  At packing number one, for a shortest odd cycle `C` with
  `|attachPoints G C| = 4` and no cross-over, as an `iff`:

  ```lean
  (no two-element subset of A meets every odd cycle of G)
    ↔ (for every two distinct p q ∈ A there is an odd cycle D with D ∩ A = A \ {p, q})
  ```

  On a four-element ground set this is the *complete* classification of the failure: a pair fails iff
  the complementary pair occurs as the trace of an odd cycle, so "no pair works" iff **all six**
  complementary pairs occur.  ⟸ is one line (`{p, q} ⊆ A`); ⟹ uses round 137's
  `two_le_card_attachPoints_inter_of_noCrossOver_of_packing_one` to price `D ∩ A` at `2` and
  `|A \ {p, q}| = 4 − 2 = 2`.  Measured as `F3`: **0 failures in the 5 040** measured cases.
* **`JSP90.exists_trace_or_crossOverPoint_of_pair_not_transversal_of_card_attachPoints_eq_four`** — the
  same content **without** the no-cross-over hypothesis: a failing pair is witnessed either by a cycle
  whose trace on `A` is exactly the complementary pair, or by a cross-over point of `C` **outside**
  `{p, q}`.  This is the forced shape of the whole `|A| ≥ 4` residual — the only obstruction is the
  cross-over, as in round 139.
* Helpers `mem_pair_iff`, `card_pair_of_mem_attachPoints`,
  `exists_oddCycle_avoid_pair_of_not_hitsOddCycles_pair`,
  `ne_of_oddCycle_avoid_pair_sub_attachPoints`.

### Part 4 — the sharp case `k = 1` is three named statements

* **`JSP90.AttachFourResidual`** — the `4 ≤ |A|` half of round 137's refined residual;
* **`JSP90.NoSixTraces`** — the **negative form** of the `|A| = 4` half: at `LocIndep 1` the six-traces
  configuration never occurs (a statement about a configuration that does not occur, of the same shape
  as round 139's `JSP90.TriangleCrossResidual`);
* **`JSP90.erdos73On_one_two_of_allCrossResidual_and_attachFourResidual`** — with round 141's
  `AllCrossResidual` (the `|A| = 3` half) this gives the **sharp** `Erdős73On 1 2`, the optimal
  constant `2`, so the whole sharp case `k = 1` is reduced to three named configurations, one of them
  in negative form;
* **`JSP90.allCrossResidual_of_erdos73On_one_two`**, **`JSP90.attachFourResidual_of_attachThreeResidualRefined`**,
  **`JSP90.exists_pair_of_not_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver`**.

### Measurements (`discovery/JSP-000090/r142.c`, all `986 787` graphs with `LocIndep 1` on `n ≤ 7`)

`2 163 652` shortest odd cycles examined; `5 040` of them have `|A| = 4` (all with `|B| = 2`):

| question | statement | result |
| --- | --- | --- |
| `F1` | `|A| > 2|B|` (the fan accounting) | **0** failures; `29 052` cases with `|A| = 2|B|` |
| `F3` | the six-traces `iff` at `|A| = 4`, `X = ∅` | **0** failures (5 040 cases) |
| `F4` | `|A| = 4`: some pair of `A` is a transversal | **0** failures |
| `F6` | `|A| = 4`, `|B| = 2`: the two attachment sets are disjoint pairs | **0** failures (5 040 / 5 040) |
| `F7` | `|A| = 4`, `|B| = 2`: some transversal pair of `A` meets **both** attachment sets | **0** failures; histogram of such pairs `3: 2520`, `4: 2520` — the `next_bet` prediction, confirmed |
| histogram | `|A| × |B|` | `|A| ≤ 2` with `|B| ≤ 4`; `|A| = 3` with `|B| = 2, 3, 4`; `|A| = 4` only with `|B| = 2` |

### What is *not* proved

`JSP90.AllCrossResidual`, `JSP90.NoSixTraces`, `JSP90.AttachFourResidual` — and behind them
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.  The
`F7` measurement says the `|A| = 4` certificate is always a *balanced* pair (one point from each
attachment set), which is stronger than `AttachFourResidual` and is the next formal target;
nothing yet proves that the six-traces configuration cannot occur.  `jsp_000090_main` is deliberately
**not** declared, so the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`;
`score.py --strict-prize` reports `build_ok = true, sorry = 0, admit = 0, partial_ok = true`.
`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.

---

## Round 144 — `lean/JSPProblem/TraceComplex.lean` (new file): **the TRACE COMPLEX of a shortest odd
cycle, and the sharp case reduced to TWO named statements**

Attack family 72.  Rounds 136–143 attacked the sharp case `Erdős73On 1 2` through the attachment
points `A = attachPoints G C` and the fan `B = boundary G C`; round 142 introduced the "traces"
`D ∩ A` one at a time.  Round 144 replaces that ad-hoc language by **one object**

```lean
JSP90.traceFamily G C  =  { D ∩ attachPoints G C  :  D  an odd cycle of G }
```

(the *trace complex* of `C`; the two-element members, the *edges of the trace graph*, are collected
separately as `JSP90.tracePairs : Finset (Finset V)`), and proves that every question the development
asks about transversals at a shortest odd cycle is a question about this one family.

### Part 1 — the trace complex (`JSP90.traceFamily`, `JSP90.mem_traceFamily`)

* `subset_traceFamily_attachPoints`, `inter_attachPoints_mem_traceFamily`,
  `attachPoints_mem_traceFamily` — every trace lies in the attachment points; the trace of `C` is `A`;
* `ne_empty_of_inter_attachPoints_of_packing_one` — at packing number one every trace of an odd cycle
  `D ≠ C` is nonempty (this is what rules out singleton traces in Part 3);
* `exists_oddCycle_avoid_of_not_hitsOddCycles`, `hitsOddCycles_of_inter_empty`,
  `exists_oddCycle_avoid_of_inter_traceFamily` — the odd cycles of `G` are accounted for by their
  traces: **a trace disjoint from `X` is witnessed by an odd cycle avoiding `X`**.

### Part 2 — the cover–transversal duality

* **`JSP90.hitsOddCycles_iff_covers_traceFamily`** — if every odd cycle `D ≠ C` meets the attachment
  points (which is exactly what `PackingNumberOne` gives for a shortest odd cycle), then for
  `X ⊆ attachPoints G C`, `X ≠ ∅`,

  ```lean
  (X meets every odd cycle of G)  ↔  (X meets every trace of C)
  ```

  No Erdős hypothesis, no fan, no cross-over analysis.  `JSP90.hitsOddCycles_iff_covers_traceFamily_of_packing_one`
  is the packing-number-one form used below.
* `JSP90.not_hitsOddCycles_pair_iff_exists_trace_disjoint` — a **failing pair** of attachment points
  is witnessed by a trace disjoint from it.
* `JSP90.tracePairs` / `JSP90.mem_tracePairs` — the two-element traces.

### Part 3 — the sharp case is TWO named statements

* **`JSP90.not_hitsOddCycles_iff_exists_trace_subset_complement`** — the general form: a pair
  `Q ⊆ A` fails to be a transversal **iff some trace lies inside `A \ Q`**.
* **`JSP90.not_hitsOddCycles_iff_exists_trace_eq_complement_of_card_attachPoints_eq_three`** — at
  `|A| = 3` the complement has **one** element, so the trace **is** the complementary singleton; **no
  `NoCrossOver` hypothesis is needed**.  Hence
  **`JSP90.not_cover_le_two_iff_threeSingletons_of_card_attachPoints_eq_three`**: the sharp case fails
  at `|A| = 3` **iff all three attachment points are singleton traces**
  (`JSP90.ThreeSingletonTraces`) — the trace-complex form of round 141's cross-over configuration,
  with its instance-level corollaries `exists_cover_le_two_of_card_attachPoints_eq_three_of_noSingletonTraces`
  and `hitsOddCycles_pair_of_card_attachPoints_eq_three_of_noSingletonTraces` (the latter strengthening
  round 141's `∃` to `∀`: with no singleton trace **every** pair of attachment points is a transversal).
* **`JSP90.not_hitsOddCycles_iff_mem_tracePair_of_card_attachPoints_eq_four_of_noCrossOver`** and
  **`JSP90.not_cover_le_two_iff_sixTraces_of_card_attachPoints_eq_four_of_noCrossOver`** (`JSP90.TraceK4`) —
  the same at `|A| = 4` under `NoCrossOver`: the failing pairs are exactly the complements of the edges
  of the trace graph, so the sharp case fails **iff** the six-traces configuration occurs.  The
  `NoCrossOver` hypothesis **is** needed here and round 144's measurement `r144c` `U2` shows why: at
  `LocIndep 1` two odd cycles may meet in **three or four** points (55 800 cases), so the counting
  `|A \ Q| = 2` alone does not make the trace two-element.  Round 142's theorem is therefore *not*
  superseded; it is re-proved here in the trace language.
* **`JSP90.TraceCoverResidual`** — the whole `3 ≤ |A|` half of the sharp case as ONE statement ("the
  trace complex of `C` has a cover of size `≤ 2` inside `A`"), and
  **`JSP90.erdos73On_one_two_of_allCrossResidual_and_traceCoverResidual`** — the sharp case
  `Erdős73On 1 2` follows from round 141's `AllCrossResidual` together with this one statement, so the
  residual is **two** named statements (down from round 142's three), one of them in negative form
  (`JSP90.NoTraceK4`, `JSP90.NoThreeSingletonTraces`).
  `JSP90.attachFourResidual_of_traceCoverResidual` (new statement ⇒ round 142's) and
  `JSP90.traceCoverResidual_of_attachThreeResidualRefined` (round 137's ⇒ new statement) locate it
  exactly between rounds 137 and 142.
* **`JSP90.exists_cover_le_two_of_card_attachPoints_eq_four_of_oneTracePair`** — a *sharper* target
  than `NoTraceK4`: at `|A| = 4` it suffices that the trace graph has at most **one** edge
  (`JSP90.OneTracePair`).

### Measurements (`discovery/JSP-000090/r144.c`, `r144b.c`, `r144c.c`)

| question | statement | result |
| --- | --- | --- |
| `T1` | traces of size `≥ 3` | 27 720 occur, so `NoCrossOver` alone does **not** bound the traces |
| `T3` | `\|A\| = 4`: "no transversal pair" `↔` "trace graph `= K₄`" | **0** violations in 5 040 cases |
| `T4` | `\|A\| = 4`: number of edges of the trace graph | **only 0 or 1** (2 520 each) |
| `T5` | a cover of size `≤ 2` inside `A` always exists | **0** failures in 1 268 520 cases with `\|A\| ≥ 3` |
| `T6` | `\|A\| ≥ 4`: number of transversal pairs of `A` | **5 or 6**, never fewer |
| `T7` | the trace graph `= K₄` | **never**, 0 occurrences |
| `U1` | edges of the trace graph by `\|A\|` | `\|A\|=2`: always 1; `\|A\|=3`: `0,1,2,3`; `\|A\|=4`: `0,1` |
| `U2` | two odd cycles of a `LocIndep`-1 graph meeting in `≥ 3` points | **yes**, 55 800 cases |
| `U7` | `\|A\| ≥ 4`, no one-point cross-over: minimum cover size | **always 1** (5 040 cases) |
| `B` | is there a `LocIndep`-1 graph with `τ_odd ≥ 3`? | **no**: `r144b.c` searches **all** 55 179 262 `LocIndep`-1 graphs on 8 vertices (search complete).  This is round 143's question; its `r143.c` pruned every branch at the root — `τ_odd < 3` is not a sound pruning rule — and was vacuous. |

### What is *not* proved

`JSP90.TraceCoverResidual`, and behind it `JSP90.NoTraceK4`, `JSP90.OneTracePair`,
`JSP90.NoThreeSingletonTraces` and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the
unchanged primary blocker.  `jsp_000090_main` is deliberately **not** declared, so the harness keeps
reporting `missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true`,
`prize_ready = false`.  `formalization.yaml` remains `status: wip`, `prize_ready: false`.
No award claim is made.


---

## Round 145 — `lean/JSPProblem/TraceExit.lean` (new file, attack family 73): **the sharp case `Erdős73On 1 2`
is ONE statement, one-point cross-overs are singleton traces, and the exit step**

New file `lean/JSPProblem/TraceExit.lean` (**16 declarations, 0 sorry/admit**, `lake build` OK with
**1296 jobs**, axiom report clean: `propext, Classical.choice, Quot.sound` only), imported from the root
module `JSPProblem.lean`.

### Part 1 — the residual is ONE statement

`JSP90.TraceCoverResidual` is stated for `3 ≤ |attachPoints G C|`, so it *already* contains the three
attachment point case; round 144 nevertheless used round 141's machinery there because it reused the
`|attachPoints| ≤ 3` branch of the older reduction.  Reorganising the case analysis:

* **`JSP90.erdos73On_one_two_of_traceCoverResidual` — THE SHARP CASE `Erdős73On 1 2` FROM
  `JSP90.TraceCoverResidual` ALONE.**

So the sharp case of Erdős #73 (the optimal constant `f(1) = 2`) is *equivalent to a single statement* —
the trace complex of a shortest odd cycle with at least three attachment points has a cover of size `≤ 2`
inside the attachment points — and round 144's `JSP90.AllCrossResidual` hypothesis is **redundant**.
`JSP90.erdos73On_one_two_of_allCrossResidual_and_traceCoverResidual` (round 144) remains, as the
weaker two-hypothesis version.

### Part 2 — a one-point cross-over is a singleton trace

* **`JSP90.mem_traceFamily_of_onePointCrossOver`**: `OnePointCrossOver G C D → a ∈ C ∩ D →
  ({a} : Finset V) ∈ traceFamily G C`.  Pure set theory (`attachPoints G C ⊆ C` gives
  `D ∩ attachPoints G C ⊆ D ∩ C = {a}`, and round 139's `JSP90.mem_attachPoints_of_onePointCrossOver`
  puts `a` in the attachment points): **no hypothesis at all**, not packing number one and not
  minimality of `C`;
* `JSP90.singletonTrace_of_crossOverPoint`, `JSP90.singletonTrace_of_mem_crossOverSet`,
  **`JSP90.threeSingletonTraces_of_subset_crossOverSet`**,
  `JSP90.threeSingletonTraces_of_eq_crossOverSet`: round 141's cross-over configuration
  `attachPoints G C = crossOverSet G C` **forces** round 144's `JSP90.ThreeSingletonTraces`, so the
  configuration compared by round 141 is *contained in* the one compared by round 144.

### Part 3 — no cross-over is a positive instance of the sharp case

* **`JSP90.eq_empty_crossOverSet_of_noCrossOver`**, `JSP90.not_mem_crossOverSet_of_noCrossOver`,
  `JSP90.not_crossOverPoint_of_noCrossOver` — under `NoCrossOver G C` there are no cross-over points;
* **`JSP90.hitsOddCycles_attachPoints_sdiff_of_noCrossOver`** — round 139's erasure lemma with **no
  exception**: `attachPoints G C \ {b}` is an odd cycle transversal for **every** attachment point `b`;
* **`JSP90.exists_cover_le_two_of_card_attachPoints_eq_three_of_noCrossOver`** — at three attachment
  points and no cross-over the sharp case holds with the **optimal** constant `2`;
* **`JSP90.SmallAttachNoCrossOver` + `JSP90.closeToBipartite_two_of_smallAttach_noCrossOver` +
  `JSP90.erdos73On_one_two_of_smallAttach_noCrossOver` — A NEW INSTANCE OF THE HEADLINE THEOREM**:
  graphs whose shortest odd cycles have at most three attachment points *and* which have no cross-over
  satisfy `Erdős73On 1 2` with the optimal constant `2` — no bound on the odd girth, the packing weight
  or the number of branch vertices, and **no residual statement at all** (rounds 141 and 144 each
  needed one on this class).

### Part 5 — the exit step

* **`JSP90.attachPoints_inter_D_nonempty_of_not_subset_C`** — **`IsOddCycle G D → (C ∩ D).Nonempty →
  ¬ D ⊆ C → (attachPoints G C ∩ D).Nonempty`**: a cycle that meets `C` but is not contained in it
  *leaves* it.  If the nonempty set of positions of the cyclic numbering lying on `C` were closed
  under `cycSucc`, then by induction every `cycSucc^[d] j` would lie on `C`, and since every position
  is a `cycSucc^[d]` of any other (`JSP90.exists_arc`) the whole cycle would lie in `C` — a
  contradiction.  This is the classical *exit step* of the fan argument: the reason every trace
  `D ∩ attachPoints G C` contains the points at which `D` leaves `C`, and the first step of the
  classical proof that both ends of a maximal `C`-chain along `D` are attachment points.

### A mathematical finding recorded in the file header

**The converse of Part 2 is false.**  A *singleton trace* does **not** imply a *one-point cross-over*:
for `C` = a 5-cycle `1-2-3-4-5`, `D` = the triangle `1-2-3` inside it and a pendant vertex `6` at `1`
(a `LocIndep 1` graph), `attachPoints G C = {1}` and `D ∩ attachPoints G C = {1}` is a singleton trace,
but `C ∩ D = {1,2,3}`.  `attachPoints` records where a cycle *leaves* `C`, while a trace only records
the attachment points met: a cycle may enter `C` at a point which is **not** an attachment point (it has
no neighbour outside `C`) and travel inside `C`.  So `ThreeSingletonTraces` is **weaker** than round
141's cross-over configuration, which is exactly what Part 2 proves.

### What is *not* proved

`JSP90.TraceCoverResidual`, and behind it `JSP90.NoTraceK4`, `JSP90.OneTracePair`,
`JSP90.NoThreeSingletonTraces` and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the
unchanged primary blocker.  `jsp_000090_main` is deliberately **not** declared, so the harness keeps
reporting `missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true`, `prize_ready = false`.
`formalization.yaml` remains `status: wip`, `prize_ready: false`.  No award claim is made.

## Round 146 (`lean/JSPProblem/FiniteSharp.lean`, attack family 74) — **THE IN-KERNEL FINITE AXIS: a computable mirror of Erdős #73, and a measured kernel-memory barrier**

New attack family.  Rounds 76–145 measured their finite configurations with **C programs outside
Lean** (`discovery/JSP-000090/r1*.c`); round 146 is the first in which **the Lean kernel itself**
verifies a finite range of Erdős #73, and the first to *measure* why the range is small.

**The mirror (Parts 1–3, 0 sorry/admit).**

* `JSP90.UpTri n` — the **strict upper triangle** of `Fin n × Fin n`; a simple graph on `Fin n` is
  a symmetric loopless `Bool` matrix, so it is presented by a `Bool` function on `UpTri n`, and
  `Fintype (UpTri n → Bool)` enumerates **exactly** the graphs, each once (`JSP90.card_upTri_five :
  Fintype.card (UpTri 5) = 10`, by `decide`, i.e. the `1024` graphs on five vertices);
* `JSP90.adjBU`, `JSP90.adjBU_irrefl`, `JSP90.adjBU_of_lt`, `JSP90.adjBU_of_ge`, **`JSP90.adjBU_comm`**
  (the matrix is symmetric) and `JSP90.graphU` (`Adj v w ↔ adjBU a v w = true`, with the symmetry and
  the irreflexivity proofs);
* `JSP90.exists_upTri_of_graph` — **every** simple graph on `Fin n` is a `graphU`, and
  `JSP90.graphU_eq_of_exists_upTri` transfers a statement about `SimpleGraph (Fin n)` through the
  mirror;
* `JSP90.locIndepB` / `JSP90.closeToBipartiteB` — the two sides of Erdős #73 re-stated over `Bool`
  adjacency so that a `Decidable` instance exists, with the **two bridges**
  **`JSP90.locIndep_of_locIndepB`** and **`JSP90.closeToBipartite_of_closeToBipartiteB`** back to
  `JSPProblem/Definitions.lean` (`JSP90.isBipartite_of_residueBipartiteB` turns a `Bool` two-colouring
  into a `SimpleGraph.Coloring`).

**The pipeline, verified end to end (Parts 4–6).**

* the twelve statements `JSP90.finiteSharp_{one,two,three}_fin{0,1,2,3}` are closed by **`decide`**,
  and `JSP90.erdos73On_one_fin_le` / `_two_fin_le` / `_three_fin_le` carry them through the bridges:
  **`LocIndep k G → CloseToBipartite k G` for every graph on at most three vertices**;
* `JSP90.moveGraph` (the graph moved along a bijection) with
  `JSP90.locIndep_of_locIndep_moveGraph` and `JSP90.closeToBipartite_of_closeToBipartite_moveGraph`
  pulls the statements back to an **arbitrary finite type** along `Fintype.equivFin V`, giving the
  instances `JSP90.erdos73On_one_one_card_le_three`, `JSP90.erdos73On_two_two_card_le_three` and
  `JSP90.erdos73On_three_three_card_le_three` of the headline theorem in the `Erdős73On` form.

**Consequences (Parts 7–8).**

* **`JSP90.exists_hitsOddCycles_singleton_of_locIndep_one_card_le_three`** — at `LocIndep 1` and
  `|V| ≤ 3` a **non-bipartite** graph has a **single vertex meeting every odd cycle**
  (`JSP90.tauOdd_le_one_of_locIndep_one_card_le_three`);
* **`JSP90.optimal_smallOrder`** — the small-order constants are machine-checked **optimal**: for
  every `1 ≤ k ≤ 3` the complete graph `K_{k+2}` satisfies `LocIndep k` and is **not**
  `(k − 1)`-close to bipartite, with the three instances
  `JSP90.not_closeToBipartite_zero_locIndep_one_fin3`,
  `JSP90.not_closeToBipartite_one_locIndep_two_fin4`,
  `JSP90.not_closeToBipartite_two_locIndep_three_fin5`.

**The measured barrier, and the two routes past it.**  The C measurement of round 146
(`discovery/JSP-000090/r146.c`, **all** graphs on `n ≤ 6`) gives `max τ_odd = 1` at `LocIndep 1` for
`n ≤ 5`, and `2` at `n = 6` (120 witnesses) — so **five vertices is the last order at which the
constant `1` suffices and six is the first at which the constant `2` of `JSP90.Erdős73On 1 2` is
needed**.  The kernel cannot follow there: the peak RSS of `lean` on the `decide` statements was
measured at `1.86 GB` (`n = 2`), `1.89 GB` (`n = 3`), **`5.30 GB` (`n = 4`, killed)** and
**`≈ 6 GB` (`n = 5`, killed twice)** — `≈ 55 MB` per graph, caused by the `Finset` quantifiers of the
mirror (every decision re-enumerates `univ.powerset`).  Chunking by the number of edges does **not**
help, because the cost is per *enumerated* candidate, not per *matching* graph.  Two concrete routes:

1. **replace the `Finset` quantifiers of the mirror by `Fin n → Bool` indicator functions** (the
   enumeration becomes `Fintype (Fin n → Bool)`, no powerset), which should bring `n = 6` inside the
   kernel budget;
2. **prove the five-vertex case structurally**: at `LocIndep 1` a shortest odd cycle has length `3`
   or `5`; in the `5`-case it is induced (`JSPProblem/Chord.lean`) and spans the whole vertex set, so
   one deleted vertex leaves a path; in the `3`-case each of the at most two remaining vertices has
   **at most two** neighbours in the triangle (else `LocIndep 1` applied to `C ∪ {x}` fails), and the
   four-vertex case analysis closes it.  The inputs are
   `JSP90.hitsOddCycles_of_isOddCycle_of_locIndep_one`,
   `JSP90.isBipartite_deleteFinset_of_isOddCycle_of_locIndep_one` and
   `JSP90.closeToBipartite_of_isOddCycle_of_locIndep_one` (`JSPProblem/OneK.lean`).

`jsp_000090_main` remains undeclared and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas)
is unchanged: the remaining obstruction is the general, 3-connected case.


---

## Round 148 (`lean/JSPProblem/Five.lean`, 31 declarations, 0 sorry/admit) — the FIVE-VERTEX AXIS:
## `f(1) = 1` on graphs of order ≤ 5, with the **optimal** constant

Round 146 built a *computable mirror* of Erdős #73 and closed the in-kernel range at **three**
vertices with `decide`; it could not decide `|V| ≤ 4` or `|V| ≤ 5` because the kernel memory of
`decide` on `Finset`-quantified graph statements is `≈ 55 MB` per enumerated graph on this machine.
`policy.json` proposed two routes past that barrier, the second being *structural*: prove the
small-order instances by hand, after the reusable small lemma "a graph on at most four vertices with
no triangle is bipartite".

**That lemma is not needed, and the barrier is not the interesting obstacle.**  The development
already has `JSP90.isBipartite_of_no_oddCycle` (`JSPProblem/Transversal.lean`), so "a triangle-free
graph on at most four vertices is bipartite" is not a colouring problem: on at most four vertices an
odd cycle has odd cardinality `≥ 3`, hence cardinality `3`, hence *is* a triangle.  Everything below
is counting on vertex sets, and the whole file builds in seconds with no `decide` and no
`native_decide`.

### What is proved

* **Part 1 — the local structure at a triangle.**
  `JSP90.exists_not_adj_of_notMem_of_isNClique_three`: at `LocIndep 1` **every vertex outside a
  triangle has a non-neighbour in it** (`LocIndep 1` on `T ∪ {x}` gives an independent `2`-set of
  four vertices, a triangle holds at most one element of an independent set, so `x` is in it and the
  other element is a non-neighbour of `x`), and its `Finset` form
  `JSP90.card_adjIn_le_two_of_isNClique_three` for `JSP90.AdjIn G x T` — the neighbours of `x` lying
  in `T`.
* **Part 2 — counting in a three-element set.**  `JSP90.card_inter_pos_of_card_two_of_card_two`
  (two `2`-subsets of a `3`-set which differ as finsets meet),
  `JSP90.exists_mem_T_of_card_le_two` (Lemma A1) and
  `JSP90.card_inter_le_one_and_exists_mem_T` (Lemma A2: the intersection is at most a singleton, and
  a point of `T` lies in both whenever it is a singleton).  All three are about finsets; no graph
  appears in them.
* **Part 3 — the shape of a triangle, and the choice of one vertex.**
  `JSP90.exists_mem_D_shapes`: in a graph whose vertex set is a triangle `T` together with at most
  two further vertices, every triangle is `T` itself, two vertices of `T` plus one further vertex, or
  one vertex of `T` plus both further vertices — the complete classification, with the adjacencies
  that come from the clique.  `JSP90.not_adjIn_eq_card_two_of_locIndep_one` is the `K₄`-exclusion in
  the `AdjIn` vocabulary (two adjacent vertices outside the triangle with the same two neighbours in
  it would form a `K₄` with it), `JSP90.exists_mem_T_setup` chooses the vertex of `T` meeting all
  the triangles, and

  > **`JSP90.exists_common_mem_triangle_of_card_le_five`: at `LocIndep 1`, `|V| ≤ 5` and a triangle
  > `T` of `G`, the triangles of `G` have a common vertex, and it lies in `T`.**

* **Part 4 — the instance.**

  > **`JSP90.closeToBipartite_one_of_locIndep_one_card_le_five`: `LocIndep 1 G → |V| ≤ 5 →
  > CloseToBipartite 1 G`** — a **new instance of the headline theorem with the OPTIMAL constant
  > `1`** on the class of graphs on at most five vertices, with no hypothesis beyond Erdős's own: no
  > odd girth, no packing weight, no degree bound, no bound on the number of branch vertices, no
  > decomposition.  `JSP90.erdos73On_one_one_of_card_le_five` is the `Erdős73On` form, and
  > `JSP90.closeToBipartite_one_of_locIndep_one_card_le_four` the intermediate `|V| ≤ 4` instance.

  The proof is short: a shortest odd cycle of `G` has `3` or `5` vertices; in the `5`-case it spans
  `V`, so every odd cycle of `G` *is* the vertex set; in the `3`-case it is a triangle and Part 3
  gives a single vertex meeting every triangle, while every odd cycle is a triangle.
  `JSP90.hitsOddCycles_of_locIndep_one_card_le_five` exhibits the vertex and
  `JSP90.tauOdd_le_one_of_locIndep_one_card_le_five` is the `τ_odd ≤ 1` form: the deleted vertex *is*
  an odd cycle transversal.
* **Part 5 — optimality.**  `JSP90.optimal_smallOrder_five` and
  `JSP90.not_erdos73On_one_zero_of_card_le_five`: `K₃` is `LocIndep 1` and is not `0`-close to
  bipartite, so no instance at `k = 1` on graphs of order at most five can have constant `0`; the
  constant `1` above is therefore **exact** for the class.

### The measurement that fixes the target (`discovery/JSP-000090/r148.c`, all graphs on `n ≤ 6`)

`MaxDef(G) = max_X |X| − 2α(G[X])` and `τ_odd(G) = min |Z| with G − Z bipartite`, computed exactly:

| `n` | graphs | `max τ_odd` over `MaxDef ≤ 1` | over `≤ 2` | over `≤ 3` | over `≤ 4` |
|---|---|---|---|---|---|
| 3 | 8 | **1** | 1 | 1 | 1 |
| 4 | 64 | **1** | 2 | 2 | 2 |
| 5 | 1024 | **1** | 2 | 3 | 3 |
| 6 | 32768 | **2** | 2 | 3 | 4 |

So `f(1) = 1` at order `≤ 5` — the instance proved above is optimal — and `f(1) = 2` is first needed
at **six** vertices (`120 + ` many witnesses, e.g. the three-sun `sun3`), which is the sharp case
`Erdős73On 1 2` on the class `|V| ≤ 6` and the concrete next target of this axis.  The count of
graphs by `MaxDef` (`n = 6`: 5177 / 19637 / 7782 / 171 / 1) is also recorded: at six vertices there
are `19 637` LocIndep-1 graphs, of which `171` have `MaxDef = 2` and one (`K₆`) has `MaxDef = 4`.

### What is *not* proved

`Erdős73On 1 2` at six vertices and above, and behind it `JSP90.TraceCoverResidual`
(`JSPProblem/TraceComplex.lean`) and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas).
`jsp_000090_main` remains undeclared, so `harness/score.py --strict-prize` keeps reporting
`missing_theorems = ["jsp_000090_main"]`.

---

## Round 150 — `lean/JSPProblem/Seven.lean`: **THE TWO-TRIANGLE EXCLUSION** and the seven-vertex instances built on it

`lake build` succeeds (1300 jobs), with **0 `sorry` and 0 `admit`** in the whole development;
`#print axioms` on every new declaration reports only `[propext, Classical.choice, Quot.sound]`.

### Round 150, Part 0 — at `LocIndep 1` there are no two vertex-disjoint triangles

```lean
JSP90.not_isNClique_three_of_disjoint_of_locIndep_one
  (hG : LocIndep 1 G) (hT : G.IsNClique 3 T) (hD : G.IsNClique 3 D) (hdis : T ∩ D = ∅) : False
```

Erdős's hypothesis is read on the six elements of `T ∪ D`: an independent set meets each triangle in
at most one point (`JSP90.card_le_one_of_isIndepSet_sub_of_card_C_eq_three`), so it has at most two
elements, while `LocIndep 1` demands `2 · |S| + 1 ≥ 6`. Two consequences:

* `JSP90.not_isNClique_three_of_sdiff_of_card_le_four_of_locIndep_one` — the residue `V \ T` of a
  triangle carries no triangle when `|V \ T| ≤ 4`;
* **`JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_seven` — `LocIndep 1 G →
  |V| ≤ 7 → G.IsNClique 3 T → (deleteFinset G T).IsBipartite`.**  An odd cycle of the residue would
  have odd cardinality `≥ 3` inside at most four vertices, hence *be* a triangle. This is the
  reduction the seven-vertex triangle case consumes.

### Round 150, Part 1 — a shortest odd cycle spanning `V` is one-delete

`JSP90.closeToBipartite_one_of_shortest_oddCycle_of_card_eq`: if `C` is a shortest odd cycle with
`C.card = Fintype.card V`, then every odd cycle has `|D| ≥ |C| = |V|`, hence `D = V`, so one vertex
meets all of them and `CloseToBipartite 1 G` holds. (Minimality is essential: a single odd cycle
spanning `V` does not suffice, since a chord may create a triangle.)

### Round 150, Part 2 — a new instance of the headline theorem with the optimal constant `1`

```lean
JSP90.closeToBipartite_one_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven
  (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 7)
  (hgirth : ∀ D, IsOddCycle G D → 7 ≤ D.card) (hne : Nonempty V) : CloseToBipartite 1 G
```

At `|V| ≤ 7` an odd cycle has `3`, `5` or `7` vertices; the first two are excluded by the odd-girth
hypothesis, so every odd cycle spans `V` and Part 1 applies. Companion statements, all proved:

| statement | content |
| --- | --- |
| `JSP90.hitsOddCycles_singleton_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven` | transversal shape: the odd cycles have a common vertex |
| `JSP90.tauOdd_le_one_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven` | `tauOdd G ≤ 1` |
| `JSP90.LocIndepOneSmallOrderOddGirth` + `JSP90.erdos73On_one_oddGirth_ge_seven` | the instance in the `Erdős73On` class shape of `Five.lean` |
| `JSP90.not_closeToBipartite_zero_of_oddGirth_ge_seven_of_not_isBipartite` | the constant `0` fails exactly when `G` is not bipartite, so `1` is optimal in the class |
| `JSP90.exists_isOddCycle_card_eq_seven_of_oddGirth_ge_seven_of_not_isBipartite` | a non-bipartite member of the class has a spanning seven-cycle |

### Round 150, Part 3 — the counting input of the five-cycle case

`JSP90.card_le_two_neighOf_card_C_five_of_triangleFree`: in a triangle-free graph, the neighbours of a
vertex inside a five-cycle are **at most two** (three neighbours are pairwise non-adjacent, an
independent set of three elements of a five-cycle, and
`JSP90.two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle` reads `2 · 3 + 1 = 7 ≤ 5`).
`JSP90.isNClique_three_of_adj_adj_adj` is the small tool that reads "no triangle" in clique language.

### The measurements of this round (`discovery/JSP-000090/r150.c`, `r150b.c`)

Both programs were written from scratch this round; the first version of `r150.c` had a bug in the
independent-set dynamic programme (`a = al[rest]` was written `al[rest \ N(v)]`, which under-counts)
and in the `2K₃` search (the second triangle was required to come *after* the first in the vertex
order), and both were found and fixed before use.  Results, over **all** graphs on `n ≤ 7`:

| question | answer |
| --- | --- |
| Q1: does `LocIndep 1` forbid `K₄` and two disjoint triangles? (`n = 4,5,6,7`, all `2 222 009` graphs) | **yes, at every order**: `0` graphs contain a `K₄`, `0` contain two vertex-disjoint triangles |
| Q2: `max τ_odd` over `LocIndep 1` graphs on seven vertices | `2` (`870 530` graphs need `1`, `13 020` need `2`, `0` need `3`) — consistent with `r148_n7.log` |
| Q3: `max τ_odd` over **triangle-free** `LocIndep 1` graphs on seven vertices | **`1`** (`133 501` graphs) |
| Q4: for each of the `13 020` sharp graphs, is a *mixed pair* `{a ∈ T, x ∉ T}` an odd cycle transversal? | **yes, in all `13 020`**; **all** of them contain a triangle, so the triangle case cannot be dodged |
| Q5 (from `r150b.c`): five-cycles of a triangle-free seven-vertex graph relative to a shortest five-cycle `C` | `16 590` cycles meet `C` in `4` points, **at most `2` per graph and at most `1` per outside vertex**; `4 410` cycles meet `C` in `3` points, **at most `1` per graph** |

Q5 is the exact shape of the remaining five-cycle case: the points of `C` missed by some five-cycle
number at most `2 + 2 = 4 < 5`, so one vertex of `C` is left over.

### What is *not* proved

`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven`, in its two remaining cases:

* **five-cycle case** (`G` triangle-free, shortest odd cycle of five vertices).  Part 3 supplies the
  counting input; what is missing is the identification of the two ring-neighbours of the missed point
  with the neighbours of the outside vertex, which needs the inducedness of a shortest odd cycle
  (`JSP90.isInduced_shortest_oddCycle`) and a four-step matching of two cyclic orders.
* **triangle case**: `T` a triangle, `X = V \ T` of four vertices, `G[X]` triangle-free (Part 0) and
  every `x ∈ X` adjacent to at most two vertices of `T`.  Per Q4 every sharp seven-vertex graph needs a
  *mixed pair* `a ∈ T`, `x ∉ T`.

`jsp_000090_main` remains deliberately undeclared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]`.

### Round 150, Part 4 — the local structure at a shortest odd cycle (amendment)

Two further declarations were added after the section above, bringing `Seven.lean` to 17 declarations:

* **`JSP90.card_neighIn_C_eq_two` — every vertex of a shortest odd cycle `C` has EXACTLY two neighbours
  inside `C`**, namely its two ring-neighbours.  The proof uses `JSP90.isInduced_shortest_oddCycle` (a
  shortest odd cycle carries no chord, so the edges inside `C` are exactly the ring edges) together with
  the two adjacencies `JSP90.CycleOrder.hcyc` and `JSP90.CycleOrder.adj_prev`; the two ring-neighbours
  are distinct by `JSP90.CycleOrder.step_prev_ne`.
* **`JSP90.neigh_eq_of_adj_of_adj` — two distinct neighbours exhaust that neighbourhood**: if
  `p ≠ q`, `v, p, q ∈ C`, `v ~ p`, `v ~ q`, then every neighbour of `v` inside `C` is `p` or `q`.

Together with Part 3 (`card_le_two_neighOf_card_C_five`) this is the whole neighbourhood theory that the
five-cycle case needs.  A third lemma of the same family —
*if `(C \ {c}) ∪ {w}` is a five-cycle and `C` is a shortest odd cycle, then the two neighbours of `w`
along it are both adjacent to `c`* — was written and machine-checked up to its **last** step (that the
two neighbours of `c` inside `C` are the two ends of the new five-cycle) but did not close in this
round's budget; it is **not** in the repository and is recorded verbatim as *Missing Lemma 1* in
`discovery/JSP-000090/policy.json`.

## Round 152 (`lean/JSPProblem/FiveWitness.lean`, 13 declarations, 0 sorry/admit) — THE FIVE-CYCLE
## WITNESS: round 150's named missing step, proved

Attack family 79.  The open item that rounds 150 and 151 both pointed at is the **five-cycle case** of
the sharp seven-vertex instance `JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven`
(`LocIndep 1 G`, `|V| ≤ 7` ⟹ `CloseToBipartite 2 G`, sharp at seven vertices per
`discovery/JSP-000090/r148_n7.log`).  Round 150 split that instance by the cardinality of a *shortest
odd cycle* and settled the case `|C| = 7` with the optimal constant `1`; round 151 settled the
triangle-free instance with no five-cycle and, after correcting a bug in the measurement code of
round 150, recorded as **the only missing step of the five-cycle case**

> *"an outside vertex `w` witnesses at most one five-cycle of the form `(C \ {c}) ∪ {w}`"*.

**This file proves it, together with the two local facts it rests on.**

* **`JSP90.card_witness_le_one` — THE WITNESS LEMMA.**  For a five-cycle `C` with cyclic numbering
  `f : Fin 5 → V` and a vertex `w ∉ C`, the set of indices at which `w` is adjacent to **both**
  ring-neighbours of `f i` — the configuration in which `(C \ {f i}) ∪ {w}` closes up — has **at most one
  element**.  The proof is the one-line pigeonhole of round 150's plan: two witnesses would give `w`
  two *different* two-element sets of neighbours inside `C`, contradicting
  `JSP90.card_le_two_neighOf_card_C_five_of_triangleFree` (round 150, `JSPProblem/Seven.lean` Part 3).
  `JSP90.WitnessSet` and `JSP90.mem_witnessSet` name the counted set.
* **`JSP90.card_neighIn_five_eq_two` — A FIVE-CYCLE OF A TRIANGLE-FREE GRAPH IS INDUCED.**  Every
  vertex of a five-cycle has *exactly* two neighbours inside it: a chord of a five-cycle closes a
  triangle.  Stated in the counting form so that **no case analysis is needed** — the upper bound is
  round 150's lemma, the lower bound is the two ring-neighbours.
* **`JSP90.filter_adj_eq_of_fiveCycle_singleton` — THE BRIDGE.**  Let `C` be a *shortest* odd cycle of
  five vertices, `c ∈ C`, `x ∉ C`, and suppose `(C \ {c}) ∪ {x}` is a five-cycle.  Then

  > `C.filter (fun z => G.Adj x z) = C.filter (fun z => G.Adj c z)`,

  i.e. **`x` is adjacent to exactly the two ring-neighbours of `c` and to nothing else of `C`**.  Here
  "a shortest odd cycle is induced" enters through `JSP90.neigh_eq_of_adj_of_adj`: a neighbour of `x`
  inside the five-cycle whose two ring-neighbours in `C` are both different from `c` would have three
  neighbours inside the five-cycle, which the previous bullet forbids; and `x ≁ c`, since that would
  close a triangle with any neighbour of `x` (rounds 151's `no_triangle_of_not_isNClique`).
* **`JSP90.five_pair_inj`, `JSP90.five_succ_ne_pred`, `JSP90.five_flip_false`,
  `JSP90.adj_ringPred`, `JSP90.cycPred`** — the arithmetic of a five-cycle; in particular the pair of
  ring-neighbours `{cycSucc i, cycPred i}` *determines* the point `i`, which is the "the missed point is
  determined" step of the counting.

Parts 1 and 3 together give the machine-checked statement that was missing: a point of a shortest odd
five-cycle is witnessed by at most one outside vertex.

### The measurement of this round

An independent odd-cycle detector (a subset is an odd cycle iff its size is odd, every vertex has
exactly two neighbours inside it, and it is connected) and an independent `MaxDef ≤ 1` test
(`|W| ≤ 2 α(G[W]) + 1` for every `W`, `α` by the subset DP), over **all** `2^21` graphs on seven
vertices (`discovery/JSP-000090/r152.c`):

| quantity | value |
| --- | --- |
| `LocIndep 1` graphs | `986 787` (bipartite `103 237`, triangle-free `133 501`) |
| `max tauOdd` | `2` |
| pairs `(G, C)`, `G` triangle-free `LocIndep 1`, `C` a five-cycle | `50 904` |
| **max five-cycles `(C \ {c}) ∪ {w}` per outside vertex `w`** | **`1`** |
| max five-cycles meeting `C` in exactly three points | `1`, occurring `12 600` times |
| max points of `C` missed by an odd cycle | `2` |
| violations of "some point of `C` meets every odd cycle" | `0` |
| triangles `(G, T)` at `LocIndep 1`, `|V| = 7` | `2 071 405`; violations of round 151's "some **pair** of `T` is a transversal" | `0` |

The first version of the program (`r152.c`, `r152b.c`) ranged over the bit positions `0, 1, 2` instead
of over the elements of the triangle and produced a spurious `208 440` violations; both were corrected
(`r152c.c`) and the corrected run reproduces round 151's count `2 071 405 / 0`.

### What is still missing

The counting around Parts 1–3, i.e. the five-cycle case itself: with `|V| ≤ 7`, `C` a shortest odd cycle
of five vertices and `G` triangle-free, an odd cycle meets `C` in `5` (it is `C`), in `4` (of the form
`(C \ {c}) ∪ {x}`, at most `|V \ C| ≤ 2` of them by Parts 1 + 3), in `3` (**at most one**, measured) or
is a seven-cycle (hence contains `C`).  At most `2 + 2 = 4` of the `5` points of `C` are missed, so
some point of `C` meets every odd cycle and `CloseToBipartite 1 G` follows.  The single unproved input
is the uniqueness of the three-intersection five-cycle; the pigeonhole itself is standard `Finset`
counting.  The triangle case of the seven-vertex instance (round 151's `CONCRETE MISSING LEMMA 1`) is
unchanged and remains open.

`jsp_000090_main` remains undeclared and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) is
unchanged: the remaining obstruction is the general, 3-connected case.

### Addendum (Parts 4 of the same round): the injectivity of the witness

Two further declarations close the counting around Parts 1–3:

* **`JSP90.filter_adj_C_eq_ringPair`** — the neighbours of `c = f i` inside the shortest odd five-cycle
  `C` are exactly its two ring-neighbours.  Together with `JSP90.five_pair_inj` (on `Fin 5`) and
  `JSP90.five_pair_inj'` (on the vertices of `G`), a *pair of ring-neighbours identifies a point*.
* **`JSP90.x_ne_y_of_two_fiveCycles_singleton`** — **two different points of `C`, each missed by a
  five-cycle of the form `(C \ {c}) ∪ {x}`, are missed by five-cycles with different outside vertices**:
  with `(C \ {c}) ∪ {x}` and `(C \ {c'}) ∪ {y}` five-cycles and `c ≠ c'`, one gets `x ≠ y`.  This is the
  pairwise form of the injection "point of `C` missed by a five-cycle meeting `C` in four points" ↦ "its
  one vertex outside `C`", so the standard `Finset` pigeonhole bounds the number of missed points by
  `|V \ C| ≤ 2`.

The five-cycle case of the seven-vertex instance is therefore reduced to a `Finset` pigeonhole plus one
combinatorial statement (`MISSING LEMMA 3` in `discovery/JSP-000090/policy.json`: at most **one**
five-cycle meets a shortest odd five-cycle `C` in exactly three points — measured, maximum `1`, attained
`12 600` times among the `50 904` pairs `(G, C)`, so it is not vacuous).

---

## Round 172 — `lean/JSPProblem/CycWitness.lean`: the **eight-vertex seven-cycle case** of Erdős #73 is
closed with the **optimal constant 1**, and the witness lemma loses its five-position hypothesis

Attack family 93.  One new file (**23 declarations, 0 `sorry`/`admit`**), `lake build` OK with **1331
jobs**; `#print axioms` on every new declaration reports only
`[propext, Classical.choice, Quot.sound]`; imported from the root module `JSPProblem.lean`.
`harness/score.py --strict-prize` reports `build_ok = true, sorry = 0, admit = 0, partial_ok = true,
missing_theorems = ["jsp_000090_main"]`.

Round 171 closed the triangle case at `|V| ≤ 8` (`JSP90.triCaseEight`).  This round closes the
**seven-cycle case** — and does so by deleting the `Fin 5` hypothesis from the round-152–162 witness
machinery.

### Part 0–2 — the order-free chain

Only two things in round 152's chain were really about five:

* `JSP90.five_flip_false` / `JSP90.five_pair_inj'` — modular arithmetic on `Fin 5`.  Replaced by
  `JSP90.cyc_flip_false_seven` / `JSP90.ring_pair_inj_seven`, whose proofs are verbatim (the flip case
  forces `m ∣ 4`, impossible for `m ≥ 5`);
* `JSP90.card_neighIn_five_eq_two`, which used **triangle-freeness** to make `D = (C \ {c}) ∪ {x}`
  chordless.  Replaced by the already order-free pair `JSP90.card_neighIn_C_eq_two` /
  `JSP90.neigh_eq_of_adj_of_adj` of `lean/JSPProblem/Seven.lean` ("a shortest odd cycle is induced"),
  applied to `D` itself through the new

  * **`JSP90.hshort_of_card_eq`** — an odd cycle of the same cardinality as a shortest one is
    shortest.

  The new order-free statements are

  | lemma | content |
  | --- | --- |
  | **`JSP90.filter_adj_C_eq_ringPair_of_five_le`** | for a shortest odd cycle of **any** length `≥ 5`, the neighbours of `o.f j` inside the cycle are exactly its two ring-neighbours |
  | **`JSP90.card_eq_of_union_sdiff_singleton`** | `\|(C \ {c}) ∪ {x}\| = \|C\|` for `c ∈ C`, `x ∉ C` |
  | **`JSP90.filter_adj_eq_of_cycle_singleton`** | `(C \ {c}) ∪ {x}` an odd cycle of cardinality `\|C\|` ⟹ `C.filter (Adj x) = C.filter (Adj c)`, i.e. `x` sees `C` **exactly** as `c` does.  No triangle-freeness hypothesis: the triangle step of round 152 is replaced by "a triangle is an odd cycle shorter than `C`" |
  | **`JSP90.x_ne_y_of_two_sevenCycles_singleton`** | **the witness is injective, for any cycle length `≥ 5`**: two different points of `C`, each missed by a cycle of the form `(C \ {·}) ∪ {·}`, are missed by cycles with different outside vertices |
  | **`JSP90.card_missedSeven_le_card_univ_sdiff`** | the missed points inject into `V \ C`: `\|Missed\| ≤ \|V \ C\|`, order-free (with `\|V \ C\| ≤ 2` this is round 152's `JSP90.card_missed_le_two_of_card_le_seven`) |
  | **`JSP90.sevenOrder`, `JSP90.filter_adj_C_eq_ringPair_seven`** | the `Fin 7` instance, where `JSP90.CycleOrder.prev` *is* `JSP90.cycPred` |

### Part 3–4 — THE INSTANCE

At `LocIndep 1` and `|V| ≤ 8`, with `C` a shortest odd cycle of **seven** vertices, every odd cycle
`D` has `7 ≤ |D|` (shortestness), `|D|` odd and `|D| ≤ 8`, hence `|D| = 7`; and `D ≠ C` forces
`|D \ C| = |C \ D| = 1`.  So **every missed point of `C` is missed by a cycle of the form
`(C \ {c}) ∪ {x}`**:

* **`JSP90.subset_missed_of_card_V_le_card_C_add_one`** — `AllMissed ⊆ Missed` at `|V| ≤ |C| + 1`,
  stated for **every** odd cycle, with no `5` in sight;
* **`JSP90.card_allMissed_le_one_of_shortest_seven_of_card_V_le_add_one`** — `|AllMissed| ≤ 1`;
* **`JSP90.hitsOddCycles_mem_C_of_shortest_seven_of_card_le_add_one`** — some point of `C` meets
  **every** odd cycle of `G` (the certificate lies **on** `C`);
* **`JSP90.closeToBipartite_one_of_shortest_seven_of_card_le_add_one` — A NEW INSTANCE OF THE
  HEADLINE THEOREM WITH THE OPTIMAL CONSTANT `1`**, stated as

  ```lean
  IsOddCycle G C → (C shortest odd cycle) → C.card = 7 → |V| ≤ |C| + 1 → CloseToBipartite 1 G
  ```

  with **no `LocIndep` hypothesis at all**, no packing hypothesis, no triangle-freeness and no bound on
  anything but the cardinality of the shortest odd cycle;
* **`JSP90.closeToBipartite_one_of_shortest_seven_of_card_le_eight`**,
  **`JSP90.closeToBipartite_one_of_locIndep_one_card_le_eight_of_oddGirth_ge_seven`** (the
  eight-vertex odd-girth-`≥ 7` class instance),
  **`JSP90.erdos73On_one_oddGirth_ge_seven_eight`** (the same in the `Erdős73On` shape),
  **`JSP90.hitsOddCycles_singleton_on_C_of_shortest_seven_of_card_le_eight`**,
  **`JSP90.tauOdd_le_one_of_shortest_seven_of_card_le_eight`**, and
  **`JSP90.not_closeToBipartite_zero_of_oddGirth_ge_seven_eight_of_not_isBipartite`** — the constant
  `1` is optimal inside the class.

### Measurements this round

`discovery/JSP-000090/r172b.c` (all `2^21` graphs on `Fin 8` containing the seven-cycle
`0-1-…-6-0`):

| quantity | value |
| --- | --- |
| `LocIndep 1` graphs with odd girth `7` | `160` |
| `\|{c ∈ C : some odd cycle misses c}\|` | `0` in `128` cases, **`1` in `32`** |
| violations of `\|AllMissed\| ≤ \|V \ C\| ≤ 1 < \|C\|` | **`0`** |
| `tau_odd` | `1` in all `160` |

so the pigeonhole is **tight** (the bound `|AllMissed| ≤ 1` is attained) and the theorem is not
vacuous.

### The remaining eight-vertex case: the five-cycle

`discovery/JSP-000090/r172.c`, over all `2^23` graphs on `Fin 8` containing the five-cycle
`0-1-2-3-4-0`, restricted to the `3 051 680` `LocIndep 1` graphs in which that five-cycle is shortest:

| question | result |
| --- | --- |
| `max \|{c ∈ C : some odd cycle misses c}\|` | **`5`**, attained `110` times |
| graphs with **no** pair of `C` meeting every odd cycle | **`0`** |
| `max #` three-intersection five-cycles | **`6`** (round 162's uniqueness fails at order eight) |
| `max #` points of `C` missed by four-intersection five-cycles | **`4`** (was `≤ 2` at order seven) |
| `tau_odd` | `1` throughout |

**So the eight-vertex five-cycle case is `CloseToBipartite 1` with the certificate on `C` — that is
refuted** (110 counterexamples), while **`CloseToBipartite 2` with the certificate a *pair* of points
of the shortest odd cycle holds with 0 failures**.  With round 171's `triCaseEight` and this round's
seven-cycle case, the five-cycle case is the *only* thing still missing from
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight`.

### What is *not* proved

`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) and hence `jsp_000090_main`; and, inside
order eight, the five-cycle case named above.  `jsp_000090_main` is deliberately **not** declared, so
the harness keeps reporting `missing_theorems = ["jsp_000090_main"]`.  `formalization.yaml` remains
`status: wip`, `prize_ready: false`.  No award claim is made.


---

## Round 175 (`lean/JSPProblem/IndepSplit.lean`) — the **INDEPENDENT-SET-SPLIT axis**: the EIGHT-VERTEX AXIS IS CLOSED, five-cycle case included, with no case analysis

Attack family 94.  New module `lean/JSPProblem/IndepSplit.lean` (27 declarations, 432 lines, **0
sorry, 0 admit**), imported from the root module `JSPProblem.lean`; `lake build` OK with 1332 jobs;
`#print axioms` on every headline result shows only `[propext, Classical.choice, Quot.sound]`.
`harness/score.py problems/JSP-000090` reports `build_ok = true, sorry = 0, admit = 0,
placeholder_total = 0, partial_ok = true`, `missing_theorems = ["jsp_000090_main"]`.

### The gap that is closed

Rounds 171 (`JSPProblem/TriEight.lean`) and 172 (`JSPProblem/CycWitness.lean`) closed two of the three
cases of

```lean
JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight : LocIndep 1 G -> |V| <= 8 -> CloseToBipartite 2 G
```

and left the **five-cycle case** as the only remaining gap of the eight-vertex axis, to be attacked by
pricing the points of the shortest odd five-cycle that a two-element certificate has to cover.

**This round closes it, and the case analysis is not needed at all.**  The obstruction was not the
counting but the *object*: rounds 152–172 ask **which odd cycles an odd cycle transversal must hit**,
while `CloseToBipartite m G` is also the statement that **the vertices of `G` split into two
independent sets and a remainder of at most `m` points**.  Under that reading Erdős's hypothesis can
be applied a second time, and once applied twice at `k = 1` and `|V| <= 8` it yields the constant `2`.

### What is proved

| result | content |
|---|---|
| `JSP90.isBipartiteWith_of_cover`, `JSP90.closeToBipartite_of_cover` | the two directions of the reading: a cover of `V` by two independent sets and a remainder `s` **is** a bipartition of `G - s` |
| **`JSP90.closeToBipartite_of_isIndepSet`** | **THE SPLIT LEMMA**, with **no hypothesis at all**: `CloseToBipartite (|V \ I| - α(G[V \ I])) G` for every independent set `I`.  The odd cycle transversal number of a graph is at most the deficiency of the complement of any independent set, and the two deleted pieces are `I` and a maximum independent set `K` of `G[V \ I]` |
| `JSP90.exists_cover_of_isIndepSet` | the certificate: two disjoint independent sets `I`, `K` with `|K| = α(G[V \ I])` |
| **`JSP90.closeToBipartite_one_iff_exists_cover`** | **the exact characterisation of `CloseToBipartite 1`**, both directions: the vertices of `G` split into two independent sets and at most one leftover vertex — *"defect `≤ 1` is bipartite plus one exception"*, machine-checked |
| `JSP90.sdiff_indepCard_le_of_locIndep` | Erdős's hypothesis bounds the cost of the split **twice**: `|V \ I| - α(G[V \ I]) ≤ ((|V| + k) / 2 + k) / 2` |
| **`JSP90.closeToBipartite_of_locIndep_of_card_le`** | **A NEW INSTANCE OF THE HEADLINE THEOREM, FOR EVERY `k`**: `LocIndep k G → CloseToBipartite (((|V| + k) / 2 + k) / 2) G`.  No odd girth, no packing number, no packing weight, no degree bound, no bound on the number of cut or branch vertices, no connectivity, no decomposition |
| **`JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight`** | **`LocIndep 1 G → |V| ≤ 8 → CloseToBipartite 2 G`: the eight-vertex axis, five-cycle case included.**  It subsumes round 171's `JSP90.triCaseEight` and round 172's `closeToBipartite_one_of_shortest_seven_of_card_le_eight` |
| `JSP90.erdos73On_two_of_locIndep_one_card_le_eight`, `exists_hitsOddCycles_two_of_card_le_eight`, `tauOdd_le_two_of_card_le_eight`, `erdos73On_of_locIndep_of_card_le`, `exists_hitsOddCycles_of_locIndep_of_card_le`, `tauOdd_le_of_locIndep_of_card_le` | the same instances in the three shapes used by the rest of the development |
| `JSP90.closeToBipartite_three_of_locIndep_one_card_le_nine`, `..._card_le_twelve`, `closeToBipartite_four_of_locIndep_one_card_le_fourteen`, `tauOdd_le_three_of_locIndep_one_card_le_twelve` | **the order ladder: orders 9, 12 and 14 had no statement in the whole development** |
| `JSP90.eq_of_adj_of_isIndepSet`, `notAdj_of_isIndepSet_of_mem`, `univ_sdiff_sdiff`, `disjoint_of_subset_sdiff`, `coloring_of_isBipartite_delete`, `isIndepSet_filter_eq`, `closeToBipartite_two_of_cover_of_card_le_two`, `closeToBipartite_two_of_locIndep_one_card_le_seven'` | the supporting lemmas |

The proof of the headline result is four lines: Erdős's hypothesis gives `α(G) ≥ 4` at `|V| ≤ 8`, so
`J = V \ I` has at most four points for a maximum independent set `I`; Erdős's hypothesis again gives
`α(G[J]) ≥ 2`; the split lemma then delivers a two-element odd cycle transversal.

### Measurement (run before formalising, as rounds 76–80 established)

* `r175/m.c`: over all `2^23` graphs on `Fin 8` with `C = {0, …, 4}` a five-cycle and `W = V \ C` of
  size `3`, of the **5717** that satisfy `LocIndep 1`, the union of the points of `C` missed by *some*
  odd cycle is **all of `C`** (`max |AllMissed| = 5`, attained 110 times).  **So the certificate-on-`C`
  version of the five-cycle case — the statement round 172 aimed at — is FALSE**, while the union of
  forbidden *pairs* of `C` has at most **5** of the 10 pairs, so a pair certificate exists with 0
  failures.
* `r175/p.c`: at most 4 of the 5 cycle edges of `C` are ever blocked by an odd cycle.
* `r175/q.c`: the union of missed points of `C` is bounded by `0, 1, 2, 5` at orders `5, 6, 7, 8` — the
  order-eight jump is the first at which an odd cycle can miss *all* of `C`.
* `r175/t.c`: **for every `LocIndep 1` triangle-free graph on `n ≤ 8` vertices the odd cycle
  transversal number is exactly `1`** (1, 11, 202 and 5717 such graphs at `n = 5, 6, 7, 8`).
* `r175/r.c`: random search at orders 9 and 10 finds no `LocIndep 1` triangle-free graph with
  `tau_odd ≥ 2`.

### Refuted this round, so that no later round re-attempts it

* **`alpha(G[X]) ≥ |X| / 2` for triangle-free `G` is FALSE** (the Petersen graph has `|V| = 10` and
  `α = 4`), so `|X| ≤ 2 α(X) + 1` is **not** available from triangle-freeness.  The instance proved
  here rests on Erdős's hypothesis, applied twice, and on nothing else.
* **The certificate-on-`C` version of the eight-vertex five-cycle case is false** (110
  counterexamples), so the `AllMissed` machinery of rounds 152–172 cannot be pushed past order seven.

### Why this does not reach `jsp_000090_main`, stated exactly

`JSP90.closeToBipartite_of_locIndep_of_card_le` bounds the transversal by `((|V| + k) / 2 + k) / 2`,
which still mentions the **order** of `G`.  `LocIndep 0` is bipartiteness and bipartite graphs have
arbitrarily many vertices, so no hypothesis at fixed `k` bounds `|V|`; the constant of the split is an
order-dependent constant.  Eliminating the order is exactly the content of Reed's theorem
(`O(k log k)`), and no finite amount of splitting removes it.  The concrete next target recorded in
`discovery/JSP-000090/policy.json` is therefore `LocIndep 1` at order **nine** with the constant `2`
(`p9`, round 76, is the first witness at which `2` is needed among triangle-free graphs), with
`JSP90.closeToBipartite_one_iff_exists_cover` — the new exact characterisation — as the tool.

`jsp_000090_main` is deliberately **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.  `formalization.yaml` remains `status: wip`,
`prize_ready: false`.  No award claim is made.


---

## Round 180 — `lean/JSPProblem/TriDescent.lean` (new file, attack family 98): **the exact descent at a triangle**

New module `JSPProblem/TriDescent.lean` (**30 declarations, 0 sorry/admit**, `lake build` OK with
**1336 jobs**, axiom report clean: `propext, Classical.choice, Quot.sound` on every new result),
imported from the root module `JSPProblem.lean`.  `harness/score.py --strict-prize` reports
`build_ok = true, sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true`,
`missing_theorems = ["jsp_000090_main"]`.

Round 179 closed the *connectivity* axis and named one remaining local step,
`JSP90.PieceMaxDefErdős73On C` ("every connected graph of deficiency `r` is `C · r`-close to
bipartite"), which `JSP90.closeToBipartite_mul_of_pieceMaxDefErdős73On` turns into the whole
headline theorem for **any** universal `C`.  This round supplies the *arithmetic* of the classical
triangle descent — the one step that must be exact if such a `C` is ever to exist — in the numerical
language, with **no order bound and no case analysis**.

### Part 1 — one triangle costs exactly one unit of deficiency

* **`JSP90.maxDef_ge_add_one_maxDef_delete_of_isNClique`**
  `G.IsNClique 3 T → 1 + MaxDef (deleteFinset G T) ≤ MaxDef G`.
  This lifts round 118's `JSP90.maxDefIn_ge_one_add_maxDefIn_of_clique` from the `maxDefIn` form to
  the `MaxDef`-of-the-deleted-graph form, through
  `JSP90.maxDefIn_eq_maxDef_induce` (round 179).  No `LocIndep`, no odd girth, no order bound.
* **`JSP90.locIndep_pred_of_isNClique`**
  `G.IsNClique 3 T → LocIndep (k+1) G → LocIndep k (deleteFinset G T)`:
  **Erdős's local parameter drops by exactly one at a triangle.**  This is the *statement* of the
  descent that rounds 162–175 carried out by hand, four times, at orders seven and eight.

### Part 2 — the iterated descent, and a packing bound with no factor

* `JSP90.TriFamily` — a family of pairwise vertex-disjoint triangles (edges *between* the triangles
  are allowed, which makes this class strictly larger than Part 4's);
  `JSP90.deleteFinset_deleteFinset_of_union`, `JSP90.isNClique_three_deleteFinset`,
  `JSP90.maxDef_ge_add_one_maxDef_delete_of_triFamily_peel` (the one-triangle step);
* **`JSP90.maxDef_ge_card_add_maxDef_delete_of_triFamily`**
  `𝒬.card + MaxDef (deleteFinset G (𝒬.biUnion id)) ≤ MaxDef G`, proved by induction on `𝒬`;
* **`JSP90.card_triFamily_le_maxDef`** — hence **the number of pairwise disjoint triangles of `G`
  is at most `MaxDef G`, with no factor**: the triangle *packing* is bounded by Erdős's own
  parameter.

### Part 3 — the cost of the descent

* `JSP90.isOddCycle_deleteFinset_of_disjoint` — an odd cycle avoiding `Z` survives in `G − Z`;
* `JSP90.card_biUnion_le_three_card` — `t` disjoint triangles use at most `3 t` vertices;
* **`JSP90.closeToBipartite_three_mul_of_triFamily_of_isBipartite_delete`** (and
  `tauOdd_le_three_mul_…`, `erdos73On_three_…`) — `TriFamily G 𝒬`, a bipartite residue and
  `LocIndep k G` give **`CloseToBipartite (3 k) G`**: three vertices per triangle, with the
  hypothesis entering **only** through `MaxDef G`.

### Part 4 — the anticomplete case: both sides have the *exact* value, optimal constant `1`

* **`JSP90.AnticompleteTriCover`** — `𝒬` pairwise disjoint and anticomplete triangles covering `V`;
* **`JSP90.exists_oddCycle_of_anticompleteTriCover`** — the odd cycles of `G` are **exactly** the
  members of `𝒬` (an odd cycle is connected, meets only one anticomplete piece, and both have at
  least three vertices);
* **`JSP90.tauOdd_eq_card_of_anticompleteTriCover`** and
  **`JSP90.maxDef_eq_card_of_anticompleteTriCover`** — `MaxDef G = tauOdd G = 𝒬.card`, so Erdős's
  hypothesis and its conclusion **coincide** on this class;
* **`JSP90.closeToBipartite_of_anticompleteTriCover_of_locIndep`** (with
  `erdos73On_one_of_anticompleteTriCover_of_locIndep`, `tauOdd_le_of_anticompleteTriCover_of_locIndep`)
  — **AN INSTANCE OF THE HEADLINE THEOREM WITH THE OPTIMAL CONSTANT `k`** on this class.

### Part 5 — the class is nonempty and the constant is optimal

* **`JSP90.anticompleteTriCover_kTriangles`** — the `k` fibres of the sharp witness `kTriangles k`
  are such a cover;
* **`JSP90.erdos73On_kTriangles_anticompleteTri`** —
  `(LocIndep k (kTriangles k) → CloseToBipartite m (kTriangles k)) ↔ k ≤ m`: the constant `1` per
  triangle is **exact**, as in `JSP90.erdos73On_of_multi_optimal` (round 106).

### What this says about the remaining gap, exactly

Parts 1–2 show a triangle is worth **exactly one** unit of `MaxDef`; Part 4 shows it costs
**exactly one** unit of `tauOdd` on the anticomplete class.  So the triangle descent is *free*, and
its optimal constant is `1` per unit of deficiency.  What it does **not** give is the *existence* of
a triangle-cut ladder: `kTriangles k` has one, while `k4sub` (round 126: `MaxDef = 1`,
`tauOdd = 2`, triangle-free) has **none**.  The remaining step is therefore unchanged and is
`JSP90.PieceMaxDefErdős73On C` for a universal `C` — i.e. Reed's theorem, `f(k) = O(k log k)` with
the sharp lower bound `f(k) ≥ 2k` (`JSP90.tauOdd_p9Family`).

`jsp_000090_main` is deliberately **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.  `formalization.yaml` remains `status: wip`,
`prize_ready: false`.  No award claim is made.
