# JSP-000090 — Lean formalization (Erdős Problem #73, Reed 1999)

## Layout

| file | contents |
| --- | --- |
| `JSPProblem/Definitions.lean` | `LocIndep`, `CloseToBipartite`, `Erdős73`, `Erdős73On` — the catalog statement, machine-checked |
| `JSPProblem/Reed.lean` | the structural API: heredity, the clique obstruction, the easy direction, the conclusion API |
| `JSPProblem/OddCycle.lean` | the odd-cycle characterisation of bipartiteness (a Mathlib `TODO`) and **Erdős #73 for `k = 0`** |
| `JSPProblem/Packing.lean` | the odd-cycle **packing** half: at most `k` vertex-disjoint odd cycles |
| `JSPProblem/Transversal.lean` | the **transversal** half: the conclusion ↔ odd cycle transversal, a maximum packing is a transversal, Erdős #73 for graphs of bounded odd girth (`f(k) = ℓ * k`), and the reduction of the whole theorem to Erdős–Pósa for odd cycles |
| `JSPProblem/Fan.lean` | the **local fan argument** (round 35): arcs of a cycle, the odd-arc parity count, the fan lemma, the short-arc lemma at a shortest odd cycle, and the resulting 2-cut structure |
| `JSPProblem/Branch.lean` | the **branch-vertex attack family** (round 38): delete the vertices with three neighbours, where the odd cycles become pairwise disjoint, so a packing bound is a transversal bound; Erdős #73 for graphs with few high-degree vertices (`f(k) = m + k`, no bound on the odd girth) |
| `JSPProblem/Sharp.lean` | the **optimality** family (round 39): the witness `K_3 ⊔ ... ⊔ K_3` makes the constant as large as possible — the lower bound `f(k) ≥ k` of Erdős #73, and sharpness of the round-38 instance `erdos73On_of_no_branch` |
| `JSPProblem/Residue.lean` | the **residue of a packed odd cycle** (round 40): the packing number of `G - C` drops by one, the induction step `CloseToBipartite q (G - C) → CloseToBipartite (q + \|C\|) G`, the case of packing number one, and the minimum transversal with its private odd cycles |
| `JSPProblem/Chord.lean` | **a shortest odd cycle is chordless and induced** (round 40): the arc machinery generalised to a closing vertex on the cycle — the complete local structure at a shortest odd cycle |
| `JSPProblem/Separator.lean` | the **2-cut decomposition** (round 42): a split `V = {a,b} ⊔ T₁ ⊔ … ⊔ T_t` with the parts pairwise anticomplete; odd cycles lie in a unique piece, transversals and the conclusion of Erdős #73 are additive over a 2-cut, and the 2-cut parity lemma — the reduction of the theorem to the 3-connected case |
| `JSPProblem/Count.lean` | the **counting half of the 2-cut decomposition** (round 43): a cycle meeting exactly one vertex of the cut lies in a half-piece, the non-bipartite parts of a split number at most `k` under `LocIndep k G`, so the decomposition costs `2 + m * k` instead of `2 + m * t` (**new, strictly stronger instance of the headline theorem**), the full packing decomposition `card ≤ 2 + t * r`, and **the precise reduction of Erdős–Pósa for odd cycles to the 2-cut-free case plus a uniform bound on the number of 2-cuts** |
| `JSPProblem/Weight.lean` | the **weighted Erdős–Pósa theorem** (round 44): the residue induction run to exhaustion — bounded *packing weight* forces a bounded odd cycle transversal, the transversal number is at most the weight of a maximum-weight packing, the residue of a maximum-weight packing is bipartite, a **new instance of the headline theorem** for graphs of bounded packing weight, the exact value of the conclusion on complete graphs, and the machine-checked **refutation of the naive `+1` absorption step** (`K_5`) |
| `JSPProblem/Free.lean` | **the fan of an odd cycle in a triangle-free graph** (round 69): triangle-freeness made usable (a `3`-cycle is a `3`-clique, `N(v)` is independent, the closed neighbourhood is bipartite, every odd cycle has `≥ 5` vertices), the *complete local structure at a shortest odd cycle* of a triangle-free graph, the packing descent `oddCycleFamily_card_le_of_boundary` (the fan carries one unit less packing), and the reduction **`erdos73_iff_fanErdős73`: Erdős #73 is EQUIVALENT to the purely local statement that the boundary of one odd cycle of a triangle-free graph can be killed with `O_k(1)` vertices** — no Menger, no connectivity, no packing number, no odd girth |
| `JSPProblem/Greedy.lean` | the **GREEDY SHORTEST-ODD-CYCLE axis** (round 102): the odd girth of a graph (`JSP90.girthOf`) and a shortest odd cycle (`JSP90.greedyCycle`), the greedy residue chain (`JSP90.level`, `JSP90.unionUpTo`, `JSP90.residueOf_greedyChain`), two greedy cycles of different levels are disjoint (`JSP90.disjoint_greedyCycle_of_lt`), `n` non-bipartite levels give `n` disjoint odd cycles (`JSP90.packing_of_levels`), Erdős's hypothesis makes the `k`-th level bipartite (`JSP90.level_isBipartite_of_locIndep`), the ladder with **no** packing bound (`JSP90.closeToBipartite_of_greedyChain_step`), and the new instance of the headline theorem `JSP90.erdos73On_of_greedyChain`: `LocIndep k G → CloseToBipartite (∑ j : Fin k, girthOf (level G j)) G`, with the transversal exhibited |
| `JSPProblem.lean` | root module |

## The statement

Erdős #73: for every `k ≥ 0` there is `f(k)` such that a finite graph `G` in which **every subgraph
`H` has an independent set of size `≥ (|V(H)| − k)/2`** is the union of a bipartite graph and at
most `f(k)` vertices.

```lean
def LocIndep (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ X : Finset V, ∃ S : Finset V, S ⊆ X ∧ G.IsIndepSet S ∧ 2 * S.card + k ≥ X.card

def induceFinset (G : SimpleGraph V) (s : Finset V) : SimpleGraph V   -- induced subgraph on `s`
def deleteFinset (G : SimpleGraph V) (X : Finset V) : SimpleGraph V   -- = induceFinset G (univ \ X)

def CloseToBipartite (m : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ X : Finset V, X.card ≤ m ∧ (deleteFinset G X).IsBipartite

def Erdős73 (k : ℕ) : Prop := ∃ m : ℕ, Erdős73On k m
```

**Correction (round 34).**  `CloseToBipartite` used to be

```lean
∃ X : Finset V, X.card ≤ m ∧ ∃ s t : Set V, G.IsBipartiteWith s t ∧ (Set.univ \ (s ∪ t)) ⊆ (X : Set V)
```

i.e. a bipartition `s, t` of the **whole** graph `G`.  That reading is degenerate — `IsBipartiteWith s t`
forces every edge of `G` to join `s` to `t`, so it can only ever absorb *isolated* vertices, and under
it `Erdős73 1` is **false**: `K_3 = completeGraph (Fin 3)` satisfies `LocIndep 1` (`completeGraph_locIndep`)
but has no bipartition for any `m` (`JSP90.rejected_reading_fails`).  The definition now says what the
catalog question says, and the `k = 1` sharp example becomes provable
(`JSP90.closeToBipartite_completeGraph_three : CloseToBipartite 1 (K_3)`).

`2 * |S| + k ≥ |X|` is `|S| ≥ (|X| − k)/2` rewritten in ℕ. Restricting the local hypothesis to
induced subgraphs `G[X]` is equivalent to quantifying over all subgraphs `H ≤ G`, because
`α(H) ≤ α(G[V(H)])`.

## Proved (`JSPProblem/Reed.lean`)

Basic API
* `IsIndepSet.mono_le`, `IsIndepSet.subset` — independent sets under super/sub-sets.
* `LocIndep.mono_le` — **heredity**: the hypothesis passes to every subgraph.
* `LocIndep.mono_k` — the hypothesis weakens with `k`.

The clique obstruction
* `indep_card_le_one_of_clique` — an independent set inside a clique has size ≤ 1.
* `LocIndep.clique_card_le` — **every clique `C` of `G` has `|C| ≤ k + 2`**.
* `completeGraph_locIndep` — `K_{k+2}` satisfies `LocIndep k` (the bound is tight from below).
* `not_completeGraph_locIndep` — `K_{k+3}` does not satisfy `LocIndep k`.

The easy direction
* `IsBipartiteWith.isIndepSet_left` / `_right` / `_univ_compl` — both parts of a bipartition and the
  complement of a part are independent.
* `bipartition_split` — completes a (possibly non-surjective) bipartition to a two-colouring of
  all of `V`.
* `exists_indep_cover_of_isBipartiteWith` — the two parts cover `X` inside `X` and are independent,
  so `|X| ≤ 2 · max`.
* `isBipartite_locIndep` — **`G.IsBipartite → LocIndep k G` for every `k`** (the easy half of the
  theorem, and the case `k = 0` of the *converse*).
* `isBipartite_indepSet_card_half` — the quantitative witness `2|S| ≥ |X|`.

The conclusion
* `isBipartiteWith_univ`, `isBipartite_closeToBipartite` — a bipartite graph is `m`-close to
  bipartite with **no** deletions.
* `CloseToBipartite.mono` — monotone in `m`.
* `closeToBipartite_zero_iff` — `CloseToBipartite 0 G ↔ G.IsBipartite`.
* `Erdős73.mono` — proving `Erdős73 k` proves it for every larger `k`, with the same witness.

## The hard direction, part 1: the odd-cycle characterisation (`JSPProblem/OddCycle.lean`)

At the pinned Mathlib revision `5ed29652` the header of
`Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` lists as an open `TODO`:

> Prove that `G.IsBipartite` iff `G` does not contain an odd cycle.

The direction needed for Erdős #73 is proved here from scratch, on top of `SimpleGraph.Walk`:

* `walk_length_parity_congr`, `walk_length_parity_ne` — walks with the same endpoints have the same
  length parity when all closed walks of a set are even.
* `col_of_even_closed_walks`, `colorable_two_of_even_closed_walks` — if every closed walk of `G` has
  even length then `G.Colorable 2`, i.e. `G` is bipartite. (Reachable-set 2-colouring, by strong
  induction on `W.ncard`.)
* `exists_odd_closed_walk_of_not_bipartite` — a non-bipartite graph has an odd closed walk.
* `exists_odd_cycle_inj` — an odd closed walk contains a **simple** odd cycle, formalised as an
  injection `f : Fin m → V` with `m` odd, `m ≥ 3`, and `f i` adjacent to the cyclic successor
  `f (cycSucc i)` (splicing a repeated vertex gives a shorter odd closed walk).
* `indep_card_le_of_odd_cycle` — an independent set on such a cycle has `2 * |S| + 1 ≤ m`
  (`α(C_m) ≤ ⌊m/2⌋`).
* `locIndep_zero_isBipartite` — **`LocIndep 0 G → G.IsBipartite`**: the hypothesis gives an
  independent set of at least `|X| / 2` inside every `X`, but on an odd cycle that is impossible.
* `erdos73On_zero`, `erdos73_zero` — hence **Erdős Problem #73 holds for `k = 0`**, with the sharp
  constant `m = 0`:
  ```lean
  JSP90.erdos73_zero : Erdős73 0
  ```

## The hard direction, part 2: odd-cycle packings (`JSPProblem/Packing.lean`)

For `k ≥ 1` the conclusion is that a *bounded number of vertices* makes `G` bipartite, i.e. that the
**odd cycle transversal number** of `G` is bounded in terms of `k`. The classical route runs through
Erdős–Pósa, and its first half is elementary:

* `card_eq_sum_card_inter_of_disjoint` — cardinality is additive over a disjoint family covering a set.
* `IsOddCyclePacking` — a family of pairwise vertex-disjoint odd cycles of `G` (the *packing number*
  is `C.card`).
* `packing_ineq` — **every independent set inside the union of a packing loses one vertex per cycle**:
  `2 * |T| + |C| ≤ |⋃ C|`.
* `LocIndep.oddCycle_packing_le` — **at most `k` vertex-disjoint odd cycles**: the independent set
  supplied by the local hypothesis on the union of the cycles has `2 * |T| + k ≥ |⋃ C|`, so `|C| ≤ k`.

## The hard direction, part 3: odd cycle transversals (`JSPProblem/Transversal.lean`)

`JSPProblem/Packing.lean` bounded the *packing* number. This file does the *transversal* half, and in
particular establishes the two bridges that the classical route needs.

Iterating the cyclic successor
* `cycSucc_pow_val` — `k` steps around the cycle from `i` land at `(i + k) mod n`;
  `cycSucc_pow` — one full turn is the identity.
* `cycSucc_pow_flip` (hence `cycSucc_pow_even`, `cycSucc_pow_odd`) — a predicate that flips at
  every step has the same value at a vertex after an even number of steps and the opposite value
  after an odd number; `not_iff_self` — a proposition is never equivalent to its own negation.

The odd-cycle characterisation of bipartiteness (both halves)
* `even_of_cycle_in_bipartition` — a cycle whose vertices lie in the two sides of a bipartition has
  **even** length (the predicate "`f j ∈ s`" flips once per step).
* `exists_outside_of_oddCycle` — an odd cycle has a vertex outside `s ∪ t`.
* `not_isOddCycle_of_isBipartite` — **a bipartite graph contains no odd cycle**.
* `isBipartite_of_no_oddCycle` — **a graph with no odd cycle is bipartite** (an odd closed walk
  contains a simple odd cycle). Together with `JSPProblem/OddCycle.lean` this closes, in this
  development, the `TODO` in the header of `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` at the
  pinned revision (`G.IsBipartite` iff `G` has no odd cycle).

The conclusion ↔ odd cycle transversal
* `isOddCycle_image` — the vertex set of a cyclic ordering is an odd cycle.
* `isOddCycle_delete_of_oddCycle_avoiding`, `oddCycle_of_isOddCycle_delete` — an odd cycle survives
  (resp. descends to) the deletion of a set it avoids.
* `isBipartite_delete_of_hitsOddCycles` — **a deletion which kills all odd cycles is bipartite**.
* `hitsOddCycles_of_isBipartite_delete` — the converse.
* `closeToBipartite_iff_hitsOddCycles` — **`CloseToBipartite m G` iff some set of at most `m`
  vertices meets every odd cycle of `G`.**  This is the missing bridge of round 33's blocker list.

A maximum packing is a transversal
* `exists_maxCard_oddCycleFamily`, `hitsOddCycles_of_maxCardFamily` — a family of pairwise
  disjoint odd cycles of maximum cardinality meets every odd cycle (otherwise it could be enlarged).

Erdős #73 for graphs of bounded odd girth — **a new proved instance of the headline theorem**
* `shortOddCycles_transversal` — if every odd cycle of `G` has at most `ℓ` vertices, a packing of at
  most `r` disjoint odd cycles yields a transversal of at most `ℓ * r` vertices.
* `shortOddCyclesErdosPosa` — the same statement phrased as a consequence (`ShortOddCyclesErdosPosa`).
* `erdos73On_of_bounded_odd_girth` — **hence, for every `k` and every `ℓ`**, if every odd cycle of
  `G` has at most `ℓ` vertices and `LocIndep k G` holds, then `CloseToBipartite (ℓ * k) G`: Erdős
  Problem #73 for the whole class of graphs of odd girth at most `ℓ`, with the **explicit**
  constant `f(k) = ℓ * k`.

The sharp example at `k = 1`, and a test of the statement
* `not_isBipartite_completeGraph_three` — `K_3` is not bipartite.
* `closeToBipartite_completeGraph_three` — **but `CloseToBipartite 1 (K_3)`**: deleting `{0}` leaves
  `K_2`. Together with `completeGraph_locIndep 1` (`LocIndep 1 K_3`) this is the `k = 1` extremal
  example of Erdős #73.
* `rejected_reading_fails` — the machine-checked record that the *rejected* reading of
  `CloseToBipartite` makes the headline statement false already at `k = 1`.

## Proved (`JSPProblem/Fan.lean`) — the local fan argument

Arithmetic on the cycle (`JSPProblem/Fan.lean`)
* `mod_inj_add` — cancellation of a common shift modulo `m` (the only modular fact needed).
* `cycSucc_pow_inj` — two *short* arcs (`p, q < m`) out of a cycle vertex are distinct.
* `arc_rev` — if `d < m` steps take `i` to `j`, then `m - d` steps take `j` back to `i`.
* `exists_c_arc` / `exists_arc` — every other vertex is reached by a number of steps in `(0, m)`.
* `even_compl_of_odd`, `arc_parity` — **exactly one of the two arcs between two distinct vertices
  of an odd cycle is odd** (the two lengths add up to the odd length `m`).

The arc-cycle constructor — the parity core of the fan argument
* `arcFun` — the closed walk `x → f i → … → f (cycSucc^[d-1] i) → x` as a map `Fin (d+2) → V`.
* `arcFun_inj`, `arcFun_adj`, `arc_card`, `card_eq_cyclicOrder` — it is a *simple* cycle with
  `d + 2` vertices, and the cycle carried by `f : Fin m → V` has `m` vertices.
* `arc_isOddCycle` — **if `d` is odd, that closed walk is an odd cycle.**  No Menger theorem, no
  connectivity: the odd cycle through `x` is found by *counting* the parity of the two arcs.

The fan lemma
* `oddCycle_through_fan` — a vertex `x` outside an odd cycle `C` adjacent to two distinct vertices
  of `C` lies on an odd cycle `D` with `x, f i, f j ∈ D` and `|D| ≤ |C|`.
* `oddCycle_through_fan_of_shortest` — at a **shortest** odd cycle, `|D| = |C|`.

The short-arc lemma (classical)
* `shortArc_of_shortest` — let `C` be a shortest odd cycle with `|C| ≥ 5`, and let `x ∉ V(C)` see
  two distinct vertices `f i`, `f j` of `C`.  Then the two attachment points are at cyclic distance
  **exactly 2**: `cycSucc (cycSucc i) = j` or `cycSucc (cycSucc j) = i`.  In particular an outside
  vertex never sees two *consecutive* vertices of a shortest odd cycle of length `≥ 5` — a genuine
  fan would have produced a shorter odd cycle.
* `neigh_pair_close_of_shortest`, `card_inter_neigh_le_two` — consequently **a vertex outside a
  shortest odd cycle of length `≥ 5` meets that cycle in at most two vertices** (three neighbours
  would be pairwise related by the rotation `T = (cycSucc ∘ cycSucc)`, and `T^[3] = id` would force
  `m ∣ 6`, impossible for odd `m ≥ 5`).
* `locIndep_shortest_attach` — the same statement instantiated under Erdős's local hypothesis
  `LocIndep k G`.

This is the **local** half of the classical proofs of Erdős–Pósa for odd cycles (Lovász 1965 for
`r = 1`, Reed–Robertson–Seymour–Thomas for general `r`); the **global** half — turning this local
structure into a bound on a transversal — is still open here.

## Proved (`JSPProblem/Branch.lean`) — the branch-vertex attack family

A third route to the same research statement, completely independent of the fan argument and of
any connectivity machinery.  A vertex with three pairwise distinct neighbours is a **branch
vertex**; deleting all of them leaves a graph of maximum degree `≤ 2`, in which the odd cycles are
pairwise disjoint — so there the *packing* bound is automatically a *transversal* bound, with no
gap.

* `BranchVertex G v`, `branchVertex_three`, `two_of_three` — the definition and its only
  consequence used below ("a vertex which is not a branch vertex has at most two neighbours").
* `CycleOrder` — the cyclic order carried by a cycle (the data of `IsOddCycle` without the
  oddness), with `prev_succ`, `succ_prev`, `iter_succ`, `iter_add_m`, `step_ne`, `prev_ne`,
  `step_prev_ne`, `adj_prev`, `prev_iter`, `exists_iter` (every vertex of the cycle is reached in
  `< m` steps).
* `neigh_two_of_not_branch`, `adj_iff_cycle_neigh` — **the two neighbours of a vertex of a cycle
  are its two cycle-neighbours** in a graph without branch vertices.
* `IsOddCycle.neigh_subset` — a vertex of an odd cycle has **no neighbour outside the cycle**.
* `subset_of_mem_inter_of_no_branch`, `eq_of_mem_inter_of_no_branch`, `disjoint_of_no_branch` —
  **two odd cycles meeting at a vertex are equal**, hence the odd cycles of such a graph are
  pairwise disjoint.
* `maxCardFamily_eq_all_oddCycles` — a **maximum** packing of odd cycles already contains *all*
  the odd cycles (a maximum packing meets every odd cycle, and an odd cycle meeting a packed cycle
  *is* that cycle).
* `hitsOddCycles_onePerCycle` — one vertex per packed cycle is a transversal, and there are at
  most as many packed cycles as the packing bound.
* `closeToBipartite_of_no_branch` — **Erdős–Pósa for odd cycles in graphs without branch
  vertices, with the optimal function `r ↦ r`.**
* `IsOddCycle.of_deleteFinset`, `deleteFinset_deleteFinset` — odd cycles survive deletions.
* `erdos73On_of_bounded_branch` — **a new instance of the headline theorem**: if every branch
  vertex of `G` lies in a set `B` of at most `m` vertices, then `LocIndep k G` forces
  `CloseToBipartite (m + k) G`.  Unlike `erdos73On_of_bounded_odd_girth` this puts **no bound on
  the odd girth**.
* `erdos73On_of_few_high_degree` — the same statement with the hypothesis read on `G` itself: the
  vertices of degree `≥ 3` lie in a set of size `m` (the classical "small kernel" formulation).
* `erdos73On_of_no_branch` — the case `m = 0`.

Why this family stops here: a *bipartite* graph may have arbitrarily many branch vertices
(`K_{n,n}` is bipartite, every vertex has degree `n`) while needing no modification at all, so the
number of branch vertices cannot be bounded in terms of `k`; only the branch vertices of the
*non-bipartite part* are controlled, and that is exactly the global content of `OddCycleErdosPosa`.

## Proved (`JSPProblem/Sharp.lean`) — how large must the constant be?

A fourth and independent family, and the first one that gives a **lower** bound: every other file
of this development bounds `f(k)` from above, none of them says how large the constant has to be.

The witness is `kTriangles k` = `K_3 ⊔ K_3 ⊔ ... ⊔ K_3` (`k` copies) on `Fin 3 × Fin k`: the
`k` fibres `Fin 3 × {i}` each carry a `K_3` and nothing joins two fibres.

* `kTriangles`, `tri`, `mem_tri`, `card_tri`, `tri_disjoint`, `tri_adj` — the graph, its `k`
  components, and the fact that two distinct vertices of a fibre are adjacent.
* `isOddCycle_tri` — **each fibre is an odd cycle**: `kTriangles k` contains `k` pairwise
  vertex-disjoint odd cycles.
* `triPick`, `triActive`, `triIndep` (with `mem_triPick`, `triIndep_indep`, `card_triIndep`) — the
  independent set used for the local hypothesis: **one vertex in each nonempty fibre**.
* `locIndep_kTriangles` — **`kTriangles k` satisfies `LocIndep k`, with equality**: for the whole
  vertex set the independent set has size `k` and the hypothesis reads `2 * k + k = 3 * k = |V|`.
* `card_le_kTriangles`, `not_locIndep_kTriangles` — an independent set has at most `k` elements, and
  the local hypothesis is *sharp*: `LocIndep (k - 1)` fails for `k ≥ 1`.
* `card_le_of_hitsOddCycles_kTriangles` — **every set meeting every odd cycle has at least `k`
  elements** (`k` disjoint odd cycles, all fibres met).
* `closeToBipartite_iff` — the **exact** value of the conclusion on this graph:
  `CloseToBipartite m (kTriangles k) ↔ k ≤ m`.
* `not_closeToBipartite_kTriangles` — the same as an inequality.
* `card_lt_four` — four pairwise distinct elements do not fit into `Fin 3`.
* `not_branch_kTriangles`, `not_branch_completeGraph_three` — the witness (and `K_3`) is free of
  branch vertices, so it lives in the class of round 38.
* `kTriangles_optimal` — the witness needs exactly `k` deletions.
* `erdos73_lower_bound`, `no_constant_below_k` — **the lower bound `f(k) ≥ k` of Erdős #73**: for
  every `m < k` there is a graph satisfying `LocIndep k` which is not `m`-close to bipartite, so
  no constant below `k` can work in the catalogue statement.
* `erdos73On_no_branch_optimal` — **the round-38 instance is sharp**: the constant `k` of
  `erdos73On_of_no_branch` cannot be lowered on the class of graphs of maximum degree `≤ 2`, so on
  that class `f(k) = k` exactly.
* `packing_kTriangles_optimal` — the **packing** bound of `JSPProblem/Packing.lean` is attained as
  well: `k` disjoint odd cycles, and no packing of more (packing and transversal number agree in
  the class without branch vertices, which is why `k` is the right number on both sides).

## Not proved — the exact remaining gap

`jsp_000090_main` (`Erdős73` for every `k`) is **not** declared. Everything except one research
statement is now proved, and the reduction is itself a theorem:

```lean
def OddCycleErdosPosa (r : ℕ) : Prop :=
  ∃ m : ℕ, ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
    (∀ C, IsOddCycleFamily (G := G) C → C.card ≤ r) → CloseToBipartite m G

theorem erdos73_of_erdosPosa (hEP : ∀ r, OddCycleErdosPosa r) : ∀ k, Erdős73 k
```

so `jsp_000090_main` follows from `jsp_000090_main := ∀ r, OddCycleErdosPosa r` and nothing else.
`OddCycleErdosPosa` is the **Erdős–Pósa theorem for odd cycles** (Reed, Robertson, Seymour,
Thomas, *Erdős–Pósa for odd cycles*, J. Combin. Theory Ser. B 86 (2002) 99–136), a research
theorem with a 40-page proof and no Mathlib analogue. The instance `r = 0` is proved
(`oddCycleErdosPosa_zero`), and the whole bounded-odd-girth half is proved
(`shortOddCyclesErdosPosa`), so what is left is precisely the case of *unbounded* odd girth, i.e. the
Erdős–Pósa theorem proper. This is the single named missing lemma for the next rounds; see
`discovery/JSP-000090/policy.json`.

---

## Round 40 — `JSPProblem/Residue.lean`: the residue of a packed odd cycle

The active line leaves the local fan / branch-vertex / sharpness frameworks (all proved, all
imported) and develops the **global** half of the classical Erdős–Pósa proof for odd cycles: what
happens to the *residue* `deleteFinset G C` when one odd cycle of a maximum packing is deleted.

| lemma | content |
| --- | --- |
| `LocIndep.of_deleteFinset` | Erdős's local hypothesis is inherited by a residue, **with the same `k`** |
| `card_add_one_le_of_mem_maxPacking` | a packing of `G - C`, together with `C`, is a packing of `G`: `\|𝒟\| + 1 ≤ \|𝒞\|` — the strictly decreasing quantity of the classical induction |
| `LocIndep.oddCycle_packing_residue_lt` | under `LocIndep k G`, a packing of the residue of an odd cycle has at most `k - 1` members |
| `residue_hits_rest` | if `𝒞` is a maximum packing, `C ∈ 𝒞`, and `D` avoids `C`, then `D` meets one of the **other** members of `𝒞` (cross-intersection) |
| `hitsOddCycles_union_cycle`, `closeToBipartite_of_residue` | **the induction step**: `CloseToBipartite q (G - C) → CloseToBipartite (q + \|C\|) G` |
| `PackingNumberOne`, `packing_one_transversal`, `packing_one_residue_bipartite`, `closeToBipartite_of_packing_one` | the case `r = 1` in full: any two odd cycles meet ⟹ every odd cycle is a transversal and its residue is bipartite |
| **`erdos73On_of_packing_one`** | **new instance of the headline theorem**: if any two odd cycles of `G` meet and `G` has an odd cycle, `LocIndep k G` forces `CloseToBipartite ℓ G` for every `k`, with a constant **independent of `k`** (the bounded-odd-girth instance only gives `ℓ * k`, and the branch-vertex instances do not apply — `K_5` has packing number one and is full of branch vertices) |
| `IsMinimalTransversal`, `exists_minimalTransversal`, `exists_minimalTransversal_of_transversal`, `closeToBipartite_of_minimalTransversal` | the odd cycle transversal number is attained by a **minimal** transversal, which can be chosen inside any given transversal |
| `exists_private_oddCycle` | every vertex of a minimal transversal lies **alone** on an odd cycle (`D ∩ X = {x}`) |
| `card_le_of_disjoint_private_cycles` | pairwise disjoint private cycles are a packing, so at most `k` of them under `LocIndep k G` |

**Where this stops, precisely.**  The induction step is proved with the term `+|C|`: a transversal
of the residue, together with the whole cycle `C`, is a transversal of `G`.  The Reed–Robertson–
Seymour–Thomas proof replaces `|C|` by `1` — a transversal of the residue can be *absorbed* by the
transversal.  That absorption step is the single remaining piece of the classical argument, and it
is what `discovery/JSP-000090/policy.json` now names as the blocker.

---

## Round 40 (second part) — `JSPProblem/Chord.lean`: a shortest odd cycle is induced

`JSPProblem/Fan.lean`'s arc constructor `arc_isOddCycle` requires the closing vertex to be **outside
the whole cycle** (`hxC : x ∉ C`), so it says nothing about *chords*, i.e. about the edges inside a
shortest odd cycle.  `JSPProblem/Chord.lean` removes the restriction: it is enough that the closing
vertex avoids the **arc** (`hximg : ∀ t ≤ d, f (cycSucc^[t] i) ≠ x`), which is exactly what a chord
gives.

| lemma | content |
| --- | --- |
| `arcFun_inj_of_notMem`, `arc_card_of_notMem`, `arc_isOddCycle_of_notMem` | the arc constructor with a closing vertex **on** the cycle |
| **`no_chord_of_shortest_oddCycle`** | **a shortest odd cycle has no chord**: for `a ≠ b` which are not consecutive around the cycle, `f a` and `f b` are not adjacent.  A chord splits `C` into cycles of `d + 1` and `m - d + 1` vertices; these add up to the odd number `m + 2`, so exactly one is odd, and it has at most `m - 1` vertices — contradicting minimality |
| **`induceFinset_adj_of_shortest` / `isInduced_shortest_oddCycle`** | **the subgraph induced by a shortest odd cycle is exactly that cycle**: `(induceFinset G C).Adj (f a) (f b) ↔ a = cycSucc b ∨ b = cycSucc a` |
| `exists_shortest_oddCycle` | a shortest odd cycle exists whenever `G` has an odd cycle |
| `cycleOrder_odd` | every cyclic numbering of an odd cycle has odd length |

With `JSP90.card_inter_neigh_le_two` of `JSPProblem/Fan.lean` this gives the **complete local
structure of `G` at a shortest odd cycle**: inside, the cycle and nothing else; outside, each vertex
is attached through a single short arc (two vertices two steps apart).  That is the base case of the
induction whose inductive step `JSPProblem/Residue.lean` proves and whose absorbing step is the
remaining blocker.

---

## Round 42 — `JSPProblem/Separator.lean`: the 2-cut decomposition

Rounds 35–41 produced *local* structure (the fan arc, the branch vertices, the residue of a packed
cycle, the chords of a shortest odd cycle) and instances of the headline theorem for special
classes.  What none of them has is a **global** structural tool.  `JSPProblem/Separator.lean` adds
the one every classical proof of the Erdős–Pósa property for odd cycles needs: the decomposition of
`G` along a vertex cut of size two.  It is formalised *without* any connectivity API (none of it is
in the pinned import slice) — a split is a partition of `V \ {a,b}` into `t ≥ 2` nonempty parts
which are pairwise **anticomplete**, i.e. `{a, b}` is a vertex cut:

```lean
structure VertexSplit (G : SimpleGraph V) (a b : V) (t : ℕ) where
  parts : Fin t → Finset V
  hne : ∀ i : Fin t, (parts i).Nonempty
  hdisj : ∀ i j : Fin t, i ≠ j → parts i ∩ parts j = ∅
  hcov : ∀ x : V, x = a ∨ x = b ∨ (∃ i : Fin t, x ∈ parts i)
  hanti : ∀ i j : Fin t, i ≠ j → ∀ x ∈ parts i, ∀ y ∈ parts j, ¬ G.Adj x y
  hnadj : ¬ G.Adj a b
```

| lemma | content |
| --- | --- |
| `VertexSplit.mem_part_of_adj` | neighbours stay in the same part: the parts behave like the connected components of `G - {a,b}` |
| **`VertexSplit.cycle_subset_parts`** | **a cycle of `G` which avoids the two vertices of the cut lies in a single part.**  The proof walks once around the cycle (`g t = f (t mod m)`, consecutive vertices adjacent) |
| `VertexSplit.oddCycle_piece_or_avoid` | every odd cycle of `G` is contained in a *piece* `T_i ∪ {a,b}` or meets the cut — **an odd cycle cannot use two parts at once** |
| **`VertexSplit.part_unique`, `oddCycle_piece_unique`** | and it lies in **exactly one** piece, which is the bookkeeping an Erdős–Pósa argument along a separator needs to charge a cycle to a single piece |
| **`VertexSplit.hitsOddCycles`** | a set meeting every odd cycle of every piece, together with the two vertices of the cut, is an odd cycle transversal of `G` |
| **`VertexSplit.exists_transversal`** | if every piece has an odd cycle transversal of at most `m` vertices then `G` has one of at most `2 + m * t` vertices |
| **`erdos73On_of_split`** | **new instance of the headline theorem**: Erdős #73 is *closed under 2-cut decomposition*.  If `LocIndep k` forces `CloseToBipartite m` on the pieces `T_i ∪ {a,b}`, then it forces `CloseToBipartite (m * t + 2)` on `G`.  This is the reduction "the theorem reduces to the 3-connected case", and the step an induction on the Erdős–Pósa function must make |
| `Good2`, `Good2On`, `flipCol`, `Good2On.flip`, `Good2.isBipartite`, `exists_good2` | 2-colourings in the `Bool` convention, and rescaling a 2-colouring at one vertex |
| **`VertexSplit.isBipartite_of_split`** | **the 2-cut parity lemma**: if every piece is bipartite and the two vertices of the cut carry the **same** colour in every piece, then `G` is bipartite.  The colouring is glued from the pieces — distinct parts are anticomplete, and `a`, `b` are the only vertices two pieces can share |
| **`VertexSplit.not_isBipartite_of_split`** | contraposed: if `G` is not bipartite and every piece is bipartite, **no** 2-colouring of the pieces can agree on `a` and `b`.  A non-bipartite `G` is glued along the cut only — the classical reason the 3-connected case is the hard one |
| `IsOddCycleFamily.of_induceFinset`, `packing_le_of_split` | the **packing** half: the Erdős–Pósa hypothesis (a bound on the odd cycle packing number) restricts to every piece, so an induction along a 2-cut decomposition goes through |
| **`erdos73On_of_split_of_bounded_branch`** | **second new instance of the headline theorem**: the composition of `erdos73On_of_split` with the branch-vertex instance of round 38.  If `G` has a 2-cut whose `t` pieces have at most `m` branch vertices each, then `LocIndep k G` forces `CloseToBipartite (2 + (m + k) * t) G` — still with **no bound on the odd girth** |

**Where this stops, precisely.**  The decomposition charges the two vertices of the cut in full
(`+ 2`); the sharp step would charge one of them, and needs the companion of `cycle_subset_parts`
saying that a cycle meeting *exactly one* vertex of the cut lies in a piece.  The packing half is
only the restriction of the bound to the pieces, not the full decomposition
`card ≤ 2 + t * r` of a packing of `G` into packings of the pieces.  Most importantly this is a
**reduction, not the theorem**: it shows that the whole difficulty of `OddCycleErdosPosa` sits in
the graphs with no 2-cut, whose structure is still not controlled here.

---

## Round 43 — `JSPProblem/Count.lean`: the counting half of the 2-cut decomposition

`JSPProblem/Separator.lean` (round 42) made Erdős #73 *closed under 2-cut decomposition*, with the
constant `m * t + 2` — one transversal per piece plus the two vertices of the cut.  It named two
gaps, both of them **counting** statements about the same decomposition, and this file closes them.

### 1. A cycle meeting exactly one vertex of the cut lies in a half-piece

| lemma | content |
| --- | --- |
| `VertexSplit.swap` | a split at `a, b` is a split at `b, a` (the parts are the same) |
| **`VertexSplit.cycle_subset_piece_of_not_mem`** | **a cycle containing `a` but not `b` lies in a single half-piece `T_i ∪ {a}`**.  The walk around the cycle starts at the vertex *after* `a`: in the cyclic order of `JSPProblem/Branch.lean` the vertex `a` sits `m − 1` steps back, so the first `m − 1` steps visit every vertex of the cycle except `a` exactly once, and consecutive vertices are adjacent and avoid the cut, so `VertexSplit.mem_part_of_adj` keeps them in one part |
| `VertexSplit.cycle_subset_piece_of_not_mem'` | the same for `b` (via `sp.swap`) |
| **`VertexSplit.oddCycle_half_or_both`** | **the complete local structure at a 2-cut**: every odd cycle of `G` is contained in a half-piece `T_i ∪ {a}` or `T_i ∪ {b}`, or contains **both** vertices of the cut.  Only cycles using both `a` and `b` are "global" |

### 2. The counting lemma: at most `k` parts cost anything

| lemma | content |
| --- | --- |
| `IsBipartite.induceFinset_subset` | a bipartite induced subgraph of a bipartite induced subgraph is bipartite |
| `VertexSplit.nonBipartiteParts` | the parts `T_i` whose induced subgraph is **not** bipartite |
| `oddCycle_subset_induceFinset` | every vertex of an odd cycle of `G[s]` lies in `s` (the membership half of `IsOddCycle.induceFinset`) |
| `VertexSplit.exists_oddCycle_of_mem_nonBipartiteParts` | a non-bipartite part contains an odd cycle, which lies in the part (so it avoids `a` and `b`) |
| **`VertexSplit.card_nonBipartiteParts_le`** | **under `LocIndep k G`, at most `k` of the `t` parts of a split are non-bipartite**: the non-bipartite parts are pairwise disjoint and each carries an odd cycle, so choosing one odd cycle each gives a packing of `G`, and Erdős's local hypothesis admits at most `k` |
| **`VertexSplit.exists_transversal_nonBipartite`** | if every non-bipartite piece is `CloseToBipartite m`, then `G` has an odd cycle transversal of at most `2 + ∑_{i ∈ J} m` vertices — bipartite parts contribute nothing, because an odd cycle in a piece with a bipartite *part* must use one of the two vertices of the cut, which are charged anyway |
| **`closeToBipartite_of_split_of_bounded_pieces`** | with `LocIndep k G` that is `CloseToBipartite (2 + m * k) G` |
| **`erdos73On_of_split_of_bounded_pieces`** | **NEW INSTANCE OF THE HEADLINE THEOREM, strictly stronger than round 42's `erdos73On_of_split`**: if `LocIndep k` forces `CloseToBipartite m` in every piece `T_i ∪ {a,b}`, then it forces `CloseToBipartite (2 + m * k) G`.  The constant no longer depends on the number `t` of pieces, and **no bound on the odd girth** is used |
| **`erdos73On_of_split_of_bounded_branch_packing`** | the same improvement on the composition with the branch-vertex instance of round 38: `2 + (m + k) * k` instead of round 42's `2 + (m + k) * t` |

### 3. The full packing decomposition

| lemma | content |
| --- | --- |
| `card_le_one_of_common` | a pairwise vertex-disjoint family of finsets which all contain one vertex has at most one member |
| **`packing_le_of_split_decomposition`** | **if every packing of odd cycles of every part `T_i` has at most `r` members, then every packing of odd cycles of `G` has at most `2 + t * r` members.**  A packing of `G` splits into the members meeting the two vertices of the cut — at most **two** of them, by `card_le_one_of_common` — and, for each part, the members avoiding the cut, which lie in a single part by `cycle_subset_parts` and form a packing of the induced subgraph on that part.  This is the direction round 42 named as missing, and it is what an Erdős–Pósa induction along a 2-cut needs to bound the packing number of `G` from **above** |

**Where this stops, precisely.**  The decomposition is now free of `t`, and both halves of the
2-cut bookkeeping (transversal and packing) are proved.  What is still missing is *global*: the
number of 2-cuts of `G`, i.e. the possibility of a long chain of nested 2-cuts, is not bounded here,
so the reduction to the 3-connected case cannot yet be turned into an induction.  That is the
Mader/Reed–Robertson–Seymour–Thomas structure step, and it remains the blocker for
`OddCycleErdosPosa r` (see `discovery/JSP-000090/policy.json`).

### 4. The precise reduction to the 3-connected case

The counting half makes the remaining gap a *single* statement, and this file proves the equivalence
formally.

| item | content |
| --- | --- |
| `HasProperSplit` / `NoProperSplit` | `G` has (resp. has not) a 2-cut into `t ≥ 2` anticomplete parts |
| `SplitDepth G d` | `G` can be decomposed by at most `d` successive 2-cuts into graphs with **no** proper 2-cut (`d = 0` is `NoProperSplit G`; at each step either `G` is 2-cut-free, or `G` has a proper 2-cut every piece of which has depth `< d`) |
| `splitBound m p d`, `le_splitBound` | the bound obtained by decomposing with `d` successive cuts: `Nat.rec (m p) (fun _ b => max (m p) (2 + p * b)) d` — one `+2` and one `p ×` per level, because at most `p` pieces are non-bipartite |
| `VertexSplit.card_nonBipartiteParts_le_pack` | the counting lemma with a **packing bound** instead of `LocIndep k G` |
| `closeToBipartite_of_split_of_bounded_pieces_pack` | the 2-cut decomposition in pure Erdős–Pósa form: packing `≤ p` + `CloseToBipartite m` on the non-bipartite pieces ⟹ `CloseToBipartite (2 + m * p)` |
| **`erdos73_of_noSplit2_of_bounded_splitDepth`** | **THE PRECISE REDUCTION: Erdős–Pósa for odd cycles follows from (i) the 2-cut-free case and (ii) a uniform bound on the length of chains of 2-cuts.**  If for every packing number `p` a graph with no proper 2-cut and packing number `≤ p` is `CloseToBipartite (m p)`, and every graph with packing number `≤ p` has `SplitDepth ≤ d`, then every graph with packing number `≤ p` is `CloseToBipartite (splitBound m p d)` |

Since `erdos73_of_erdosPosa` is proved, this says exactly: **`jsp_000090_main` follows from the
2-cut-free case of Erdős–Pósa together with a uniform bound on the number of 2-cuts of `G`.**
Everything else the classical proof needs — the local structure at a shortest odd cycle
(`Chord.lean`, `Fan.lean`), the residue induction (`Residue.lean`), the 2-cut decomposition and its
counting half (`Separator.lean`, `Count.lean`) — is proved and enters only through the two
hypotheses of that theorem.  The bound on the number of 2-cuts is the Mader / Reed–Robertson–
Seymour–Thomas structure step, absent from the pinned Mathlib import slice, and it is the single
concrete missing lemma recorded in `discovery/JSP-000090/policy.json`.

---

## Round 44 — `JSPProblem/Weight.lean`: the weighted Erdős–Pósa theorem

This round leaves the 2-cut framework (rounds 42–43, proved, imported) and attacks the residue
induction of `Residue.lean` **from the other side**: instead of trying to repair the `+|C|` cost of
`closeToBipartite_of_residue` by absorption, it *sums* that cost over a whole packing and inducts on
the running total.

### 1. The weighted Erdős–Pósa theorem

| item | content |
| --- | --- |
| `PackingWeight 𝒞 = ∑ C ∈ 𝒞, \|C\|` | the **weight** of a family of cycles: the total number of vertices it covers, i.e. the cost the residue induction pays for it |
| `WeightLe G L` | every packing of odd cycles of `G` covers at most `L` vertices in total |
| `insert_oddCycle_of_disjoint` | a packing together with an odd cycle **disjoint from all of its members** is a packing — the weight version of `insert_oddCycle_of_delete` |
| **`closeToBipartite_of_weightLe`** | **if every packing of odd cycles of `G` has total length at most `L`, then `G` is `CloseToBipartite L`** — strong induction on `L`: the residue of an odd cycle inherits the bound `L - \|C\|` (a packing of the residue together with `C` is a packing of `G`), and `closeToBipartite_of_residue` closes the step |
| `IsMaxWeightPacking`, `exists_maxWeightPacking` | a packing of maximum **weight** exists (by `Finset.exists_max_image`) |
| `hitsOddCycles_of_maxWeightFamily` | the union of a maximum-weight packing **is** an odd cycle transversal |
| **`isBipartite_delete_of_maxWeightFamily`** | **the residue of a maximum-weight packing is bipartite** — an odd cycle of the residue is disjoint from every member, so it could be added and increase the weight |
| `closeToBipartite_of_maxWeightPacking` | **the odd cycle transversal number of `G` is at most the weight of a maximum-weight packing of odd cycles** |

This is strictly more general than round 40's `shortOddCycles_transversal`, which needs a bound on
the length of *every* individual odd cycle: only the **total** length of a packing is controlled, and
the packing used is the heaviest one rather than the largest one.

### 2. Instances of the headline theorem

| item | content |
| --- | --- |
| `packingWeight_le` | the weight of a packing, from a global length bound and a packing number: `≤ ℓ * r` |
| **`erdos73On_of_bounded_packing_weight`** | **a new instance of the headline theorem**: `LocIndep k G` + every packing of odd cycles covers at most `L` vertices ⟹ `CloseToBipartite L G`.  A strictly weaker hypothesis than bounded odd girth: no bound on the odd girth, none on the number of branch vertices, and the *total* length of a packing is what matters |
| `erdos73On_of_bounded_odd_circumference` | the `ℓ * k` instance re-derived as a corollary of the weighted theorem |
| `closeToBipartite_iff_completeGraph_add_two` | **on complete graphs the conclusion is exact**: `CloseToBipartite m (K_n) ↔ n ≤ m + 2` (a complete graph is bipartite exactly when it has at most two vertices) |
| `erdos73On_completeGraph` | the resulting instance: `LocIndep k (K_n)` forces `n ≤ k + 2`, and `K_{k+2}` is `k`-close to bipartite but not `m`-close for any `m < k` — a second witness for `f(k) ≥ k` |

### 3. The naive `+1` absorption step is false — machine-checked (`K_5`)

The step the classical proof wants is

```
CloseToBipartite q (G - C)  →  CloseToBipartite (q + 1) G        (C an odd cycle of G)
```

and it is **false as stated**:

| item | content |
| --- | --- |
| `isOddCycle_completeGraph_five_triangle` | `{0,1,2}` is an odd cycle of `K_5` |
| `isBipartite_deleteFinset_of_card_le_two` | a residue of at most two vertices is bipartite |
| `closeToBipartite_zero_deleteFinset_completeGraph_five` | `CloseToBipartite 0 (K_5 - {0,1,2})` — the hypothesis holds with `q = 0`, the residue being `K_2` |
| `not_closeToBipartite_one_completeGraph_five` | `¬ CloseToBipartite 1 (K_5)` — deleting one vertex of `K_5` leaves a complete graph on at least four vertices, which is not bipartite (`not_isBipartite_induceFinset_of_clique`) |
| **`absorption_step_fails`** | the two together: the `+ 1` step fails for `G = K_5`, `C = {0,1,2}` |
| `locIndep_completeGraph_five_three` | `LocIndep 3 (K_5)` holds, so the failure is **inside** the range of the headline theorem, not on a graph excluded by it |

The cause is visible in the witness and is exactly the hypothesis a correct absorption lemma needs:
in `K_5` every vertex outside `C` meets the triangle in **all three** of its vertices, whereas at a
shortest odd cycle of length `≥ 5` an outside vertex meets the cycle in at most **two** of its
vertices, two steps apart (`JSPProblem.card_inter_neigh_le_two`, `JSPProblem.shortArc_of_shortest`
in `Fan.lean`) — the local structure the classical absorption uses.  This is the concrete form of
the blocker recorded in `discovery/JSP-000090/policy.json`.

---

## Round 46 — `JSPProblem/Optimal.lean`: the identity case of Erdős–Pósa, proved and sharp

Round 46 attacks the Erdős–Pósa theorem for odd cycles from the **sharpness** side instead of from
a structural hypothesis.  On the class of graphs in which **any two distinct odd cycles are
vertex-disjoint**, the odd cycle transversal number and the odd cycle packing number are the same
number, so Erdős–Pósa holds there with the **identity function** — proved here, not quoted.

### The class

```lean
def OddCyclesDisjoint (G : SimpleGraph V) : Prop :=
  ∀ C D : Finset V, IsOddCycle G C → IsOddCycle G D → C = D ∨ C ∩ D = ∅
```

A hypothesis about the intersection pattern of the odd cycles alone: no bound on degrees, no bound
on the odd girth, no counting bound.

### The identity Erdős–Pósa theorem

```lean
theorem closeToBipartite_iff_packingLe (h : OddCyclesDisjoint G) (m : ℕ) :
    CloseToBipartite m G ↔ ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ m
```

Three steps, each a theorem of the file:

| step | theorem | content |
| --- | --- | --- |
| maximality becomes exactness | `mem_of_oddCycle_of_maxPacking` | a maximum packing meets every odd cycle, and in this class a member it meets is *equal* to it — so every odd cycle of `G` is a member of every maximum packing |
| a transversal of size `|C|` | `exists_transversal_onePerMember` | one vertex per member of a maximum packing (`Classical.choose` of its nonemptiness); injectivity is exactly the disjointness of the members |
| the converse counting | `card_le_of_hitsOddCycles_of_disjointFamily` | a transversal of a family of pairwise disjoint finsets is at least as large as the family |

### A new instance of the headline theorem, with the optimal constant `f(k) = k`

```lean
theorem erdos73On_of_disjoint_oddCycles (k : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W),
      LocIndep k G → OddCyclesDisjoint G → CloseToBipartite k G
```

and its sharpness on the **whole class** — the least Erdős constant there is exactly `k`:

```lean
theorem erdos73On_disjoint_oddCycles_iff (k m : ℕ) :
    (∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W),
        LocIndep k G → OddCyclesDisjoint G → CloseToBipartite m G) ↔ k ≤ m
```

The forward direction needs `oddCycle_eq_tri_of_kTriangles` (the odd cycles of `kTriangles k` are
exactly its `k` fibres: consecutive vertices of a cycle are adjacent, hence lie in one fibre, and
the cyclic successor reaches every position) together with `closeToBipartite_iff` of
`JSPProblem/Sharp.lean`.

### The composition lemma that was missing: anticomplete pieces

```lean
def Anticover (G : SimpleGraph V) (A B : Finset V) : Prop :=
  (∀ ⦃x : V⦄, x ∈ A → x ∉ B) ∧ A ∪ B = Finset.univ ∧ ∀ v ∈ A, ∀ w ∈ B, ¬ G.Adj v w

theorem closeToBipartite_of_anticover {m₁ m₂ : ℕ} (h : Anticover G A B)
    (h₁ : CloseToBipartite m₁ (induceFinset G A))
    (h₂ : CloseToBipartite m₂ (induceFinset G B)) : CloseToBipartite (m₁ + m₂) G
```

Rounds 42–43 compose the conclusion along **2-cuts**, where the two sides share the two cut vertices
and the constant pays an extra `+2`.  Here the two sides share nothing and the constants simply
add, so the instances compose: `erdos73On_of_anticover`.

### Machine-checked negative result: the identity function does **not** extend

| item | content |
| --- | --- |
| `inter_nonempty_of_oddCycles_card` | any two odd cycles of a complete graph on at most `5` vertices meet (`|C| + |D| = |C ∩ D| + |C ∪ D|`, `|C|, |D| ≥ 3`, `|C ∪ D| ≤ 5`) |
| `packing_card_le_one_completeGraph_five` | every packing of odd cycles of `K_5` has at most **one** member |
| `isOddCycle_fiveCycle` | the Hamiltonian `5`-cycle `0-1-2-3-4-0` is an odd cycle of `K_5` |
| `not_oddCyclesDisjoint_completeGraph_five` | `K_5` is **not** in the class: the triangle `{0,1,2}` and the `5`-cycle share the two vertices `0`, `1` |
| **`class_hypothesis_is_necessary`** | `LocIndep 3 (K_5)` holds, every packing has at most one member, and `K_5` is not `2`-close to bipartite — the sole reason is the line above |
| **`packingNumber_one_not_enough`** | a packing bound does **not** imply `CloseToBipartite 2 (K_5)`: `τ ≠ ν` in general |

So the candidate route "prove Erdős–Pósa for odd cycles by showing that the transversal number
equals the packing number" is **refuted**, and the exact remaining content is the payment for the
overlap of a pair of odd cycles.  This is the same `K_5` obstruction as
`JSPProblem.absorption_step_fails` (round 44), now seen as a statement about the Erdős–Pósa
function itself.

---

## Round 64 — `JSPProblem/CutTriangle.lean`: the cut triangle, and Erdős #73 from two local
statements

Rounds 62–63 built the *instance* half of a reduction of Erdős #73 to its triangle-free case
(`closeToBipartite_of_anticoverCut`: a cut at a triangle, constant `3 + k * m`) and named two
gaps.  This file closes both and **runs the induction**, so that the whole remaining content of
JSP-000090 is now a pair of statements about *classes* of graphs.

### 1. The deficiency of an induced subgraph

| item | content |
| --- | --- |
| `indepCard_induceFinset_of_subset` | `α(G[U], X) = α(G, X)` for `X ⊆ U` |
| `mem_indepSets_union_sdiff` | if `S ⊆ Y ∩ U` is independent in `G[U]`, then `S ∪ (Y \ U) ∈ indepSets (G[U]) Y`: the vertices outside `U` are **isolated** in `G[U]` |
| **`indepCard_induceFinset_inter_add_sdiff`** | **`α(G[U], Y) = α(G[U], Y ∩ U) + |Y \ U|`** |
| `defOf_induceFinset_inter_le` | `|Y| - 2 α(G[U], Y) ≤ |Y ∩ U| - 2 α(G[U], Y ∩ U)` |
| **`maxDef_eq_maxDefIn_induceFinset`** | **`MaxDef (induceFinset G U) = maxDefIn G U`** — the deficiency of the graph `G[U]`, read over all subsets of the ambient vertex type, is the deficiency *inside `U`* |
| `locIndep_induceFinset_of_maxDefIn_le` | a bound on the deficiency inside a vertex set is a `LocIndep` hypothesis on the induced subgraph |

This is the answer to the correction round 63 recorded against the unrestricted
`maxDefIn (induceFinset G Q) V`, and it is what lets an induction on Erdős's parameter run over
the *pieces* of a cut.

### 2. A cut triangle

| item | content |
| --- | --- |
| `anticoverCoverFamily_compPieces_sub` | the components of a subgraph `H ≤ G`, restricted to a vertex set on which `H` and `G` have the same edges, are pairwise disjoint and pairwise anticomplete **in `G`** |
| **`CutTriangle G T`** | `T.card = 3` and **no edge of `G` joins `T` to `V \ T`** |
| `cutPieces G T` | the components of `G[V \ T]`, each **intersected with `V \ T`** |
| `cutPieces_sub`, `mem_cutPieces`, `anticoverCoverFamily_cutPieces` | the pieces avoid `T` by construction, are pairwise disjoint/anticomplete, and cover `V \ T` |
| **`anticoverCut_of_cutTriangle`** | they are the `AnticoverCut` of `JSPProblem/Cut.lean` at that triangle |
| **`closeToBipartite_of_cutTriangle`** | **a new instance of the headline theorem at a canonical cut:** `LocIndep k G` + every component of `G[V \ T]` is `m`-close to bipartite ⟹ `CloseToBipartite (3 + k * m) G` |

The intersection of each component with `V \ T` is what makes the pieces avoid `T` *by
construction*: the components of `deleteFinset G T` do **not** form an `AnticoverCut` (a component
may contain a vertex of `T` that has a neighbour outside `T`), which is the gap round 63 recorded.
Here the gap is replaced by a hypothesis, and no induction on `SimpleGraph.Walk` is needed.

### 3. The descent

| item | content |
| --- | --- |
| **`maxDefIn_le_of_cutPiece`** | at a cut triangle, `1 + maxDefIn G Q ≤ k` for every piece `Q` |
| **`locIndep_piece_of_cutTriangle`** | `LocIndep k G`, `Q ∈ cutPieces G T` ⟹ `LocIndep (k - 1) (induceFinset G Q)` |

### 4. The reduction

```lean
def cutBound : ℕ → ℕ          -- cutBound 0 = 1,  cutBound (k + 1) = 3 + (k + 1) * cutBound k
def TriangleFreeErdős73       -- Erdős #73 for triangle-free graphs, with the constant cutBound
def CutTriangleErdős73        -- LocIndep k G, k ≥ 1 ⟹ a cut triangle, or CloseToBipartite (cutBound k) G

theorem erdos73_of_triangleFree (htf : TriangleFreeErdős73) (hc : CutTriangleErdős73) :
    ∀ k, Erdős73 k
```

**Erdős Problem #73, in full, from two local statements**, by induction on `k` alone.  Neither
hypothesis mentions a packing number, a transversal, an odd girth, a packing weight or a number of
branch vertices; both are statements about a class of graphs.

### 5. A negative result and a correction

* `not_cutTriangle_completeGraph_four` — in `K_4` no `3`-clique cuts the graph, so `CutTriangle` is
  a hypothesis and not a theorem (the `K_4`/`K_5` obstruction of rounds 44 and 63, machine-checked
  at the level of the new predicate).  `erdos73_of_triangleFree_of_allTrianglesCut` closes the
  reduction unconditionally on the class of graphs whose `3`-cliques all cut.
* **The constant `f k = 4 ^ k` planned in rounds 62–63 is impossible**: the proved instance costs
  `3 + k * f (k - 1)`, and `3 + k * 4 ^ (k - 1) > 4 ^ k` for `k ≥ 5`.  The recurrence actually
  forced by the instance is `f (k + 1) = 3 + (k + 1) * f k`, i.e. `cutBound`.

### Not proved

`JSP90.TriangleFreeOnly` — Erdős #73 for triangle-free graphs — and nothing else.  Round 68 proved
`JSP90.erdos73_iff_triangleFreeOnly`, so this single class-restricted statement is the whole
remaining content, and round 69 localised it further: it is now equivalent
(`JSP90.erdos73_iff_fanErdős73`) to a statement about **one odd cycle and the set of vertices that
touch it** (`JSP90.FanErdős73`), with no connectivity, no packing number, no odd girth and no bound
on the size of the boundary.

* `JSPProblem.Class` — **the classes of the fan, the parity of two classes, and the "no short cut"
  lemma** (round 70).  `JSP90.fanClass G C a` is the set of fan vertices attached to `a`, and
  `JSP90.isIndepSet_fanClass` makes it an independent set.  The parity core of the class structure
  is `JSP90.not_isOddCycle_of_subset_fanClass_union`: **an odd cycle of `G` is never contained in
  two classes**.  With `JSP90.farFan G C a b` (the part of the fan attached to neither `a` nor `b`)
  this gives `JSP90.hitsOddCycles_farFan` and the **counting lemma of the fan**
  `JSP90.card_farFan_ge_of_disjoint_oddCycles`: a packing of `j` odd cycles inside the fan needs `j`
  vertices of the far part, for *every* pair `a, b ∈ C` — the shape of the classical half-integral
  argument, as a Lean theorem.  `JSP90.erdos73On_of_fan_twoClass` is a new instance of the headline
  theorem along this axis.  The file also supplies the **two-vertex arc** constructor missing from
  `JSPProblem.Fan`: `JSP90.arcFun2`, `JSP90.arc2_isOddCycle` (closing an even arc through two
  adjacent outside vertices gives a simple odd cycle of exactly `arc + 3` vertices) and the
  classical **"no short cut" lemma** `JSP90.not_adj_of_attach_far` (two fan vertices of a shortest
  odd cycle whose attachment points are `4` to `m - 5` steps apart are never adjacent — no
  triangle-free hypothesis needed).
* `JSPProblem.Petersen`: `p9`, the Petersen graph with one vertex deleted, and **the improved lower
  bound `f(k) >= 2 k`** (`JSP90.erdos73_lower_bound_two`, `JSP90.no_constant_below_two_k`), which
  strictly improves `JSPProblem/Sharp.lean`'s `f(k) >= k`: `JSP90.locIndep_one_p9` (deficiency of
  `p9` is exactly one, by exhaustive decision), `JSP90.triangleFree_p9`, `JSP90.not_closeToBipartite_one_p9`,
  `JSP90.closeToBipartite_two_p9` (least odd cycle transversal of `p9` is exactly two),
  `JSP90.locIndep_p9Family` and `JSP90.closeToBipartite_p9Family_iff`
  (`CloseToBipartite m (p9Family k) <-> 2 * k <= m`).
* `JSPProblem/Layer`: the **internal-degree axis** (round 77).  `JSP90.InternalDegree G S r` asks
  only that every vertex outside `S` has at most `r` neighbours outside `S` — strictly weaker than
  the total-degree hypotheses of rounds 38 and 74 — and `JSP90.erdos73On_of_internalDegree_three`
  is a new instance of the headline theorem from it, with the `k`-term sharp
  (`JSP90.no_constant_below_internalDegree_three`).  The file also names the bounded-degree
  localisation `JSP90.BoundedDegreeErdős73 g r` and the **subcubic** statement
  `JSP90.SubcubicErdős73 g`, proves the levels `k = 0` and `r = 2`
  (`JSP90.erdos73On_boundedDegree_zero`, `JSP90.boundedDegreeErdős73_two`), and the tight-witness
  theory (`JSP90.exists_tight_of_maxDef_ne_zero`, `JSP90.indepCard_add_one_of_notMem_of_tight`).
* `JSPProblem/Subcubic`: the **SUBCUBIC axis** (round 78, this file's newest module).  Everything
  rests on one numerical fact: a vertex of an odd cycle already uses two of its at most three
  neighbours.  Hence (i) a vertex of an odd cycle has at most **one** neighbour outside it, so
  `|∂C| ≤ |C|` and `|N[C]| ≤ 2 |C|` (`JSP90.card_le_one_outerNeigh_oddCycle`,
  `JSP90.card_boundary_le_card_oddCycle`, `JSP90.card_neighClosed_le_two_mul_card_oddCycle`); (ii)
  **two odd cycles that meet share a cycle edge of the first**
  (`JSP90.CycleOrder.exists_adj_mem_inter`, and `JSP90.exists_ne_two_mem_inter_oddCycle`), because
  two `2`-subsets of the three edges at a common vertex intersect; (iii) for a cycle of odd length
  the vertices at **even positions** meet every edge of the cycle
  (`JSP90.evenIdx`, `JSP90.evenCover`, `JSP90.exists_mem_evenCover_of_cycleEdge`,
  `JSP90.card_evenCover`), and combining (ii) and (iii):
  **`JSP90.hitsOddCycles_of_inter`** — if every odd cycle of a subcubic graph meets one fixed odd
  cycle `C`, some set of at most `(C.card + 1) / 2` vertices of `C` meets every odd cycle.  The
  **new instance of the headline theorem** is
  `JSP90.closeToBipartite_of_subcubic_of_shortOddCycles`: a subcubic graph of `LocIndep k` whose odd
  cycles have at most `ℓ` vertices is `k * ((ℓ + 1) / 2)`-close to bipartite — better than the
  constant `ℓ k` of `JSP90.erdos73On_of_bounded_odd_girth` — with the `k = 1` case free of `k`
  (`JSP90.closeToBipartite_of_subcubic_of_locIndep_one_of_shortOddCycle`, and
  `JSP90.closeToBipartite_of_subcubic_of_locIndep_one_of_three` = `CloseToBipartite 2 G` when every
  odd cycle is a triangle).  The constant `1` at `k = 1` is **refuted**
  (`JSP90.subcubic_constant_ne_one`, `JSP90.not_subcubicErdős73_one`, using
  `JSP90.maxDegLe_p9` and round 76's `p9`), and the remaining statement is isolated as
  `JSP90.SubcubicPackingOne` (two vertices suffice in a subcubic graph whose odd cycles pairwise
  meet) with its reduction `JSP90.erdos73On_subcubic_one_of_packingOne`.  The file also re-proves
  the `MaxDeg ≤ 2` level in the total-degree vocabulary, `JSP90.erdos73On_one_of_maxDegLe_two`.

## Round 80 — `JSPProblem/Cover.lean`: the **SHARED-EDGE axis** — the odd-girth bound with no degree
## bound, the packing-number-one case, and the refutation of round 78's closing plan

Round 78 proved the new instance `closeToBipartite_of_subcubic_of_shortOddCycles` under a **degree**
hypothesis (`MaxDegLe G 3`) and closed its policy with a *plan*: "for a shortest odd cycle `C` of a
subcubic graph, the **active edges** — the edges of `C` lying in another odd cycle — are covered by two
vertices of `C`".  This round (the twenty-seventh attack family) shows that plan to be **false** by
machine check and replaces it by the hypothesis the argument really uses.

### 1. The degree-free hypothesis

`JSP90.ShareCycleEdge G`: *two odd cycles of `G` that meet share a cycle edge of the first*, in every
cyclic ordering of the first.  No degree, no girth, no packing.  `JSP90.ShareCycleEdge
.lemma_of_maxDegLe_three` derives it from subcubicity (round 78), so it is the weaker of the two, and
`JSP90.exists_ne_two_mem_inter_of_shareCycleEdge` is the degree-free form of round 78's
`exists_ne_two_mem_inter_oddCycle`.

### 2. A new instance of the headline theorem, with no degree bound

`JSP90.erdos73On_of_shareCycleEdge_of_shortOddCycles` (`k * ((ℓ + 1) / 2)`), i.e.
`JSP90.closeToBipartite_of_shareCycleEdge_of_shortOddCycles`, with the `k = 1` level
(`…_shortOddCycle_one`) and the `ℓ = 3` level `CloseToBipartite (2 * k) G`
(`JSP90.closeToBipartite_of_shareCycleEdge_of_three`, `JSP90.erdos73On_shareCycleEdge_of_three`).  The
constant is round 78's (better than the general `ℓ k` of `erdos73On_of_bounded_odd_girth`) under a
strictly weaker hypothesis; `JSP90.closeToBipartite_of_maxDegLe_three_of_shortOddCycles` records that
round 78's instance is the special case.

### 3. The packing-number-one case, with **no** local hypothesis

`JSP90.closeToBipartite_of_shareCycleEdge_of_packingOne`: if **every two odd cycles meet**, then
`CloseToBipartite ((ℓ + 1) / 2) G` — Erdős's hypothesis appears nowhere (`LocIndep 1` enters only
through `inter_oddCycle_of_locIndep_one`).  In particular

> `JSP90.closeToBipartite_of_shareCycleEdge_of_packingOne_of_three`: a graph whose odd cycles are all
> triangles, pairwise meet, and share a cycle edge whenever they meet, is `2`-close to bipartite,

a new instance of the headline theorem on a class carrying **no degree bound and no local
hypothesis**; the subcubic case is
`JSP90.closeToBipartite_of_maxDegLe_three_of_packingOne_of_three`.  The constant `2` is **sharp** and
machine-checked: `K₄` satisfies all the hypotheses (`JSP90.shareCycleEdge_completeGraph_four`,
`JSP90.card_le_three_of_oddCycle_completeGraph_four`,
`JSP90.inter_oddCycle_completeGraph_four`, `JSP90.maxDegLe_completeGraph_four`) and
`JSP90.not_closeToBipartite_one_K4` says it is not one vertex away from bipartite; it is a
`LocIndep 2` graph (`JSP90.locIndep_two_K4`).

### 4. The active edges, and the refutation of round 78's plan

`JSP90.ActiveEdges o` is the finset of **cycle edges** of `C` (in the cyclic ordering `o`) that lie in
another odd cycle.  `JSP90.hitsOddCycles_of_activeEdgeCover_of_shareCycleEdge` and
`JSP90.closeToBipartite_of_activeEdgeCover_of_shareCycleEdge` are the criterion the plan aimed at: *a
vertex cover of the active edges of `C`, sitting inside `C`, is a transversal of the whole graph*;
`JSP90.evenCover_cover_activeEdges` and `JSP90.hitsOddCycles_of_activeEdgeCover_evenCover` verify it at
the even cover.

In the Petersen graph with one vertex deleted (`p9`, subcubic by `JSP90.maxDegLe_p9`, odd girth `5` by
the new `JSP90.card_ge_five_of_oddCycle_p9`, so `Cb` is a shortest odd cycle):

* **all five** cycle edges of `Cb` are active — `JSP90.each_activeCb_active` (they lie in `Ca`, `Ca`,
  `Cc`, `Cd`, `Cd`), and `JSP90.activeCb_eq_cycleEdges` puts this in the vocabulary of `ActiveEdges`;
* **no** two vertices of `Cb` cover them: `JSP90.not_two_cover_of_Cb` (the conjecture
  `JSP90.TwoCoverCycleEdges` in its own order-based formulation) and `JSP90.no_two_cover_activeCb`
  (a `decide` over all `3 ^ 9 = 19 683` subsets);
* three are needed (`JSP90.card_vertexCover_activeCb`) and three suffice
  (`JSP90.exists_cover_activeCb_three`).

So the vertex-cover number of the active edges of a shortest odd cycle of a subcubic graph is **three,
not two** (`JSP90.not_vertexCover_two_of_activeCb`): the `k = 1` subcubic constant `2`, which `p9` does
attain (`JSP90.closeToBipartite_two_p9`), cannot be obtained by covering the active edges of one odd
cycle.

### 5. The remaining statement

`JSP90.ShareEdgePackingOne r` (stated, not assumed): a graph in which two meeting odd cycles share a
cycle edge and whose odd cycles pairwise meet is `r`-close to bipartite.  It drops **both**
hypotheses of the `k = 1` subcubic case (degree and odd girth) and hence generalises round 78's
`JSP90.SubcubicPackingOne` (`JSP90.subcubicPackingOne_of_shareEdgePackingOne_two` is that special
case); Part 3 proves its base level for the graphs whose odd cycles are triangles, and

> `JSP90.not_shareEdgePackingOne_one : ¬ JSP90.ShareEdgePackingOne 1` — by machine check, `p9`
> satisfies the hypotheses and is not one vertex away from bipartite,

so `r = 2` is the sharp candidate.  `JSP90.erdos73On_shareEdgePackingOne_one` is the consumer: the
statement implies the `k = 1` level of the headline theorem on the class of Part 1.

### Environment notes (round 80)

* `Finset.inter`, `Finset.subset` and every `Finset` operation build `DecidableEq α` into the *data* of
  the finset, so a finset built with the classical instance and the same finset built with the
  computable instance are **not** defeq.  Consequently the finite checks of Part 4 must live in a
  section in which the *computable* `instDecidableEqFin` is the instance in scope, and every
  statement that is used across the two sections must mention only `⊆` and element membership (hence
  the instance-free formulation of `JSP90.TwoCoverCycleEdges`, and the instance-free bridge
  `JSP90.activeCb_eq_cycleEdges`).
* `rw [def, dif_pos h]` on a `dite` built in another file works **iff** the `Decidable` instance
  elaborated here is defeq to the one baked in there; declaring
  `local instance : Decidable (IsOddCycle G D) := Classical.propDecidable _` exactly as
  `JSPProblem/Subcubic.lean` does keeps the rewrite working.
* `subst h` on `h : D = C` may eliminate `C` rather than `D`; use `have hsub' : Z ⊆ D := by rw [h]; …`
  instead of `subst`.
* `rcases` on `Finset.mem_inter.mp h` returns the two components **in the order of the intersection**,
  not the order one usually expects.
* `Finset.mem_pair` does not exist at the pinned revision; `{a, b} = insert b {a}`, so use
  `Finset.mem_insert` and `Finset.mem_singleton`.
* `Finset.card_pair_of_ne` is gone; `rw [Finset.card_insert_of_notMem (by simp [h]), Finset.card_singleton]`
  computes the card of a two-element finset.
* `Finset.not_mem_empty` does not exist; use `Finset.not_nonempty_empty ⟨x, hx⟩`.
* `by decide` on a statement quantifying over `Finset (Fin n)` needs `set_option maxRecDepth 100000`
  inside the enclosing `section` (`by decide` itself is fine once the section options are set).
* `OfNat`-annotated numerals (`(2 : Fin 3)`) keep `by decide` well-typed; `⟨2, by omega⟩` inside the
  *type* of a `have` makes the type contain a free variable and `decide` refuses it.

---

## `JSPProblem/Ring.lean` (round 82) — the three-arc cycle constructor and the ring lemma

The file develops, from scratch and with no Mathlib input beyond what earlier files use:

* `JSP90.arcOf` / `JSP90.arcRev` — an arc of a cycle as a **directed** path and the same path
  traversed backwards, both as maps `ℕ → V`;
* `JSP90.exists_oddPath` — between two distinct vertices of an odd cycle there is a simple path of
  **odd** length lying on the cycle (directedness matters: the three arcs of a ring need not be
  oriented consistently, cf. the three-sun of `JSPProblem/Sun.lean`);
* `JSP90.arcCat3`, `arcCat3_inj`, `arcCat3_adj`, `isOddCycle_of_ring3` — the **three-arc cycle
  constructor**, the "closing path" generalisation of `JSP90.arc_isOddCycle_of_notMem`;
* `JSP90.twoHelly_of_linearOddCycles` — the **ring lemma** — and with it
  `JSP90.oddCactus_iff_linear` (`OddCactus G ↔ LinearOddCycles G`) and the two instances of the
  headline theorem `JSP90.erdos73On_linear_one` (constant `1`, optimal) and `JSP90.erdos73On_linear`
  (constant `k * (k + 1)`) for the **weaker** hypothesis `LinearOddCycles G`.

Toolchain facts learned here (they cost most of the round):

* **A `def` whose branches use a hypothesis of their own `if` in a proof (e.g. `by omega`) elaborates
  to a `dite`, and `if_pos` / `if_neg` then do not rewrite it.**  Hence `JSP90.arcCat3` is defined on
  `ℕ` (a total map) with *proof-free* branches: every later `simpa only [arcCat3, if_pos h, …]` works.
  Defining it on `Fin (d₁ + d₂ + d₃)` instead, with `⟨j.val, by omega⟩` in the branches, costs a
  `dite` per entry and defeats every later rewrite.
* `+` is **left**-associative in Lean 4 terms, so `a + b + c - 1` is `((a + b) + c) - 1`; several
  index computations below are stated in that shape on purpose.
* `omega` **refuses to split a trailing `- 1` inside a sum** (`d₁ + d₂ + d₃ - 1 ≤ d₁` is not provable
  for it).  Feed it the decomposition first: `Nat.add_sub_assoc (h : 1 ≤ d₃) (d₁ + d₂)` rewrites
  `n + d₃ - 1` to `n + (d₃ - 1)`, after which the goal is linear in the atom `d₃ - 1`.  Likewise
  `Nat.sub_pos_iff_lt` is stated with `k < n`, so `0 < d₃ - 1` needs `1 < d₃`, not `0 < d₃`.
* `Nat.sub_sub : n - m - p = n - (m + p)` and `Nat.add_sub_cancel_left : n + m - n = m` do the
  remaining index arithmetic; `Nat.add_sub` does **not** exist (it is `Nat.add_sub_assoc`).
* `rcases h with h' | h'` then `exact absurd h'.1 (by omega)` is the robust way to kill a case: the
  hypotheses `1 ≤ x` and the goal `¬x = 0` do not unify syntactically, and `Nat.ne_of_gt` will not
  take `1 ≤ x` either.
* `if_pos h` / `if_neg h` are deprecated at the pinned toolchain (use `ite_eq_left` / `ite_eq_right`)
  but still work; `simp only [Fin.val_mk]` is frequently an unused simp argument in this development.

---

## Round 83 — `JSPProblem/Helly.lean`: the **HELLY axis** (attack family 30)

`JSP90.HellyOddCycles G` says the odd cycles of `G` form a **Helly family**: every finite family of
pairwise meeting odd cycles has a common vertex.  Round 81/82's `TwoHellyOddCycles` is only the
three-element case.  The new file (31 declarations, 565 lines, 0 `sorry`, 0 `admit`, `lake build`
OK with 1238 jobs) proves

* **`JSP90.helly_of_linearOddCycles : LinearOddCycles G → HellyOddCycles G`** — the Helly lemma.
  Strong induction on `|𝒞|`; for `|𝒞| ≥ 3` take three distinct members `C₁, C₂, C₃` and, for each
  `i`, the induction hypothesis on `𝒞.erase Cᵢ`, which is common to all the *other* members.  If some
  `vᵢ ∈ Cᵢ` it is common to `𝒞`.  Otherwise `v₁ ∉ C₁`, `v₂ ∉ C₂`, `v₁ ∈ C₂ ∩ C₃`, `v₂ ∈ C₁ ∩ C₃`;
  write `C₁ ∩ C₂ = {a}` (linearity) and apply **round 82's ring lemma** to `C₁, C₂, C₃`: the common
  vertex lies in `C₁ ∩ C₂ = {a}`, so `a ∈ C₃`; then `v₁ ≠ a` are two vertices of `C₂ ∩ C₃`,
  contradicting linearity.  So round 82's ring lemma generalises to families of **any** size;
* **`JSP90.twoHelly_of_helly`**, `JSP90.exists_commonVertex_of_helly`,
  `JSP90.exists_commonVertex_of_helly_three`;
* **`JSP90.closeToBipartite_one_of_helly_of_locIndep_one` / `JSP90.erdos73On_helly_one`** — a **new
  instance of the headline theorem at `k = 1` with the optimal constant `1`, under the strictly weaker
  hypothesis `HellyOddCycles G`**.  Erdős's hypothesis enters only through
  `JSP90.inter_oddCycle_of_locIndep_one`;
* **`JSP90.helly_completeGraph_three` / `helly_locIndep_one_K3` /
  `helly_not_closeToBipartite_zero_K3` / `not_helly_attained_zero`** — `K₃` attains the constant, so
  `f(1) = 1` **exactly** on the Helly class;
* **the diamond `K₄` minus an edge** (`JSPProblem/Helly.lean`, `section Diamond`):
  `three_cycle_isClique`, `mem_zero_of_oddCycle_diamond`, `helly_diamond`, `locIndep_one_diamond`,
  `closeToBipartite_one_diamond`, `not_linear_diamond` and the summary **`JSP90.HellyOfNonlinear`** —
  a graph with the Helly property, `LocIndep 1` and `CloseToBipartite 1` which is **not** linear.
  Hence the new instance is **not** a corollary of round 82's;
* **`JSP90.HellyErdős73 f`**, the remaining statement at a general constant, a `def`, **not**
  assumed.

### Environment notes added this round

* `Finset.nonempty_iff_ne_empty` is stated **`s.Nonempty ↔ s ≠ ∅`** — `.mp` turns `≠ ∅` into a
  witness, `.mpr` turns a `Nonempty` into `≠ ∅` — so `Finset.nonempty_iff_ne_empty.mpr h` with
  `h : s.Nonempty` is the statement `s ≠ ∅` and **not** the other way round.  `Finset.ne_empty_of_mem`
  is the least surprising form when the witness is in hand;
* `Finset.mem_erase : a ∈ s.erase b ↔ a ≠ b ∧ a ∈ s`, so the *inequality* comes **first**; getting
  the order wrong produces the misleading `C₂ ≠ C₁` / `C₁ ≠ C₂` mismatches;
* `Finset.mem_insert.mp` will not fire on `h : x ∈ {a}` because the singleton is not displayed as
  `insert a ∅`; use `Finset.mem_singleton.mp`, or give the set explicitly
  (`Finset.mem_insert (s := (∅ : Finset _))`);
* `refine ⟨x, h⟩` against a goal of the form `s ≠ ∅` fails (`⟨...⟩` expects an inductive type);
  either `show ∃ z, z ∈ s` first, or convert with `Finset.nonempty_iff_ne_empty`;
* `by_contra h` on `x ∈ s` gives `h : ¬ (x ∈ s)`, which **is** what `absurd hx h` wants; but
  `Finset.mem_singleton.mp` on `h : x ∈ {a}` gives `x = a`, not `a = x`;
* a statement quantifying over `Finset V` has **no** `Decidable` instance out of the box: there is no
  `Fintype (Finset α)`, so `by decide` over `∀ C : Finset V, …` fails with *failed to synthesize
  `Decidable`*.  Enumerate with `Finset.card_eq_three` / `Finset.card_eq_four` + `fin_cases`, or work
  with `C = {a, b, c}` and prove a membership lemma instead (this is what `mem_zero_of_oddCycle_diamond`
  does);
* for a graph defined by an explicit `Finset (α × α)` edge set, `by decide` over a `∀` statement needs
  an explicit `local instance : DecidableRel G.Adj := fun v w => inferInstanceAs (Decidable ((v, w) ∈ e))`
  — the `Decidable` of a `∀ j : Fin 3, G.Adj …` does not appear automatically (the copy in
  `JSPProblem/Sun.lean`);
* `SimpleGraph.IsClique D := ∀ ⦃v w⦄, v ∈ D → w ∈ D → v ≠ w → G.Adj v w` — the vertices are
  **implicit**, so call it as `hcl hm1 hm2 hne`;
* `JSP90.not_linear_of_two_mem h hC hD hCne hx1 hx2 **hy1 hy2** hxy` — the two membership arguments
  of the second vertex are `(y ∈ C)` then `(y ∈ D)`, not the other way round; and `C`, `D` are implicit,
  so give them `(C := …) (D := …)` when the `IsOddCycle` proofs are stated with explicit finsets;
* `Finset.two_lt_card_iff : 2 < s.card ↔ ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c` is
  `.mp`, not `.mpr`, to *extract* the three members from `3 ≤ s.card`;
* `local instance` declared at namespace level is **not** reverted by a later `section … end`: it
  stays in scope for the rest of the file and silently makes `by decide` fail (the classical
  `DecidableEq` is noncomputable).  Put the classical instances **inside** the `section` that needs
  them and open a fresh section for the finite (computable) part.

---

## Round 84 — `JSPProblem/Descent.lean`: the **deficiency descent**, and Erdős #73 on the Helly class with the *optimal* constant

Attack family 31.  New file `JSPProblem/Descent.lean` (24 declarations, 0 `sorry`, 0 `admit`,
`lake build` OK with 1239 jobs), imported from the root module.  `#print axioms` on all the headline
results shows only `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

Round 83 characterised the Helly class and left one statement open (`JSP90.HellyErdős73 f` for a
general `f`).  This round computes, exhaustively, what the *best* constant on that class is, proves
that the right invariant is the **maximum deficiency** `MaxDef G`, and reduces the whole instance to
**one** statement about a single vertex deletion.

### The statement

```lean
JSP90.erdos73On_helly_of_maxDefDescent :
    JSP90.HellyMaxDefDescent → JSP90.HellyErdős73 id
```

i.e. **Erdős Problem #73 for the graphs whose odd cycles form a Helly family, with the *optimal*
constant `f(k) = k`** (`LocIndep k G → HellyOddCycles G → CloseToBipartite k G`), from the single
hypothesis `JSP90.HellyMaxDefDescent`, the *vertex descent*

```lean
JSP90.VertexDescent G : Prop :=
  1 ≤ MaxDef G → ∃ (C : Finset V) (v : V), IsOddCycle G C ∧ v ∈ C ∧
    MaxDef (deleteFinset G {v}) + 1 ≤ MaxDef G
```

— stated as a `def` and **not** assumed.  This is the residual content of the round.

### What is proved

* **`JSP90.isOddCycle_induceFinset`**, **`JSP90.helly_induceFinset`**, **`JSP90.helly_deleteFinset`** —
  **the Helly property is hereditary**: the odd cycles of `G[s]` are odd cycles of `G`
  (`IsOddCycle (induceFinset G s) C → IsOddCycle G C ∧ C ⊆ s`, proved from the definition), hence a
  subfamily of a Helly family, hence Helly.  This is what makes an induction on `MaxDef G` possible
  on the class at all.  Also `JSP90.helly_of_isBipartite`.
* **`JSP90.defOf_oddCycle_ge_one'`**, **`JSP90.defOf_ge_succ_add`** and
  **`JSP90.maxDef_ge_one_add_maxDef_delete_of_oddCycle`** — **the residue descent, with no
  separation hypothesis**: `IsOddCycle G C → 1 + MaxDef (deleteFinset G C) ≤ MaxDef G`.  The
  numerical heart is `α(G[A ∪ C]) ≤ α(G[A]) + α(G[C])` together with `2 α(G[C]) + 1 ≤ |C|`, i.e. an
  odd cycle pays for at most `|C| - 1` of the deficiency, so **adding** it costs a unit.  This could
  not be stated in `JSPProblem/OffCycle.lean`, whose version needs `Separated G C X`.
* **The duality of a witness and a transversal** (Part 3):
  * `JSP90.defOf_maxDef_inter_oddCycle_ne` — a vertex set of deficiency exactly `MaxDef G` **meets
    every odd cycle**: *maximum-deficiency witnesses are odd cycle transversals* (the dual of
    `JSP90.maxDef_le_of_hitsOddCycles`);
  * `JSP90.exists_oddCycle_of_defOf_gt_zero` — a vertex set of positive deficiency **contains an odd
    cycle**;
  * `JSP90.mem_of_common_oddCycle`, `JSP90.vertexDescent_of_common_oddCycle` — hence a vertex on
    every odd cycle lies in every witness, its deletion is bipartite, and **the vertex descent is
    proved** in that situation.
* **`JSP90.closeToBipartite_maxDef_aux` / `JSP90.closeToBipartite_maxDef_of_maxDefDescent`** — the
  induction: `MaxDef G = 0` gives bipartiteness; otherwise delete one vertex `v` of an odd cycle,
  the residue is Helly with deficiency one smaller, and a transversal of the residue is extended by
  `v`.  **`JSP90.erdos73On_helly_of_maxDefDescent`** is the `Erdős73On`/`HellyErdős73` form.
* **`JSP90.closeToBipartite_one_of_helly_of_pairwiseMeeting` /
  `JSP90.erdos73On_helly_pairwiseMeeting`** — a **proved** instance: if the odd cycles pairwise meet
  (packing number `≤ 1`) and `G` is Helly, then `LocIndep c G → CloseToBipartite c G` for **every**
  `c` (round 83 had `c = 1` only).  No bound on the odd girth, degrees, packing weight, branch
  vertices or components.
* **`JSP90.helly_kTriangles`**, `JSP90.not_closeToBipartite_helly_kTriangles`,
  `JSP90.helly_attained_sharp` — **the constant `k` cannot be lowered**: `kTriangles k` is Helly,
  satisfies `LocIndep k` and is not `(k - 1)`-close to bipartite.

### What is *not* proved

`JSP90.HellyMaxDefDescent` — the vertex descent for every Helly graph.  It is proved in the
situation of Part 5 and verified computationally for the whole class (below), and it is the *only*
statement Part 4 uses.  `jsp_000090_main` remains **not** declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `score.py --strict-prize` reports `build_ok = true,
sorry = 0, admit = 0, placeholder_total = 0, partial_ok = true`.

### Verification done before formalising (exhaustive, in C)

Over **all** graphs on `n ≤ 7` vertices (`2²¹` graphs, `1 103 955` of them Helly):

* `HellyOddCycles ∧ MaxDef ≤ 1 → τ = 1`, `∧ MaxDef ≤ 2 → τ ≤ 2`, and **no** Helly graph on `n ≤ 7`
  has `τ > MaxDef` (0 counterexamples): `CloseToBipartite (MaxDef G) G` is the right statement;
* **`VertexDescent` holds for every Helly graph** (0 counterexamples);
* but it **fails without Helly**: 13020 counterexamples on `n = 7`, all with `MaxDef = 1`; the
  smallest is the diamond `K₄ - e` (its two triangles share an edge, so deleting a vertex of one
  leaves the other).  The Helly hypothesis is therefore *not* cosmetic;
* **two candidate proofs of the instance are false**, recorded so later rounds do not retry them:
  * **König's property fails on the Helly class**: Helly graphs with `τ > ν` exist (360
    counterexamples on `n = 7`; the first has `MaxDef = τ = 3`, `ν = 2`), so the least odd cycle
    transversal is *not* the packing number here — only the deficiency sees it;
  * **the `+1` absorption step at a residue fails** on the Helly class too: there need not be an odd
    cycle `C` and a transversal `X` of `G - C` with `|X| ≤ MaxDef (G - C)` that one vertex of `C`
    extends (360 counterexamples on `n = 7`; the smallest is a 6-vertex graph with
    `MaxDef = τ = 2`, `ν = 2` whose triangles `{0,2,4}` and `{1,3,5}` are met by no single vertex of
    `C = {3,4,5}`).  This is the same step `JSPProblem/Weight.lean` refutes with `K₅` in general
    graphs, and it is why the descent has to be about *single vertices* rather than residues.

### Environment notes added this round

* the deficiency is **sub**additive, never superadditive, over a disjoint decomposition: for
  `A = {v}` (isolated) and `C` a triangle, `defOf G (A ∪ C) = 0 < 1 = defOf G A + 1`, so
  `defOf G (A ∪ C) ≥ defOf G A + defOf G C` is **false** (this is the truncation at zero already
  recorded in `JSP90.defOf_le_add_of_anticover`).  The lemma that *is* true needs
  `1 ≤ defOf G A`; the case `defOf G A = 0` has to be split off, because then `MaxDef G ≥ 1` follows
  from the odd cycle alone;
* `Nat.le_sub_iff_add_le` at the pinned revision is stated as `?m ≤ ?m → (?m ≤ ?m - ?m ↔ …)`: it
  needs a side-condition hypothesis *before* the `↔`, so `.mp`/`.mpr` do not apply to a bare
  inequality.  `Nat.sub_le_iff_le_add` has the same problem.  The two conversions actually used are
  `Nat.sub_eq_zero_of_le` + `omega` and `JSP90.le_sub_of_add_le'` (proved here by `by_contra`);
* `defOf_induceFinset_le_inter` is stated for `induceFinset`, **not** for `deleteFinset`: rewriting
  `deleteFinset G C` into `induceFinset G (univ \ C)` first (`simp [deleteFinset]`) is required;
* a `set W := … with hW` definition is *definitionally* equal to its body but Lean will not unfold it
  inside `Finset.mem_sdiff.mp`; write `have hwW' : w ∈ … := hwW` first;
* `ih m hmt W G hle hH` for `Nat.strong_induction_on` on a motive that mentions the graph: the
  `[Fintype W]` binder is *instance* implicit in the induction hypothesis, so `letI := inst` is
  needed and `inst` must **not** be passed positionally;
* `deleteFinset G ({v} ∪ Y) = deleteFinset (deleteFinset G {v}) Y` is proved by
  `ext w x; simp only [deleteFinset_adj, Finset.mem_union, Finset.mem_singleton, not_or]; tauto`
  — `tauto` does *not* unfold `Finset.mem_union` itself;
* `omega` treats `a - b` as an **opaque atom**: every ℕ subtraction in a goal must first be
  linearised (`Nat.sub_le_iff_le_add` / `Nat.sub_add_cancel` / `le_sub_of_add_le'`) or the goal will
  fail even when the arithmetic is right; conversely `simp only [defOf]` inside a `have` proof
  *creates* such an atom and breaks `omega`;
* `helly_induceFinset (s := …) hH`: `s` is implicit, so a positional `Finset.univ \ X` is parsed as
  the *result* and elaborates into a nonsensical `Finset (Finset V)`.

---

## Round 102 — `JSPProblem/Greedy.lean`: the **GREEDY SHORTEST-ODD-CYCLE CHAIN**

Round 101 proved the odd-girth ladder from an **assumed chain** of odd cycles, one per residue level.
This round **derives the chain from the graph**: delete the *shortest* odd cycle, then the shortest odd
cycle of the residue, and so on.  No chain has to be exhibited and **no girth hypothesis at all is
needed**.

* `JSP90.girthOf H` — vertices of a shortest odd cycle of `H` (`0` if `H` is bipartite);
  `JSP90.greedyCycle H` — such a shortest odd cycle (`∅` if there is none).
* `JSP90.level H j` / `JSP90.unionUpTo H j` — the greedy residue chain and the vertices deleted;
  `JSP90.level_eq_deleteFinset_unionUpTo`, and `JSP90.residueOf_greedyChain`: level `j` of the greedy
  chain **is** level `j` of the residue chain of `JSPProblem/Stair.lean`.
* **The greedy step** — `JSP90.disjoint_greedyCycle_of_lt` (two greedy cycles of different levels are
  vertex-disjoint) and `JSP90.packing_of_levels` (`n` non-bipartite levels give `n` disjoint odd
  cycles), hence `JSP90.level_isBipartite_of_locIndep`: Erdős's hypothesis makes the `k`-th level
  bipartite.  `JSP90.firstBipartiteLevel` marks where the construction stops.
* **`JSP90.closeToBipartite_of_greedyChain_step`** — the ladder **without any packing bound**: the first
  `n` greedy cycles plus a bipartite residue at level `n` pay `∑ j < n, girthOf (level H j)`.  The only
  index lemma needed is the self-similarity `JSP90.level_tail : level (level H b) n = level H (b + n)`.
* **`JSP90.erdos73On_of_greedyChain` / `_univ` — a new instance of the headline theorem**:
  `LocIndep k G → CloseToBipartite (∑ j : Fin k, girthOf (level G j)) G`, the hypothesis being exactly
  Erdős's own; the transversal is the greedy chain (`JSP90.closeToBipartite_of_greedyChain`,
  `JSP90.hitsOddCycles_greedyChain`).
* The comparison with the uniform bound is machine-checked: `JSP90.greedySum_le_uniform` ⇒
  `JSP90.erdos73On_of_greedyChain_uniform` **re-derives** `JSPProblem/Transversal.lean`'s `ℓ * k`
  instance, and `JSP90.greedySum_lt_uniform` records the strict improvement.

Two traps of this axis, both machine-checked and recorded so that no later round repeats them:
`OddCyclePackingLe (firstBipartiteLevel G k) G` is **not** available (Erdős's hypothesis bounds
packings by `k`, not by the length of a maximal greedy chain), and bipartiteness propagates
**forward** along the residue chain only (a triangle minus one vertex is bipartite).

---

## Round 103 — the PACKING BUDGET along the greedy chain (`lean/JSPProblem/Budget.lean`)

Attack family 44.  Round 102 built the greedy shortest-odd-cycle chain but could only use it to make
the *last* level bipartite; `discovery/JSP-000090/policy.json` recorded the quantitative statement
that its ladder was missing, `OddCyclePackingLe (k - j) (level G j)` for `j ≤ k`.  It is proved here,
in **two** forms, together with a generalisation of the ladder step and a new instance.

* **The exchange lemma** `JSP90.oddCycleFamily_union_chainBelow`: a packing `P` of the residue at
  level `j`, adjoined with the `j` greedy cycles of the earlier levels, is a packing of odd cycles of
  `G` of size `P.card + j` — the greedy chain does not merely *complete* every packing of the
  residue, it dominates it.  (`JSP90.chainBelow`, `JSP90.greedyCycle_subset_unionUpTo`,
  `JSP90.disjoint_unionUpTo_of_isOddCycle_level`, `JSP90.not_mem_chainBelow_of_isOddCycleFamily`,
  `JSP90.biUnion_chainBelow`, `JSP90.card_chainBelow`.)

* **THE PACKING BUDGET** `JSP90.level_oddCyclePackingLe`:

  > `LocIndep k G → j ≤ k → OddCyclePackingLe (k - j) (level G j)`

  with `JSP90.level_packing_add_le` (`P.card + j ≤ k`), the classical residue step
  `JSP90.level_oddCyclePackingLe_one`, and `JSP90.level_isBipartite_of_budget` (the `j = k` end:
  packing number `0` means bipartite — round 102's `level_isBipartite_of_locIndep` re-derived).

* **THE DEFICIENCY BUDGET** `JSP90.level_locIndep`:

  > `LocIndep k G → LocIndep (k - j) (level G j)`

  proved from round 87's `maxDef_ge_card_add_maxDef_delete` along the chain
  (`JSP90.level_maxDef_add_le`: `j + MaxDef (level G j) ≤ MaxDef G`), in the hypothesis-free form
  `JSP90.level_locIndep_of_firstBipartite`, and at the top of the chain
  (`JSP90.level_locIndep_one`).  This is the parameter that the classical Erdős–Pósa descent
  decreases, and it was not available anywhere in the development before this round.

* **THE LADDER WITH A PER-LEVEL RESIDUE PRICE** `JSP90.closeToBipartite_of_greedyChain_cost`
  (`JSP90.stepCost` = `g j + c (j + 1)`) strictly generalises round 102's
  `closeToBipartite_of_greedyChain_step` (recovered as
  `JSP90.closeToBipartite_of_greedyChain_cost_bipartiteLevels`), and yields the new instance

  > `JSP90.erdos73On_of_greedyChain_cost`:
  > `LocIndep k G → (∀ i, 1 ≤ i → i ≤ k → CloseToBipartite (c i) (level G i)) →
  >   CloseToBipartite (∑ j < k, girthOf (level G j) + c (j + 1)) G`

  in which each greedy residue pays a *level-dependent* price — the shape in which the budgets enter
  a theorem — and its unit-cost instance `JSP90.closeToBipartite_of_greedyChain_cost_one`, whose
  constant is **strictly smaller** than round 102's by exactly `k`
  (`JSP90.girthSum_lt_of_unit`).

The gap to `jsp_000090_main` is unchanged: the budgets are proved, but the *transversal* half — a
bound on an odd cycle transversal in terms of the packing number — is still
`JSP90.OddCycleErdosPosa r`, and the budgets themselves do not improve the constant of
`JSP90.erdos73On_of_greedyChain` (the greedy sum is not a function of `k`, as round 102 recorded).

---

## Round 104 — CLUSTER GRAPHS: a new instance with the optimal constant `k`
(`lean/JSPProblem/Cluster.lean`, `lean/JSPProblem/ClusterSharp.lean`)

Attack family 45.  Every instance so far was of the shape "hypothesis `LocIndep k` **plus** a
structural hypothesis" (bounded odd girth, no branch vertex, a packing budget, ...).  Round 98's
`DisjointFamily (OddCycles G)` is the only one with no side condition, and it forces `G` to be a
disjoint union of *odd cycles*.  This round asks for the **largest** class on which the hypothesis
alone already gives the conclusion: **disjoint unions of complete graphs** (cluster graphs).  On
that class Erdős's hypothesis and its conclusion coincide, and the instance has the optimal
constant `f(k) = k`.

* **The class** `JSP90.ClusterDecomposition G 𝒬`: the pieces of `𝒬` are pairwise disjoint and
  pairwise anticomplete and cover `V` (`AnticoverCoverFamily`, so every cycle of `G` lies in one
  piece), each piece has at least two vertices, and each piece is a **clique**.

* **THE INSTANCE** `JSP90.erdos73On_of_cluster`:

  > `ClusterDecomposition G 𝒬 → LocIndep k G → CloseToBipartite k G`

  with the quantified form `JSP90.erdos73On_of_cluster_univ`.  No odd girth, no packing weight, no
  degree bound, no bound on the number of pieces.

* **Hypothesis = conclusion on this class** `JSP90.closeToBipartite_iff_maxDef_cluster`:

  > `CloseToBipartite m G ↔ MaxDef G ≤ m`

  so the whole content of Erdős #73 there is the comparison of two invariants — and the deficiency
  is **exactly the cost of the pieces**, `JSP90.maxDef_cluster`:

  > `MaxDef G = ∑ C ∈ 𝒬, (|C| - 2)`

  proved from `JSP90.indepCard_cluster` (`α(G[X])` = the number of pieces `X` meets,
  `JSP90.piecesMet`), `JSP90.card_biUnion_eq_sum`, `JSP90.sum_card_eq_sum_cost` and the transversal
  `JSP90.exists_oddCycle_transversal` (big pieces, two vertices deleted per piece, every odd cycle
  hit).

* **Exactness of the conclusion** `JSP90.cluster_isBipartite_iff` (`G.IsBipartite ↔ every piece has
  ≤ 2 vertices`), the single-piece case `JSP90.maxDef_cluster_univ` (`MaxDef = |V| - 2`, recovering
  round 54's `MaxDef (K_n) = n - 2`), and the proved case `k = 0`,
  `JSP90.erdos73On_cluster_zero`.

* **Sharpness, machine-checked** (`lean/JSPProblem/ClusterSharp.lean`, no `DecidableEq` instance in
  scope, as the toolchain notes of round 103 require): the witness of the lower bound,
  `kTriangles k`, **is** a cluster graph (`JSP90.cluster_kTriangles`, `JSP90.anticover_fibreFamily`),
  its fibres cost `3 - 2 = 1` each (`JSP90.sum_cost_fibreFamily`, `JSP90.card_fibreFamily`), so

  > `JSP90.maxDef_kTriangles_eq : MaxDef (kTriangles k) = k`
  > `JSP90.erdos73On_of_cluster_optimal : (LocIndep k (kTriangles k) → CloseToBipartite m (kTriangles k)) ↔ k ≤ m`
  > `JSP90.erdos73_cluster_notBelowK / JSP90.cluster_lower_bound`: for `m < k` the implication fails

  i.e. **the new instance is an equivalence with the optimal constant**, and the class is strictly
  larger than round 98's (`K_5 ⊔ K_5` is a cluster graph which is not a disjoint union of odd
  cycles, `JSP90.not_oddCyclesDisjoint_completeGraph_five`).

The headline theorem `jsp_000090_main` (`Erdős73` for every `k`, i.e. `JSP90.OddCycleErdosPosa r` for
the 3-connected case) is **unchanged**: this round removes no restriction on `G` in general, only on
a class on which the answer is already explicit.

## Round 105 — `lean/JSPProblem/Exact.lean`: the EXACT-ADDITIVITY axis

**Attack family 46.**  `JSPProblem/Deficiency.lean` proves only the *sub*-additivity of the maximum
deficiency over an anticomplete decomposition and says so explicitly:

> *"The *converse* (equality for `MaxDef`) is not proved here …"*

Round 104 re-derived the equality inside the much narrower hypothesis "every piece is a clique",
which is why its counting apparatus (`piecesMet`, `inj_pieces_choice`, `card_le_piecesMet`, …) runs to
forty declarations.  This file settles the equality **in general**, and then pushes the *same*
statement through the conclusion, so that both sides of Erdős #73 split exactly over a cover.

### The missing equality

```lean
JSP90.maxDefIn_anticoverIn_add : AnticoverIn G s A B →
    maxDefIn G s = maxDefIn G (s ∩ A) + maxDefIn G (s ∩ B)
JSP90.maxDef_anticover_add     : Anticover G A B →
    MaxDef G = MaxDef (G[A]) + MaxDef (G[B])
```

The mechanism is **attainment**, not monotonicity: `defOf G X = |X| − 2 α(G[X])` is a *truncated*
subtraction and is only subadditive over such a split (counterexample in the `Deficiency.lean`
header: `K_3 ⊔ K_1`, deficiency `0` on the vertex set, `1` on the triangle).  For the maximum the
truncation cannot bite, because `JSP90.exists_eq_maxDefIn` gives on each side a vertex set attaining
its own maximum, and a side of deficiency `p > 0` satisfies `|X| ≥ 2 α(G[X])`, so the two sides pay
for themselves separately.

**What is false, and is recorded in the file header:** `defOf` is *not* monotone under vertex sets.
For `G` a triangle plus two isolated vertices the triangle has `defOf = 1` and the whole vertex set
has `defOf = 0`; so `maxDefIn G U = defOf G U` and `MaxDef G = |V| − 2 α(G)` are both false, and the
route suggested in `Deficiency.lean` ("a vertex of `X \ s` is isolated in `G[s]`, so adding it …
leaves `defOf` unchanged") is not the one taken.

### The linear split on an `AnticoverIn`

`JSP90.card_indepCard_anticoverIn_add` — for `Y ⊆ s` with `A ⊔ B = s` anticomplete,
`|Y| = |Y ∩ A| + |Y ∩ B|` and `α(G[Y]) = α(G[Y ∩ A]) + α(G[Y ∩ B])` *exactly*.  This is the
generalisation of `JSP90.card_indepCard_anticover_add` (stated there only for `Y ⊆ V`), and
`JSP90.card_indepCard_anticover_add_of_anticover` recovers the old statement as the case `s = V`.

### The finitary form, on the hypothesis side

```lean
JSP90.maxDef_eq_sum_of_cover : AnticoverCoverFamily G 𝒬 → (cover) →
    MaxDef G = ∑ X ∈ 𝒬, MaxDef (G[X])                     -- induction on the family
JSP90.locIndep_cover_iff     : LocIndep k G ↔ (∑ X ∈ 𝒬, MaxDef (G[X])) ≤ k
JSP90.maxDef_eq_sum_cost_of_cover : … pieces cliques of ≥ 2 vertices … →
    MaxDef G = ∑ C ∈ 𝒬, (|C| - 2)                          -- ROUND 104'S THEOREM, NOW A COROLLARY
JSP90.maxDef_clique / JSP90.closeToBipartite_of_clique : MaxDef (G[C]) = |C| - 2, and the transversal
```

### The finitary form, on the conclusion side

```lean
JSP90.closeToBipartite_of_cover_cost  : (∀ X ∈ 𝒬, CloseToBipartite (c X) (G[X])) →
    CloseToBipartite (∑ X ∈ 𝒬, c X) G
JSP90.closeToBipartite_iff_cost_cover : CloseToBipartite m G ↔
    ∃ c, (∀ X ∈ 𝒬, CloseToBipartite (c X) (G[X])) ∧ (∑ X ∈ 𝒬, c X) ≤ m
JSP90.card_sum_inter_le               : (∑ X ∈ 𝒬, |Z ∩ X|) ≤ |Z|   -- the disjointness counting
```

### The new instance, and its optimality

```lean
JSP90.PieceMaxDef G 𝒬 : AnticoverCoverFamily G 𝒬 ∧ cover ∧
    ∀ X ∈ 𝒬, CloseToBipartite (MaxDef (G[X])) (G[X])

JSP90.erdos73On_of_pieceMaxDef (+ _univ) : PieceMaxDef G 𝒬 → LocIndep k G → CloseToBipartite k G
JSP90.closeToBipartite_iff_maxDef_of_pieceMaxDef : CloseToBipartite m G ↔ MaxDef G ≤ m
JSP90.pieceMaxDef_of_cluster             : ClusterDecomposition G 𝒬 → PieceMaxDef G 𝒬
JSP90.erdos73On_of_pieceMaxDef_optimal   : (LocIndep k (kTriangles k) → CloseToBipartite m (kTriangles k)) ↔ k ≤ m
JSP90.erdos73_pieceMaxDef_notBelowK      : m < k → ¬ CloseToBipartite m (kTriangles k)
```

`PieceMaxDef` is the **cover closure of the class on which the hypothesis and the conclusion of
Erdős #73 coincide**: the pieces pay their deficiency jointly because the deficiency splits over the
cover and the per-piece deletion sets are disjoint.  It contains round 104's cluster class
(`JSP90.pieceMaxDef_of_cluster`; strictly larger: `K_5 ⊔ K_{2,3}` is on it and is not a cluster
graph), and every disjoint union of graphs of any proved class of that kind.  The constant `k` is
machine-checked optimal on the lower-bound witness `kTriangles k`.

### Toolchain notes from this round (for `policy.json`)

* `Membership (Finset V) (Finset V)` **cannot be synthesised** from a file-local
  `local instance : DecidableEq V` (Mathlib's `Finset.decidableEq` is not found by instance search in
  this setting).  Consequences: `Finset.disjoint_iff_ne` is unusable (use
  `JSP90.false_of_mem_inter`, proved once from `Finset.disjoint_iff_inter_eq_empty` +
  `Finset.disjoint_left`); no lemma may be *stated* with `X ∈ s` for `X s : Finset V`; and `simp`
  cannot reduce `X ∈ ∅` for `X : Finset V` (use `JSP90.not_mem_finsetEmpty`, proved by
  `rw [Finset.mem_def]; simp`).  Membership in `Finset (Finset V)` (one level up) *is* available.
* The `∉` in `JSP90.AnticoverIn` is **finset**-typed, so `⟨fun _ hxA hx' => …⟩` works for its first
  field, but Mathlib's `Finset.Disjoint` is **Set**-typed (`a ⊆ s → a ⊆ t → False`): never apply
  `Disjoint` as a function, use `Finset.disjoint_iff_inter_eq_empty` / `false_of_mem_inter`.
* `Finset.mem_insert.mp h` with `h : Y ∈ insert X t` yields `Y = X ∨ Y ∈ t`; in the first branch the
  contradiction comes from the *caller's* hypothesis (`x ∉ X`), **not** from `hX : X ∉ t`.
* `Finset.sum_insert` takes the non-membership proof as an *argument*: `Finset.sum_insert hX`, not
  `Finset.sum_insert`; and `Finset.sum_congr` takes `(s₁ = s₂)` first, so
  `Finset.sum_congr rfl (fun X _ => …)`.
* `Finset.inter_eq_left.mpr : s ⊆ t → s ∩ t = s` and `Finset.inter_eq_right.mpr : t ⊆ s → s ∩ t = t`
  need explicit `(s₁ := _) (s₂ := _)` when the finsets are not determined by the goal.
* `IsOddCycle.induceFinset (hC : IsOddCycle G C) (hsub : C ⊆ s)` and
  `isOddCycle_sub_induceFinset` are the two conversions between an odd cycle of `G` and of `G[s]`;
  together with `isOddCycle_sub_anticoverCover` they give the transversal half without any induction.
* `CloseToBipartite` is `def`, so `HitsOddCycles` (also a `def`) must be applied as
  `(hhits X hX) C hC`, not `hhits X hX C hC`.
* `JSP90.isBipartite_induceFinset_of_card_le_two` (`JSPProblem/Weight.lean`) is the "≤ 2 vertices is
  bipartite" lemma needed by `JSP90.closeToBipartite_of_clique`.
* `JSP90.maxDef_eq_sum_of_cover` needs `set_option maxHeartbeats 4000000` (the induction over a finset
  of finsets is expensive); the rest of the file is fast.

## Round 106 — `JSPProblem/Multi.lean`: the COMPLETE MULTIPARTITE axis

New file (30 declarations, 0 sorry/admit, `lake build` OK with 1257 jobs), imported from the root
module `JSPProblem.lean`.  Round 105 proved that both sides of Erdős #73 are exactly additive over
an **anticomplete** cover and recorded its own limit: an anticomplete cover with two nonempty pieces
*is* a disconnection, so the additive axis only pays for disconnected graphs.  This round attacks
the complementary, **connected** family: the complete multipartite graph.

* `JSP90.multi t n` — the complete multipartite graph with `t` parts of `n` vertices on
  `Fin t × Fin n`, with `multiPart`, `mem_multiPart_iff`, `card_multiPart`, `multiPart_disjoint`,
  `isIndepSet_multiPart`;
* `JSP90.card_eq_sum_card_multiPart` — `|X| = ∑ i, |X ∩ P_i|` (the counting lemma, by induction on
  `X`), and `JSP90.card_le_mul_indepCard_multi` — `|X| ≤ t * α(G[X])`;
* `JSP90.indepCard_le_multi` — `α(G[X]) ≤ n` (an independent set lies in one part);
* **`JSP90.maxDef_multi`** — `MaxDef (multi t n) = (t - 2) * n`, the exact value of Erdős's
  hypothesis on this class, with `JSP90.locIndep_multi_iff`;
* `JSP90.not_isBipartite_of_tri` (pigeonhole on `Fin 2`), `JSP90.liveParts`,
  `JSP90.liveParts_le_two_of_isBipartite` (the colours of the live parts inject into `Fin 2`),
  `JSP90.deadParts`, `JSP90.card_deadParts_add_liveParts`, `JSP90.isBipartite_multi_of_cover`,
  `JSP90.isBipartite_multi_of_le_two`, and
  **`JSP90.isBipartite_deleteFinset_multi_iff`** — `G − X` is bipartite iff its surviving vertices lie
  in at most two parts;
* **`JSP90.closeToBipartite_iff_multi`** — `CloseToBipartite m (multi t n) ↔ (t - 2) * n ≤ m`, the
  exact value of the conclusion on this class;
* **`JSP90.erdos73On_of_multi`** (+ `_univ`, `_optimal`, `not_closeToBipartite_multi`) — **a new
  instance of the headline theorem with the optimal constant `f(k) = k`**, on a class which is
  *connected* for `t ≥ 2` (so no anticomplete-decomposition instance applies) and is not a cluster
  graph for `n ≥ 2`.

`#print axioms` on all of these gives only `[propext, Classical.choice, Quot.sound]`.

### Toolchain notes (this round)

* `Finset.mem_filter` does **not** apply to a membership in a `def` that unfolds to a `filter`: the
  expected type is `p ∈ filter q s ↔ p ∈ s ∧ q p` and the `p ∈ s` conjunct has to be discharged
  (`by rw [liveParts, Finset.mem_filter]; simp`, or `Finset.mem_filter.mpr ⟨Finset.mem_univ _, _⟩`).
  Anonymous constructors `⟨x, h⟩` for a goal `x ∈ (def …)` are *not* usable: the elaborator unfolds
  `def` and then `Membership.mem` and hits `List.Mem` (a two-constructor inductive) — always go
  through `Finset.mem_image`/`Finset.mem_filter` explicitly.
* `Finset.Nonempty s` unfolds to a `Quot.lift`-level membership, so `hp.1` after
  `obtain ⟨p, hp⟩ := h` fails; use `Finset.sdiff_eq_empty_iff_subset` and
  `Finset.not_nonempty_iff_eq_empty.mp` instead of projecting.
* `Nat.sub_mul : (n - m) * k = n * k - m * k` has the *subtrahend first*: `(t - 2) * n` is
  `Nat.sub_mul t 2 n`, and `Nat.mul_le_mul_left n h` (coefficient first),
  `Nat.sub_le_sub_left h k` (hypothesis first, then the minuend).
* `Finset.card_erase_of_mem : a ∈ s → #(s.erase a) = #s - 1`, and a single `rw` rewrites *all*
  occurrences of the pattern, so both `erase`s go at once.
* `Finset.card_union_add_card_inter (s t) : #(s ∪ t) + #(s ∩ t) = #s + #t` — `.symm` is the direction
  that rewrites a sum into a union.
* `JSP90.card_biUnion_eq_sum` (Cluster.lean) is stated with *that file's* `DecidableEq` instance, so
  its conclusion cannot be matched against a `Finset.biUnion` elaborated elsewhere; the counting
  identity is proved locally instead (by induction on the finset of parts).
* `Set.InjOn f s` unfolds to a **five**-binder `∀ ⦃a⦄, a ∈ s → ⦃b⦄, b ∈ s → f a = f b → a = b`, so
  `Finset.card_le_card_of_injOn` must be given `intro i hi j hj heq`.
* `Classical.choose` never reduces, so a colouring built as `d (Classical.choose h)` cannot be
  rewritten to `d p`; the witness properties have to be fetched with `Classical.choose_spec`.
* A file that opens a `noncomputable section` needs a bare `end` for it before `end <Namespace>`.

## Round 107 — `JSPProblem/Split.lean`: the SPLIT-GRAPH axis

New file (32 declarations, 0 sorry/admit), a new attack family: graphs `V = A ⊔ B` with `A`
independent and `B` a clique.  The two sides of Erdős #73 are both computed exactly, and the class
is connected, neither a cluster graph nor multipartite nor a disjoint union of odd cycles.

* hypothesis: `cardB_le_locIndep_add_two` (`LocIndep k G → |B| ≤ k + 2`), `maxDef_split_le`
  (`MaxDef G ≤ |B| − 1`);
* conclusion: `IsolatedPair`, `closeToBipartite_split_iff` (the exact value, `τ(G) ∈ {|B| − 1,
  |B| − 2}`), `closeToBipartite_split_cardB_sub_two_iff`;
* new instance: **`erdos73On_of_splitPartition`, constant `k + 1`**, plus
  `closeToBipartite_of_splitPartition_of_isolatedPair` (constant `k`);
* Part 4: the witness `K_{k+2,k+2}` minus a perfect matching, where the constant `k + 1` is attained
  for every `k ≥ 1`; the three `Finset` computations that finish its `LocIndep` proof are recorded
  as the one remaining step of the axis.

Toolchain notes:

* `DecidableEq V` is declared once at the top of the file (`instDecidableEqSplitGraph`), exactly as
  `JSPProblem/Deficiency.lean` does it, because the statements mention `X ∩ A`;
* `Nat.sub_le_sub_left : n ≤ m → ∀ k, k − m ≤ k − n` is the "bigger subtrahend, smaller result"
  lemma and `Nat.sub_le_sub_right` the other one — the names are the opposite of what the argument
  order suggests;
* `IsolatedPair` must be read with the deletion set `B \ {b₁, b₂}` in mind: a witness
  `CloseToBipartite (|B| − 2) G` has `Z ⊆ B` (proved in `not_closeToBipartite_of_split_no_isolatedPair`
  by counting), which is what makes the isolated-pair statement an equivalence;
* a split graph may have edges *between* the two sides — the claim `α(G[X]) ≥ 1 + |X ∩ A|` is false
  and Lean rejected it; only `α ≥ |X ∩ A|` and `α ≥ 1` are available, and they are enough.
