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
