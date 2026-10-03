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
