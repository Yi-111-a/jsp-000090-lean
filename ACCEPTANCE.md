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
