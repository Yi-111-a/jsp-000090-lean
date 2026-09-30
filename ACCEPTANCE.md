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
