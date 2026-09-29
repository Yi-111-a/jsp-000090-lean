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

`formalization.yaml` remains `status: wip`, `prize_ready: false`. No award claim is made.
