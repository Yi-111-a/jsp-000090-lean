/-
# JSP-000090 — Erdős Problem #73 (Reed 1999)

This is the root module of the `JSPProblem` library for the Justin Sun Prize Lean harness,
problem `JSP-000090`.

* `JSPProblem.Definitions` — the catalog statement of JSP-000090 as Lean definitions
  (`LocIndep`, `induceFinset`/`deleteFinset`, `CloseToBipartite`, `Erdős73`).
* `JSPProblem.Reed` — the structural results proved about those definitions.
* `JSPProblem.OddCycle` — the odd-cycle characterisation of bipartiteness (an open Mathlib `TODO`)
  and with it **Erdős Problem #73 for `k = 0`**, i.e. `JSP90.erdos73_zero : Erdős73 0`.
* `JSPProblem.Packing` — the *packing* half of the Erdős–Pósa strategy: Erdős's local hypothesis
  allows at most `k` vertex-disjoint odd cycles (`JSP90.LocIndep.oddCycle_packing_le`).
* `JSPProblem.Transversal` — the *transversal* half:
  - `JSP90.closeToBipartite_iff_hitsOddCycles`: the conclusion of Erdős #73 is equivalent to "`X` of
    size at most `m` meets every odd cycle of `G`";
  - `JSP90.not_isOddCycle_of_isBipartite` / `JSP90.isBipartite_of_no_oddCycle`: both halves of the
    odd-cycle characterisation of bipartiteness, hence `JSP90.oddCycleErdosPosa_zero`;
  - `JSP90.erdos73On_of_bounded_odd_girth`: **Erdős #73 for every graph whose odd girth is at most
    `ℓ`**, with the explicit constant `f(k) = ℓ * k`;
  - `JSP90.closeToBipartite_completeGraph_three`: the `k = 1` sharp example (`K_3` is one vertex away
    from bipartite), and `JSP90.rejected_reading_fails`, the record of the corrected formulation of
    `CloseToBipartite`;
  - `JSP90.erdos73_of_erdosPosa`: the whole theorem follows from `∀ r, JSP90.OddCycleErdosPosa r`.
* `JSPProblem.Fan` — the **local half of the classical fan argument**, developed from scratch
  (no Mathlib connectivity / Menger / fan API is used, none of it is in the pinned import slice):
  - `JSP90.arc_isOddCycle`: closing an arc of an odd cycle through an outside vertex gives a
    *simple odd cycle*; this is the parity core of the fan argument, obtained by counting;
  - `JSP90.oddCycle_through_fan`: a vertex outside an odd cycle which sees two of its vertices
    lies on an odd cycle with at most `|C|` vertices;
  - `JSP90.shortArc_of_shortest`: at a *shortest* odd cycle of length `≥ 5`, the two attachment
    points of any fan are exactly two steps apart (and the odd cycle through them has exactly
    `|C|` vertices);
  - `JSP90.card_inter_neigh_le_two`: consequently a vertex outside a shortest odd cycle of length
    `≥ 5` meets that cycle in **at most two** vertices, and
    `JSP90.locIndep_shortest_attach` instantiates this under Erdős's local hypothesis.
* `JSPProblem.Branch` — the **branch-vertex attack family** (round 38), a third and completely
  independent route to the same research statement.  Delete every vertex with three distinct
  neighbours and the residue has maximum degree `≤ 2`, where the odd cycles are pairwise
  disjoint, so a packing bound is automatically a transversal bound:
  - `JSP90.IsOddCycle.neigh_subset`: a vertex of an odd cycle of a graph without branch vertices
    has no neighbour outside the cycle;
  - `JSP90.eq_of_mem_inter_of_no_branch`: two odd cycles meeting at a vertex are equal, hence the
    odd cycles of such a graph are pairwise disjoint;
  - `JSP90.closeToBipartite_of_no_branch`: **Erdős–Pósa for odd cycles in graphs without branch
    vertices, with the optimal function `r ↦ r`**;
  - `JSP90.erdos73On_of_bounded_branch`: **a new proved instance of the headline theorem** — if all
    branch vertices of `G` lie in a set of at most `m` vertices, then `LocIndep k G` forces
    `CloseToBipartite (m + k) G`, with **no bound on the odd girth** (unlike
    `erdos73On_of_bounded_odd_girth`);
  - `JSP90.erdos73On_of_no_branch`: the case `m = 0`.
* `JSPProblem.Sharp` — the **optimality** half (round 39), a fourth and independent attack family.  The
  witness is `kTriangles k` = `K_3 ⊔ ... ⊔ K_3` (`k` copies) on `Fin 3 × Fin k`, the graph which
  makes the constant of Erdős #73 as large as possible:
  - `JSP90.locIndep_kTriangles`: it satisfies Erdős's local hypothesis `LocIndep k`, with equality
    (`2 * k + k = 3 * k = |V|`, and `not_locIndep_kTriangles` shows `LocIndep (k - 1)` fails);
  - `JSP90.isOddCycle_tri` / `card_le_of_hitsOddCycles_kTriangles`: every set meeting every odd
    cycle has at least `k` elements, hence `JSP90.closeToBipartite_iff : CloseToBipartite m
    (kTriangles k) ↔ k ≤ m` — the *exact* value of the conclusion on this graph;
  - `JSP90.erdos73_lower_bound` / `no_constant_below_k`: **the lower bound `f(k) ≥ k` of Erdős #73**,
    i.e. no constant below `k` can work in the statement of the catalogue question;
  - `JSP90.not_branch_kTriangles` / `erdos73On_no_branch_optimal`: the witness has no branch vertex,
    so the constant `k` of round 38 is **sharp** — on the class of graphs of maximum degree `≤ 2`
    the value of `f(k)` is exactly `k`;
  - `JSP90.packing_kTriangles_optimal`: the packing bound of `JSPProblem/Packing.lean` is attained
    too (`k` disjoint odd cycles, and no more), and `JSP90.not_branch_completeGraph_three` records
    that `K_3` itself is free of branch vertices.

* `JSPProblem.Residue` — the **global half of the Erdős–Pósa proof for odd cycles**, i.e. the
  residue of a packed odd cycle, to the extent it does not need connectivity/Menger:
  - `JSP90.LocIndep.of_deleteFinset`: Erdős's local hypothesis is inherited by a residue, with the
    same parameter;
  - `JSP90.card_add_one_le_of_mem_maxPacking` / `LocIndep.oddCycle_packing_residue_lt`: a packing of
    the residue of an odd cycle, together with that cycle, is a packing of `G`; so under
    `LocIndep k G` a packing of the residue has at most `k - 1` members — the strictly decreasing
    quantity on which the classical induction rests;
  - `JSP90.residue_hits_rest`: if `𝒞` is a maximum packing and `C ∈ 𝒞`, then every odd cycle
    avoiding `C` meets one of the *other* members of `𝒞` (the cross-intersection statement);
  - `JSP90.hitsOddCycles_union_cycle` / `closeToBipartite_of_residue`: the **induction step**, in
    the form `CloseToBipartite q (G - C) → CloseToBipartite (q + |C|) G`.  The `+|C|` term is exactly
    where this development stops: turning it into `+1` is the absorption step of
    Reed–Robertson–Seymour–Thomas;
  - `JSP90.packing_one_residue_bipartite` / `closeToBipartite_of_packing_one` /
    **`JSP90.erdos73On_of_packing_one`**: the case of packing number **one** in full — any two odd
    cycles meet, so *every* odd cycle is a transversal and its residue is bipartite.  Hence a graph
    of packing number one with an odd cycle of at most `ℓ` vertices satisfies `LocIndep k G →
    CloseToBipartite ℓ G` for every `k`: a **new instance of the headline theorem** with a constant
    that does not grow with `k`;
  - `JSP90.IsMinimalTransversal` / `exists_minimalTransversal` /
    `exists_minimalTransversal_of_transversal` / `exists_private_oddCycle`: a minimum transversal
    exists, is minimal, and **every one of its vertices lies alone on an odd cycle** — the
    "private" odd cycles the absorption step has to charge against a maximum packing
    (`card_le_of_disjoint_private_cycles`).

* `JSPProblem.Chord` — the arc machinery of `JSPProblem/Fan.lean` **generalised to a closing vertex
  on the cycle** (`arcFun_inj_of_notMem`, `arc_card_of_notMem`, `arc_isOddCycle_of_notMem`: it is
  enough that the closing vertex avoids only the arc, which is what a chord provides), and with it
  the structural facts the classical induction needs at its base:
  - `JSP90.no_chord_of_shortest_oddCycle`: **a shortest odd cycle is chordless** (a chord splits it
    into two cycles whose lengths add up to the odd number `m + 2`, so one is odd and shorter);
  - `JSP90.induceFinset_adj_of_shortest` / `isInduced_shortest_oddCycle`: **the subgraph induced by a
    shortest odd cycle is exactly that cycle**;
  - `JSP90.exists_shortest_oddCycle`: a shortest odd cycle exists whenever `G` has an odd cycle.
  Together with `JSP90.card_inter_neigh_le_two` of `JSPProblem/Fan.lean` this is the *complete*
  local structure of `G` at a shortest odd cycle.

* `JSPProblem.Separator` — the **2-cut decomposition**, the fifth and last attack family, and the
  first piece of *global* structure in this development: a split of `V(G)` as
  `{a, b} ⊔ T₁ ⊔ … ⊔ T_t` with the parts pairwise anticomplete, i.e. `{a, b}` is a vertex cut.
  It is formalised without any connectivity API (none is in the pinned import slice):
  - `VertexSplit.cycle_subset_parts` / `oddCycle_piece_or_avoid` / **`oddCycle_piece_unique`**: **a
    cycle of `G` which avoids the two vertices of the cut lies in a single part** — in exactly one
    — so every odd cycle of `G` is contained in a *piece* `T_i ∪ {a,b}` or meets the cut;
  - `VertexSplit.hitsOddCycles` / `exists_transversal` / **`erdos73On_of_split`**: the odd cycle
    transversal and the conclusion of Erdős #73 are additive over a 2-cut (up to the two vertices
    of the cut), giving a **new instance of the headline theorem** — Erdős #73 is *closed under
    2-cut decomposition*, with the constant `m * t + 2`; this is the reduction "the theorem reduces
    to the 3-connected case", and the step an induction on the Erdős–Pósa function must make;
  - `VertexSplit.isBipartite_of_split` / `not_isBipartite_of_split`: the **2-cut parity lemma** —
    if every piece is bipartite and the two vertices of the cut carry the same colour in every
    piece, then `G` is bipartite; so a non-bipartite `G` with bipartite pieces cannot be 2-coloured
    with `a` and `b` agreeing.  This is the classical reason the 3-connected case is the hard one;
  - `packing_le_of_split`: the **packing** half — the Erdős–Pósa hypothesis restricts to the
    pieces, so an induction along a 2-cut decomposition goes through;
  - **`erdos73On_of_split_of_bounded_branch`**: a second new instance of the headline theorem, the
    composition with the branch-vertex instance of round 38 (`2 + (m + k) * t` for a 2-cut whose
    pieces have at most `m` branch vertices each, with no bound on the odd girth).

* `JSPProblem.Count` — the **counting half of the 2-cut decomposition** (round 43), a fifth
  independent angle on the same object, and the round that removes the number of pieces from the
  constant of round 42:
  - `VertexSplit.cycle_subset_piece_of_not_mem` / `oddCycle_half_or_both`: **a cycle which meets
    exactly one vertex of the cut lies in a single half-piece** `T_i ∪ {a}` (resp. `T_i ∪ {b}`), so
    the only "global" odd cycles at a 2-cut are those using *both* vertices of the cut;
  - **`VertexSplit.card_nonBipartiteParts_le`**: under `LocIndep k G`, at most `k` of the `t` parts
    of a split are non-bipartite (each non-bipartite part carries an odd cycle and the parts are
    disjoint, so they form a packing);
  - **`erdos73On_of_split_of_bounded_pieces`**: **a new instance of the headline theorem, strictly
    stronger than round 42's `erdos73On_of_split`** — the constant is `2 + m * k` and no longer
    depends on the number of pieces `t`, still with no bound on the odd girth; and
    `erdos73On_of_split_of_bounded_branch_packing` is the same improvement for the composition with
    the branch-vertex instance;
  - **`packing_le_of_split_decomposition`**: the **full packing decomposition** — the packing number
    of `G` is at most `2 + t * r` if the parts have packing number at most `r` — the direction round
    42 named as missing;
  - `HasProperSplit`, `NoProperSplit`, **`SplitDepth`**, `splitBound` and
    **`erdos73_of_noSplit2_of_bounded_splitDepth`**: the **precise reduction** of Erdős–Pósa for
    odd cycles — it follows from the 2-cut-free case together with a uniform bound on the length of
    chains of 2-cuts, with the explicit bound `splitBound m p d`.  Since `erdos73_of_erdosPosa` is
    proved, `jsp_000090_main` therefore follows from exactly two statements, and everything else the
    classical proof uses is already proved here.

* `JSPProblem.Weight` — the **weighted Erdős–Pósa theorem** (round 44), a sixth and independent
  attack family: the residue induction of `JSPProblem/Residue.lean` run to *exhaustion*, with the
  running total `|C₁| + |C₂| + …` of the packed odd cycles as the induction parameter:
  - **`JSP90.closeToBipartite_of_weightLe`: if every packing of odd cycles of `G` has total length
    at most `L`, then `G` is `CloseToBipartite L`** — a strictly more general statement than
    round 40's `shortOddCycles_transversal`, which needs a bound on the length of *every* odd cycle;
  - `IsMaxWeightPacking`, `exists_maxWeightPacking` and `closeToBipartite_of_maxWeightPacking`:
    **the odd cycle transversal number of `G` is at most the weight of a maximum-weight packing of
    odd cycles** (a maximum-weight packing exists);
  - `hitsOddCycles_of_maxWeightFamily` and **`isBipartite_delete_of_maxWeightFamily`: the residue of
    a maximum-weight packing is bipartite** — the structural content of the weighted argument;
  - `erdos73On_of_bounded_packing_weight`: **a new instance of the headline theorem**, for graphs of
    bounded *packing weight* (a weaker hypothesis than bounded odd girth, no bound on the odd girth
    and none on the branch vertices), and `erdos73On_of_bounded_odd_circumference`, the `ℓ * k`
    instance re-derived as its corollary;
  - `closeToBipartite_iff_completeGraph_add_two` and `erdos73On_completeGraph`: **on complete graphs
    the conclusion is exact**, `CloseToBipartite m (K_n) ↔ n ≤ m + 2`, so Erdős's constant on the
    class of complete graphs is exactly `k` (a second witness for `f(k) ≥ k`);
  - **`JSP90.absorption_step_fails`: the naive `+ 1` absorption step is FALSE**, with the
    machine-checked witness `K_5` and the triangle `{0,1,2}` (the residue is `K_2`, hence
    `CloseToBipartite 0`, but `K_5` is not `1`-close to bipartite; and `LocIndep 3 (K_5)` holds, so
    the failure is inside the range of the theorem).  This is the concrete form of the blocker: the
    `+|C|` of `closeToBipartite_of_residue` cannot be replaced by `+1` without a hypothesis coming
    from the local structure at a shortest odd cycle of `JSPProblem/Fan.lean`.

* `JSPProblem.Optimal` — the **identity case of Erdős–Pósa, proved and sharp** (round 46), a
  seventh and independent attack family, and the first that attacks the problem from the
  *sharpness* side:
  - `OddCyclesDisjoint G`: the class in which **any two distinct odd cycles of `G` are
    vertex-disjoint** — a hypothesis about the intersection pattern of the odd cycles alone, with
    no degree bound, no length bound and no counting bound;
  - **`closeToBipartite_iff_packingLe`**: on that class the least odd cycle transversal and the
    largest odd cycle packing **are the same number** (Erdős–Pósa with the identity function,
    proved rather than quoted: `exists_transversal_onePerMember` gives one vertex per member of a
    maximum packing, `card_le_of_hitsOddCycles_of_disjointFamily` gives the converse counting, and
    `mem_of_oddCycle_of_maxPacking` makes every odd cycle a member of a maximum packing);
  - **`erdos73On_of_disjoint_oddCycles`: a new instance of the headline theorem with the OPTIMAL
    constant `f(k) = k`** — `LocIndep k G` plus `OddCyclesDisjoint G` forces `CloseToBipartite k G`,
    with no extra parameter, no bound on the odd girth and no bound on the number of branch
    vertices — and **`erdos73On_disjoint_oddCycles_iff`**, which shows that on this class the least
    Erdős constant is exactly `k` (witness `kTriangles k`, whose odd cycles are exactly its `k`
    fibres: `oddCycle_eq_tri_of_kTriangles`, `oddCyclesDisjoint_kTriangles`);
  - **`closeToBipartite_of_anticover`**: the composition lemma missing from all earlier rounds —
    the conclusion of Erdős #73 is **additive over an anticomplete decomposition** of the vertex
    set, so the instances compose (rounds 42–43 compose along 2-cuts, where the two sides share the
    two cut vertices and the constant pays an extra `2`);
  - **`class_hypothesis_is_necessary`** and **`packingNumber_one_not_enough`**: machine-checked
    negative results.  `LocIndep 3 (K_5)` holds and every packing of odd cycles of `K_5` has at most
    one member (`inter_nonempty_of_oddCycles_card`, `packing_card_le_one_completeGraph_five`), yet
    `K_5` is not `2`-close to bipartite; the single reason is
    `not_oddCyclesDisjoint_completeGraph_five` — the triangle `{0,1,2}` and the Hamiltonian
    `5`-cycle share the two vertices `0` and `1`.  So the identity function does not extend beyond
    the class, and a packing bound alone does not give the conclusion.

* `JSPProblem.Additive` — **strong additivity over anticomplete decompositions** (round 47), a new
  attack family built on the composition lemma `closeToBipartite_of_anticover` of
  `JSPProblem.Optimal`:
  - `JSP90.isOddCycle_sub_anticover` / `isOddCycle_sub_anticoverIn`: **a cycle never crosses an
    anticomplete split** (consecutive vertices of a cycle are adjacent, hence on the same side, and
    the predicate "`x ∈ A`" is preserved by the cyclic successor);
  - `JSP90.closeToBipartite_iff_add_anticover` and
    `JSP90.closeToBipartite_of_anticover_restrict`: **exact additivity in both directions** — the
    budget `m₁ + m₂` works for `G` iff it splits between the two sides, and a budget for `G`
    restricts to both sides;
  - `JSP90.AnticoverFamily` and `JSP90.closeToBipartite_of_anticoverFamily_cost`: the conclusion
    adds up over a family of pairwise disjoint, pairwise anticomplete pieces, with **no `+ 2`**
    (the 2-cut composition of round 43 pays for the two shared cut vertices);
  - `JSP90.card_le_of_pieces` / `JSP90.card_nonBipartiteParts_le`: the **counting lemma** — at most
    `k` pieces of an anticomplete family are non-bipartite;
  - `JSP90.erdos73On_of_anticover_decomposition`: **a new instance of the headline theorem** — if
    `V` is partitioned into pairwise anticomplete pieces (the shape of the connected components)
    and every non-bipartite piece is `m`-close to bipartite, then `LocIndep k G` forces
    `CloseToBipartite (k * m) G`, a constant **independent of the number of pieces**.

* `JSPProblem.Connect` — **the connectivity and 1-cut reductions** (round 48), a ninth attack family
  built on the composition lemma `JSPProblem/Additive.lean` and the 2-cut machinery of
  `JSPProblem/Separator.lean`:
  - `compPiece` / `compPieces` and **`anticoverDecomposition_compPieces`**: the connected components of
    `G` form an `AnticoverDecomposition` — pairwise disjoint, pairwise anticomplete, covering `V`,
    anticomplete to the complement of their union; and `compPiece_piecePreconnected` is the
    irreducibility of a component;
  - `card_le_of_pieces_pack` and `oddCycleErdosPosa_of_anticover_decomposition`: the counting lemma
    and round 47's instance in the **Erdős–Pósa** form (the *packing number* replaces the
    `LocIndep` parameter, which is the form the research statement is phrased in);
  - `erdos73On_of_connected_components`: **a new instance of the headline theorem** — if every
    connected component of `G` is `m`-close to bipartite, then `LocIndep k G` forces
    `CloseToBipartite (k * m) G`, a constant independent of the number of components;
  - `PieceErdős73On` / **`erdos73On_of_piece` / `erdos73_of_erdos73_piece`**: **Erdős #73 reduces
    to connected pieces** at the price of one factor `k` (`PiecePreconnected G s` = any two vertices
    of `s` are joined by a path of `G`; for `s = V` this is `G.Preconnected`), and
  - `PieceOddCycleErdosPosa` / **`oddCycleErdosPosa_of_piece` / `erdos73_of_connected_erdosPosa`**:
    **the research statement reduces to the connected case** with the explicit bound `r * m`;
  - `OneSplit` — a **1-cut** `V = {v} ⊔ T₁ ⊔ … ⊔ T_t` (the counterpart of `VertexSplit`, a 2-cut),
    with `cycle_subset_part` (a cycle avoiding the cut vertex lies in a single part),
    **`isBipartite_of_bipartite_pieces`** (the 1-cut parity lemma: all *pieces* `T_i ∪ {v}`
    bipartite ⟹ `G` bipartite) and `one_nonBipartitePiece`;
  - **`erdos73On_of_1split_of_bounded_pieces`: a second new instance of the headline theorem**, with
    the constant `1 + m * k` — a 1-cut shares a *single* vertex with each of its pieces, so this
    improves on round 43's 2-cut constant `2 + m * k`; and `erdos73On_of_1split_pieces` chains it
    with the connectivity reduction, i.e. the classical step *connected → 2-connected*;
  - `HasProper1Split`, `NoProper1Split`, `OneDepth`, `oneBound` and
    **`oddCycleErdosPosa_of_noOneCut_of_bounded_oneDepth`**: the precise reduction along the 1-cut
    axis — Erdős–Pósa for odd cycles follows from the 1-cut-free case together with a uniform bound
    on the number of successive 1-cuts (the block-cut tree bound, the remaining missing lemma).
* `JSPProblem/Critical.lean` — the **tenth attack family** (round 53): *minimal transversals and
  critical cycles*, i.e. the interior of a single graph, with no decomposition at all:
  - `JSP90.exists_criticalCycle_of_minimal` / `exists_criticalTransversal_of_minimal`: minimality of
    an odd cycle transversal `X` gives, for each `x ∈ X`, an odd cycle meeting `X` exactly in `x`
    (the classical first step of the Reed–Robertson–Seymour–Thomas proof);
  - `JSP90.IntGraph`, `CriticalTransversal`, `disjoint_of_colour_eq`: the **critical intersection
    graph** — inside one colour class the critical cycles are pairwise vertex-disjoint;
  - **`JSP90.card_X_le_of_colouring_pack`** (and its `LocIndep` form `card_X_le_of_colouring`): the
    counting lemma — a `c`-colourable critical intersection graph gives `|X| ≤ c * k`, with no
    bound on the odd girth, on the cycle lengths, or on the connectivity of `G`;
  - **`JSP90.erdos73On_of_spread_transversal`**: a new instance of the headline theorem with the
    constant `c * k`; its `c = 1` case `erdos73On_of_disjoint_transversal` has the optimal constant
    `f(k) = k` and strictly generalises `erdos73On_of_no_branch`;
  - `packing_of_disjoint_transversal` / `card_le_of_disjoint_transversal`: for a 1-spread transversal
    the critical cycles are also a packing of the same size (packing number = transversal number);
  - **`JSP90.erdos73_of_spreadMinimalTransversal`**: the new, precise localisation of the missing
    lemma — Erdős Problem #73 follows as soon as every graph of odd cycle packing number at most `r`
    admits a minimal odd cycle transversal whose critical intersection graph is `r`-colourable.
* `JSPProblem.Deficiency` — **the maximum deficiency: the numerical form of Erdős's hypothesis**
  (round 54, the eleventh attack family).  `LocIndep k G` is a `∀ ∃` statement over all vertex sets;
  `MaxDef G = max { |X| - 2 α(G[X]) : X ⊆ V }` is a *number*, and the two are equivalent:
  - **`JSP90.locIndep_iff_maxDef_le`**: `LocIndep k G ↔ MaxDef G ≤ k`, and
    `JSP90.erdos73_iff_maxDef` restates the whole of Erdős Problem #73 in that language, so the
    hypothesis of the problem is a numerical bound on a function of `G` (what an induction on `|V|`
    or a minimal-counterexample argument needs);
  - **THE SANDWICH `ν(G) ≤ MaxDef G ≤ τ(G)`** (`JSP90.packing_le_maxDef_le_transversal`): every
    packing of odd cycles is at most as large as the maximum deficiency
    (`JSP90.card_le_of_maxDef_le`), which is at most every odd cycle transversal
    (`JSP90.maxDef_le_of_hitsOddCycles`, `JSP90.maxDef_le_closeToBipartite` — the *new* direction:
    a transversal must be at least as large as the deficiency).  This is exactly the chain along
    which the Erdős–Pósa theorem would prove JSP-000090, with `MaxDef` in place of the packing
    number;
  - **`JSP90.maxDef_eq_zero_iff`**: deficiency `0` is bipartiteness, i.e. the proved case `k = 0`
    (`JSP90.erdos73_zero`) in the new language;
  - the exact values on the two extremal witnesses: **`JSP90.maxDef_kTriangles`**,
    `JSP90.maxDef_completeGraph` (`MaxDef (K_n) = n - 2`), together with
    `closeToBipartite_kTriangles_iff_maxDef` and `closeToBipartite_completeGraph_iff_maxDef`, which
    say that on those graphs the number of vertices to delete *is* the deficiency;
  - the arithmetic: `JSP90.maxDef_mono`, `maxDef_induceFinset_le`, **`maxDef_deleteFinset_le`** (the
    residue inherits the bound — an induction on `MaxDef G` is now possible),
    `maxDef_le_maxDef_induceFinset_add_card` (local-to-global), and
    **`JSP90.card_indepCard_anticover_add`** / `defOf_le_add_of_anticover` /
    `maxDef_le_add_of_anticover` (the deficiency splits, and is *subadditive*, over an anticomplete
    decomposition — equality fails, e.g. a triangle disjoint from an isolated vertex, and that
    failure is recorded in the file);
  - **`JSP90.LinearErdős73` / `erdos73Of_linearErdős73`**: a *linear* statement about the deficiency,
    `τ(G) ≤ C * MaxDef G` for a universal `C`, would prove the whole of Erdős #73 with constant
    `C * k`; it is a strictly weaker input than Erdős–Pósa, and `not_linearErdős73_zero` refutes it
    for `C = 0` (witness `K_3`).

The full theorem `Erdős73 k` for every `k ≥ 0` is Reed 1999, *Mangoes and Blueberries*, Combinatorica
19 (1999) 267–296.  Everything except the Erdős–Pósa theorem for odd cycles
(`JSP90.OddCycleErdosPosa`, Reed–Robertson–Seymour–Thomas 2002) is proved, and
`JSP90.erdos73_of_erdosPosa` shows that this single statement is all that is missing.
Round 59 added a *twelfth* attack family, `JSPProblem/OffCycle.lean` (40 declarations): the
deficiency **off an odd cycle**.  It proves the exact additivity of the deficiency between an odd
cycle and a set separated from it (`JSP90.maxDef_ge_one_add_maxDef_of_oddCycle`:
`1 + MaxDef G[X] ≤ MaxDef G`), which answers the secondary blocker recorded in
`discovery/JSP-000090/policy.json` about the anticomplete additivity of `MaxDef`; it makes the
induction measure decrease (`JSP90.maxDef_offCycle_le`, `JSP90.locIndep_of_separated_oddCycle`); and
it turns this into **a new instance of the headline theorem proved by an induction on the
deficiency**, `JSP90.erdos73On_of_layered`: for graphs whose odd cycles are *layers* (pairwise
vertex-disjoint, each separated from everything outside it, and every odd cycle of `G` being one
of them) Erdős #73 holds with the **sharp constant `k`**, and the class is attained
(`JSP90.layeredOddCycles_kTriangles`).  Round 35
added the local fan machinery of `JSPProblem/Fan.lean` (arcs, the odd-arc parity count, the fan
lemma, the short-arc lemma at a shortest odd cycle, and the resulting 2-cut structure); what is
still missing there is the *global* step from that local structure to a transversal bound.  Round 38
added a *third* attack family, `JSPProblem/Branch.lean` (delete the branch vertices; in a graph of
maximum degree `≤ 2` the odd cycles are pairwise disjoint, so Erdős–Pósa holds with the optimal
function there), which gives the new instances `erdos73On_of_bounded_branch` and
`erdos73On_of_no_branch` of the headline theorem.  The research statement itself
(`OddCycleErdosPosa r` for arbitrary `r`) is **not** proved here, so `jsp_000090_main` is
deliberately not declared.
* `JSPProblem.Boundary` — **the boundary of an odd cycle, and a new instance of the headline
  theorem** (round 61):
  - `JSP90.neighOf` / `JSP90.boundary G C = N(C) \ C` — the *fan* of the classical argument, and
    the class `JSP90.BoundedBoundary d G` (every odd cycle has at most `d` vertices outside it that
    touch it), which is hereditary (`JSP90.boundedBoundary_induceFinset`) and has the exact value
    `n - 3` on complete graphs;
  - `JSP90.outerLayer G C = V \ (C ∪ N(C))` — the vertices at distance `≥ 2` from `C`,
    **separated from `C` by construction**, so the deficiency induction drops there
    (`JSP90.maxDef_outerLayer_le`, `JSP90.locIndep_outerLayer`) with *no* hypothesis on `G` near `C`;
  - `JSP90.eq_of_isOddCycle_subset_shortest` and `JSP90.exists_bipartite_delete_of_shortest_oddCycle`
    — the local structure at a shortest odd cycle: it contains no proper odd cycle, and it becomes
    bipartite after **any** one of its vertices is deleted;
  - `JSP90.hitsOddCycles_of_bipartite_outer` and `JSP90.closeToBipartite_of_bipartite_outerLayer` —
    the local absorption statement: if the part of `G` at distance `≥ 2` from a shortest odd cycle is
    bipartite, then `G` is `1 + |boundary|` close to bipartite;
  - **`JSP90.erdos73On_of_bounded_boundary` — A NEW INSTANCE OF THE HEADLINE THEOREM**:
    `LocIndep k G` + `BoundedBoundary d G` gives `CloseToBipartite (k * (d + 1)) G`, by induction on
    `k` through the outer layer.  At `d = 0` the constant is the sharp `k` of
    `JSP90.erdos73On_of_layered`; at `d = 2` it applies to `K_5`, the witness that no earlier
    instance reaches.
-/
import JSPProblem.Definitions
import JSPProblem.Reed
import JSPProblem.OddCycle
import JSPProblem.Packing
import JSPProblem.Transversal
import JSPProblem.Fan
import JSPProblem.Branch
import JSPProblem.Sharp
import JSPProblem.Residue
import JSPProblem.Chord
import JSPProblem.Separator
import JSPProblem.Count
import JSPProblem.Weight
import JSPProblem.Optimal
import JSPProblem.Additive
import JSPProblem.Connect
import JSPProblem.Critical
import JSPProblem.Deficiency
import JSPProblem.OffCycle
import JSPProblem.Boundary
