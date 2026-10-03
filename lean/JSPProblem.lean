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
* `JSPProblem.CutTriangle` — the **cut triangle**, and **the reduction of Erdős #73 to two local
  statements** (round 64, 26 declarations).  It closes the two gaps left by
  `JSPProblem/Cut.lean` and then runs the induction on `k`:
  - `JSP90.indepCard_induceFinset_inter_add_sdiff` — **α of an induced subgraph splits off the
    vertices outside it**, `α(G[U], Y) = α(G[U], Y ∩ U) + |Y \ U|` (they are isolated in `G[U]`),
    hence `JSP90.maxDef_eq_maxDefIn_induceFinset : MaxDef (induceFinset G U) = maxDefIn G U`:
    the deficiency of a *piece* is the deficiency inside the piece, and an induction on Erdős's
    parameter can be run over the pieces of a cut;
  - `JSP90.anticoverCoverFamily_compPieces_sub` — the components of a subgraph, restricted to a
    vertex set on which the two graphs agree, are pairwise anticomplete *in the ambient graph*;
  - **`JSP90.CutTriangle G T`** (`T.card = 3` and no edge of `G` joins `T` to `V \ T`) and
    `JSP90.cutPieces G T` = the components of `G[V \ T]` intersected with `V \ T`; with
    `JSP90.anticoverCut_of_cutTriangle` they form the `AnticoverCut` of
    `JSPProblem/Cut.lean`, and
    **`JSP90.closeToBipartite_of_cutTriangle` is a new instance of the headline theorem at a
    canonical cut** (`3 + k * m`, no bound on odd girth, packing weight or branch vertices);
  - **`JSP90.maxDefIn_le_of_cutPiece` / `JSP90.locIndep_piece_of_cutTriangle`** — the descent:
    at a cut triangle every piece satisfies `LocIndep (k - 1)`, the step of the classical
    induction;
  - **`JSP90.erdos73_of_triangleFree`: ERDŐS PROBLEM #73, IN
    FULL, FROM `JSP90.TriangleFreeErdős73` (the triangle-free case) AND
    `JSP90.CutTriangleErdős73` (a cut triangle, or already `cutBound k`-close to bipartite)**,
    with the constant `JSP90.cutBound`, `cutBound 0 = 1`, `cutBound (k+1) = 3 + (k+1) * cutBound k`.
    **A correction to rounds 62–63: the planned constant `4 ^ k` cannot work**, since the instance
    of round 63 costs `3 + k * f (k-1)` and `3 + k * 4^(k-1) > 4^k` for `k ≥ 5`;
  - `JSP90.not_cutTriangle_completeGraph_four` — a **machine-checked negative result**: in `K_4`
    no `3`-clique cuts the graph, so `CutTriangle` is a hypothesis and not a theorem;
    `JSP90.erdos73_of_triangleFree_of_allTrianglesCut` closes the reduction on the class of graphs
    whose triangles all cut.
  - **`JSP90.erdos73On_of_bounded_boundary` — A NEW INSTANCE OF THE HEADLINE THEOREM**:
    `LocIndep k G` + `BoundedBoundary d G` gives `CloseToBipartite (k * (d + 1)) G`, by induction on
    `k` through the outer layer.  At `d = 0` the constant is the sharp `k` of
    `JSP90.erdos73On_of_layered`; at `d = 2` it applies to `K_5`, the witness that no earlier
    instance reaches.
* `JSPProblem.Touch` — the **touching axis** (round 74), the twenty-third attack family.  Round 73
  had to state, as a second conjunct of `JSP90.FanCriticalErdős73 c`, that a minimal transversal of
  the odd cycles *contained* in `∂C` also meets every odd cycle that merely *touches* `∂C` — and
  recorded that this is **not** automatic.  This file removes that conjunct by changing the family:
  - **`JSP90.Touches`, `JSP90.HitsTouching`, `JSP90.MinTouching`** — the touching family of odd
    cycles, its transversals and its minimal transversals;
  - **`JSP90.exists_criticalTouchCycle_of_minimal`** — for every vertex of a minimal transversal of
    the *touching* family there is an odd cycle **touching** `∂C` and meeting `X` in exactly that
    vertex; the touching property is then the definition, not a conjunct
    (`JSP90.minTouching_hits`);
  - **`JSP90.card_touchTransversal_le_of_colouring` / `card_touchTransversal_le_one`** — the
    counting: `|X| ≤ c * k` (round 73's `k − 1` becomes `k`, the price of the touching property);
  - **`JSP90.TouchCriticalErdős73 c`, `erdos73_on_of_touchCritical`,
    `JSP90.erdos73_of_touchCritical`** — the remaining statement of JSP-000090 with **one** conjunct,
    and **`JSP90.TouchCriticalErdős73.of_fanCritical`**, which shows round 73's hypothesis implies it:
    the two are the same missing lemma;
  - **`JSP90.EdgelessOutside`, `erdos73On_of_edgelessOutside`,
    `JSP90.erdos73On_of_bounded_neighbourhood` — a new instance of the headline theorem on the
    degree axis**: if all of `G`'s edges touch a set of at most `m` vertices then `G` is `m`-close to
    bipartite, with no bound on the odd girth, the packing number, the packing weight or the number
    of branch vertices.
* `JSPProblem.Petersen` — **the deficiency-one axis: the Petersen graph with one vertex deleted, and
  the improved lower bound `f(k) >= 2 k`** (round 76, the twenty-fourth attack family).  This is the
  first file that *improves a quantitative statement about the headline theorem* rather than
  reformulating it.  `JSPProblem/Sharp.lean` proved `f(k) >= k` with `kTriangles k`; here the witness
  is `p9`, the nine-vertex Petersen graph with one outer vertex deleted, whose deficiency is exactly
  one and whose least odd cycle transversal is exactly two:
  - `p9`, `p9Edge`, `p9_adj`, `cyc5`, `isOddCycle_Ca/Cb/Cc/Cd`: the witness and four of its 5-cycles;
  - **`JSP90.locIndep_one_p9`** (`LocIndep 1 p9`, i.e. maximum deficiency at most one, by exhaustive
    decision over the `512` vertex sets), **`JSP90.not_locIndep_zero_p9`** (its deficiency is exactly
    one) and **`JSP90.triangleFree_p9`** (the improved lower bound already holds for triangle-free
    graphs, the class of rounds 61-74);
  - **`JSP90.exists_oddCycle_av` / `exists_oddCycle_data_av`**: every vertex of `p9` is avoided by one
    of the four 5-cycles, and **`JSP90.exists_oddCycle_delete_av`**: the residue of `p9` at any single
    vertex still carries an odd cycle, whence
    **`JSP90.not_closeToBipartite_one_p9`**;
  - **`JSP90.closeToBipartite_two_p9`**: `p9` is `2`-close to bipartite, with the explicit
    transversal `{2, 6}` and the explicit 2-colouring `{0,7,8} | {1,3,4,5}` of the residue, so the
    least odd cycle transversal of `p9` is **exactly two**;
  - `p9Family k` on `Fin 9 x Fin k`, the disjoint union of `k` copies, with
    **`JSP90.locIndep_p9Family`: `LocIndep k (p9Family k)`** (fibre-wise counting), and
    **`JSP90.closeToBipartite_p9Family_iff`: `CloseToBipartite m (p9Family k) <-> 2 * k <= m`**, the
    *exact* value of the conclusion on that class of graphs;
  - **`JSP90.erdos73_lower_bound_two` / `JSP90.no_constant_below_two_k`: `f(k) >= 2 k`**, which
    *strictly improves* `JSP90.erdos73_lower_bound` (`f(k) >= k`) of `JSPProblem/Sharp.lean`: for every
    `k` and every `m < 2 k` there is a finite graph satisfying `LocIndep k` which is not `m`-close to
    bipartite.

* `JSPProblem.Cactus` — **the ODD CACTUS axis** (round 81), the twenty-eighth attack family: the
  class on which Erdős #73 holds at `k = 1` with the **optimal** constant `1`, on graphs of unbounded
  degree and unbounded odd girth.
  - `JSP90.OddCactus G` = `JSP90.LinearOddCycles G ∧ JSP90.TwoHellyOddCycles G`: two *distinct* odd
    cycles of `G` meet in at most one vertex, and three pairwise meeting odd cycles have a common
    vertex (no **ring** of three odd cycles meeting in three distinct vertices).  The hypothesis is
    purely about how the odd cycles intersect — no degree, no odd girth, no connectivity, no
    decomposition — and it **contains** round 39's class
    (`JSP90.OddCactus.of_oddCyclesDisjoint`);
  - `JSP90.disjoint_of_attach_ne`: **the structural lemma** — two odd cycles that meet a common odd
    cycle at *different* vertices are disjoint;
  - **`JSP90.closeToBipartite_one_of_oddCactus_of_locIndep_one`** and, in the `Erdős73On` form,
    **`JSP90.erdos73On_oddCactus_one`**: `LocIndep 1 G → OddCactus G → CloseToBipartite 1 G`, a
    **new instance of the headline theorem with the optimal constant `1`**; Erdős's hypothesis
    enters only through the packing bound at `k = 1`, the key step being
    `JSP90.exists_commonVertex_oddCactus_of_locIndep_one` (in an odd cactus with `LocIndep 1` all the
    odd cycles have a common vertex);
  - **`JSP90.erdos73On_oddCactus`**: a new instance at every `k`, with the constant `k * (k + 1)`;
  - `JSP90.LinearRing`, `JSP90.twoHelly_of_linearRing`, `JSP90.oddCactus_iff`: **the remaining
    statement**, the classical *ring lemma*, stated as a `def` and *not* assumed
    (`JSP90.OddCactus G` is exactly `LinearOddCycles G ∧ LinearRing G`).

* `JSPProblem.Sun` — **the sharpness half of the ODD CACTUS axis** (round 81), all by machine check:
  - `K₃` is an `OddCactus` graph (`JSP90.oddCactus_completeGraph_three`), satisfies `LocIndep 1`, and
    is not bipartite (`JSP90.not_closeToBipartite_zero_completeGraph_three`): **so `f(1) = 1`
    exactly on the new class**, against the constant `2` of `JSPProblem/Cover.lean`;
  - `JSP90.oddCactus_kTriangles`: the class contains round 39's sharp witness `kTriangles k`, whose
    least odd cycle transversal is exactly `k`;
  - `sun3`, the **3-sun** (six vertices: a triangle with a degree-two vertex on each edge), with
    `JSP90.locIndep_one_sun3` and `JSP90.not_closeToBipartite_one_sun3`: it satisfies `LocIndep 1`
    and its least odd cycle transversal is exactly **two** — a six-vertex witness for `f(1) >= 2`,
    against the nine-vertex `p9` of round 76 — while `JSP90.not_twoHelly_sun3`,
    `JSP90.not_linear_sun3` and `JSP90.not_oddCactus_sun3` show its three peripheral triangles form a
    ring, so **the two-Helly hypothesis cannot be dropped** and the class is cut exactly where it
    must be.

- `JSPProblem.Helly` — **the HELLY axis** (round 83, attack family 30), the **thirtieth** attack family
  and the first that does not add instances to an existing class but *characterises* one:

  - `JSP90.HellyOddCycles G` — the odd cycles of `G` form a **Helly family**: every finite family of
    pairwise meeting odd cycles has a common vertex.  This is the full Helly property, as opposed to
    round 81/82's `JSP90.TwoHellyOddCycles G`, which asks only for the three-element case;
  - **`JSP90.helly_of_linearOddCycles : LinearOddCycles G → HellyOddCycles G`** — **the Helly lemma**:
    in a graph whose odd cycles are linear, the odd cycles form a Helly family.  Round 82's ring
    lemma kills rings of *three*; this kills non-Helly families of *any* size, by strong induction on
    `|𝒞|` whose inductive step consumes the ring lemma.  `JSP90.twoHelly_of_helly` then recovers
    round 82's class;
  - **`JSP90.closeToBipartite_one_of_helly_of_locIndep_one`, `JSP90.erdos73On_helly_one`** — a **new
    instance of the headline theorem at `k = 1` with the optimal constant `1`, under the strictly
    weaker hypothesis `HellyOddCycles G`**: Erdős's hypothesis enters only through the packing bound
    at `k = 1`, and there is no bound on the odd girth, the degrees, the packing weight, the branch
    vertices or the number of components;
  - `JSP90.helly_completeGraph_three`, `JSP90.not_helly_attained_zero` — `K₃` attains the constant, so
    `f(1) = 1` **exactly** on the Helly class;
  - **`JSP90.HellyOfNonlinear`** — the **diamond** `K₄` minus an edge has the Helly property, satisfies
    `LocIndep 1` and is one vertex away from bipartite, yet is **not** linear (its two triangles meet
    in two vertices).  Hence the new instance is **not** a corollary of round 82's, and the Helly class
    strictly contains round 82's;
  - `JSP90.HellyErdős73 f` — **the remaining statement** for the Helly class at a general constant,
    a `def`, **not** assumed; Part 3 is its proved base level.  Behind it stands
    `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.
* `JSPProblem.Witness` — **the maximum-deficiency witnesses** (round 86, attack family 32).  Round 84
  reduced Erdős #73 on the Helly class to the vertex descent `JSP90.HellyMaxDefDescent`; this file
  proves the numerical content of that descent and replaces the blocker by a weaker one:
  - **`JSP90.card_inter_ge_maxDef`, `JSP90.inter_maxWitness_ne`** — **two maximum-deficiency
    witnesses of `G` overlap in at least `MaxDef G` vertices**, so the family of witnesses is
    pairwise intersecting (in contrast with the family of odd cycles);
  - **`JSP90.CommonMaxWitness G d`, `JSP90.defOf_le_sub_one_of_not_mem`,
    `JSP90.maxDef_add_one_le_maxDef_delete_of_common`** — **the descent in the form in which it is
    needed**: one vertex common to all witnesses of deficiency `d = MaxDef G` forces
    `MaxDef (G − {v}) + 1 ≤ MaxDef G`, with no hypothesis on odd cycles;
  - **`JSP90.commonWitness_iff_maxDef_descent`** — the descent is *equivalent* to the existence of a
    common witness vertex (machine-checked on all graphs with `n ≤ 6` vertices), so the new statement
    is exactly as strong as round 84's;
  - **`JSP90.HellyCommonMaxWitness`, `JSP90.TwoHellyCommonMaxWitness`** — the two missing lemmas, and
    **`JSP90.hellyCommonMaxWitness_of_hellyMaxDefDescent`** shows the new one implies round 84's;
  - **`JSP90.erdos73On_helly_of_commonWitness`, `JSP90.closeToBipartite_of_helly_of_commonWitness`,
    `JSP90.closeToBipartite_of_twoHelly_of_commonWitness`** — **Erdős #73 with the optimal constant
    `f(k) = k` on the Helly class and on the strictly larger two-Helly class** from those single
    statements.  Two machine-checked results of round 84 are corrected here (its `tau_` was an upper
    bound, so its "König fails on the Helly class" was an artefact: König's property *holds* there).
* `JSPProblem.PackDescent` — **the packing-weighted residue descent** (round 87, attack family 33).
  Round 84's descent and round 86's blocker are statements about **one** odd cycle and **one** vertex;
  this file generalises them to a whole packing and replaces the blocker by a strictly weaker one:
  - **`JSP90.maxDef_ge_card_add_maxDef_delete`** — **THE PACKING-WEIGHTED RESIDUE DESCENT**: for a
    family `𝒞` of pairwise vertex-disjoint odd cycles,
    `|𝒞| + MaxDef (deleteFinset G (⋃ 𝒞)) ≤ MaxDef G`.  The deficiency of `G` pays for a whole
    packing of odd cycles **at once**, which is the quantity that decreases along the classical
    Erdős–Pósa induction, in the language of the deficiency.  The one-cycle case
    (`JSP90.maxDef_ge_one_add_maxDef_delete`) is recovered, so nothing is lost;
  - **`JSP90.defOf_ge_add_card_biUnion`, `JSP90.defOf_biUnion_ge_card`,
    `JSP90.two_indepCard_biUnion_add_card_le_card`** — the union of `t` disjoint odd cycles has
    deficiency at least `t`, the `t`-fold version of `JSP90.defOf_oddCycle_ge_one`;
  - **`JSP90.card_inter_biUnion_ge_card_of_maxDef`** — a maximum-deficiency witness meets a packing
    of `t` odd cycles in **at least `t` vertices** (the packing counterpart of round 84's
    "a maximum-deficiency witness is an odd cycle transversal");
  - **`JSP90.SelfPay G d`, `JSP90.HellySelfPay`** — the **self-pay** form of the missing statement: a
    vertex set `Z` with `MaxDef (G − Z) + |Z| ≤ d`.  `JSP90.selfPay_of_commonWitness` shows it is
    implied by round 86's `JSP90.HellyCommonMaxWitness` (so it is **strictly weaker**), while
    `JSP90.erdos73On_helly_of_selfPay` / `JSP90.closeToBipartite_of_helly_of_selfPay` give **Erdős #73
    with the optimal constant `f(k) = k` on the Helly class** from it, and
    `JSP90.hellySelfPay_of_hellyErdős73` shows it is **equivalent to the instance** `HellyErdős73 id`
    itself.  Unlike the single-vertex descent it allows a whole set to be deleted in one step, which
    is what an absorption argument needs (round 44 proved the `+ 1` absorption step false).
* `JSPProblem.SplitOne` — **charging ONE vertex of a 2-cut instead of two** (round 88, attack
  family 34).  The 2-cut decomposition of `JSPProblem/Separator.lean` charged **both** vertices of a
  cut `{a, b}`; its header named the missing step exactly ("*a cycle meeting exactly one vertex of
  the cut lies in a piece*"), and this file proves it and applies it:
  - **`JSP90.VertexSplit.cycle_subset_insert`** — an odd cycle containing `a` and avoiding `b` lies
    in `T_i ∪ {a}` for a single `i` (the cycle minus `a` is a path, and no edge joins two parts);
  - **`JSP90.VertexSplit.oddCycle_piece_or_both`** — **the only odd cycles not contained in a piece
    are the ones containing *both* `a` and `b`**, which *strengthens*
    `JSPProblem.VertexSplit.oddCycle_piece_or_avoid` (a cycle meeting the cut in one vertex is still
    contained in a piece);
  - **`JSP90.VertexSplit.hitsOddCycles_one`, `JSP90.VertexSplit.exists_transversal_one`** — **THE
    SHARP CUT STEP**: a transversal of every piece together with the **single** vertex `a` is an
    odd cycle transversal of `G`, so `τ(G) ≤ 1 + Σᵢ τ(Tᵢ ∪ {a,b})` instead of round 78's
    `2 + Σᵢ τ(Tᵢ ∪ {a,b})`;
  - **`JSP90.erdos73On_of_split_one`** — **a new instance of the headline theorem**,
    `CloseToBipartite (1 + m * t) G`, strictly stronger than
    `JSPProblem.erdos73On_of_split` (`m * t + 2`); likewise
    `JSP90.erdos73On_of_split_one_of_bounded_branch` (`1 + (m + k) * t` instead of `2 + (m + k) * t`)
    and `JSP90.closeToBipartite_of_split_one_of_oddCycleErdosPosa`, the **Erdős–Pósa form** of the
    same step, which is what an induction on the Erdős–Pósa function along a 2-cut consumes;
  - **`JSP90.c5`, `JSP90.sp5`, `JSP90.sp5_split_one_attained`** — the `+ 1` is **necessary and
    attained**: the 5-cycle has a 2-cut whose two pieces are both bipartite (transversal number
    `0`), yet `c5` needs one deleted vertex, so `1 + m * t` cannot be lowered to `m * t`.
* `JSPProblem.HalfOne` — **the refined cut step: paying one cut vertex and only the cycles that
  avoid it** (round 89, attack family 35).  Round 88 still assumed a transversal of every *piece*
  `Tᵢ ∪ {a,b}`, i.e. of the odd cycles *through* `a` as well, which `a` itself already meets; this
  file weakens that per-piece obligation and obtains the classical cut lemma counted by the
  **packing number**:
  - **`JSP90.VertexSplit.hitsOddCycles_one_avoid`** — **THE REFINED CUT STEP**: a set `X i` meeting
    every odd cycle of the piece `Tᵢ ∪ {a,b}` which **avoids `a`** is enough, together with the
    single vertex `a`, to be an odd cycle transversal of `G`.  Equivalently
    (**`JSP90.VertexSplit.hitsOddCycles_half`**): a transversal of every **half-piece** `Tᵢ ∪ {b}`
    suffices — a **strictly weaker** hypothesis than round 88's, of which round 88's step is a
    corollary (`JSP90.VertexSplit.hitsOddCycles_half_of_hitsOddCycles_one`);
  - **`JSP90.VertexSplit.exists_transversal_half`, `JSP90.erdos73On_of_split_one_avoid`** — **new
    instances of the headline theorem** `CloseToBipartite (1 + m * t) G` from a hypothesis on the
    *half-pieces*, strictly stronger than round 88's `erdos73On_of_split_one` (full pieces), in both
    the `LocIndep k` and the Erdős–Pósa (`…_of_oddCycleErdosPosa`) forms;
  - **`JSP90.VertexSplit.closeToBipartite_one_avoid_of_clean`,
    `JSP90.erdos73On_of_split_one_avoid_of_clean`, `…_of_clean_pack`,
    `…_of_clean_of_bounded_branch`, `…_of_clean_swap`** — **THE PACKING-COUNTED CUT LEMMA WITH THE
    OPTIMAL `+1`**: `CloseToBipartite (1 + m * r) G` (`CloseToBipartite (1 + m * k) G` under
    `LocIndep k`), i.e. the constant is a function of the **packing number**, not of the number of
    pieces `t`, under the explicit *cleanliness* hypothesis "every **bipartite** part `Tᵢ` has a
    bipartite half-piece `Tᵢ ∪ {b}`".  This beats round 43's `2 + m * p` by one vertex and round
    88's `1 + m * t` by the counting, and is the step that turns the 2-cut decomposition into a
    genuine induction on the Erdős–Pósa function;
  - **`JSP90.plus_one_necessary_in_packing_form`, `JSP90.c5_closeToBipartite_one_from_clean_split`** —
    the `+1` is still **necessary** in the packing-counted form: on the clean 2-cut `sp5` of the
    5-cycle nothing is charged per piece and `c5` still needs one vertex.
* `JSPProblem.Windmill` — **the negative result of round 89: the cleanliness of a 2-cut is NOT
  automatic** (machine-checked).  The *windmill* `wf` (two triangles sharing one vertex, plus an
  isolated vertex) satisfies `LocIndep 1` and hence has **packing number one**
  (`JSP90.locIndep_one_wf`, `JSP90.packing_wf`, by exhaustive decision over the `2⁶` vertex sets),
  while **both** half-pieces of its 2-cut are triangles
  (`JSP90.not_isBipartite_half_wfs`).  So "the number of non-bipartite half-pieces is bounded by the
  packing number" is **false** (`JSP90.windmill_counting_fails`): the counting of the cut step must
  be done on the **parts** (`JSPProblem/Count.lean`) and the half-piece hypothesis of round 89 must
  be kept.  Note the obstruction is only to the *counting*: `wf` itself is one vertex away from
  bipartite (`JSP90.windmill_closeToBipartite_one`), as Erdős #73 predicts.
* `JSPProblem.CutVertex` — **the 2-cut axis is closed: `+1` needs the cleanliness hypothesis and
  `+2` needs none, and both are sharp.**  The local fact
  `JSP90.oddCycle_mem_b_of_halfPiece_of_isBipartite_part` says that over a **bipartite** part every
  odd cycle of the half-piece passes through the cut vertex, so a bipartite part costs nothing; the
  cut step `JSP90.VertexSplit.hitsOddCycles_both` then gives, with **no hypothesis on the cut at
  all**, the packing-counted lemma
  **`JSP90.VertexSplit.closeToBipartite_two_of_nonBipartiteParts`: `CloseToBipartite (2 + m * r) G`**
  from a packing bound `r` and `CloseToBipartite m` on the **half-pieces** `T_i ∪ {a}` of the
  non-bipartite parts — a strictly weaker hypothesis than round 43's
  `closeToBipartite_of_split_of_bounded_pieces_pack` (`2 + m * p`, on the *pieces*) and with no
  hypothesis where round 89's `closeToBipartite_one_avoid_of_clean` needed `hclean`.  In the two
  forms an induction consumes: `JSP90.closeToBipartite_of_split_step` and
  `JSP90.closeToBipartite_of_split_of_oddCycleErdosPosa_two` — **the induction step of the classical
  proof along a 2-cut, with no hypothesis on the cut** — and
  `JSP90.closeToBipartite_of_split_step_one_of_clean` (the `+1` form, `1 + m * r`);
  `JSP90.erdos73On_of_split_two_of_nonBipartiteParts` and
  `JSP90.erdos73On_of_split_two_of_nonBipartiteParts_of_bounded_branch` are **new instances of the
  headline theorem**.  The residue is exact
  (`JSP90.VertexSplit.sdiff_biUnion_half`, `JSP90.VertexSplit.isBipartite_delete_of_both`): the
  residue of the cut step is the union, over the parts, of the residues of the parts.  And the
  obstruction of round 89 is pinned exactly by
  `JSP90.hitsOddCycles_empty_iff_isBipartite_half`: **`X i = ∅` is a transversal of the half-piece
  iff the half-piece is bipartite**, i.e. iff the cut is clean, so no weakening of `hclean` is
  available and `+1` vs `+2` is the exhaustive choice (`JSP90.windmill_plus_two_plus_one`).
* `JSPProblem.MaxCut` — **the CUT AXIS: odd cycle transversals are exactly the sets covering the
  monochromatic edges of some cut.**  `JSP90.MonoEdge G A v w` is an edge that does not cross the
  cut with side `A`, and `JSP90.HitsMono G A Z` says `Z` meets all of them.
  - **`JSP90.exists_monoEdge_of_isOddCycle`** — **every odd cycle of `G` contains a monochromatic
    edge of *every* cut**, with both witnesses inside the cycle.  This is the load-bearing step
    (`JSP90.even_of_cycle_noMono`: a cycle all of whose edges cross a cut has even length, by the
    `cycSucc_pow_odd` parity argument of `JSPProblem/Transversal.lean`);
  - **`JSP90.hitsOddCycles_iff_hitsMono`** — **the odd cycle transversals of `G` are exactly the
    monochromatic covers of some cut** (`⟸` is the lemma above; `⟧` puts the transversal on one
    side together with a colour class of the bipartition of the residue);
  - **`JSP90.closeToBipartite_iff_hitsMono`** — **the conclusion of Erdős #73 *is* a cut
    certificate**: `CloseToBipartite q G ↔ ∃ A Z, HitsMono G A Z ∧ Z.card ≤ q`, with the explicit
    `2`-colouring `if v ∈ A then 0 else 1` of `G - Z` in `JSP90.isBipartite_deleteFinset_of_hitsMono`;
  - **new instances of the headline theorem**: `JSP90.erdos73On_of_hasMonoCover` (some cut carries a
    `q`-vertex monochromatic cover) and `JSP90.erdos73On_of_monoCoverBetween` (**one** set covering
    the monochromatic edges of **every** cut separating two given vertex sets — the multiway-cut
    formulation), with `JSP90.hasMonoCover_of_vertexCover` /
    `JSP90.monoCoverBetween_of_vertexCover` as elementary sources of certificates;
  - **exactness and obstructions**: `JSP90.exists_noMonoEdge_iff_isBipartite` (`q = 0` ⟺ bipartite),
    `JSP90.hasMonoCover_completeGraph_of_split` (on `K_n` the certificate is `n - 2`, exactly
    optimal), `JSP90.hasMonoCover_completeGraph_two_three` (a cut of `K_3` whose certificate is one
    vertex) and `JSP90.not_hasMonoCover_completeGraph_three` (**the certificate depends on the
    cut**: the trivial cut of `K_3` has no one-vertex certificate although `K_3` is `1`-close to
    bipartite).

* `JSPProblem.Finite` — **a finite search form of Erdős #73** (round 96, a new attack family):
  both the hypothesis and the conclusion of the statement are rewritten so that every quantifier
  ranges over an explicitly listed collection, which makes them kernel decision problems
  (`JSP90.LocIndepSearch`, `JSP90.CloseToBipartiteSearch`, `JSP90.erdos73On_fin`, plus
  `JSP90.isOddCycle_iff_bounded`: an odd cycle of a finite graph is a cyclic ordering of length
  `≤ |V|`); and with it the **six-vertex witness `g6`** (a triangle with one further vertex on each
  of its three edges) with `JSP90.closeToBipartite_iff_g6 : CloseToBipartite m g6 ↔ 2 ≤ m` and
  `JSP90.not_erdos73_fin6_one_one`, so the constant of Erdős #73 at `k = 1` is at least `2` on six
  vertices, a smaller witness than `JSPProblem/Petersen.lean`'s `p9`.
* `JSPProblem.DegColour` — **the DISJOINT-ODD-CYCLE and the DEGREE–COLOURING axes** (round 98, two
  new attack families):
  - **`JSP90.OddCycles G`**, the family of *all* the odd cycles of `G`, and
    **`JSP90.erdos73On_of_disjointOddCycles : LocIndep k G → DisjointFamily (OddCycles G) →
    CloseToBipartite k G`** — **a new instance of the headline theorem with the *optimal* constant
    `k` and a strictly weaker hypothesis than `JSPProblem/Branch.lean`'s**: the hypothesis is only
    "two distinct odd cycles are vertex-disjoint" (no degree bound, no odd-girth bound, no
    connectivity, no decomposition), and `JSP90.disjointFamily_oddCycles_of_no_branch` shows
    round 38's "every vertex has at most two neighbours" is used for this one conclusion and nothing
    else;
  - **`JSP90.erdos73On_disjointOddCycles_exact`** — the constant is *exactly* `k` on that class: the
    witness `kTriangles k` of `JSPProblem/Sharp.lean` has pairwise vertex-disjoint odd cycles
    (`JSP90.exists_eq_tri_of_isOddCycle_kTriangles`, `JSP90.disjointFamily_oddCycles_kTriangles`)
    and is not `(k - 1)`-close to bipartite;
  - **the greedy colouring theorem**, which the pinned Mathlib slice does not have in any form
    (`JSPProblem/Layer.lean` has to define `SimpleGraph.degree` by hand for the same reason):
    `JSP90.exists_colouringOn_of_degLe` (the greedy step, by strong induction on the size of the
    vertex set), `JSP90.coloring_of_degLe` (a graph of maximum degree `≤ d` is `Fin (d+1)`-
    colourable), `JSP90.coloring_of_maxDegLe` and `JSP90.card_clique_le_of_coloring` (the converse,
    in the only form in which it is true: a `(d+1)`-colouring bounds the size of a *clique*);
  - **`JSP90.OddColorClass` / `JSP90.closeToBipartite_of_oddColorClass` /
    `JSP90.erdos73On_of_oddColorClass`** — **a colour class is a certificate for the conclusion of
    Erdős #73**: one colour class meeting every odd cycle and of size `≤ q` gives
    `CloseToBipartite q G`.  This is the only form in which a colouring argument can be used, and
    properness alone is not a certificate (machine-checked at `JSP90.g6`).
* `JSPProblem.Sparse` — **the EDGE-COUNTING axis** (round 99, one new attack family).  Every axis so
  far counts *vertices*; this one counts **edges**, and gets the classical *local* bound that
  `JSPProblem/MaxCut.lean` recorded as the missing one:
  - `JSP90.degSum G = ∑ v |N(v)|` and `JSP90.edgeCount G = |E(G)|` (Mathlib's
    `SimpleGraph.edgeFinset`), with `JSP90.two_mul_edgeCount : 2 * |E(G)| = degSum G`
    (`SimpleGraph.sum_degrees_eq_twice_card_edges`);
  - `JSP90.degSum_deleteFinset : degSum (G - v) + 2 * |N(v)| = degSum G` and
    `JSP90.edgeCount_deleteFinset : |E(G - v)| = |E(G)| - |N(v)|` — the invariant of the induction;
  - `JSP90.two_le_card_neigh_of_mem_oddCycle` — **every vertex of an odd cycle has at least two
    neighbours** (the two cycle-neighbours), which is what makes such a vertex the right thing to
    delete;
  - **`JSP90.closeToBipartite_of_edgeCount_le : |E(G)| ≤ 2 * m + 1 → CloseToBipartite m G`**, i.e.
    **`τ_odd(G) ≤ ⌊ |E(G)| / 2 ⌋`** — the classical max-cut counting bound — and its
    `degSum`-only form `JSP90.closeToBipartite_of_degSum_le`;
  - **`JSP90.erdos73On_of_edgeCount` — a NEW INSTANCE of the headline theorem** for the class of
    graphs with a bounded number of edges, whose constant does **not** mention `k`: the local
    hypothesis `LocIndep k G` is never used, and this file records *why* (`LocIndep 0` **is**
    bipartiteness, `JSP90.locIndep_zero_of_isBipartite`, and bipartite graphs have arbitrarily many
    edges), which is also recorded as the unproved statement `JSP90.LocIndepEdgeUnbounded`;
  - `JSP90.edgeCount_le_card_mul_maxDeg` and `JSP90.closeToBipartite_of_maxDegLe_of_card_le`
    (hence `JSP90.erdos73On_of_maxDegLe_of_card_le`) — the order-dependent instance `τ ≤ |V| Δ / 4`;
  - **sharpness**: `JSP90.edgeCount_completeGraph_three`, `K_3` is not `0`-close to bipartite and
    `JSP90.edgeCount_bound_tight_completeGraph_three`, so `⌊ |E| / 2 ⌋` is attained and cannot be
    improved; `JSP90.closeToBipartite_kTriangles_of_edgeCount` shows the bound is loose in the
    direction of the deficiency (`kTriangles k` needs `k`, the edge count gives `3 k`);
  - the remaining statement of the axis, **stated and not assumed**:
    `JSP90.BoundedOddGirthEdgeCount` (odd girth `ℓ` and degree `≤ d` ⟹ `f ℓ d`-close to bipartite).
* `JSPProblem.Pivot` — **the LOCAL-TRANSVERSAL axis** (round 100, one new attack family).  Where
  must the odd cycle transversal sit?  `JSPProblem/Transversal.lean` puts it on a maximum packing and
  `JSPProblem/Sparse.lean` counts edges; this file puts it *around* one:
  - `JSP90.NeighClosed G C = C ∪ ∂C`, `JSP90.mem_neighClosed`, `JSP90.disjoint_boundary`,
    `JSP90.card_neighClosed_eq_add`;
  - **`JSP90.hitsOddCycles_neighClosed_of_maxPacking` — the distance-one neighbourhood of the union
    of a maximum packing of odd cycles is an odd cycle transversal** (an odd cycle missing it could be
    added to the packing), with `JSP90.card_neighClosed_maxPacking_le` for its size;
  - the counting at an odd cycle in **every** degree range:
    `JSP90.two_le_card_inter_neigh_of_mem_oddCycle` (a vertex of an odd cycle has two neighbours *on*
    it), `JSP90.card_boundary_le_card_mul_sub_two` (generalising `JSPProblem/Subcubic.lean`'s
    `card_boundary_le_card_oddCycle` from `d = 3` to every `d ≥ 2` and every set `S`),
    `JSP90.card_neighClosed_le_card_mul_sub_one` (generalising
    `card_neighClosed_le_two_mul_card_oddCycle`), and `JSP90.erdos73On_of_neighClosedPacking`
    (`LocIndep k` + degree `≤ d` + odd cycles of length `≤ ℓ` ⟹ `CloseToBipartite (ℓ * k * (d - 1))`,
    with the transversal *exhibited* as that neighbourhood);
  - **the two-level odd-girth ladder**: `JSP90.closeToBipartite_of_twoLevelGirth` (pay `ℓ₁` for a
    cycle of at most `ℓ₁` vertices, then `ℓ₂ * (k - 1) * (d - 1)` for the residue),
    `JSP90.closeToBipartite_of_ladder_uniform`, `JSP90.erdos73On_of_ladder`,
    `JSP90.erdos73On_of_ladder_subcubic` (constant `ℓ * (2 k - 1)`) and
    `JSP90.closeToBipartite_of_twoLevelGirth_degreeTwo` (no degree factor at `d = 2`);
  - **exactness at maximum degree `≤ 2`, for every `k`**:
    `JSP90.disjointFamily_oddCycles_of_maxDegLe_two`,
    `JSP90.maxDegLe_two_iff_oddCyclePackingLe` (`CloseToBipartite m G ↔ OddCyclePackingLe m G`, i.e.
    `τ_odd = ν_odd`), `JSP90.erdos73On_of_maxDegLe_two` with the optimal constant `k`, and
    `JSP90.erdos73On_of_maxDegLe_two_optimal` / `JSP90.closeToBipartite_kTriangles_of_maxDegLe_two`
    (attained on `kTriangles k`);
  - **two machine-checked refutations**: `JSP90.not_boundedOddGirthEdgeCount` — round 99's recorded
    target `JSP90.BoundedOddGirthEdgeCount` is **false** (odd girth and degree alone do not bound the
    transversal, `JSP90.maxDegLe_two_unbounded_oddCycles`) — and
    `JSP90.not_oddGirth_bound_without_packing`, which pins the *direction*: an odd girth from **below**
    (`JSP90.OddGirthGe ℓ G`) bounds nothing, whereas the upper bound on odd cycle length used by
    `JSPProblem/Transversal.lean` is the one that works.
* `JSPProblem.Stair` — **the ODD-GIRTH LADDER axis** (round 101, one new attack family).  Each
  level of a residue chain pays *its own* girth, so the constant of Erdős #73 becomes a **sum**:
  - `JSP90.residueOf H C j` — level `j` of a chain of odd cycles (the residue after deleting
    `C 0, …, C j.succ`), `JSP90.residueOf_zero`, and the **shift identity**
    `JSP90.residueOf_succChain`: inside `H - C 0` the tail `C 1, …, C (n-1)` walks exactly the tail of
    the original chain, which is what makes the induction step go through;
  - `JSP90.IsOddCycleChain` and `JSP90.isOddCycleChain_succChain`;
  - **`JSP90.closeToBipartite_of_girthLadder` — THE ODD-GIRTH LADDER**: a chain of odd cycles of
    length at most `g j` at level `j`, and packing number at most `n`, give
    `CloseToBipartite (g 0 + g 1 + … + g (n-1)) G`, with **no degree bound, no packing-weight bound
    and no uniform bound on odd cycle length** (`JSP90.closeToBipartite_of_girthLadder_fin` is the
    `Fin`-indexed form, `JSP90.girthSum`/`JSP90.girthSum_succ` its arithmetic);
  - **`JSP90.erdos73On_of_girthLadder` — a new instance of the headline theorem**, and
    `JSP90.closeToBipartite_of_girthLadder_uniform` / `JSP90.erdos73On_of_girthLadder_uniform`
    *re-derive* `JSPProblem/Transversal.lean`'s `ℓ * k` instance from the ladder, so that the
    comparison is precise: the ladder is strictly stronger because its constant sees the sequence of
    level girths, not only their maximum (`JSP90.girthLadder_sum_le_sub_one_mul`);
  - **`JSP90.erdos73On_of_girthLadder_staircase` with the closed-form constant `k² + 2k`**
    (`JSP90.girthSum_arith`, `JSP90.staircase_const`) for a chain whose levels grow like `3, 5, 7, …`,
    and `JSP90.staircase_lt_uniform` machine-checks `k² + 2k < (2k + 1) * k` for `k ≥ 2`;
  - `JSP90.isBipartite_of_oddCyclePackingLe_zero` — packing number `0` means bipartite, the base case
    of every packing-number induction of this development in one line.
* `JSPProblem.Greedy` — **the GREEDY SHORTEST-ODD-CYCLE axis** (round 102, one new attack family).
  Round 101's ladder *assumed* a chain of odd cycles, one per residue level; this file **derives the
  chain from the graph** — delete the *shortest* odd cycle, then the shortest odd cycle of the
  residue, and so on — with **no girth hypothesis at all**:
  - `JSP90.girthOf H` — the number of vertices of a shortest odd cycle of `H` (`0` if `H` is
    bipartite), `JSP90.shortestOddCycle` / `JSP90.greedyCycle H` — such a shortest odd cycle
    (`∅` if there is none), with `JSP90.girthOf_le` and `JSP90.card_greedyCycle_le_girthOf`;
  - `JSP90.level H j` — the residue after deleting the greedy cycles of the `j` earlier levels,
    `JSP90.unionUpTo H j` — the set deleted, `JSP90.level_eq_deleteFinset_unionUpTo` — the two are
    complementary, and `JSP90.residueOf_greedyChain` identifies level `j` of the greedy chain with
    `JSP90.residueOf` of `JSPProblem/Stair.lean`;
  - **`JSP90.disjoint_greedyCycle_of_lt` — the greedy step**: two greedy cycles of different levels
    are vertex-disjoint (`JSP90.vertsOf`, `JSP90.isOddCycle_subset_vertsOf`,
    `JSP90.not_mem_of_mem_vertsOf_deleteFinset`), hence
    **`JSP90.packing_of_levels`**: `n` non-bipartite levels give `n` disjoint odd cycles, and
    **`JSP90.level_isBipartite_of_locIndep`**: Erdős's hypothesis makes the `k`-th level bipartite;
  - `JSP90.firstBipartiteLevel`, `JSP90.firstBipartiteLevel_spec/min`,
    `JSP90.not_isBipartite_of_lt_firstBipartiteLevel`, `JSP90.isBipartite_of_ge_firstBipartiteLevel`
    — where the greedy construction stops;
  - **`JSP90.closeToBipartite_of_greedyChain_step`** — the ladder *without* any packing bound: the
    chain of the first `n` greedy cycles plus a bipartite residue at level `n` pay the sum of the
    level girths (via the self-similarity `JSP90.level_tail`);
  - **`JSP90.erdos73On_of_greedyChain` / `JSP90.erdos73On_of_greedyChain_univ` — a new instance of
    the headline theorem**: `LocIndep k G → CloseToBipartite (∑ j : Fin k, girthOf (level G j)) G`,
    the hypothesis being **exactly** Erdős's own, and the constant being read off the graph; the
    transversal is exhibited (`JSP90.closeToBipartite_of_greedyChain`,
    `JSP90.hitsOddCycles_greedyChain`);
  - the comparison with the uniform bound is machine-checked (`JSP90.greedySum_le_uniform`), so
    `JSP90.erdos73On_of_greedyChain_uniform` re-derives `JSPProblem/Transversal.lean`'s `ℓ * k`
    instance, and `JSP90.greedySum_lt_uniform` / `JSP90.erdos73On_of_greedyChain_strict` record when
    the new constant is *strictly* better (`JSP90.girthSum_lt_mul_of_short_first`).
* `JSPProblem.Budget` — **the PACKING-BUDGET axis** (round 103, one new attack family).  Round 102's
  greedy chain was only used to make the *last* level bipartite; this file proves the **quantitative**
  statement that an induction along the chain consumes, in two forms, and derives a new instance of
  the headline theorem from it:
  - **`JSP90.oddCycleFamily_union_chainBelow` — the exchange lemma**: a packing `P` of the residue at
    level `j`, adjoined with the `j` greedy cycles of the earlier levels, is a packing of odd cycles
    of `G` of size `P.card + j` (`JSP90.chainBelow`, `JSP90.greedyCycle_subset_unionUpTo`,
    `JSP90.disjoint_unionUpTo_of_isOddCycle_level`, `JSP90.not_mem_chainBelow_of_isOddCycleFamily`,
    `JSP90.biUnion_chainBelow`);
  - **THE PACKING BUDGET `JSP90.level_oddCyclePackingLe`**: `LocIndep k G → j ≤ k →
    OddCyclePackingLe (k - j) (level G j)`, with `JSP90.level_packing_add_le` (`P.card + j ≤ k`),
    `JSP90.level_oddCyclePackingLe_one` (the classical residue step) and
    `JSP90.level_isBipartite_of_budget`;
  - **THE DEFICIENCY BUDGET `JSP90.level_locIndep`**: `LocIndep k G → LocIndep (k - j) (level G j)`
    (via `JSP90.level_maxDef_add_le`, round 87's descent read along the chain), the hypothesis-free
    form `JSP90.level_locIndep_of_firstBipartite`, and `JSP90.level_locIndep_one`;
  - **`JSP90.closeToBipartite_of_greedyChain_cost` / `JSP90.stepCost`** — the ladder with a
    **per-level residue price**, strictly generalising round 102's step, and the new instance
    **`JSP90.erdos73On_of_greedyChain_cost`**: `LocIndep k G` plus "each greedy residue is `c i`-close
    to bipartite" gives `CloseToBipartite (∑ j < k, girthOf (level G j) + c (j + 1)) G`, with the
    unit-cost corollary `JSP90.closeToBipartite_of_greedyChain_cost_one` (strictly cheaper than round
    102's constant by exactly `k`, `JSP90.girthSum_lt_of_unit`).
 * `JSPProblem.Cluster` — **the CLUSTER-GRAPH axis** (round 104, one new attack family).  The
   largest class on which Erdős's hypothesis and its conclusion coincide: `G` a disjoint union of
   complete graphs.
   - **THE CLASS `JSP90.ClusterDecomposition`**: the pieces of `𝒬` are pairwise disjoint, pairwise
     anticomplete and cover `V` (`AnticoverCoverFamily`, so every cycle of `G` lies in one piece),
     each piece has at least two vertices, and each piece is a clique;
   - **THE COUNT `JSP90.maxDef_cluster`**: `MaxDef G = ∑ C ∈ 𝒬, (|C| - 2)`, from
     `JSP90.indepCard_cluster` (the independence number of `G[X]` is *exactly* the number of pieces
     `X` meets, `JSP90.piecesMet`, `JSP90.exists_indep_onePerPiece`), `JSP90.card_biUnion_eq_sum`
     and `JSP90.sum_card_eq_sum_cost`;
   - **THE TRANSVERSAL `JSP90.exists_oddCycle_transversal`**: `JSP90.bigPieces` (the pieces with at
     least three vertices), two vertices deleted and two points chosen per big piece, which gives
     `JSP90.closeToBipartite_iff_maxDef_cluster`: `CloseToBipartite m G ↔ MaxDef G ≤ m` — on this
     class the hypothesis and the conclusion of Erdős #73 are the same statement;
   - **THE NEW INSTANCE `JSP90.erdos73On_of_cluster`**: `ClusterDecomposition G 𝒬 → LocIndep k G →
     CloseToBipartite k G`, constant `k`, with no odd girth, no packing weight, no degree bound and
     no bound on the number of pieces (plus `JSP90.erdos73On_of_cluster_univ`,
     `JSP90.cluster_isBipartite_iff`, `JSP90.maxDef_cluster_univ` = round 54's `MaxDef (K_n) = n - 2`,
     `JSP90.erdos73On_cluster_zero`);
   - `JSPProblem.ClusterSharp` — **the sharpness certificate for that instance**: the lower-bound
     witness `kTriangles k` *is* a cluster graph (`JSP90.cluster_kTriangles`), so
     `JSP90.maxDef_kTriangles_eq : MaxDef (kTriangles k) = k` and
     `JSP90.erdos73On_of_cluster_optimal : (LocIndep k (kTriangles k) → CloseToBipartite m
     (kTriangles k)) ↔ k ≤ m` — the new instance is an **equivalence with the optimal constant**, and
     `JSP90.erdos73_cluster_notBelowK` shows no `m < k` works.  This file declares **no** `DecidableEq`
     instance (the round-103 toolchain note: a file with a local instance cannot state anything over
     `Fin 3 × Fin k` that mentions an intersection).
 * `JSPProblem.Multi` (round 106) — the **complete multipartite axis**: `multi t n` is the complete
  multipartite graph with `t` parts of `n` vertices on `Fin t × Fin n`;
  - `JSP90.card_eq_sum_card_multiPart` / `JSP90.card_le_mul_indepCard_multi` — the counting lemmas:
    a vertex set splits over the parts (`|X| = ∑ i, |X ∩ P_i|`) and has size at most `t * α(G[X])`;
  - `JSP90.indepCard_le_multi` — `α(G[X]) ≤ n`, because an independent set lies in one part;
  - **`JSP90.maxDef_multi`** — `MaxDef (multi t n) = (t - 2) * n`, the *exact value of Erdős's
    hypothesis* on the complete multipartite graphs, with `JSP90.locIndep_multi_iff`;
  - `JSP90.not_isBipartite_of_tri`, `JSP90.isBipartite_multi_of_le_two`,
    `JSP90.isBipartite_multi_of_cover` and **`JSP90.isBipartite_deleteFinset_multi_iff`** — the
    *exact value of the conclusion's side*: `G − X` is bipartite iff the vertices it keeps lie in at
    most two parts (the counting steps being `JSP90.liveParts_le_two_of_isBipartite`,
    `JSP90.card_deadParts_add_liveParts`);
  - **`JSP90.closeToBipartite_iff_multi`** — `CloseToBipartite m (multi t n) ↔ (t - 2) * n ≤ m`,
    the exact value of the conclusion of Erdős #73 on this class;
  - **`JSP90.erdos73On_of_multi`** — *a new instance of the headline theorem with the optimal
    constant `f(k) = k`*, with `JSP90.erdos73On_of_multi_univ`,
    `JSP90.erdos73On_of_multi_optimal` and `JSP90.not_closeToBipartite_multi` for its optimality.
    This class is **connected** for `t ≥ 2`, so none of the anticomplete-decomposition instances of
    rounds 42–48 and 104–105 applies to it;
* `JSPProblem.Exact` — **the EXACT-ADDITIVITY axis** (round 105, one new attack family).  It proves
   the statement that `JSPProblem/Deficiency.lean` records as *missing* — the **equality**
   `MaxDef G = MaxDef (G[A]) + MaxDef (G[B])` over an anticomplete decomposition of the vertices —
   and pushes the same statement through the conclusion, so that *both* sides of Erdős #73 split
   exactly over an anticomplete cover.
   - **THE MISSING EQUALITY `JSP90.maxDef_anticover_add`** (from
     `JSP90.maxDefIn_anticoverIn_add`, with `AnticoverIn G s A B`: `maxDefIn G s = maxDefIn G (s ∩ A)
     + maxDefIn G (s ∩ B)`).  The truncated subtraction `defOf G X = |X| − 2 α(G[X])` is only
     *sub*additive over such a split (the file header of `JSPProblem/Deficiency.lean` gives the
     counterexample `K_3 ⊔ K_1`); the obstruction disappears for the *maximum* because each side
     carries a vertex set attaining its own maximum (`JSP90.exists_eq_maxDefIn`), and a side with
     positive deficiency satisfies `|X| ≥ 2 α(G[X])`, so the two sides pay separately and nothing
     truncates.  Note that `defOf` is **not** monotone under vertex sets (the file header gives the
     machine-checked obstruction), so attainment — not monotonicity — is the mechanism;
   - **THE LINEAR SPLIT ON AN `AnticoverIn`** `JSP90.card_indepCard_anticoverIn_add`: the vertices
     *and* the independent numbers of `Y` split over an anticomplete split of a vertex set `s`,
     `|Y| = |Y ∩ A| + |Y ∩ B|` and `α(G[Y]) = α(G[Y ∩ A]) + α(G[Y ∩ B])`; the `Anticover` version of
     `JSPProblem/Deficiency.lean` is recovered as `JSP90.card_indepCard_anticover_add_of_anticover`;
   - **THE FINITARY FORM `JSP90.maxDef_eq_sum_of_cover`**: `MaxDef G = ∑ X ∈ 𝒬, MaxDef (G[X])` for
     *any* pairwise anticomplete cover of the vertices (induction on the family, one piece peeled off
     at a time), together with `JSP90.locIndep_cover_iff` (the hypothesis splits) and
     `JSP90.maxDef_eq_sum_cost_of_cover` — **round 104's `maxDef_cluster` is now a corollary** of
     `JSP90.maxDef_clique` (`MaxDef (G[C]) = |C| − 2` for a clique `C` of at least two vertices);
   - **THE CONCLUSION SPLITS EXACTLY TOO**: `JSP90.closeToBipartite_of_cover_cost` (the per-piece
     costs add up) and `JSP90.closeToBipartite_iff_cost_cover` — `CloseToBipartite m G ↔ ∃ c,
     (∀ X ∈ 𝒬, CloseToBipartite (c X) (G[X])) ∧ ∑ c X ≤ m` — the *exact* additive form of the
     conclusion, with `JSP90.card_sum_inter_le` for the cardinality;
   - **THE NEW INSTANCE `JSP90.erdos73On_of_pieceMaxDef`** (+ `_univ`): `LocIndep k G →
     CloseToBipartite k G` on `JSP90.PieceMaxDef G 𝒬`, the class of graphs admitting an anticomplete
     cover whose pieces are MaxDef-close to bipartite — **the cover closure of the class on which the
     hypothesis and the conclusion of Erdős #73 coincide**, which contains round 104's cluster class
     (`JSP90.pieceMaxDef_of_cluster`, strictly: `K_5 ⊔ K_{2,3}` is on it and is not a cluster graph)
     and every disjoint union of graphs of any such class.  With
     `JSP90.closeToBipartite_iff_maxDef_of_pieceMaxDef` (hypothesis = conclusion on the class) and
     **`JSP90.erdos73On_of_pieceMaxDef_optimal`** — `(LocIndep k (kTriangles k) → CloseToBipartite m
     (kTriangles k)) ↔ k ≤ m`, so the constant `k` is machine-checked optimal and the lower bound
     `f(k) ≥ k` is re-derived (`JSP90.erdos73_pieceMaxDef_notBelowK`).


/-!
## `JSPProblem/Split.lean` (round 107) — the SPLIT-GRAPH axis

`JSP90.SplitPartition G A B` (`V = A ⊔ B`, `A` independent, `B` a clique) is the class on which both
sides of Erdős #73 have an exact value, and it is the first class whose optimal constant is
*strictly larger* than `k` while the odd cycles are still described by one local rule ("a triangle is
a clique edge plus a common neighbour on the independent side"):

* `JSP90.cardB_le_locIndep_add_two` — `LocIndep k G → |B| ≤ k + 2` (the hypothesis, used once);
* `JSP90.maxDef_split_le` — `MaxDef G ≤ |B| − 1`;
* `JSP90.IsolatedPair G A B` — a pair of clique vertices with **no** common neighbour in `A`;
* `JSP90.closeToBipartite_split_iff` — **the exact value of the conclusion**: `τ(G) = |B| − 1`, or
  `|B| − 2` when an isolated pair exists (`closeToBipartite_split_cardB_sub_two_iff`);
* **`JSP90.erdos73On_of_splitPartition` — a new instance of the headline theorem, constant `k + 1`**,
  plus the sharper `closeToBipartite_of_splitPartition_of_isolatedPair` (constant `k`);
* ~~`JSPProblem/Split.lean`'s Part 4 records the witness `K_{k+2,k+2}` minus a perfect matching, on
  which the constant `k + 1` is attained.~~  **This was wrong** (the graph named there is bipartite,
  so it is not a split graph) and was corrected in round 108; see `JSPProblem/SplitSharp.lean`.

One intermediate claim was refuted by Lean while writing the file (`α(G[X]) ≥ 1 + |X ∩ A|`): a split
graph may have edges *between* the two sides, so the deficiency bound uses only `α ≥ |X ∩ A|` and
`α ≥ 1`.  The refutation is recorded in the file.
-/

## `JSPProblem/SplitSharp.lean` (round 108) — the witness of the split-graph axis, and `f(k) ≥ k + 1`

`JSP90.splitWitness n` on `Fin n × Bool`: the **independent** side `A = {(i, false)}`, the **clique**
side `B = {(i, true)}`, and `p ~ q ↔ p.1 ≠ q.1 ∧ ¬ (p.2 = false ∧ q.2 = false)` — i.e. the cross edge
`a_i ~ b_j` is present exactly when `i ≠ j`.  This is the graph round 107 named (incorrectly), and it
is the **first witness in this development on which the hypothesis and the conclusion do not
coincide**: Erdős's hypothesis allows `k` and the conclusion needs `k + 1`.

* `JSP90.splitWitness_splitPartition` — it *is* a split graph, `n` vertices on each side;
* `JSP90.not_isolatedPair_splitWitness` — every pair of `B` has a common neighbour in `A` (`3 ≤ n`),
  so the `|B| − 2` regime of round 107 is unavailable;
* **`JSP90.locIndep_splitWitness` — `LocIndep k (splitWitness (k + 2))`** for every `k`, with the
  counting identity `|X ∩ A| + |X ∩ B| = |I ∩ J| + |I ∪ J|` for the index sets
  `I = (X ∩ A).image fst`, `J = (X ∩ B).image fst` as its only input;
* **`JSP90.maxDef_splitWitness` — `MaxDef (splitWitness (k + 2)) = k`**, the exact value of the
  hypothesis (via `JSP90.indepCard_two`, `α(B ∪ {a_i, a_j}) = 2`), so the witness is tight for
  `LocIndep` just as `kTriangles k` is;
* **`JSP90.closeToBipartite_iff_splitWitness` — `CloseToBipartite m (splitWitness (k + 2)) ↔
  k + 1 ≤ m`** for `k ≥ 1`: the exact value of the conclusion;
* **`JSP90.not_erdos73On_splitWitness` — `¬ Erdős73On k k` for every `k ≥ 1`, i.e. the constant
  `f(k)` of Erdős #73 satisfies `f(k) ≥ k + 1`.**  This is the first machine-checked lower bound on
  that constant that is *strictly larger* than the `f(k) ≥ k` of rounds 39/104, and it is a statement
  about the answer to the problem, not only about a class;
* `JSP90.erdos73On_of_splitPartition_optimal` — the constant `k + 1` of round 107's split-graph
  instance is **optimal**.

Round 107's Part 4 text (the `K_{k+2,k+2}` minus a perfect matching) has been corrected in place: it
was bipartite, so it was never a split graph, and the independent set it proposed was not
independent.  `jsp_000090_main` is still not declared — the *upper* bound on `f(k)`, i.e. Erdős #73
itself, is unchanged.

## `JSPProblem/Chain.lean` (round 109) — the DECREASE at a hard 1-cut, and the block-cut bound

The **fiftieth** attack family, and the first one to work on the *quantitative* content of the
classical descent along the 1-cut axis of `JSPProblem/Connect.lean` (round 48).  What that axis had
was a *count* of the charged parts (`OneSplit.card_nonBipartiteParts_le`) and an instance with the
constant `1 + m * r`; what it lacked is **how much the packing bound drops** at a 1-cut.

* **`JSP90.OneSplit.packing_part_le`** — **THE DECREASING LEMMA.**  Under a packing bound `r`, a
  non-bipartite part `T_i` of a 1-cut whose `s` non-bipartite parts are all non-bipartite satisfies
  `packing number of G[T_i] ≤ r + 1 - s`: a packing inside the part, together with one odd cycle in
  each of the *other* non-bipartite parts, is a packing of `G` (the parts are pairwise disjoint), so
  `|𝒞| + (s − 1) ≤ r`.  For `s = 2` the bound **strictly** decreases
  (`JSP90.OneSplit.packing_part_le_lt`).  The input is
  `JSP90.OneSplit.oddCycle_family_erase`: one odd cycle in each of the other non-bipartite parts,
  pairwise disjoint, and as many as there are parts;
* **`JSP90.OneSplit.packing_part_no_decrease_of_oneSide`** — at a *one-sided* 1-cut (`s = 1`) the
  bound is inherited unchanged: the descent genuinely stalls there.  This is the machine-checked
  form of round 48's negative result number 1;
* **`JSP90.closeToBipartite_of_1split_of_decreasing`** — **a new instance of the headline theorem**
  along the 1-cut axis whose hypothesis on the parts is needed only at the **decreased** bound
  `r + 1 − s`, constant `1 + s * m`, independent of the number of parts, with no bound on the odd
  girth, packing weight or number of branch vertices;
* **`JSP90.HardCert`**, **`JSP90.exists_packing_of_hardCert`**, **`JSP90.hardCert_isBipartite_of_packing_le`**
  — **the block-cut bound, proved for the hard chains**: a chain of `d` successive 1-cuts *each of
  which separates two non-bipartite sides* gives `d` pairwise disjoint odd cycles, so a packing bound
  `r` forbids a hard chain of `r + 1` cuts.  This is round 48's named missing lemma
  `oneDepth_le_of_packing` **in the form in which it is true**, and it is the form the recursion of
  `JSP90.oddCycleErdosPosa_of_noOneCut_of_bounded_oneDepth` needs;
* **`JSP90.locIndep_param_cannot_be_lowered`** — **a machine-checked negative result found while
  writing this file**: the classical descent cannot be stated in Erdős's own parameter, because
  `LocIndep` is monotone *increasing* in `k`; the witness is `LocIndep 1 (K_3)` together with
  `¬ LocIndep 0 (K_3)` (`LocIndep 0` ⟺ bipartite).  Every statement of the file is therefore in the
  packing language, which is also the language in which the research statement
  `JSP90.OddCycleErdosPosa r` lives.

What remains: **the one-sided chains** (cut vertices with a single non-bipartite side).  They cannot
be bounded by the packing number — a triangle with a pendant path has packing number `1` and
arbitrarily long such chains — and are handled in the classical proof by the block-cut tree and the
short-C-path lemma.  `jsp_000090_main` is still not declared and `JSP90.OddCycleErdosPosa r` is
unchanged.
## `JSPProblem/CPath.lean` (round 111) — the **C-PATH** (Mader's object) and the TWO-ATTACHMENT transversal

The **fifty-second** attack family, and the one `discovery/JSP-000090/policy.json` named as the next
single step: formalise the **C-path** — a path from a vertex of the odd cycle `C` to a vertex
`x ∉ C` whose other vertices all avoid `C`.

* **`JSP90.IsCPath`** — the object itself, with its API (`IsCPath.card`, `IsCPath.adj_step`,
  `IsCPath.notMem_interior`): a `C`-path of length `d` has `d + 1` vertices, `d` edges, and **no
  vertex other than the first one lies on `C`**;
* **`JSP90.IsCPath.extend`** — a `C`-path may be **extended by one edge**, the classical step from
  length `d` to length `d + 1`;
* **`JSP90.IsOddCycle.exists_edge_avoiding`** — a cycle of length `≥ 3` has an edge avoiding any
  prescribed vertex of it;
* **`JSP90.closeToBipartite_of_twoAttach`** — **THE TWO-ATTACHMENT TRANSVERSAL**: if every odd cycle
  of `G` meets one odd cycle `C` in at least two vertices, then `G` is `(|C| - 1)`-close to
  bipartite, and
* **`JSP90.erdos73On_of_twoAttach`** — **a new instance of the headline theorem**, with the constant
  `|C| - 1`, **independent of `k`** (the first transversal bound in this development that does not
  grow with Erdős's local parameter, against `ℓ * k` of
  `JSP90.erdos73On_of_bounded_odd_girth`).

Still open: `policy.json`'s second half — *the shortest `C`-path is induced* — needs
`IsCPath.skip`, `IsCPath.Shortest`, `IsCPath.induced_of_shortest`, `IsCPath.ne_iff_last` and
`IsCPath.isOddCycle_return`; the index arithmetic of the first two (`skipPath`, `skip_idx_lt`,
`skip_idx_inj`) is written out in the file and the three lemmas are named as the next concrete step in
`discovery/JSP-000090/policy.json`.  `JSP90.OddCycleErdosPosa r` and `jsp_000090_main` are unchanged.
## `JSPProblem/CPathSkip.lean` (round 112) — the C-PATH SHORTCUT, the SHORTEST `C`-PATH IS INDUCED, the CLOSED `C`-PATH IS AN ODD CYCLE, and the TWO-ATTACHMENT COVER

Round 111 left four named lemmas and the file closed the whole set.

* **A CHORD OF A `C`-PATH SHORTENS IT.**  `JSP90.skipPath` is the splice `p 0 … p a`, chord
  `p a ~ p b`, `p b … p d`; `JSP90.IsCPath.skip` builds from it a `C`-path **to the same target** of
  length `a + 1 + (d - b)`, and `JSP90.IsCPath.skip_shorter` records that this is `< d`
  (`JSP90.skip_len_lt`);
* **`JSP90.IsCPath.Shortest`** — minimality, necessarily a *hypothesis*: `Nat.find` would need a
  `DecidablePred` and the predicate quantifies over a *function* `Fin (d' + 1) → V`;
* **`JSP90.IsCPath.induced_of_shortest` — THE SHORTEST `C`-PATH IS INDUCED** (the exact lemma named by
  `discovery/JSP-000090/policy.json` after round 111): for `u ≠ v`, `u + 1 ≠ v`, `v + 1 ≠ u` one has
  `¬ G.Adj (p u) (p v)`;
* **`JSP90.IsCPath.adj_target_of_shortest`** — Mader's neighbour count at the far end (`x` sees only
  `p (d-1)` and `p d`), and **`JSP90.IsCPath.adj_iff_step_of_shortest`** — the *full* neighbour count:
  a vertex of a shortest `C`-path is adjacent to no other vertex of it except its own two
  path-neighbours;
* **`JSP90.IsCPath.isOddCycle_return` — A CLOSED `C`-PATH OF EVEN LENGTH IS AN ODD CYCLE OF `G`**, and
  `JSP90.oneAttach_of_isCPath_return` records that this odd cycle meets `C` in **exactly one vertex**
  and contains the target: *Mader's one-attachment lemma in `C`-path form*, the first odd cycle
  attached to `C` at a single point that this development constructs;
* **`JSP90.TwoAttachCover` / `JSP90.closeToBipartite_of_twoAttachCover` — THE TWO-ATTACHMENT COVER**:
  a family `𝒞` of vertex sets (the members need **not** be odd cycles, and there is **no bound** on
  their number) such that every odd cycle of `G` meets some member in at least two vertices gives
  `CloseToBipartite (∑ X ∈ 𝒞, |X| - 1) G`.  This is a **strict generalisation** of round 111's
  `closeToBipartite_of_twoAttach`, which is the singleton case
  (`JSP90.closeToBipartite_of_twoAttachCover_of_singleton`,
  `JSP90.sum_card_sub_one_singleton`).  The certificate and its cost are
  `JSP90.hitsOddCycles_of_twoAttachCover` and
  `JSP90.card_biUnion_erase_le_sum_card_sub_one_of_twoAttachCover`; the counting input is
  `JSP90.exists_mem_inter_erase_of_card_ge_two` (an odd cycle meeting `X` in two vertices also meets
  `X` minus any one of them);
* **NEW INSTANCES OF THE HEADLINE THEOREM**, constants independent of `k`:
  **`JSP90.erdos73On_of_twoAttachCover`** (cost `∑ X ∈ 𝒞, |X| - 1`) and
  **`JSP90.erdos73On_of_twoAttachCover_bounded`** (cost `ℓ * |𝒞|` when every member has at most `ℓ`
  vertices — the Erdős–Pósa shape, one unit per cover member).

Still open: the one-attachment lemma gives an odd cycle attached to `C` **once**, but no transversal
— the *two-attachment cover* hypothesis is what pays, and the classical existence of such a cover for
a 3-connected graph is the unresolved part.  `JSP90.OddCycleErdosPosa r` and `jsp_000090_main` are
unchanged.

## `JSPProblem/CPathPair.lean` (round 114) — the FAN at DEPTH TWO: MADER'S TWO-ATTACHMENT LEMMA

Round 112 named the missing depth-two step, and this file delivers it.  No Menger theorem is used;
the two arcs between the attachment points are counted, and the parity decides which one closes up
into an odd cycle.

* **`JSP90.IsCPathPair`** — **THE OBJECT: THE FAN AT DEPTH TWO.**  Two `C`-paths `p`, `q` to a
  common target `x ∉ C`, ending at **distinct** vertices `f i`, `f j` of `C`, whose vertex sets meet
  only in `{f i, f j, x}`: the classical "two internally vertex-disjoint `C`-paths" formulation of
  a fan.  `JSP90.IsCPathPair.d1_pos` / `d2_pos` (a length-0 `C`-path would put its target on `C`),
  `JSP90.IsCPathPair.eq_fi_of_mem_supset_p_mem_C` (the first path meets `C` in exactly its first
  vertex) and **`JSP90.IsCPathPair.inter_ne`** (the two interiors never meet) complete its API;
* **`JSP90.arcPairFun`** — **THE TWO-PATH ARC CYCLE**, the closed walk
  `f j → arc of length `e` → f i → p → x → q → f j` carried by `Fin (e + d1 + d2) → V`.  For
  `d1 = d2 = 1` this is `JSPProblem/Fan.lean`'s `arcFun`, so the constructor **generalises** it to
  two paths of arbitrary length.  `JSP90.arcPairFun_inj` (the walk is **simple**), and
  `JSP90.arcPairFun_adj` (every step is an edge, including the closing step `q 1 ~ q 0 = f j`);
* **`JSP90.arcPair_isOddCycle`** — the two-path arc cycle is an **odd cycle** of `G` when
  `e + d1 + d2` is odd, and `JSP90.card_arcPair` gives its **exact** number of vertices;
* **`JSP90.exists_oddCycle_twoAttach_of_isCPathPair` — MADER'S TWO-ATTACHMENT LEMMA.**  If `x` has
  two internally vertex-disjoint `C`-paths to two distinct vertices `f i`, `f j` of an odd cycle
  `C`, then **`x` lies on an odd cycle of `G` through both `f i` and `f j`**.  This is the *second*
  attachment point, the resource `discovery/JSP-000090/policy.json` asked for after rounds 111–112
  (which produced only one-attachment odd cycles), and the first odd cycle of `G` this development
  builds through a vertex at `C`-distance `≥ 2`.  The parity is pure counting
  (`JSP90.mod_two_of_sum_odd`): the two candidate totals add up to `m + 2 (d1 + d2)`, which is odd;
* **`JSP90.arc_sum_ge_of_shortest` — A SHORTEST ODD CYCLE IS THICK**: at a shortest odd cycle of
  length `m`, `m ≤ e + d1 + d2` for the odd arc.  In the fan case this forces
  **`JSP90.oddArc_eq_two_of_fan_of_shortest`: the odd arc has length exactly `m - 2`**, and hence
  **`JSP90.shortArc_of_pairFan`** — the short-arc lemma of `JSPProblem/Fan.lean`, re-derived here
  from the two-path arc cycle and its vertex count (an independent route, and a check on the new
  machinery).  The depth-one input is now *derived*, not assumed:
  `JSP90.IsCPath_edgePath` (a length-1 `C`-path is an edge) and `JSP90.isCPathPair_of_adj` (a vertex
  adjacent to two distinct vertices of `C` **is** a fan);
* **`JSP90.twoAttach_kTriangles_one`** — the two-attachment hypothesis *holds* on `kTriangles 1`:
  `CloseToBipartite 2 (kTriangles 1)`, so round 111's transversal is not vacuous;
* **`JSP90.not_twoAttach_kTriangles_two` — MACHINE-CHECKED NEGATIVE RESULT**: on
  `kTriangles 2` **no** odd cycle is two-attached, i.e. the hypothesis of
  `JSP90.closeToBipartite_of_twoAttach` is not automatic and needs real content.

Still open: Mader's lemma produces an odd cycle through `x` meeting `C` twice, but it does not make
the two-attachment *hypothesis* hold for every odd cycle of `G`, so no transversal follows from it
alone.  The two-attachment **cover** of round 112 still needs its global existence statement, and the
one-attachment odd cycles of `JSP90.oneAttach_of_isCPath_return` still need to be absorbed by a
2-cut.  `JSP90.OddCycleErdosPosa r` and `jsp_000090_main` are unchanged.

## `JSPProblem/TwoAttach.lean` (round 115) — the **cover statement itself**, in machine-checked form,
   and the **exact cost of a cover**

The **fifty-fifth** attack family, and the one `discovery/JSP-000090/policy.json` named as the next
single step: *state the cover statement*.  `JSPProblem/CPathSkip.lean` (round 112) had the
two-attachment cover as a **hypothesis**; this file isolates what it costs, what it buys, and what
is still missing — and it settles the two design questions about the cover route.

* **`JSP90.exists_oneSidedDeletion`** — **A FAMILY OF NONEMPTY SETS HAS A ONE-SIDED DELETION SET**:
  for a finite family `𝒞` of nonempty sets there is `U` with `|U| ≤ ∑ X ∈ 𝒞, (|X| - 1)` and
  `|X \ U| ≤ 1` for every `X ∈ 𝒞`.  **No graph occurs in this statement** — the induction spares one
  vertex per member;
* **`JSP90.TwoAttachCover'`** and **`JSP90.closeToBipartite_of_twoAttachCover'`** — the
  two-attachment cover **without the choice function** of round 112 (`TwoAttachCover G 𝒞 pick`), for
  which the pick is unnecessary and ill-defined when `V` is empty; the transversal is the deletion set
  of the lemma above (`JSP90.hitsOddCycles_of_twoAttachCover'`), of cost `∑ X ∈ 𝒞, |X| - 1`;
* **`JSP90.closeToBipartite_of_twoAttachCover'_bounded`** — `ℓ` vertices per member and `q` members
  give `CloseToBipartite (ℓ * q) G`: **the Erdős–Pósa shape**, one unit per member of an `r`-sized
  object.  With **`JSP90.erdos73On_of_twoAttachCover'`** this is another instance of the headline
  theorem, with a constant independent of `k`;
* **`JSP90.TwoAttachCoverExists r ℓ q`** — **THE MACHINE-CHECKED GLOBAL TARGET**, a `def` (nothing
  assumed, no placeholder): every graph whose odd cycle packings all have at most `r` members carries a
  two-attachment cover with at most `q` members of at most `ℓ` vertices.  Then
  **`JSP90.oddCycleErdosPosa_of_twoAttachCoverExists`** (constant `ℓ * q`) and
  **`JSP90.erdos73_of_twoAttachCoverExists`**: `∀ ℓ q, ∀ r, TwoAttachCoverExists r ℓ q` implies
  `∀ k, Erdős73 k`, i.e. `jsp_000090_main`.  **The residual difficulty of JSP-000090 is now one
  statement of combinatorial existence kind**;
* **`JSP90.TwoAttachPacking`, `JSP90.twoAttachPacking_triangles`, `JSP90.sum_card_sub_one_tri`,
  `JSP90.packing_cover_cost_two_of_kTriangles`** — a cover whose members are **odd cycles** (a
  two-attachment *packing*) exists on the sharp witness, but costs exactly **`2 * k`** there, while
  `k` suffices: the members of a cover must be allowed to be **non-cycles**;
* **`JSP90.triPairCover`, `JSP90.twoAttachCover'_triPairs`, `JSP90.cover_cost_ge_of_kTriangles`,
  `JSP90.cover_cost_min_kTriangles`, `JSP90.cover_cost_kTriangles_is_optimal`** — the two-vertex cover
  `{0, 1} × {i}` of `kTriangles k` costs **exactly `k`**, and **no cover of `kTriangles k` costs less
  than `k`**: the minimum cover cost is the odd cycle transversal number, so the cover *method* is
  optimal in constant on the family that makes Erdős #73 hard.  Only the *existence* of a small cover
  is open.

### Round 117 — `JSPProblem/Petals.lean`: the multi-petal windmill refutes the two-attachment target

What remains: `TwoAttachCoverExists` itself.  Together with the round-114 obstruction — the
one-attachment odd cycles of `JSP90.oneAttach_of_isCPath_return` must be absorbed by a 2-cut before a
cover can be built, and that absorption is bounded by nothing here — the two missing statements are
now *both* about the construction of `𝒞`.  `JSP90.OddCycleErdosPosa r` and `jsp_000090_main` are
unchanged.

### Round 118 — `JSPProblem/CriticalSharp.lean`: the SPREAD CONSTANT (round 53's route is closed)

* **`JSP90.card_le_sub_two_of_hitsOddCycles_completeGraph`, `JSP90.minimalTransversal_card_completeGraph`,
  `JSP90.card_criticalTransversal_completeGraph`** — a set of `K_n` meets every odd cycle only if
  `n ≤ |X| + 2`, and **any set carrying critical data has exactly `n - 2` vertices** (a critical cycle
  of `x ∈ X` has three vertices inside `{x} ∪ (V \ X)`);
* **`JSP90.criticalCycle_eq_completeGraph`, `JSP90.mem_compl_of_criticalCycle`,
  `JSP90.adj_IntGraph_completeGraph`** — every critical cycle of a transversal of `K_n` is exactly the
  triangle `{x} ∪ (V \ X)`, so **the critical intersection graph of `K_n` is the complete graph on
  its transversal**;
* **`JSP90.spreadTransversal_completeGraph_iff` — THE SPREAD CONSTANT OF A COMPLETE GRAPH, EXACTLY:
  `SpreadTransversal c (completeGraph (Fin n)) ↔ (n - 2 ≤ c ∧ 0 < c)`** — so `K_4` needs exactly two
  colours, `K_5` exactly three, and the minimum spread constant of the family `K_n` is unbounded;
* **`JSP90.not_spread_transversal_two_completeGraph_five`** — round 53's remark that "`c = 2` is the
  classical shape of Reed–Robertson–Seymour–Thomas" is refuted by a complete graph;
* **`JSP90.spreadMinimalTransversal_c_ge`, `JSP90.not_spreadMinimalTransversal_of_packing`,
  `JSP90.no_fixed_spreadConstant`** — **NO FIXED COLOUR COUNT WORKS**: a graph of odd cycle packing
  number `r` needs at least `3 * r - 2` colours (witness `K_{3r}`, whose packing bound `⌊n / 3⌋` is
  `JSP90.packing_card_le_completeGraph`), so the class-level hypothesis of
  `JSP90.erdos73_of_spreadMinimalTransversal` — a *fixed* `c` for all `r` — is **false**;
* **`JSP90.spreadConstant_exact_completeGraph`** — the lower bound `3 * r - 2` is **sharp**: `K_{3r}`
  has odd cycle packing number at most `r` and its minimum spread constant is exactly `3 * r - 2`;
* **`JSP90.exact_spread_constant_locIndep`, `JSP90.spread_constant_ge_of_locIndep`** — and the route is
  in any case **quadratic**: `K_{k + 2}` satisfies `LocIndep k` and has spread constant exactly `k`,
  while round 53's counting lemma gives `|X| ≤ c * k`; every instance obtained that way therefore
  carries a constant of at least `k * (k + 2)`, whereas Erdős–Pósa for odd cycles has the constant
  `O(k log k)`.

What remains: `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) and
`jsp_000090_main` are unchanged; what round 118 removes is one *route* to them, not the theorem.

## `JSPProblem/FewOdd.lean` (round 126) — the FEW-ODD-CYCLES axis

* **`JSP90.exists_transversal_card_le`** — the **pairing lemma**: a pairwise-meeting family of nonempty
  sets has a transversal of `⌈|𝒞| / 2⌉` vertices (strong induction on `|𝒞|`; the step pays one vertex
  for a *pair* of members);
* **`JSP90.closeToBipartite_of_locIndep_one_of_card_oddCycles_le`**, **`JSP90.erdos73On_fewOddCycles`**
  — **a new instance of the headline theorem**: `LocIndep 1 G` together with `|OddCycles G| ≤ 2 m`
  gives `CloseToBipartite m G`.  Erdős's hypothesis enters only through the fact that two odd cycles
  of a `LocIndep 1` graph meet;
* **`JSP90.k4sub`** — `K₄` with four of its six edges subdivided: eight vertices, ten edges, **no
  triangle**, `MaxDef = 1` exactly, **four** 5-cycles which pairwise meet and have empty total
  intersection, and `JSP90.closeToBipartite_iff_k4sub : CloseToBipartite m k4sub ↔ 2 ≤ m`;
* **`JSP90.not_helly_k4sub`** and **`JSP90.three_commonVertex_of_k4sub`** — `LocIndep 1` does **not**
  imply `HellyOddCycles`, and the failure is invisible to every three-element version of the property.
  **The Helly route is therefore closed at `k = 1`** (rounds 83, 84, 87 and 124 used it).

What remains: `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) and `jsp_000090_main`, both
unchanged; what round 126 adds is one more instance and the removal of one route.

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
import JSPProblem.Cut
import JSPProblem.CutTriangle
import JSPProblem.Attach
import JSPProblem.Triangle
import JSPProblem.Free
import JSPProblem.Class
import JSPProblem.Book
import JSPProblem.Double
import JSPProblem.Touch
import JSPProblem.Petersen
import JSPProblem.Layer
import JSPProblem.Subcubic
import JSPProblem.Cover
import JSPProblem.Cactus
import JSPProblem.Sun
import JSPProblem.Ring
import JSPProblem.Helly
import JSPProblem.Descent
import JSPProblem.Witness
import JSPProblem.PackDescent
import JSPProblem.SplitOne
import JSPProblem.HalfOne
import JSPProblem.Windmill
import JSPProblem.CutVertex
import JSPProblem.MaxCut
import JSPProblem.Finite
import JSPProblem.DegColour
import JSPProblem.Sparse
import JSPProblem.Pivot
import JSPProblem.Stair
import JSPProblem.Greedy
import JSPProblem.Budget
import JSPProblem.Cluster
import JSPProblem.ClusterSharp
import JSPProblem.Exact
import JSPProblem.Multi
import JSPProblem.Split
import JSPProblem.SplitSharp
import JSPProblem.Chain
import JSPProblem.Piece
import JSPProblem.CPath
import JSPProblem.CPathSkip
import JSPProblem.CPathPair
import JSPProblem.TwoAttach
import JSPProblem.Petals
import JSPProblem.CriticalSharp
import JSPProblem.Petal
import JSPProblem.PetalFinite
import JSPProblem.PetalBound
import JSPProblem.Hub
import JSPProblem.HubSharp
import JSPProblem.Two
import JSPProblem.Wheel
import JSPProblem.Petal3
import JSPProblem.FewOdd
import JSPProblem.Mono
import JSPProblem.CutFlip
import JSPProblem.MonoWind
import JSPProblem.OneK
import JSPProblem.PetalOverlap
import JSPProblem.MeetSet
import JSPProblem.Nonagon
import JSPProblem.AttachErase
