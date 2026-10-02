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
