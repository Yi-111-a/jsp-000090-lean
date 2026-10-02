# JSP-000090

**If local subgraphs have large independent sets, must the whole graph be close to bipartite after
few modifications?**

* Catalog: `problems/catalog-0001-0100.md#JSP-000090` — area *graph theory*, proposed no later than
  1982, **status Solved**, **Lean proof: No**.
* Reference: `[Re99]` B. Reed, *Mangoes and Blueberries*, Combinatorica (1999), 267–296.
* Precise source statement: **Erdős Problem #73**, <https://www.erdosproblems.com/73> —
  for every `k ≥ 0` there is `f(k)` such that any graph in which every subgraph `H` has an
  independent set of size `≥ (|V(H)| − k)/2` is the union of a bipartite graph and `f(k)` vertices.

Formalization: `lean/JSPProblem/` — `Definitions.lean` (the statement, with
`CloseToBipartite m G` = *deleting at most `m` vertices leaves a bipartite graph*), `Reed.lean`
(structural API), `OddCycle.lean` (the odd-cycle characterisation of bipartiteness, a Mathlib
`TODO`, and **Erdős #73 for `k = 0`**: `JSP90.erdos73_zero : Erdős73 0`), `Packing.lean` (at
most `k` vertex-disjoint odd cycles), `Transversal.lean` (odd cycle transversals: the conclusion
↔ transversal bridge, **Erdős #73 for graphs of bounded odd girth** with the explicit constant
`f(k) = ℓ * k` in `JSP90.erdos73On_of_bounded_odd_girth`, and the reduction
`JSP90.erdos73_of_erdosPosa` of the whole theorem to the Erdős–Pósa theorem for odd cycles),
`Branch.lean` (graphs with few high-degree vertices: `f(k) = m + k`) and `Sharp.lean` (the lower bound `f(k) ≥ k`, witnessed by `K_3 ⊔ ... ⊔ K_3`, and the sharpness of the
previous instance), and `Residue.lean` (the **residue of a packed odd cycle** and the induction step
of the Erdős–Pósa proof: the packing number of `G - C` drops by one, every odd cycle of the residue
meets the rest of a maximum packing, the case of packing number one in full, and the minimum
transversal with its "private" odd cycles), and `Chord.lean` (**a shortest odd cycle is induced**:
the arc machinery of `Fan.lean` generalised to a closing vertex on the cycle, whence
`no_chord_of_shortest_oddCycle` and `induceFinset_adj_of_shortest` — the complete local structure of
`G` at a shortest odd cycle), and `Separator.lean` (the **2-cut decomposition**, the first piece of
*global* structure: a split `V = {a,b} ⊔ T₁ ⊔ … ⊔ T_t` with the parts pairwise anticomplete, so
`{a,b}` is a vertex cut; a cycle avoiding the cut lies in a single part — in exactly one piece — and
hence odd cycle transversals, and the conclusion of Erdős #73, are additive over a 2-cut:
`JSP90.erdos73On_of_split` gives `CloseToBipartite (m * t + 2)` on `G` from `CloseToBipartite m` on
the pieces, i.e. Erdős #73 is closed under 2-cut decomposition, so the theorem reduces to the
3-connected case; `JSP90.isBipartite_of_split` is the 2-cut parity lemma, and
`JSP90.erdos73On_of_split_of_bounded_branch` composes the split with the branch-vertex instance), and
`Count.lean` (the **counting half** of the same decomposition: a cycle meeting exactly one vertex of
the cut lies in a half-piece `T_i ∪ {a}` or `T_i ∪ {b}`, and at most `k` of the `t` parts of a split
are non-bipartite under `LocIndep k G`, so the new instance
`JSP90.erdos73On_of_split_of_bounded_pieces` gives `CloseToBipartite (2 + m * k)` on `G` — the
constant is free of the number of pieces — and `JSP90.packing_le_of_split_decomposition` is the full
packing decomposition `card ≤ 2 + t * r`, and the precise reduction
`JSP90.erdos73_of_noSplit2_of_bounded_splitDepth`: Erdős–Pósa for odd cycles follows from the
2-cut-free case together with a uniform bound on the number of 2-cuts of `G`)., and `Weight.lean` (the **weighted Erdős–Pósa theorem**: the residue
induction run to exhaustion, with the total length of a packing of odd cycles as the induction
parameter — `JSP90.closeToBipartite_of_weightLe` says that a uniform bound on the *packing weight*
bounds the odd cycle transversal, which is **strictly more general** than the bounded-odd-girth
instance; `JSP90.isBipartite_delete_of_maxWeightFamily` says the residue of a maximum-weight packing
is bipartite, and `JSP90.closeToBipartite_of_maxWeightPacking` bounds the transversal number by the
weight of a maximum-weight packing; `JSP90.erdos73On_of_bounded_packing_weight` is a **new
instance** of the headline theorem for graphs of bounded packing weight;
`JSP90.closeToBipartite_iff_completeGraph_add_two` gives the **exact** value of the conclusion on
complete graphs, `CloseToBipartite m (K_n) ↔ n ≤ m + 2`; and `JSP90.absorption_step_fails` is the
machine-checked **negative result** that the naive `+ 1` absorption step is false — for `G = K_5`
and the triangle `{0,1,2}` the residue is `K_2` (so the hypothesis `CloseToBipartite 0 (G − C)`
holds) while `K_5` is not `1`-close to bipartite, and `LocIndep 3 (K_5)` holds, so the failure is
inside the range of the theorem: the `+|C|` of the residue induction cannot be replaced by `+1`
without a hypothesis from the local structure at a shortest odd cycle of length `≥ 5`).

Prize gate: `jsp_000090_main` = the complete theorem for all `k`, still open — the one remaining
statement is `JSP90.OddCycleErdosPosa r` for all `r` (Erdős–Pósa for odd cycles); everything else
is proved.  Round 44 localised it further: the unconditional absorption step is **refuted**
(`JSP90.absorption_step_fails`), so the missing lemma is the *conditional* absorption step at a
shortest odd cycle of length `≥ 5`, together with a bound on the number of 2-cuts of `G` as a
function of the **odd girth** (round 43's reduction, whose hypothesis (ii) cannot be a function of
the packing number). See `ACCEPTANCE.md` and `discovery/JSP-000090/policy.json`.

**Round 76 (`lean/JSPProblem/Petersen.lean`) — the deficiency-one axis and the improved lower
bound `f(k) ≥ 2 k`.**  The witness `kTriangles k` of `Sharp.lean` gives the lower bound `f(k) ≥ k`.
A better witness is the **Petersen graph with one vertex deleted** (`p9`, nine vertices, twelve
edges, triangle-free): its maximum deficiency is exactly one (`JSP90.locIndep_one_p9`,
`JSP90.not_locIndep_zero_p9`) and its least odd cycle transversal is exactly two
(`JSP90.not_closeToBipartite_one_p9`, `JSP90.closeToBipartite_two_p9`).  The disjoint union of `k`
copies satisfies `LocIndep k` (`JSP90.locIndep_p9Family`) and has least odd cycle transversal exactly
`2 k` (`JSP90.closeToBipartite_p9Family_iff`), so

> **`JSP90.erdos73_lower_bound_two` / `JSP90.no_constant_below_two_k`: `f(k) ≥ 2 k`** — no constant
> below `2 k` works — which *strictly improves* `JSP90.erdos73_lower_bound` (`f(k) ≥ k`).

**Round 80 (`lean/JSPProblem/Cover.lean`) — the SHARED-EDGE axis: the odd-girth bound with no degree
bound, and the refutation of round 78's closing plan.**  Round 78 proved
`closeToBipartite_of_subcubic_of_shortOddCycles` under the *degree* hypothesis `MaxDegLe G 3`, and left
as its concrete next lemma "the **active edges** (the edges of a shortest odd cycle that lie in another
odd cycle) are covered by two vertices of that cycle".  That lemma is **false**, by machine check:
in `p9` (subcubic, odd girth `5`) all five cycle edges of the pentagon `Cb` are active
(`JSP90.each_activeCb_active`) and no two vertices cover them (`JSP90.not_two_cover_of_Cb`,
`JSP90.no_two_cover_activeCb`), so the vertex-cover number is three
(`JSP90.card_vertexCover_activeCb`).  Replacing the degree hypothesis by the degree-free local property
`JSP90.ShareCycleEdge` ("two odd cycles that meet share a cycle edge of the first") gives

> **`JSP90.erdos73On_of_shareCycleEdge_of_shortOddCycles`: `ShareCycleEdge G` + `LocIndep k G` + odd
> girth `≤ ℓ` ⇒ `CloseToBipartite (k * ((ℓ + 1) / 2)) G`**

— the constant of round 78 under a strictly weaker hypothesis (`JSP90.lemma_of_maxDegLe_three` shows
every subcubic graph satisfies `ShareCycleEdge`) — and, with **no local hypothesis at all**,

> **`JSP90.closeToBipartite_of_shareCycleEdge_of_packingOne`: every two odd cycles meet + odd girth
> `≤ ℓ` ⇒ `CloseToBipartite ((ℓ + 1) / 2) G`**, whose triangle level
> (`…_of_packingOne_of_three`) is a new instance of the headline theorem with no degree bound, sharp at
> `2` (`JSP90.not_closeToBipartite_one_K4`).

The remaining statement is now `JSP90.ShareEdgePackingOne r` (stated, not assumed), which drops **both**
hypotheses of the `k = 1` subcubic case and generalises `JSP90.SubcubicPackingOne`; and
`JSP90.not_shareEdgePackingOne_one` shows by machine check that `r = 1` is impossible (`p9`), so `r = 2`
is the sharp candidate.

**Round 81 (`lean/JSPProblem/Cactus.lean`, `lean/JSPProblem/Sun.lean`) — the ODD CACTUS axis: a new
class on which Erdős #73 holds at `k = 1` with the OPTIMAL constant `1`.**  The class
`JSP90.OddCactus G` says the odd cycles of `G` form a cactus: two *distinct* odd cycles meet in at
most one vertex (`JSP90.LinearOddCycles`) and three pairwise meeting odd cycles have a common vertex
(`JSP90.TwoHellyOddCycles` — no "ring").  It is a purely local intersection-pattern hypothesis: no
degree bound, no odd-girth bound, no connectivity, no decomposition; and it contains round 39's
class (`JSP90.OddCactus.of_oddCyclesDisjoint`).  The structural content is
`JSP90.disjoint_of_attach_ne` — two odd cycles meeting a common odd cycle at *different* vertices are
disjoint — and from it

> **`JSP90.erdos73On_oddCactus_one`: `LocIndep 1 G → OddCactus G → CloseToBipartite 1 G`** — a new
> instance of the headline theorem at `k = 1` with the **optimal** constant `1` (Erdős's hypothesis
> enters only through "every two odd cycles meet"),

together with `JSP90.erdos73On_oddCactus` at every `k` with the constant `k * (k + 1)`.  The constant
`1` is **exact** (`K₃` is an `OddCactus` `LocIndep 1` graph and is not bipartite) and the hypothesis
is **necessary**: the 3-sun `sun3` (six vertices, a triangle with a degree-2 vertex on each edge)
satisfies `LocIndep 1` and needs two vertices, and its three peripheral triangles form a ring — so
`sun3` is a six-vertex witness for `f(1) >= 2`, against the nine-vertex `p9` of round 76, and
`JSP90.not_oddCactus_sun3` shows the class cannot be enlarged.  An exhaustive search over **all**
`2^28` graphs on eight vertices (run *before* formalising, as the policy of rounds 76–80 requires)
shows that among the `52 256 816` graphs with `MaxDef <= 1` **none** needs three vertices, so the
route `f(1) >= 3` is dead and `f(k) >= 2k` is sharp at the level of the constant `2`.

The remaining statement of this attack is `JSP90.LinearRing` — the **ring lemma** (in a linear graph
three pairwise meeting odd cycles have a common vertex), stated as a `def` and *not* assumed;
`JSP90.OddCactus G` is exactly `LinearOddCycles G ∧ LinearRing G`.

**Round 87 (`lean/JSPProblem/PackDescent.lean`) — the PACKING-WEIGHTED residue descent, and the
SELF-PAY form of the blocker.**  Round 84's descent and round 86's blocker are statements about **one**
odd cycle and **one** vertex; round 87 generalises the descent to a whole packing and weakens the
blocker:

* **`JSP90.maxDef_ge_card_add_maxDef_delete`: `|𝒦| + MaxDef (deleteFinset G (⋃ 𝒦)) ≤ MaxDef G` for
  every family `𝒦` of pairwise vertex-disjoint odd cycles** — the deficiency of `G` pays for a whole
  packing of odd cycles *at once*, one unit each; this is the quantity that decreases along the
  classical Erdős–Pósa induction, and it strictly generalises round 84's `+1` residue descent
  (`JSP90.maxDef_ge_one_add_maxDef_delete` is its one-cycle case, so nothing is lost).  With it,
  `JSP90.defOf_biUnion_ge_card` (the union of `t` disjoint odd cycles has deficiency at least `t`),
  `JSP90.card_inter_biUnion_ge_card_of_maxDef` (a maximum-deficiency witness meets a packing of `t`
  odd cycles in at least `t` vertices) and the **tightness** results
  `JSP90.maxDef_deleteFinset_eq_zero_of_card_eq_maxDef` /
  `JSP90.hitsOddCycles_of_card_eq_maxDef` (a packing with as many members as the deficiency has its
  union as an odd cycle transversal and a bipartite residue — exhibited on `kTriangles k` by
  `JSP90.card_eq_maxDef_of_maxPacking_kTriangles`);

* **`JSP90.SelfPay G d` / `JSP90.HellySelfPay`: a *self-pay* deletion** `MaxDef (G − Z) + |Z| ≤ d`.
  `JSP90.selfPay_of_commonWitness` shows round 86's `JSP90.HellyCommonMaxWitness` implies it (so it is
  **strictly weaker**), `JSP90.erdos73On_helly_of_selfPay` /
  `JSP90.closeToBipartite_of_helly_of_selfPay` give **Erdős #73 with the optimal constant `f(k) = k`
  on the Helly class** from it, and `JSP90.hellySelfPay_of_hellyErdős73` shows it is **equivalent to
  the instance** `JSP90.HellyErdős73 id` itself.  Unlike the single-vertex descent it allows a whole
  set to be deleted in one step, which is what an absorption argument needs (round 44 proved the
  `+1` absorption step false).

The upper-bound side is unchanged: the missing statement is still `JSP90.OddCycleErdosPosa r` for all
`r` (equivalently `JSP90.TouchCriticalErdős73 c` for some `c`, per round 74, or
`JSP90.ShareEdgePackingOne r` for some `r` per round 80); behind it, on the Helly axis,
`JSP90.HellySelfPay` (equivalently `JSP90.HellyErdős73 id`).

**Round 90 (`lean/JSPProblem/CutVertex.lean`, 24 declarations, 0 sorry/admit) — the 2-CUT AXIS IS
CLOSED: `+1` iff the cut is clean, `+2` unconditionally, and both are sharp.**  Round 89 obtained
`CloseToBipartite (1 + m * r) G` over a *clean* 2-cut and machine-checked (windmill) that cleanliness
is not automatic.  This round answers exactly what replaces it.  The local fact
`JSP90.oddCycle_mem_b_of_halfPiece_of_isBipartite_part` is that *every odd cycle of the half-piece
`T_i ∪ {b}` over a bipartite part passes through `b`*; hence a bipartite part needs **no** hypothesis
and the refined cut step

> **`JSP90.VertexSplit.closeToBipartite_two_of_nonBipartiteParts`: every packing of odd cycles of `G`
> has at most `r` members and `CloseToBipartite m` on the half-pieces `T_i ∪ {a}` of the
> non-bipartite parts ⟹ `CloseToBipartite (2 + m * r) G`** —

with **no hypothesis on the cut at all** and a *strictly weaker* hypothesis than round 43's
`closeToBipartite_of_split_of_bounded_pieces_pack` (half-pieces `T_i ∪ {a}`, not pieces
`T_i ∪ {a,b}`).  In the two forms an induction consumes: `JSP90.closeToBipartite_of_split_step` /
`JSP90.closeToBipartite_of_split_of_oddCycleErdosPosa_two` (**the induction step of the classical
proof along a 2-cut**, no cut hypothesis) and `…_of_clean` (the `+1` form, `1 + m * r`).  New
instances of the headline theorem: `JSP90.erdos73On_of_split_two_of_nonBipartiteParts`
(`2 + m * k` from `LocIndep k`) and `…_of_bounded_branch` (`2 + (m + k) * k`).  The residue is exact
(`JSP90.VertexSplit.sdiff_biUnion_half`, `isBipartite_delete_of_both`).  And the obstruction is
pinned to the last degree by `JSP90.hitsOddCycles_empty_iff_isBipartite_half`: `X i = ∅` is a
transversal of the half-piece **iff** the half-piece is bipartite **iff** the cut is clean at `i`, so
`+1` vs `+2` is the exhaustive choice (`JSP90.windmill_plus_two_plus_one`).

**Round 93 (`lean/JSPProblem/MaxCut.lean`, 26 declarations, 0 sorry/admit) — the CUT AXIS: odd cycle
transversals are exactly the sets covering the monochromatic edges of a cut.**  Rounds 76–92 left the
max-cut / 2-colouring reformulation untouched.  With `JSP90.MonoEdge G A v w` (the edge `vw` does
not cross the cut with side `A`) and `JSP90.HitsMono G A Z`,

* **`JSP90.exists_monoEdge_of_isOddCycle`** — every odd cycle of `G` contains a monochromatic edge of
  *every* cut, both witnesses inside the cycle (`JSP90.even_of_cycle_noMono` is the parity lemma: a
  cycle all of whose edges cross a cut has even length);
* **`JSP90.hitsOddCycles_iff_hitsMono`** — the odd cycle transversals of `G` are exactly the
  monochromatic covers of some cut;
* **`JSP90.closeToBipartite_iff_hitsMono`** — **the conclusion of Erdős #73 is a cut certificate**:
  `CloseToBipartite q G ↔ ∃ A Z, HitsMono G A Z ∧ Z.card ≤ q` (with the explicit `2`-colouring
  `if v ∈ A then 0 else 1` of `G - Z` in `JSP90.isBipartite_deleteFinset_of_hitsMono`);
* **new instances of the headline theorem** `JSP90.erdos73On_of_hasMonoCover` (one cut carries a
  `q`-vertex certificate) and `JSP90.erdos73On_of_monoCoverBetween` (**one** set must cover the
  monochromatic edges of **every** cut separating two given vertex sets — the multiway-cut form);
* **exactness and obstruction**: `JSP90.exists_noMonoEdge_iff_isBipartite` (`q = 0` ⟺ bipartite),
  `JSP90.hasMonoCover_completeGraph_of_split` (on `K_n` the certificate is `n - 2`, exactly optimal),
  and the machine-checked `JSP90.not_hasMonoCover_completeGraph_three` — **the certificate depends on
  the cut**: `K_3` is `1`-close to bipartite but its trivial cut has no one-vertex certificate, while
  `JSP90.hasMonoCover_completeGraph_two_three` exhibits a cut of `K_3` whose certificate is exactly
  one vertex.

A bound on the certificate in terms of `MaxDef G` *is* `JSP90.OddCycleErdosPosa r` again (the
`iff` above), so what remains on this axis is a **local** bound — the classical max-cut bound
`τ(G) ≤ e(G)/2`, which needs a neighbourhood-counting apparatus absent from the pinned Mathlib slice.
**Round 98 (`lean/JSPProblem/DegColour.lean`, 26 declarations, 0 sorry/admit) — the DISJOINT-ODD-CYCLE
and the DEGREE–COLOURING axes.**  Round 38 proved `erdos73On_of_no_branch` ("no vertex has three
neighbours") with the *optimal* constant `k`; this round shows that the degree hypothesis is used
for exactly one thing and replaces it, and it builds the greedy colouring theorem, which the pinned
Mathlib slice does not have in any form (`JSPProblem/Layer.lean` has to define
`SimpleGraph.degree` by hand for the same reason).

* `JSP90.OddCycles G` is the family of *all* the odd cycles of `G`, and

  > **`JSP90.erdos73On_of_disjointOddCycles : LocIndep k G → DisjointFamily (OddCycles G) →
  > CloseToBipartite k G`** — a **new instance of the headline theorem with the optimal constant `k`
  > and a strictly weaker hypothesis**: the hypothesis is only "two distinct odd cycles are
  > vertex-disjoint" (no degree bound, no odd-girth bound, no connectivity, no decomposition), and
  > `JSP90.disjointFamily_oddCycles_of_no_branch` shows round 38's "every vertex has at most two
  > neighbours" is used for that one conclusion (`eq_of_mem_inter_of_no_branch`) and nothing else,
  > with `JSP90.erdos73On_of_no_branch'` re-proving round 38's instance from the new one;

* the class is **decided by a single count**, not merely bounded:
  **`JSP90.closeToBipartite_iff_card_oddCycles_of_disjoint : DisjointFamily (OddCycles G) →
  CloseToBipartite m G ↔ (OddCycles G).card ≤ m`** (upper bound: one vertex per odd cycle; lower
  bound: `JSP90.card_le_of_hitsOddCycles_disjoint`, a transversal meets the pairwise disjoint odd
  cycles in *different* vertices) — so the odd cycle transversal number of such a graph *equals* its
  number of odd cycles, and `JSP90.erdos73On_of_disjointOddCycles` is the case `m = k` of it;

* **the exact value of the constant on that class is `k`**:
  `JSP90.erdos73On_disjointOddCycles_exact` (for every `k ≥ 1`, the upper bound `k` holds and `k - 1`
  fails), the lower bound being the witness `kTriangles k` of `JSPProblem/Sharp.lean`, whose odd
  cycles are exactly its `k` pairwise disjoint fibres — proved here by
  `JSP90.exists_eq_tri_of_isOddCycle_kTriangles` (every edge of `kTriangles k` joins two vertices of
  one fibre, so a cycle lies in one fibre, and the fibre has three vertices);
  `JSP90.mem_oddCycles_tri`, `JSP90.disjointFamily_oddCycles_kTriangles`;

* **the greedy colouring theorem** (new machinery, from scratch):
  `JSP90.exists_colouringOn_of_degLe` is the greedy step by strong induction on the size of the
  vertex set (with `JSP90.exists_not_mem_of_card_lt`, the "there is a free colour" step);
  `JSP90.coloring_of_degLe` and `JSP90.coloring_of_maxDegLe`: a graph all of whose vertices have at
  most `d` neighbours is `Fin (d + 1)`-colourable; `JSP90.card_clique_le_of_coloring` is the
  converse *in the only form in which it is true* (a `(d+1)`-colouring bounds the size of a **clique**
  — a degree bound would be false, a 3-regular bipartite graph being 2-colourable);

* **`JSP90.OddColorClass`, `JSP90.closeToBipartite_of_oddColorClass`, `JSP90.erdos73On_of_oddColorClass`
  — a colour class is a certificate for the conclusion of Erdős #73**: if one colour class of a
  proper colouring meets every odd cycle and has at most `q` vertices, then
  `CloseToBipartite q G`.  This is a new hypothesis form of the headline theorem and the only form in
  which a colouring argument can be used; **properness alone is not a certificate**, and the
  machine-checked counterexample is `JSP90.g6` of `JSPProblem/Finite.lean`, which is `2`-close and
  not `1`-close to bipartite (`JSP90.not_closeToBipartite_one_g6'`).

The remaining statement of this attack is the *degree* part of the axis: `JSP90.SubcubicErdős73`
(3-connected case excluded, `LocIndep k G → MaxDegLe G 3 → CloseToBipartite g k G`) is still
*assumed* in `JSPProblem/Subcubic.lean`; the greedy theorem bounds cliques, not transversals, and a
`(d+1)`-colouring of a `d`-degenerate graph does **not** bound the size of a colour class, so the
degree axis needs the same kind of structural input as everything else.

**Round 99 (`lean/JSPProblem/Sparse.lean`, 29 declarations, 0 sorry/admit) — the EDGE-COUNTING axis:
the classical local bound `τ_odd(G) ≤ ⌊ |E(G)| / 2 ⌋`, and a new instance of the headline theorem in
which Erdős's hypothesis is not used at all.**  Every axis so far (anticomplete decompositions,
2-cuts, cut vertices, packings, fans, max-cuts, colourings) counts *vertices*; this one counts
**edges**, which is what round 93 recorded as the missing item (*"a bound coming from a **local**
quantity, e.g. the max-cut counting bound `τ(G) ≤ e(G)/2`, which needs a neighbourhood-counting
apparatus that `SimpleGraph.degree` does not provide at the pinned revision"*).  The apparatus now
exists on both sides: `JSPProblem/Layer.lean` supplies `JSP90.Neigh` and `JSP90.MaxDeg`, and the
pinned slice does provide `SimpleGraph.edgeFinset`, `SimpleGraph.degree` and
`SimpleGraph.sum_degrees_eq_twice_card_edges`.  With

* `JSP90.degSum G = ∑ v |N(v)|`, `JSP90.edgeCount G = |E(G)|` and
  `JSP90.two_mul_edgeCount : 2 * |E(G)| = degSum G`;
* `JSP90.degSum_deleteFinset : degSum (G - v) + 2 * |N(v)| = degSum G` and
  `JSP90.edgeCount_deleteFinset : |E(G - v)| = |E(G)| - |N(v)|` — the invariant of the induction;
* `JSP90.two_le_card_neigh_of_mem_oddCycle` — **every vertex of an odd cycle has at least two
  neighbours**, which is what makes such a vertex the right thing to delete,

one gets by induction on the budget

> **`JSP90.closeToBipartite_of_edgeCount_le : |E(G)| ≤ 2 * m + 1 → CloseToBipartite m G`**, i.e.
> **`τ_odd(G) ≤ ⌊ |E(G)| / 2 ⌋`** — the classical max-cut counting bound, in the `degSum` form
> `JSP90.closeToBipartite_of_degSum_le` as well;

and hence

> **`JSP90.erdos73On_of_edgeCount`** — a **new instance of the headline theorem** for the class of
> graphs with a bounded number of edges, whose constant does **not** mention `k`: the local
> hypothesis is never used — together with the order-dependent instance
> `JSP90.erdos73On_of_maxDegLe_of_card_le` (`τ_odd(G) ≤ ⌈ |V(G)| * Δ(G) / 2 ⌉`, i.e. `τ ≤ |V| Δ / 4`).

The constant is **machine-checked sharp** (`JSP90.edgeCount_completeGraph_three`,
`JSP90.edgeCount_bound_tight_completeGraph_three`: `|E(K_3)| = 3` and the transversal number of
`K_3` is exactly `1 = ⌊ 3/2 ⌋`) and **machine-checked loose in the direction of the deficiency**
(`JSP90.closeToBipartite_kTriangles_of_edgeCount`: on `kTriangles k` the edge count gives `3 k`
where the exact answer is `k`).  Why the axis stops here is also recorded: `LocIndep 0` **is**
bipartiteness (`JSP90.locIndep_zero_of_isBipartite`), and bipartite graphs have arbitrarily many
edges, so no function of `k` bounds `|E(G)|` — stated, not assumed, as
`JSP90.LocIndepEdgeUnbounded`.  The next statement of the axis, `JSP90.BoundedOddGirthEdgeCount`
(odd girth `ℓ` and degree `≤ d` ⟹ `f ℓ d`-close to bipartite), is stated and not assumed.

**Round 100 (`lean/JSPProblem/Pivot.lean`, 41 declarations, 0 sorry/admit) — the LOCAL-TRANSVERSAL
axis: round 99's recorded target is FALSE (machine-checked), and the correct statements replace it.**

* `JSP90.NeighClosed G C = C ∪ ∂C` and **`JSP90.hitsOddCycles_neighClosed_of_maxPacking`** — the
  distance-one neighbourhood of the union of a **maximum** packing of odd cycles is an odd cycle
  transversal — with `JSP90.card_neighClosed_maxPacking_le` for its size;
* `JSP90.two_le_card_inter_neigh_of_mem_oddCycle`, `JSP90.card_boundary_le_card_mul_sub_two` and
  `JSP90.card_neighClosed_le_card_mul_sub_one`, which **generalise** `JSPProblem/Subcubic.lean`'s
  `d = 3` statements to every degree `d ≥ 2` and every set `S`;
* `JSP90.erdos73On_of_neighClosedPacking` — `LocIndep k` + degree `≤ d` + odd cycles of length `≤ ℓ`
  ⟹ `CloseToBipartite (ℓ * k * (d - 1))`, with the transversal exhibited; the constant is **dominated**
  by `JSP90.erdos73On_of_bounded_odd_girth` (`ℓ * k`), the new content being the certificate;
* the **two-level odd-girth ladder** `JSP90.closeToBipartite_of_twoLevelGirth`,
  `JSP90.erdos73On_of_ladder`, `JSP90.erdos73On_of_ladder_subcubic` (`ℓ * (2 k - 1)`) and
  `JSP90.closeToBipartite_of_twoLevelGirth_degreeTwo`;
* **exactness at maximum degree `≤ 2`, for every `k`**: `JSP90.maxDegLe_two_iff_oddCyclePackingLe`
  (`τ_odd = ν_odd` exactly), `JSP90.erdos73On_of_maxDegLe_two` with the optimal constant `k`, attained
  on `kTriangles k`;
* **`JSP90.not_boundedOddGirthEdgeCount`**: round 99's `JSP90.BoundedOddGirthEdgeCount` is **false**
  (odd girth and degree alone do not bound the transversal), and
  **`JSP90.not_oddGirth_bound_without_packing`**: an odd girth from *below* bounds nothing — only an
  upper bound on the length of the odd cycles pays.

**Round 103 (`lean/JSPProblem/Budget.lean`, 28 declarations, 0 sorry/admit) — the PACKING BUDGET
AXIS: `k - j` at level `j`, in both the packing and the deficiency form.**  Round 102's greedy chain
could only be used to make the *last* level bipartite; the concrete lemma it was missing —
`OddCyclePackingLe (k - j) (level G j)` — is now proved, and so is its stronger deficiency form.

* **The exchange lemma** `JSP90.oddCycleFamily_union_chainBelow`: a packing of the residue at level
  `j`, adjoined with the `j` greedy cycles of the earlier levels, is a packing of odd cycles of `G` of
  size `P.card + j` (`JSP90.disjoint_unionUpTo_of_isOddCycle_level`,
  `JSP90.not_mem_chainBelow_of_isOddCycleFamily`, `JSP90.biUnion_chainBelow`);
* **`JSP90.level_oddCyclePackingLe`: `LocIndep k G → j ≤ k → OddCyclePackingLe (k - j) (level G j)`**
  (the *packing budget*), with `JSP90.level_packing_add_le`, the residue step
  `JSP90.level_oddCyclePackingLe_one`, and `JSP90.level_isBipartite_of_budget`;
* **`JSP90.level_locIndep`: `LocIndep k G → LocIndep (k - j) (level G j)`** (the *deficiency
  budget*), from round 87's `maxDef_ge_card_add_maxDef_delete` along the chain
  (`JSP90.level_maxDef_add_le`), hypothesis-free up to the first bipartite level
  (`JSP90.level_locIndep_of_firstBipartite`), and at the top (`JSP90.level_locIndep_one`) — this is
  the parameter the classical Erdős–Pósa descent decreases, and it was absent before;
* **`JSP90.closeToBipartite_of_greedyChain_cost` / `JSP90.stepCost`** — the ladder with a
  **per-level residue price**, strictly generalising round 102's step, giving the **new instance**
  `JSP90.erdos73On_of_greedyChain_cost` (`LocIndep k G` + "each greedy residue is `c i`-close to
  bipartite" ⇒ `CloseToBipartite (∑ j < k, girthOf (level G j) + c (j + 1)) G`) and its unit-cost
  corollary `JSP90.closeToBipartite_of_greedyChain_cost_one`, strictly cheaper than round 102's
  constant by exactly `k`.

The budgets do not by themselves improve the constant of `JSP90.erdos73On_of_greedyChain` (the greedy
sum is not a function of `k`, round 102); the missing half is unchanged, `JSP90.OddCycleErdosPosa r`.

**Round 104 (`lean/JSPProblem/Cluster.lean` + `lean/JSPProblem/ClusterSharp.lean`, 59 declarations,
0 sorry/admit) — the CLUSTER-GRAPH AXIS: a new instance with the optimal constant `k` on the
largest class on which hypothesis and conclusion coincide.**

* `JSP90.ClusterDecomposition G 𝒬` — the pieces are pairwise disjoint, pairwise anticomplete, cover
  `V`, have at least two vertices, and are **cliques**; i.e. `G` is a disjoint union of complete
  graphs;
* **`JSP90.erdos73On_of_cluster`**: `ClusterDecomposition G 𝒬 → LocIndep k G → CloseToBipartite k G`
  (with `_univ`), the **new instance** of the headline theorem, with no odd girth, no packing weight,
  no degree bound and no bound on the number of pieces;
* **`JSP90.closeToBipartite_iff_maxDef_cluster`**: on this class `CloseToBipartite m G ↔ MaxDef G ≤ m`,
  and **`JSP90.maxDef_cluster`**: `MaxDef G = ∑ C ∈ 𝒬, (|C| - 2)` — the deficiency *is* the sum of the
  piece costs, via `JSP90.indepCard_cluster` (`α(G[X])` = number of pieces met) and the transversal
  `JSP90.exists_oddCycle_transversal`;
* **`JSP90.erdos73On_of_cluster_optimal`** (`ClusterSharp.lean`): the new instance is an
  **equivalence** on `kTriangles k`, `(LocIndep k → CloseToBipartite m) ↔ k ≤ m`, with
  `JSP90.maxDef_kTriangles_eq : MaxDef (kTriangles k) = k`, so the constant is optimal; and
  `JSP90.erdos73_cluster_notBelowK` re-derives the lower bound `f(k) ≥ k` *through* the new instance.
  The class is strictly larger than round 98's (`K_5 ⊔ K_5` is a cluster graph that is not a disjoint
  union of odd cycles).

The missing half is unchanged: `JSP90.OddCycleErdosPosa r`, i.e. `jsp_000090_main`.

**Round 105 (`lean/JSPProblem/Exact.lean`, 26 declarations, 0 sorry/admit) — the EXACT-ADDITIVITY
axis: the statement `JSPProblem/Deficiency.lean` records as *missing*.**  That file proves only
`MaxDef G ≤ MaxDef (G[A]) + MaxDef (G[B])` over an anticomplete decomposition and says the converse
"is not proved here"; round 104 had to re-derive the equality under the narrow hypothesis "every
piece is a clique".  This file proves it in general and pushes the same statement through the
conclusion, so that **both sides of Erdős #73 split exactly over an anticomplete cover**:

* **`JSP90.maxDef_anticover_add : MaxDef G = MaxDef (G[A]) + MaxDef (G[B])`** (from
  `JSP90.maxDefIn_anticoverIn_add`, stated for `AnticoverIn G s A B`), together with the linear split
  `JSP90.card_indepCard_anticoverIn_add` (`|Y| = |Y ∩ A| + |Y ∩ B|` and
  `α(G[Y]) = α(G[Y ∩ A]) + α(G[Y ∩ B])` over a split of a vertex set `s`), which generalises
  `JSPProblem/Deficiency.lean`'s version, stated only for `Y ⊆ V`.  The mechanism is **attainment**,
  not monotonicity: `defOf` is a truncated subtraction and is *not* monotone under vertex sets (the
  file header records the machine-checked obstruction `K_3 ⊔ K_1`, and the false consequence
  `maxDefIn G U = defOf G U`), but a vertex set attaining each side's maximum with positive
  deficiency satisfies `|X| ≥ 2 α(G[X])`, so the two sides pay separately and no truncation occurs;
* **`JSP90.maxDef_eq_sum_of_cover : MaxDef G = ∑ X ∈ 𝒬, MaxDef (G[X])`** for *any* pairwise
  anticomplete cover of the vertices (induction on the family, one piece peeled at a time), with
  `JSP90.locIndep_cover_iff` (the hypothesis splits) and `JSP90.maxDef_eq_sum_cost_of_cover`, so
  **round 104's `maxDef_cluster` is now a corollary** of `JSP90.maxDef_clique`
  (`MaxDef (G[C]) = |C| − 2` for a clique `C` of at least two vertices, with the transversal
  `JSP90.closeToBipartite_of_clique`);
* **the conclusion splits too**: `JSP90.closeToBipartite_of_cover_cost` and the *exact*
  `JSP90.closeToBipartite_iff_cost_cover` — `CloseToBipartite m G ↔ ∃ c, (∀ X ∈ 𝒬,
  CloseToBipartite (c X) (G[X])) ∧ ∑ c X ≤ m` — with `JSP90.card_sum_inter_le` for the counting;
* **`JSP90.erdos73On_of_pieceMaxDef` — a NEW INSTANCE with the optimal constant `k`** on
  `JSP90.PieceMaxDef G 𝒬`, the **cover closure of the class on which the hypothesis and the
  conclusion of Erdős #73 coincide** (the pieces pay their deficiency jointly, because the deficiency
  splits over the cover and the per-piece deletion sets are disjoint).  `JSP90.pieceMaxDef_of_cluster`
  puts round 104's cluster class inside it (strictly: `K_5 ⊔ K_{2,3}` is on it and is not a cluster
  graph), `JSP90.closeToBipartite_iff_maxDef_of_pieceMaxDef` gives hypothesis = conclusion on the
  class, and **`JSP90.erdos73On_of_pieceMaxDef_optimal`** proves the constant `k` machine-checked
  optimal on the lower-bound witness `kTriangles k`, re-deriving `f(k) ≥ k`.

The missing statement is unchanged: `jsp_000090_main` is still not declared and
`JSP90.OddCycleErdosPosa r` (the 3-connected case) is untouched — this file relates the two sides of
Erdős #73 to each other over covers, it does not bound the transversal of a graph whose pieces are
themselves not covered.

## Round 106 note (`lean/JSPProblem/Multi.lean`)

New attack family, the **complete multipartite axis**.  `multi t n` = the complete multipartite
graph with `t` parts of `n` vertices (`Fin t × Fin n`).  Proved, with 0 sorry/admit:

* `MaxDef (multi t n) = (t - 2) * n` — the exact value of Erdős's hypothesis on this class
  (`JSP90.maxDef_multi`, `JSP90.locIndep_multi_iff`);
* `CloseToBipartite m (multi t n) ↔ (t - 2) * n ≤ m` — the exact value of the conclusion
  (`JSP90.closeToBipartite_iff_multi`), via the characterisation
  `JSP90.isBipartite_deleteFinset_multi_iff` ("`G − X` is bipartite iff its surviving vertices lie in
  at most two parts");
* **`JSP90.erdos73On_of_multi`** — a new instance of the headline theorem with the **optimal
  constant `f(k) = k`**, with its optimality machine-checked (`JSP90.erdos73On_of_multi_optimal`,
  `JSP90.not_closeToBipartite_multi`).

On this class the hypothesis and the conclusion of Erdős #73 coincide, and the class is
**connected** for `t ≥ 2`, so it is not covered by any anticomplete-decomposition instance of the
earlier rounds.  `jsp_000090_main` remains undeclared and `JSP90.OddCycleErdosPosa r` (Reed–
Robertson–Seymour–Thomas) is unchanged: the remaining obstruction is the general, 3-connected case.

## Round 107 note (`lean/JSPProblem/Split.lean`)

New attack family, the **split-graph axis**: `V = A ⊔ B` with `A` independent and `B` a clique.  It
is the connected class whose odd cycles straddle a partition — the class none of the additive axes
(rounds 98–106) reaches — and it is the **first class whose optimal constant is strictly larger than
`k`** while the odd cycles are still described by one local rule ("a triangle is a clique edge plus a
common neighbour on the independent side").  Proved, with 0 sorry/admit (32 declarations):

* `JSP90.SplitPartition G A B` and `card_eq_card_inter_add_card_inter_splitPartition` (`|X| = |X ∩ A|
  + |X ∩ B|`): the class and its counting lemma;
* `JSP90.cardB_le_locIndep_add_two` — **Erdős's hypothesis sees only the size of the clique side**
  (`LocIndep k G → |B| ≤ k + 2`; this is the *only* use of the hypothesis, applied to `X = B`), and
  `JSP90.maxDef_split_le` (`MaxDef G ≤ |B| − 1`);
* `JSP90.IsolatedPair G A B` — the deciding local object: a pair of clique vertices with **no**
  common neighbour in `A`;
* `JSP90.closeToBipartite_split_iff` — **the exact value of the conclusion on this class**:
  `CloseToBipartite m G ↔ |B| ≤ m + 1 ∨ (|B| ≤ m + 2 ∧ IsolatedPair G A B)`, i.e. `τ(G) = |B| − 1`,
  or `|B| − 2` when an isolated pair exists; the `|B| − 2` clause is an equivalence
  (`closeToBipartite_split_cardB_sub_two_iff`), and the machinery is the triangle obstruction
  `not_isBipartite_deleteFinset_of_commonNeighbour` plus the injection
  `cardBsdiff_le_two_of_isBipartite_deleteFinset`;
* **`JSP90.erdos73On_of_splitPartition` — a NEW INSTANCE OF THE HEADLINE THEOREM with the constant
  `k + 1`** (no odd-girth, packing, degree or decomposition hypothesis), with the sharper form
  `closeToBipartite_of_splitPartition_of_isolatedPair` (constant `k`);
* Part 4 of the file records the **witness** on which the constant `k + 1` is attained.  **Round 108
  refuted that part**: the graph named there (`K_{k+2,k+2}` minus a perfect matching) is *bipartite*,
  so its "clique side" carries no edge and it is not a split graph at all; moreover the independent
  set it proposed is not independent, because the cross edge `a_i ~ b_j` is present when `i ≠ j`.

## Round 108 — `JSPProblem/SplitSharp.lean`: the correct witness, and `f(k) ≥ k + 1`

The corrected witness `JSP90.splitWitness n` on `Fin n × Bool` — the same two sides
`A = {(i, false)}` (independent) and `B = {(i, true)}` (a clique), with `Adj p q ↔ p.1 ≠ q.1 ∧
¬ (p.2 = false ∧ q.2 = false)` — settles the axis exactly:

* `JSP90.splitWitness_splitPartition`: it is a split graph with `n` vertices on each side;
* `JSP90.not_isolatedPair_splitWitness`: every pair of `B` has a common neighbour in `A`
  (`3 ≤ n`), so no isolated pair exists;
* **`JSP90.locIndep_splitWitness`: `LocIndep k (splitWitness (k + 2))`** — the hypothesis holds, so
  the witness is in range; the only counting input is
  `|X ∩ A| + |X ∩ B| = |I ∩ J| + |I ∪ J|` for `I = (X ∩ A).image fst`, `J = (X ∩ B).image fst`;
* **`JSP90.maxDef_splitWitness`: `MaxDef (splitWitness (k + 2)) = k`** — the exact value of Erdős's
  hypothesis on this graph, so the witness is tight for `LocIndep` as `kTriangles k` is;
* **`JSP90.closeToBipartite_iff_splitWitness`: `CloseToBipartite m (splitWitness (k + 2)) ↔ k + 1 ≤
  m`** for `k ≥ 1` — the exact value of the conclusion;
* **`JSP90.not_erdos73On_splitWitness`: `¬ Erdős73On k k` for every `k ≥ 1`**, i.e. the constant
  `f(k)` of Erdős #73 satisfies **`f(k) ≥ k + 1`**.  This is the first machine-checked lower bound
  on that constant strictly larger than the `f(k) ≥ k` of rounds 39/104, and it is a statement about
  the answer to the problem, not only about a class;
* `JSP90.erdos73On_of_splitPartition_optimal`: the constant `k + 1` of round 107's split-graph
  instance is **optimal**.

`jsp_000090_main` remains undeclared and `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas)
is unchanged: the remaining obstruction is the general, 3-connected case.

## Round 109 — `JSPProblem/Chain.lean`: the decrease at a hard 1-cut, and the block-cut bound

The class axis is closed on both sides (rounds 104–108), so this round works on the packing-number
axis, on its *quantitative* content: what a 1-cut does to the packing bound.

* **`JSP90.OneSplit.packing_part_le`**: under a packing bound `r`, a non-bipartite part `T_i` of a
  1-cut whose `s` non-bipartite parts satisfies **packing number of `G[T_i]` ≤ `r + 1 − s`**.  For
  `s = 2` the bound strictly decreases (`packing_part_le_lt`); the input is
  `OneSplit.oddCycle_family_erase`, one odd cycle in each of the other non-bipartite parts,
  pairwise disjoint and as many as there are parts;
* **`JSP90.OneSplit.packing_part_no_decrease_of_oneSide`**: at a one-sided 1-cut (`s = 1`) the bound
  is inherited unchanged — the descent stalls, the machine-checked form of round 48's negative
  result number 1;
* **`JSP90.closeToBipartite_of_1split_of_decreasing`**: a new instance of the headline theorem along
  the 1-cut axis whose hypothesis on the parts is needed only at the **decreased** bound
  `r + 1 − s`, with the constant `1 + s · m`, independent of the number of parts and with no bound
  on the odd girth, packing weight or number of branch vertices;
* **`JSP90.hardCert_isBipartite_of_packing_le`**: a packing bound `r` forbids a chain of `r + 1`
  cut vertices *each of which separates two non-bipartite sides*
  (`exists_packing_of_hardCert`: such a chain gives `r + 1` disjoint odd cycles).  This is round
  48's named missing lemma `oneDepth_le_of_packing` in the form in which it is true;
* **`JSP90.locIndep_param_cannot_be_lowered`** (machine-checked negative result): `LocIndep 1 (K_3)`
  holds while `¬ LocIndep 0 (K_3)`, so the descent cannot be stated in Erdős's own parameter — it
  runs on the packing number.

The remaining obstruction is located exactly: the **one-sided chains** (cut vertices with a single
non-bipartite side), which cannot be bounded by the packing number and need the block-cut tree and
the short-C-path lemma.  `jsp_000090_main` remains undeclared and
`JSP90.OddCycleErdosPosa r` is unchanged.

---

## Round 110 note

New module `lean/JSPProblem/Piece.lean` (0 `sorry`, 0 `admit`, `lake build` OK): the cut-vertex
**piece** axis.  `JSP90.OneSplit.cycle_subset_piece` (an odd cycle through the cut vertex lies in a
single piece) completes the local structure at a 1-cut, so the odd cycles of `G` are exactly those
of its pieces; the composition rule then costs **no `+1`** for the cut vertex
(`JSP90.closeToBipartite_of_1split_bounded_pieces`, `…_twoPieces` with the sharp `2 * m`,
`…_nonBipartitePieces`), and **a one-sided 1-cut is free**
(`JSP90.closeToBipartite_iff_of_oneNonBipartitePiece`, iterated in
`JSP90.closeToBipartite_iff_of_twoSideCuts`) — this is the machine-checked block-cut reduction, so the
short-`C`-path lemma that `policy.json` demanded for the one-sided chains is **not needed**.
`JSP90.wf_locIndep_one_two_nonBipartitePieces` records why no `f(k)` comes out of the piece count.

## Round 111 note (attack family 52)

`JSPProblem/CPath.lean` introduces **Mader's C-path** (`JSP90.IsCPath`), proves that a C-path may be
extended by one edge, and derives the **two-attachment transversal**: if every odd cycle of `G`
meets one odd cycle `C` in at least two vertices, then `G` is the union of a bipartite graph and at
most `|C| - 1` vertices — a bound **independent of `k`**, the first such bound in this development.
It is a new instance of the headline theorem (`JSP90.erdos73On_of_twoAttach`).  The second half of
the step named by `policy.json` (the shortest `C`-path is induced) is the next round's target:
`IsCPath.skip` → `IsCPath.Shortest` → `IsCPath.induced_of_shortest`.  `jsp_000090_main` is still not
declared.

## Round 114 note (`lean/JSPProblem/CPathPair.lean`, attack family 54) — the FAN at depth two:
## Mader's two-attachment lemma

Round 112 named the missing depth-two step, and this file delivers it.  **No Menger theorem** is
used: the two arcs between the two attachment points are counted, and the parity decides which of the
two closed walks `arc + p + q` is an odd cycle.  52 declarations, 0 sorry/admit:

* **`JSP90.IsCPathPair`** — **THE OBJECT: THE FAN AT DEPTH TWO.**  Two `C`-paths `p`, `q` to a
  common target `x ∉ C`, ending at **distinct** vertices `f i`, `f j` of `C`, whose vertex sets meet
  only in `{f i, f j, x}`.  `IsCPathPair.d1_pos`/`d2_pos` (a length-0 `C`-path would put its target
  on `C`), `IsCPathPair.eq_fi_of_mem_supset_p_mem_C` (the first path meets `C` in exactly its first
  vertex) and **`IsCPathPair.inter_ne`** (the two interiors never meet);
* **`JSP90.arcPairFun`** — **THE TWO-PATH ARC CYCLE**, the closed walk
  `f j → (arc of length `e`) → f i → p → x → q → f j` on `Fin (e + d1 + d2)`.  For `d1 = d2 = 1` it is
  `JSPProblem/Fan.lean`'s `arcFun`, so the constructor **generalises** it to two paths of arbitrary
  length.  `arcPairFun_inj` (**the walk is simple**), `arcPairFun_adj` (**every step is an edge**,
  including the closing step `q 1 ~ q 0 = f j`), `arcPair_isOddCycle` and `card_arcPair` (**exactly**
  `e + d1 + d2` vertices);
* **`JSP90.exists_oddCycle_twoAttach_of_isCPathPair` — MADER'S TWO-ATTACHMENT LEMMA**: if `x` has two
  internally vertex-disjoint `C`-paths to two distinct vertices of an odd cycle `C`, then `x` lies on
  an **odd cycle of `G` through both attachment points**.  This is the *second* attachment point, the
  resource round 112 asked for (rounds 111–112 produced only one-attachment odd cycles), and the
  first odd cycle of `G` this development builds through a vertex at `C`-distance `≥ 2`.  The parity
  is pure counting (`JSP90.mod_two_of_sum_odd`): the two candidate totals add up to
  `m + 2 (d1 + d2)`, which is odd;
* **`JSP90.arc_sum_ge_of_shortest` — A SHORTEST ODD CYCLE IS THICK**: at a shortest odd cycle of
  length `m`, `m ≤ e + d1 + d2` for the odd arc; in the fan case this forces
  **`JSP90.oddArc_eq_two_of_fan_of_shortest`**, the odd arc has length exactly `m - 2`, and hence
  **`JSP90.shortArc_of_pairFan`** — the short-arc lemma of `JSPProblem/Fan.lean`, re-derived here
  from the two-path arc cycle and its vertex count.  The depth-one input is now *derived*, not
  assumed: `IsCPath_edgePath` (a length-1 `C`-path is an edge) and `isCPathPair_of_adj` (a vertex
  adjacent to two distinct vertices of `C` **is** a fan);
* **`JSP90.twoAttach_kTriangles_one`** — the two-attachment hypothesis *holds* on `kTriangles 1`
  (`CloseToBipartite 2 (kTriangles 1)`), so round 111's transversal is not vacuous, and
* **`JSP90.not_twoAttach_kTriangles_two`** — **machine-checked negative result**: on `kTriangles 2`
  **no** odd cycle is two-attached, so round 111's hypothesis is not automatic and needs real
  content.

Mader's lemma is a *resource*, not a transversal: it exhibits an odd cycle through `x` meeting `C`
twice, but it does not make the two-attachment hypothesis hold for every odd cycle of `G`.  The
two-attachment **cover** of round 112 still needs its global existence statement, together with the
absorption of the one-attachment odd cycles.  `jsp_000090_main` remains undeclared and
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) is unchanged.

## Round 112 note (`lean/JSPProblem/CPathSkip.lean`, attack family 53)

Round 111 defined Mader's `C`-path and left three named lemmas.  All three are now proved, plus the
transversal they make possible:

* `JSP90.IsCPath.skip` — **a chord of a `C`-path shortens it** (the splice `skipPath`), with
  `skip_len_lt` recording the strict decrease `a + 1 + (d - b) < d`;
* `JSP90.IsCPath.Shortest` + **`JSP90.IsCPath.induced_of_shortest`: THE SHORTEST `C`-PATH IS
  INDUCED** — the exact lemma named by the round-111 policy.  With
  `JSP90.IsCPath.adj_target_of_shortest` (Mader's neighbour count at the far end) and
  `JSP90.IsCPath.adj_iff_step_of_shortest` (the full neighbour count) the local structure of a
  shortest `C`-path is complete;
* **`JSP90.IsCPath.isOddCycle_return`** — **a closed `C`-path of even length is an odd cycle of `G`**,
  and `JSP90.oneAttach_of_isCPath_return` records that this odd cycle meets `C` in **exactly one
  vertex** and contains the target: *Mader's one-attachment lemma in `C`-path form*, the first
  single-attachment odd cycle this development constructs;
* **`JSP90.closeToBipartite_of_twoAttachCover`** — **THE TWO-ATTACHMENT COVER**, a **strict
  generalisation** of round 111's `closeToBipartite_of_twoAttach`: a family `𝒞` of vertex sets (the
  members need **not** be odd cycles, and there is **no bound** on their number) such that every odd
  cycle of `G` meets some member in at least two vertices gives
  `CloseToBipartite (∑ X ∈ 𝒞, |X| - 1) G`; the singleton case is round 111's theorem
  (`closeToBipartite_of_twoAttachCover_of_singleton`).  The certificate and its cost are
  `hitsOddCycles_of_twoAttachCover` and
  `card_biUnion_erase_le_sum_card_sub_one_of_twoAttachCover`, with counting input
  `exists_mem_inter_erase_of_card_ge_two`;
* **new instances of the headline theorem** with constants independent of `k`:
  `JSP90.erdos73On_of_twoAttachCover` (cost `∑ X ∈ 𝒞, |X| - 1`) and
  `JSP90.erdos73On_of_twoAttachCover_bounded` (cost `ℓ * |𝒞|` when every cover member has at most `ℓ`
  vertices — the Erdős–Pósa shape, one unit per cover member).

The one-attachment lemma yields an odd cycle attached **once**, which no transversal pays for; the
*two-attachment cover* is what pays, and its existence for a 3-connected graph is the unresolved
part.  `jsp_000090_main` remains undeclared and `JSP90.OddCycleErdosPosa r` is unchanged.
