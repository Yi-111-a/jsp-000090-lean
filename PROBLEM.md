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
