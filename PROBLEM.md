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
