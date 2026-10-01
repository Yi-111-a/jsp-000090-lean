import JSPProblem.DegColour
import JSPProblem.Sun
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# JSP-000090, round 99 — the EDGE-COUNTING axis: **the odd cycle transversal is at most half the
number of edges**, a *local* bound, and a new instance of the headline theorem in which Erdős's
local hypothesis is not needed at all.

## What this file is

Every decomposition axis of JSP-000090 so far (the anticomplete decompositions of round 47, the
2-cuts of rounds 43/90, the cut vertices of rounds 43–48, the packing descent of round 87, the
fans of rounds 69–74) counts *vertices*.  This file counts **edges**, which is the classical way
to bound an odd cycle transversal:

> `JSP90.closeToBipartite_of_edgeCount_le` — **if `G` has at most `2 * m + 1` edges then deleting
> at most `m` vertices leaves a bipartite graph**, i.e. **`τ_odd(G) ≤ ⌊ |E(G)| / 2 ⌋`.**

This is the classical max-cut counting bound, recorded as the missing *local* quantity in
`JSPProblem/MaxCut.lean` (round 93): *"a bound on the certificate in terms of `MaxDef G` **is**
`JSP90.OddCycleErdosPosa r` again; what is still missing on this axis is a bound coming from a
**local** quantity (e.g. the max-cut counting bound `τ(G) ≤ e(G)/2`, which needs a
neighbourhood-counting apparatus that `SimpleGraph.degree` does not provide at the pinned
revision)"*.  The apparatus now exists on both sides: `JSPProblem/Layer.lean` (round 77) supplies
`JSP90.Neigh` and `JSP90.MaxDeg` as finsets, and the pinned Mathlib slice does provide
`SimpleGraph.edgeFinset`, `SimpleGraph.degree` and `SimpleGraph.sum_degrees_eq_twice_card_edges`.

## The idea

Two facts do all the work.

* **`JSP90.degSum_deleteFinset` — deleting one vertex removes exactly its degree from the degree
  sum, on both sides: `degSum (G - v) + 2 * |N(v)| = degSum G`.**  Each of the `|N(v)|` edges
  incident to `v` is counted once in `degSum G` at each of its two ends, and both counts disappear
  when `v` is deleted.
* **`JSP90.two_le_card_neigh_of_mem_oddCycle` — every vertex of an odd cycle has at least two
  neighbours** (the two cycle-neighbours; this is `two_le_innerDeg_of_mem_oddCycle` of
  `JSPProblem/Layer.lean` read at `S = ∅`).

Induction on `m`: if `G` is not bipartite, delete a vertex of an odd cycle.  Its degree is at least
`2`, so `|E(G - v)| ≤ |E(G)| - 2`, the hypothesis `|E| ≤ 2 * m + 1` passes to
`|E| ≤ 2 * (m - 1) + 1`, and one more vertex is charged.

## The new instance of the headline theorem, and what it costs

`JSP90.erdos73On_of_edgeCount` is a new instance of Erdős #73 whose hypothesis is

```
|E(G)| ≤ 2 * m + 1
```

with **no reference to `k`**: it is an instance for the class of graphs with a bounded number of
edges, and the proof never uses Erdős's local hypothesis — `LocIndep k G` is a hypothesis of the
packaged statement only so that the statement has the shape of an instance.

**This is also the sharp limit of the axis.**  A bound on `|E(G)|` is *not* implied by
`LocIndep k G` for any `k`: `LocIndep 0` is *equivalent* to `G` being bipartite
(`locIndep_iff_maxDef_le` with `maxDef_eq_zero_iff`), and bipartite graphs have arbitrarily many
edges — so the constant of this file's instance is **not a function of `k`**, and this axis does
not by itself produce a value of `f(k)`: it is the *local* counterpart of the theorem, not an
instance of it.  What it does produce, besides the sparse instance, is the classical order-dependent
instance `JSP90.erdos73On_of_maxDegLe_of_card_le` (`|N(v)| ≤ d` and `|V| ≤ n` ⟹
`⌈n * d / 2⌉`-close to bipartite), which is the statement `τ ≤ |V| * Δ / 4`.

## Sharpness

The constant `⌊ |E| / 2 ⌋` is **attained**: `JSP90.edgeCount_completeGraph_three` is `3` while
`JSP90.not_closeToBipartite_zero_completeGraph_three` says `K_3` is not bipartite, so on the class
of graphs with three edges the bound `⌊ |E| / 2 ⌋ = 1` is exact.  In the other direction the bound
is loose: on `kTriangles k` (`JSPProblem/Sharp.lean`) it gives `⌈ 3 k / 2 ⌉` where the exact answer
is `k`.

## The remaining statement on this axis

`JSP90.BoundedOddGirthEdgeCount` — *a graph of odd girth `ℓ` in which every vertex has at most `d`
neighbours is `f ℓ d`-close to bipartite* — is **stated, not assumed**; nothing above proves it,
because the induction above pays for a vertex of degree at least `2` and says nothing about the
higher degrees a shortest odd cycle would need.

`jsp_000090_main` is still not declared: behind it stands `JSP90.OddCycleErdosPosa r`.  See
`discovery/JSP-000090/policy.json`.
-/

namespace JSP90

noncomputable section

variable {V : Type*} [Fintype V]

local instance instDecidableEqSparse : DecidableEq V := Classical.decEq V

local instance instDecidableRelSparse {G : SimpleGraph V} : DecidableRel G.Adj :=
  Classical.decRel G.Adj

/-! ### Part 1 — counting the edges of a graph -/

section Counting

variable {G : SimpleGraph V}

/-- **The degree sum of `G`**: `∑ v, |N_G(v)|`, i.e. twice the number of edges.  This is the
counting quantity of this file; `JSPProblem/Layer.lean` supplies `Neigh`. -/
noncomputable def degSum (G : SimpleGraph V) : ℕ := ∑ v, (Neigh G v).card

/-- **The number of edges of `G`**, each edge counted once: Mathlib's `SimpleGraph.edgeFinset`, a
finset of `Sym2 V`, which is available at the pinned revision. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ := G.edgeFinset.card

/-- The neighbourhood finset of `v`, as Mathlib sees it. -/
theorem neighborFinset_eq_neigh (G : SimpleGraph V) (v : V) : G.neighborFinset v = Neigh G v := by
  ext w
  simp [Neigh, SimpleGraph.mem_neighborFinset]

/-- **THE DEGREE SUM COUNTS EVERY EDGE TWICE**: `2 * |E(G)| = degSum G`.

This is Mathlib's `SimpleGraph.sum_degrees_eq_twice_card_edges`, read with `Neigh`; it is what
makes `edgeCount` the classical object the rest of the development counts. -/
theorem two_mul_edgeCount (G : SimpleGraph V) : 2 * edgeCount G = degSum G := by
  have h1 : ∀ v : V, G.degree v = (Neigh G v).card := fun v => by
    unfold SimpleGraph.degree
    rw [neighborFinset_eq_neigh]
  calc 2 * edgeCount G = 2 * G.edgeFinset.card := rfl
    _ = ∑ v : V, G.degree v := (SimpleGraph.sum_degrees_eq_twice_card_edges G).symm
    _ = degSum G := by
        unfold degSum
        exact Finset.sum_congr rfl fun v _ => h1 v

/-- **THE NEIGHBOURHOOD OF A VERTEX OF THE RESIDUE, SPELLED OUT.** -/
theorem mem_neigh_deleteFinset' (G : SimpleGraph V) {v w x : V} :
    x ∈ Neigh (deleteFinset G {v}) w ↔ w ≠ v ∧ x ≠ v ∧ G.Adj w x := by
  simp [Neigh, deleteFinset_adj]

/-- The neighbourhood of a vertex of `G - v`, for `v ≠ w`, is the neighbourhood in `G` with `v`
erased. -/
theorem neigh_deleteFinset (G : SimpleGraph V) {v w : V} (hvw : v ≠ w) :
    Neigh (deleteFinset G {v}) w = (Neigh G w).erase v := by
  ext x
  rw [Finset.mem_erase, mem_neigh_deleteFinset', mem_neigh]
  tauto

/-- **The degree of a vertex `w ≠ v` drops by exactly one if `w` is adjacent to `v`, and not at all
otherwise.** -/
theorem card_neigh_deleteFinset (G : SimpleGraph V) {v w : V} (hvw : v ≠ w) :
    (Neigh (deleteFinset G {v}) w).card = (Neigh G w).card - if G.Adj v w then 1 else 0 := by
  rw [neigh_deleteFinset (G := G) (v := v) (w := w) hvw, Finset.card_erase_eq_ite]
  by_cases h : G.Adj v w
  · rw [if_pos h, if_pos (show v ∈ Neigh G w from mem_neigh.mpr (G.adj_symm h))]
  · rw [if_neg h, if_neg (show v ∉ Neigh G w from fun hh => h (G.adj_symm (mem_neigh.mp hh)))]
    omega

/-- The vertex deleted from `G` has no neighbours left in the residue. -/
theorem card_neigh_deleteFinset_self (G : SimpleGraph V) (v : V) :
    (Neigh (deleteFinset G {v}) v).card = 0 := by
  have hx : ∀ x : V, x ∉ Neigh (deleteFinset G {v}) v := fun x hx =>
    (mem_neigh_deleteFinset' G).mp hx |>.1 rfl
  rw [Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem hx)]

/-- **THE DEGREE OF A VERTEX NEVER INCREASES WHEN A VERTEX IS DELETED.** -/
theorem card_neigh_mono_deleteFinset (G : SimpleGraph V) (v w : V) :
    (Neigh (deleteFinset G {v}) w).card ≤ (Neigh G w).card := by
  refine Finset.card_le_card ?_
  intro x hx
  exact mem_neigh.mpr ((mem_neigh_deleteFinset' G).mp hx).2.2

/-- **THE DEGREE-SUM IDENTITY OF A SINGLE DELETION.**

`degSum (G - v) + 2 * |N(v)| = degSum G`: deleting `v` and its `|N(v)|` incident edges removes
`|N(v)|` from the degree of `v` itself and one from the degree of each of its `|N(v)|` neighbours,
i.e. `2 * |N(v)|` in total.  This is the invariant of the induction below. -/
theorem degSum_deleteFinset (G : SimpleGraph V) (v : V) :
    degSum (deleteFinset G {v}) + 2 * (Neigh G v).card = degSum G := by
  have hirr : ¬ G.Adj v v := fun hh => G.irrefl hh
  -- (a) the vertex-wise difference of the two degree sums
  have hcongr : (∑ w : V, ((Neigh G w).card - (Neigh (deleteFinset G {v}) w).card))
      = ∑ w : V, (if w = v then (Neigh G v).card else (if G.Adj v w then 1 else 0) : ℕ) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hwv : w = v
    · subst w
      have hz : (Neigh (deleteFinset G {v}) v).card = 0 := card_neigh_deleteFinset_self G v
      simp [hz]
    · by_cases hadj : G.Adj v w
      · have hkey := card_neigh_deleteFinset (G := G) (v := v) (w := w) (Ne.symm hwv)
        rw [if_pos hadj] at hkey
        have hpos : 1 ≤ (Neigh G w).card := Finset.card_pos.mpr ⟨v, mem_neigh.mpr hadj.symm⟩
        simp only [if_neg hwv, if_pos hadj]
        omega
      · have hkey := card_neigh_deleteFinset (G := G) (v := v) (w := w) (Ne.symm hwv)
        rw [if_neg hadj] at hkey
        simp only [if_neg hwv, if_neg hadj]
        omega
  -- (b) the contribution of `v` itself is its whole degree
  have hone1 : (∑ w : V, (if w = v then 1 else 0 : ℕ)) = 1 := by
    rw [← Finset.card_filter,
      show ((Finset.univ : Finset V)).filter (fun w : V => w = v) = ({v} : Finset V) by
        ext x
        simp,
      Finset.card_singleton]
  have hone : (∑ w : V, (if w = v then (Neigh G v).card else 0 : ℕ)) = (Neigh G v).card := by
    calc (∑ w : V, (if w = v then (Neigh G v).card else 0 : ℕ))
        = ∑ w : V, (Neigh G v).card * (if w = v then 1 else 0) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          by_cases hwv : w = v <;> simp [hwv]
      _ = (Neigh G v).card * (∑ w : V, (if w = v then 1 else 0)) := by
        rw [Finset.mul_sum]
      _ = (Neigh G v).card * 1 := by rw [hone1]
      _ = (Neigh G v).card := by omega
  -- (c) the contribution of the neighbours of `v`, which are not `v` itself
  have htwo : (∑ w : V, (if w = v then 0 else (if G.Adj v w then 1 else 0) : ℕ))
      = (Neigh G v).card := by
    have hstep : (∑ w : V, (if w = v then 0 else (if G.Adj v w then 1 else 0) : ℕ))
        = ∑ w : V, (if G.Adj v w then 1 else 0) := by
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hwv : w = v
      · subst w
        simp
      · have hz : (if G.Adj v w then 1 else 0 : ℕ) = (if w ≠ v ∧ G.Adj v w then 1 else 0) := by
          by_cases hadj : G.Adj v w
          · rw [if_pos hadj, if_pos (And.intro hwv hadj)]
          · rw [if_neg hadj, if_neg (fun h => hadj h.2)]
        rw [if_neg hwv, hz]
    have hsumadj : (∑ w : V, (if G.Adj v w then 1 else 0 : ℕ)) = (Neigh G v).card := by
      rw [← Finset.card_filter,
        show ((Finset.univ : Finset V)).filter (fun w : V => G.Adj v w) = Neigh G v by
          ext w
          simp [Neigh]]
    rw [hstep, hsumadj]
  -- (d) assembling the two
  have hdiff : (∑ w : V, ((Neigh G w).card - (Neigh (deleteFinset G {v}) w).card))
      = 2 * (Neigh G v).card := by
    rw [hcongr]
    calc (∑ w : V, (if w = v then (Neigh G v).card else (if G.Adj v w then 1 else 0) : ℕ))
        = (∑ w : V, (if w = v then (Neigh G v).card else 0 : ℕ))
          + (∑ w : V, (if w = v then 0 else (if G.Adj v w then 1 else 0) : ℕ)) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun w _ => ?_
            by_cases hwv : w = v
            · subst w
              simp
            · simp only [if_neg hwv, Nat.zero_add]
      _ = 2 * (Neigh G v).card := by rw [hone, htwo, Nat.two_mul]
  have htot : degSum G = degSum (deleteFinset G {v}) + 2 * (Neigh G v).card := by
    unfold degSum
    calc (∑ w : V, (Neigh G w).card)
        = ∑ w : V, ((Neigh (deleteFinset G {v}) w).card
          + ((Neigh G w).card - (Neigh (deleteFinset G {v}) w).card)) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          have hle := card_neigh_mono_deleteFinset G v w
          omega
      _ = (∑ w : V, (Neigh (deleteFinset G {v}) w).card)
          + ∑ w : V, ((Neigh G w).card - (Neigh (deleteFinset G {v}) w).card) :=
        Finset.sum_add_distrib
      _ = _ + 2 * (Neigh G v).card := by rw [hdiff]
  omega

/-- **DELETING A VERTEX REMOVES EXACTLY ITS DEGREE FROM THE EDGE COUNT.** -/
theorem edgeCount_deleteFinset (G : SimpleGraph V) (v : V) :
    edgeCount (deleteFinset G {v}) = edgeCount G - (Neigh G v).card := by
  have h1 := two_mul_edgeCount G
  have h2 := two_mul_edgeCount (deleteFinset G {v})
  have h3 := degSum_deleteFinset G v
  omega

/-- **A VERTEX OF AN ODD CYCLE HAS AT LEAST TWO NEIGHBOURS** — the two cycle-neighbours.

This is the only local input of the induction below, and it is what makes a vertex of an odd cycle
a good thing to delete: it costs one vertex and removes at least two edges. -/
theorem two_le_card_neigh_of_mem_oddCycle {C : Finset V} (hC : IsOddCycle G C) {v : V} (hv : v ∈ C) :
    2 ≤ (Neigh G v).card := by
  have hCS : C ∩ (∅ : Finset V) = ∅ := Finset.inter_empty C
  have h := two_le_innerDeg_of_mem_oddCycle hC hCS hv
  have heq : InnerDeg G (∅ : Finset V) v = (Neigh G v).card := by
    show (OuterNeigh G (∅ : Finset V) v).card = _
    have : OuterNeigh G (∅ : Finset V) v = Neigh G v := by
      ext w
      simp [OuterNeigh, mem_neigh]
    rw [this]
  omega

/-- An odd cycle has at least three vertices. -/
theorem three_le_card_of_isOddCycle {C : Finset V} (hC : IsOddCycle G C) : 3 ≤ C.card := by
  obtain ⟨o, -⟩ := hC.cycleOrder
  rw [card_eq_cyclicOrder o.f o.hinj o.hmem]
  exact o.hm3

/-- **THE DEGREE SUM IS AT LEAST TWICE THE LENGTH OF AN ODD CYCLE.**  Every vertex of an odd cycle
has two neighbours on the cycle, so the cycle alone accounts for `2 * |C|` of the degree sum. -/
theorem two_mul_card_le_edgeCount_of_isOddCycle {C : Finset V} (hC : IsOddCycle G C) :
    2 * C.card ≤ 2 * edgeCount G := by
  have hsum : 2 * C.card ≤ ∑ w ∈ C, (Neigh G w).card := by
    calc 2 * C.card = C.sum (fun _ => 2) := by
          simp [Finset.sum_const, Nat.mul_comm]
      _ ≤ ∑ w ∈ C, (Neigh G w).card :=
        Finset.sum_le_sum fun w hw => two_le_card_neigh_of_mem_oddCycle hC hw
  have hsum' : (∑ w ∈ C, (Neigh G w).card) ≤ degSum G :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h1 := two_mul_edgeCount G
  omega

/-- **AN ODD CYCLE FORCES AT LEAST THREE EDGES.** -/
theorem three_le_edgeCount_of_isOddCycle {C : Finset V} (hC : IsOddCycle G C) : 3 ≤ edgeCount G := by
  have h1 := three_le_card_of_isOddCycle hC
  have h2 := two_mul_card_le_edgeCount_of_isOddCycle hC
  omega

end Counting

/-! ### Part 2 — the classical bound `τ_odd(G) ≤ ⌊ |E(G)| / 2 ⌋` -/

section Bound

variable {G : SimpleGraph V}

/-- **A transversal of the odd cycles of `G - v`, together with `v`, is a transversal of the odd
cycles of `G`.**  Every odd cycle of `G` either meets `v`, or avoids `v` — and is then an odd cycle
of `G - v`. -/
theorem HitsOddCycles.insert_v_of_deleteFinset {v : V} {X : Finset V}
    (hX : HitsOddCycles (deleteFinset G {v}) X) : HitsOddCycles G (insert v X) := by
  intro C hC hdis
  have hnotX : ∀ x : V, x ∈ C → x ∉ insert v X := by
    intro x hxC hx
    have hx' : x ∈ C ∩ insert v X := Finset.mem_inter.mpr ⟨hxC, hx⟩
    rw [hdis] at hx'
    simp at hx'
  have hCv : C ∩ ({v} : Finset V) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨hC1, hC2⟩ := Finset.mem_inter.mp hx
    have hxv : x = v := Finset.mem_singleton.mp hC2
    exact hnotX x hC1 (hxv ▸ Finset.mem_insert_self v X)
  have hCX : C ∩ X = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨hC1, hC2⟩ := Finset.mem_inter.mp hx
    exact hnotX x hC1 (Finset.mem_insert_of_mem hC2)
  have hsub : C ⊆ (Finset.univ : Finset V) \ ({v} : Finset V) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hxv
    exact absurd (Finset.mem_inter.mpr ⟨hx, hxv⟩) (by rw [hCv]; simp)
  have hC' : IsOddCycle (induceFinset G ((Finset.univ : Finset V) \ ({v} : Finset V))) C :=
    hC.induceFinset hsub
  have hC'' : IsOddCycle (deleteFinset G ({v} : Finset V)) C := by
    have heq : deleteFinset G ({v} : Finset V)
        = induceFinset G ((Finset.univ : Finset V) \ ({v} : Finset V)) := rfl
    rw [heq]
    exact hC'
  exact hX C hC'' hCX

/-- **THE CLASSICAL LOCAL BOUND: `τ_odd(G) ≤ ⌊ |E(G)| / 2 ⌋`.**

If `G` has at most `2 * m + 1` edges, deleting at most `m` vertices leaves a bipartite graph.

The proof is the classical one: delete a vertex of an odd cycle, which costs one vertex and removes
at least two edges (`edgeCount_deleteFinset`, `two_le_card_neigh_of_mem_oddCycle`). -/
theorem closeToBipartite_of_edgeCount_le (G : SimpleGraph V) (m : ℕ) :
    edgeCount G ≤ 2 * m + 1 → CloseToBipartite m G := by
  induction m generalizing G with
  | zero =>
      intro h
      have hb : G.IsBipartite := by
        by_contra hnb
        obtain ⟨C, hC⟩ : ∃ C : Finset V, IsOddCycle G C := by
          by_contra hn
          exact hnb (isBipartite_of_no_oddCycle hn)
        have h3 := three_le_edgeCount_of_isOddCycle hC
        omega
      exact closeToBipartite_of_isBipartite' hb
  | succ m ih =>
      intro h
      by_cases hb : G.IsBipartite
      · exact closeToBipartite_of_isBipartite' hb
      · obtain ⟨C, hC⟩ : ∃ C : Finset V, IsOddCycle G C := by
          by_contra hn
          exact hb (isBipartite_of_no_oddCycle hn)
        obtain ⟨v, hv⟩ := hC.nonempty
        have hle : edgeCount (deleteFinset G {v}) ≤ 2 * m + 1 := by
          have he := edgeCount_deleteFinset G v
          have h2 := two_le_card_neigh_of_mem_oddCycle hC hv
          omega
        obtain ⟨X, hXcard, hXhits⟩ :=
          (closeToBipartite_iff_hitsOddCycles (m := m)).mp (ih (deleteFinset G {v}) hle)
        refine (closeToBipartite_iff_hitsOddCycles (m := m + 1)).mpr
          ⟨insert v X, ?_, hXhits.insert_v_of_deleteFinset⟩
        by_cases hvX : v ∈ X
        · rw [Finset.card_insert_of_mem hvX]; omega
        · rw [Finset.card_insert_of_notMem hvX]; omega

/-- **THE DEGREE-SUM FORM OF THE SAME BOUND**, `degSum G ≤ 4 * m + 2` ⟹ `CloseToBipartite m G`,
which needs no `edgeFinset` at all. -/
theorem closeToBipartite_of_degSum_le (G : SimpleGraph V) (m : ℕ)
    (h : degSum G ≤ 4 * m + 2) : CloseToBipartite m G := by
  refine closeToBipartite_of_edgeCount_le G m ?_
  have h2 := two_mul_edgeCount G
  omega

end Bound

/-! ### Part 3 — new instances of the headline theorem -/

section Instances

universe u

variable {G : SimpleGraph V}

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM: THE CLASS OF GRAPHS WITH A BOUNDED NUMBER OF EDGES.**

`LocIndep k G` and `|E(G)| ≤ 2 * m + 1` force `CloseToBipartite m G` — with a constant that does
not mention `k`, because **the local hypothesis of Erdős's problem is not used at all**: the bound
is the classical local statement `τ_odd(G) ≤ ⌊ |E(G)| / 2 ⌋`, which holds for every graph. -/
theorem erdos73On_of_edgeCount (k m : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
      LocIndep k G → edgeCount G ≤ 2 * m + 1 → CloseToBipartite m G :=
  fun W instW G _ h => closeToBipartite_of_edgeCount_le G m h

/-- **THE EDGE COUNT IS BOUNDED BY THE ORDER AND THE DEGREE**: `|E(G)| ≤ ⌈ |V(G)| * Δ(G) / 2 ⌉`. -/
theorem edgeCount_le_card_mul_maxDeg {d : ℕ} (hdeg : MaxDegLe G d) :
    edgeCount G ≤ (Fintype.card V * d) / 2 := by
  have hsum : degSum G = ∑ v : V, (MaxDeg G v : ℕ) := rfl
  have hsum' : (∑ v : V, (MaxDeg G v : ℕ)) ≤ (∑ v : V, (d : ℕ)) :=
    Finset.sum_le_sum fun v _ => hdeg v
  have hsum'' : (∑ v : V, (d : ℕ)) = Fintype.card V * d := by simp
  have h1 := two_mul_edgeCount G
  omega

/-- **THE ORDER-DEPENDENT INSTANCE OF THE HEADLINE THEOREM: `τ_odd(G) ≤ ⌈ |V(G)| * Δ(G) / 2 ⌉`.**

Every vertex has at most `d` neighbours and there are at most `n` vertices, so the graph has at
most `n * d / 2` edges and `JSP90.closeToBipartite_of_edgeCount_le` applies.  The constant depends
on the *order* and the *degree*, not on `k`; it is the classical `τ ≤ |V| * Δ / 4` statement, and it
is **not** a value of `f(k)`. -/
theorem closeToBipartite_of_maxDegLe_of_card_le {d n : ℕ} (hdeg : MaxDegLe G d)
    (hn : Fintype.card V ≤ n) : CloseToBipartite ((n * d + 1) / 2) G := by
  refine closeToBipartite_of_edgeCount_le G _ ?_
  have h1 := edgeCount_le_card_mul_maxDeg hdeg
  have h2 : Fintype.card V * d ≤ n * d := Nat.mul_le_mul_right d hn
  have h3 : n * d ≤ 2 * ((n * d + 1) / 2) + 1 := by
    have h4 := Nat.div_add_mod (n * d + 1) 2
    omega
  omega

/-- The same statement in the form of an instance of Erdős #73. -/
theorem erdos73On_of_maxDegLe_of_card_le (k d n : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → MaxDegLe G d →
      Fintype.card W ≤ n → CloseToBipartite ((n * d + 1) / 2) G :=
  fun W instW G _ hdeg hn => closeToBipartite_of_maxDegLe_of_card_le hdeg hn

end Instances

/-! ### Part 4 — sharpness of the constant -/

section Sharp

variable {G : SimpleGraph V}

/-- **EVERY VERTEX OF `K_3` HAS TWO NEIGHBOURS.** -/
theorem card_neigh_completeGraph_three (v : Fin 3) :
    (Neigh (SimpleGraph.completeGraph (Fin 3)) v).card = 2 := by
  have heq : Neigh (SimpleGraph.completeGraph (Fin 3)) v
      = (Finset.univ : Finset (Fin 3)).erase v := by
    ext w
    constructor
    · intro h
      exact Finset.mem_erase.mpr ⟨fun e => (mem_neigh.mp h) e.symm, Finset.mem_univ _⟩
    · intro h
      obtain ⟨h1, -⟩ := Finset.mem_erase.mp h
      exact mem_neigh.mpr (show v ≠ w from fun e => h1 e.symm)
  rw [heq]
  have hmem : v ∈ (Finset.univ : Finset (Fin 3)) := Finset.mem_univ v
  rw [Finset.card_erase_of_mem hmem]
  simp

/-- **`K_3` HAS THREE EDGES** — `⌊ |E| / 2 ⌋ = 1`, the least non-vacuous case of the bound. -/
theorem edgeCount_completeGraph_three : edgeCount (SimpleGraph.completeGraph (Fin 3)) = 3 := by
  have h1 : (∑ v : Fin 3, (Neigh (SimpleGraph.completeGraph (Fin 3)) v).card)
      = ∑ _v : Fin 3, (2 : ℕ) :=
    Finset.sum_congr rfl fun v _ => card_neigh_completeGraph_three v
  have hdeg : degSum (SimpleGraph.completeGraph (Fin 3)) = 6 := by
    show (∑ v : Fin 3, (Neigh (SimpleGraph.completeGraph (Fin 3)) v).card) = 6
    rw [h1]
    simp [Finset.sum_const]
  have h2 := two_mul_edgeCount (SimpleGraph.completeGraph (Fin 3))
  omega

/-- **THE CONSTANT `⌊ |E| / 2 ⌋` IS ATTAINED AND CANNOT BE IMPROVED.**

`K_3` has three edges (`edgeCount_completeGraph_three`) and its odd cycle transversal number is
exactly `1 = ⌊ 3 / 2 ⌋`, so no budget below `⌊ |E(G)| / 2 ⌋` works in general — the bound of
`JSP90.closeToBipartite_of_edgeCount_le` is sharp at the first graph where it is not vacuous. -/
theorem edgeCount_bound_tight_completeGraph_three (m : ℕ)
    (hm : CloseToBipartite m (SimpleGraph.completeGraph (Fin 3))) : 1 ≤ m := by
  by_cases hm0 : CloseToBipartite 0 (SimpleGraph.completeGraph (Fin 3))
  · exact absurd hm0 not_closeToBipartite_zero_completeGraph_three
  · have h1 := (closeToBipartite_iff_completeGraph_add_two m 3).mp hm
    omega

/-- **THE EDGE COUNT OF THE DISJOINT UNION OF `k` TRIANGLES, THROUGH THE DEGREE BOUND.**

`JSP90.closeToBipartite_of_maxDegLe_of_card_le` gives `⌈ 3 k / 2 ⌉` on `kTriangles k`, where the
exact answer is `k` (`JSPProblem/Sharp.lean`): the edge-counting bound is a genuine bound but a
loose one in the direction of the deficiency. -/
theorem closeToBipartite_kTriangles_of_edgeCount (k : ℕ) :
    CloseToBipartite ((3 * k * 2 + 1) / 2) (kTriangles k) := by
  have hne : ∀ v : Fin 3 × Fin k, Neigh (kTriangles k) v = (tri v.2).erase v := by
    intro v
    ext w
    constructor
    · intro h
      rw [mem_neigh, kTriangles_adj] at h
      refine Finset.mem_erase.mpr ⟨?_, mem_tri.mpr h.1.symm⟩
      intro hcon
      subst hcon
      exact h.2 rfl
    · intro h
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp h
      rw [mem_neigh]
      refine kTriangles_adj.mpr ⟨mem_tri.mp hmem |>.symm, ?_⟩
      intro hcon
      exact hne (Prod.ext hcon.symm (mem_tri.mp hmem))
  have hdeg : MaxDegLe (kTriangles k) 2 := by
    intro v
    show (Neigh (kTriangles k) v).card ≤ 2
    rw [hne v, Finset.card_erase_of_mem (mem_tri.mpr (rfl : v.2 = v.2)), card_tri v.2]
  have hcard : Fintype.card (Fin 3 × Fin k) ≤ 3 * k := by
    simp [Fintype.card_prod]
  exact closeToBipartite_of_maxDegLe_of_card_le (V := Fin 3 × Fin k) (G := kTriangles k)
    (n := 3 * k) hdeg hcard

end Sharp

/-! ### Part 5 — what this axis cannot do, and the statement it leaves behind -/

section Limit

variable {G : SimpleGraph V}

/-- **Erdős's local hypothesis at `k = 0` IS bipartiteness**, so the class of graphs allowed by
`LocIndep 0` is exactly the class of bipartite graphs.  This is why the constant of
`JSP90.erdos73On_of_edgeCount` is not a function of `k`: the number of edges is not controlled by
the hypothesis of JSP-000090 (bipartite graphs have arbitrarily many edges), and this file's
instance is the *local* counterpart of the theorem rather than an instance of it. -/
theorem locIndep_zero_of_isBipartite (h : G.IsBipartite) : LocIndep 0 G :=
  locIndep_of_maxDef_le (by rw [maxDef_eq_zero_iff.mpr h])

/-- **NO FUNCTION OF `k` BOUNDS THE NUMBER OF EDGES UNDER `LocIndep k`.**

**Stated, not assumed.**  `LocIndep 0` holds exactly for the bipartite graphs
(`locIndep_zero_of_isBipartite` above together with `maxDef_le_of_locIndep` applied to `k = 0`),
and bipartite graphs have arbitrarily many edges, so no `f(k)` makes the hypothesis of
`JSP90.erdos73On_of_edgeCount` automatic.  This is the precise reason the edge-counting axis
delivers the classical *local* bound `τ_odd(G) ≤ ⌊ |E(G)| / 2 ⌋` and no value of `f(k)`. -/
def LocIndepEdgeUnbounded : Prop :=
  ∀ k : ℕ, ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W),
    LocIndep k G ∧ ∀ m : ℕ, m < edgeCount G

/-- **THE REMAINING STATEMENT OF THE EDGE-COUNTING AXIS.**

A graph of odd girth `ℓ` in which every vertex has at most `d` neighbours should be `f ℓ d`-close
to bipartite, with `f` a function of the odd girth and the degree **alone** — no packing number,
no transversal, no cut.  This is the natural next step of this axis: the induction above pays for a
vertex of degree at least `2` and says nothing about the higher degrees that a shortest odd cycle
would have to exhibit for a degree/odd-girth bound to follow.

**Stated, not assumed**, and nothing in this file proves it. -/
def BoundedOddGirthEdgeCount : Prop :=
  ∀ ℓ d : ℕ, ∃ f : ℕ, ∀ (W : Type) (_ : Fintype W) (G : SimpleGraph W),
    (∀ C : Finset W, IsOddCycle G C → ℓ ≤ C.card) → MaxDegLe G d → CloseToBipartite f G

end Limit

end

end JSP90
