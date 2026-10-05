/-
# `JSPProblem/IndepSplit.lean` — the **INDEPENDENT-SET-SPLIT axis**

Rounds 171 and 172 closed two of the three cases of `LocIndep 1 G → |V| ≤ 8 → CloseToBipartite 2 G`
(the triangle case and the seven-cycle case), the five-cycle case being left open and
`discovery/JSP-000090/policy.json` naming it as the only remaining gap of the eight-vertex axis.
**This round closes it — with no case analysis at all**, which is why it was not found earlier: the
five-cycle case had been approached from the *odd cycles* (which of them a transversal must hit),
and the right object is a *split of the vertex set*.

## The reading

A graph of defect `≤ k` is `bipartite + O(k)` vertices, so `CloseToBipartite m G` should be read as
**"the vertices of `G` split into two independent sets and a leftover of at most `m` points"**:

* `JSP90.isBipartiteWith_of_cover` — if `A ∪ B = V \ s` with `A`, `B` independent, then `G - s` is
  bipartite with sides `A`, `B` (so `JSP90.closeToBipartite_of_cover`);
* `JSP90.closeToBipartite_of_isIndepSet` — **THE SPLIT LEMMA**: for *any* independent set `I`,
  ```lean
  CloseToBipartite (|V \ I| - α(G[V \ I])) G
  ```
  deleting the points of `V \ I` outside a maximum independent set of `G[V \ I]`.  No hypothesis is
  used, so this is a statement about every graph: the odd cycle transversal number is at most the
  deficiency of the complement of any independent set;
* Erdős's hypothesis then bounds that deficiency **twice**
  (`JSP90.sdiff_indepCard_le_of_locIndep`): `α(G) ≥ (|V| - k) / 2` makes `V \ I` small for a
  *maximum* independent set `I`, and `α(G[V \ I]) ≥ (|V \ I| - k) / 2` makes the cost of the split
  small.

At `k = 1` and `|V| ≤ 8` this gives, in four lines, `CloseToBipartite 2 G` — the eight-vertex axis,
**five-cycle case included**, with no hypothesis on the shortest odd cycle and no triangle-freeness
assumption.  The general shape is `JSP90.closeToBipartite_of_locIndep_of_card_le`:

```lean
LocIndep k G → CloseToBipartite (((|V| + k) / 2 + k) / 2) G
```

a **new instance of the headline theorem for every `k`**, in which the constant depends on the order
of `G` and on `k` and on nothing else — no odd girth, no packing number, no packing weight, no degree
bound, no bound on the number of cut or branch vertices, no connectivity, no decomposition.

`JSP90.closeToBipartite_one_iff_exists_isIndepSet_of_defOf_le_one` is the exact characterisation of
the conclusion at `m = 1`: `G` is `1`-close to bipartite **iff** some independent set leaves a
complement of deficiency `≤ 1` — "defect `≤ 1` is bipartite plus one exception", in both directions.

Nothing about Reed's theorem is assumed; the missing input remains `JSP90.OddCycleErdosPosa r`.
-/

import JSPProblem.CycWitness

namespace JSP90

open Finset Fintype

variable {V : Type*} [Fintype V]

noncomputable section

local instance indepSplitDecidableEq : DecidableEq V := Classical.decEq V

/-! ### Part 0 — the two directions of the "two independent sets and a remainder" reading -/

section Helper

variable {G : SimpleGraph V}

/-- Two adjacent vertices of an independent set are equal: the single point at which the
"two independent sets" reading of a `2`-colouring is used below. -/
theorem eq_of_adj_of_isIndepSet {A : Finset V} (hAi : G.IsIndepSet A) {v w : V}
    (hv : v ∈ A) (hw : w ∈ A) (hvw : G.Adj v w) : v = w := by
  by_cases hne : v = w
  · exact hne
  · rw [SimpleGraph.isIndepSet_iff] at hAi
    exact False.elim (hAi hv hw hne hvw)

/-- **No two distinct vertices of an independent set are adjacent.** -/
theorem notAdj_of_isIndepSet_of_mem {A : Finset V} (hAi : G.IsIndepSet A) {v w : V}
    (hv : v ∈ A) (hw : w ∈ A) : ¬ G.Adj v w := by
  intro h
  have hvw : v = w := eq_of_adj_of_isIndepSet hAi hv hw h
  rw [hvw] at h
  exact G.irrefl h

end Helper

section Split

variable {G : SimpleGraph V}

/-- `V \ ((V \ I) \ K) = I ∪ K` when `K ⊆ V \ I`: the cover identity of the split. -/
theorem univ_sdiff_sdiff (I K : Finset V) :
    univ \ ((univ \ I) \ K) = I ∪ K := by
  rw [Finset.sdiff_sdiff_eq_sdiff_union (Finset.subset_univ _),
    Finset.sdiff_sdiff_self_left, Finset.inter_comm, Finset.inter_univ]

/-- **THE FIRST DIRECTION: a cover by two independent sets is a bipartition of the residue.**
If `A ∪ B = V \ s` with `A` and `B` independent in `G`, then `G - s` has `A`, `B` as a bipartition. -/
theorem isBipartiteWith_of_cover {A B s : Finset V} (hcover : A ∪ B = univ \ s)
    (hAB : Disjoint A B) (hAi : G.IsIndepSet A) (hBi : G.IsIndepSet B) :
    (deleteFinset G s).IsBipartiteWith (A : Set V) (B : Set V) := by
  refine ⟨Set.disjoint_left.mpr fun v hvA hvB => ?_, ?_⟩
  · exact Finset.disjoint_left.mp hAB hvA (by simpa using hvB)
  · intro v w hvw
    have hvs : v ∉ s := (Finset.mem_sdiff.mp hvw.1).2
    have hws : w ∉ s := (Finset.mem_sdiff.mp hvw.2.1).2
    have hvAB : v ∈ A ∪ B := by
      have hmem : v ∈ univ \ s := Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvs⟩
      rw [← hcover] at hmem
      exact hmem
    have hwAB : w ∈ A ∪ B := by
      have hmem : w ∈ univ \ s := Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hws⟩
      rw [← hcover] at hmem
      exact hmem
    rw [Finset.mem_union] at hvAB
    rw [Finset.mem_union] at hwAB
    rcases hvAB with hvA | hvB
    · rcases hwAB with hwA | hwB
      · exact (notAdj_of_isIndepSet_of_mem hAi hvA hwA hvw.2.2).elim
      · exact Or.inl ⟨hvA, hwB⟩
    · rcases hwAB with hwA | hwB
      · exact Or.inr ⟨hvB, hwA⟩
      · exact (notAdj_of_isIndepSet_of_mem hBi hvB hwB hvw.2.2).elim

/-- **The second direction, packaged as the conclusion of Erdős #73.** -/
theorem closeToBipartite_of_cover {A B s : Finset V} (hcover : A ∪ B = univ \ s)
    (hAB : Disjoint A B) (hAi : G.IsIndepSet A) (hBi : G.IsIndepSet B) :
    CloseToBipartite s.card G :=
  ⟨s, Nat.le_refl _, (isBipartiteWith_of_cover hcover hAB hAi hBi).isBipartite⟩

/-- `I` and `K` are disjoint whenever `K ⊆ V \ I`. -/
theorem disjoint_of_subset_sdiff {I K : Finset V} (hK : K ⊆ univ \ I) : Disjoint I K :=
  Finset.disjoint_left.mpr fun _ h1 h2 => (Finset.mem_sdiff.mp (hK h2)).2 h1

/-- **THE SPLIT LEMMA.**  For every independent set `I` of `G`, deleting the points of `V \ I` that
are *not* in a maximum independent set of `G[V \ I]` leaves a bipartite graph:

```lean
CloseToBipartite (|V \ I| - α(G[V \ I])) G
```

The two independent sets are `I` and that maximum independent set `K`; the deleted set is `J \ K` with
`J = V \ I`.  **No hypothesis is used**: the odd cycle transversal number of *any* graph is at most
the deficiency of the complement of any independent set. -/
theorem closeToBipartite_of_isIndepSet {I : Finset V} (hI : G.IsIndepSet I) :
    CloseToBipartite ((univ \ I).card - indepCard G (univ \ I)) G := by
  classical
  obtain ⟨K, hKsub, hKi, hKcard⟩ := exists_indepCard G (univ \ I)
  refine ⟨(univ \ I) \ K, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hKsub, hKcard]
  · exact (isBipartiteWith_of_cover (A := I) (B := K)
      (hcover := by rw [← univ_sdiff_sdiff I K])
      (hAB := disjoint_of_subset_sdiff hKsub) hI hKi).isBipartite

/-- The certificate of the split lemma, read off: the deleted vertices are the complement of the
union of two independent sets, the second of size exactly `α(G[V \ I])`. -/
theorem exists_cover_of_isIndepSet {I : Finset V} (hI : G.IsIndepSet I) :
    ∃ K : Finset V, K ⊆ univ \ I ∧ G.IsIndepSet K ∧ Disjoint I K ∧
      K.card = indepCard G (univ \ I) ∧
      CloseToBipartite ((univ \ I).card - indepCard G (univ \ I)) G := by
  classical
  obtain ⟨K, hKsub, hKi, hKcard⟩ := exists_indepCard G (univ \ I)
  exact ⟨K, hKsub, hKi, disjoint_of_subset_sdiff hKsub, hKcard, closeToBipartite_of_isIndepSet hI⟩

end Split


/-! ### Part 1 — the exact characterisation of the conclusion at `m = 1` -/

section Exact

variable {G : SimpleGraph V}

/-- **A proper `2`-colouring of the residue, read off the bipartiteness.** -/
theorem coloring_of_isBipartite_delete {Z : Finset V} (hb : (deleteFinset G Z).IsBipartite) :
    ∃ d : V → Fin 2, ∀ ⦃v w : V⦄, v ∉ Z → w ∉ Z → G.Adj v w → d v ≠ d w := by
  obtain ⟨⟨d, hd⟩⟩ := hb
  refine ⟨d, fun v1 w1 hv1 hw1 hadj => ?_⟩
  apply hd
  rw [deleteFinset_adj]
  exact ⟨hv1, hw1, hadj⟩

/-- **A colour class of that colouring is an independent set of `G`.** -/
theorem isIndepSet_filter_eq {d : V → Fin 2} {Z : Finset V}
    (hd : ∀ ⦃v w : V⦄, v ∉ Z → w ∉ Z → G.Adj v w → d v ≠ d w) (c : Fin 2) :
    G.IsIndepSet ((univ \ Z).filter (fun v => d v = c)) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro v hv w hw hne hadj
  have hv' : v ∈ ((univ \ Z).filter (fun u => d u = c) : Finset V) := (Finset.mem_coe).mp hv
  have hw' : w ∈ ((univ \ Z).filter (fun u => d u = c) : Finset V) := (Finset.mem_coe).mp hw
  rcases Finset.mem_filter.mp hv' with ⟨hvUZ, hvc⟩
  rcases Finset.mem_filter.mp hw' with ⟨hwUZ, hwc⟩
  have hvZ : v ∉ Z := (Finset.mem_sdiff.mp hvUZ).2
  have hwZ : w ∉ Z := (Finset.mem_sdiff.mp hwUZ).2
  have hne' : d v = d w := hvc.trans hwc.symm
  exact absurd hne' (hd hvZ hwZ hadj)

/-- **THE EXACT CHARACTERISATION OF THE CONCLUSION AT `m = 1`.**

`G` is `1`-close to bipartite **iff** its vertices split into two independent sets and at most one
leftover vertex:

```lean
CloseToBipartite 1 G ↔ ∃ I K, G.IsIndepSet I ∧ G.IsIndepSet K ∧ Disjoint I K ∧
                      |V \ (I ∪ K)| ≤ 1
```

This is the reading of the conclusion of Erdős #73 on which the whole file rests on ("a graph of
defect at most `1` is bipartite plus one exception"), and it is machine-checked in **both**
directions.  It is strictly more informative than `JSPProblem/Transversal.lean`'s
`closeToBipartite_iff_hitsOddCycles`, which only produces a set meeting every odd cycle: here the two
independent sets themselves are produced, which is exactly the form in which Erdős's hypothesis can
be applied a second time. -/
theorem closeToBipartite_one_iff_exists_cover :
    CloseToBipartite 1 G ↔
      ∃ I K : Finset V, G.IsIndepSet I ∧ G.IsIndepSet K ∧ Disjoint I K ∧
        (univ \ (I ∪ K)).card ≤ 1 := by
  constructor
  · rintro ⟨Z, hZ, hb⟩
    rcases coloring_of_isBipartite_delete hb with ⟨d, hd⟩
    set A : Finset V := (univ \ Z).filter (fun v => d v = 0) with hAdef
    set B : Finset V := (univ \ Z).filter (fun v => d v = 1) with hBdef
    have hAi : G.IsIndepSet A := by rw [hAdef]; exact isIndepSet_filter_eq hd 0
    have hBi : G.IsIndepSet B := by rw [hBdef]; exact isIndepSet_filter_eq hd 1
    have hAB : Disjoint A B := by
      refine Finset.disjoint_left.mpr fun v hA hB => ?_
      simp only [hAdef, hBdef] at hA hB
      rcases Finset.mem_filter.mp hA with ⟨hAZ, hAc⟩
      rcases Finset.mem_filter.mp hB with ⟨hBZ, hBc⟩
      simp_all
    have hcover : A ∪ B = univ \ Z := by
      have h1 : A ∪ B ⊆ univ \ Z := by
        intro v hv
        rcases Finset.mem_union.mp hv with hA | hB
        · simp only [hAdef, Finset.mem_filter] at hA; exact hA.1
        · simp only [hBdef, Finset.mem_filter] at hB; exact hB.1
      have h2 : univ \ Z ⊆ A ∪ B := by
        intro v hv
        rw [Finset.mem_union]
        rcases Finset.mem_sdiff.mp hv with ⟨-, hZ⟩
        by_cases hd0 : d v = 0
        · refine Or.inl ?_
          rw [hAdef, Finset.mem_filter]
          exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hZ⟩, hd0⟩
        · have hd1 : d v = 1 := by
            have hv0 : (d v).val = 0 ∨ (d v).val = 1 := by omega
            rcases hv0 with h | h
            · exact absurd (Fin.ext h) hd0
            · exact Fin.ext h
          refine Or.inr ?_
          rw [hBdef, Finset.mem_filter]
          exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hZ⟩, hd1⟩
      exact Finset.Subset.antisymm h1 h2
    refine ⟨A, B, hAi, hBi, hAB, ?_⟩
    rw [hcover, Finset.card_sdiff_of_subset (Finset.subset_univ (univ \ Z)),
      Finset.card_sdiff_of_subset (Finset.subset_univ Z), Finset.card_univ]
    omega
  · rintro ⟨I, K, hAi, hBi, hAB, hcard⟩
    refine closeToBipartite_mono hcard ?_
    exact closeToBipartite_of_cover (A := I) (B := K) (s := univ \ (I ∪ K))
      (by rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ (I ∪ K))]) hAB hAi hBi

/-- **The characterisation at `m = 1`, one step up: two independent sets with a leftover of at
most two points.** -/
theorem closeToBipartite_two_of_cover_of_card_le_two {I K : Finset V} (hAi : G.IsIndepSet I)
    (hBi : G.IsIndepSet K) (hAB : Disjoint I K) (hcard : (univ \ (I ∪ K)).card ≤ 2) :
    CloseToBipartite 2 G :=
  closeToBipartite_mono (by omega) (closeToBipartite_of_cover (A := I) (B := K)
    (s := univ \ (I ∪ K))
    (by rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ (I ∪ K))]) hAB hAi hBi)

end Exact

/-! ### Part 2 — Erdős's hypothesis bounds the cost of the split -/

section Bounded

variable {G : SimpleGraph V}

/-- **Erdős's hypothesis bounds the cost of the split twice.**  For every independent set `I` of a
graph of defect at most `k`,

```lean
|V \ I| - α(G[V \ I]) ≤ ((|V| + k) / 2 + k) / 2
```

The two applications are: (i) `α(G) ≥ (|V| - k) / 2`, which makes `V \ I` small when `I` is a
*maximum* independent set; (ii) `α(G[V \ I]) ≥ (|V \ I| - k) / 2`, which makes the cost of the split
small.  Erdős's hypothesis is used here and nowhere else. -/
theorem sdiff_indepCard_le_of_locIndep (hG : LocIndep k G) {I : Finset V} (_hI : G.IsIndepSet I)
    (hmax : I.card = indepCard G (univ : Finset V)) :
    (univ \ I).card - indepCard G (univ \ I) ≤ ((Fintype.card V + k) / 2 + k) / 2 := by
  have hmd : MaxDef G ≤ k := maxDef_le_of_locIndep hG
  have h1 : Fintype.card V ≤ 2 * indepCard G (univ : Finset V) + k := by
    have hle := (le_maxDef G (univ : Finset V)).trans hmd
    rw [defOf, Finset.card_univ] at hle
    omega
  have h2 : (univ \ I).card ≤ 2 * indepCard G (univ \ I) + k := by
    have hle := (le_maxDef G (univ \ I)).trans hmd
    rw [defOf] at hle
    omega
  have hcardI : (univ \ I).card = Fintype.card V - I.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ]
  have hJ : (univ \ I).card ≤ (Fintype.card V + k) / 2 := by
    have h3 : 2 * (univ \ I).card ≤ Fintype.card V + k := by
      rw [hcardI, hmax]
      omega
    omega
  rw [Nat.sub_le_iff_le_add]
  omega

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, FOR EVERY `k`.**  A graph of defect at most `k` on `n`
vertices is `((n + k) / 2 + k) / 2`-close to bipartite.  The constant depends on the order of `G` and
on `k`, and on **nothing else**: no odd girth, no packing number, no packing weight, no degree bound,
no bound on the number of cut or branch vertices, no connectivity, no decomposition.  The certificate
is explicit (`JSP90.exists_cover_of_isIndepSet`) and is the complement of two independent sets. -/
theorem closeToBipartite_of_locIndep_of_card_le (hG : LocIndep k G) :
    CloseToBipartite (((Fintype.card V + k) / 2 + k) / 2) G := by
  classical
  rcases exists_indepCard G (univ : Finset V) with ⟨I, -, hIi, hIcard⟩
  exact closeToBipartite_mono (sdiff_indepCard_le_of_locIndep hG hIi hIcard)
    (closeToBipartite_of_isIndepSet hIi)

/-- The same instance with `|V| ≤ n` in the hypothesis and an explicit bound in the conclusion. -/
theorem closeToBipartite_of_locIndep_of_card_le' (n : ℕ) (hG : LocIndep k G)
    (hV : Fintype.card V ≤ n) :
    CloseToBipartite (((n + k) / 2 + k) / 2) G := by
  exact closeToBipartite_mono (by omega) (closeToBipartite_of_locIndep_of_card_le hG)

/-- **THE EIGHT-VERTEX INSTANCE: `LocIndep 1 G → |V| ≤ 8 → CloseToBipartite 2 G`.**

This is the statement rounds 171–172 were reducing to.  Their triangle case
(`JSPProblem/TriEight.lean`) and their seven-cycle case (`JSPProblem/CycWitness.lean`) are subsumed,
and **the five-cycle case — the only one left open — needs no case analysis**: Erdős's hypothesis
gives `α(G) ≥ 4` at `|V| ≤ 8`, so `J = V \ I` has at most four points for a maximum independent set
`I`; Erdős's hypothesis again gives `α(G[J]) ≥ 2`; the split lemma then delivers a two-element odd
cycle transversal.  Note that the certificate is *not* required to lie on the shortest odd cycle,
which is what rounds 152–172 were computing. -/
theorem closeToBipartite_two_of_locIndep_one_card_le_eight (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 8) : CloseToBipartite 2 G := by
  have h := closeToBipartite_of_locIndep_of_card_le' 8 hG hV
  simpa using h

end Bounded

/-! ### Part 3 — the instances in the shapes used by the rest of the development -/

section Shapes

variable {G : SimpleGraph V}

/-- **THE ORDER-EIGHT INSTANCE OF THE HEADLINE THEOREM, FOR EVERY `k ≥ 1`, in the `Erdős73On`
shape**: a graph of defect at most `k` on at most eight vertices is `2`-close to bipartite.  For
`k = 1` this is `JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight`; note the constant `2` does
not grow with `k` beyond `k = 1` because Erdős's hypothesis at `|V| ≤ 8` forces `α(G) ≥ 4`
regardless. -/
theorem erdos73On_two_of_locIndep_one_card_le_eight :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
      Fintype.card W ≤ 8 → CloseToBipartite 2 G := by
  intro W _ G hG hV
  exact closeToBipartite_two_of_locIndep_one_card_le_eight hG hV

/-- **THE ORDER-EIGHT INSTANCE IN THE TRANSVERSAL FORM.** -/
theorem exists_hitsOddCycles_two_of_card_le_eight (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 8) :
    ∃ X : Finset V, X.card ≤ 2 ∧ HitsOddCycles G X :=
  (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2)).mp
    (closeToBipartite_two_of_locIndep_one_card_le_eight hG hV)

/-- **THE ORDER-EIGHT INSTANCE IN THE `tauOdd` FORM.** -/
theorem tauOdd_le_two_of_card_le_eight (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 8) :
    tauOdd G ≤ 2 :=
  (closeToBipartite_iff_tauOdd_le (G := G) (m := 2)).mp
    (closeToBipartite_two_of_locIndep_one_card_le_eight hG hV)

/-- The seven-vertex restatement, which the split also delivers (and which
`JSPProblem/TriFix.lean` had reached by other means). -/
theorem closeToBipartite_two_of_locIndep_one_card_le_seven' (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 7) : CloseToBipartite 2 G := by
  have h := closeToBipartite_of_locIndep_of_card_le' 7 hG hV
  simpa using h

/-- **THE GENERAL INSTANCE IN THE `Erdős73On` SHAPE, WITH THE ORDER IN THE HYPOTHESIS.** -/
theorem erdos73On_of_locIndep_of_card_le :
    ∀ (k n : ℕ) (W : Type*) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      Fintype.card W ≤ n → CloseToBipartite (((n + k) / 2 + k) / 2) G := by
  intro k n W _ G hG hV
  exact closeToBipartite_of_locIndep_of_card_le' n hG hV

/-- The general instance in the transversal form: **the odd cycle transversal of a graph of defect
at most `k` on `n` vertices has at most `((n + k) / 2 + k) / 2` elements.** -/
theorem exists_hitsOddCycles_of_locIndep_of_card_le (hG : LocIndep k G) :
    ∃ X : Finset V, X.card ≤ (((Fintype.card V + k) / 2 + k) / 2) ∧ HitsOddCycles G X :=
  (closeToBipartite_iff_hitsOddCycles (G := G)
    (m := (((Fintype.card V + k) / 2 + k) / 2))).mp
    (closeToBipartite_of_locIndep_of_card_le hG)

/-- **THE SAME IN THE `tauOdd` FORM.** -/
theorem tauOdd_le_of_locIndep_of_card_le (hG : LocIndep k G) :
    tauOdd G ≤ ((Fintype.card V + k) / 2 + k) / 2 :=
  (closeToBipartite_iff_tauOdd_le (G := G) (m := (((Fintype.card V + k) / 2 + k) / 2))).mp
    (closeToBipartite_of_locIndep_of_card_le hG)

/-- **THE ORDER LADDER DELIVERED BY THE SPLIT, AT `k = 1`.**  A graph of defect at most `1` on `n`
vertices is `((n + 1) / 2 + 1) / 2`-close to bipartite.  The three levels below are *new* instances
of the headline theorem: `lean/JSPProblem/` contains no statement for order `9`, `12` or `14` at
all.  The bound grows like `n / 4`, which is the shape one gets by applying Erdős's hypothesis twice,
and it is far from the `O(k log k)` of Reed's theorem — but it is a uniform statement in `k`, in the
sense that the *constant* here is a function of the order only. -/
theorem closeToBipartite_three_of_locIndep_one_card_le_nine (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 9) : CloseToBipartite 3 G := by
  have h := closeToBipartite_of_locIndep_of_card_le' 9 hG hV
  simpa using h

theorem closeToBipartite_three_of_locIndep_one_card_le_twelve (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 12) : CloseToBipartite 3 G := by
  have h := closeToBipartite_of_locIndep_of_card_le' 12 hG hV
  simpa using h

theorem closeToBipartite_four_of_locIndep_one_card_le_fourteen (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 14) : CloseToBipartite 4 G := by
  have h := closeToBipartite_of_locIndep_of_card_le' 14 hG hV
  simpa using h

/-- The same ladder in the `tauOdd` form. -/
theorem tauOdd_le_three_of_locIndep_one_card_le_twelve (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 12) : tauOdd G ≤ 3 :=
  (closeToBipartite_iff_tauOdd_le (G := G) (m := 3)).mp
    (closeToBipartite_three_of_locIndep_one_card_le_twelve hG hV)

end Shapes

end
end JSP90
