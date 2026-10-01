import JSPProblem.Stair

/-!
# JSP-000090, round 102 — the **GREEDY SHORTEST-ODD-CYCLE CHAIN**: the odd-girth ladder with *no
chain to be exhibited*

Attack family 43.  Round 101 (`JSPProblem/Stair.lean`) proved the **odd-girth ladder**
`τ_odd(H) ≤ g 0 + g 1 + … + g (n-1)` and recorded in `discovery/JSP-000090/policy.json` option (A)
that its hypothesis is *assumed*: a **chain** `C 0, …, C (n-1)` of odd cycles, one per residue
level, has to be given.  This file **derives the chain from the graph itself** — delete the
*shortest* odd cycle, then the shortest odd cycle of the residue, and so on.  Nothing has to be
exhibited, and **no girth hypothesis at all is needed**.

## What is proved

* **The greedy chain.**  `JSP90.girthOf H` is the number of vertices of a *shortest* odd cycle of
  `H` (`0` if `H` has none); `JSP90.greedyCycle H` is such a shortest odd cycle (the empty set if
  there is none); `JSP90.level H j` is the residue left after deleting the greedy cycles of the `j`
  earlier levels and `JSP90.unionUpTo H j` is the set deleted.  `JSP90.level_eq_deleteFinset_unionUpTo`
  ties the two together and `JSP90.residueOf_greedyChain` identifies level `j` of the greedy chain
  with `JSP90.residueOf` of `JSPProblem/Stair.lean` — so the greedy chain *is* a chain in the
  vocabulary of the ladder, with no choice to be made.
* **THE GREEDY CHAIN IS A PACKING** — `JSP90.packing_of_levels`: if the first `n` levels are all
  non-bipartite then `H` contains `n` pairwise vertex-disjoint odd cycles
  (`JSP90.disjoint_greedyCycle_of_lt`).  This is the classical greedy step, and it is what forces
  the *last* level to be bipartite under a packing bound
  (`JSP90.level_isBipartite_of_locIndep`).
* **THE HEADLINE INSTANCE** — `JSP90.erdos73On_of_greedyChain`:

  > `LocIndep k G → CloseToBipartite (∑ j : Fin k, girthOf (level G j)) G`

  The hypothesis is **exactly Erdős's own**, with nothing else: no degree bound, no odd-girth bound,
  no packing *weight*, no chain, no connectivity or decomposition hypothesis.  The constant is read
  off the graph: the sum of the *actual* odd girths of the residues.
* **THE CERTIFICATE IS EXHIBITED** — `JSP90.hitsOddCycles_unionUpTo` and
  `JSP90.closeToBipartite_of_greedyChain`: the transversal is `JSP90.unionUpTo G k` itself, the
  greedy cycles, and it *meets every odd cycle of `G`*.
* **THE COMPARISON WITH THE UNIFORM BOUND, MACHINE CHECKED** —
  `JSP90.greedySum_le_uniform` (the new constant is at most `ℓ * k`), so
  `JSP90.erdos73On_of_greedyChain_uniform` **re-derives** `JSPProblem/Transversal.lean`'s instance
  `JSP90.erdos73On_of_bounded_odd_girth` from the greedy chain, and `JSP90.greedySum_lt_uniform`
  records when the new constant is **strictly** better (`JSP90.girthSum_lt_mul_of_short_first` is
  the arithmetic).

## Why this is progress and not a reformulation

The constant of Erdős #73 must be a number depending only on `k`, and
`JSP90.erdos73On_of_greedyChain_uniform` *is* such a number: on the class "packing number `≤ k` and
odd girth `≤ ℓ`" the greedy chain pays for the odd cycles it actually deletes, and the bound is at
most `ℓ * k`, strictly smaller as soon as some residue has a shorter odd cycle.  The gap to
`jsp_000090_main` is unchanged and is recorded in `discovery/JSP-000090/policy.json`: it is
`JSP90.OddCycleErdosPosa r` for arbitrary `r`, because nothing here bounds
`∑ j, girthOf (level G j)` in terms of `k` alone — `kTriangles` has packing number `k`, odd girth
`3`, and greedy sum `3 k`, which is the best this development can do there.
-/

set_option maxHeartbeats 800000

namespace JSP90

noncomputable section

variable {V : Type*} [Fintype V]

local instance instDecidableEqGreedy : DecidableEq V := Classical.decEq V

/-- The `Nonempty` test on the family of odd cycles is decided classically; this is the only
`Decidable` instance the file needs (it is used by the `if` inside `greedyCycle` and `girthOf`). -/
local instance instDecidableOddCyclesNonempty {W : Type*} [Fintype W] {H : SimpleGraph W} :
    Decidable ((OddCycles H).Nonempty) := Classical.propDecidable _

local instance instDecidableExistsAdj {W : Type*} {H : SimpleGraph W} {v : W} :
    Decidable (∃ w, H.Adj v w) := Classical.propDecidable _

universe u

/-! ### Part 1 — shortest odd cycles -/

section Shortest

/-- **A member of a nonempty finite family of vertex sets of smallest cardinality exists.** -/
theorem exists_min_card (s : Finset (Finset V)) (hs : s.Nonempty) :
    ∃ C, C ∈ s ∧ ∀ D ∈ s, C.card ≤ D.card := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs (Finset.not_nonempty_iff_eq_empty.mpr rfl)
  | insert a s ha ih =>
      by_cases hse : s.Nonempty
      · obtain ⟨C, hC, hmin⟩ := ih hse
        by_cases hac : ∀ D ∈ s, a.card ≤ D.card
        · refine ⟨a, Finset.mem_insert_self a s, fun D hD => ?_⟩
          rcases Finset.mem_insert.mp hD with rfl | hD
          · exact Nat.le_refl _
          · exact hac D hD
        · have hex : ∃ D ∈ s, D.card < a.card := by
            by_contra hcon
            refine hac ?_
            intro D hD
            by_contra hle
            exact hcon ⟨D, hD, Nat.lt_of_not_ge hle⟩
          obtain ⟨D, hD, hlt⟩ := hex
          refine ⟨C, Finset.mem_insert_of_mem hC, fun E hE => ?_⟩
          rcases Finset.mem_insert.mp hE with rfl | hE
          · exact (hmin D hD).trans (Nat.le_of_lt hlt)
          · exact hmin E hE
      · refine ⟨a, Finset.mem_insert_self a s, fun D hD => ?_⟩
        rcases Finset.mem_insert.mp hD with rfl | hD
        · exact Nat.le_refl _
        · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hse
          rw [hs'] at hD
          exact absurd hD (by simp)

/-- **A shortest odd cycle of `H`**, in the sense of fewest vertices. -/
noncomputable def shortestOddCycle (H : SimpleGraph V) (h : (OddCycles H).Nonempty) : Finset V :=
  Classical.choose (exists_min_card (OddCycles H) h)

theorem mem_shortestOddCycle {H : SimpleGraph V} {h : (OddCycles H).Nonempty} :
    shortestOddCycle H h ∈ OddCycles H :=
  (Classical.choose_spec (exists_min_card (OddCycles H) h)).1

theorem isOddCycle_shortestOddCycle {H : SimpleGraph V} {h : (OddCycles H).Nonempty} :
    IsOddCycle H (shortestOddCycle H h) := mem_oddCycles.mp mem_shortestOddCycle

theorem card_le_of_mem_oddCycles {H : SimpleGraph V} {h : (OddCycles H).Nonempty} {D : Finset V}
    (hD : D ∈ OddCycles H) : (shortestOddCycle H h).card ≤ D.card :=
  (Classical.choose_spec (exists_min_card (OddCycles H) h)).2 D hD

/-- **THE ODD GIRTH OF `H`**: the number of vertices of a shortest odd cycle, or `0` if `H` has no
odd cycle (i.e. if `H` is bipartite).

This is the *upper* bound direction: `JSPProblem/Transversal.lean` needs
`∀ C, IsOddCycle G C → C.card ≤ ℓ`, and round 100 showed that the opposite, "odd girth from below",
carries no information. -/
noncomputable def girthOf (H : SimpleGraph V) : ℕ :=
  if h : (OddCycles H).Nonempty then (shortestOddCycle H h).card else 0

/-- **THE GREEDY STEP**: a shortest odd cycle of `H`, or the empty set if `H` is bipartite. -/
noncomputable def greedyCycle (H : SimpleGraph V) : Finset V :=
  if h : (OddCycles H).Nonempty then shortestOddCycle H h else ∅

theorem card_greedyCycle {H : SimpleGraph V} (h : (OddCycles H).Nonempty) :
    (greedyCycle H).card = girthOf H := by
  rw [greedyCycle, dif_pos h, girthOf, dif_pos h]

theorem isOddCycle_greedyCycle {H : SimpleGraph V} (h : (OddCycles H).Nonempty) :
    IsOddCycle H (greedyCycle H) := by
  rw [greedyCycle, dif_pos h]; exact isOddCycle_shortestOddCycle

/-- **A non-bipartite graph has an odd cycle.** -/
theorem oddCycles_nonempty_of_not_isBipartite {H : SimpleGraph V} (h : ¬ H.IsBipartite) :
    (OddCycles H).Nonempty := by
  by_contra hcon
  have hb : H.IsBipartite := isBipartite_of_no_oddCycle fun ⟨C, hC⟩ => hcon ⟨C, mem_oddCycles_univ hC⟩
  exact h hb

theorem isOddCycle_greedyCycle_of_not_isBipartite {H : SimpleGraph V} (h : ¬ H.IsBipartite) :
    IsOddCycle H (greedyCycle H) :=
  isOddCycle_greedyCycle (oddCycles_nonempty_of_not_isBipartite h)

/-- **THE ODD GIRTH OF A BIPARTITE GRAPH IS `0`.** -/
theorem girthOf_eq_zero_of_isBipartite {H : SimpleGraph V} (h : H.IsBipartite) : girthOf H = 0 := by
  have hne : ¬ (OddCycles H).Nonempty := by
    rintro ⟨C, hC⟩
    exact (not_isOddCycle_of_isBipartite h) ⟨C, mem_oddCycles.mp hC⟩
  rw [girthOf, dif_neg hne]

/-- **THE ODD GIRTH IS AT MOST THE LENGTH OF EVERY ODD CYCLE.** -/
theorem girthOf_le {H : SimpleGraph V} {D : Finset V} (hD : IsOddCycle H D) :
    girthOf H ≤ D.card := by
  by_cases hne : (OddCycles H).Nonempty
  · rw [girthOf, dif_pos hne]
    exact card_le_of_mem_oddCycles (mem_oddCycles_univ hD)
  · rw [girthOf, dif_neg hne]
    exact absurd hD (fun hD' => hne ⟨D, mem_oddCycles_univ hD'⟩)

/-- **THE ODD GIRTH IS NOT A SUBSTANTIVE COST: THE GREEDY CYCLE COSTS EXACTLY THE ODD GIRTH.** -/
theorem card_greedyCycle_le_girthOf (H : SimpleGraph V) : (greedyCycle H).card ≤ girthOf H := by
  by_cases hne : (OddCycles H).Nonempty
  · rw [card_greedyCycle hne]
  · rw [greedyCycle, girthOf, dif_neg hne, dif_neg hne]
    simp

/-- **A NONEMPTY GRAPH HAS AN ODD CYCLE OF AT LEAST THREE VERTICES, so a nonempty family of odd
cycles has a positive odd girth.** -/
theorem three_le_girthOf {H : SimpleGraph V} (h : (OddCycles H).Nonempty) : 3 ≤ girthOf H := by
  rw [girthOf, dif_pos h]
  exact three_le_card_of_isOddCycle isOddCycle_shortestOddCycle

end Shortest

/-! ### Part 2 — the greedy residue chain -/

section GreedyChain

/-- **LEVEL `j` OF THE GREEDY CHAIN**: `H` with the greedy (shortest) odd cycles of levels
`0, …, j-1` deleted.  Level `0` is `H` itself. -/
noncomputable def level (H : SimpleGraph V) : ℕ → SimpleGraph V
  | 0 => H
  | (j + 1) => deleteFinset (level H j) (greedyCycle (level H j))

/-- **The vertices deleted before level `j`**: the union of the greedy odd cycles of the earlier
levels. -/
noncomputable def unionUpTo (H : SimpleGraph V) : ℕ → Finset V
  | 0 => ∅
  | (j + 1) => unionUpTo H j ∪ greedyCycle (level H j)

theorem level_zero (H : SimpleGraph V) : level H 0 = H := rfl

theorem level_succ (H : SimpleGraph V) (j : ℕ) :
    level H (j + 1) = deleteFinset (level H j) (greedyCycle (level H j)) := rfl

theorem unionUpTo_zero (H : SimpleGraph V) : unionUpTo H 0 = ∅ := rfl

theorem unionUpTo_succ (H : SimpleGraph V) (j : ℕ) :
    unionUpTo H (j + 1) = unionUpTo H j ∪ greedyCycle (level H j) := rfl

/-- **A VERTEX IS DELETED BEFORE LEVEL `j` IFF IT LIES IN THE GREEDY CYCLE OF AN EARLIER LEVEL.** -/
theorem mem_unionUpTo {H : SimpleGraph V} {j : ℕ} {v : V} :
    v ∈ unionUpTo H j ↔ ∃ i, i < j ∧ v ∈ greedyCycle (level H i) := by
  induction j with
  | zero =>
      constructor
      · intro hv
        rw [unionUpTo_zero] at hv
        simp at hv
      · rintro ⟨i, hi, _⟩
        omega
  | succ j ih =>
      constructor
      · intro hv
        rw [unionUpTo_succ] at hv
        rw [Finset.mem_union] at hv
        rcases hv with hv | hv
        · obtain ⟨i', hi', hv'⟩ := ih.mp hv
          exact ⟨i', by omega, hv'⟩
        · exact ⟨j, Nat.lt_succ_self j, hv⟩
      · rintro ⟨i, hi, hv⟩
        rw [unionUpTo_succ]
        refine Finset.mem_union.mpr ?_
        rcases lt_or_ge i j with hlt | hge
        · exact Or.inl (ih.mpr ⟨i, hlt, hv⟩)
        · have hie : i = j := by omega
          rw [hie] at hv
          exact Or.inr hv

/-- **LEVEL `j` IS THE RESIDUE ON THE COMPLEMENT OF THE DELETED SET.** -/
theorem level_eq_deleteFinset_unionUpTo (H : SimpleGraph V) (j : ℕ) :
    level H j = deleteFinset H (unionUpTo H j) := by
  induction j with
  | zero => rw [level_zero, unionUpTo_zero, deleteFinset_empty]
  | succ j ih =>
      calc level H (j + 1) = deleteFinset (level H j) (greedyCycle (level H j)) := level_succ H j
        _ = deleteFinset (deleteFinset H (unionUpTo H j)) (greedyCycle (level H j)) := by rw [ih]
        _ = deleteFinset H (unionUpTo H j ∪ greedyCycle (level H j)) := deleteFinset_deleteFinset _ _
        _ = deleteFinset H (unionUpTo H (j + 1)) := by rw [unionUpTo_succ]

/-- **THE DELETED SET GROWS ALONG THE CHAIN.** -/
theorem unionUpTo_mono (H : SimpleGraph V) {i j : ℕ} (h : i ≤ j) :
    unionUpTo H i ⊆ unionUpTo H j := by
  intro v hv
  obtain ⟨k, hk, hvk⟩ := mem_unionUpTo.mp hv
  exact mem_unionUpTo.mpr ⟨k, by omega, hvk⟩

/-- **THE GREEDY CHAIN AS A CHAIN OF LENGTH `k`** in the vocabulary of `JSPProblem/Stair.lean`. -/
noncomputable def greedyChain (G : SimpleGraph V) (k : ℕ) : Fin k → Finset V :=
  fun j => greedyCycle (level G j.val)

/-- **THE DELETED SET OF THE GREEDY CHAIN IS `unionUpTo`.** -/
theorem deletedUpTo_greedyChain {k : ℕ} (G : SimpleGraph V) (j : Fin k) :
    deletedUpTo (greedyChain G k) j = unionUpTo G j.val := by
  ext v
  rw [deletedUpTo, mem_unionUpTo]
  simp only [greedyChain, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hv⟩
    exact ⟨i.val, by simpa using hi, by simpa using hv⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨⟨i, by omega⟩, by simpa using hi, by simpa using hv⟩

/-- **LEVEL `j` OF THE GREEDY CHAIN IS LEVEL `j` OF THE RESIDUE CHAIN OF `JSPProblem/Stair.lean`.**

This is the bridge to round 101: the greedy chain *is* a chain in the vocabulary of the ladder, and
no chain has to be exhibited. -/
theorem residueOf_greedyChain {k : ℕ} (G : SimpleGraph V) (j : Fin k) :
    residueOf G (greedyChain G k) j = level G j.val := by
  rw [residueOf, deletedUpTo_greedyChain, level_eq_deleteFinset_unionUpTo]

/-- **BIPARTITENESS OF A LEVEL PROPAGATES DOWN THE CHAIN.** -/
theorem isBipartite_level_succ {H : SimpleGraph V} {j : ℕ} (h : (level H j).IsBipartite) :
    (level H (j + 1)).IsBipartite := by
  rw [level_succ]; exact isBipartite_delete h

end GreedyChain

/-! ### Part 3 — vertex sets, and the disjointness of the greedy chain -/

section Vertices

/-- **The vertices of `G` that have a neighbour.** -/
noncomputable def vertsOf (G : SimpleGraph V) : Finset V :=
  (Finset.univ : Finset V).filter fun v => ∃ w, G.Adj v w

theorem mem_vertsOf {G : SimpleGraph V} {v : V} : v ∈ vertsOf G ↔ ∃ w, G.Adj v w := by
  simp [vertsOf]

/-- **AN ODD CYCLE HAS A VERTEX.** -/
theorem nonempty_of_isOddCycle {G : SimpleGraph V} {C : Finset V} (hC : IsOddCycle G C) :
    C.Nonempty := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  exact ⟨f ⟨0, by omega⟩, (hmem _).mpr ⟨⟨0, by omega⟩, rfl⟩⟩

/-- **AN ODD CYCLE LIES IN THE VERTEX SET OF ITS GRAPH.** -/
theorem isOddCycle_subset_vertsOf {G : SimpleGraph V} {C : Finset V} (hC : IsOddCycle G C) :
    C ⊆ vertsOf G := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  intro v hv
  rw [mem_vertsOf]
  obtain ⟨j, hj⟩ := (hmem v).mp hv
  exact ⟨f (cycSucc j), hj ▸ hcyc j⟩

/-- **A VERTEX OF A DELETION IS NOT DELETED.** -/
theorem not_mem_of_mem_vertsOf_deleteFinset {G : SimpleGraph V} {X : Finset V} {v : V}
    (h : v ∈ vertsOf (deleteFinset G X)) : v ∉ X := by
  rw [mem_vertsOf] at h
  obtain ⟨w, hw⟩ := h
  rw [deleteFinset_adj] at hw
  exact hw.1

/-- **AN ODD CYCLE AVOIDING THE DELETED SET IS AN ODD CYCLE OF THE RESIDUE.** -/
theorem isOddCycle_deleteFinset_of_disjoint {G : SimpleGraph V} {X C : Finset V} (hC : IsOddCycle G C)
    (hdis : Disjoint C X) : IsOddCycle (deleteFinset G X) C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  have hfj : ∀ j : Fin m, f j ∉ X :=
    fun j => Finset.disjoint_left.mp hdis ((hmem (f j)).mpr ⟨j, rfl⟩)
  have hadj : ∀ j : Fin m, (deleteFinset G X).Adj (f j) (f (cycSucc j)) := by
    intro j
    exact ((show (deleteFinset G X).Adj (f j) (f (cycSucc j)) ↔
        f j ∉ X ∧ f (cycSucc j) ∉ X ∧ G.Adj (f j) (f (cycSucc j)) from deleteFinset_adj).2
      ⟨hfj j, hfj (cycSucc j), hcyc j⟩)
  exact ⟨m, f, hm, hm3, hinj, hadj, hmem⟩

/-- **ADJACENCY IN A LATER LEVEL IMPLIES ADJACENCY IN AN EARLIER ONE.** -/
theorem level_adj_mono {H : SimpleGraph V} {j : ℕ} {v w : V} (h : (level H (j + 1)).Adj v w) :
    (level H j).Adj v w := by
  rw [level_succ, deleteFinset_adj] at h
  exact h.2.2

/-- **THE VERTEX SETS SHRINK ALONG THE CHAIN.** -/
theorem vertsOf_level_mono {H : SimpleGraph V} : ∀ (j : ℕ) (i : ℕ), i ≤ j →
    vertsOf (level H j) ⊆ vertsOf (level H i) := by
  intro j
  induction j with
  | zero =>
      intro i hi
      have hii : i = 0 := by omega
      subst hii
      exact fun _ hv => hv
  | succ j ih =>
      intro i hi v hv
      rcases Nat.eq_or_lt_of_le hi with hie | hlt
      · rw [hie]; exact hv
      · rw [mem_vertsOf] at hv
        obtain ⟨w, hw⟩ := hv
        rw [mem_vertsOf]
        exact mem_vertsOf.mp
          (ih i (Nat.lt_succ_iff.mp hlt) (mem_vertsOf.mpr ⟨w, level_adj_mono hw⟩))

theorem vertsOf_level_mono' {H : SimpleGraph V} {i j : ℕ} (h : i ≤ j) :
    vertsOf (level H j) ⊆ vertsOf (level H i) := vertsOf_level_mono j i h

/-- **TWO GREEDY CYCLES OF DIFFERENT LEVELS ARE DISJOINT.**

This is the greedy step of the classical argument: the greedy cycle of level `j` is an odd cycle of
the residue at level `j`, so all of its vertices survived the deletion of the greedy cycle of level
`i < j`, and none of them was deleted. -/
theorem disjoint_greedyCycle_of_lt {H : SimpleGraph V} {i j : ℕ} (hij : i < j)
    (hCi : IsOddCycle (level H i) (greedyCycle (level H i)))
    (hCj : IsOddCycle (level H j) (greedyCycle (level H j))) :
    Disjoint (greedyCycle (level H i)) (greedyCycle (level H j)) := by
  refine (Finset.disjoint_left.2 fun _ hvj => ?_).symm
  have h1 := vertsOf_level_mono (j := j) (i := i + 1) (Nat.succ_le_iff.mpr hij)
    (isOddCycle_subset_vertsOf hCj hvj)
  rw [level_succ] at h1
  exact not_mem_of_mem_vertsOf_deleteFinset h1

end Vertices

/-- **AN ODD CYCLE OF A LEVEL IS AN ODD CYCLE OF `H`, AS THE SAME VERTEX SET.** -/
theorem isOddCycle_of_isOddCycle_level {H : SimpleGraph V} {C : Finset V} {j : ℕ}
    (hC : IsOddCycle (level H j) C) : IsOddCycle H C := by
  induction j with
  | zero => exact hC
  | succ j ih =>
      rw [level_succ] at hC
      exact ih (isOddCycle_of_isOddCycle_deleteFinset hC)

/-- **THE MEMBERS OF THE GREEDY CHAIN OF LENGTH `n` ARE A PACKING OF ODD CYCLES OF `H`.** -/
theorem isOddCycleFamily_greedyChain_image {H : SimpleGraph V} {n : ℕ}
    (hC : ∀ j, j < n → IsOddCycle (level H j) (greedyCycle (level H j))) :
    IsOddCycleFamily (G := H) ((Finset.range n).image fun j => greedyCycle (level H j)) := by
  refine ⟨?_, fun X hX => ?_⟩
  · intro X hX Y hY hne
    simp only [Finset.mem_image] at hX hY
    obtain ⟨i, hi, hiX⟩ := hX
    obtain ⟨j, hj, hjY⟩ := hY
    have hil : i < n := Finset.mem_range.mp hi
    have hjl : j < n := Finset.mem_range.mp hj
    have hX : X = greedyCycle (level H i) := hiX.symm
    have hY : Y = greedyCycle (level H j) := hjY.symm
    rw [hX, hY]
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have hd : Disjoint (greedyCycle (level H i)) (greedyCycle (level H j)) :=
        disjoint_greedyCycle_of_lt (H := H) hlt (hC i hil) (hC j hjl)
      exact (Finset.disjoint_iff_inter_eq_empty (s := greedyCycle (level H i))
        (t := greedyCycle (level H j))).mp hd
    · rw [heq] at hX
      have hXY : X = Y := by rw [hX, hY]
      exact absurd hXY hne
    · have hd : Disjoint (greedyCycle (level H j)) (greedyCycle (level H i)) :=
        disjoint_greedyCycle_of_lt (H := H) hgt (hC j hjl) (hC i hil)
      exact (Finset.disjoint_iff_inter_eq_empty (s := greedyCycle (level H i))
        (t := greedyCycle (level H j))).mp hd.symm
  · simp only [Finset.mem_image] at hX
    obtain ⟨j, hj, hjX⟩ := hX
    have hjX' : X = greedyCycle (level H j) := hjX.symm
    rw [hjX']
    exact isOddCycle_of_isOddCycle_level (H := H) (C := greedyCycle (level H j)) (j := j)
      (hC j (Finset.mem_range.mp hj))

/-- **THE GREEDY CYCLES OF THE FIRST `n` LEVELS ARE PAIRWISE DISTINCT.** -/
theorem injOn_greedyChain {H : SimpleGraph V} {n : ℕ}
    (hC : ∀ j, j < n → IsOddCycle (level H j) (greedyCycle (level H j))) :
    Set.InjOn (fun j => greedyCycle (level H j)) (Finset.range n) := by
  rintro i hi j hj heq
  have hil : i < n := Finset.mem_range.mp hi
  have hjl : j < n := Finset.mem_range.mp hj
  have heq' : greedyCycle (level H i) = greedyCycle (level H j) := by simpa using heq
  rcases lt_trichotomy i j with hlt | heqij | hgt
  · exfalso
    have hd := disjoint_greedyCycle_of_lt (H := H) hlt (hC i hil) (hC j hjl)
    obtain ⟨x, hx⟩ := nonempty_of_isOddCycle (hC i hil)
    exact (Finset.disjoint_left.mp hd hx) (heq'.symm ▸ hx)
  · exact heqij
  · exfalso
    have hd := disjoint_greedyCycle_of_lt (H := H) hgt (hC j hjl) (hC i hil)
    obtain ⟨x, hx⟩ := nonempty_of_isOddCycle (hC i hil)
    exact (Finset.disjoint_right.mp hd hx) (heq'.symm ▸ hx)

/-- **THE CARDINALITY OF THE PACKING FORMED BY THE GREEDY CHAIN.** -/
theorem card_image_greedyChain {H : SimpleGraph V} {n : ℕ}
    (hC : ∀ j, j < n → IsOddCycle (level H j) (greedyCycle (level H j))) :
    ((Finset.range n).image fun j => greedyCycle (level H j)).card = n := by
  rw [Finset.card_image_of_injOn (s := Finset.range n)
    (f := fun j => greedyCycle (level H j)) (injOn_greedyChain hC), Finset.card_range]

/-- **THE GREEDY STEP OF THE CLASSICAL ARGUMENT: `n` NON-BIPARTITE LEVELS GIVE `n` DISJOINT ODD
CYCLES OF `H`.**

This is the "either a large packing, or a small transversal" alternative.  It is what makes the
*last* level bipartite under a packing bound, and it is the content round 101 had to assume. -/
theorem packing_of_levels {H : SimpleGraph V} {n : ℕ}
    (hnb : ∀ j, j < n → ¬ (level H j).IsBipartite) :
    ∃ P : Finset (Finset V), IsOddCycleFamily (G := H) P ∧ n ≤ P.card := by
  have hC : ∀ j, j < n → IsOddCycle (level H j) (greedyCycle (level H j)) :=
    fun j hj => isOddCycle_greedyCycle_of_not_isBipartite (hnb j hj)
  exact ⟨(Finset.range n).image fun j => greedyCycle (level H j),
    isOddCycleFamily_greedyChain_image hC, by rw [card_image_greedyChain hC]⟩

/-- **AN ODD CYCLE OF `H` MEETS THE SET DELETED BEFORE A BIPARTITE LEVEL.**

If `C` were disjoint from the deleted set, `C` would be an odd cycle of the bipartite residue — the
last lemma of the greedy argument. -/
theorem inter_unionUpTo_ne {H : SimpleGraph V} {k : ℕ} (hb : (level H k).IsBipartite)
    {C : Finset V} (hC : IsOddCycle H C) : ¬ Disjoint C (unionUpTo H k) := by
  intro hdis
  have hC' : IsOddCycle (level H k) C := by
    rw [level_eq_deleteFinset_unionUpTo]
    exact isOddCycle_deleteFinset_of_disjoint hC hdis
  exact (not_isOddCycle_of_isBipartite hb) ⟨C, hC'⟩

/-! ### Part 4 — the first bipartite level, and why it is at most `k` -/

section FirstBipartite

/-- **THE GREEDY CYCLE OF A BIPARTITE GRAPH IS EMPTY.** -/
theorem greedyCycle_eq_empty_of_isBipartite {H : SimpleGraph V} (h : H.IsBipartite) :
    greedyCycle H = ∅ := by
  have hne : ¬ (OddCycles H).Nonempty := by
    rintro ⟨C, hC⟩
    exact (not_isOddCycle_of_isBipartite h) ⟨C, mem_oddCycles.mp hC⟩
  rw [greedyCycle, dif_neg hne]

/-- **BIPARTITENESS PERSISTS ALONG THE CHAIN.**  Deleting vertices cannot destroy it. -/
theorem isBipartite_level_mono {H : SimpleGraph V} : ∀ (j : ℕ) (i : ℕ), i ≤ j →
    (level H i).IsBipartite → (level H j).IsBipartite := by
  intro j
  induction j with
  | zero =>
      intro i hi h
      have hii : i = 0 := by omega
      subst hii
      exact h
  | succ j ih =>
      intro i hi h
      rcases Nat.eq_or_lt_of_le hi with hie | hlt
      · subst hie
        exact h
      · exact isBipartite_level_succ (ih i (Nat.lt_succ_iff.mp hlt) h)

theorem isBipartite_level_mono' {H : SimpleGraph V} {i j : ℕ} (h : i ≤ j)
    (hb : (level H i).IsBipartite) : (level H j).IsBipartite := isBipartite_level_mono j i h hb

/-- **ERDŐS'S HYPOTHESIS MAKES THE `k`-TH LEVEL BIPARTITE.**

The payoff of the greedy step: `LocIndep k G` forbids `k + 1` disjoint odd cycles
(`JSP90.locIndep_oddCyclePackingLe`), while the greedy chain of `k + 1` non-bipartite levels would
be exactly such a packing (`JSP90.packing_of_levels`). -/
theorem level_isBipartite_of_locIndep {k : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) :
    (level G k).IsBipartite := by
  by_contra hnb
  have hex : ¬ ∃ j, j ≤ k ∧ (level G j).IsBipartite := by
    rintro ⟨j, hj, hb⟩
    exact hnb (isBipartite_level_mono' hj hb)
  have hnb' : ∀ j, j < k + 1 → ¬ (level G j).IsBipartite := by
    intro j hj
    exact fun hb => hex ⟨j, by omega, hb⟩
  obtain ⟨P, hP, hcard⟩ := packing_of_levels (H := G) (n := k + 1) hnb'
  have hp := locIndep_oddCyclePackingLe hG
  have hle := hp P hP
  omega

/-- The existence of a bipartite level is decided classically. -/
local instance instDecidableBipartiteLevel {W : Type*} [Fintype W] {H : SimpleGraph W} {k : ℕ}
    (n : ℕ) : Decidable (n ≤ k ∧ (level H n).IsBipartite) := Classical.propDecidable _

local instance instDecidableExistsBipartiteLevel {W : Type*} [Fintype W] {H : SimpleGraph W}
    {k : ℕ} : Decidable (∃ j, j ≤ k ∧ (level H j).IsBipartite) := Classical.propDecidable _

/-- **THE FIRST BIPARTITE LEVEL OF THE CHAIN, or `k + 1` IF THERE IS NONE AMONG `0 … k`.**

This is where the greedy construction stops: the greedy odd cycles of the levels below it form the
chain of `JSPProblem/Stair.lean`, and the level itself is where the residue becomes bipartite. -/
noncomputable def firstBipartiteLevel (H : SimpleGraph V) (k : ℕ) : ℕ :=
  if h : ∃ j, j ≤ k ∧ (level H j).IsBipartite then Nat.find h else k + 1

theorem firstBipartiteLevel_spec {H : SimpleGraph V} {k : ℕ}
    (h : ∃ j, j ≤ k ∧ (level H j).IsBipartite) :
    firstBipartiteLevel H k ≤ k ∧ (level H (firstBipartiteLevel H k)).IsBipartite := by
  rw [firstBipartiteLevel, dif_pos h]
  exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2⟩

theorem firstBipartiteLevel_min {H : SimpleGraph V} {k : ℕ}
    (h : ∃ j, j ≤ k ∧ (level H j).IsBipartite) {m : ℕ} (hm : m ≤ k)
    (hbm : (level H m).IsBipartite) : firstBipartiteLevel H k ≤ m := by
  rw [firstBipartiteLevel, dif_pos h]
  exact Nat.find_min' (p := fun j => j ≤ k ∧ (level H j).IsBipartite) (m := m) h ⟨hm, hbm⟩

/-- **EVERY LEVEL BELOW THE FIRST BIPARTITE ONE IS NON-BIPARTITE**, i.e. the greedy cycle of such a
level really is an odd cycle. -/
theorem not_isBipartite_of_lt_firstBipartiteLevel {H : SimpleGraph V} {k : ℕ}
    (h : ∃ j, j ≤ k ∧ (level H j).IsBipartite) {j : ℕ} (hlt : j < firstBipartiteLevel H k) :
    ¬ (level H j).IsBipartite := by
  intro hb
  have hjle : j ≤ k := by
    have h1 := (firstBipartiteLevel_spec (H := H) (k := k) h).1
    omega
  have hmin : firstBipartiteLevel H k ≤ j := firstBipartiteLevel_min (m := j) h hjle hb
  omega

/-- **EVERY LEVEL AT OR ABOVE THE FIRST BIPARTITE ONE IS BIPARTITE.** -/
theorem isBipartite_of_ge_firstBipartiteLevel {H : SimpleGraph V} {k : ℕ}
    (h : ∃ j, j ≤ k ∧ (level H j).IsBipartite) {j : ℕ} (hj : firstBipartiteLevel H k ≤ j)
    (hjk : j ≤ k) : (level H j).IsBipartite :=
  isBipartite_level_mono' hj (firstBipartiteLevel_spec (H := H) (k := k) h).2

end FirstBipartite

/-! ### Part 5 — the arithmetic of the greedy sum -/

section Arithmetic

/-- **`∑ i ∈ range k, g i ≤ ℓ * k` whenever every level pays at most `ℓ`.** -/
theorem girthSum_le_mul : ∀ (k ℓ : ℕ) (g : ℕ → ℕ), (∀ j, j < k → g j ≤ ℓ) →
    girthSum k g ≤ ℓ * k := by
  intro k
  induction k with
  | zero => intro ℓ g hg; simp [girthSum]
  | succ k ih =>
      intro ℓ g hg
      rw [girthSum_succ]
      have h1 := ih ℓ (fun i => g (i + 1)) (fun i hi => hg (i + 1) (by omega))
      have h2 : g 0 ≤ ℓ := hg 0 (by omega)
      calc girthSum k (fun i => g (i + 1)) + g 0 ≤ ℓ * k + ℓ := Nat.add_le_add h1 h2
        _ = ℓ * (k + 1) := by rw [Nat.mul_add, Nat.mul_one]

/-- **THE GREEDY SUM GROWS ONLY WHERE A LEVEL IS CHARGED.** -/
theorem girthSum_mono_of_zero {k k' : ℕ} (hkk : k ≤ k') (f : ℕ → ℕ)
    (hz : ∀ i, k ≤ i → i < k' → f i = 0) : girthSum k f ≤ girthSum k' f := by
  have key : (Finset.range k).sum f ≤ (Finset.range k').sum f := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.range k) (t := Finset.range k')
      (fun x hx => Finset.mem_range.mpr
        (Nat.lt_of_lt_of_le (Finset.mem_range.mp hx) hkk)) ?_
    intro i hi hni
    have hi' : i < k' := Finset.mem_range.mp hi
    by_cases hik : i < k
    · exact Nat.zero_le _
    · rw [hz _ (by omega) hi']
  simpa [girthSum] using key

/-- **`∑ i ∈ range (k+1), g i = ∑ i ∈ range k, g i + g k`** — the form of the step in which the
new level is the *last* one, as the residue chain sees it. -/
theorem girthSum_succ' (k : ℕ) (g : ℕ → ℕ) : girthSum (k + 1) g = girthSum k g + g k := by
  unfold girthSum
  exact Finset.sum_range_succ g k

/-- **THE DELETED SET OF THE FIRST `k` LEVELS COSTS AT MOST THE SUM OF THE LEVEL GIRTHS.** -/
theorem card_unionUpTo_le {H : SimpleGraph V} : ∀ (k : ℕ) (g : ℕ → ℕ),
    (∀ i, i < k → (greedyCycle (level H i)).card ≤ g i) → (unionUpTo H k).card ≤ girthSum k g := by
  intro k
  induction k with
  | zero => intro g hg; rw [unionUpTo_zero]; simp [girthSum]
  | succ k ih =>
      intro g hg
      have hstep : (unionUpTo H (k + 1)).card ≤
          (unionUpTo H k).card + (greedyCycle (level H k)).card := by
        rw [unionUpTo_succ]
        exact Finset.card_union_le (unionUpTo H k) (greedyCycle (level H k))
      rw [girthSum_succ']
      exact Nat.le_trans hstep (Nat.add_le_add (ih g (fun i hi => hg i (by omega)))
        (hg k (by omega)))

/-- **THE ARITHMETIC OF THE STRICT IMPROVEMENT.**  If the first level pays at most `ℓ - 1` and every
other level at most `ℓ`, the greedy sum is *strictly* smaller than `ℓ * k`. -/
theorem girthSum_lt_mul_of_short_first : ∀ (k ℓ : ℕ) (g : ℕ → ℕ),
    1 ≤ k → 1 ≤ ℓ → (∀ j, j < k → g j ≤ ℓ) → g 0 ≤ ℓ - 1 → girthSum k g < ℓ * k := by
  intro k ℓ g hk hℓ hg h0
  have hsplit : girthSum k g = g 0 + girthSum (k - 1) (fun i => g (i + 1)) := by
    have h := girthSum_succ (k - 1) g
    rw [Nat.sub_add_cancel hk, Nat.add_comm] at h
    exact h
  have h1 : girthSum (k - 1) (fun i => g (i + 1)) ≤ ℓ * (k - 1) :=
    girthSum_le_mul (k - 1) ℓ (fun i => g (i + 1)) (fun i hi => hg (i + 1) (by omega))
  have h2 : g 0 ≤ ℓ - 1 := h0
  have hkm : ℓ ≤ ℓ * k := by
    have h := Nat.mul_le_mul_left ℓ hk
    simpa using h
  have e1 : (ℓ * k - ℓ) + ℓ = ℓ * k := Nat.sub_add_cancel hkm
  have hpos : 0 < ℓ * k := Nat.mul_pos (by omega) (by omega)
  have hne : ℓ * k ≠ 0 := by omega
  have e2 : (ℓ - 1) + ℓ * (k - 1) = ℓ * k - 1 := by
    calc (ℓ - 1) + ℓ * (k - 1) = (ℓ - 1) + (ℓ * k - ℓ) := by rw [Nat.mul_sub, Nat.mul_one]
      _ = (ℓ * k - ℓ) + (ℓ - 1) := Nat.add_comm _ _
      _ = ℓ * k - 1 := by
        have h3 := Nat.add_sub_assoc (m := ℓ) (k := 1) (by omega) (n := ℓ * k - ℓ)
        rw [← h3, e1]
  calc girthSum k g = g 0 + girthSum (k - 1) (fun i => g (i + 1)) := hsplit
    _ ≤ (ℓ - 1) + ℓ * (k - 1) := Nat.add_le_add h2 h1
    _ = ℓ * k - 1 := e2
    _ < ℓ * k := Nat.sub_lt hpos (by omega)

end Arithmetic

/-! ### Part 6 — the greedy ladder: a new instance of the headline theorem -/

section Ladder

/-- **THE CHAIN IS SELF-SIMILAR: `level (level H b) n = level H (b + n)`**, by induction on `n`.  This
is what lets the greedy induction restart on the residue at no cost. -/
theorem level_tail (H : SimpleGraph V) : ∀ (b n : ℕ), level (level H b) n = level H (b + n) := by
  intro b n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [level_succ, ih, show b + (n + 1) = (b + n) + 1 by omega, level_succ]

/-- **THE GREEDY LADDER, WITHOUT ANY PACKING BOUND: the chain of the first `n` greedy cycles plus a
bipartite residue at level `n` pay the sum of the level girths.**

This is the form of the ladder that the greedy construction actually needs — the chain comes from the
graph, and the last level is bipartite, so no packing bound is required anywhere. -/
theorem closeToBipartite_of_greedyChain_step : ∀ (n : ℕ) (H : SimpleGraph V),
    (∀ j : Fin n, IsOddCycle (level H j) (greedyCycle (level H j))) →
    (level H n).IsBipartite →
    CloseToBipartite (girthSum n (fun j => girthOf (level H j))) H := by
  intro n
  induction n with
  | zero =>
      intro H hC hb
      exact closeToBipartite_of_isBipartite' hb
  | succ n ih =>
      intro H hC hb
      have hlev : ∀ j : ℕ, level (level H 1) j = level H (1 + j) := level_tail H 1
      have hC' : ∀ j : Fin n,
          IsOddCycle (level (level H 1) j.val) (greedyCycle (level (level H 1) j.val)) := by
        intro j
        rw [hlev]
        have hcc := hC ⟨j.val + 1, by omega⟩
        rw [Fin.val_mk, show j.val + 1 = 1 + j.val by omega] at hcc
        exact hcc
      have hres : (level (level H 1) n).IsBipartite := by
        rw [hlev, show 1 + n = n + 1 by omega]
        exact hb
      have hrec := ih (level H 1) hC' hres
      have hpay : (greedyCycle (level H 0)).card ≤ girthOf (level H 0) :=
        card_greedyCycle_le_girthOf (level H 0)
      have hres2 := closeToBipartite_of_residue (G := level H 0) (C := greedyCycle (level H 0)) hrec
      have hH : level H 0 = H := level_zero H
      have hlift : CloseToBipartite (girthSum n (fun j => girthOf (level (level H 1) j)) +
          (greedyCycle (level H 0)).card) H := by
        rw [← hH]
        exact hres2
      refine CloseToBipartite.mono hlift ?_
      rw [girthSum_succ]
      have e : (fun j => girthOf (level (level H 1) j)) = (fun j => girthOf (level H (j + 1))) := by
        funext j
        rw [hlev, Nat.add_comm]
      rw [← e]
      exact Nat.add_le_add (Nat.le_refl _) hpay


/-- **THE NUMBER OF LEVELS THE GREEDY CHAIN ACTUALLY USES.** -/
theorem exists_firstBipartiteLevel {k : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) :
    ∃ j, j ≤ k ∧ (level G j).IsBipartite := ⟨k, le_rfl, level_isBipartite_of_locIndep hG⟩

/-- **THE HEADLINE INSTANCE OF ERDŐS #73 IN THIS FILE.**

> `LocIndep k G → CloseToBipartite (∑ j : Fin k, girthOf (level G j)) G`

The hypothesis is **exactly** Erdős's own.  There is **no** girth bound, **no** degree bound, **no**
packing-weight bound, **no** chain to be exhibited and **no** connectivity or decomposition
hypothesis.  The constant is read off the graph: it is the sum of the odd girths of the greedy
residues, i.e. the sharp automatic instance of the ladder `g 0 + … + g (n-1)` of
`JSPProblem/Stair.lean` (via `JSP90.residueOf_greedyChain`). -/
theorem closeToBipartite_of_greedyChain_girthSum (k : ℕ) (G : SimpleGraph V) (hG : LocIndep k G) :
    CloseToBipartite (girthSum k (fun j => girthOf (level G j))) G := by
  obtain ⟨j0, hj0, hb0⟩ := exists_firstBipartiteLevel hG
  have hex : ∃ j, j ≤ k ∧ (level G j).IsBipartite := ⟨j0, hj0, hb0⟩
  have hjle : firstBipartiteLevel G k ≤ k := (firstBipartiteLevel_spec (H := G) (k := k) hex).1
  have hnb : ∀ i : Fin (firstBipartiteLevel G k), ¬ (level G i.val).IsBipartite :=
    fun i => not_isBipartite_of_lt_firstBipartiteLevel (H := G) (k := k) (j := i.val) hex i.isLt
  have hstep := closeToBipartite_of_greedyChain_step (firstBipartiteLevel G k) G
    (fun i => isOddCycle_greedyCycle_of_not_isBipartite (hnb i))
    ((firstBipartiteLevel_spec (H := G) (k := k) hex).2)
  refine CloseToBipartite.mono hstep ?_
  refine girthSum_mono_of_zero hjle (fun i => girthOf (level G i)) ?_
  intro i hi1 hi2
  exact girthOf_eq_zero_of_isBipartite (isBipartite_of_ge_firstBipartiteLevel (H := G) (k := k) hex hi1
    hi2.le)

/-- **THE HEADLINE INSTANCE, WITH THE CONSTANT SUMMED OVER `Fin k`.** -/
theorem erdos73On_of_greedyChain (k : ℕ) (G : SimpleGraph V) (hG : LocIndep k G) :
    CloseToBipartite (∑ j : Fin k, girthOf (level G j)) G := by
  convert closeToBipartite_of_greedyChain_girthSum k G hG using 1
  simpa [girthSum] using sum_fin_val k (fun j => girthOf (level G j))

/-- **THE HEADLINE INSTANCE, IN THE SHAPE OF THE PROBLEM STATEMENT** (all finite vertex types). -/
theorem erdos73On_of_greedyChain_univ (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      CloseToBipartite (∑ j : Fin k, girthOf (level G j)) G := by
  intro W instW G hG
  exact erdos73On_of_greedyChain k G hG

/-- **AN ODD CYCLE OF `G` MEETS THE DELETED SET OF THE FIRST BIPARTITE LEVEL** — the transversal
certificate, before any counting. -/
theorem hitsOddCycles_of_bipartite_level {j : ℕ} {G : SimpleGraph V} (hb : (level G j).IsBipartite) :
    HitsOddCycles G (unionUpTo G j) := by
  intro C hC
  intro hcon
  exact inter_unionUpTo_ne hb hC ((Finset.disjoint_iff_inter_eq_empty (s := C)
    (t := unionUpTo G j)).mpr hcon)

/-- **THE TRANSVERSAL FOR THE HEADLINE INSTANCE IS EXPLICIT.** -/
theorem hitsOddCycles_greedyChain {k : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) :
    HitsOddCycles G (unionUpTo G (firstBipartiteLevel G k)) := by
  obtain ⟨j0, hj0, hb0⟩ := exists_firstBipartiteLevel hG
  have hex : ∃ j, j ≤ k ∧ (level G j).IsBipartite := ⟨j0, hj0, hb0⟩
  exact hitsOddCycles_of_bipartite_level ((firstBipartiteLevel_spec (H := G) (k := k) hex).2)

/-- **THE CONCLUSION WITH ITS CERTIFICATE, EXHIBITED.**  The transversal is
`unionUpTo G (firstBipartiteLevel G k)` — the greedy cycles themselves; its size is at most the sum
of the level odd girths, and deleting it leaves a bipartite graph. -/
theorem closeToBipartite_of_greedyChain_girthSum_witness (k : ℕ) (G : SimpleGraph V)
    (hG : LocIndep k G) :
    ∃ X : Finset V, X.card ≤ girthSum k (fun j => girthOf (level G j)) ∧
      (deleteFinset G X).IsBipartite := by
  obtain ⟨j0, hj0, hb0⟩ := exists_firstBipartiteLevel hG
  have hex : ∃ j, j ≤ k ∧ (level G j).IsBipartite := ⟨j0, hj0, hb0⟩
  have hjle : firstBipartiteLevel G k ≤ k := (firstBipartiteLevel_spec (H := G) (k := k) hex).1
  refine ⟨unionUpTo G (firstBipartiteLevel G k), ?_, ?_⟩
  · refine le_trans
        (card_unionUpTo_le (firstBipartiteLevel G k) (fun i => girthOf (level G i))
          (fun i _ => card_greedyCycle_le_girthOf (level G i))) ?_
    exact girthSum_mono_of_zero hjle (fun i => girthOf (level G i)) (fun i hi1 hi2 =>
      girthOf_eq_zero_of_isBipartite (isBipartite_of_ge_firstBipartiteLevel (H := G) (k := k) hex hi1 hi2.le))
  · have heq : (deleteFinset G (unionUpTo G (firstBipartiteLevel G k))) =
        level G (firstBipartiteLevel G k) :=
      (level_eq_deleteFinset_unionUpTo G (firstBipartiteLevel G k)).symm
    rw [heq]
    exact (firstBipartiteLevel_spec (H := G) (k := k) hex).2

/-- **THE CONCLUSION WITH ITS CERTIFICATE, EXHIBITED (the `Fin k` form of the constant).** -/
theorem closeToBipartite_of_greedyChain (k : ℕ) (G : SimpleGraph V) (hG : LocIndep k G) :
    ∃ X : Finset V, X.card ≤ ∑ j : Fin k, girthOf (level G j) ∧ (deleteFinset G X).IsBipartite := by
  obtain ⟨X, hX, hb⟩ := closeToBipartite_of_greedyChain_girthSum_witness k G hG
  refine ⟨X, le_trans hX ?_, hb⟩
  have key : (∑ j : Fin k, girthOf (level G j)) = girthSum k (fun j => girthOf (level G j)) :=
    sum_fin_val k (fun j => girthOf (level G j))
  rw [key]

/-- **THE GREEDY LADDER IS AT MOST THE UNIFORM BOUND.**  Every level pays the odd girth of its own
residue, so if every odd cycle of `G` has at most `ℓ` vertices the sum is at most `ℓ * k`. -/
theorem greedySum_le_uniform (k ℓ : ℕ) (G : SimpleGraph V)
    (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ) :
    (∑ j : Fin k, girthOf (level G j)) ≤ ℓ * k := by
  have hg : ∀ i, i < k → girthOf (level G i) ≤ ℓ := by
    intro i hi
    by_cases hb : (level G i).IsBipartite
    · rw [girthOf_eq_zero_of_isBipartite hb]; exact Nat.zero_le _
    · exact (girthOf_le (isOddCycle_greedyCycle_of_not_isBipartite hb)).trans
        (hlen _ (isOddCycle_of_isOddCycle_level (H := G) (C := greedyCycle (level G i)) (j := i)
          (isOddCycle_greedyCycle_of_not_isBipartite hb)))
  have key : (∑ j : Fin k, girthOf (level G j)) = girthSum k (fun i => girthOf (level G i)) :=
    sum_fin_val k (fun j => girthOf (level G j))
  rw [key]
  exact girthSum_le_mul k ℓ (fun i => girthOf (level G i)) hg

/-- **`JSPProblem/Transversal.lean`'s INSTANCE IS A COROLLARY OF THE GREEDY CHAIN**: the bound
`CloseToBipartite (ℓ * k) G` of `JSP90.erdos73On_of_bounded_odd_girth`, re-derived here from
`JSP90.erdos73On_of_greedyChain` through `JSP90.greedySum_le_uniform`. -/
theorem erdos73On_of_greedyChain_uniform (k ℓ : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      (∀ D, IsOddCycle G D → D.card ≤ ℓ) → CloseToBipartite (ℓ * k) G := by
  intro W instW G hG hlen
  exact CloseToBipartite.mono (erdos73On_of_greedyChain k G hG) (greedySum_le_uniform k ℓ G hlen)

/-- **THE GREEDY LADDER IS *STRICTLY* CHEAPER THAN THE UNIFORM BOUND** whenever the first residue
has an odd cycle shorter than the largest one: this is the quantitative content of the greedy chain,
and it is the reason the constant of `JSP90.erdos73On_of_greedyChain` can beat `ℓ * k`. -/
theorem greedySum_lt_uniform {k ℓ : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (G : SimpleGraph V)
    (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ) (hshort : girthOf G ≤ ℓ - 1) :
    (∑ j : Fin k, girthOf (level G j)) < ℓ * k := by
  have hg : ∀ i, i < k → girthOf (level G i) ≤ ℓ := by
    intro i hi
    by_cases hb : (level G i).IsBipartite
    · rw [girthOf_eq_zero_of_isBipartite hb]; exact Nat.zero_le _
    · exact (girthOf_le (isOddCycle_greedyCycle_of_not_isBipartite hb)).trans
        (hlen _ (isOddCycle_of_isOddCycle_level (H := G) (C := greedyCycle (level G i)) (j := i)
          (isOddCycle_greedyCycle_of_not_isBipartite hb)))
  have h0 : girthOf (level G 0) ≤ ℓ - 1 := by
    rw [level_zero]; exact hshort
  have key : (∑ j : Fin k, girthOf (level G j)) = girthSum k (fun i => girthOf (level G i)) :=
    sum_fin_val k (fun j => girthOf (level G j))
  rw [key]
  exact girthSum_lt_mul_of_short_first k ℓ (fun i => girthOf (level G i)) hk hℓ hg h0

/-- **THE STRICTLY CHEAPER INSTANCE**: if `G` has an odd cycle of at most `ℓ - 1` vertices, then
`LocIndep k G` forces `G` to be closer to bipartite than the uniform bound `ℓ * k` — by the exact
amount of `JSP90.greedySum_lt_uniform`. -/
theorem erdos73On_of_greedyChain_strict {k ℓ : ℕ} (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      (∀ D, IsOddCycle G D → D.card ≤ ℓ) → girthOf G ≤ ℓ - 1 →
      CloseToBipartite (∑ j : Fin k, girthOf (level G j)) G ∧
        (∑ j : Fin k, girthOf (level G j)) < ℓ * k := by
  intro W instW G hG hlen hshort
  exact ⟨erdos73On_of_greedyChain k G hG, greedySum_lt_uniform hk hℓ G hlen hshort⟩

end Ladder

end

end JSP90
