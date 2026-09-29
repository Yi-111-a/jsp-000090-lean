/-
# JSP-000090 — the WEIGHTED Erdős–Pósa theorem (the residue induction run to exhaustion)

`JSPProblem/Residue.lean` (round 40) proved the two ingredients of the classical induction for
odd cycles: a packing of the residue `G - C` together with the odd cycle `C` is a packing of `G`
(`insert_oddCycle_of_delete`), and a transversal of the residue together with `C` is a transversal
of `G` (`hitsOddCycles_union_cycle`), with the quantitative step

* `closeToBipartite_of_residue : CloseToBipartite q (G - C) → CloseToBipartite (q + |C|) G`.

The step `+ |C|` is what stops that argument, and the *classical* proof replaces it by an absorption
step `+ 1`.  This file takes a third route: it keeps the honest cost `|C|`, but **sums it over a
whole packing** instead of over a single cycle, and inducts on the running total.  The result is the
**weighted Erdős–Pósa theorem**:

* `closeToBipartite_of_weightLe` — **if every packing of odd cycles of `G` has total length at most
  `L`, then `G` is the union of a bipartite graph and `L` vertices.**

Equivalently (`IsMaxWeightPacking`, `exists_maxWeightPacking`, `closeToBipartite_of_maxWeightPacking`):

* **the odd cycle transversal number of `G` is at most the weight of a maximum-weight packing of
  odd cycles**, and a maximum-weight packing exists.

Two further structural facts come out of the same argument, both new in this development:

* `hitsOddCycles_of_maxWeightFamily` — the union of a maximum-weight packing **is** an odd cycle
  transversal (the weight version of `JSPProblem.Transversal.hitsOddCycles_of_maxCardFamily`);
* `isBipartite_delete_of_maxWeightFamily` — **the residue of a maximum-weight packing is bipartite**:
  an odd cycle of the residue is disjoint from every member of the packing, so it could be added to
  the packing and increase its weight.

The instances of the headline theorem obtained here:

* `erdos73On_of_bounded_packing_weight` — Erdős #73 for the class of graphs of **bounded packing
  weight** (a strictly weaker hypothesis than the bounded-odd-girth instance of round 40: only the
  *total* length of a packing is controlled, not the length of each odd cycle);
* `erdos73On_of_bounded_odd_circumference` — the `ℓ * k` instance re-derived as a corollary of the
  weighted theorem;
* `closeToBipartite_iff_completeGraph_add_two` — **on complete graphs the conclusion of Erdős #73
  is exact**, `CloseToBipartite m (K_n) ↔ n ≤ m + 2`, and `erdos73On_completeGraph` — the resulting
  instance, in which the value of Erdős's constant on the class of complete graphs is exactly `k`
  (matching the lower bound `f(k) ≥ k` of `JSPProblem/Sharp.lean` from a second witness).

Finally, this file machine-checks the **negative result which explains the `+|C|` obstacle**:
`absorption_step_fails` shows that the naive absorption step

```
CloseToBipartite q (G - C)  →  CloseToBipartite (q + 1) G        (C an odd cycle of G)
```

is **false as it stands**: for `G = K_5` and the triangle `C = {0,1,2}` the residue `G - C = K_2` is
bipartite (`closeToBipartite_zero_deleteFinset_completeGraph_five`, so the hypothesis holds with
`q = 0`) while `K_5` is not `1`-close to bipartite
(`not_closeToBipartite_one_completeGraph_five`) — its odd cycle transversal number is `3`.  The
failure happens *inside* the range of the headline theorem (`locIndep_completeGraph_five_three`:
`LocIndep 3 (K_5)` holds), and its geometric cause is visible in the witness: every vertex outside
`C` meets `C` in all three of its vertices, whereas at a shortest odd cycle of length `≥ 5` an
outside vertex meets the cycle in at most two of its vertices, two steps apart
(`JSPProblem.card_inter_neigh_le_two` and `JSPProblem.shortArc_of_shortest` in
`JSPProblem/Fan.lean`).  So any absorption lemma must carry such a hypothesis; the concrete form of
the blocker is recorded in `discovery/JSP-000090/policy.json`.
-/

import JSPProblem.Residue
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqWeight : DecidableEq V := Classical.decEq V

/-- The same `DecidableEq` instance as `JSPProblem.Definitions`, so that the ambient `Finset.univ`
appearing in `deleteFinset` is the one this file writes. -/
local instance instDecidableEqFinN (n : ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

/-! ### A finset with at least three elements contains three distinct elements -/

section FinsetHelpers

variable {α : Type*}

/-- **A finset of cardinality at least `2` contains two distinct elements.** -/
theorem exists_two_of_card_ge_two {s : Finset α} (h : 2 ≤ s.card) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro h; simp at h
  | @insert a t ha ih =>
      intro h
      have hcard : (insert a t).card = t.card + 1 := Finset.card_insert_of_notMem ha
      by_cases h1 : 2 ≤ t.card
      · obtain ⟨x, hx, y, hy, hxy⟩ := ih h1
        exact ⟨x, Finset.mem_insert_of_mem hx, y, Finset.mem_insert_of_mem hy, hxy⟩
      · have hnon : t.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨x, hx⟩ := hnon
        exact ⟨a, Finset.mem_insert_self a t, x, Finset.mem_insert_of_mem hx, fun h => ha (h ▸ hx)⟩

/-- **A finset of cardinality at least `3` contains three distinct elements.**  This is the
extraction step used by the clique lemma `not_isBipartite_induceFinset_of_clique` below. -/
theorem exists_three_of_card_ge_three {s : Finset α} (h : 3 ≤ s.card) :
    ∃ x ∈ s, ∃ y ∈ s, ∃ z ∈ s, x ≠ y ∧ y ≠ z ∧ z ≠ x := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro h; simp at h
  | @insert a t ha ih =>
      intro h
      have hcard : (insert a t).card = t.card + 1 := Finset.card_insert_of_notMem ha
      by_cases h3 : 3 ≤ t.card
      · obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hzx⟩ := ih h3
        exact ⟨x, Finset.mem_insert_of_mem hx, y, Finset.mem_insert_of_mem hy,
          z, Finset.mem_insert_of_mem hz, hxy, hyz, hzx⟩
      · have h2 : 2 ≤ t.card := by omega
        obtain ⟨x, hx, y, hy, hxy⟩ := exists_two_of_card_ge_two h2
        exact ⟨a, Finset.mem_insert_self a t, x, Finset.mem_insert_of_mem hx,
          y, Finset.mem_insert_of_mem hy, fun h => ha (h ▸ hx), hxy, fun h => ha (h ▸ hy)⟩

end FinsetHelpers

/-! ### An odd cycle has at least three vertices, and lies in any set containing it -/

section OddCycleFacts

/-- **An odd cycle of `G` has at least three vertices.** -/
theorem isOddCycle_card_ge_three {C : Finset V} (hC : IsOddCycle G C) : 3 ≤ C.card := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hXim : C = (Finset.univ : Finset (Fin m)).image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := (hCmem x).mp hx
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
    · intro hx
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
      exact (hCmem x).mpr ⟨j, hj⟩
  rw [hXim, Finset.card_image_of_injective _ hinj]
  simp
  omega

/-- **An odd cycle of `G` lies in every vertex set containing it.** -/
theorem isOddCycle_subset {C s : Finset V} (hC : IsOddCycle G C)
    (hs : ∀ x ∈ C, x ∈ s) : C ⊆ s := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  intro x hx
  obtain ⟨j, hj⟩ := (hCmem x).mp hx
  exact hs x ((hCmem x).mpr ⟨j, hj⟩)

/-- **Every odd cycle of a residue is an odd cycle of the whole graph.**  (The converse direction
is `JSPProblem.Residue.isOddCycle_of_isOddCycle_avoiding`.) -/
theorem isOddCycle_of_isOddCycle_delete' {B D : Finset V} [Fintype V]
    (hD : IsOddCycle (deleteFinset G B) D) : IsOddCycle G D := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  exact ⟨m, f, hm, hm3, hinj, fun j => (deleteFinset_adj.mp (hcyc j)).2.2, hmem⟩

/-- **A graph induced on at most two vertices is bipartite** (it is a subgraph of `K_2`). -/
theorem isBipartite_induceFinset_of_card_le_two [Fintype V] {s : Finset V} (h2 : s.card ≤ 2) :
    (induceFinset G s).IsBipartite := by
  refine isBipartite_of_no_oddCycle ?_
  rintro ⟨D, hD⟩
  have h3 := isOddCycle_card_ge_three hD
  have hsub : D ⊆ s := isOddCycle_subset hD fun x hx => by
    obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
    obtain ⟨j, hj⟩ := (hmem x).mp hx
    exact hj.symm ▸ (induce_adj.mp (hcyc j)).1
  have hle : D.card ≤ s.card := Finset.card_le_card hsub
  omega

/-- **A complete graph on at least three vertices is not bipartite.**  This is the clique form of
`not_isBipartite_completeGraph_three`, needed for the complete-graph instance below. -/
theorem not_isBipartite_induceFinset_of_clique [Fintype V] {X : Finset V}
    (hclique : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → G.Adj x y) (h3 : 3 ≤ X.card) :
    ¬ (induceFinset G X).IsBipartite := by
  rintro ⟨C, hC⟩
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hca⟩ := exists_three_of_card_ge_three h3
  have hv1 : C a ≠ C b := hC ⟨ha, hb, hclique a ha b hb hab⟩
  have hv2 : C b ≠ C c := hC ⟨hb, hc, hclique b hb c hc hbc⟩
  have hv3 : C c ≠ C a := hC ⟨hc, ha, hclique c hc a ha hca⟩
  have h1 : (C a).val ≤ 1 := by omega
  have h2 : (C b).val ≤ 1 := by omega
  have h3' : (C c).val ≤ 1 := by omega
  have w1 : (C a).val ≠ (C b).val := fun h => hv1 (Fin.val_injective h)
  have w2 : (C b).val ≠ (C c).val := fun h => hv2 (Fin.val_injective h)
  have w3 : (C c).val ≠ (C a).val := fun h => hv3 (Fin.val_injective h)
  omega

end OddCycleFacts

/-! ### The weight of a packing of odd cycles -/

section Weight

/-- The **weight** of a family of cycles: the total number of vertices they cover, i.e. the cost the
residue induction of `JSPProblem/Residue.lean` pays for that family. -/
def PackingWeight {V : Type*} (C : Finset (Finset V)) : ℕ := ∑ i ∈ C, i.card

theorem packingWeight_empty (V : Type*) : PackingWeight (∅ : Finset (Finset V)) = 0 := by
  simp [PackingWeight]

/-- **Adding an odd cycle to a family adds its length to the weight.** -/
theorem packingWeight_insert {V : Type*} (C : Finset (Finset V)) (D : Finset V) (hD : D ∉ C) :
    PackingWeight (insert D C) = D.card + PackingWeight C := by
  simp [PackingWeight, Finset.sum_insert hD]

/-- **`G` has bounded packing weight**: every packing of odd cycles of `G` covers at most `L`
vertices in total.  This is the hypothesis of `closeToBipartite_of_weightLe` below. -/
def WeightLe {V : Type*} (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → PackingWeight C ≤ L

/-- **A packing together with an odd cycle disjoint from all of its members is still a packing.**
This is the weight version of `JSPProblem.Residue.insert_oddCycle_of_delete`: the disjointness
hypothesis is that the new cycle meets no member of the family. -/
theorem insert_oddCycle_of_disjoint {C : Finset (Finset V)} {D : Finset V}
    (hC : IsOddCycleFamily (G := G) C) (hD : IsOddCycle G D)
    (hdis : ∀ X ∈ C, X ∩ D = ∅) : IsOddCycleFamily (G := G) (insert D C) := by
  refine ⟨?_, ?_⟩
  · intro X hX Y hY hXY
    have hX' : X = D ∨ X ∈ C := Finset.mem_insert.mp hX
    have hY' : Y = D ∨ Y ∈ C := Finset.mem_insert.mp hY
    rcases hX' with hXD | hXC
    · rcases hY' with hYD | hYC
      · exact absurd (hXD.trans hYD.symm) hXY
      · refine (Finset.disjoint_iff_inter_eq_empty).mp (Finset.disjoint_left.mpr fun a haX haY => ?_)
        have h0 : Y ∩ D = ∅ := hdis Y hYC
        have h0' : D ∩ Y = ∅ := by rw [Finset.inter_comm]; exact h0
        exact (Finset.disjoint_left.mp (Finset.disjoint_iff_inter_eq_empty.mpr h0') (hXD ▸ haX)) haY
    · rcases hY' with hYD | hYC
      · refine (Finset.disjoint_iff_inter_eq_empty).mp (Finset.disjoint_left.mpr fun a haX haY => ?_)
        have h0 : X ∩ D = ∅ := hdis X hXC
        have h0' : D ∩ X = ∅ := by rw [Finset.inter_comm]; exact h0
        exact (Finset.disjoint_left.mp (Finset.disjoint_iff_inter_eq_empty.mpr h0') (hYD ▸ haY)) haX
      · exact hC.1 X hXC Y hYC hXY
  · intro X hX
    rcases Finset.mem_insert.mp hX with hXD | hXC
    · exact hXD ▸ hD
    · exact hC.2 X hXC

/-- **THE WEIGHTED ERDŐS–PÓSA THEOREM: bounded packing weight forces a bounded odd cycle
transversal.**

If every packing of odd cycles of `G` covers at most `L` vertices in total, then `G` is the union of
a bipartite graph and `L` vertices.

*Proof.*  Induct on `L`.  For `L = 0` (and, more generally, whenever `G` has no odd cycle) `G` is
bipartite.  Otherwise let `C` be an odd cycle; `WeightLe` applied to the packing `{C}` gives
`|C| ≤ L`, and a packing of the residue `G - C` together with `C` is a packing of `G`
(`insert_oddCycle_of_delete`), so the residue has packing weight at most `L - |C|`.  The induction
hypothesis makes the residue `L - |C|`-close to bipartite, and
`JSPProblem.Residue.closeToBipartite_of_residue` lifts this to `CloseToBipartite (L - |C| + |C|) G`.

The proof is the residue induction of `JSPProblem/Residue.lean` iterated, with the running total
`|C₁| + |C₂| + …` as the induction parameter. -/
theorem closeToBipartite_of_weightLe {L : ℕ} :
    ∀ (W : Type*) (instW : Fintype W) (H : SimpleGraph W),
      WeightLe H L → CloseToBipartite L H := by
  intro W instW H
  induction L using Nat.strong_induction_on generalizing W H with
  | h L ih =>
    intro hL
    by_cases hno : ∃ C : Finset W, IsOddCycle H C
    · obtain ⟨C, hC⟩ := hno
      have hsing : DisjointFamily ({C} : Finset (Finset W)) := by
        intro X hX Y hY hXY
        have hXC : X = C := Finset.mem_singleton.mp hX
        have hYC : Y = C := Finset.mem_singleton.mp hY
        exact False.elim (absurd (hXC.trans hYC.symm) hXY)
      have hfam1 : IsOddCycleFamily (G := H) ({C} : Finset (Finset W)) :=
        ⟨hsing, fun X hX => (Finset.mem_singleton.mp hX) ▸ hC⟩
      have hCcard : C.card ≤ L := by
        have h2 := hL {C} hfam1
        simpa [PackingWeight] using h2
      have hres : WeightLe (deleteFinset H C) (L - C.card) :=
        fun 𝒟 h𝒟 => by
          have hfam := insert_oddCycle_of_delete h𝒟 hC
          have h2 := hL _ hfam
          have hCnin : C ∉ 𝒟 := fun h => (not_mem_of_isOddCycle_delete h𝒟 hC h) rfl
          rw [packingWeight_insert 𝒟 C hCnin] at h2
          omega
      have hCpos : 0 < C.card := Finset.card_pos.mpr hC.nonempty
      obtain ⟨X, hX, hbip⟩ := ih (L - C.card) (by omega) (W := W) (instW := instW)
        (H := deleteFinset H C) hres
      have hres' := closeToBipartite_of_residue (G := H) (C := C) (q := L - C.card) ⟨X, hX, hbip⟩
      rwa [Nat.sub_add_cancel hCcard] at hres'
    · exact isBipartite_closeToBipartite (m := L) (isBipartite_of_no_oddCycle (G := H) hno)

/-- `closeToBipartite_of_weightLe` in the usual form: bounded weight of the packings of `G` gives
the conclusion of Erdős #73. -/
theorem closeToBipartite_of_weightLe' [Fintype V] {L : ℕ} (hL : WeightLe G L) :
    CloseToBipartite L G :=
  closeToBipartite_of_weightLe (W := V) (instW := inferInstance) G hL

/-- `𝒞` is a **maximum-weight packing** of odd cycles of `G`: a packing whose weight is at least
that of every packing. -/
def IsMaxWeightPacking {V : Type*} (G : SimpleGraph V) (C : Finset (Finset V)) : Prop :=
  IsOddCycleFamily (G := G) C ∧ ∀ D, IsOddCycleFamily (G := G) D → PackingWeight D ≤ PackingWeight C

/-- **A maximum-weight packing of odd cycles exists.** -/
theorem exists_maxWeightPacking [Fintype V] : ∃ C : Finset (Finset V), IsMaxWeightPacking G C := by
  classical
  set S := (Finset.univ : Finset (Finset (Finset V))).filter (IsOddCycleFamily (G := G)) with hS
  have hne : S.Nonempty :=
    (Finset.filter_nonempty_iff).mpr ⟨∅, Finset.mem_univ _,
      ⟨fun _ hX _ _ hXY => absurd hX (by simp), fun _ hX => absurd hX (by simp)⟩⟩
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image S PackingWeight hne
  exact ⟨C, (Finset.mem_filter.mp hC).2,
    fun D hD => hmax D (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩)⟩

/-- **The union of a maximum-weight packing meets every odd cycle**: an odd cycle missing the union
could be added to the family, increasing its weight.  (The weight version of
`JSPProblem.Transversal.hitsOddCycles_of_maxCardFamily`.) -/
theorem hitsOddCycles_of_maxWeightFamily {C : Finset (Finset V)} (hC : IsMaxWeightPacking G C) :
    HitsOddCycles G (C.biUnion id) := by
  classical
  intro D hD hdis
  have hfam := insert_oddCycle_of_disjoint hC.1 hD fun X hX => by
    have hsub : X ⊆ C.biUnion id := fun y hy => Finset.mem_biUnion.mpr ⟨X, hX, hy⟩
    have hsubD : ∀ z, z ∈ D → z ∉ C.biUnion id :=
      Finset.disjoint_left.mp (Finset.disjoint_iff_inter_eq_empty.mpr hdis)
    refine (Finset.disjoint_iff_inter_eq_empty).mp
      (Finset.disjoint_left.mpr fun z hzX hzD => ?_)
    exact hsubD z hzD (hsub hzX)
  have hle := hC.2 _ hfam
  have hDnin : D ∉ C := by
    intro hDin
    obtain ⟨a, ha⟩ := hD.nonempty
    exact Finset.disjoint_left.mp (Finset.disjoint_iff_inter_eq_empty.mpr hdis) ha
      (Finset.mem_biUnion.mpr ⟨D, hDin, ha⟩)
  rw [packingWeight_insert C D hDnin] at hle
  obtain ⟨a, ha⟩ := hD.nonempty
  have hpos : 0 < D.card := Finset.card_pos.mpr ⟨a, ha⟩
  omega

/-- **THE STRUCTURAL CONTENT OF THE WEIGHTED ARGUMENT: the residue of a maximum-weight packing is
bipartite.**  Indeed an odd cycle of the residue `G - ⋃ C` is disjoint from every member of the
packing and could be added to it, increasing the weight. -/
theorem isBipartite_delete_of_maxWeightFamily [Fintype V] {C : Finset (Finset V)}
    (hC : IsMaxWeightPacking G C) : (deleteFinset G (C.biUnion id)).IsBipartite := by
  refine isBipartite_of_no_oddCycle ?_
  rintro ⟨D, hD⟩
  have hD' : IsOddCycle G D := isOddCycle_of_isOddCycle_delete' hD
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  have hdis : D ∩ C.biUnion id = ∅ := by
    refine (Finset.disjoint_iff_inter_eq_empty).mp
      (Finset.disjoint_left.mpr fun z hzD hzU => ?_)
    obtain ⟨j, hj⟩ := (hmem z).mp hzD
    have hout : f j ∉ C.biUnion id := (deleteFinset_adj.mp (hcyc j)).1
    exact hout (hj ▸ hzU)
  exact absurd hdis (hitsOddCycles_of_maxWeightFamily hC D hD')

/-- **THE WEIGHTED ERDŐS–PÓSA THEOREM, second form: the odd cycle transversal number of `G` is at
most the weight of a maximum-weight packing of odd cycles.**  The union of a maximum-weight packing
is a transversal (`hitsOddCycles_of_maxWeightFamily`) and, since the members are pairwise
disjoint, its cardinality is the weight of the packing. -/
theorem closeToBipartite_of_maxWeightPacking [Fintype V] {C : Finset (Finset V)}
    (hC : IsMaxWeightPacking G C) : CloseToBipartite (PackingWeight C) G := by
  classical
  refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := PackingWeight C)).mpr
    ⟨C.biUnion id, ?_, hitsOddCycles_of_maxWeightFamily hC⟩
  -- the members of a packing are pairwise disjoint, so the union counts each vertex once
  have hcov : ∀ ⦃x : V⦄, x ∈ C.biUnion id → ∃ i ∈ C, x ∈ i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact ⟨i, hi, hxi⟩
  have hcard : (C.biUnion id).card = PackingWeight C := by
    have h1 := card_eq_sum_card_inter_of_disjoint hC.1.1 hcov
    have hinter : ∀ i ∈ C, C.biUnion id ∩ i = i := by
      intro i hi
      ext x
      constructor
      · intro hx
        obtain ⟨_, hx2⟩ := Finset.mem_inter.mp hx
        exact hx2
      · intro hx
        exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, hi, hx⟩, hx⟩
    calc (C.biUnion id).card = ∑ i ∈ C, i.card := by
          refine h1.trans (Finset.sum_congr rfl fun i hi => ?_)
          rw [hinter i hi]
      _ = PackingWeight C := rfl
  exact hcard.le

end Weight

/-! ### Instances of the headline theorem from the weighted theorem -/

section Instances

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **The weight of a packing, from a global length bound and a packing number**: if every odd
cycle of `G` has at most `ℓ` vertices and `𝒞` is a packing of at most `r` of them, then `𝒞` covers
at most `ℓ * r` vertices. -/
theorem packingWeight_le {C : Finset (Finset V)} {r ℓ : ℕ} (hC : IsOddCycleFamily (G := G) C)
    (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ) (hcard : C.card ≤ r) :
    PackingWeight C ≤ ℓ * r := by
  have h1 : PackingWeight C ≤ ∑ _D ∈ C, (ℓ : ℕ) :=
    Finset.sum_le_sum fun D hD => hlen D (hC.2 D hD)
  calc PackingWeight C ≤ ∑ _D ∈ C, (ℓ : ℕ) := h1
    _ = ℓ * C.card := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]
        rfl
    _ ≤ ℓ * r := Nat.mul_le_mul_left ℓ hcard

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM: graphs of bounded packing weight.**  If every
packing of odd cycles of `G` covers at most `L` vertices in total, then Erdős's local hypothesis
with parameter `k` forces `G` to be the union of a bipartite graph and `L` vertices.

This is a strictly weaker hypothesis than the `ℓ * k` instance
`JSPProblem.Transversal.erdos73On_of_bounded_odd_girth`, which needs a bound on the length of every
individual odd cycle: here only the total length of a packing is controlled, and neither a bound on
the odd girth nor a bound on the number of branch vertices is used. -/
theorem erdos73On_of_bounded_packing_weight (k L : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W),
      LocIndep k G → (∀ C : Finset (Finset W), IsOddCycleFamily (G := G) C → PackingWeight C ≤ L) →
        CloseToBipartite L G := by
  intro W instW G hG hw
  exact closeToBipartite_of_weightLe (W := W) (instW := instW) (L := L) G hw

/-- **The `ℓ * k` instance of the headline theorem, re-derived from the weighted theorem.**  A
graph all of whose odd cycles have at most `ℓ` vertices, satisfying `LocIndep k`, is the union of a
bipartite graph and `ℓ * k` vertices.  (The instance itself is
`JSPProblem.Transversal.erdos73On_of_bounded_odd_girth`; here it appears as a *corollary of the
weighted Erdős–Pósa theorem*, since every packing then has weight at most `ℓ * k`.) -/
theorem erdos73On_of_bounded_odd_circumference (k ℓ : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W),
      LocIndep k G → (∀ C, IsOddCycle G C → C.card ≤ ℓ) → CloseToBipartite (ℓ * k) G := by
  intro W instW G hG hlen
  exact erdos73On_of_bounded_packing_weight k (ℓ * k) W instW G hG (fun C hC =>
    packingWeight_le hC hlen (hG.oddCycleFamily_card_le hC))

/-- **The residue of `X` is the induced subgraph on the vertices outside `X`**, stated with the
ambient `Finset.univ` so that no `DecidableEq` instance is fixed in the statement. -/
theorem deleteFinset_eq_induceFinset (X : Finset V) :
    deleteFinset G X = induceFinset G ((Finset.univ : Finset V) \ X) := rfl

/-- **On complete graphs the conclusion of Erdős Problem #73 is exact**: deleting at most `m`
vertices of `K_n` leaves a bipartite graph exactly when `n ≤ m + 2`, because a complete graph is
bipartite exactly when it has at most two vertices. -/
theorem closeToBipartite_iff_completeGraph_add_two (m n : ℕ) :
    CloseToBipartite m (SimpleGraph.completeGraph (Fin n)) ↔ n ≤ m + 2 := by
  constructor
  · rintro ⟨X, hX, hbip⟩
    by_contra hn
    have hcard : ((Finset.univ : Finset (Fin n)) \ X).card = n - X.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_fin]
    have h3' : 3 ≤ n - X.card := by omega
    have h3 : 3 ≤ ((Finset.univ : Finset (Fin n)) \ X).card := by
      rw [hcard]
      exact h3'
    rw [deleteFinset_eq_induceFinset] at hbip
    exact not_isBipartite_induceFinset_of_clique
      (G := SimpleGraph.completeGraph (Fin n)) (X := Finset.univ \ X)
      (fun x _ y _ hne => SimpleGraph.top_adj x y |>.mpr hne) h3 hbip
  · intro hn
    by_cases hsmall : n ≤ 2
    · refine ⟨∅, Nat.zero_le _, ?_⟩
      rw [deleteFinset_eq_induceFinset, Finset.sdiff_empty]
      exact isBipartite_induceFinset_of_card_le_two (by rw [Finset.card_fin]; exact hsmall)
    · have h3n : 3 ≤ n := by omega
      have hv : (⟨0, by omega⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin n) := by
        intro he
        have hval := congrArg Fin.val he
        simp only at hval
        omega
      have hcard2 : (({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n))).card = 2 := by simp
      refine ⟨(Finset.univ : Finset (Fin n)) \ (({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n))), ?_, ?_⟩
      · have hcard : ((Finset.univ : Finset (Fin n))
            \ (({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n)))).card = n - 2 := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_fin, hcard2]
        rw [hcard]
        omega
      · have hsub : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n))
            ⊆ (Finset.univ : Finset (Fin n)) := fun x _ => Finset.mem_univ x
        have hres : (Finset.univ \ (Finset.univ \ (({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n)))
            : Finset (Fin n))) = ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n)) :=
          Finset.sdiff_sdiff_eq_self hsub
        rw [deleteFinset_eq_induceFinset, hres]
        exact isBipartite_induceFinset_of_card_le_two (by rw [hcard2])

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, in a sharp form: on complete graphs the value of
Erdős's constant is exactly `k`.**  `LocIndep k (K_n)` forces `n ≤ k + 2` (the clique obstruction
`JSPProblem.LocIndep.clique_card_le`), and `K_{k+2}` is `k`-close to bipartite but is not
`m`-close to bipartite for any `m < k`.  Together with `JSPProblem.Sharp.no_constant_below_k` this pins down the lower
bound `f(k) ≥ k` from two different witnesses. -/
theorem erdos73On_completeGraph (k : ℕ) (n : ℕ)
    (hG : LocIndep k (SimpleGraph.completeGraph (Fin n))) :
    n ≤ k + 2 ∧ CloseToBipartite k (SimpleGraph.completeGraph (Fin (k + 2))) ∧
      (∀ m, m < k → ¬ CloseToBipartite m (SimpleGraph.completeGraph (Fin (k + 2)))) := by
  have hcl : (SimpleGraph.completeGraph (Fin n) : SimpleGraph (Fin n)).IsClique
      (Finset.univ : Finset (Fin n)) := by
    rw [SimpleGraph.isClique_iff]
    intro x _ y _ hne
    exact SimpleGraph.top_adj x y |>.mpr hne
  have hle := hG.clique_card_le hcl
  rw [Finset.card_fin] at hle
  refine ⟨hle, ?_, ?_⟩
  · exact (closeToBipartite_iff_completeGraph_add_two k (k + 2)).mpr (by omega)
  · intro m hm hnot
    rw [closeToBipartite_iff_completeGraph_add_two m (k + 2)] at hnot
    omega

end Instances

/-! ### The naive absorption step is false: the machine-checked witness `K_5` -/

section Absorption

/-- **A residue of at most two vertices is bipartite**: if at most two vertices are deleted from a
graph on `n` vertices, the residue is bipartite, and it is not a multiple of the `DecidableEq`
instance which is in scope. -/
theorem isBipartite_deleteFinset_of_card_le_two {n : ℕ} {H : SimpleGraph (Fin n)} (X : Finset (Fin n))
    (h2 : n - X.card ≤ 2) : (deleteFinset H X).IsBipartite := by
  have hcard : ((Finset.univ : Finset (Fin n)) \ X).card = n - X.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_fin]
  have hle : ((Finset.univ : Finset (Fin n)) \ X).card ≤ 2 := by
    rw [hcard]
    exact h2
  rw [deleteFinset_eq_induceFinset]
  exact isBipartite_induceFinset_of_card_le_two hle

/-- **`K_5` minus a triangle is bipartite**, since two vertices are left. -/
theorem isBipartite_deleteFinset_completeGraph_five :
    (deleteFinset (SimpleGraph.completeGraph (Fin 5)) {0, 1, 2}).IsBipartite :=
  isBipartite_deleteFinset_of_card_le_two (H := SimpleGraph.completeGraph (Fin 5))
    (X := {0, 1, 2}) (by
      have h1 : (0 : Fin 5) ∉ ({(1 : Fin 5), 2} : Finset (Fin 5)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
        omega
      have h2 : (1 : Fin 5) ∉ ({(2 : Fin 5)} : Finset (Fin 5)) := by
        simp only [Finset.mem_singleton, Fin.ext_iff]
        omega
      have hcard : ({0, 1, 2} : Finset (Fin 5)).card = 3 := by
        rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
          show ({(2 : Fin 5)} : Finset (Fin 5)) = insert 2 ∅ from rfl,
          Finset.card_insert_of_notMem (by simp), Finset.card_empty]
      omega)

/-- **The residue of a triangle of `K_5` needs no modification at all**:
`CloseToBipartite 0 (K_5 - {0,1,2})`.  This is the hypothesis of the naive absorption step with
`q = 0`. -/
theorem closeToBipartite_zero_deleteFinset_completeGraph_five :
    CloseToBipartite 0 (deleteFinset (SimpleGraph.completeGraph (Fin 5)) {0, 1, 2}) :=
  ⟨∅, Nat.zero_le _, by
    rw [deleteFinset_empty]
    exact isBipartite_deleteFinset_completeGraph_five⟩

/-- **Membership in the triangle of `K_5`**: `x ∈ {0, 1, 2}` exactly when `x < 3`. -/
theorem mem_triangle_five (x : Fin 5) : x ∈ ({0, 1, 2} : Finset (Fin 5)) ↔ x.val < 3 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

/-- **A triangle is an odd cycle of `K_5`**: `{0,1,2}` is a 3-cycle, and it is the odd cycle whose
residue is bipartite in `absorption_step_fails` below. -/
theorem isOddCycle_completeGraph_five_triangle :
    IsOddCycle (SimpleGraph.completeGraph (Fin 5)) {0, 1, 2} := by
  set f0 : Fin 3 → Fin 5 := fun j => ⟨j.val, by omega⟩
  refine ⟨3, f0, by decide, by decide, ?_, ?_, ?_⟩
  · intro a b hab
    have hval := congrArg Fin.val hab
    simp only [f0] at hval
    exact Fin.val_injective hval
  · intro j
    have hjv := j.isLt
    refine SimpleGraph.top_adj _ _ |>.mpr ?_
    intro he
    have hval := congrArg Fin.val he
    simp only [f0, cycSucc] at hval
    omega
  · intro x
    constructor
    · intro hx
      have hx' := (mem_triangle_five x).mp hx
      refine ⟨⟨x.val, by omega⟩, ?_⟩
      show (⟨x.val, by omega⟩ : Fin 5) = x
      exact Fin.eta x x.isLt
    · intro hx
      obtain ⟨j, hj⟩ := hx
      have hjv := j.isLt
      refine (mem_triangle_five x).mpr ?_
      rw [← hj]
      simp only [f0]
      omega



/-- **`K_5` is not one vertex away from bipartite**: deleting at most one vertex of `K_5` leaves a
complete graph on at least four vertices, which is not bipartite
(`not_isBipartite_induceFinset_of_clique`). -/
theorem not_closeToBipartite_one_completeGraph_five :
    ¬ CloseToBipartite 1 (SimpleGraph.completeGraph (Fin 5)) := by
  rintro ⟨X, hX, hbip⟩
  have hcard : ((Finset.univ : Finset (Fin 5)) \ X).card = 5 - X.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), Finset.card_fin]
  have h3' : 3 ≤ 5 - X.card := by omega
  have h3 : 3 ≤ ((Finset.univ : Finset (Fin 5)) \ X).card := by
    rw [hcard]
    exact h3'
  rw [deleteFinset_eq_induceFinset] at hbip
  exact not_isBipartite_induceFinset_of_clique
    (G := SimpleGraph.completeGraph (Fin 5)) (X := Finset.univ \ X)
    (fun x _ y _ hne => SimpleGraph.top_adj x y |>.mpr hne) h3 hbip

/-- **THE ABSORPTION STEP IS FALSE AS STATED — the machine-checked reason the residue induction of
`JSPProblem/Residue.lean` pays `+ |C|` and not `+ 1`.**

The step the classical proof needs is

```
CloseToBipartite q (G - C)  →  CloseToBipartite (q + 1) G     (C an odd cycle of G)
```

and it is **false**: take `G = K_5` and `C = {0,1,2}`, a triangle.  Then `G - C` is `K_2`, hence
bipartite, so the hypothesis holds with `q = 0`
(`closeToBipartite_zero_deleteFinset_completeGraph_five`), but `G = K_5` is not `1`-close to
bipartite (`not_closeToBipartite_one_completeGraph_five`) — its odd cycle transversal number is
`3`.  So any absorption lemma must carry a hypothesis: at a shortest odd cycle of length `≥ 5` an
outside vertex meets the cycle in at most two vertices (`JSPProblem.card_inter_neigh_le_two`,
`JSPProblem/Fan.lean`), whereas in `K_5` every outside vertex meets the triangle in all
three of its vertices, and that is exactly what defeats the step.  This is the concrete form of
the blocker recorded in `discovery/JSP-000090/policy.json`. -/
theorem absorption_step_fails :
    ¬ (CloseToBipartite 0 (deleteFinset (SimpleGraph.completeGraph (Fin 5)) {0, 1, 2}) →
        CloseToBipartite 1 (SimpleGraph.completeGraph (Fin 5))) :=
  fun h => not_closeToBipartite_one_completeGraph_five
    (h closeToBipartite_zero_deleteFinset_completeGraph_five)

/-- **`K_5` satisfies Erdős's local hypothesis with `k = 3`** (`JSP90.completeGraph_locIndep`), so
the failure above happens *inside* the range of the headline theorem, and not on a graph excluded by
it. -/
theorem locIndep_completeGraph_five_three : LocIndep 3 (SimpleGraph.completeGraph (Fin 5)) :=
  completeGraph_locIndep 3

end Absorption

end

end JSP90
