/-
# JSP-000090 — odd-cycle packings under Erdős's local hypothesis

Erdős Problem #73 (Reed 1999) says that a graph in which every subgraph has an independent set of
size `≥ (|V| - k) / 2` is the union of a bipartite graph and `O_k(1)` vertices.  Equivalently: the
number of vertices that must be deleted to make `G` bipartite (the *odd cycle transversal number*)
is bounded in terms of `k`.

The classical route to that conclusion runs through **odd cycle packings**: a *packing* is a family
of pairwise vertex-disjoint odd cycles, and Erdős's local hypothesis bounds how many of them there
can be.  This file proves that half, in the form

* `card_eq_sum_card_inter_of_disjoint` — cardinality is additive over a disjoint family that covers
  a set (the bookkeeping lemma);
* `indep_card_le_of_odd_cycle` (from `JSPProblem.OddCycle`) gives `2 * |S ∩ C| + 1 ≤ |C|` for every
  independent set `S` and every odd cycle `C` of `G`;
* `LocIndep.oddCycle_packing_le` — **at most `k` vertex-disjoint odd cycles**, i.e.
  `2 * |S| + r ≤ |⋃ C|` for `r` disjoint odd cycles and `|S| ≥ (|⋃ C| - k) / 2`.

The complementary half — "a bounded packing number forces a bounded odd cycle transversal" — is the
Erdős–Pósa theorem for odd cycles (Reed, Robertson, Seymour, Thomas, *J. Combin. Theory Ser. B*
2003), which Mathlib does not have in any form.  See `discovery/JSP-000090/policy.json`.
-/

import JSPProblem.OddCycle
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance : DecidableEq V := Classical.decEq V

section Sum

/-- A family `C` of finsets is **vertex-disjoint** if any two distinct members are disjoint. -/
def DisjointFamily (C : Finset (Finset V)) : Prop :=
  ∀ X ∈ C, ∀ Y ∈ C, X ≠ Y → X ∩ Y = ∅

/-- **Additivity over a disjoint family.**  If the members of `C` are pairwise disjoint and every
element of `S` lies in one of them, then `S` is the disjoint union of the pieces `S ∩ i`, so
`|S| = ∑ i ∈ C, |S ∩ i|`. -/
theorem card_eq_sum_card_inter_of_disjoint {C : Finset (Finset V)} {S : Finset V}
    (hC : DisjointFamily C) (hcov : ∀ ⦃x : V⦄, x ∈ S → ∃ i ∈ C, x ∈ i) :
    S.card = ∑ i ∈ C, (S ∩ i).card := by
  classical
  induction C using Finset.induction_on generalizing S with
  | empty =>
      have hS0 : S = ∅ := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hi, -⟩ := hcov hx
          exact absurd hi (by simpa using hi)
        · intro hx
          exact absurd hx (by simp)
      rw [hS0, Finset.card_empty]
      simp
  | @insert a t ha ih =>
      have hne : ∀ b ∈ t, a ≠ b := by
        intro b hb hab
        subst hab
        exact ha hb
      have hat : ∀ b ∈ t, a ∩ b = ∅ :=
        fun b hb => hC a (Finset.mem_insert_self a t) b (Finset.mem_insert_of_mem hb) (hne b hb)
      have hnot : ∀ (b : Finset V) (hb : b ∈ t) ⦃x : V⦄, x ∈ b → x ∉ a := by
        intro b hb x hxb hxa
        have hempty : x ∈ (a ∩ b) := Finset.mem_inter.mpr ⟨hxa, hxb⟩
        rw [hat b hb] at hempty
        simp at hempty
      have hdisj : Disjoint (S ∩ a) (S \ a) := by
        refine Finset.disjoint_left.mpr fun x hx hx2 => ?_
        obtain ⟨hx1, hx2'⟩ := Finset.mem_inter.mp hx
        obtain ⟨_, hna⟩ := Finset.mem_sdiff.mp hx2
        exact hna hx2'
      have hsplit : S.card = (S ∩ a).card + (S \ a).card := by
        have hsub : S = (S ∩ a) ∪ (S \ a) := by
          ext x
          constructor
          · intro hx
            by_cases hxa : x ∈ a
            · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, hxa⟩))
            · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxa⟩))
          · intro hx
            obtain hx | hx := Finset.mem_union.mp hx
            · exact (Finset.mem_inter.mp hx).1
            · exact (Finset.mem_sdiff.mp hx).1
        calc S.card = ((S ∩ a) ∪ (S \ a)).card := congrArg Finset.card hsub
          _ = (S ∩ a).card + (S \ a).card := Finset.card_union_of_disjoint hdisj
      have hcov' : ∀ ⦃x : V⦄, x ∈ S \ a → ∃ i ∈ t, x ∈ i := by
        intro x hx
        obtain ⟨hxS, hna⟩ := Finset.mem_sdiff.mp hx
        obtain ⟨i, hi, hxi⟩ := hcov hxS
        rw [Finset.mem_insert] at hi
        rcases hi with hi' | hi
        · subst hi'
          exact absurd hxi hna
        · exact ⟨i, hi, hxi⟩
      have hDt : DisjointFamily t := fun X hX Y hY hXY =>
        hC X (Finset.mem_insert_of_mem hX) Y (Finset.mem_insert_of_mem hY) hXY
      have hrec := ih hDt hcov'
      have hcongr : (∑ i ∈ t, ((S \ a) ∩ i).card) = ∑ i ∈ t, (S ∩ i).card := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have heq : S \ a ∩ i = S ∩ i := by
          ext x
          constructor
          · intro hx
            obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
            exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hx1).1, hx2⟩
          · intro hx
            obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
            exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hx1, hnot i hi hx2⟩, hx2⟩
        rw [heq]
      have hsum : (∑ i ∈ insert a t, (S ∩ i).card) = (S ∩ a).card + ∑ i ∈ t, (S ∩ i).card :=
        Finset.sum_insert ha
      rw [hsum, hsplit, hrec, hcongr]

end Sum

section Packing

/-- **A family of vertex-disjoint odd cycles of `G`.**  `C` is a set of finsets which are pairwise
vertex-disjoint, and each member is carried by a cyclic ordering `f : Fin m → V` of odd length
`m ≥ 3` in which consecutive vertices (cyclically) are adjacent; `C.card` is the *packing number*
of the family.

The *odd cycle transversal number* of `G` is by definition the least number of vertices meeting
every odd cycle of `G`, i.e. the least `m` with `CloseToBipartite m G`; Erdős Problem #73 asserts
that it is bounded in terms of `k` whenever `LocIndep k G` holds. -/
def IsOddCyclePacking (C : Finset (Finset V)) : Prop :=
  DisjointFamily C ∧
    ∀ X ∈ C, ∃ (m : ℕ) (f : Fin m → V), m % 2 = 1 ∧ 3 ≤ m ∧ Function.Injective f ∧
      (∀ j : Fin m, G.Adj (f j) (f (cycSucc j))) ∧ ∀ x : V, x ∈ X ↔ ∃ j : Fin m, f j = x

/-- **Independent sets lose one vertex per odd cycle of a packing.**
If `C` is a family of pairwise vertex-disjoint odd cycles of `G` and `T` is an independent set
inside the union of `C`, then `2 * |T| + |C| ≤ |⋃ C|`.

Indeed each odd cycle `C i` of the family satisfies `2 * |T ∩ C i| + 1 ≤ |C i|`, and the cycles are
disjoint, so the union of `C` has at least `2 * |T| + |C|` vertices.  This counting statement is the
"packing" half of the Erdős–Pósa strategy for Erdős Problem #73; it is unconditional, and
`LocIndep.oddCycle_packing_le` below is the consequence for the local hypothesis. -/
theorem packing_ineq [Fintype V] {C : Finset (Finset V)} (hpack : IsOddCyclePacking (G := G) C)
    (T : Finset V)
    (hTi : G.IsIndepSet T) (hTsub : T ⊆ C.biUnion id) :
    2 * T.card + C.card ≤ (C.biUnion id).card := by
  classical
  obtain ⟨hdisj, hcycl⟩ := hpack
  -- the union of the family of cycles
  set U : Finset V := C.biUnion id with hUdef
  have hcovU : ∀ ⦃x : V⦄, x ∈ U → ∃ i ∈ C, x ∈ i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact ⟨i, hi, hxi⟩
  have hcardU : U.card = ∑ i ∈ C, i.card := by
    refine card_eq_sum_card_inter_of_disjoint hdisj hcovU |>.trans ?_
    refine Finset.sum_congr rfl fun i hi => ?_
    have hsub : i ⊆ U := fun x hx => Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
    have heq : U ∩ i = i := by
      ext x
      constructor
      · intro hx
        obtain ⟨_, hx2⟩ := Finset.mem_inter.mp hx
        exact hx2
      · intro hx
        exact Finset.mem_inter.mpr ⟨hsub hx, hx⟩
    exact congrArg Finset.card heq
  -- the independent set splits over the disjoint family
  have hTsub' : T ⊆ U := hTsub
  have hTsum : T.card = ∑ i ∈ C, (T ∩ i).card := by
    refine card_eq_sum_card_inter_of_disjoint hdisj fun x hx => ?_
    exact hcovU (hTsub' hx)
  -- every cycle has at least one vertex more than the independent set meets
  have hpart : ∀ i ∈ C, 2 * (T ∩ i).card + 1 ≤ i.card := by
    intro i hi
    obtain ⟨m, f, hm, hm3, hinj, hcyc, hXi⟩ := hcycl i hi
    have hXim : i = (Finset.univ : Finset (Fin m)).image f := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, hj⟩ := (hXi x).mp hx
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
      · intro hx
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
        exact (hXi x).mpr ⟨j, hj⟩
    have hXcard : i.card = m := by
      rw [hXim, Finset.card_image_of_injective _ hinj]
      simp
    have hSind : G.IsIndepSet ↑(T ∩ i) := by
      refine IsIndepSet.subset hTi fun x hx => ?_
      exact (Finset.mem_inter.mp hx).1
    have hSin : ∀ ⦃x : V⦄, x ∈ T ∩ i → ∃ j : Fin m, f j = x := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      exact (hXi x).mp hx2
    have hle := indep_card_le_of_odd_cycle hm f hinj hcyc (T ∩ i) hSind hSin
    rw [hXcard]
    exact hle
  -- summing the per-cycle bound: 2 * |T| + |C| ≤ |U|
  have h1 : 2 * T.card + C.card = ∑ i ∈ C, (2 * (T ∩ i).card + 1) := by
    calc 2 * T.card + C.card
        = 2 * (∑ i ∈ C, (T ∩ i).card) + ∑ i ∈ C, (1 : ℕ) := by
          rw [hTsum, Finset.card_eq_sum_ones]
      _ = ∑ i ∈ C, (2 * (T ∩ i).card) + ∑ i ∈ C, (1 : ℕ) := by rw [Finset.mul_sum]
      _ = ∑ i ∈ C, (2 * (T ∩ i).card + 1) := by rw [Finset.sum_add_distrib]
  have h2 : (∑ i ∈ C, (2 * (T ∩ i).card + 1)) ≤ ∑ i ∈ C, i.card :=
    Finset.sum_le_sum fun i hi => hpart i hi
  omega

/-- **Erdős's local hypothesis bounds the number of vertex-disjoint odd cycles by `k`.**
If `LocIndep k G` holds and `C` is a family of pairwise vertex-disjoint odd cycles of `G`, then
`|C| ≤ k`: the independent set supplied by the local hypothesis on the union of the cycles loses at
least one vertex per cycle, and the hypothesis only allows a deficit of `k`. -/
theorem LocIndep.oddCycle_packing_le [Fintype V] {k : ℕ} (hG : LocIndep k G) {C : Finset (Finset V)}
    (hpack : IsOddCyclePacking (G := G) C) :
    C.card ≤ k := by
  obtain ⟨T, hTU, hTi, hbnd⟩ := hG (C.biUnion id)
  have h := packing_ineq hpack T hTi hTU
  omega

end Packing

end

end JSP90
