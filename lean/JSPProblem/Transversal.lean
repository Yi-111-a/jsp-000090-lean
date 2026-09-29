/-
# JSP-000090 — odd cycle transversals: the exact Erdős–Pósa step

This file is the bridge between the two halves of the classical route to Erdős Problem #73
(Reed 1999, *Mangoes and Blueberries*, Combinatorica 19 (1999) 267–296).

`JSPProblem/Packing.lean` proved the **packing** half: Erdős's local hypothesis `LocIndep k G`
admits at most `k` pairwise vertex-disjoint odd cycles (`JSP90.LocIndep.oddCycle_packing_le`).
The **transversal** half is what is missing, and this file develops it as far as it goes:

1. **The conclusion, in odd-cycle form.**  `CloseToBipartite m G` is equivalent to the existence of a
   set of at most `m` vertices meeting *every* odd cycle of `G`
   (`closeToBipartite_iff_hitsOddCycles`).  The nontrivial direction is
   `isBipartite_delete_of_hitsOddCycles`: a deletion which kills all odd cycles is bipartite.
2. **A maximal packing is a transversal** (`hitsOddCycles_of_maxCardFamily`): a family of pairwise
   disjoint odd cycles of maximum cardinality meets every odd cycle of `G`.
3. **Erdős–Pósa for graphs of bounded odd girth** (`shortOddCycles_transversal`,
   `shortOddCyclesErdosPosa`): if every odd cycle of `G` has at most `ℓ` vertices, then a packing
   of at most `r` disjoint odd cycles yields a transversal of at most `ℓ * r` vertices.
4. **Hence a new, fully proved instance of the headline theorem**
   (`erdos73On_of_bounded_odd_girth`): if every odd cycle of `G` has at most `ℓ` vertices, then
   `LocIndep k G` forces `CloseToBipartite (ℓ * k) G` — Erdős Problem #73 for graphs of bounded
   odd girth, with the **explicit** constant `f(k) = ℓ * k`.
5. **The remaining research statement, isolated** (`OddCycleErdosPosa`, `erdos73_of_erdosPosa`):
   the whole of `Erdős73` follows from the Erdős–Pósa theorem for odd cycles, and conversely
   `Erdős73` *is* that theorem.  `erdos73_of_erdosPosa` is proved, so `jsp_000090_main` would
   follow from `∀ r, OddCycleErdosPosa r` alone; the `r = 0` instance is proved too
   (`oddCycleErdosPosa_zero`).
6. **Sharpness / a test of the statement** (`closeToBipartite_completeGraph_three`): `K_3`
   satisfies `LocIndep 1` and is *one* vertex away from bipartite.  This is the `k = 1` extremal
   example of Erdős #73 and the test case which the earlier (rejected) formulation of
   `CloseToBipartite` got wrong — see `rejected_reading_fails` and the header of
   `JSPProblem/Definitions.lean`.
-/

import JSPProblem.Packing
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance : DecidableEq V := Classical.decEq V

/-! ### Iterating the cyclic successor -/

section CycPow

/-- **Iterating the cyclic successor.**  `k` steps around the cycle starting at `i` land at index
`(i + k) mod n`. -/
theorem cycSucc_pow_val {n : ℕ} : ∀ (k : ℕ) (i : Fin n),
    ((cycSucc^[k] : Fin n → Fin n) i).val = (i.val + k) % n := by
  intro k
  induction k with
  | zero =>
      intro i
      rw [Function.iterate_zero, id_eq, Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
      intro i
      have h1 : ((cycSucc^[k] : Fin n → Fin n) (cycSucc i)).val = (i.val + 1 + k) % n := by
        rw [ih (cycSucc i), cycSucc_val, Nat.mod_add_mod]
      have h2 : (cycSucc^[k + 1] : Fin n → Fin n) i = (cycSucc^[k] : Fin n → Fin n) (cycSucc i) := by
        simpa using (Function.iterate_add_apply cycSucc k 1 i)
      rw [h2, h1]
      congr 1
      omega

/-- **Going once around a cycle brings you back.** -/
theorem cycSucc_pow {n : ℕ} (i : Fin n) : ((cycSucc^[n] : Fin n → Fin n) i) = i := by
  have h := cycSucc_pow_val (n := n) n i
  have hlt : i.val < n := i.isLt
  have hmod : (i.val + n) % n = i.val := by
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hlt]
  rw [hmod] at h
  exact Fin.ext h

/-- A predicate which **flips** along the cycle: after an even number of steps it has the same value
at the starting vertex, after an odd number of steps the opposite value.  The two cases are proved
simultaneously, since one step switches them. -/
theorem cycSucc_pow_flip {n : ℕ} {P : Fin n → Prop} (hstep : ∀ j : Fin n, P (cycSucc j) ↔ ¬ P j) :
    ∀ k : ℕ, ∀ j : Fin n,
      (k % 2 = 0 → (P ((cycSucc^[k] : Fin n → Fin n) j) ↔ P j)) ∧
      (k % 2 = 1 → (P ((cycSucc^[k] : Fin n → Fin n) j) ↔ ¬ P j)) := by
  have hstep' : ∀ j : Fin n, ¬ P (cycSucc j) ↔ P j := by
    intro j
    have h1 : ¬ P (cycSucc j) ↔ ¬ ¬ P j := not_congr (hstep j)
    simpa only [not_not] using h1
  intro k
  induction k with
  | zero =>
      intro j
      constructor
      · intro _
        simp
      · intro h
        exact absurd h (by omega)
  | succ k ih =>
      intro j
      have hcomp : (cycSucc^[k + 1] : Fin n → Fin n) j = (cycSucc^[k] : Fin n → Fin n) (cycSucc j) := by
        simpa using (Function.iterate_add_apply cycSucc k 1 j)
      rw [hcomp]
      rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
      · constructor
        · intro h
          exact absurd h (by omega)
        · intro _
          exact ((ih (cycSucc j)).1 hk0).trans (hstep j)
      · constructor
        · intro _
          exact ((ih (cycSucc j)).2 hk1).trans (hstep' j)
        · intro h
          exact absurd h (by omega)

/-- A predicate which **flips** along the cycle has the same value at a vertex after an even number
of steps. -/
theorem cycSucc_pow_even {n : ℕ} {P : Fin n → Prop} (hstep : ∀ j : Fin n, P (cycSucc j) ↔ ¬ P j)
    {j : Fin n} {k : ℕ} (hk : k % 2 = 0) : P ((cycSucc^[k] : Fin n → Fin n) j) ↔ P j :=
  (cycSucc_pow_flip hstep k j).1 hk

/-- The odd counterpart of `cycSucc_pow_even`. -/
theorem cycSucc_pow_odd {n : ℕ} {P : Fin n → Prop} (hstep : ∀ j : Fin n, P (cycSucc j) ↔ ¬ P j)
    {j : Fin n} {k : ℕ} (hk : k % 2 = 1) : P ((cycSucc^[k] : Fin n → Fin n) j) ↔ ¬ P j :=
  (cycSucc_pow_flip hstep k j).2 hk

/-- **A proposition is never equivalent to its own negation.** -/
theorem not_iff_self (P : Prop) (h : P ↔ ¬ P) : False := by
  by_cases hp : P
  · exact h.mp hp hp
  · exact hp (h.mpr hp)

end CycPow

/-! ### Odd cycles -/

section OddCycle

/-- `C` is an **odd cycle** of `G`: a cyclic ordering `f : Fin m → V` by an injection, `m` odd and
`m ≥ 3`, whose image is `C` and in which consecutive vertices are adjacent. -/
def IsOddCycle (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ (m : ℕ) (f : Fin m → V), m % 2 = 1 ∧ 3 ≤ m ∧ Function.Injective f ∧
    (∀ j : Fin m, G.Adj (f j) (f (cycSucc j))) ∧ ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x

/-- `X` is an **odd cycle transversal** of `G`: it meets every odd cycle of `G`. -/
def HitsOddCycles (G : SimpleGraph V) (X : Finset V) : Prop :=
  ∀ C : Finset V, IsOddCycle G C → C ∩ X ≠ ∅

/-- A family of **pairwise vertex-disjoint odd cycles** of `G`; `C.card` is its packing number.
`IsOddCycleFamily` is the `IsOddCyclePacking` of `JSPProblem/Packing.lean`, with the cycle condition
factored out. -/
def IsOddCycleFamily (G : SimpleGraph V) (C : Finset (Finset V)) : Prop :=
  DisjointFamily C ∧ ∀ X ∈ C, IsOddCycle G X

theorem isOddCycleFamily_iff (C : Finset (Finset V)) :
    IsOddCycleFamily (G := G) C ↔ IsOddCyclePacking (G := G) C :=
  ⟨fun h => ⟨h.1, fun X hX => h.2 X hX⟩, fun h => ⟨h.1, fun X hX => h.2 X hX⟩⟩

/-- The packing bound of `JSPProblem/Packing.lean` in the new vocabulary. -/
theorem LocIndep.oddCycleFamily_card_le [Fintype V] {k : ℕ} (hG : LocIndep k G)
    {C : Finset (Finset V)} (hC : IsOddCycleFamily (G := G) C) : C.card ≤ k :=
  hG.oddCycle_packing_le ((isOddCycleFamily_iff C).mp hC)

/-- **A cycle lying in the two sides of a bipartition has even length.**  Indeed the predicate
"`f j ∈ s`" flips at each step, and one full turn of an odd number of steps brings it back to `j`. -/
theorem even_of_cycle_in_bipartition {bip : G.IsBipartiteWith s t} {m : ℕ} (hm3 : 3 ≤ m)
    (f : Fin m → V) (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hall : ∀ j : Fin m, f j ∈ s ∪ t) : m % 2 = 0 := by
  by_contra hn
  have hodd : m % 2 = 1 := Nat.mod_two_eq_zero_or_one m |>.resolve_left hn
  have hstep : ∀ j : Fin m, (f (cycSucc j) ∈ s) ↔ ¬ (f j ∈ s) := by
    intro j
    have hadj := hcyc j
    have disj := Set.disjoint_left.mp bip.disjoint
    rcases hall j with hj | hj
    · constructor
      · intro hmem
        intro _
        exact disj hmem (bip.mem_of_mem_adj hj hadj)
      · intro hnp
        exact False.elim (hnp hj)
    · constructor
      · intro _
        intro hmem
        exact disj hmem hj
      · intro _
        exact bip.mem_of_mem_adj' hj hadj.symm
  have h0 : Fin m := ⟨0, by omega⟩
  have hiter := cycSucc_pow_odd (P := fun j => f j ∈ s) hstep (j := h0) (k := m) hodd
  rw [cycSucc_pow] at hiter
  exact not_iff_self _ hiter

/-- **An odd cycle cannot be contained in the two sides of a bipartition**: some vertex of it lies
outside `s ∪ t`. -/
theorem exists_outside_of_oddCycle {bip : G.IsBipartiteWith s t} {C : Finset V}
    (hC : IsOddCycle G C) : ∃ x ∈ C, x ∉ s ∪ t := by
  by_contra hcon
  have hsub : ∀ x ∈ C, x ∈ s ∪ t := fun x hx => by
    by_contra hx'
    exact hcon ⟨x, hx, hx'⟩
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hall : ∀ j : Fin m, f j ∈ s ∪ t := fun j => hsub (f j) ((hCmem (f j)).mpr ⟨j, rfl⟩)
  have heven : m % 2 = 0 := even_of_cycle_in_bipartition (bip := bip) hm3 f hcyc hall
  omega

/-- **A bipartite graph contains no odd cycle.**  This is the second half of the odd-cycle
characterisation of bipartiteness; `JSPProblem/OddCycle.lean` proved the first half ("no odd closed
walk ⇒ bipartite"). -/
theorem not_isOddCycle_of_isBipartite [Fintype V] (h : G.IsBipartite) :
    ¬ ∃ C : Finset V, IsOddCycle G C := by
  obtain ⟨s, t, bip⟩ := SimpleGraph.IsBipartite.exists_isBipartiteWith h
  obtain ⟨-, hdis, hcover⟩ := bipartition_split bip
  have hbip := isBipartiteWith_univ bip hdis
  rintro ⟨C, hC⟩
  obtain ⟨x, hx, hx'⟩ := exists_outside_of_oddCycle (bip := hbip) (C := C) hC
  have hxmem : x ∈ s ∪ (Set.univ \ t : Set V) ∪ t := by
    rw [hcover]
    exact Set.mem_univ x
  exact hx' (hxmem.elim (fun h => Or.inl h) Or.inr)

/-- **The vertex set of a cyclic ordering is an odd cycle**: for `f : Fin m → V` injective, `m` odd,
`m ≥ 3`, with consecutive vertices adjacent, the image `(univ : Finset (Fin m)).image f` is an odd
cycle of the graph in which the adjacencies hold. -/
theorem isOddCycle_image [Fintype V] {H : SimpleGraph V} {m : ℕ} (f : Fin m → V) (hm : m % 2 = 1)
    (hm3 : 3 ≤ m) (hinj : Function.Injective f) (hcyc : ∀ j : Fin m, H.Adj (f j) (f (cycSucc j))) :
    IsOddCycle H ((Finset.univ : Finset (Fin m)).image f) := by
  refine ⟨m, f, hm, hm3, hinj, hcyc, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
    exact ⟨j, hj⟩
  · rintro ⟨j, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- **The other half of the odd-cycle characterisation of bipartiteness**: a graph with no odd cycle
is bipartite.  Together with `not_isOddCycle_of_isBipartite` this closes, in this development, the
`TODO` listed in the header of `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` at the pinned
revision (`G.IsBipartite` iff `G` contains no odd cycle). -/
theorem isBipartite_of_no_oddCycle [Fintype V] (h : ¬ ∃ C : Finset V, IsOddCycle G C) :
    G.IsBipartite := by
  by_contra hn
  obtain ⟨w, p, hmod⟩ := exists_odd_closed_walk_of_not_bipartite (G := G) hn
  obtain ⟨m, f, hm, hm3, hinj, hcyc⟩ := exists_odd_cycle_inj
    (G := G) p.length w w p rfl rfl hmod
  exact h ⟨(Finset.univ : Finset (Fin m)).image f, isOddCycle_image f hm hm3 hinj hcyc⟩

/-- **An odd cycle of `G` avoiding `X` survives in the deletion `deleteFinset G X`.** -/
theorem isOddCycle_delete_of_oddCycle_avoiding [Fintype V] {X : Finset V} {C : Finset V}
    (hC : IsOddCycle G C) (hdis : C ∩ X = ∅) :
    ∃ C' : Finset V, IsOddCycle (deleteFinset G X) C' ∧ C' ∩ X = ∅ := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hfnx : ∀ j : Fin m, f j ∉ X := by
    intro j
    intro hx
    have hmemC : f j ∈ C := (hCmem (f j)).mpr ⟨j, rfl⟩
    have hmemI : f j ∈ C ∩ X := Finset.mem_inter.mpr ⟨hmemC, hx⟩
    rw [hdis] at hmemI
    exact absurd hmemI (by simp)
  have hfadj : ∀ j : Fin m, (deleteFinset G X).Adj (f j) (f (cycSucc j)) :=
    fun j => deleteFinset_adj.mpr ⟨hfnx j, hfnx (cycSucc j), hcyc j⟩
  refine ⟨(Finset.univ : Finset (Fin m)).image f, isOddCycle_image f hm hm3 hinj hfadj, ?_⟩
  refine (Finset.disjoint_iff_inter_eq_empty).mp (Finset.disjoint_left.mpr fun _ hxA hxX => ?_)
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hxA
  exact (hj ▸ hfnx j) hxX

/-- **An odd cycle of the deletion `deleteFinset G X` is an odd cycle of `G` avoiding `X`.** -/
theorem oddCycle_of_isOddCycle_delete [Fintype V] {X : Finset V} {C' : Finset V}
    (hC' : IsOddCycle (deleteFinset G X) C') :
    ∃ C : Finset V, IsOddCycle G C ∧ C ∩ X = ∅ := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, -⟩ := hC'
  have hfadj : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)) := fun j => hcyc j |>.2.2
  refine ⟨(Finset.univ : Finset (Fin m)).image f, isOddCycle_image f hm hm3 hinj hfadj, ?_⟩
  refine (Finset.disjoint_iff_inter_eq_empty).mp (Finset.disjoint_left.mpr fun x hxA hxX => ?_)
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hxA
  exact (hj ▸ (deleteFinset_adj.mp (hcyc j)).1) hxX

/-- **A set of vertices meeting every odd cycle makes the deletion bipartite.**  Formally: if no odd
cycle of `G` survives the deletion of `X`, then `deleteFinset G X` is bipartite.

This is the direction needed to read the conclusion of Erdős #73 as "delete a bounded number of
vertices and be left with a bipartite graph". -/
theorem isBipartite_delete_of_hitsOddCycles [Fintype V] {X : Finset V} (hX : HitsOddCycles G X) :
    (deleteFinset G X).IsBipartite := by
  by_contra hn
  obtain ⟨w, p, hmod⟩ := exists_odd_closed_walk_of_not_bipartite (G := deleteFinset G X) hn
  obtain ⟨m, f, hm, hm3, hinj, hcyc⟩ := exists_odd_cycle_inj
    (G := deleteFinset G X) p.length w w p rfl rfl hmod
  obtain ⟨C, hC, hd⟩ := oddCycle_of_isOddCycle_delete (G := G) (X := X)
    (isOddCycle_image f hm hm3 hinj hcyc)
  exact hX C hC hd

/-- Conversely, a deletion which is bipartite leaves no odd cycle behind. -/
theorem hitsOddCycles_of_isBipartite_delete [Fintype V] {X : Finset V}
    (hb : (deleteFinset G X).IsBipartite) : HitsOddCycles G X := by
  intro C hC hdis
  obtain ⟨C', hC', -⟩ := isOddCycle_delete_of_oddCycle_avoiding (G := G) (X := X) hC hdis
  exact not_isOddCycle_of_isBipartite (G := deleteFinset G X) hb ⟨C', hC'⟩

end OddCycle

/-! ### Transversals of odd cycles -/

section Transversal

/-- **The conclusion of Erdős #73 in odd-cycle form.**  `G` is the union of a bipartite graph and at
most `m` vertices **iff** some set of at most `m` vertices meets every odd cycle of `G`. -/
theorem closeToBipartite_iff_hitsOddCycles [Fintype V] {m : ℕ} :
    CloseToBipartite m G ↔ ∃ X : Finset V, X.card ≤ m ∧ HitsOddCycles G X := by
  constructor
  · rintro ⟨X, hX, hb⟩
    exact ⟨X, hX, hitsOddCycles_of_isBipartite_delete hb⟩
  · rintro ⟨X, hX, h⟩
    exact ⟨X, hX, isBipartite_delete_of_hitsOddCycles h⟩

/-- A packing of odd cycles of maximum cardinality exists. -/
theorem exists_maxCard_oddCycleFamily [Fintype V] :
    ∃ C : Finset (Finset V), IsOddCycleFamily (G := G) C ∧
      ∀ D, IsOddCycleFamily (G := G) D → D.card ≤ C.card := by
  classical
  have hne : ((Finset.univ : Finset (Finset (Finset V))).filter
      (IsOddCycleFamily (G := G))).Nonempty :=
    (Finset.filter_nonempty_iff).mpr ⟨∅, Finset.mem_univ _,
      ⟨fun _ hX _ _ hXY => absurd hX (by simp), fun _ hX => absurd hX (by simp)⟩⟩
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Finset (Finset V))).filter (IsOddCycleFamily (G := G)))
    Finset.card hne
  exact ⟨C, (Finset.mem_filter.mp hC).2,
    fun D hD => hmax D (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hD⟩)⟩

/-- **A maximum packing of odd cycles meets every odd cycle.**  If some odd cycle missed the union of
the packing, it could be added to the packing, contradicting maximality. -/
theorem hitsOddCycles_of_maxCardFamily {C : Finset (Finset V)} (hC : IsOddCycleFamily (G := G) C)
    (hmax : ∀ D, IsOddCycleFamily (G := G) D → D.card ≤ C.card) :
    HitsOddCycles G (C.biUnion id) := by
  classical
  intro D hD hdis
  have hD' : IsOddCycle G D := hD
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  have hne : D.Nonempty := ⟨f ⟨0, by omega⟩, (hmem (f ⟨0, by omega⟩)).mpr ⟨⟨0, by omega⟩, rfl⟩⟩
  have hdis' : Disjoint D (C.biUnion id) := (Finset.disjoint_iff_inter_eq_empty).mpr hdis
  -- the odd cycle `D` cannot be one of the packed cycles: it misses their union but is nonempty
  have hDmem : D ∉ C := by
    intro hDin
    obtain ⟨x, hx⟩ := hne
    exact Finset.disjoint_left.mp hdis' hx (Finset.mem_biUnion.mpr ⟨D, hDin, hx⟩)
  have hnew : IsOddCycleFamily (G := G) (insert D C) := by
    refine ⟨?_, ?_⟩
    · intro X hX Y hY hXY
      have hX' : X = D ∨ X ∈ C := Finset.mem_insert.mp hX
      have hY' : Y = D ∨ Y ∈ C := Finset.mem_insert.mp hY
      rcases hX' with hXD | hXc
      · rcases hY' with hYD | hYc
        · exact absurd (hXD.trans hYD.symm) hXY
        · refine (Finset.disjoint_iff_inter_eq_empty).mp (Finset.disjoint_left.mpr ?_)
          intro a haX haY
          exact Finset.disjoint_left.mp hdis' (hXD ▸ haX) (Finset.mem_biUnion.mpr ⟨Y, hYc, haY⟩)
      · rcases hY' with hYD | hYc
        · refine (Finset.disjoint_iff_inter_eq_empty).mp (Finset.disjoint_left.mpr ?_)
          intro a haX haY
          exact Finset.disjoint_left.mp hdis' (hYD ▸ haY) (Finset.mem_biUnion.mpr ⟨X, hXc, haX⟩)
        · exact hC.1 X hXc Y hYc hXY
    · intro X hX
      have hX' : X = D ∨ X ∈ C := Finset.mem_insert.mp hX
      rcases hX' with hXD | hXc
      · exact hXD ▸ hD'
      · exact hC.2 X hXc
  have hcard := hmax (insert D C) hnew
  have hcard' : (insert D C).card = C.card + 1 := Finset.card_insert_of_notMem hDmem
  rw [hcard'] at hcard
  omega

/-- **Erdős–Pósa for odd cycles of bounded length.**  If every odd cycle of `G` has at most `ℓ`
vertices, then a packing of at most `r` disjoint odd cycles yields a transversal of at most `ℓ * r`
vertices. -/
theorem shortOddCycles_transversal (r ℓ : ℕ) [Fintype V]
    (hbound : ∀ C, IsOddCycleFamily (G := G) C → C.card ≤ r)
    (hlen : ∀ C, IsOddCycle G C → C.card ≤ ℓ) :
    ∃ X : Finset V, X.card ≤ ℓ * r ∧ HitsOddCycles G X := by
  classical
  obtain ⟨C, hC, hmax⟩ := exists_maxCard_oddCycleFamily (G := G)
  have hle : C.card ≤ r := hbound C hC
  have hcov : ∀ ⦃x : V⦄, x ∈ C.biUnion id → ∃ i ∈ C, x ∈ i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact ⟨i, hi, hxi⟩
  have hcard : (C.biUnion id).card ≤ ℓ * C.card := by
    have hsum := card_eq_sum_card_inter_of_disjoint hC.1 hcov
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
          refine hsum.trans (Finset.sum_congr rfl fun i hi => ?_)
          rw [hinter i hi]
      _ ≤ ∑ _i ∈ C, (ℓ : ℕ) := Finset.sum_le_sum fun i hi => by
            exact hlen i (hC.2 i hi)
      _ = ℓ * C.card := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]
            rfl
  exact ⟨C.biUnion id, hcard.trans (Nat.mul_le_mul_left ℓ hle),
    hitsOddCycles_of_maxCardFamily hC hmax⟩

/-- **Erdős–Pósa for odd cycles in graphs of bounded odd girth**, packaged: a packing of at most `r`
disjoint odd cycles bounds the transversal by `ℓ * r` whenever odd cycles have at most `ℓ` vertices. -/
def ShortOddCyclesErdosPosa (r : ℕ) : Prop :=
  ∀ (ℓ : ℕ) (W : Type*) (_ : Fintype W) (G : SimpleGraph W),
    (∀ C, IsOddCycleFamily (G := G) C → C.card ≤ r) →
    (∀ C, IsOddCycle G C → C.card ≤ ℓ) → CloseToBipartite (ℓ * r) G

theorem shortOddCyclesErdosPosa (r : ℕ) : ShortOddCyclesErdosPosa r := by
  intro ℓ W instW G hbound hlen
  obtain ⟨X, hX, hhits⟩ := shortOddCycles_transversal (G := G) r ℓ hbound hlen
  exact (closeToBipartite_iff_hitsOddCycles (G := G)).mpr ⟨X, hX, hhits⟩

/-- **A new instance of Erdős Problem #73: graphs of bounded odd girth.**
If every odd cycle of `G` has at most `ℓ` vertices, then Erdős's local hypothesis with parameter `k`
forces `G` to be the union of a bipartite graph and at most `ℓ * k` vertices — i.e. Erdős #73 holds
for the whole class of graphs with odd girth at most `ℓ`, with the explicit constant `f(k) = ℓ * k`. -/
theorem erdos73On_of_bounded_odd_girth (k ℓ : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W),
      LocIndep k G → (∀ C, IsOddCycle G C → C.card ≤ ℓ) → CloseToBipartite (ℓ * k) G := by
  intro W instW G hG hlen
  exact shortOddCyclesErdosPosa k ℓ W instW G
    (fun C hC => hG.oddCycleFamily_card_le hC) hlen

end Transversal

/-! ### The remaining research statement: Erdős–Pósa for odd cycles -/

section ErdosPosa

universe u

/-- **The Erdős–Pósa theorem for odd cycles** (Reed, Robertson, Seymour, Thomas, *Erdős–Pósa for
odd cycles*, J. Combin. Theory Ser. B 86 (2002) 99–136), in the form needed for JSP-000090: for
every `r` there is `m` such that every graph whose odd cycle packings all have at most `r` members
is the union of a bipartite graph and `m` vertices.

Everything else in JSP-000090 is proved: the packing half (`JSPProblem/Packing.lean`) and the
bounded-odd-girth transversal half (`shortOddCycles_transversal` above). -/
def OddCycleErdosPosa (r : ℕ) : Prop :=
  ∃ m : ℕ, ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
    (∀ C, IsOddCycleFamily (G := G) C → C.card ≤ r) → CloseToBipartite m G

/-- **The whole of Erdős Problem #73 follows from the Erdős–Pósa theorem for odd cycles.**  So
`jsp_000090_main` reduces to the single statement `∀ r, OddCycleErdosPosa r`. -/
theorem erdos73_of_erdosPosa (hEP : ∀ r, OddCycleErdosPosa.{u} r) : ∀ k, Erdős73.{u} k := by
  intro k
  obtain ⟨m, hm⟩ := hEP k
  exact ⟨m, fun W instW G hG => hm W instW G fun C hC => hG.oddCycleFamily_card_le hC⟩

/-- **The `r = 0` instance of Erdős–Pósa for odd cycles**: a graph with no odd cycle at all is
bipartite and needs no modifications. -/
theorem oddCycleErdosPosa_zero : OddCycleErdosPosa 0 := by
  refine ⟨0, fun W instW G hpack => ?_⟩
  have hno : ¬ ∃ C : Finset W, IsOddCycle G C := by
    rintro ⟨C, hC⟩
    refine absurd (hpack {C} ⟨?_, ?_⟩) (by simp)
    · intro X hX Y hY hXY
      have hXC : X = C := Finset.mem_singleton.mp hX
      have hYC : Y = C := Finset.mem_singleton.mp hY
      exact False.elim (absurd (hXC.trans hYC.symm) hXY)
    · intro X hX
      exact Finset.mem_singleton.mp hX ▸ hC
  exact isBipartite_closeToBipartite (m := 0) (isBipartite_of_no_oddCycle (G := G) hno)

end ErdosPosa

/-! ### The sharp example at `k = 1`, and a test of the formulation -/

section Sharp

/-- **`K_3` is not bipartite.** -/
theorem not_isBipartite_completeGraph_three :
    ¬ (SimpleGraph.completeGraph (Fin 3)).IsBipartite := by
  intro hnon
  obtain ⟨s, t, hb⟩ := SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mp hnon
  have notin : ∀ a : Fin 3, a ∈ s → ¬ (a ∈ t) := by
    intro a ha hb'
    exact Set.disjoint_left.mp hb.disjoint ha hb'
  have hadj (a b : Fin 3) (hne : a ≠ b) : (SimpleGraph.completeGraph (Fin 3)).Adj a b :=
    SimpleGraph.top_adj a b |>.mpr hne
  by_cases h0 : (0 : Fin 3) ∈ s
  · -- `1` and `2` are then both in `t`, and adjacent: impossible
    have h1t : (1 : Fin 3) ∈ t := by
      rcases hb.mem_of_adj (hadj 0 1 (by decide)) with hp | hp
      · exact hp.2
      · exact False.elim ((notin 0 h0) hp.1)
    have h2t : (2 : Fin 3) ∈ t := by
      rcases hb.mem_of_adj (hadj 0 2 (by decide)) with hp | hp
      · exact hp.2
      · exact False.elim ((notin 0 h0) hp.1)
    rcases hb.mem_of_adj (hadj 1 2 (by decide)) with hp | hp
    · exact (notin 1 hp.1) h1t
    · exact (notin 2 hp.2) h2t
  · -- `1` and `2` are then both in `s`, and adjacent: impossible
    have h1s : (1 : Fin 3) ∈ s := by
      rcases hb.mem_of_adj (hadj 0 1 (by decide)) with hp | hp
      · exact False.elim (absurd hp.1 h0)
      · exact hp.2
    have h2s : (2 : Fin 3) ∈ s := by
      rcases hb.mem_of_adj (hadj 0 2 (by decide)) with hp | hp
      · exact False.elim (absurd hp.1 h0)
      · exact hp.2
    rcases hb.mem_of_adj (hadj 1 2 (by decide)) with hp | hp
    · exact (notin 2 h2s) hp.2
    · exact (notin 1 h1s) hp.1

/-- **The sharp example of Erdős Problem #73 at `k = 1`.**  `K_3` satisfies `LocIndep 1` (see
`JSP90.completeGraph_locIndep`) and is **one** vertex away from being bipartite, i.e.
`CloseToBipartite 1 (K_3)`: the deletion `{0}` leaves `K_2`, which is `2`-colourable.  This is the
test case which shows the conclusion really means "delete at most `m` vertices and be left with a
bipartite graph" — under the rejected reading of `CloseToBipartite` (see
`JSPProblem/Definitions.lean`) `K_3` could not be a witness for any `m` at all. -/
theorem closeToBipartite_completeGraph_three :
    CloseToBipartite 1 (SimpleGraph.completeGraph (Fin 3)) := by
  have hval : ∀ z : Fin 3, z ∉ ({0} : Finset (Fin 3)) → z.val = 1 ∨ z.val = 2 := by
    intro z hz
    have h0 : z.val ≠ 0 := fun h => hz (Finset.mem_singleton.mpr (Fin.ext h))
    omega
  refine ⟨{0}, by simp, ⟨SimpleGraph.Coloring.mk (fun v => if v = 1 then (0 : Fin 2) else 1) ?_⟩⟩
  intro v w hadj
  have hvw := deleteFinset_adj.mp hadj
  have hne : v ≠ w := hvw.2.2.ne
  by_cases hv1 : v = 1
  · have hw1 : w ≠ 1 := fun h => hne (hv1.trans h.symm)
    simp [hv1, hw1]
  · by_cases hw1 : w = 1
    · simp [hv1, hw1]
    · rcases hval v hvw.1 with hv2 | hv2
      · exact absurd (Fin.ext hv2) hv1
      · have hv2' : v = 2 := Fin.ext hv2
        have hw2' : w = 2 :=
          Fin.ext ((hval w hvw.2.1).resolve_left (fun h => absurd (Fin.ext h) hw1))
        exact False.elim (hne (Eq.trans hv2' hw2'.symm))

/-- **The rejected reading of the conclusion was false already at `k = 1`.**  An earlier version of
this development read `CloseToBipartite m G` as "a bipartition `s ∪ t` of the *whole* graph `G`
whose leftover vertices are covered by a set of at most `m` vertices".  Since `K_3` satisfies
`LocIndep 1` but has no bipartition at all, that reading makes `Erdős73 1` a false statement: for
every `m` the witness does not exist.  This theorem is the machine-checked record of that bug; see
the header of `JSPProblem/Definitions.lean`. -/
theorem rejected_reading_fails (m : ℕ) :
    ¬ ∃ X : Finset (Fin 3), X.card ≤ m ∧ ∃ s t : Set (Fin 3),
      (SimpleGraph.completeGraph (Fin 3)).IsBipartiteWith s t ∧
        (Set.univ \ (s ∪ t)) ⊆ (X : Set (Fin 3)) := by
  rintro ⟨X, hX, s, t, hbip, -⟩
  exact not_isBipartite_completeGraph_three hbip.isBipartite

end Sharp

end

end JSP90
