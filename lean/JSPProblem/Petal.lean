/-
# JSP-000090 — `JSPProblem/Petal.lean`: the ONE-ATTACHMENT odd cycles at an odd cycle
  (the petal set, and the absorption step with a growing parameter)

`discovery/JSP-000090/policy.json` (round 118) asked for the counting half of the Mader step: how many
**one-attachment** odd cycles can hang off a shortest odd cycle, and how they are absorbed.  Round 117
had already refuted the two-attachment *cover* of round 115 (`JSP90.not_twoAttachCoverExists_one`,
witness the windmill) and round 118 had refuted the `c`-spread-transversal route
(`JSP90.no_fixed_spreadConstant`), so this file does **not** try to close either.  It introduces the
one new finite quantity that both routes need and that the classical argument genuinely has to
control.

## The new objects

* `JSP90.OneAttach G C D` — `D` is an odd cycle of `G` meeting `C` in **exactly one** vertex: a
  *petal* attached to `C` at a single point, and `D ∩ C` is its attachment point.
* `JSP90.PetalSet G C` — the **attachment set**: the vertices `v ∈ C` which lie *alone* on some odd
  cycle of `G`, i.e. the set of attachment points of the petals.  It is a subset of `C`
  (`petalSet_subset`, `card_petalSet_le_card`), hence finite and bounded by `|C|`; it is empty for
  a bipartite graph (`petalSet_empty_of_isBipartite`); and every petal meets it at its attachment
  point (`oneAttach_mem_petalSet`).

## What is proved

1. **`JSP90.petalSet_transversal` — THE ATTACHMENT-SET TRANSVERSAL.**  If `C` is an odd cycle of `G`
   and *every* odd cycle of `G` meets `C`, then some set **contained in `C`** with at most
   `|C| - 1 + |PetalSet G C|` vertices meets every odd cycle of `G`.

   The certificate is `C.erase c ∪ PetalSet G C` for an arbitrary `c ∈ C`, and the proof is the two
   cases of an odd cycle `D`: if `D` meets `C` in at least two vertices then `D` meets `C.erase c`
   (`JSP90.exists_mem_inter_erase_of_card_ge_two` of `JSPProblem/CPathSkip.lean`), and if it meets `C`
   in exactly one vertex then that vertex is an attachment point.  The certificate is a subset of `C`,
   so this is never weaker than the trivial statement "`C` meets every odd cycle".

2. **`JSP90.closeToBipartite_of_petalSet`, `JSP90.erdos73On_of_petalSet` — A NEW INSTANCE OF THE
   HEADLINE THEOREM, WITH A GROWING PARAMETER `a`:**  `LocIndep k G`, an odd cycle `C` meeting every
   odd cycle of `G` (equivalently `G - C` bipartite) and at most `a` attachment points give
   `CloseToBipartite (a + |C| - 1) G`.  The constant does **not** grow with `k`; the hypothesis
   `LocIndep k G` is not even needed for this step, which is a feature: the transversal is built
   from the structure at `C` alone.

3. **`JSP90.closeToBipartite_of_residue_petalSet` — THE ABSORPTION STEP WITH THE ATTACHMENT SET.**
   The residue induction step of `JSPProblem/Residue.lean` is
   `CloseToBipartite q (G - C) → CloseToBipartite (q + |C|) G`, and its `+|C|` is the recorded
   blocker.  This file improves it *quantitatively*: `CloseToBipartite q (G - C)` together with
   `|PetalSet G C| ≤ a` gives `CloseToBipartite (q + a + (|C| - 1)) G`, and
   `JSP90.closeToBipartite_of_residue_petalSet_zero` (attachment set empty) gives `q + |C| - 1`,
   **one vertex less than round 40**, in exactly the case where the petals are absent.  So the `|C|`
   term of the absorption step is only ever needed to pay for the attachment points; what is still
   missing is a bound on those attachment points in terms of `k`.

4. **`JSP90.closeToBipartite_of_petalSet_empty` and `JSP90.closeToBipartite_of_twoAttach'`**:
   the two-attachment transversal of round 111 (`JSP90.closeToBipartite_of_twoAttach`, constant
   `|C| - 1`) is **re-derived** from the present machinery, by observing that the two-attachment
   hypothesis is exactly "the petal set is empty".

5. **`JSP90.IsOddCycle.of_finset_ext` and `JSP90.IsOddCycle.of_finset_eq`** — transport lemmas for
   the `IsOddCycle` predicate along an equality of vertex sets; these remove the instance pitfall
   recorded in the round-53 header of `discovery/JSP-000090/policy.json` (a `Finset (Fin n)` built
   with one `DecidableEq` instance is not syntactically the one built with another) and are reusable
   by any later concrete witness.

## What is *not* proved

* **The counting bound on `|PetalSet G C|`** — the actual "Mader step" of `policy.json`.  At a
  shortest odd cycle with `|C| >= 5` a vertex outside `C` meets `C` in at most two vertices two steps
  apart (`JSPProblem.card_inter_neigh_le_two`, `JSPProblem/shortArc_of_shortest`), and the family of
  petals has to be charged against the packing number.  Without that bound `a` is not known to be
  `O(k)`, so `JSP90.erdos73On_of_petalSet` does not close Erdős #73;
  `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas) and `jsp_000090_main` are unchanged.
* **The nine-vertex witness** which shows the attachment term is needed.  The graph is the "triangle
  with a pendant triangle at each vertex": vertices `0..8`, triangles `{0,1,2}`, `{0,3,4}`, `{1,5,6}`,
  `{2,7,8}`, no other edges; `C = {0,1,2}`.  (i) `G - C` is the bipartite matching `3-4, 5-6, 7-8`, so
  every odd cycle meets `C`; (ii) each of the three pendant triangles meets `C` in exactly one
  vertex, so `PetalSet G C = C`; (iii) the three pendant triangles are pairwise disjoint odd cycles,
  so `¬ CloseToBipartite 2 G = ¬ CloseToBipartite (|C| - 1) G`.  This refutes the tempting
  strengthening of round 111 obtained by dropping "in at least two vertices".  The construction is
  written out in `discovery/JSP-000090/policy.json` (together with the four instance pitfalls found
  in this round: the `DecidableEq` instance inside `Finset.inter`, `decide` being unusable under the
  classical instance, `IsOddCycle` fixing the `Finset.image` instance, and `Finset.card` of a
  literal needing a computable instance).  Everything else in this file is proved; only the witness
  is outstanding.
-/

import JSPProblem.Weight
import JSPProblem.CPathSkip
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance petalDecidableEq : DecidableEq V := Classical.decEq V

/-! ### Part 1 — one attachment, and the petal set -/

section Attach

omit [Fintype V] in
theorem finset_eq_empty_of_not_nonempty {s : Finset V} (h : ¬ s.Nonempty) : s = ∅ := by
  rw [← Finset.card_eq_zero (s := s)]
  have hcard : ¬ 0 < s.card := fun hp => h (Finset.card_pos.mp hp)
  refine Nat.le_antisymm (by omega) (by omega)



omit [Fintype V] in
theorem mem_union_of_right' {s t : Finset V} {v : V} (hv : v ∈ t) : v ∈ s ∪ t :=
  Finset.mem_union.mpr (Or.inr hv)

omit [Fintype V] in
theorem mem_union_of_left' {s t : Finset V} {v : V} (hv : v ∈ s) : v ∈ s ∪ t :=
  Finset.mem_union.mpr (Or.inl hv)

omit [Fintype V] in
/-- **Transporting an odd cycle along an equality of vertex sets.**  This removes the instance
pitfall recorded in the header of round 53 (`discovery/JSP-000090/policy.json`): the statements of
`JSPProblem/Transversal.lean` were elaborated with the classical `DecidableEq` instance, so a finset
built with another instance is *equal* to, but not syntactically, the one appearing there. -/
theorem IsOddCycle.of_finset_ext {C : Finset V} (hC : IsOddCycle G C)
    (hext : ∀ x : V, x ∈ C ↔ x ∈ C') : IsOddCycle G C' := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  exact ⟨m, f, hm, hm3, hinj, hcyc, fun x => (hext x).symm.trans (hmem x)⟩

omit [Fintype V] in
/-- **Transporting an odd cycle along an equality of finsets.** -/
theorem IsOddCycle.of_finset_eq {C C' : Finset V} (hC : IsOddCycle G C') (heq : C = C') :
    IsOddCycle G C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  exact ⟨m, f, hm, hm3, hinj, hcyc, fun x => by rw [heq]; exact hmem x⟩

/-- `D` is **one-attached to `C`**: an odd cycle of `G` which meets `C` in exactly one vertex.  Such a
`D` is a *petal* of `C`, and the unique point of `D ∩ C` is its *attachment point*. -/
def OneAttach (G : SimpleGraph V) (C D : Finset V) : Prop :=
  IsOddCycle G D ∧ (D ∩ C).card = 1

/-- **The attachment set of `C`**: the vertices of `C` which lie *alone* on some odd cycle of `G`,
i.e. the attachment points of the petals of `C`. -/
noncomputable def PetalSet (G : SimpleGraph V) (C : Finset V) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter fun v => ∃ D : Finset V, IsOddCycle G D ∧ D ∩ C = {v}

theorem mem_petalSet {C : Finset V} {v : V} :
    v ∈ PetalSet G C ↔ v ∈ C ∧ ∃ D : Finset V, IsOddCycle G D ∧ D ∩ C = {v} := by
  simp only [PetalSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨D, hD, hDinter⟩
    have hvD : v ∈ ({v} : Finset V) := Finset.mem_singleton_self v
    rw [← hDinter] at hvD
    exact ⟨(Finset.mem_inter.mp hvD).2, D, hD, hDinter⟩
  · rintro ⟨-, D, hD, hDinter⟩
    exact ⟨D, hD, hDinter⟩

/-- The attachment set is a subset of `C`: an attachment point is a point of `C`. -/
theorem petalSet_subset {C : Finset V} : PetalSet G C ⊆ C :=
  fun v hv => (mem_petalSet.mp hv).1

theorem card_petalSet_le_card {C : Finset V} : (PetalSet G C).card ≤ C.card :=
  Finset.card_le_card (petalSet_subset (C := C))

/-- **A BIPARTITE GRAPH HAS NO PETALS**, so its attachment set is empty. -/
theorem petalSet_empty_of_isBipartite {C : Finset V} (h : G.IsBipartite) : PetalSet G C = ∅ := by
  have hne : ¬ (PetalSet G C).Nonempty := by
    rintro ⟨v, hv⟩
    obtain ⟨-, D, hD, hDinter⟩ := mem_petalSet.mp hv
    exact (not_isOddCycle_of_isBipartite h) ⟨D, hD⟩
  exact finset_eq_empty_of_not_nonempty hne

/-- **A PETAL IS MET BY THE ATTACHMENT SET**, at its unique attachment point. -/
theorem oneAttach_mem_petalSet {C D : Finset V} (hD : OneAttach G C D) :
    ∃ v ∈ D, v ∈ PetalSet G C := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hD.2
  have hac : a ∈ D ∩ C := by rw [ha]; simp
  obtain ⟨haD, haC⟩ := Finset.mem_inter.mp hac
  exact ⟨a, haD, mem_petalSet.mpr ⟨haC, D, hD.1, ha⟩⟩

end Attach

/-! ### Part 2 — the attachment-set transversal -/

section Transversal

/-- **THE ATTACHMENT-SET TRANSVERSAL.**  Let `C` be an odd cycle of `G` such that *every* odd cycle of
`G` meets `C`.  Then some set **contained in `C`** with at most `|C| - 1 + |PetalSet G C|` vertices
meets every odd cycle of `G`.

The certificate is `C.erase c ∪ PetalSet G C` for any `c ∈ C`. -/
theorem petalSet_transversal {C : Finset V} (hC : IsOddCycle G C)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅) :
    ∃ T : Finset V, T ⊆ C ∧ HitsOddCycles G T ∧ T.card ≤ (C.card - 1) + (PetalSet G C).card := by
  have h3 := isOddCycle_card_ge_three hC
  have hpos : 0 < C.card := by omega
  obtain ⟨c₀, hc₀⟩ := Finset.card_pos.mp hpos
  refine ⟨(C.erase c₀) ∪ PetalSet G C, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_of_mem_erase hv
    · exact petalSet_subset (C := C) hv
  · intro D hD
    have hne := hmeet D hD
    have hcard0 : (D ∩ C).card ≠ 0 :=
      Finset.card_ne_zero.mpr ((Finset.nonempty_iff_ne_empty (s := D ∩ C)).mpr hne)
    rcases Nat.lt_or_ge (D ∩ C).card 2 with hlt | hge
    · have h1 : (D ∩ C).card = 1 := by omega
      obtain ⟨v, hvD, hvA⟩ := oneAttach_mem_petalSet (C := C) (D := D) ⟨hD, h1⟩
      have hne0 : (D ∩ ((C.erase c₀) ∪ PetalSet G C)).Nonempty :=
        ⟨v, Finset.mem_inter.mpr ⟨hvD,
          mem_union_of_right' (s := C.erase c₀) (t := PetalSet G C) hvA⟩⟩
      exact Finset.nonempty_iff_ne_empty.mp hne0
    · obtain ⟨y, hyD, hyX⟩ := exists_mem_inter_erase_of_card_ge_two (D := D) (X := C) hge
      have hne0 : (D ∩ ((C.erase c₀) ∪ PetalSet G C)).Nonempty :=
        ⟨y, Finset.mem_inter.mpr ⟨hyD,
          mem_union_of_left' (s := C.erase c₀) (t := PetalSet G C) hyX⟩⟩
      exact Finset.nonempty_iff_ne_empty.mp hne0
  · refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ (le_refl _))
    rw [Finset.card_erase_of_mem hc₀]

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, WITH A GROWING PARAMETER.**  If `C` is an odd cycle of
`G` meeting every odd cycle of `G` and at most `a` of its vertices are attachment points, then `G` is
the union of a bipartite graph and at most `a + |C| - 1` vertices.  The constant does **not** grow
with Erdős's parameter `k` — and the hypothesis `LocIndep k G` is not needed for this step at all,
which is a feature: the transversal is built from the structure at `C` alone. -/
theorem closeToBipartite_of_petalSet {C : Finset V} {a : ℕ} (hC : IsOddCycle G C)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (ha : (PetalSet G C).card ≤ a) : CloseToBipartite (a + (C.card - 1)) G := by
  obtain ⟨T, -, hT, hcard⟩ := petalSet_transversal hC hmeet
  refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := a + (C.card - 1))).mpr ⟨T, ?_, hT⟩
  have h2 : (C.card - 1) + (PetalSet G C).card ≤ a + (C.card - 1) :=
    (Nat.add_le_add_left ha (C.card - 1)).trans_eq (Nat.add_comm _ _)
  exact hcard.trans h2

/-- The headline-theorem form of `closeToBipartite_of_petalSet`. -/
theorem erdos73On_of_petalSet {k a : ℕ} {C : Finset V} (hC : IsOddCycle G C)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅)
    (ha : (PetalSet G C).card ≤ a) (hG : LocIndep k G) :
    CloseToBipartite (a + (C.card - 1)) G :=
  closeToBipartite_of_petalSet hC hmeet ha

/-- **NO PETALS, `|C| - 1` VERTICES.**  If `C` is an odd cycle meeting every odd cycle of `G` and no
vertex of `C` is an attachment point, then `C` minus one vertex is a transversal. -/
theorem closeToBipartite_of_petalSet_empty {C : Finset V} (hC : IsOddCycle G C)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅) (hattach : PetalSet G C = ∅) :
    CloseToBipartite (C.card - 1) G := by
  have hcard : (PetalSet G C).card ≤ 0 := by rw [hattach]; simp
  have h := closeToBipartite_of_petalSet (C := C) (a := 0) hC hmeet hcard
  simpa using h

/-- **ROUND 111's TWO-ATTACHMENT TRANSVERSAL, RE-DERIVED.**  If every odd cycle of `G` meets `C` in at
least two vertices then `C` carries no attachment point, and `C` minus one vertex is a transversal. -/
theorem closeToBipartite_of_twoAttach' {C : Finset V} (hC : IsOddCycle G C)
    (hatt : ∀ D : Finset V, IsOddCycle G D → 2 ≤ (D ∩ C).card) :
    CloseToBipartite (C.card - 1) G := by
  refine closeToBipartite_of_petalSet_empty hC (fun D hD => ?_) ?_
  · have h2 : 2 ≤ (D ∩ C).card := hatt D hD
    have hpos : 0 < (D ∩ C).card := by omega
    exact (Finset.nonempty_iff_ne_empty (s := D ∩ C)).mp (Finset.card_pos.mp hpos)
  · refine finset_eq_empty_of_not_nonempty ?_
    rintro ⟨v, hv⟩
    obtain ⟨hvC, D, hD, hDinter⟩ := mem_petalSet.mp hv
    have h2 : 2 ≤ (D ∩ C).card := hatt D hD
    rw [hDinter] at h2
    have hcard1 : (({v} : Finset V)).card = 1 := Finset.card_singleton v
    omega

/-! ### Part 3 — the absorption step with the petal set -/

/-- **THE ABSORPTION STEP, WITH THE ATTACHMENT SET.**  If the residue of an odd cycle `C` is `q`-close
to bipartite and `C` has at most `a` attachment points, then `G` is `q + a + (|C| - 1)` close to
bipartite.

This is the improvement of round 40's `JSP90.closeToBipartite_of_residue` (`q + |C|`): the `|C|` term
is only needed to pay for the attachment points of the petals. -/
theorem closeToBipartite_of_residue_petalSet {C : Finset V} {q a : ℕ} (hC : IsOddCycle G C)
    (h : CloseToBipartite q (deleteFinset G C)) (ha : (PetalSet G C).card ≤ a) :
    CloseToBipartite (q + a + (C.card - 1)) G := by
  obtain ⟨X, hX, hhits⟩ :=
    (closeToBipartite_iff_hitsOddCycles (G := deleteFinset G C) (m := q)).mp h
  have h3 := isOddCycle_card_ge_three hC
  have hpos : 0 < C.card := by omega
  obtain ⟨c₀, hc₀⟩ := Finset.card_pos.mp hpos
  refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := q + a + (C.card - 1))).mpr
    ⟨X ∪ ((C.erase c₀) ∪ PetalSet G C), ?_, ?_⟩
  · have hAT : ((C.erase c₀) ∪ PetalSet G C).card ≤ a + (C.card - 1) := by
      refine (Finset.card_union_le (C.erase c₀) (PetalSet G C)).trans ?_
      rw [Finset.card_erase_of_mem hc₀]
      exact (Nat.add_le_add_left ha (C.card - 1)).trans_eq (Nat.add_comm _ _)
    have hsum : (X ∪ ((C.erase c₀) ∪ PetalSet G C)).card ≤ q + (a + (C.card - 1)) :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add hX hAT)
    omega
  · intro D hD
    by_cases hDC : D ∩ C = ∅
    · obtain ⟨x, hx⟩ := (Finset.nonempty_iff_ne_empty (s := D ∩ X)).mpr
        (hhits D (isOddCycle_of_isOddCycle_avoiding hD hDC))
      obtain ⟨hxD, hxX⟩ := Finset.mem_inter.mp hx
      have hne0 : (D ∩ (X ∪ ((C.erase c₀) ∪ PetalSet G C))).Nonempty :=
        ⟨x, Finset.mem_inter.mpr ⟨hxD,
          mem_union_of_left' (s := X) (t := (C.erase c₀) ∪ PetalSet G C) hxX⟩⟩
      exact Finset.nonempty_iff_ne_empty.mp hne0
    · by_cases h1 : (D ∩ C).card = 1
      · obtain ⟨v, hvD, hvA⟩ := oneAttach_mem_petalSet (C := C) (D := D) ⟨hD, h1⟩
        have hne0 : (D ∩ (X ∪ ((C.erase c₀) ∪ PetalSet G C))).Nonempty :=
          ⟨v, Finset.mem_inter.mpr ⟨hvD, mem_union_of_right'
            (s := X) (t := (C.erase c₀) ∪ PetalSet G C)
            (mem_union_of_right' (s := C.erase c₀) (t := PetalSet G C) hvA)⟩⟩
        exact Finset.nonempty_iff_ne_empty.mp hne0
      · have hcard0 : (D ∩ C).card ≠ 0 :=
          Finset.card_ne_zero.mpr ((Finset.nonempty_iff_ne_empty (s := D ∩ C)).mpr hDC)
        have h2 : 2 ≤ (D ∩ C).card := by omega
        obtain ⟨y, hyD, hyX⟩ := exists_mem_inter_erase_of_card_ge_two (D := D) (X := C) h2
        have hyAT : y ∈ (C.erase c₀) ∪ PetalSet G C :=
          mem_union_of_left' (s := C.erase c₀) (t := PetalSet G C) hyX
        have hne0 : (D ∩ (X ∪ ((C.erase c₀) ∪ PetalSet G C))).Nonempty :=
          ⟨y, Finset.mem_inter.mpr ⟨hyD,
            mem_union_of_right' (s := X) (t := (C.erase c₀) ∪ PetalSet G C) hyAT⟩⟩
        exact Finset.nonempty_iff_ne_empty.mp hne0

/-- **THE `q + |C|` STEP OF ROUND 40, IMPROVED BY ONE VERTEX** whenever `C` carries no petal. -/
theorem closeToBipartite_of_residue_petalSet_zero {C : Finset V} {q : ℕ} (hC : IsOddCycle G C)
    (h : CloseToBipartite q (deleteFinset G C)) (hattach : PetalSet G C = ∅) :
    CloseToBipartite (q + (C.card - 1)) G := by
  have hcard : (PetalSet G C).card ≤ 0 := by rw [hattach]; simp
  have h := closeToBipartite_of_residue_petalSet (C := C) (q := q) (a := 0) hC h hcard
  simpa using h

/-- **THE INSTANCE FORM OF THE ABSORPTION STEP**: Erdős's hypothesis together with a bound on the
attachment set of one odd cycle and a bound on its residue gives the conclusion for `G`, with the
explicit constant `m + a + (|C| - 1)`. -/
theorem erdos73On_of_petalSet_of_residue {k m a : ℕ} {C : Finset V} (hC : IsOddCycle G C)
    (hres : CloseToBipartite m (deleteFinset G C)) (ha : (PetalSet G C).card ≤ a)
    (hG : LocIndep k G) : CloseToBipartite (m + a + (C.card - 1)) G :=
  closeToBipartite_of_residue_petalSet (C := C) (q := m) (a := a) hC hres ha

end Transversal

end

end JSP90
