/-
# JSP-000090 — `JSPProblem/Chain.lean`: the DECREASE at a hard 1-cut, and the block-cut bound

Round 108 closed the class axis on both sides and named the **packing-number axis** as the place
where real progress is left.  Round 109 works on that axis, and specifically on the **quantitative
content of the descent**: what a 1-cut does to the packing bound, and what a *chain* of 1-cuts does.

## What was missing

`JSPProblem/Connect.lean` (round 48) proved, along the 1-cut axis,

* `OneSplit.card_nonBipartiteParts_le` — under a packing bound `r`, at most `r` parts of a 1-cut are
  non-bipartite;
* `erdos73On_of_1split_of_bounded_pieces` / `oddCycleErdosPosa_of_1split_of_bounded_pieces` — an
  instance of the headline theorem along a 1-cut, with the constant `1 + m * r`;
* `oddCycleErdosPosa_of_noOneCut_of_bounded_oneDepth` — the reduction along the 1-cut axis, whose
  second hypothesis is the block-cut tree bound `oneDepth_le_of_packing`.

None of these says **how much** the packing bound *drops* at a 1-cut: they count the charged parts
instead of measuring the decrease.  The classical Reed–Robertson–Seymour–Thomas descent uses the
exact statement, and it is the first theorem of this file.

## What is proved

| result | content |
| --- | --- |
| `isOddCycle_subset_of_induceFinset` | an odd cycle of `G[s]` lies in `s` |
| `OneSplit.exists_oddCycle_of_mem_nonBipartiteParts`, `OneSplit.exists_oddCycle_of_not_isBipartite_part` | a non-bipartite part carries an odd cycle of `G` |
| `OneSplit.oddCycle_family_erase` | **one odd cycle in each of the other non-bipartite parts, pairwise disjoint, and as many as there are parts** |
| **`OneSplit.packing_part_le`** | **THE DECREASE: under a packing bound `r`, a non-bipartite part of a 1-cut with `s` non-bipartite parts has packing number at most `r + 1 - s`** |
| `OneSplit.packing_part_le_lt` | for `2 ≤ s` the bound is **strictly** smaller than `r` |
| **`OneSplit.packing_part_no_decrease_of_oneSide`** | at a **one-sided** 1-cut (`s = 1`) the bound is inherited *unchanged*: the descent stalls |
| **`closeToBipartite_of_1split_of_decreasing`** | **A NEW INSTANCE OF THE HEADLINE THEOREM with the *decreased* hypothesis on the parts**, constant `1 + s * m`, independent of the number of parts |
| `erdos73On_of_1split_of_decreasing`, `closeToBipartite_of_1split_of_decreasing_pack` | the same instance as a composition rule, in the packing language (the one in which the research statement lives) |
| `HardCert` | **a chain of `d` successive 1-cuts, each separating at least two non-bipartite sides** |
| **`exists_packing_of_hardCert`** | **THE BLOCK-CUT BOUND: a non-bipartite graph with such a chain of length `d + 1` has `d + 1` pairwise disjoint odd cycles** |
| **`hardCert_isBipartite_of_packing_le`** | **THE CORRECTED BLOCK-CUT THEOREM: a packing bound `r` forbids a hard chain of `r + 1` cuts** — round 48's named missing lemma `oneDepth_le_of_packing`, in the form in which it is true |
| `not_hardCert_of_not_isBipartite_of_packing_le` | the same, contrapositive: a 1-cut decomposition carries at most `r` hard levels |

## A machine-checked negative result found while writing this file

The classical descent was first written in Erdős's own parameter, and **Lean refuted it**:
`LocIndep` is monotone *increasing* in `k` (`LocIndep.mono_k`), so `LocIndep k G` never yields
`LocIndep (k - 1) G`, and the witness is the triangle:

* **`JSP90.locIndep_param_cannot_be_lowered`** — `LocIndep 1 (K_3)` holds while `¬ LocIndep 0 (K_3)`
  (`LocIndep 0` is equivalent to bipartiteness and `K_3` is not bipartite).

So the induction of the classical proof runs on the **packing number**, never on the `LocIndep`
parameter — which is why every statement of this file is in the packing language, and why the
decrease is measured by `OneSplit.packing_part_le` and not by a statement about `LocIndep`.

## The remaining gap, located precisely

`OneSplit.packing_part_no_decrease_of_oneSide` (the descent stalls at a one-sided 1-cut) together
with `hardCert_isBipartite_of_packing_le` (the hard chains are bounded by the packing number) says
exactly where the classical proof still needs work: **the one-sided chains** — cut vertices with a
single non-bipartite side.  They cannot be bounded by the packing number (a triangle with a pendant
path has packing number `1` and arbitrarily long such chains), so they are handled in the classical
proof by the block-cut tree and the short-C-path lemma.  `JSPProblem/Connect.lean`
`oddCycleErdosPosa_of_noOneCut_of_bounded_oneDepth` is unchanged and still needs that one hypothesis;
what is new here is that its *hard* half is a theorem.

## Toolchain notes

* `s = (sp.nonBipartiteParts : Finset (Fin t)).card` needs the `DecidablePred` instance of the
  definition site; it is named as a `local instance` (`fun _ => Classical.propDecidable _`), and
  because a finset built with one instance is not syntactically the finset built with another
  (round 54), the statements in the `Hard` section use
  `OneSplit.exists_oddCycle_of_not_isBipartite_part` instead of the `nonBipartiteParts`-version;
* a `def` whose body is `∃ (a : A) (b : B), …` needs a comma before the body (`OneDepth` in
  `JSPProblem/Connect.lean` has it), and a nested `∃ (x : A) (y : B), …` inside such a binder list
  does not parse — `HardCert` therefore names a finset `Q` of non-bipartite parts and its properties
  with `∀`-form hypotheses;
* `Finset.Disjoint s t` is the *membership* form, so `Disjoint s t ↔ s ∩ t = ∅` is
  `Finset.disjoint_iff_inter_eq_empty` (in that order: `.mp` turns `Disjoint` into `∩ = ∅`);
  `intro` cannot unfold `Finset.inter`, so membership in an intersection is obtained with
  `Finset.mem_inter.mpr ⟨…⟩` and the contradiction by `rw` + `simp`;
* `Finset.notMem_empty`, not `Finset.mem_empty_iff_false`, is the "not in the empty finset" lemma;
* `Finset.card_pos` and `Finset.card_ne_zero` are *implications* (not iff) in this Mathlib, so
  `Nonempty` is obtained from a bound with `Finset.nonempty_iff_ne_empty.mpr`;
* `Finset.card_erase_of_mem : #(s.erase a) = #s - 1`, so `1 ≤ #(s.erase a)` needs
  `Finset.card_erase_of_mem` plus `omega`, not an equation `#(s.erase a) + 1 = #s`;
* a one-variable function built as `fun j => if hj : p j then … else ∅` needs `simp only []`
  (beta reduction) before `rw [dite_eq_left hj]`, since `rw` cannot see through the redex;
* an identifier ending in `'` before `]` occasionally defeats the `obtain ⟨…⟩` parser; rename to
  avoid the prime when in doubt.
-/

import JSPProblem.Connect

namespace JSP90

open Finset Fintype Set

universe u

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqChain : DecidableEq V := Classical.decEq V

/-- An odd cycle of `G[s]` lies in `s`. -/
theorem isOddCycle_subset_of_induceFinset [Fintype V] {s C : Finset V}
    (hC : IsOddCycle (induceFinset G s) C) : C ⊆ s := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  intro x hx
  obtain ⟨j, hj⟩ := (hCmem x).mp hx
  have h1 := (induce_adj.mp (hcyc j)).1
  rwa [hj] at h1

section Decrease

variable {v : V} {t : ℕ} (sp : OneSplit G v t)

local instance instDecidablePredNBPartDec : DecidablePred fun i : Fin t =>
    ¬ (induceFinset G (sp.parts i)).IsBipartite := fun _ => Classical.propDecidable _

/-- **A non-bipartite part carries an odd cycle of `G`.**

The induced subgraph on the part is not bipartite, hence it has an odd cycle
(`isBipartite_of_no_oddCycle`), and that cycle is an odd cycle of `G`
(`IsOddCycle.of_induceFinset`) lying in the part. -/
theorem OneSplit.exists_oddCycle_of_mem_nonBipartiteParts [Fintype V] {i : Fin t}
    (hi : i ∈ sp.nonBipartiteParts) : ∃ C : Finset V, IsOddCycle G C ∧ C ⊆ sp.parts i := by
  classical
  obtain ⟨-, hnb⟩ := Finset.mem_filter.mp hi
  by_contra hcon
  have h1 : (induceFinset G (sp.parts i)).IsBipartite :=
    isBipartite_of_no_oddCycle fun h => by
      obtain ⟨C, hC⟩ := h
      exact hcon ⟨C, IsOddCycle.of_induceFinset hC, isOddCycle_subset_of_induceFinset hC⟩
  exact hnb h1

/-- **The same, phrased without `OneSplit.nonBipartiteParts`** — the finset `nonBipartiteParts`
depends on a `DecidablePred` instance (round 54), so a statement about it is not portable between
two `OneSplit`'s living in different `DecidablePred` scopes.  This version takes the
non-bipartiteness of the part directly. -/
theorem OneSplit.exists_oddCycle_of_not_isBipartite_part [Fintype V] {i : Fin t}
    (hnb : ¬ (induceFinset G (sp.parts i)).IsBipartite) :
    ∃ C : Finset V, IsOddCycle G C ∧ C ⊆ sp.parts i := by
  classical
  by_contra hcon
  have h1 : (induceFinset G (sp.parts i)).IsBipartite :=
    isBipartite_of_no_oddCycle fun h => by
      obtain ⟨C, hC⟩ := h
      exact hcon ⟨C, IsOddCycle.of_induceFinset hC, isOddCycle_subset_of_induceFinset hC⟩
  exact hnb h1

/-- **ONE ODD CYCLE IN EACH OF THE OTHER NON-BIPARTITE PARTS, PAIRWISE DISJOINT, AND AS MANY AS
THERE ARE PARTS.**  This is the counting object of the classical descent at a cut vertex: the parts
are pairwise disjoint (`OneSplit.hdisj`), so one odd cycle per part is a packing, and the map is
injective on the set of parts (two odd cycles in disjoint parts cannot be equal), so the family of
those odd cycles has as many members as there are parts. -/
theorem OneSplit.oddCycle_family_erase [Fintype V] {i : Fin t} (hi : i ∈ sp.nonBipartiteParts) :
    ∃ (g : Fin t → Finset V),
      (∀ j, j ∈ sp.nonBipartiteParts.erase i → IsOddCycle G (g j)) ∧
        (∀ j k, j ∈ sp.nonBipartiteParts.erase i → k ∈ sp.nonBipartiteParts.erase i →
          j ≠ k → Disjoint (g j) (g k)) ∧
          (∀ j, j ∈ sp.nonBipartiteParts.erase i → g j ⊆ sp.parts j) ∧
          ((sp.nonBipartiteParts.erase i).image g).card
            = (sp.nonBipartiteParts.erase i).card := by
  classical
  set g : Fin t → Finset V := fun j => if hj : j ∈ sp.nonBipartiteParts.erase i then
      (sp.exists_oddCycle_of_mem_nonBipartiteParts (Finset.mem_erase.mp hj).2).choose else ∅
    with hgdef
  have hgodd : ∀ j, j ∈ sp.nonBipartiteParts.erase i → IsOddCycle G (g j) := by
    intro j hj
    rw [hgdef]
    simp only []
    rw [dite_eq_left hj]
    exact (sp.exists_oddCycle_of_mem_nonBipartiteParts (Finset.mem_erase.mp hj).2).choose_spec.1
  have hgdisj : ∀ j k, j ∈ sp.nonBipartiteParts.erase i → k ∈ sp.nonBipartiteParts.erase i →
      j ≠ k → Disjoint (g j) (g k) := by
    intro j k hj hk hjk
    rw [hgdef]
    simp only []
    rw [dite_eq_left hj, dite_eq_left hk, Finset.disjoint_left]
    intro x hx1 hx2
    have hmem : x ∈ (sp.parts j) ∩ (sp.parts k) := Finset.mem_inter.mpr
      ⟨(sp.exists_oddCycle_of_mem_nonBipartiteParts (Finset.mem_erase.mp hj).2).choose_spec.2 hx1,
        (sp.exists_oddCycle_of_mem_nonBipartiteParts (Finset.mem_erase.mp hk).2).choose_spec.2 hx2⟩
    rw [sp.hdisj j k hjk] at hmem
    simp at hmem
  have hgsub : ∀ j, j ∈ sp.nonBipartiteParts.erase i → g j ⊆ sp.parts j := by
    intro j hj
    rw [hgdef]
    simp only []
    rw [dite_eq_left hj]
    exact (sp.exists_oddCycle_of_mem_nonBipartiteParts (Finset.mem_erase.mp hj).2).choose_spec.2
  refine ⟨g, hgodd, hgdisj, hgsub, ?_⟩
  rw [Finset.card_image_of_injOn]
  intro j hj
  intro k hk
  intro hEq
  by_contra hne
  obtain ⟨mm, f, hm, hm3, hfinj, hcyc, hmem⟩ := hgodd j hj
  have hnonempty : (g j).Nonempty := by
    have hxmem : f ⟨0, by omega⟩ ∈ g j := (hmem _).mpr ⟨⟨0, by omega⟩, rfl⟩
    exact Finset.nonempty_iff_ne_empty.mpr (fun hempty => by
      rw [hempty] at hxmem
      simp at hxmem)
  obtain ⟨x, hx⟩ := hnonempty
  have hmem : x ∈ g j ∩ g k := Finset.mem_inter.mpr ⟨hx, (by rw [← hEq]; exact hx)⟩
  have h2 := hgdisj j k hj hk hne
  rw [Finset.disjoint_iff_inter_eq_empty] at h2
  rw [h2] at hmem
  simp at hmem

/-! ### THE DECREASE -/

/-- **THE DECREASING LEMMA.**  Let `sp : OneSplit G v t`, let `s` be the number of its non-bipartite
parts, and suppose every packing of odd cycles of `G` has at most `r` members.  Then **every
packing of odd cycles inside a non-bipartite part has at most `r + 1 - s` members.**

The proof is the classical one: a nonempty packing inside the part, together with one odd cycle in
each of the *other* non-bipartite parts, is a packing of `G` — the parts are pairwise disjoint, so
the odd cycles contributed by the other parts meet neither the packing nor one another — of size
`|𝒞| + (s - 1)`, whence `|𝒞| + s - 1 ≤ r`.

For `s = 2` this says the packing number of the part is at most `r - 1`: **it strictly decreases at
every 1-cut with two non-bipartite sides.**  `JSPProblem/Connect.lean`
`OneSplit.card_nonBipartiteParts_le` does not give this: it counts the charged parts, it does not
measure the decrease. -/
theorem OneSplit.packing_part_le {r : ℕ} [Fintype V]
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r)
    {i : Fin t} (hi : i ∈ sp.nonBipartiteParts) {s : ℕ} (hse : s = (sp.nonBipartiteParts).card)
    {C : Finset (Finset V)}
    (hC : IsOddCycleFamily (G := induceFinset G (sp.parts i)) C) :
    C.card ≤ r + 1 - s := by
  classical
  obtain ⟨g, hgodd, hgdisj, hgsub, hcardimg⟩ := sp.oddCycle_family_erase hi
  have hsubC : ∀ X ∈ C, X ⊆ sp.parts i :=
    fun X hX => isOddCycle_subset_of_induceFinset (hC.2 X hX)
  -- a member of the packing is disjoint from the odd cycle of any other non-bipartite part
  have hDisj : ∀ X ∈ C, ∀ j, j ∈ sp.nonBipartiteParts.erase i → X ∩ g j = ∅ := by
    intro X hX j hj
    have hdj : Disjoint X (g j) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have hmem : x ∈ (sp.parts i) ∩ (sp.parts j) :=
        Finset.mem_inter.mpr ⟨hsubC X hX hx1, hgsub j hj hx2⟩
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      rw [sp.hdisj i j (Ne.symm hji)] at hmem
      simp at hmem
    exact Finset.disjoint_iff_inter_eq_empty.mp hdj
  by_cases hCne : C.Nonempty
  · -- the packing of `G`
    have hfam : IsOddCycleFamily (G := G) (C ∪ (sp.nonBipartiteParts.erase i).image g) := by
      refine ⟨?_, ?_⟩
      · intro X hX Y hY hne
        rcases Finset.mem_union.mp hX with hXc | hXimg
        · rcases Finset.mem_union.mp hY with hYc | hYimg
          · exact hC.1 X hXc Y hYc hne
          · obtain ⟨j, hj, hYimg'⟩ := Finset.mem_image.mp hYimg
            have hdj : Disjoint X Y := by
              rw [← hYimg']
              exact Finset.disjoint_iff_inter_eq_empty.mpr (hDisj X hXc j hj)
            exact Finset.disjoint_iff_inter_eq_empty.mp hdj
        · obtain ⟨j, hj, hXimg'⟩ := Finset.mem_image.mp hXimg
          rcases Finset.mem_union.mp hY with hYc | hYimg
          · have hdj0 : Disjoint Y (g j) :=
              Finset.disjoint_iff_inter_eq_empty.mpr (hDisj Y hYc j hj)
            have hdj : Disjoint X Y := by
              rw [← hXimg']
              exact disjoint_comm.mp hdj0
            exact Finset.disjoint_iff_inter_eq_empty.mp hdj
          · obtain ⟨j', hj', hYimg'⟩ := Finset.mem_image.mp hYimg
            have hne' : j ≠ j' := by
              intro hjj
              subst hjj
              exact absurd (hXimg'.symm.trans hYimg') hne
            have hdj : Disjoint X Y := by
              rw [← hXimg', ← hYimg']
              exact hgdisj j j' hj hj' hne'
            exact Finset.disjoint_iff_inter_eq_empty.mp hdj
      · intro X hX
        rcases Finset.mem_union.mp hX with hXc | hXimg
        · exact IsOddCycle.of_induceFinset (hC.2 X hXc)
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hXimg
          exact hgodd j hj
    have hcardfam := hpack _ hfam
    have hdisjfam : Disjoint C ((sp.nonBipartiteParts.erase i).image g) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      obtain ⟨j, hj, hxe⟩ := Finset.mem_image.mp hy
      have h2 := hDisj x hx j hj
      rw [← Finset.disjoint_iff_inter_eq_empty] at h2
      rw [← hxe] at h2
      obtain ⟨mm, f, hm, hm3, hfinj, hcyc, hmem⟩ := hgodd j hj
      have hxmem : f ⟨0, by omega⟩ ∈ g j := (hmem _).mpr ⟨⟨0, by omega⟩, rfl⟩
      have hmem : f ⟨0, by omega⟩ ∈ g j ∩ g j := Finset.mem_inter.mpr ⟨hxmem, hxmem⟩
      rw [Finset.disjoint_iff_inter_eq_empty] at h2
      rw [h2] at hmem
      simp at hmem
    have hcardfam' : (C ∪ (sp.nonBipartiteParts.erase i).image g).card
        = C.card + (sp.nonBipartiteParts.erase i).card := by
      rw [Finset.card_union_of_disjoint hdisjfam, hcardimg]
    have hEcard : (sp.nonBipartiteParts.erase i).card = s - 1 := by
      have h1 := Finset.card_erase_of_mem (s := sp.nonBipartiteParts) hi
      have h2 : 1 ≤ (sp.nonBipartiteParts : Finset (Fin t)).card :=
        Finset.card_pos.mpr ⟨i, hi⟩
      rw [← hse] at h1
      omega
    have hs1 : 1 ≤ s := by
      have hne' : (sp.nonBipartiteParts : Finset (Fin t)).Nonempty := ⟨i, hi⟩
      have hpos : 0 < (sp.nonBipartiteParts : Finset (Fin t)).card := Finset.card_pos.mpr hne'
      rw [← hse] at hpos
      omega
    have hfin : C.card + (s - 1) ≤ r := by
      have h1 : C.card + (sp.nonBipartiteParts.erase i).card ≤ r := by
        rw [← hcardfam']
        exact hcardfam
      rwa [hEcard] at h1
    have hkey : r + 1 - s = r - (s - 1) := by
      have hs'' : s = (s - 1) + 1 := (Nat.sub_add_cancel hs1).symm
      calc r + 1 - s = Nat.succ r - Nat.succ (s - 1) := by rw [hs'']; rfl
        _ = r - (s - 1) := Nat.succ_sub_succ _ _
    rw [hkey]
    exact Nat.le_sub_of_add_le hfin
  · have h0 : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCne
    have hle : (sp.nonBipartiteParts : Finset (Fin t)).card ≤ r :=
      sp.card_nonBipartiteParts_le hpack
    have hle' : s ≤ r := by
      rw [hse]
      exact hle
    simp only [h0, Finset.card_empty]
    omega

/-- **THE DECREASE, in the form used by the induction: for `2 ≤ s` the packing number of a
non-bipartite part is *strictly* smaller than `r`. -/
theorem OneSplit.packing_part_le_lt {r : ℕ} [Fintype V]
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r)
    {i : Fin t} (hi : i ∈ sp.nonBipartiteParts) {s : ℕ}
    (hs : 2 ≤ s) (hse : s = (sp.nonBipartiteParts).card) {C : Finset (Finset V)}
    (hC : IsOddCycleFamily (G := induceFinset G (sp.parts i)) C) : C.card < r := by
  have h1 := sp.packing_part_le (r := r) hpack hi hse hC
  have h2 : s ≤ r := by
    have hle := sp.card_nonBipartiteParts_le hpack
    rw [← hse] at hle
    omega
  omega

/-- **THE DESCENT IS IN THE PACKING NUMBER, NOT IN ERDŐS'S PARAMETER.**  The classical induction
step at a cut vertex is `OneSplit.packing_part_le_lt`: the *packing number* of a non-bipartite part
is strictly smaller than that of `G` whenever the cut separates two non-bipartite sides.

**The analogous statement in Erdős's own parameter is FALSE, and this development machine-checked the
refutation while writing it.**  `LocIndep` is *monotone increasing* in `k`
(`JSPProblem/Reed.lean` `LocIndep.mono_k`: `LocIndep k G → LocIndep k' G` for `k ≤ k'`), so from
`LocIndep k G` one gets `LocIndep (k + 1) G`, never `LocIndep (k - 1) G`; and the decreasing
statement is refuted by a graph: `LocIndep 1 (K_3)` holds while `LocIndep 0 (K_3)` fails, since
`LocIndep 0` means bipartite (`JSPProblem/OddCycle.lean` `locIndep_zero_isBipartite`) and `K_3` is not
bipartite.  The witness is `JSP90.locIndep_param_cannot_be_lowered` below.

So the induction of the classical proof runs on the packing number (`JSP90.OddCycleErdosPosa`),
never on `LocIndep`'s parameter — which is why this file's instances are stated for packings and the
composition rule below decreases the *packing bound*. -/
theorem locIndep_param_cannot_be_lowered :
    LocIndep 1 (SimpleGraph.completeGraph (Fin 3)) ∧
      ¬ LocIndep 0 (SimpleGraph.completeGraph (Fin 3)) := by
  refine ⟨completeGraph_locIndep 1, ?_⟩
  intro h
  exact not_isBipartite_completeGraph_three (locIndep_zero_isBipartite h)

/-- **THE DESCENT STALLS AT A ONE-SIDED 1-CUT.**  If a 1-cut has exactly one non-bipartite part the
decrease is `s - 1 = 0`: the packing bound of the part is inherited *unchanged*.

This is the machine-checked form of round 48's negative result number 1 ("a non-bipartite graph with
a 1-cut need not have two non-bipartite pieces"), and it is why the block-cut invariant `HardCert`
below has to ask for `2 ≤ s`.  Together with `OneSplit.packing_part_le_lt` the obstruction is
located exactly: **the packing number of the hard side drops by `s - 1` at a 1-cut which separates
two non-bipartite sides, and by nothing at any other 1-cut.** -/
theorem OneSplit.packing_part_no_decrease_of_oneSide {r : ℕ} [Fintype V]
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r)
    {i : Fin t} (hi : i ∈ sp.nonBipartiteParts) {s : ℕ} (hs : s = 1)
    (hse : s = (sp.nonBipartiteParts).card) {C : Finset (Finset V)}
    (hC : IsOddCycleFamily (G := induceFinset G (sp.parts i)) C) : C.card ≤ r := by
  have h1 := sp.packing_part_le (r := r) hpack hi hse hC
  rw [hs] at h1
  omega

end Decrease

/-! ### The new instance of the headline theorem, with the *decreased* hypothesis -/

section Instance

variable {v : V} {t : ℕ} (sp : OneSplit G v t)

local instance instDecidablePredNBPartInst : DecidablePred fun i : Fin t =>
    ¬ (induceFinset G (sp.parts i)).IsBipartite := fun _ => Classical.propDecidable _

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM along the 1-cut axis, with the *decreased* hypothesis
on the parts.**

If `sp` is a 1-cut of `G`, its `s` non-bipartite parts are each `m`-close to bipartite, `2 ≤ s`, and
every packing of odd cycles of `G` has at most `k` members, then

```
CloseToBipartite (1 + s * m) G
```

and the hypothesis on the parts is required only at the **decreased** packing bound `k + 1 - s`
(`OneSplit.packing_part_le`), not at `k` as in
`JSPProblem/Connect.lean` `oddCycleErdosPosa_of_1split_of_bounded_pieces`.  The constant is
independent of the number `t` of parts, and no bound on the odd girth, packing weight or number of
branch vertices is used. -/
theorem closeToBipartite_of_1split_of_decreasing {k m : ℕ} [Fintype V] {s : ℕ}
    (hs : 2 ≤ s) (hse : s = (sp.nonBipartiteParts).card)
    (hpart : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (sp.parts i)))
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ k) :
    CloseToBipartite (1 + s * m) G := by
  obtain ⟨Y, hY, hYcard⟩ := sp.exists_transversal_nonBipartite (m := m) hpart
  have hJ : (sp.nonBipartiteParts : Finset (Fin t)).card ≤ k :=
    sp.card_nonBipartiteParts_le hpack
  have hsum : (∑ i ∈ sp.nonBipartiteParts, m) ≤ s * m := by
    have h1 : (∑ i ∈ sp.nonBipartiteParts, m)
        = (sp.nonBipartiteParts : Finset (Fin t)).card * m := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    have h2 : (sp.nonBipartiteParts : Finset (Fin t)).card * m ≤ s * m := by
      rw [hse]
    exact h1.le.trans h2
  have hcard : Y.card ≤ 1 + s * m := hYcard.trans (Nat.add_le_add_left hsum 1)
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 1 + s * m)).mpr ⟨Y, hcard, hY⟩

/-- **The same instance as a COMPOSITION RULE, in the form in which the classical induction uses
it**: if a packing bound `q` forces `CloseToBipartite m` in every part of the 1-cut, then the
**decreased** bound `q' = q + 1 - s` does, and `LocIndep q G` then forces
`CloseToBipartite (1 + s * m) G`.

So a 1-cut with `s ≥ 2` non-bipartite sides lets the induction run with a strictly smaller packing
bound on the hard side, at the price of the constant `1 + s * m`. -/
theorem erdos73On_of_1split_of_decreasing {k m : ℕ} [Fintype V] {s : ℕ}
    (hs : 2 ≤ s) (hse : s = (sp.nonBipartiteParts).card)
    (hpiece : ∀ (q : ℕ),
      (∀ i : Fin t, (∀ C : Finset (Finset V),
        IsOddCycleFamily (G := induceFinset G (sp.parts i)) C → C.card ≤ q) →
          CloseToBipartite m (induceFinset G (sp.parts i))))
    (hG : LocIndep k G) : CloseToBipartite (1 + s * m) G := by
  have hq : k + 1 - s ≤ k := by
    have hle := sp.card_nonBipartiteParts_le (fun C hC => hG.oddCycleFamily_card_le hC)
    rw [← hse] at hle
    have h3 : s ≤ k := by omega
    omega
  have hbound : ∀ (i : Fin t), i ∈ sp.nonBipartiteParts →
      (∀ C : Finset (Finset V),
        IsOddCycleFamily (G := induceFinset G (sp.parts i)) C → C.card ≤ k + 1 - s) := by
    intro i hi C hC
    exact sp.packing_part_le (r := k) (fun D hD => hG.oddCycleFamily_card_le hD) (i := i) (hi := hi)
      hse hC
  exact closeToBipartite_of_1split_of_decreasing sp (k := k) (m := m) hs hse
    (fun i hi => hpiece (k + 1 - s) i (hbound i hi))
    (fun C hC => hG.oddCycleFamily_card_le hC)

/-- **The same instance in the packing language** (`JSP90.OddCycleErdosPosa`), the form in which the
research statement is available: a bound `r` on the packings of `G` forces the non-bipartite parts to
satisfy the **decreased** bound `r + 1 - s`, i.e. one unit less for each extra non-bipartite side. -/
theorem closeToBipartite_of_1split_of_decreasing_pack {r m : ℕ} [Fintype V] {s : ℕ}
    (hs : 2 ≤ s) (hse : s = (sp.nonBipartiteParts).card)
    (hpiece : ∀ i ∈ sp.nonBipartiteParts,
      (∀ C : Finset (Finset V),
        IsOddCycleFamily (G := induceFinset G (sp.parts i)) C → C.card ≤ r + 1 - s) →
          CloseToBipartite m (induceFinset G (sp.parts i)))
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r) :
    CloseToBipartite (1 + s * m) G := by
  have hpart : ∀ i ∈ sp.nonBipartiteParts, CloseToBipartite m (induceFinset G (sp.parts i)) :=
    fun i hi => hpiece i hi fun C hC => sp.packing_part_le (r := r) hpack hi hse hC
  obtain ⟨Y, hY, hYcard⟩ := sp.exists_transversal_nonBipartite (m := m) hpart
  have hJ : (sp.nonBipartiteParts : Finset (Fin t)).card ≤ r :=
    sp.card_nonBipartiteParts_le hpack
  have hsum : (∑ i ∈ sp.nonBipartiteParts, m) ≤ s * m := by
    have h1 : (∑ i ∈ sp.nonBipartiteParts, m)
        = (sp.nonBipartiteParts : Finset (Fin t)).card * m := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    have h2 : (sp.nonBipartiteParts : Finset (Fin t)).card * m ≤ s * m := by
      rw [hse]
    exact h1.le.trans h2
  have hcard : Y.card ≤ 1 + s * m := hYcard.trans (Nat.add_le_add_left hsum 1)
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 1 + s * m)).mpr ⟨Y, hcard, hY⟩

end Instance

/-! ### The block-cut bound: a chain of *hard* 1-cuts is paid for by disjoint odd cycles -/

section Hard

/-- **`HardCert G d`**: `G` carries a certificate of depth `d` — a decomposition of `V` by `d`
successive 1-cuts, **each of which has at least two non-bipartite parts**, every piece of every
level satisfying `HardCert` at the level below; `HardCert G 0` is vacuous.

This is the *hard* part of the 1-cut decomposition: the cuts at which the classical induction is
allowed to drop the packing number (`OneSplit.packing_part_le`).  A level with a single non-bipartite
part is **not** a hard level, and `HardCert` refuses it — for the reason recorded in
`OneSplit.packing_part_no_decrease_of_oneSide`.

The hypothesis on a level names the two non-bipartite parts explicitly rather than using
`OneSplit.nonBipartiteParts`, whose finset depends on a `DecidablePred` instance (round 54). -/
def HardCert (G : SimpleGraph V) : ℕ → Prop
  | 0 => True
  | d + 1 => ∃ (v : V) (t : ℕ) (sp : OneSplit G v t) (h2t : 2 ≤ t)
      (Q : Finset (Fin t)) (hQ : ∀ j, j ∈ Q → ¬ (induceFinset G (sp.parts j)).IsBipartite)
      (hcard : 2 ≤ Q.card) (hfree : ∀ j, j ∈ Q → v ∉ sp.parts j),
      ∀ i : Fin t, HardCert (induceFinset G (insert v (sp.parts i))) d

/-- **THE BLOCK-CUT BOUND.**  If `G` is not bipartite and carries a hard certificate of depth `d + 1`
then `G` has **at least `d + 1` pairwise vertex-disjoint odd cycles**.

The induction: a level of the certificate provides two distinct non-bipartite parts `T_i` and `T_j`;
an odd cycle inside `T_j` is disjoint from the *piece* `T_i ∪ {v}` — the parts are pairwise
anticomplete — and that piece carries a certificate of depth `d`, so by induction it has `d`
disjoint odd cycles.  Together they are `d + 1` disjoint odd cycles of `G`.

This is the classical "a chain of blocks, each of which contains an odd cycle, forces that many
disjoint odd cycles", in the form in which the 1-cut decomposition needs it. -/
theorem exists_packing_of_hardCert {d : ℕ} [Fintype V] (h : HardCert G (d + 1))
    (hnb : ¬ G.IsBipartite) :
    ∃ C : Finset (Finset V), IsOddCycleFamily (G := G) C ∧ d + 1 ≤ C.card := by
  classical
  induction d using Nat.strong_induction_on generalizing G with
  | h d ih =>
    obtain ⟨v, t, sp, h2t, Q, hQ, hcardQ, hfree, hrec⟩ := h
    have hQne0 : Q.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      intro hempty
      have hz : Q.card = 0 := hempty ▸ Finset.card_empty
      omega)
    obtain ⟨j, hjQ⟩ := hQne0
    -- a second non-bipartite part, distinct from `j`
    have hQne : (Q.erase j).Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      intro hempty
      have hz : (Q.erase j).card = 0 := hempty ▸ Finset.card_empty
      have h1 : (Q.erase j).card = Q.card - 1 := Finset.card_erase_of_mem hjQ
      have h2 : 1 ≤ Q.card := by omega
      omega)
    obtain ⟨i, himem⟩ := hQne
    have hne : i ≠ j := (Finset.mem_erase.mp himem).1
    have himemQ : i ∈ Q := (Finset.mem_erase.mp himem).2
    have hi : ¬ (induceFinset G (sp.parts i)).IsBipartite := hQ i himemQ
    have hj : ¬ (induceFinset G (sp.parts j)).IsBipartite := hQ j hjQ
    -- an odd cycle inside the part `T_j`, which avoids the cut vertex
    obtain ⟨C₁, hC₁, hC₁sub⟩ := sp.exists_oddCycle_of_not_isBipartite_part hj
    -- the piece `T_i ∪ {v}` is non-bipartite and carries a certificate of depth `d`
    have hpiece : ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite :=
      fun hb => hi (isBipartite_induceFinset_of_isBipartite hb (Finset.subset_insert v (sp.parts i)))
    obtain ⟨C₀, hC₀, hC₀card⟩ :
        ∃ C : Finset (Finset V),
          IsOddCycleFamily (G := induceFinset G (insert v (sp.parts i))) C ∧ d ≤ C.card := by
      by_cases hd0 : d = 0
      · refine ⟨∅, ⟨?_, ?_⟩, ?_⟩
        · intro X hX
          simp at hX
        · intro X hX
          simp at hX
        · simp [hd0]
      · have hd1 : 0 < d := by omega
        obtain ⟨C, hC, hcard⟩ :=
          ih (d - 1) (by omega) (G := induceFinset G (insert v (sp.parts i)))
            (by
              have h1 : d - 1 + 1 = d := by omega
              rw [h1]
              exact hrec i) hpiece
        exact ⟨C, hC, by omega⟩
    -- the piece of `T_i` is disjoint from the part `T_j`
    have hdisjParts : Disjoint (insert v (sp.parts i)) (sp.parts j) := by
      refine Finset.disjoint_left.mpr fun x hx hy => ?_
      rcases Finset.mem_insert.mp hx with h | h
      · subst h
        exact (hfree j hjQ hy).elim
      · have hmem : x ∈ (sp.parts i) ∩ (sp.parts j) := Finset.mem_inter.mpr ⟨h, hy⟩
        rw [sp.hdisj i j hne] at hmem
        simp at hmem
    have hC₀sub : ∀ X ∈ C₀, X ⊆ insert v (sp.parts i) :=
      fun X hX => isOddCycle_subset_of_induceFinset (hC₀.2 X hX)
    have hC₀odd : ∀ X ∈ C₀, IsOddCycle G X := fun X hX => IsOddCycle.of_induceFinset (hC₀.2 X hX)
    -- a member of `C₀` is disjoint from `C₁`, which lives in another part
    have hdisjParts' : (insert v (sp.parts i)) ∩ (sp.parts j) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdisjParts
    have hXC : ∀ X ∈ C₀, Disjoint X C₁ := by
      intro X hX
      refine Finset.disjoint_left.mpr ?_
      intro x hx1 hx2
      have hmem : x ∈ (insert v (sp.parts i)) ∩ (sp.parts j) :=
        Finset.mem_inter.mpr ⟨hC₀sub X hX hx1, hC₁sub hx2⟩
      rw [hdisjParts'] at hmem
      simp at hmem
    have hfam : IsOddCycleFamily (G := G) (C₀ ∪ insert C₁ ∅) := by
      refine ⟨?_, ?_⟩
      · intro X hX Y hY hXY
        rcases Finset.mem_union.mp hX with hXc | hX1
        · rcases Finset.mem_union.mp hY with hYc | hY1
          · exact hC₀.1 X hXc Y hYc hXY
          · rcases Finset.mem_insert.mp hY1 with hY1' | hY1''
            · rw [hY1']
              exact Finset.disjoint_iff_inter_eq_empty.mp (hXC X hXc)
            · exact (Finset.notMem_empty Y hY1'').elim
        · rcases Finset.mem_insert.mp hX1 with hX1' | hX1''
          · rcases Finset.mem_union.mp hY with hYc | hY1
            · rw [hX1']
              exact Finset.disjoint_iff_inter_eq_empty.mp (disjoint_comm.mp (hXC Y hYc))
            · rcases Finset.mem_insert.mp hY1 with hY1' | hY1''
              · exact (hXY (hX1'.trans hY1'.symm)).elim
              · exact (Finset.notMem_empty Y hY1'').elim
          · simp at hX1''
      · intro X hX
        rcases Finset.mem_union.mp hX with hXc | hX1
        · exact hC₀odd X hXc
        · rcases Finset.mem_insert.mp hX1 with hX1' | hX1''
          · rw [hX1']
            exact hC₁
          · exact (Finset.notMem_empty X hX1'').elim
    refine ⟨C₀ ∪ insert C₁ ∅, hfam, ?_⟩
    have hdisj : Disjoint C₀ (insert C₁ ∅) := by
      refine Finset.disjoint_left.mpr ?_
      intro X hX hX1
      rcases Finset.mem_insert.mp hX1 with hX1' | hX1''
      · have hmem1 : C₁ ∈ C₀ := hX1' ▸ hX
        obtain ⟨mm, f, hm, hm3, hfinj, hcyc, hmem⟩ := hC₁
        have hxm : f ⟨0, by omega⟩ ∈ C₁ := (hmem _).mpr ⟨⟨0, by omega⟩, rfl⟩
        have hmem : f ⟨0, by omega⟩ ∈ (insert v (sp.parts i)) ∩ (sp.parts j) := Finset.mem_inter.mpr
          ⟨hC₀sub C₁ hmem1 hxm, hC₁sub hxm⟩
        rw [hdisjParts'] at hmem
        exact (Finset.notMem_empty _ hmem).elim
      · exact (Finset.notMem_empty X hX1'').elim
    have hcard : (C₀ ∪ insert C₁ ∅).card = C₀.card + 1 := by
      rw [Finset.card_union_of_disjoint hdisj]
      simp
    rw [hcard]
    omega

/-- **THE CORRECTED BLOCK-CUT THEOREM.**  A bound `r` on the odd cycle packings of `G` **forbids a hard
chain of `r + 1` successive 1-cuts**: if every packing of odd cycles of `G` has at most `r` members
and `G` carries a hard certificate of depth `r + 1`, then `G` is bipartite.

In words: **a chain of `r + 1` cut vertices, each of which separates two non-bipartite sides, forces
`r + 1` pairwise disjoint odd cycles.**  This is the theorem round 48 named as the missing lemma
`oneDepth_le_of_packing`, *in the form in which it is true*: it is the **hard** levels, i.e. the
levels at which the classical descent `OneSplit.packing_part_le_lt` applies, that are counted.  The
levels with a single non-bipartite side are not, and `OneSplit.packing_part_no_decrease_of_oneSide`
shows the descent genuinely stalls there, so the two results together localise the remaining work to
the *one-sided* chains — which is what the block-cut tree proper (and the short-C-path lemma) is
for. -/
theorem hardCert_isBipartite_of_packing_le {r : ℕ} [Fintype V]
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r)
    (hcert : HardCert G (r + 1)) : G.IsBipartite := by
  classical
  by_contra hnb
  obtain ⟨C, hC, hcard⟩ := exists_packing_of_hardCert (d := r) hcert hnb
  have h1 := hpack C hC
  omega

/-- **The same statement, contrapositive**: a non-bipartite graph whose odd cycle packings have at
most `r` members admits no hard chain of depth `r + 1`.  This is the form in which the
block-cut bound enters the recursion of the 1-cut reduction: a 1-cut decomposition of depth `d`
carries at most `r` hard levels. -/
theorem not_hardCert_of_not_isBipartite_of_packing_le {r : ℕ} [Fintype V]
    (hnb : ¬ G.IsBipartite)
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r) :
    ¬ HardCert G (r + 1) := by
  classical
  intro hcert
  exact hnb (hardCert_isBipartite_of_packing_le hpack hcert)

end Hard

end

end JSP90
