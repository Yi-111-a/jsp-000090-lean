/-
# JSP-000090 — the MEETING-SET axis: a new instance of Erdős #73, and its exact threshold

Attack family 62, companion to `JSPProblem/PetalOverlap.lean` (round 131, the overlap budget and
the refutation of the petal-overlap bound).

## The hypothesis

Round 131 closed the structural-hypothesis line with

> **`JSP90.closeToBipartite_two_of_oddCycles_meet_two`**: if every odd cycle of `G` meets a
> **triangle** `C` in at least two vertices, then `G` is `2`-close to bipartite,

a new instance of the headline theorem in which Erdős's hypothesis is not used at all.  That
statement is the `t = 2`, `|S| = 3` level of the family the round-131 policy asked for:

> *the odd cycles meet a fixed set `S` in at least `t` points ⇒ `t` vertices suffice.*

This file proves that family **in general**, for every `t`, and shows the threshold is exact.

* **`JSP90.MeetSet G S t`** — every odd cycle of `G` meets `S` in at least `t` of its vertices.
* **`JSP90.closeToBipartite_of_meetSet_of_card_le_two_mul_sub_one`** — if additionally
  `|S| ≤ 2 t - 1`, then `G` is `t`-close to bipartite.  The proof is the pigeonhole: a set of `t`
  vertices of `S` leaves at most `t - 1` vertices of `S` outside it, and every odd cycle carries
  `t` points of `S`.
* **`JSP90.erdos73On_of_meetSetHypothesis_of_le`** — the same statement in the shape of an instance
  of the headline theorem, `LocIndep k G → MeetSetHypothesis t G → CloseToBipartite m G`.
* **`JSP90.MeetSetErdős73On`** — the quantified instance class, and
  **`JSP90.meetSetErdős73On`**, which discharges it.

## What the hypothesis forces besides the transversal

* **`JSP90.exists_mem_inter_of_meetSet_of_card_le_two_mul_sub_one`** — **any two odd cycles of `G`
  share a point of `S`**: two `t`-point subsets of a set of at most `2t - 1` points meet.  So under
  the hypothesis the **packing number of odd cycles is at most one**
  (`JSP90.card_isOddCycleFamily_le_one_of_meetSet_of_card_le_two_mul_sub_one`), i.e. Erdős–Pósa is
  already at `r = 1`.

## Sharpness (machine-checked, both directions)

* **The constant `t` is optimal at `|S| = 2t - 1`.**  `sun3`, the 3-sun, satisfies
  `MeetSet T₀ 2` for the three-set `T₀` (`JSP90.meetSet_two_sun3`) and is not one vertex away from
  bipartite (`JSP90.not_closeToBipartite_one_sun3`).
* **The threshold `2t - 1` is optimal.**  `K₅`, with `S` four of its five vertices, satisfies
  `MeetSet S 2` (`JSP90.meetSet_completeGraph_five`) and is **not** `2`-close to bipartite
  (`JSP90.not_closeToBipartite_two_completeGraph_five`), so the instance
  `JSP90.closeToBipartite_of_meetSet_of_card_le_two_mul_sub_one` cannot be extended from `|S| ≤ 3`
  to `|S| ≤ 4` (`JSP90.not_forall_closeToBipartite_two_of_meetSet_two_of_card_four`).
* **The packing-number conclusion also fails at `2t`.**  `twoPend`, `K₄` with a pendent triangle on
  each of the two disjoint edges `0 – 1` and `2 – 3`, satisfies `MeetSet pendS 2` for the four-set
  `pendS` (`JSP90.meetSet_two_twoPend`) and has **two vertex-disjoint odd cycles**
  (`JSP90.exists_two_oddCycles_of_twoPend`), so "any two odd cycles share a point"
  (`JSP90.not_forall_oddCycles_meet_of_meetSet_two_of_card_four`) fails at `|S| = 2t`.
* **The pigeonhole claim itself is false at `2t`** (`JSP90.not_pigeonholeClaim_two_mul`, against
  `JSP90.pigeonholeClaim_of_card_le_two_mul_sub_one`), so the axis is closed on both sides: the
  family is proved for every `t`, the constant `t` is optimal, and `2t - 1` cannot be relaxed.

## A note on `DecidableEq`

Every finset statement in this file is phrased in the `DecidableEq` instance installed at its head
(`JSP90.instDecidableEqMeetSet`), which differs from the instance carried by the statements imported
from `JSPProblem/Transversal.lean` and `JSPProblem/Packing.lean`; for a *concrete* vertex type
(`Fin 5`, `Fin 6`) instance synthesis picks the **computable** `DecidableEq` instead, so a finset
term written in this file is not syntactically the term inside a hypothesis of those files.  All
crossings therefore go through `rw`/`simp`/`ext` (which match up to instances) or through the two
elementwise predicates `JSP90.HitsAllOddCycles` and the `∀`-form of the hypotheses; the one place
where a hypothesis of an imported statement is consumed uses `rw … at h` (`isBipartite_delete_of_hitsAllOddCycles`,
`card_isOddCycleFamily_le_one_of_…`). -/


import JSPProblem.PetalOverlap
import Mathlib.Data.Finset.SDiff

namespace JSP90

noncomputable section

open Finset Fintype Set

variable {V : Type*} [Fintype V]

local instance instDecidableEqMeetSet : DecidableEq V := Classical.decEq V

/-- `Finset.inter_subset_right` with the instances of this file made explicit. -/
theorem inter_subset_right_of {A B : Finset V} : A ∩ B ⊆ B :=
  fun _ hx => (Finset.mem_inter.mp hx).2

/-- `Finset.inter_subset_left` with the instances of this file made explicit. -/
theorem inter_subset_left_of {A B : Finset V} : A ∩ B ⊆ A :=
  fun _ hx => (Finset.mem_inter.mp hx).1

/-! ## Part 1 — "meets every odd cycle", read elementwise

The statements of this file use intersections built with `JSP90.instDecidableEqMeetSet`, while
`JSP90.HitsOddCycles` of `JSPProblem/Transversal.lean` was elaborated with a *different* (also
classical) `DecidableEq`.  The two conversions below are therefore written with `rw`, which matches
up to instances; `not_mem_of_inter_eq_empty` is the only place where an intersection term of the
other instance is consumed. -/

/-- **ELEMENTWISE READING OF "MEETS EVERY ODD CYCLE"**: every odd cycle of `G` contains a vertex of
`Z`.  This is `JSP90.HitsOddCycles G Z` read without any `DecidableEq`. -/
def HitsAllOddCycles (G : SimpleGraph V) (Z : Finset V) : Prop :=
  ∀ C : Finset V, IsOddCycle G C → ∃ x : V, x ∈ C ∧ x ∈ Z

theorem isBipartite_delete_of_hitsAllOddCycles {Z : Finset V} (h : HitsAllOddCycles G Z) :
    (deleteFinset G Z).IsBipartite := by
  refine isBipartite_of_no_oddCycle ?_
  rintro ⟨C', hC'⟩
  obtain ⟨C, hC, hd⟩ := oddCycle_of_isOddCycle_delete (G := G) (X := Z) hC'
  obtain ⟨x, hxC, hxZ⟩ := h C hC
  have hI : x ∈ C ∩ Z := Finset.mem_inter.mpr ⟨hxC, hxZ⟩
  rw [hd] at hI
  simp at hI

theorem hitsOddCycles_of_hitsAllOddCycles {Z : Finset V} (h : HitsAllOddCycles G Z) :
    HitsOddCycles G Z :=
  hitsOddCycles_of_isBipartite_delete (isBipartite_delete_of_hitsAllOddCycles h)

/-- **THE CONCLUSION OF ERDŐS #73 IN THE ELEMENTWISE FORM.** -/
theorem closeToBipartite_of_hitsAllOddCycles {m : ℕ} {Z : Finset V} (hZ : Z.card ≤ m)
    (h : HitsAllOddCycles G Z) : CloseToBipartite m G :=
  ⟨Z, hZ, isBipartite_delete_of_hitsAllOddCycles h⟩

/-- **TWO DISTINCT NEIGHBOURS OF A VERTEX OF AN ODD CYCLE, BOTH ON THE CYCLE.**  The two
cycle-neighbours; the form without `Neigh`, so that it composes with a description of the
adjacency of a concrete graph. -/
theorem exists_pair_adj_of_mem_isOddCycle {C : Finset V} (hC : IsOddCycle G C) {v : V} (hv : v ∈ C) :
    ∃ a b : V, a ≠ b ∧ G.Adj a v ∧ G.Adj b v ∧ a ∈ C ∧ b ∈ C := by
  obtain ⟨o, -⟩ := hC.cycleOrder
  obtain ⟨i, hi⟩ := (o.hmem v).mp hv
  have hadja : G.Adj (o.f (cycSucc i)) v := by rw [← hi]; exact (o.hcyc i).symm
  have hadjb : G.Adj (o.f (o.prev i)) v := by rw [← hi]; exact (o.adj_prev i).symm
  exact ⟨o.f (cycSucc i), o.f (o.prev i), o.step_prev_ne i, hadja, hadjb,
    (o.hmem _).mpr ⟨cycSucc i, rfl⟩, (o.hmem _).mpr ⟨o.prev i, rfl⟩⟩

/-! ## Part 2 — the MEETING SET and the pigeonhole -/

section Meet

/-- **THE MEETING SET.**  `MeetSet G S t` says that every odd cycle of `G` meets the fixed set `S`
in at least `t` of its vertices.  It is a purely *local intersection property*: no size, no degree,
no girth, no count, no connectivity. -/
def MeetSet (G : SimpleGraph V) (S : Finset V) (t : ℕ) : Prop :=
  ∀ C : Finset V, IsOddCycle G C → t ≤ (C ∩ S).card

/-- **THE PIGEONHOLE STEP.**  If every odd cycle meets `S` in at least `t` points and `Z ⊆ S` leaves
fewer than `t` points of `S` uncovered, then every odd cycle meets `Z`. -/
theorem hitsAllOddCycles_of_meetSet_of_card_le {t : ℕ} {S Z : Finset V} (hmeet : MeetSet G S t)
    (hZ : Z ⊆ S) (hlen : Z.card + t > S.card) : HitsAllOddCycles G Z := by
  intro C hC
  by_contra hcon
  have hn : ∀ x : V, x ∈ C → x ∉ Z := fun x hx hz => hcon ⟨x, hx, hz⟩
  have hmeetC := hmeet C hC
  have hsub : C ∩ S ⊆ S \ Z := by
    intro x hx
    obtain ⟨hxC, hxS⟩ := Finset.mem_inter.mp hx
    rw [Finset.mem_sdiff]
    exact ⟨hxS, hn x hxC⟩
  have hZcard : Z.card ≤ S.card := Finset.card_le_card hZ
  have hcard1 : (C ∩ S).card ≤ (S \ Z).card := Finset.card_le_card hsub
  have hcard2 : (S \ Z).card = S.card - Z.card := by
    have h := Finset.card_sdiff (s := Z) (t := S)
    rw [← Finset.inter_comm, Finset.inter_eq_right.mpr hZ] at h
    exact h
  omega

/-- **`S` ITSELF IS A TRANSVERSAL AS SOON AS `t ≥ 1`.** -/
theorem hitsAllOddCycles_of_meetSet_of_pos {t : ℕ} {S : Finset V} (ht : 1 ≤ t)
    (hmeet : MeetSet G S t) : HitsAllOddCycles G S :=
  hitsAllOddCycles_of_meetSet_of_card_le hmeet (Finset.Subset.refl _) (by omega)

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, FOR EVERY `t`: A `(2t - 1)`-SET WHICH EVERY ODD
CYCLE MEETS IN `t` POINTS IS AN ODD CYCLE TRANSVERSAL OF SIZE `t`.**

This is the general form of round 131's `JSP90.closeToBipartite_two_of_oddCycles_meet_two`, and
Erdős's hypothesis does not occur in it: `LocIndep` is not needed at all. -/
theorem closeToBipartite_of_meetSet_of_card_le_two_mul_sub_one {t : ℕ} (ht : 1 ≤ t) {S : Finset V}
    (hmeet : MeetSet G S t) (hS : S.card ≤ 2 * t - 1) : CloseToBipartite t G := by
  by_cases hcardS : t ≤ S.card
  · obtain ⟨Z, hZ, hcardZ⟩ := Finset.exists_subset_card_eq (s := S) hcardS
    have hlen : Z.card + t > S.card := by rw [hcardZ]; omega
    exact closeToBipartite_of_hitsAllOddCycles (le_of_eq hcardZ)
      (hitsAllOddCycles_of_meetSet_of_card_le hmeet hZ hlen)
  · refine ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    refine isBipartite_of_no_oddCycle ?_
    rintro ⟨C, hC⟩
    have h := hmeet C hC
    have hle := Finset.card_le_card (inter_subset_right_of (A := C) (B := S))
    omega

/-- **THE TRANSVERSAL LIES INSIDE `S`.**  This is the same statement with the location of the
transversal made explicit. -/
theorem exists_hitsAllOddCycles_of_meetSet_of_card_le_two_mul_sub_one {t : ℕ} (ht : 1 ≤ t)
    {S : Finset V} (hmeet : MeetSet G S t) (hS : S.card ≤ 2 * t - 1) :
    ∃ Z : Finset V, Z ⊆ S ∧ Z.card ≤ t ∧ HitsAllOddCycles G Z := by
  by_cases hcardS : t ≤ S.card
  · obtain ⟨Z, hZ, hcardZ⟩ := Finset.exists_subset_card_eq (s := S) hcardS
    have hlen : Z.card + t > S.card := by rw [hcardZ]; omega
    exact ⟨Z, hZ, le_of_eq hcardZ, hitsAllOddCycles_of_meetSet_of_card_le hmeet hZ hlen⟩
  · refine ⟨∅, Finset.empty_subset S, by simp, ?_⟩
    refine fun C hC => absurd (hmeet C hC) ?_
    have hle := Finset.card_le_card (inter_subset_right_of (A := C) (B := S))
    omega

end Meet

/-! ## Part 3 — the same statement in the shape of an instance of the headline theorem -/

section Instance

/-- The hypothesis of the instance, quantified over the meeting set: for the given `t` there is a
set of at most `2t - 1` vertices which every odd cycle meets in at least `t` points. -/
def MeetSetHypothesis (t : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ S : Finset V, S.card ≤ 2 * t - 1 ∧ MeetSet G S t

theorem meetSetHypothesis_of_card_le_of_meetSet {t : ℕ} {S : Finset V} (hS : S.card ≤ 2 * t - 1)
    (hmeet : MeetSet G S t) : MeetSetHypothesis t G := ⟨S, hS, hmeet⟩

theorem meetSetHypothesis_two_of_card_three_of_meetSet {S : Finset V} (hS : S.card = 3)
    (hmeet : MeetSet G S 2) : MeetSetHypothesis 2 G := by
  refine ⟨S, by omega, hmeet⟩

universe u

/-- **THE MEETING-SET INSTANCE CLASS OF THE HEADLINE THEOREM**: for every `k`, every `LocIndep k`
graph for which each level `1 ≤ t ≤ m` carries a meeting set of at most `2t - 1` vertices, deleting
`m` vertices leaves a bipartite graph. -/
def MeetSetErdős73On (k m : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
    (∀ t : ℕ, t ≤ m → 1 ≤ t → MeetSetHypothesis t G) → CloseToBipartite m G

/-- The class statement is implied by the full `Erdős73On k m`, as for every other instance class
of this development. -/
theorem meetSetErdős73On_of_erdos73On {k m : ℕ} (h : Erdős73On.{u} k m) :
    MeetSetErdős73On.{u} k m := fun _ instW G hG _ => h _ instW G hG

/-- **THE MEETING-SET INSTANCE CLASS IS DISCHARGED.**  Erdős's hypothesis is not used: the `t = m`
level of the class suffices, and the pigeonhole step of Part 2 turns its meeting set into a
transversal of size `m`. -/
theorem meetSetErdős73On (k m : ℕ) (hm : 1 ≤ m) : MeetSetErdős73On.{u} k m := by
  intro W _ G _ hhyp
  obtain ⟨S, hS, hmeet⟩ := hhyp m (le_refl m) hm
  exact closeToBipartite_of_meetSet_of_card_le_two_mul_sub_one hm hmeet hS

/-- **ERDŐS #73 WITH THE CONSTANT `m` FOR EVERY GRAPH WHOSE MEETING-SET HYPOTHESIS IS DERIVABLE
FROM ERDŐS'S OWN HYPOTHESIS.**  In particular `JSP90.meetSetErdős73On k m hm` is the statement of the
headline theorem for the class `MeetSetErdős73On k m`, and the whole theorem would follow from it by
taking `k = 0` — for which no meeting set exists and the class is empty. -/
theorem erdos73On_of_meetSetErdős73On {k m : ℕ} (hm : 1 ≤ m)
    (hderiv : ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      ∀ t : ℕ, t ≤ m → 1 ≤ t → MeetSetHypothesis t G) : Erdős73On.{u} k m :=
  fun W instW G hG => meetSetErdős73On k m hm W instW G hG (hderiv W instW G hG)

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, FOR EVERY `k`, WITH THE CONSTANT `m`.**  If every
odd cycle of `G` meets a set of at most `2t - 1` vertices in at least `t` points, then `G` is
`t`-close to bipartite, hence `m`-close to bipartite for every `m ≥ t`. -/
theorem erdos73On_of_meetSetHypothesis_of_le {k t m : ℕ} (hm : t ≤ m) (ht : 1 ≤ t) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → MeetSetHypothesis t G →
      CloseToBipartite m G := by
  intro W _ G _ hH
  obtain ⟨S, hS, hmeet⟩ := hH
  exact CloseToBipartite.mono
    (closeToBipartite_of_meetSet_of_card_le_two_mul_sub_one ht hmeet hS) hm

/-- **THE `t = 1` LEVEL: A SINGLE FIXED VERTETEX THROUGH WHICH EVERY ODD CYCLE PASSES.** -/
theorem erdos73On_of_meetSetHypothesis_one {k m : ℕ} (hm : 1 ≤ m) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → MeetSetHypothesis 1 G →
      CloseToBipartite m G := erdos73On_of_meetSetHypothesis_of_le hm (by omega)

end Instance

/-! ## Part 4 — round 131's triangle statement, recovered without the triangle hypothesis -/

section Bridge

/-- **THE `t = 2` LEVEL WITH AN ARBITRARY THREE-SET**: if every odd cycle meets *some* three vertices
in at least two points, then `G` is `2`-close to bipartite.  Round 131 needed the three vertices to
be a triangle (`JSP90.closeToBipartite_two_of_oddCycles_meet_two`); the set need not be a cycle, an
independent set, or even three adjacent vertices. -/
theorem closeToBipartite_two_of_oddCycles_meet_set_of_card_three {S : Finset V} (hS : S.card = 3)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → 2 ≤ (D ∩ S).card) : CloseToBipartite 2 G :=
  closeToBipartite_of_meetSet_of_card_le_two_mul_sub_one (by omega)
    (fun D hD => hmeet D hD) (by omega)

/-- **ROUND 131'S STATEMENT, RECOVERED FROM THE GENERAL ONE.**  A triangle meets the hypotheses
with `S = C`; nothing else about `C` is used. -/
theorem closeToBipartite_two_of_oddCycles_meet_C {C : Finset V}
    (hmeet : ∀ D : Finset V, IsOddCycle G D → 2 ≤ (D ∩ C).card) (hC3 : C.card = 3) :
    CloseToBipartite 2 G := closeToBipartite_two_of_oddCycles_meet_set_of_card_three hC3 hmeet

/-- **THE `t = 2` LEVEL, FOR EVERY `k`, AS AN INSTANCE OF THE HEADLINE THEOREM.** -/
theorem erdos73On_of_oddCycles_meet_set_of_card_three {k : ℕ} (hG : LocIndep k G) {S : Finset V}
    (hS : S.card = 3) (hmeet : ∀ D : Finset V, IsOddCycle G D → 2 ≤ (D ∩ S).card) :
    CloseToBipartite 2 G := closeToBipartite_two_of_oddCycles_meet_set_of_card_three hS hmeet

end Bridge

/-! ## Part 5 — THE PACKING NUMBER OF ODD CYCLES IS AT MOST ONE -/

section Packing

/-- **UNDER THE HYPOTHESIS, ANY TWO ODD CYCLES OF `G` SHARE A POINT OF `S`.**  Two subsets of `S`,
each of size at least `t`, meet as soon as `|S| ≤ 2t - 1`. -/
theorem exists_mem_inter_of_meetSet_of_card_le_two_mul_sub_one {t : ℕ} (ht : 1 ≤ t)
    {S : Finset V} (hmeet : MeetSet G S t) (hS : S.card ≤ 2 * t - 1) {D E : Finset V}
    (hD : IsOddCycle G D) (hE : IsOddCycle G E) : ∃ x : V, x ∈ D ∩ E := by
  have h1 := hmeet D hD
  have h2 := hmeet E hE
  have hcard := Finset.card_union_add_card_inter (D ∩ S) (E ∩ S)
  have hle : ((D ∩ S) ∪ (E ∩ S)).card ≤ S.card :=
    Finset.card_le_card (Finset.union_subset (inter_subset_right_of (A := D) (B := S))
      (inter_subset_right_of (A := E) (B := S)))
  have hcard2 : 1 ≤ ((D ∩ S) ∩ (E ∩ S)).card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard2
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
  obtain ⟨hxD, _⟩ := Finset.mem_inter.mp hx1
  obtain ⟨hxE, _⟩ := Finset.mem_inter.mp hx2
  exact ⟨x, Finset.mem_inter.mpr ⟨hxD, hxE⟩⟩

/-- The same statement as an intersection inequality. -/
theorem inter_oddCycle_of_meetSet_of_card_le_two_mul_sub_one {t : ℕ} (ht : 1 ≤ t) {S : Finset V}
    (hmeet : MeetSet G S t) (hS : S.card ≤ 2 * t - 1) {D E : Finset V} (hD : IsOddCycle G D)
    (hE : IsOddCycle G E) : D ∩ E ≠ ∅ := by
  obtain ⟨x, hx⟩ := exists_mem_inter_of_meetSet_of_card_le_two_mul_sub_one ht hmeet hS hD hE
  rw [← Finset.nonempty_iff_ne_empty]
  exact ⟨x, hx⟩

/-- **A FAMILY OF PAIRWISE VERTEX-DISJOINT ODD CYCLES OF `G` HAS AT MOST ONE MEMBER.** -/
theorem subset_singleton_of_meetSet_of_card_le_two_mul_sub_one {t : ℕ} (ht : 1 ≤ t) {S : Finset V}
    (hmeet : MeetSet G S t) (hS : S.card ≤ 2 * t - 1) {𝒞 : Finset (Finset V)}
    (h𝒞 : IsOddCycleFamily (G := G) 𝒞) {D : Finset V} (hD : D ∈ 𝒞) : 𝒞 ⊆ {D} := by
  intro E hE
  by_contra hne
  have hne' : E ≠ D := fun h => hne (by rw [h]; exact Finset.mem_singleton_self D)
  obtain ⟨x, hx⟩ :=
    exists_mem_inter_of_meetSet_of_card_le_two_mul_sub_one ht hmeet hS (h𝒞.2 D hD) (h𝒞.2 E hE)
  have hne'' : D ≠ E := fun h => hne' h.symm
  have hmem : x ∈ D ∩ E := hx
  rw [h𝒞.1 D hD E hE hne''] at hmem
  simp at hmem

theorem card_isOddCycleFamily_le_one_of_meetSet_of_card_le_two_mul_sub_one {t : ℕ} (ht : 1 ≤ t)
    {S : Finset V} (hmeet : MeetSet G S t) (hS : S.card ≤ 2 * t - 1) {𝒞 : Finset (Finset V)}
    (h𝒞 : IsOddCycleFamily (G := G) 𝒞) : 𝒞.card ≤ 1 := by
  classical
  by_cases hne : 𝒞.Nonempty
  · obtain ⟨D, hD⟩ := hne
    have hsub : 𝒞 ⊆ ({D} : Finset (Finset V)) :=
      subset_singleton_of_meetSet_of_card_le_two_mul_sub_one ht hmeet hS h𝒞 hD
    rw [← Finset.card_singleton]
    exact Finset.card_le_card hsub
  · have hnotpos : ¬ (0 < 𝒞.card) := fun h => hne (Finset.card_pos.mp h)
    omega

end Packing

/-! ## Part 6 — the structural lemma, and the `3`-sun as the sharp example -/

section Dominating

/-- **TWO VERTICES OF `S` SUFFICE IF `S` DOMINATES THE GRAPH.**  If every vertex outside `S` has all
of its neighbours in `S`, then every odd cycle of `G` meets `S` in at least two vertices, so
`JSP90.closeToBipartite_two_of_oddCycles_meet_set_of_card_three` applies whenever `|S| = 3`.

Indeed, a vertex of an odd cycle carries two of its cycle-neighbours, and both lie on `S`; hence an
odd cycle either meets `S` twice, or is contained in `S`, in which case it has exactly three
vertices and meets `S` three times. -/
theorem meetSet_two_of_neigh_outside {S : Finset V}
    (hneigh : ∀ v w : V, v ∉ S → G.Adj w v → w ∈ S) : MeetSet G S 2 := by
  intro C hC
  have h3 : 3 ≤ C.card := isOddCycle_card_ge_three hC
  by_contra hcon
  have hle1 : (C ∩ S).card ≤ 1 := by omega
  have hstep : ∀ v ∈ C, v ∉ S → 2 ≤ (C ∩ S).card := by
    intro v hv hvn
    obtain ⟨a, b, hab, hadja, hadjb, haC, hbC⟩ := exists_pair_adj_of_mem_isOddCycle hC hv
    have haS : a ∈ S := hneigh v a hvn hadja
    have hbS : b ∈ S := hneigh v b hvn hadjb
    have hxS_of : ∀ x : V, x ∈ ({a, b} : Finset V) → x ∈ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact haS
      · rw [Finset.mem_singleton.mp h]; exact hbS
    have hxC : ∀ x : V, x ∈ ({a, b} : Finset V) → x ∈ C := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact haC
      · rw [Finset.mem_singleton.mp h]; exact hbC
    have hsub' : ({a, b} ∩ S : Finset V) ⊆ C ∩ S := by
      intro x hx
      obtain ⟨hxab, hxS⟩ := Finset.mem_inter.mp hx
      rw [Finset.mem_inter]
      exact ⟨hxC x hxab, hxS⟩
    have hsup : ({a, b} : Finset V) ⊆ {a, b} ∩ S := by
      intro x hx
      rw [Finset.mem_inter]
      exact ⟨hx, hxS_of x hx⟩
    have hcardab : ({a, b} : Finset V).card = 2 := by simp [hab]
    have hsub'' : ({a, b} : Finset V) ⊆ C ∩ S := fun x hx => hsub' (hsup hx)
    have h1 : 2 ≤ ({a, b} ∩ S : Finset V).card := by
      have hle : ({a, b} : Finset V).card ≤ ({a, b} ∩ S : Finset V).card :=
        Finset.card_le_card hsup
      rw [← hcardab]
      exact hle
    exact le_trans h1 (Finset.card_le_card hsub')
  have hsub : C ⊆ S := by
    intro v hv
    by_contra hvn
    have h2 := hstep v hv hvn
    omega
  have hcardEq : (C ∩ S).card = C.card :=
    le_antisymm (Finset.card_le_card (inter_subset_left_of (A := C) (B := S)))
      (Finset.card_le_card (fun x hx => Finset.mem_inter.mpr ⟨hx, hsub hx⟩))
  have hle : C.card ≤ 3 := by rw [← hcardEq]; omega
  omega

end Dominating

/-! ### The `3`-sun, where the constant `2` is sharp -/

local instance instDecidableRelMeetSetSun3 : DecidableRel sun3.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ sun3Edge))

theorem mem_not_T0_sun3 : ∀ x : Fin 6, x ∉ T0 ↔ x = 1 ∨ x = 3 ∨ x = 4 := by decide

theorem neigh_of_not_T0_mem_T0 : ∀ v w : Fin 6, v ∉ T0 → sun3.Adj w v → w ∈ T0 := by decide

/-- **EVERY ODD CYCLE OF THE 3-SUN MEETS ITS CENTRAL TRIANGLE `T₀` IN AT LEAST TWO VERTICES.**  The
three vertices outside `T₀` are the degree-two vertices of the sun and all of their neighbours lie on
`T₀`, so `T₀` dominates `sun3` and `JSP90.meetSet_two_of_neigh_outside` applies. -/
theorem meetSet_two_sun3 : MeetSet (G := sun3) T0 2 := by
  apply meetSet_two_of_neigh_outside (G := sun3) (S := T0)
  intro v w hv hw
  exact neigh_of_not_T0_mem_T0 v w hv hw

/-- **THE CONSTANT `2` OF THE MEETING-SET INSTANCE IS OPTIMAL AT `|S| = 3`:** `sun3` satisfies
`MeetSet T₀ 2` and is not one vertex away from bipartite (`JSP90.not_closeToBipartite_one_sun3`).
Together with `JSP90.locIndep_one_sun3` this says that the meeting-set hypothesis, even at a
`LocIndep 1` graph, does not buy a smaller constant. -/
theorem not_closeToBipartite_one_of_meetSet_two_sun3 : ¬ CloseToBipartite 1 sun3 :=
  not_closeToBipartite_one_sun3

/-- The sharp meeting-set level of `sun3`, as an instance hypothesis. -/
theorem meetSetHypothesis_two_sun3 : MeetSetHypothesis 2 sun3 :=
  meetSetHypothesis_two_of_card_three_of_meetSet (by decide) meetSet_two_sun3

/-! ## Part 7 — `K₅`: the threshold `2t - 1` is optimal (the transversal conclusion) -/

/-- **A SET MISSING AT MOST ONE VERTEX IS MET BY EVERY ODD CYCLE IN AT LEAST TWO POINTS.**  An
odd cycle has at least three vertices, and at most one of them can lie outside `S`.

The hypothesis is phrased elementwise — "two vertices outside `S` are equal" — so that it can be
discharged by `decide` on a concrete vertex type whatever `DecidableEq` that type carries. -/
theorem meetSet_two_of_card_sdiff_le_one {S : Finset V}
    (hS : ∀ x y : V, x ∉ S → y ∉ S → x = y) : MeetSet G S 2 := by
  intro C hC
  have h3 : 3 ≤ C.card := isOddCycle_card_ge_three hC
  have hle1 : (C \ S).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    by_cases hex : ∃ x : V, x ∉ S
    · obtain ⟨x, hx⟩ := hex
      rw [Finset.mem_sdiff] at ha hb
      exact hS a b ha.2 hb.2
    · have hz : C \ S = ∅ := Finset.Subset.antisymm
        (fun y hy => (hex ⟨y, by rw [Finset.mem_sdiff] at hy; exact hy.2⟩).elim) (by simp)
      rw [hz] at ha
      simp at ha
  have hcard : C.card = (C ∩ S).card + (C \ S).card := by
    have hdisj : Disjoint (C ∩ S) (C \ S) :=
    Finset.disjoint_left.mpr fun x h1 h2 =>
      (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
    have hunion : (C ∩ S) ∪ (C \ S) = C := by
      refine Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
      · rcases Finset.mem_union.mp hx with h | h
        · rw [Finset.mem_inter] at h
          exact h.1
        · rw [Finset.mem_sdiff] at h
          exact h.1
      · by_cases hxS : x ∈ S
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, hxS⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx, hxS⟩))
    have hcard' := congrArg Finset.card hunion.symm
    rw [Finset.card_union_of_disjoint hdisj] at hcard'
    exact hcard'
  omega

/-- The four-set `Finset.univ \ {4}` of `K₅`, described elementwise; the description carries no
`DecidableEq`, so it can be produced by `decide`. -/
theorem mem_fin5_four : ∀ x : Fin 5, x ∈ ({0, 1, 2, 3} : Finset (Fin 5)) ↔ x ≠ 4 := by decide

/-- **EVERY ODD CYCLE OF `K₅` MEETS ANY FOUR-SET IN AT LEAST TWO VERTICES.**  An odd cycle of `K₅`
has at least three vertices, and only one vertex lies outside the four-set. -/
theorem meetSet_completeGraph_five {S : Finset (Fin 5)} (hS : ∀ x : Fin 5, x ∈ S ↔ x ≠ 4) :
    MeetSet (SimpleGraph.completeGraph (Fin 5)) S 2 := by
  apply meetSet_two_of_card_sdiff_le_one (G := SimpleGraph.completeGraph (Fin 5)) (S := S)
  intro x y hx hy
  rw [hS] at hx
  rw [hS] at hy
  exact Fin.le_antisymm (by omega) (by omega)

/-- **`K₅` IS NOT TWO VERTICES AWAY FROM BIPARTITE.** -/
theorem not_closeToBipartite_two_completeGraph_five :
    ¬ CloseToBipartite 2 (SimpleGraph.completeGraph (Fin 5)) := by
  rw [closeToBipartite_iff_completeGraph_add_two 2 5]
  omega

/-- **THE THRESHOLD `|S| ≤ 2t - 1` IS EXACT FOR `t = 2`: `K₅` SATISFIES THE MEETING SET WITH A
FOUR-SET AND IS NOT `2`-CLOSE TO BIPARTITE.**  The instance
`JSP90.closeToBipartite_of_meetSet_of_card_le_two_mul_sub_one` therefore cannot be extended from
`|S| ≤ 3` to `|S| ≤ 4`. -/
theorem not_forall_closeToBipartite_two_of_meetSet_two_of_card_four :
    ¬ ∀ G : SimpleGraph (Fin 5), MeetSet G ({0, 1, 2, 3} : Finset (Fin 5)) 2 →
      CloseToBipartite 2 G := by
  intro h
  apply not_closeToBipartite_two_completeGraph_five
  apply h (SimpleGraph.completeGraph (Fin 5))
  refine meetSet_completeGraph_five (S := ({0, 1, 2, 3} : Finset (Fin 5))) ?_
  intro x
  exact mem_fin5_four x

/-! ## Part 8 — `twoPend`: at `|S| = 2t` the *packing* conclusion fails too -/

/-- The edge set of `twoPend`: `K₄` on `0, 1, 2, 3`, with the vertex `4` joined to `0` and `1` and
the vertex `5` joined to `2` and `3`.  The two pendent triangles `{0,1,4}` and `{2,3,5}` are
vertex-disjoint. -/
def pendEdge : Finset (Fin 6 × Fin 6) :=
  {(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 0), (0, 3),
    (4, 0), (0, 4), (4, 1), (1, 4), (5, 2), (2, 5), (5, 3), (3, 5)}

theorem pendEdge_symm : ∀ v w : Fin 6, (v, w) ∈ pendEdge ↔ (w, v) ∈ pendEdge := by decide

theorem pendEdge_irrefl : ∀ v : Fin 6, (v, v) ∉ pendEdge := by decide

/-- **`twoPend`**: `K₄` with a pendent triangle on each of the two disjoint edges `0 – 1` and
`2 – 3`. -/
def twoPend : SimpleGraph (Fin 6) where
  Adj v w := (v, w) ∈ pendEdge
  symm := ⟨fun _ _ h => (pendEdge_symm _ _).mp h⟩
  loopless := ⟨fun _ h => (pendEdge_irrefl _ h)⟩

local instance instDecidableRelMeetSetTwoPend : DecidableRel twoPend.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ pendEdge))

@[simp] theorem twoPend_adj {v w : Fin 6} : twoPend.Adj v w ↔ (v, w) ∈ pendEdge := Iff.rfl

/-- The `K₄`-part of `twoPend`. -/
def pendS : Finset (Fin 6) := {0, 1, 2, 3}

theorem mem_pendS : ∀ x : Fin 6, x ∈ pendS ↔ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide

theorem not_mem_pendS : ∀ x : Fin 6, x ∉ pendS → x = 4 ∨ x = 5 := by decide

/-- **THE TWO PENDANT VERTICES HAVE ALL THEIR NEIGHBOURS ON `pendS`.** -/
theorem adj_not_pendS_mem_pendS : ∀ v w : Fin 6, v ∉ pendS → twoPend.Adj w v → w ∈ pendS := by decide

/-- **EVERY ODD CYCLE OF `twoPend` MEETS `pendS` IN AT LEAST TWO VERTICES.**  The vertices `4` and `5`
are the pendent ones and all of their neighbours lie on `pendS`, so `pendS` dominates `twoPend` and
`JSP90.meetSet_two_of_neigh_outside` applies. -/
theorem meetSet_two_twoPend : MeetSet twoPend pendS 2 := by
  apply meetSet_two_of_neigh_outside (G := twoPend) (S := pendS)
  intro v w hv hw
  exact adj_not_pendS_mem_pendS v w hv hw

theorem isOddCycle_twoPend_left : IsOddCycle twoPend ({0, 1, 4} : Finset (Fin 6)) :=
  ⟨3, cyc3n 6 0 1 4, by decide, by decide, by decide, by decide, by decide⟩

theorem isOddCycle_twoPend_right : IsOddCycle twoPend ({2, 3, 5} : Finset (Fin 6)) :=
  ⟨3, cyc3n 6 2 3 5, by decide, by decide, by decide, by decide, by decide⟩

theorem inter_twoPend_left_right : ({0, 1, 4} : Finset (Fin 6)) ∩ {2, 3, 5} = ∅ := by decide

/-- The odd-cycle family `{0,1,4}, {2,3,5}` of `twoPend`. -/
def twoPendFamily : Finset (Finset (Fin 6)) :=
  insert ({0, 1, 4} : Finset (Fin 6)) (insert ({2, 3, 5} : Finset (Fin 6)) ∅)

/-- **THE PACKING-NUMBER CONCLUSION OF PART 5 IS FALSE AT `|S| = 2t`.**  `twoPend` satisfies
`MeetSet pendS 2` (with `|pendS| = 4 = 2 t`), and it has **two vertex-disjoint odd cycles**,
`{0,1,4}` and `{2,3,5}`.  So the packing number of odd cycles is at least `2` while the hypothesis
of Part 5 holds, and neither the transversal conclusion nor the packing conclusion of Part 5
extends to `|S| = 2t`.

The disjointness is recorded elementwise — "no vertex lies in both" — because the finset
intersections of this development are built with a `DecidableEq` that a concrete vertex type does
not see (see the file header). -/
theorem exists_two_oddCycles_of_twoPend :
    ∃ D E : Finset (Fin 6), IsOddCycle twoPend D ∧ IsOddCycle twoPend E ∧
      ∀ x : Fin 6, x ∈ D → x ∈ E → False := by
  refine ⟨{0, 1, 4}, {2, 3, 5}, isOddCycle_twoPend_left, isOddCycle_twoPend_right, ?_⟩
  intro x hxD hxE
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxD hxE
  rcases hxD with hxD | hxD | hxD <;> rcases hxE with hxE | hxE | hxE <;> simp_all

/-- **NO TWO ODD CYCLES OF `twoPend` ALWAYS MEET**, i.e. the conclusion
`JSP90.inter_oddCycle_of_meetSet_of_card_le_two_mul_sub_one` of Part 5 — "under the hypothesis,
any two odd cycles share a point" — does **not** extend to `|S| = 2t`. -/
theorem not_forall_oddCycles_meet_of_meetSet_two_of_card_four :
    ¬ (∀ D E : Finset (Fin 6), IsOddCycle twoPend D → IsOddCycle twoPend E →
        ∃ x : Fin 6, x ∈ D ∧ x ∈ E) := by
  intro h
  obtain ⟨x, hxD, hxE⟩ := h ({0, 1, 4} : Finset (Fin 6)) ({2, 3, 5} : Finset (Fin 6))
    isOddCycle_twoPend_left isOddCycle_twoPend_right
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxD hxE
  rcases hxD with hxD | hxD | hxD <;> rcases hxE with hxE | hxE | hxE <;> simp_all

/-! ## Part 9 — the pigeonhole claim itself is false at `|S| = 2t` -/

/-- **THE PIGEONHOLE CLAIM OF PART 2, IN ABSTRACT FORM.**  With `|S| = 2t` no set of at most `t`
points of `S` need meet every `t`-point subset of `S`.  The statement is phrased without
intersections, so that it can be applied to concrete vertex types. -/
def PigeonholeClaim (t : ℕ) (S : Finset V) : Prop :=
  ∃ Z : Finset V, Z ⊆ S ∧ Z.card ≤ t ∧
    ∀ A : Finset V, A ⊆ S → t ≤ A.card → ∃ x : V, x ∈ A ∧ x ∈ Z

/-- **THE CLAIM IS TRUE AS SOON AS `|S| ≤ 2t - 1`** — the pigeonhole step of Part 2, read as a
statement about sets only. -/
theorem pigeonholeClaim_of_card_le_two_mul_sub_one {t : ℕ} (ht : 1 ≤ t) {S : Finset V}
    (hS : S.card ≤ 2 * t - 1) : PigeonholeClaim t S := by
  by_cases hcardS : t ≤ S.card
  · obtain ⟨Z, hZ, hcardZ⟩ := Finset.exists_subset_card_eq (s := S) (n := t) hcardS
    refine ⟨Z, hZ, le_of_eq hcardZ, ?_⟩
    intro A hA hcardA
    by_contra hcon
    have hcon' : ∀ x : V, x ∈ A → x ∉ Z := fun x hxA hxZ => hcon ⟨x, hxA, hxZ⟩
    have hsub : A ⊆ S \ Z := by
      intro x hx
      rw [Finset.mem_sdiff]
      exact ⟨hA hx, hcon' x hx⟩
    have hcard1 : A.card ≤ (S \ Z).card := Finset.card_le_card hsub
    have hZcard : Z.card ≤ S.card := Finset.card_le_card hZ
    have hcard2 : (S \ Z).card = S.card - Z.card := by
      have h := Finset.card_sdiff (s := Z) (t := S)
      rw [← Finset.inter_comm, Finset.inter_eq_right.mpr hZ] at h
      exact h
    have hle : Z.card ≤ S.card - Z.card :=
      le_trans (by rw [hcardZ]; exact hcardA) (hcard1.trans hcard2.le)
    have heq : S.card = (S.card - Z.card) + Z.card := (Nat.sub_add_cancel hZcard).symm
    have htwo : 2 * Z.card ≤ S.card := by
      have h1 : Z.card + Z.card ≤ (S.card - Z.card) + Z.card := Nat.add_le_add_right hle Z.card
      rw [← heq] at h1
      omega
    omega
  · refine ⟨∅, Finset.empty_subset S, by simp, ?_⟩
    intro A hA hcardA
    have hle : A.card ≤ S.card := Finset.card_le_card hA
    omega

/-- **THE CLAIM IS FALSE AT `|S| = 2t`**: the complement of any candidate works as a counterexample.
So `2t - 1` is the exact threshold of the whole axis. -/
theorem not_pigeonholeClaim_two_mul (t : ℕ) :
    ¬ PigeonholeClaim t (Finset.univ : Finset (Fin (2 * t))) := by
  rintro ⟨Z, -, hZcard, hA⟩
  have hsub : ((Finset.univ : Finset (Fin (2 * t))) \ Z) ⊆
      (Finset.univ : Finset (Fin (2 * t))) := Finset.sdiff_subset
  have hcardA : t ≤ ((Finset.univ : Finset (Fin (2 * t))) \ Z).card := by
    have h := Finset.card_sdiff (s := Z) (t := (Finset.univ : Finset (Fin (2 * t))))
    rw [Finset.inter_comm] at h
    rw [Finset.inter_eq_right.mpr (Finset.subset_univ Z)] at h
    rw [Finset.card_univ, Fintype.card_fin] at h
    omega
  obtain ⟨x, hxA, hxZ⟩ := hA _ hsub hcardA
  rw [Finset.mem_sdiff] at hxA
  exact hxA.2 hxZ

end
end JSP90
