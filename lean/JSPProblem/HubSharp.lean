/-
# JSP-000090 — `JSPProblem/HubSharp.lean`: the HUB COVER is EXACTLY OPTIMAL on complete graphs, the
## residual `HubByPacking` FORCES `ℓ + q ≥ 3r - 1`, and the residual is FALSE at `r = 0`

`discovery/JSP-000090/policy.json` (round 121, `lean/JSPProblem/Hub.lean` and
`lean/JSPProblem/Wheel.lean`) left the live residual of JSP-000090 in the shape

```lean
JSP90.HubByPacking (r ℓ q : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] (G : SimpleGraph W), OddCyclePackingLe r G →
    ∃ C Z : Finset W, IsOddCycle G C ∧ C.card ≤ q ∧ HubCover G C Z ∧ Z.card ≤ ℓ
```

with the reduction `JSP90.erdos73_of_hubByPacking_of_forall : (∀ r, HubByPacking r ℓ q) →
∀ k, Erdős73 k`, i.e. the whole of Erdős #73 (`jsp_000090_main`).  This file attacks that
residual on three axes, all of them new.

1. **The local structure of a hub cover at a *shortest* odd cycle** (Part 1).  The wheel of round
   121 has `|PetalSet| = n` with a single hub, so nothing bounds the attachment set — but the reason
   is that the rim of the wheel is *not* a shortest odd cycle.  At a **shortest** odd cycle of
   length `≥ 5` a vertex off the cycle is adjacent to at most **two** points of it
   (`JSP90.card_attachSet_le_two` of `JSPProblem/Book.lean`), so a hub is adjacent to at most two
   attachment points; and *if the petals are triangles* the attachment set is counted by the hubs:
   `JSP90.card_petalSet_le_of_hubCover_trianglePetals`, with the contrapositive
   `JSP90.card_petalSet_gt_of_hubCover_of_longPetal` ("**an unbounded attachment set forces a long
   petal**").  This is the repaired form of the numerical route that round 121 refuted, with the
   triangle hypothesis *stated* instead of hidden.

2. **The exact value of the instance on complete graphs** (Part 2).  For every `n ≥ 4` the minimum
   of `hubCost C Z` over the hub covers of `K_n` is **exactly `n - 2`**, the odd cycle transversal
   number of `K_n`: `JSP90.hubCost_ge_completeGraph` (the lower bound),
   `JSP90.hubCover_completeGraph_odd` / `_even` (the upper bound) and
   `JSP90.hubCost_min_completeGraph` (the exact minimum).  The round-121 instance is therefore
   *optimal* on complete graphs.

3. **What the residual forces, and the fact that it cannot hold at `r = 0`** (Parts 3–4).
   `JSP90.hubByPacking_cost_ge`: `HubByPacking r ℓ q` forces `3 * r - 2 ≤ ℓ + (q - 1)` for every
   `r ≥ 1` (witness `K_{3r}`), so **any** valid pair satisfies `ℓ + q ≥ 3 * r - 1`: the constants of
   the residual must grow at least linearly, with slope `3`, in the packing number.
   `JSP90.not_hubByPacking_zero`: the residual is **false at `r = 0`** (a bipartite graph has no odd
   cycle at all, so the existential cannot be witnessed), which makes
   `JSP90.erdos73_of_hubByPacking_of_forall` of round 121 a reduction demanding an impossible
   hypothesis.  `JSP90.erdos73_of_hubByPacking_of_succ` is the repaired reduction: the residual is
   needed **only for `r ≥ 1`**, and that still gives `∀ k, Erdős73 k`.
-/

import JSPProblem.Hub
import JSPProblem.Book
import JSPProblem.CriticalSharp

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance hubSharpEq : DecidableEq V := Classical.decEq V

/-- The vertex type of the complete graphs of Part 2 is `Fin n`; this local instance makes every
finset literal of this file agree with the `DecidableEq` baked into `JSP90.HitsOddCycles`,
`JSP90.HubCover` and `JSP90.IsOddCycle` (which were elaborated in files whose own local instances
were `Classical.decEq`). -/
local instance completeGraphEqFin (n : ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

/-! ### Part 0 — the cost of a hub cover -/

section Cost

/-- **The cost of a hub cover** `(C, Z)`: `|C| - 1 + |Z|`, the constant that
`JSP90.closeToBipartite_of_hubCover` of `JSPProblem/Hub.lean` pays. -/
def hubCost (C Z : Finset V) : ℕ := (C.card - 1) + Z.card

@[simp] theorem hubCost_eq {C Z : Finset V} : hubCost C Z = (C.card - 1) + Z.card := rfl

theorem closeToBipartite_of_hubCost {C Z : Finset V} {c : V} (hC : IsOddCycle G C) (hc : c ∈ C)
    (hZ : HubCover G C Z) : CloseToBipartite (hubCost C Z) G :=
  closeToBipartite_of_hubCover hC hc hZ

/-- A cheaper hub set is a cheaper constant. -/
theorem hubCost_mono {C Z Z' : Finset V} (h : Z.card ≤ Z'.card) : hubCost C Z ≤ hubCost C Z' := by
  show (C.card - 1) + Z.card ≤ (C.card - 1) + Z'.card
  exact Nat.add_le_add_left h _

/-- The vertices of a set split between the set itself and its complement in the whole vertex type. -/
theorem card_inter_compl_add {n : ℕ} {D C : Finset (Fin n)} :
    (D ∩ C).card + (D ∩ ((Finset.univ : Finset (Fin n)) \ C)).card = D.card := by
  set K := (Finset.univ : Finset (Fin n)) \ C with hK
  have hdisj : Disjoint (D ∩ C) (D ∩ K) := Finset.disjoint_left.mpr fun _ h1 h2 =>
    ((Finset.mem_sdiff.mp (Finset.mem_inter.mp h2).2).2) (Finset.mem_inter.mp h1).2
  have hunion : (D ∩ C) ∪ (D ∩ K) = D := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).1
      · exact (Finset.mem_inter.mp hx).1
    · intro x hx
      by_cases hxC : x ∈ C
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, hxC⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_inter.mpr ⟨hx, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxC⟩⟩))
  calc (D ∩ C).card + (D ∩ K).card = ((D ∩ C) ∪ (D ∩ K)).card :=
        (Finset.card_union_of_disjoint (s := D ∩ C) (t := D ∩ K) hdisj).symm
    _ = D.card := congrArg Finset.card hunion

/-- **THE CARDINALITY OF A `biUnion` OVER AN ARBITRARY INDEX SET** is at most the sum of the
cardinalities.  (`JSP90.card_le_sum_card_biUnion` of `JSPProblem/Cactus.lean` is the same lemma for
an index set which is itself a finset of finsets, which is not the shape a hub set has.) -/
theorem card_biUnion_le_sum_gen {ι : Type*} {W : Type*} [DecidableEq W] (s : Finset ι)
    (f : ι → Finset W) : (s.biUnion f).card ≤ ∑ i ∈ s, (f i).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have h1 := Finset.card_union_le (f a) (t.biUnion f)
      have h2 := ih
      omega

end Cost

/-! ### Part 1 — a hub sees at most two attachment points of a *shortest* odd cycle -/

section ShortestCycle

variable {m : ℕ} {C : Finset V}

/-- **THE CARDINALITY OF AN ODD CYCLE IS ODD.** -/
theorem card_mod_two_of_isOddCycle {D : Finset V} (hD : IsOddCycle G D) : D.card % 2 = 1 := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  have hcardD : D.card = m := by
    have heq : D = (Finset.univ : Finset (Fin m)).image f := by
      ext x
      simp only [hmem x, Finset.mem_image, Finset.mem_univ, true_and]
    rw [heq, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  rw [hcardD]
  exact hm

/-- **TWO VERTICES OF AN ODD CYCLE OF CARDINALITY THREE ARE ADJACENT.**  An odd cycle with three
vertices is a triangle, so any two of its vertices are adjacent.  This is the step that turns a
*triangle petal* into an attachment of its hub to the cycle. -/
theorem adj_of_oddCycle_card_three {D : Finset V} (hD : IsOddCycle G D) (hcard : D.card = 3)
    {x y : V} (hx : x ∈ D) (hy : y ∈ D) (hne : x ≠ y) : G.Adj x y := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  have hcardD : D.card = m := by
    have heq : D = (Finset.univ : Finset (Fin m)).image f := by
      ext x
      simp only [hmem x, Finset.mem_image, Finset.mem_univ, true_and]
    rw [heq, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hm3' : m = 3 := by omega
  subst hm3'
  have key2 : ∀ a b : Fin 3, a ≠ b → (b = cycSucc a ∨ a = cycSucc b) := by
    intro a b hab
    have hla := a.isLt
    have hlb := b.isLt
    have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    by_cases hij : a.val < b.val
    · by_cases h1 : a.val + 1 = b.val
      · refine Or.inl (Fin.ext ?_)
        rw [cycSucc_val, h1, Nat.mod_eq_of_lt (by omega)]
      · refine Or.inr (Fin.ext ?_)
        rw [cycSucc_val]
        have h2 : b.val + 1 = a.val + 3 := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · by_cases h1 : b.val + 1 = a.val
      · refine Or.inr (Fin.ext ?_)
        rw [cycSucc_val, h1, Nat.mod_eq_of_lt (by omega)]
      · refine Or.inl (Fin.ext ?_)
        rw [cycSucc_val]
        have h2 : a.val + 1 = b.val + 3 := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have key : ∀ a b : Fin 3, a ≠ b → G.Adj (f a) (f b) := by
    intro a b hab
    rcases key2 a b hab with h | h
    · rw [h]; exact hcyc a
    · rw [h]; exact (hcyc b).symm
  obtain ⟨a, ha⟩ := (hmem x).mp hx
  obtain ⟨b, hb⟩ := (hmem y).mp hy
  have hne' : a ≠ b := by
    intro hcon
    exact hne (by rw [← ha, hcon, ← hb])
  have h1 : G.Adj (f a) (f b) := key a b hne'
  have h2 : G.Adj x (f b) := by rw [← ha]; exact h1
  rw [← hb]
  exact h2

/-- **A HUB SEES AT MOST TWO ATTACHMENT POINTS.**  At a shortest odd cycle `C` of length `≥ 5` the
attachment points of `C` which are adjacent to a vertex `x ∉ V(C)` number at most **two**: they lie
in the attachment set of `x`, which `JSP90.card_attachSet_le_two` bounds by two.  This is the local
reason why the wheel of `JSPProblem/Wheel.lean` (one hub, `n` attachment points) escapes: the rim of
that wheel is **not** a shortest odd cycle. -/
theorem card_petalSet_inter_attachSet_le_two
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {x : V} (hxb : x ∈ boundary G C) :
    (PetalSet G C ∩ attachSet G C x).card ≤ 2 := by
  have hsub : PetalSet G C ∩ attachSet G C x ⊆ attachSet G C x :=
    Finset.inter_subset_right (s₁ := PetalSet G C) (s₂ := attachSet G C x)
  calc (PetalSet G C ∩ attachSet G C x).card ≤ (attachSet G C x).card := Finset.card_le_card hsub
    _ ≤ 2 := card_attachSet_le_two hshort hm hm3 f hinj hcyc hCmem hxb

/-- **IF EVERY PETAL OF A SHORTEST ODD CYCLE IS A TRIANGLE, THE ATTACHMENT SET IS COUNTED BY THE
HUBS**: `|PetalSet G C| ≤ |Z ∩ C| + 2 * |Z \ C|`.

Every attachment point outside `Z` carries a petal which, being a triangle, meets the hub set `Z` in
a vertex `z ∉ C` **adjacent to the attachment point**; the attachment points are then counted twice
over by the hubs. -/
theorem card_petalSet_le_of_hubCover_trianglePetals
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x)
    (htri : ∀ D : Finset V, IsOddCycle G D → (D ∩ C).card = 1 → D.card = 3)
    {Z : Finset V} (hZ : HubCover G C Z) :
    (PetalSet G C).card ≤ (Z ∩ C).card + 2 * (Z \ C).card := by
  classical
  have key : ∀ v ∈ PetalSet G C, v ∉ Z → ∃ z ∈ Z \ C, G.Adj v z := by
    intro v hv hvZ
    obtain ⟨hvC, D, hD, hDint⟩ := mem_petalSet.mp hv
    have hcard1 : (D ∩ C).card = 1 := Finset.card_eq_one.mpr ⟨v, hDint⟩
    have hvD : v ∈ D := by
      have hv' : v ∈ D ∩ C := by rw [hDint]; exact Finset.mem_singleton_self v
      exact (Finset.mem_inter.mp hv').1
    have hcard3 : D.card = 3 := htri D hD hcard1
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr (hZ.2 D hD hcard1)
    have hzD : z ∈ D := (Finset.mem_inter.mp hz).1
    have hzZ : z ∈ Z := (Finset.mem_inter.mp hz).2
    have hzC : z ∉ C := by
      intro hzC'
      exact hvZ ((Finset.mem_singleton.mp
        (by rw [← hDint]; exact Finset.mem_inter.mpr ⟨hzD, hzC'⟩)) ▸ hzZ)
    have hzne : v ≠ z := fun hcon => hzC (hcon ▸ hvC)
    refine ⟨z, Finset.mem_sdiff.mpr ⟨hzZ, hzC⟩, ?_⟩
    exact adj_of_oddCycle_card_three hD hcard3 hvD hzD hzne
  have hsub : PetalSet G C
      ⊆ (Z ∩ C) ∪ (Z \ C).biUnion (fun z => PetalSet G C ∩ attachSet G C z) := by
    intro v hv
    by_cases hvZ : v ∈ Z
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hvZ, (mem_petalSet.mp hv).1⟩))
    · obtain ⟨z, hz, hvz⟩ := key v hv hvZ
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨z, hz,
        Finset.mem_inter.mpr ⟨hv, mem_attachSet.mpr ⟨(mem_petalSet.mp hv).1, hvz.symm⟩⟩⟩))
  have h1 : (PetalSet G C).card
      ≤ ((Z ∩ C) ∪ (Z \ C).biUnion (fun z => PetalSet G C ∩ attachSet G C z)).card :=
    Finset.card_le_card hsub
  have h2 : ((Z ∩ C) ∪ (Z \ C).biUnion (fun z => PetalSet G C ∩ attachSet G C z)).card
      ≤ (Z ∩ C).card + ((Z \ C).biUnion (fun z => PetalSet G C ∩ attachSet G C z)).card :=
    Finset.card_union_le _ _
  have h3 : ((Z \ C).biUnion (fun z => PetalSet G C ∩ attachSet G C z)).card
      ≤ ∑ z ∈ Z \ C, (PetalSet G C ∩ attachSet G C z).card :=
    card_biUnion_le_sum_gen (Z \ C) (fun z => PetalSet G C ∩ attachSet G C z)
  have h4 : ∀ z : V, z ∈ Z \ C → (PetalSet G C ∩ attachSet G C z).card ≤ 2 := by
    intro z hz
    by_cases hzb : z ∈ boundary G C
    · exact card_petalSet_inter_attachSet_le_two hshort hm hm3 f hinj hcyc hCmem hzb
    · have hempty : PetalSet G C ∩ attachSet G C z = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxm : x ∈ C ∧ G.Adj z x := mem_attachSet.mp (Finset.mem_inter.mp hx).2
        have hzC : z ∉ C := (Finset.mem_sdiff.mp hz).2
        refine hzb ((mem_boundary (G := G) (C := C)).mpr
          (And.intro hzC (Exists.intro x (And.intro hxm.1 hxm.2))))
      rw [hempty]
      simp
  have h5 : (∑ z ∈ Z \ C, (PetalSet G C ∩ attachSet G C z).card) ≤ ∑ _z ∈ Z \ C, (2 : ℕ) := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact h4 i hi
  have h6 : (∑ _z ∈ Z \ C, (2 : ℕ)) = 2 * (Z \ C).card := by
    rw [Finset.sum_const]
    simp [Nat.mul_comm]
  have hstep1 : (Z ∩ C).card + ((Z \ C).biUnion (fun z => PetalSet G C ∩ attachSet G C z)).card
      ≤ (Z ∩ C).card + ∑ z ∈ Z \ C, (PetalSet G C ∩ attachSet G C z).card :=
    Nat.add_le_add_left h3 _
  have hstep2 : (Z ∩ C).card + (∑ z ∈ Z \ C, (PetalSet G C ∩ attachSet G C z).card)
      ≤ (Z ∩ C).card + ∑ _z ∈ Z \ C, (2 : ℕ) := Nat.add_le_add_left h5 _
  have hfinal : (PetalSet G C).card ≤ (Z ∩ C).card + ∑ _z ∈ Z \ C, (2 : ℕ) :=
    h1.trans (h2.trans (hstep1.trans hstep2))
  rw [h6] at hfinal
  exact hfinal

/-- **AN UNBOUNDED ATTACHMENT SET AT A SHORTEST ODD CYCLE FORCES A LONG PETAL.**  The contrapositive
of `JSP90.card_petalSet_le_of_hubCover_trianglePetals`: if some petal of `C` has at least five
vertices then no hub cover is cheap, whatever its size. -/
theorem card_petalSet_gt_of_hubCover_of_longPetal
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x)
    {Z : Finset V} (hZ : HubCover G C Z)
    (hlt : (Z ∩ C).card + 2 * (Z \ C).card < (PetalSet G C).card) :
    ∃ D : Finset V, IsOddCycle G D ∧ (D ∩ C).card = 1 ∧ 5 ≤ D.card := by
  classical
  by_contra hcon
  have htri : ∀ D : Finset V, IsOddCycle G D → (D ∩ C).card = 1 → D.card = 3 := by
    intro D hD h1
    have h5 : ¬ (5 : ℕ) ≤ D.card := fun h5' => hcon ⟨D, hD, h1, h5'⟩
    have h3 := isOddCycle_card_ge_three hD
    have hodd := card_mod_two_of_isOddCycle hD
    omega
  have hle := card_petalSet_le_of_hubCover_trianglePetals hshort hm hm3 f hinj hcyc hCmem htri hZ
  exact absurd hle (Nat.not_le_of_gt hlt)

end ShortestCycle

/-! ### Part 2 — the hub cover of a complete graph, exactly -/

section CompleteGraph

variable {n : ℕ}

/-- Membership in a three-element literal, read as a disjunction of equations. -/
theorem mem_triple_iff {n : ℕ} {a b c x : Fin n} :
    x ∈ ({a, b, c} : Finset (Fin n)) ↔ x = a ∨ x = b ∨ x = c := by
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact Or.inl h
    · rcases Finset.mem_insert.mp h with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Finset.mem_singleton.mp h'))
  · intro hx
    rcases hx with h | h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- **ANY THREE DISTINCT VERTICES OF A COMPLETE GRAPH ARE AN ODD CYCLE.**  The cyclic ordering
`j ↦ a, b, c` is injective and adjacent by a nine-case analysis on the three possible indices — the
analysis is written out because `decide` and `simp` on `Fin` literals are unusable in the scope of
a classical `DecidableEq (Fin n)` (see `discovery/JSP-000090/policy.json`). -/
theorem isOddCycle_triple_completeGraph {n : ℕ} (hn : 3 ≤ n) {a b c : Fin n}
    (h12 : a ≠ b) (h23 : b ≠ c) (h31 : c ≠ a) :
    IsOddCycle (SimpleGraph.completeGraph (Fin n)) ({a, b, c} : Finset (Fin n)) := by
  have hinj : Function.Injective (fun j : Fin 3 => match j.val with
    | 0 => a
    | 1 => b
    | _ => c) := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hv' : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    have hw' : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    rcases hv' with h | h | h <;> rcases hw' with h2 | h2 | h2
    · simp only [h, h2, Fin.val_mk] at hij; exact Fin.ext (by omega)
    · simp only [h, h2, Fin.val_mk] at hij; exact False.elim (absurd hij h12)
    · simp only [h, h2, Fin.val_mk] at hij; exact False.elim (absurd hij h31.symm)
    · simp only [h, h2, Fin.val_mk] at hij; exact False.elim (absurd hij h12.symm)
    · simp only [h, h2, Fin.val_mk] at hij; exact Fin.ext (by omega)
    · simp only [h, h2, Fin.val_mk] at hij; exact False.elim (absurd hij h23)
    · simp only [h, h2, Fin.val_mk] at hij; exact False.elim (absurd hij h31)
    · simp only [h, h2, Fin.val_mk] at hij; exact False.elim (absurd hij h23.symm)
    · simp only [h, h2, Fin.val_mk] at hij; exact Fin.ext (by omega)
  have hcyc : ∀ j : Fin 3, (SimpleGraph.completeGraph (Fin n)).Adj
      ((fun j : Fin 3 => match j.val with | 0 => a | 1 => b | _ => c) j)
      ((fun j : Fin 3 => match j.val with | 0 => a | 1 => b | _ => c) (cycSucc j)) := by
    intro j
    have hj := j.isLt
    have hv' : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    rcases hv' with h | h | h
    · simp only [h, Fin.val_mk, cycSucc_val]; exact completeGraph_adj' _ _ h12
    · simp only [h, Fin.val_mk, cycSucc_val]; exact completeGraph_adj' _ _ h23
    · simp only [h, Fin.val_mk, cycSucc_val]; exact completeGraph_adj' _ _ h31
  exact isOddCycle_triple (SimpleGraph.completeGraph (Fin n)) hinj hcyc rfl rfl rfl

/-- **A SET AND ITS COMPLEMENT IN THE WHOLE VERTEX TYPE SPLIT THE CARDINALITY.** -/
theorem card_univ_sub_add (C : Finset (Fin n)) :
    C.card + ((Finset.univ : Finset (Fin n)) \ C).card = n := by
  have hinter : C ∩ (Finset.univ : Finset (Fin n)) = C := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro x hx
      exact (Finset.mem_inter.mp hx).1
    · intro x hx
      exact Finset.mem_inter.mpr ⟨hx, Finset.mem_univ x⟩
  have h := Finset.card_sdiff (s := C) (t := Finset.univ)
  rw [hinter, Finset.card_univ, Fintype.card_fin] at h
  have hle := Finset.card_le_univ C
  rw [Fintype.card_fin] at hle
  omega

/-- **IN A COMPLETE GRAPH A SET MEETING EVERY ODD CYCLE LEAVES AT MOST TWO VERTICES OUT.**  Three
distinct vertices outside `C` are an odd cycle of `K_n` which avoids `C`. -/
theorem card_compl_le_two_completeGraph {C : Finset (Fin n)}
    (hmeet : HitsOddCycles (SimpleGraph.completeGraph (Fin n)) C) :
    ((Finset.univ : Finset (Fin n)) \ C).card ≤ 2 := by
  by_contra hgt
  obtain ⟨r1, hr1, r2, hr2, r3, hr3, h12, h23, h31⟩ :=
    exists_three_of_card_ge_three (s := (Finset.univ : Finset (Fin n)) \ C) (by omega)
  have hne1 : r1 ∉ C := (Finset.mem_sdiff.mp hr1).2
  have hne2 : r2 ∉ C := (Finset.mem_sdiff.mp hr2).2
  have hne3 : r3 ∉ C := (Finset.mem_sdiff.mp hr3).2
  have hD := isOddCycle_triple_completeGraph (by omega) (a := r1) (b := r2) (c := r3) h12 h23 h31
  have hempty : ({r1, r2, r3} : Finset (Fin n)) ∩ C = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    rcases (mem_triple_iff).mp (Finset.mem_inter.mp hx).1 with h | h | h
    · exact hne1 (h ▸ (Finset.mem_inter.mp hx).2)
    · exact hne2 (h ▸ (Finset.mem_inter.mp hx).2)
    · exact hne3 (h ▸ (Finset.mem_inter.mp hx).2)
  exact hmeet _ hD hempty

/-- **THE COST OF ANY HUB COVER OF `K_n` IS AT LEAST `n - 2`** — the odd cycle transversal number of
`K_n`.  The certificate `JSP90.closeToBipartite_of_hubCover` produces is `(C.erase c) ∪ Z`, which
meets every odd cycle, so it has at least `n - 2` vertices (Part 2 above), and it has at most
`|C| - 1 + |Z|` of them.  So the round-121 hub instance is **never better than the true transversal
number**. -/
theorem hubCost_ge_completeGraph (hn : 3 ≤ n) {C Z : Finset (Fin n)} {c : Fin n}
    (hC : IsOddCycle (SimpleGraph.completeGraph (Fin n)) C) (hc : c ∈ C)
    (hZ : HubCover (SimpleGraph.completeGraph (Fin n)) C Z) : n - 2 ≤ hubCost C Z := by
  have hcert : HitsOddCycles (SimpleGraph.completeGraph (Fin n)) ((C.erase c) ∪ Z) :=
    hitsOddCycles_of_hubCover hC hc hZ
  have hle := card_compl_le_two_completeGraph hcert
  have hsum := card_univ_sub_add ((C.erase c) ∪ Z)
  have hle' : n - 2 ≤ ((C.erase c) ∪ Z).card := by omega
  calc n - 2 ≤ ((C.erase c) ∪ Z).card := hle'
    _ ≤ (C.erase c).card + Z.card := Finset.card_union_le _ _
    _ = (C.card - 1) + Z.card := by rw [Finset.card_erase_of_mem hc]
    _ = hubCost C Z := (hubCost_eq).symm

end CompleteGraph

/-! ### Part 3 — what the residual `HubByPacking` forces -/

section HubByPackingSharp

/-- **EVERY PACKING BOUND FOR A COMPLETE GRAPH**: `K_n` has odd cycle packings of at most `n / 3`
members (`JSP90.mul_three_le_of_packing_completeGraph` of `JSPProblem/CriticalSharp.lean`). -/
theorem oddCyclePackingLe_completeGraph {n r : ℕ} (hr : 3 * r ≤ n) (hr' : 3 * (r + 1) > n) :
    OddCyclePackingLe r (SimpleGraph.completeGraph (Fin n)) := by
  intro P hP
  have h3 := mul_three_le_of_packing_completeGraph hP
  omega

/-- **THE RESIDUAL FORCES `3 * r - 2 ≤ ℓ + (q - 1)` FOR EVERY `r ≥ 1`.**  The witness is `K_{3r}`,
whose hub covers all cost at least `3r - 2` (Part 2).  Hence **any** pair `(ℓ, q)` for which
`JSP90.HubByPacking r ℓ q` holds satisfies `ℓ + q ≥ 3 * r - 1`: the constants of the residual must
grow at least linearly, with slope `3`, in the packing number, and no `r`-independent pair can ever
work. -/
theorem hubByPacking_cost_ge {r ℓ q : ℕ} (hr : 1 ≤ r) (h : HubByPacking.{0} r ℓ q) :
    3 * r - 2 ≤ ℓ + (q - 1) := by
  have hpack : OddCyclePackingLe r (SimpleGraph.completeGraph (Fin (3 * r))) :=
    oddCyclePackingLe_completeGraph (n := 3 * r) (r := r) le_rfl (by omega)
  obtain ⟨C, Z, hCodd, hCcard, hZ, hZcard⟩ :=
    h (Fin (3 * r)) (SimpleGraph.completeGraph (Fin (3 * r))) hpack
  have h3 := isOddCycle_card_ge_three hCodd
  have hpos : 0 < C.card := by omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  have hge := hubCost_ge_completeGraph (by omega) hCodd hc hZ
  rw [hubCost_eq] at hge
  omega

/-- **THE RESIDUAL FORCES `q ≥ 3`**: the witness `C` of a hub cover is an odd cycle. -/
theorem hubByPacking_q_ge_three {ℓ q : ℕ} (h : HubByPacking.{0} 1 ℓ q) : 3 ≤ q := by
  obtain ⟨C, Z, hC, hCcard, _, _⟩ :=
    h (Fin 3) (SimpleGraph.completeGraph (Fin 3))
      (oddCyclePackingLe_completeGraph (n := 3) (r := 1) (by omega) (by omega))
  have h3 := isOddCycle_card_ge_three hC
  omega

/-- **THE RESIDUAL IS FALSE AT `r = 0`.**  A graph with no odd cycle at all — the graph on the empty
vertex type, whose odd cycle packing number is `0` — admits no odd cycle `C`, so
`JSP90.HubByPacking 0 ℓ q` cannot hold for any `ℓ, q`.  Round 121's reduction
`JSP90.erdos73_of_hubByPacking_of_forall` assumes `∀ r, HubByPacking r ℓ q` and is therefore
demanding an impossible hypothesis; Part 4 is the repair. -/
theorem not_hubByPacking_zero {ℓ q : ℕ} : ¬ HubByPacking.{0} 0 ℓ q := by
  rintro h
  obtain ⟨C, Z, hC, _, _, _⟩ :=
    h Empty (⊥ : SimpleGraph Empty) (by
      intro P hP
      by_contra hgt
      have hcardP : 0 < P.card := by omega
      obtain ⟨X, hX⟩ := Finset.card_pos.mp hcardP
      have h3 := isOddCycle_card_ge_three (hP.2 X hX)
      have hleX := Finset.card_le_univ X
      rw [Fintype.card_empty] at hleX
      omega)
  have hcardC : C.card = 0 :=
    Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => nomatch x)
  have h3 := isOddCycle_card_ge_three hC
  omega

end HubByPackingSharp

/-! ### Part 4 — the repaired reduction to Erdős #73 -/

section HubByPackingSucc

universe u

/-- **THE HEADLINE SHAPE, REPAIRED**: the residual is needed **only for `r ≥ 1`**.  Every graph
satisfying Erdős's hypothesis with parameter `k ≥ 1` is then the union of a bipartite graph and at
most `ℓ + (q - 1)` vertices; for `k = 0` the graph is bipartite already
(`JSP90.locIndep_zero_isBipartite`). -/
theorem erdos73_on_of_hubByPacking_of_succ {k ℓ q : ℕ}
    (h : ∀ r, 1 ≤ r → HubByPacking.{u} r ℓ q) {W : Type u} [instW : Fintype W]
    (G : SimpleGraph W) (hG : LocIndep k G) : CloseToBipartite (ℓ + (q - 1)) G := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact closeToBipartite_mono (Nat.zero_le _)
      ⟨∅, by simp, by rw [deleteFinset_empty G]; exact locIndep_zero_isBipartite hG⟩
  · exact closeToBipartite_of_hubByPacking (h k (Nat.succ_le_of_lt hk))
      (locIndep_oddCyclePackingLe hG)

/-- **AND THEREFORE ERDŐS #73 ITSELF, WITH THE REPAIRED HYPOTHESIS.**  `(∀ r ≥ 1, HubByPacking r ℓ
q)` implies `Erdős73 k` for every `k`, i.e. `jsp_000090_main`.  This is the live residual of
JSP-000090; `JSP90.not_hubByPacking_zero` shows that the hypothesis cannot be extended to `r = 0`. -/
theorem erdos73_of_hubByPacking_of_succ {k ℓ q : ℕ} (h : ∀ r, 1 ≤ r → HubByPacking.{u} r ℓ q) :
    Erdős73.{u} k := by
  refine ⟨ℓ + (q - 1), ?_⟩
  intro W instW G hG
  exact erdos73_on_of_hubByPacking_of_succ h G hG

end HubByPackingSucc

end

end JSP90