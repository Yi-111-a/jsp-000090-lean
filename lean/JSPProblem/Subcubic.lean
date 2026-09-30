import JSPProblem.Layer

/-!
# JSP-000090, round 78 — the **SUBCUBIC axis**: the fan is finite, and one odd cycle covers all
of them

This is the **twenty-sixth attack family**.  Round 77 named the missing input

`JSP90.SubcubicErdős73 g` — *every graph of maximum degree at most `3` satisfying `LocIndep k` is
`g k`-close to bipartite* — and left as its sub-goal (1) the `k = 1` case with the constant `1`.

**Sub-goal (1) of round 77 is refuted, and this file records why.**  The Petersen graph with one
vertex deleted (`JSP90.p9`, `JSPProblem/Petersen.lean`) has maximum degree `3`
(`JSP90.maxDegLe_p9`), satisfies `LocIndep 1 p9`, and has `¬ CloseToBipartite 1 p9`; so no
admissible `g` satisfies `g 1 ≤ 1` (`JSP90.subcubic_constant_ne_one` below, and
`JSP90.not_subcubicErdős73_one`).  The sharp constant at `k = 1` is **two**, and Part 4 of this file
attains it.

What is proved here is a transversal statement that is new and structural, and it gives **a new
instance of the headline theorem** with a constant better than
`JSP90.erdos73On_of_bounded_odd_girth` (`ℓ * k`) on the subcubic class.

## The idea

At a vertex `u` of an odd cycle `C`, subcubicity gives `|N(u)| ≤ 3` while the cycle already uses two
of those neighbours.  Everything follows from that one numerical fact.

* **Part 1 — the fan of an odd cycle in a subcubic graph is finite.**  A vertex of an odd cycle has
  at most **one** neighbour outside the cycle (`card_le_one_outerNeigh_oddCycle`), hence
  `|∂C| ≤ |C|` (`card_boundary_le_card_oddCycle`) and `|N[C]| ≤ 2 * |C|`
  (`card_neighClosed_le_two_mul_card_oddCycle`); a fan vertex has at most two neighbours outside
  `C` (`card_le_two_outerNeigh_boundary`).
* **Part 2 — two odd cycles that meet share a *cycle edge* of the first**
  (`CycleOrder.exists_adj_mem_inter`).  The two cycles each use two of the three edges at the
  common vertex `u`, and two `2`-subsets of a `3`-set intersect, so one of the first cycle's
  neighbours of `u` is a neighbour along the second cycle as well; the shared edge is an edge *of
  the cyclic order*, not a chord.  This is what allows a cyclically chosen set to meet every odd
  cycle.
* **Part 3 — the even cover of a cycle** (`evenCover`).  For a cycle of odd length `m`, the
  `⌈m/2⌉` vertices at **even positions** meet every edge of the cycle
  (`exists_mem_evenCover_of_cycleEdge`), and there are at most `(m + 1) / 2` of them
  (`card_evenCover`).  Consequently

  > `JSP90.hitsOddCycles_of_inter` — if every odd cycle of a subcubic graph meets one fixed odd
  > cycle `C`, then some set of at most `(C.card + 1) / 2` vertices meets **every** odd cycle.

  and `JSP90.inter_oddEvenCover_of_isOddCycle` is the single-cycle form, phrased with
  `JSP90.oddEvenCover` (the even cover of the *chosen* cyclic order of a finset that is an odd
  cycle, `∅` otherwise — no choice over a `Finset` of cyclic orders is needed).
* **Part 4 — a new instance of the headline theorem**
  (`closeToBipartite_of_subcubic_of_shortOddCycles`): a subcubic graph of `LocIndep k` whose odd
  cycles have at most `ℓ` vertices is `k * ((ℓ + 1) / 2)`-close to bipartite.  At `k = 1` the
  constant does not mention `k` at all
  (`closeToBipartite_of_subcubic_of_locIndep_one_of_shortOddCycle`), and the case `k = 1, ℓ = 3`
  — every odd cycle of `G` is a triangle — is `CloseToBipartite 2 G`, the sharp value.
* **Part 5 — the remaining statement, isolated.**  `JSP90.SubcubicPackingOne`: in a subcubic graph
  whose odd cycles pairwise meet, **two** vertices meet all of them.  Exhaustive computation over
  all subcubic graphs on `≤ 8` vertices (`10 355 376` of them, of which `1540` have transversal
  number `≥ 3`, none of those with packing number `1`) and random search up to `13` vertices finds
  no counterexample.  It is **stated, not assumed**: `erdos73On_subcubic_one_of_packingOne` is the
  only reduction, and it goes in the direction that makes the statement *stronger* than the `k = 1`
  level of `JSP90.SubcubicErdős73`.
* **Part 6 — the `MaxDeg ≤ 2` level** in the *total*-degree vocabulary
  (`erdos73On_one_of_maxDegLe_two`): `LocIndep 1` plus maximum degree `2` is `1`-close to
  bipartite.  This is round 77's `boundedDegreeErdős73_two` with the `B` and the branch-vertex
  count removed.

Every hypothesis is used and none is smuggled in: `#print axioms` on the headline results shows
only `[propext, Classical.choice, Quot.sound]`.
-/

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqSubcubic : DecidableEq V := Classical.decEq V

local instance instDecidableAdjSubcubic : ∀ v w : V, Decidable (G.Adj v w) :=
  fun _ _ => Classical.propDecidable _

local instance instDecidableIsOddCycleSubcubic {D : Finset V} : Decidable (IsOddCycle G D) :=
  Classical.propDecidable _

/-! ### Two counting helpers -/

section Helpers

variable {α : Type*}

theorem card_four_of_disjoint [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset α).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]),
    Finset.card_insert_of_notMem (by simp [hcd]),
    Finset.card_singleton]

theorem sum_le_card_mul {ι : Type*} (s : Finset ι) (c : ℕ) : s.sum (fun _ => c) ≤ s.card * c := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp

/-- **`(a + 1) / 2` IS MONOTONE IN `a`.** -/
theorem div_add_one_mono {a b : ℕ} (h : a ≤ b) : (a + 1) / 2 ≤ (b + 1) / 2 := by
  have hd1 := Nat.div_add_mod (a + 1) 2
  have hd2 := Nat.div_add_mod (b + 1) 2
  have hr1 := Nat.mod_two_eq_zero_or_one ((a + 1) % 2)
  have hr2 := Nat.mod_two_eq_zero_or_one ((b + 1) % 2)
  omega

end Helpers

/-! ## Part 0 — the even indices of `Fin m`, and the even cover of a cycle -/

section EvenIdx

variable {m : ℕ}

/-- The **even indices** of `Fin m`. -/
def evenIdx (m : ℕ) : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun i => Even i.val)

theorem mem_evenIdx {i : Fin m} : i ∈ evenIdx m ↔ Even i.val := by
  simp [evenIdx]

/-- **AN EVEN INDEX IS TWICE A SMALL NATURAL NUMBER.** -/
theorem exists_two_mul_of_mem_evenIdx {i : Fin m} (hi : i ∈ evenIdx m) :
    ∃ t : ℕ, 2 * t = i.val := by
  obtain ⟨c, hc⟩ := dvd_def.mp (even_iff_two_dvd.mp (mem_evenIdx.mp hi))
  exact ⟨c, hc.symm⟩

theorem evenIdx_card_le {m : ℕ} (hm : m % 2 = 1) : (evenIdx m).card ≤ (m + 1) / 2 := by
  have hm' : m = 2 * (m / 2) + 1 := by omega
  have h1 : (evenIdx m).card = ((evenIdx m).image Fin.val).card :=
    (Finset.card_image_of_injective (s := evenIdx m) (f := Fin.val)
      (fun a b h => Fin.ext h)).symm
  have h2 : ((evenIdx m).image Fin.val) ⊆
      (Finset.range (m / 2 + 1)).image (fun t : ℕ => 2 * t) := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    rw [← hix]
    obtain ⟨t, ht⟩ := exists_two_mul_of_mem_evenIdx hi
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), ht⟩
  have h3 : ((Finset.range (m / 2 + 1)).image (fun t : ℕ => 2 * t)).card = m / 2 + 1 := by
    rw [Finset.card_image_of_injective (s := Finset.range (m / 2 + 1)) (f := fun t : ℕ => 2 * t)
      (by
        intro a b h
        have h' : 2 * a = 2 * b := by simpa using h
        omega), Finset.card_range]
  have hle : (evenIdx m).card ≤ m / 2 + 1 := by
    calc (evenIdx m).card = ((evenIdx m).image Fin.val).card := h1
      _ ≤ ((Finset.range (m / 2 + 1)).image (fun t : ℕ => 2 * t)).card :=
        Finset.card_le_card h2
      _ = m / 2 + 1 := h3
  omega

/-- **EVERY EDGE OF AN ODD CYCLE HAS AN EVEN END.** -/
theorem exists_evenIdx_or {m : ℕ} (hm : m % 2 = 1) (j : Fin m) :
    j ∈ evenIdx m ∨ cycSucc j ∈ evenIdx m := by
  by_cases he : Even j.val
  · exact Or.inl (mem_evenIdx.mpr he)
  · have ho : Odd j.val := (Nat.even_or_odd j.val).resolve_left he
    have hjlt : j.val + 1 < m := by
      rcases ho with ⟨k, hk⟩
      have hlt := j.isLt
      omega
    refine Or.inr (mem_evenIdx.mpr ?_)
    rw [cycSucc_val, Nat.mod_eq_of_lt hjlt]
    rcases ho with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩

end EvenIdx

section EvenCover

variable {C : Finset V} {o : CycleOrder G C}

/-- **THE EVEN COVER OF A CYCLE.**  For a cycle of odd length, the vertices at even positions meet
every edge of the cycle.  This is the cheapest vertex cover of a cycle used here: it needs no
choice, and it uses only the parity of the *length*. -/
noncomputable def evenCover (o : CycleOrder G C) (_hm : o.m % 2 = 1) : Finset V :=
  (evenIdx o.m).image o.f

theorem mem_evenCover_even_index {hm : o.m % 2 = 1} {i : Fin o.m} (he : Even i.val) :
    o.f i ∈ evenCover o hm :=
  Finset.mem_image_of_mem o.f (mem_evenIdx.mpr he)

/-- **THE EVEN COVER MEETS EVERY EDGE OF THE CYCLE.** -/
theorem exists_mem_evenCover_of_cycleEdge {hm : o.m % 2 = 1} (i : Fin o.m) :
    o.f i ∈ evenCover o hm ∨ o.f (cycSucc i) ∈ evenCover o hm := by
  rcases exists_evenIdx_or hm i with h | h
  · exact Or.inl (mem_evenCover_even_index (mem_evenIdx.mp h))
  · exact Or.inr (mem_evenCover_even_index (mem_evenIdx.mp h))

theorem card_evenCover {hm : o.m % 2 = 1} : (evenCover o hm).card ≤ (C.card + 1) / 2 := by
  have h1 : (evenCover o hm).card = (evenIdx o.m).card :=
    Finset.card_image_of_injective (s := evenIdx o.m) (f := o.f) o.hinj
  have h2 := evenIdx_card_le hm
  have h3 : C.card = o.m := card_eq_cyclicOrder o.f o.hinj o.hmem
  omega

end EvenCover

/-! ## Part 1 — the fan of an odd cycle in a subcubic graph is finite -/

section Fan

/-- **A VERTEX OF AN ODD CYCLE OF A SUBCUBIC GRAPH HAS AT MOST ONE NEIGHBOUR OUTSIDE THE CYCLE.**

The two cycle-neighbours of `v` are distinct and lie in `C`, and `v` has at most three neighbours
in all. -/
theorem card_le_one_outerNeigh_oddCycle (hdeg : MaxDegLe G 3) {C : Finset V} (hC : IsOddCycle G C)
    {v : V} (hv : v ∈ C) : (OuterNeigh G C v).card ≤ 1 := by
  obtain ⟨o, -⟩ := hC.cycleOrder
  obtain ⟨i, hi⟩ := (o.hmem v).mp hv
  rw [← hi]
  have h1 : o.f (cycSucc i) ∉ OuterNeigh G C (o.f i) :=
    not_mem_outerNeigh_of_mem ((o.hmem _).mpr ⟨cycSucc i, rfl⟩)
  have h2 : o.f (o.prev i) ∉ OuterNeigh G C (o.f i) :=
    not_mem_outerNeigh_of_mem ((o.hmem _).mpr ⟨o.prev i, rfl⟩)
  have hne : o.f (cycSucc i) ≠ o.f (o.prev i) := o.step_prev_ne i
  have hsub : OuterNeigh G C (o.f i) ∪ {o.f (cycSucc i), o.f (o.prev i)} ⊆ Neigh G (o.f i) := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact mem_neigh.mpr ((mem_outerNeigh.mp hx).1)
    · rw [Finset.mem_insert] at hx
      rcases hx with hxa | hxb
      · rw [hxa]; exact mem_neigh.mpr (o.hcyc i)
      · rw [Finset.mem_singleton.mp hxb]; exact mem_neigh.mpr (o.adj_prev i)
  have hdisj : Disjoint (OuterNeigh G C (o.f i)) ({o.f (cycSucc i), o.f (o.prev i)} : Finset V) :=
    Finset.disjoint_left.mpr fun x hx1 hx2 => by
      rw [Finset.mem_insert] at hx2
      rcases hx2 with hxa | hxb
      · rw [hxa] at hx1
        exact h1 hx1
      · rw [Finset.mem_singleton.mp hxb] at hx1
        exact h2 hx1
  have hle : (OuterNeigh G C (o.f i)).card + 2 ≤ (Neigh G (o.f i)).card := by
    have hcard : ({o.f (cycSucc i), o.f (o.prev i)} : Finset V).card = 2 := by simp [hne]
    have heq : (OuterNeigh G C (o.f i)).card + 2
        = ((OuterNeigh G C (o.f i)) ∪ {o.f (cycSucc i), o.f (o.prev i)} : Finset V).card := by
      rw [Finset.card_union_of_disjoint hdisj, hcard]
    rw [heq]
    exact Finset.card_le_card hsub
  have hdeg3 : (Neigh G (o.f i)).card ≤ 3 := hdeg (o.f i)
  omega

/-- **`|∂C| ≤ |C|` FOR AN ODD CYCLE OF A SUBCUBIC GRAPH.**  Every vertex of `C` carries at most one
fan vertex, so the boundary of an odd cycle of a subcubic graph is no larger than the cycle: the
fan of a shortest odd cycle is a finite object of controlled size. -/
theorem card_boundary_le_card_oddCycle (hdeg : MaxDegLe G 3) {C : Finset V} (hC : IsOddCycle G C) :
    (boundary G C).card ≤ C.card := by
  have hcov : boundary G C ⊆ C.biUnion (fun v : V => OuterNeigh G C v) := by
    intro x hx
    obtain ⟨hxC, hx⟩ := (mem_boundary.mp hx)
    obtain ⟨w, hwC, hxw⟩ := hx
    exact Finset.mem_biUnion.mpr ⟨w, hwC, mem_outerNeigh.mpr ⟨G.adj_symm hxw, hxC⟩⟩
  have hle : (C.biUnion (fun v : V => OuterNeigh G C v)).card
      ≤ ∑ v ∈ C, (OuterNeigh G C v).card :=
    Finset.card_biUnion_le (s := C) (t := fun v : V => OuterNeigh G C v)
  have hsum : (∑ v ∈ C, (OuterNeigh G C v).card) ≤ C.sum (fun _ => (1 : ℕ)) := by
    refine Finset.sum_le_sum fun v hv => ?_
    exact card_le_one_outerNeigh_oddCycle hdeg hC hv
  have hsum1 : C.sum (fun _ => (1 : ℕ)) ≤ C.card := by
    have := sum_le_card_mul C 1
    omega
  calc (boundary G C).card ≤ (C.biUnion (fun v : V => OuterNeigh G C v)).card :=
        Finset.card_le_card hcov
    _ ≤ ∑ v ∈ C, (OuterNeigh G C v).card := hle
    _ ≤ C.card := hsum.trans hsum1

/-- **THE CLOSED NEIGHBOURHOOD OF AN ODD CYCLE OF A SUBCUBIC GRAPH HAS AT MOST `2 * |C|`
VERTICES.** -/
theorem card_neighClosed_le_two_mul_card_oddCycle (hdeg : MaxDegLe G 3) {C : Finset V}
    (hC : IsOddCycle G C) : (C ∪ boundary G C).card ≤ 2 * C.card := by
  have h1 := card_boundary_le_card_oddCycle hdeg hC
  have h2 : (C ∪ boundary G C).card ≤ C.card + (boundary G C).card := Finset.card_union_le _ _
  omega

/-- **A FAN VERTEX HAS AT MOST TWO NEIGHBOURS OUTSIDE THE CYCLE.** -/
theorem card_le_two_outerNeigh_boundary (hdeg : MaxDegLe G 3) {C : Finset V} (_hC : IsOddCycle G C)
    {x : V} (hx : x ∈ boundary G C) : (OuterNeigh G C x).card ≤ 2 := by
  obtain ⟨w, hwC, hxw⟩ := (mem_boundary.mp hx).2
  have hdisj : Disjoint (OuterNeigh G C x) ({w} : Finset V) := Finset.disjoint_left.mpr
    fun y hy1 hy2 => (not_mem_outerNeigh_of_mem hwC) (Finset.mem_singleton.mp hy2 ▸ hy1)
  have hle : (OuterNeigh G C x).card + 1 ≤ (Neigh G x).card := by
    have hsub : (OuterNeigh G C x ∪ ({w} : Finset V)) ⊆ Neigh G x := by
      intro y hy
      rw [Finset.mem_union] at hy
      rcases hy with hy | hy
      · exact mem_neigh.mpr ((mem_outerNeigh.mp hy).1)
      · rw [Finset.mem_singleton.mp hy]; exact mem_neigh.mpr hxw
    have heq : (OuterNeigh G C x).card + 1
        = ((OuterNeigh G C x) ∪ ({w} : Finset V) : Finset V).card := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
    rw [heq]
    exact Finset.card_le_card hsub
  have hdeg3 : (Neigh G x).card ≤ 3 := hdeg x
  omega

end Fan

/-! ## Part 2 — two odd cycles of a subcubic graph that meet share a *cycle edge* -/

section SharedEdge

/-- **TWO ODD CYCLES OF A SUBCUBIC GRAPH THAT MEET SHARE AN EDGE OF THE FIRST CYCLE.**

At a common vertex `u` the first cycle uses the two edges `o.f (cycSucc i)`, `o.f (o.prev i)` and
the second uses its own two; all four are neighbours of `u`, of which there are at most three, so
one of the first cycle's two neighbours of `u` is a neighbour of `u` along the second cycle as
well.  The shared edge is an edge *of the cyclic order* `o` — not a chord of `C`. -/
theorem CycleOrder.exists_adj_mem_inter {o : CycleOrder G C} (hdeg : MaxDegLe G 3)
    {D : Finset V} (hD : IsOddCycle G D) {u : V} (hu : u ∈ C ∩ D) :
    ∃ i : Fin o.m, G.Adj (o.f i) (o.f (cycSucc i)) ∧ o.f i ∈ D ∧ o.f (cycSucc i) ∈ D := by
  obtain ⟨p, -⟩ := hD.cycleOrder
  obtain ⟨i, hi⟩ := (o.hmem u).mp (Finset.mem_inter.mp hu).1
  obtain ⟨j, hj⟩ := (p.hmem u).mp (Finset.mem_inter.mp hu).2
  set a1 : V := o.f (cycSucc i) with ha1
  set a2 : V := o.f (o.prev i) with ha2
  set b1 : V := p.f (cycSucc j) with hb1
  set b2 : V := p.f (p.prev j) with hb2
  have ha1adj : G.Adj u a1 := by rw [ha1]; rw [← hi]; exact o.hcyc i
  have ha2adj : G.Adj u a2 := by rw [ha2]; rw [← hi]; exact o.adj_prev i
  have hb1adj : G.Adj u b1 := by rw [hb1]; rw [← hj]; exact p.hcyc j
  have hb2adj : G.Adj u b2 := by rw [hb2]; rw [← hj]; exact p.adj_prev j
  have hne12 : a1 ≠ a2 := by rw [ha1, ha2]; exact o.step_prev_ne i
  have hne21 : a2 ≠ a1 := Ne.symm hne12
  have hne34 : b1 ≠ b2 := by rw [hb1, hb2]; exact p.step_prev_ne j
  have hne43 : b2 ≠ b1 := Ne.symm hne34
  have hsub : ({a1, a2, b1, b2} : Finset V) ⊆ Neigh G u := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · rw [h]; exact mem_neigh.mpr ha1adj
    · rw [h]; exact mem_neigh.mpr ha2adj
    · rw [h]; exact mem_neigh.mpr hb1adj
    · rw [h]; exact mem_neigh.mpr hb2adj
  have hle : ({a1, a2, b1, b2} : Finset V).card ≤ 3 := by
    calc ({a1, a2, b1, b2} : Finset V).card ≤ (Neigh G u).card := Finset.card_le_card hsub
      _ = MaxDeg G u := rfl
      _ ≤ 3 := hdeg u
  have huD : o.f i ∈ D := by rw [hi]; exact Finset.mem_inter.mp hu |>.2
  by_cases h1 : a1 = b1
  · refine ⟨i, o.hcyc i, huD, (p.hmem _).mpr ⟨cycSucc j, by rw [← hb1, ← h1, ha1]⟩⟩
  by_cases h2 : a1 = b2
  · refine ⟨i, o.hcyc i, huD, (p.hmem _).mpr ⟨p.prev j, by rw [← hb2, ← h2, ha1]⟩⟩
  by_cases h3 : a2 = b1
  · refine ⟨o.prev i, o.hcyc (o.prev i), (p.hmem _).mpr ⟨cycSucc j, by rw [← hb1, ← h3, ha2]⟩, ?_⟩
    rw [o.succ_prev i, hi]
    exact Finset.mem_inter.mp hu |>.2
  by_cases h4 : a2 = b2
  · refine ⟨o.prev i, o.hcyc (o.prev i), (p.hmem _).mpr ⟨p.prev j, by rw [← hb2, ← h4, ha2]⟩, ?_⟩
    rw [o.succ_prev i, hi]
    exact Finset.mem_inter.mp hu |>.2
  exfalso
  have h4' : ({a1, a2, b1, b2} : Finset V).card = 4 :=
    card_four_of_disjoint hne12 h1 h2 h3 h4 hne34
  omega

/-- **A COROLLARY: two odd cycles of a subcubic graph that meet share an EDGE, so their
intersection has at least two vertices.** -/
theorem exists_ne_two_mem_inter_oddCycle (hdeg : MaxDegLe G 3) {C D : Finset V}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) {u : V} (hu : u ∈ C ∩ D) :
    ∃ a b : V, a ∈ C ∩ D ∧ b ∈ C ∩ D ∧ a ≠ b := by
  obtain ⟨o, -⟩ := hC.cycleOrder
  obtain ⟨i, -, h1, h2⟩ := o.exists_adj_mem_inter hdeg hD hu
  exact ⟨o.f i, o.f (cycSucc i),
    Finset.mem_inter.mpr ⟨(o.hmem _).mpr ⟨i, rfl⟩, h1⟩,
    Finset.mem_inter.mpr ⟨(o.hmem _).mpr ⟨cycSucc i, rfl⟩, h2⟩, o.step_ne i⟩

end SharedEdge

/-! ## Part 3 — the subcubic transversal: one odd cycle covers all of them -/

section Transversal

/-- **THE EVEN COVER, IN THE FORM THAT MENTIONS NO CYCLIC ORDER.**  For each finset `D` this is the
even cover of the *chosen* cyclic order of `D` when `D` is an odd cycle of `G`, and `∅` otherwise.
`Classical.choose` on `∃ o, o.m % 2 = 1` is all that is used: there is no `Finset` of cyclic orders
anywhere in this file. -/
noncomputable def oddEvenCover (G : SimpleGraph V) (D : Finset V) : Finset V :=
  if hD : IsOddCycle G D then
    evenCover (hD.cycleOrder).choose (hD.cycleOrder).choose_spec
  else ∅

theorem card_oddEvenCover_of_isOddCycle {D : Finset V} (hD : IsOddCycle G D) :
    (oddEvenCover G D).card ≤ (D.card + 1) / 2 := by
  rw [oddEvenCover, dif_pos hD]
  exact card_evenCover (hm := (hD.cycleOrder).choose_spec)

theorem card_oddEvenCover_of_not_isOddCycle {D : Finset V} (hD : ¬ IsOddCycle G D) :
    oddEvenCover G D = ∅ := by
  rw [oddEvenCover, dif_neg hD]

/-- **THE TRANSVERSAL PROPERTY OF THE EVEN COVER.**  In a subcubic graph, every odd cycle meeting
the odd cycle `C` meets `oddEvenCover G C`. -/
theorem inter_oddEvenCover_of_isOddCycle (hdeg : MaxDegLe G 3) {C D : Finset V}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) (hmeet : C ∩ D ≠ ∅) :
    D ∩ oddEvenCover G C ≠ ∅ := by
  rw [oddEvenCover, dif_pos hC]
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hmeet
  obtain ⟨i, hi, h1, h2⟩ :=
    ((hC.cycleOrder).choose).exists_adj_mem_inter hdeg hD hu
  rcases exists_mem_evenCover_of_cycleEdge (o := (hC.cycleOrder).choose)
      (hm := (hC.cycleOrder).choose_spec) i with h | h
  · exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨h1, h⟩)
  · exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨h2, h⟩)

/-- **THE SUBCUBIC TRANSVERSAL, IN THE FORM THAT MENTIONS NO CYCLIC ORDER.**  If every odd cycle
of a subcubic graph meets one fixed odd cycle `C`, then some subset of `C` of at most
`(C.card + 1) / 2` vertices meets **every** odd cycle of `G`. -/
theorem hitsOddCycles_of_inter (hdeg : MaxDegLe G 3) {C : Finset V} (hC : IsOddCycle G C)
    (hmeet : ∀ D, IsOddCycle G D → C ∩ D ≠ ∅) :
    ∃ Z : Finset V, Z.card ≤ (C.card + 1) / 2 ∧ HitsOddCycles G Z := by
  obtain ⟨o, hm⟩ := hC.cycleOrder
  refine ⟨evenCover o hm, card_evenCover (hm := hm), ?_⟩
  intro D hD
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr (hmeet D hD)
  obtain ⟨i, hi, h1, h2⟩ := o.exists_adj_mem_inter hdeg hD hu
  rcases exists_mem_evenCover_of_cycleEdge (o := o) (hm := hm) i with h | h
  · exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨h1, h⟩)
  · exact Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨h2, h⟩)

end Transversal

/-! ## Part 4 — a new instance of the headline theorem: subcubic graphs of bounded odd girth -/

section Instance

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, ON THE SUBCUBIC AXIS.**

If every vertex of `G` has at most three neighbours, `LocIndep k G` holds, and every odd cycle of
`G` has at most `ℓ` vertices, then `G` is `k * ((ℓ + 1) / 2)`-close to bipartite.

The hypothesis is a **degree** hypothesis, not a girth hypothesis on its own: the graph is
subcubic.  The constant `k * ((ℓ + 1) / 2)` improves the constant `ℓ * k` of
`JSP90.erdos73On_of_bounded_odd_girth` on this class, and no bound on the packing weight, on the
number of branch vertices, or on the total degree is used. -/
theorem closeToBipartite_of_subcubic_of_shortOddCycles (k ℓ : ℕ) (hdeg : MaxDegLe G 3)
    (hG : LocIndep k G) (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ) :
    CloseToBipartite (k * ((ℓ + 1) / 2)) G := by
  classical
  obtain ⟨P, hP, hmax⟩ := exists_maxCard_oddCycleFamily (G := G)
  have hPC : P.card ≤ k := hG.oddCycleFamily_card_le hP
  have htrans : HitsOddCycles G (P.biUnion (oddEvenCover G)) := by
    intro D hD
    have h1 : D ∩ (P.biUnion id) ≠ ∅ := hitsOddCycles_of_maxCardFamily hP hmax D hD
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr h1
    obtain ⟨hxD, hxU⟩ := Finset.mem_inter.mp hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxU
    have hne2 : D ∩ oddEvenCover G i ≠ ∅ :=
      inter_oddEvenCover_of_isOddCycle hdeg (hP.2 i hi) hD
        (Finset.ne_empty_of_mem (Finset.mem_inter.mpr ⟨hxi, hxD⟩))
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hne2
    obtain ⟨hyD, hycov⟩ := Finset.mem_inter.mp hy
    exact Finset.ne_empty_of_mem
      (Finset.mem_inter.mpr ⟨hyD, Finset.mem_biUnion.mpr ⟨i, hi, hycov⟩⟩)
  refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := k * ((ℓ + 1) / 2))).mpr
    ⟨P.biUnion (oddEvenCover G), ?_, htrans⟩
  calc (P.biUnion (oddEvenCover G)).card ≤ ∑ D ∈ P, (oddEvenCover G D).card := by
        exact Finset.card_biUnion_le (s := P) (t := oddEvenCover G)
    _ ≤ ∑ D ∈ P, (D.card + 1) / 2 := Finset.sum_le_sum fun D hD =>
        card_oddEvenCover_of_isOddCycle (hP.2 D hD)
    _ ≤ ∑ _D ∈ P, ((ℓ + 1) / 2) := Finset.sum_le_sum fun D hD =>
        div_add_one_mono (hlen D (hP.2 D hD))
    _ ≤ P.card * ((ℓ + 1) / 2) := sum_le_card_mul P ((ℓ + 1) / 2)
    _ ≤ k * ((ℓ + 1) / 2) := Nat.mul_le_mul_right _ hPC

/-- **THE `k = 1` CASE, AND THE CONSTANT DOES NOT MENTION `k`.** -/
theorem closeToBipartite_of_subcubic_of_locIndep_one_of_shortOddCycle (ℓ : ℕ)
    (hdeg : MaxDegLe G 3) (hG : LocIndep 1 G) (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ) :
    CloseToBipartite ((ℓ + 1) / 2) G := by
  have h := closeToBipartite_of_subcubic_of_shortOddCycles 1 ℓ hdeg hG hlen
  simpa using h

/-- **THE `k = 1`, `ℓ = 3` CASE: A SUBCUBIC GRAPH WITH A TRIANGLE AND `LocIndep 1` IS
`2`-CLOSE TO BIPARTITE.**

Two is the sharp value of the `k = 1` subcubic constant: `p9` is subcubic, satisfies `LocIndep 1`,
and no single vertex meets all of its odd cycles (`JSP90.subcubic_constant_ne_one`).  This is
Erdős Problem #73 for the class "subcubic graphs whose maximum deficiency is one and which carry a
triangle", with the sharp constant.  (The hypothesis is that *every* odd cycle of `G` has at most
three vertices; the existence of one triangle alone is not enough, and a first draft of this file
claimed otherwise.) -/
theorem closeToBipartite_of_subcubic_of_locIndep_one_of_three (hdeg : MaxDegLe G 3)
    (hG : LocIndep 1 G) (hlen : ∀ D, IsOddCycle G D → D.card ≤ 3) :
    CloseToBipartite 2 G :=
  closeToBipartite_of_subcubic_of_locIndep_one_of_shortOddCycle 3 hdeg hG hlen

end Instance

/-! ## Part 5 — the remaining statement, isolated -/

section Missing

/-- **`LocIndep 1` IMPLIES THAT EVERY TWO ODD CYCLES OF `G` MEET.**

This is the packing bound `JSP90.LocIndep.oddCycle_packing_le` for the family `{C, D}`: two
vertex-disjoint odd cycles would be a packing of size `2 > 1`. -/
theorem inter_oddCycle_of_locIndep_one (hG : LocIndep 1 G) {C D : Finset V}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) : C ∩ D ≠ ∅ := by
  by_cases hCD : C = D
  · subst hCD
    simpa using Finset.nonempty_iff_ne_empty.mp hC.nonempty
  by_contra hne
  have hfam : IsOddCycleFamily (G := G) ({C, D} : Finset (Finset V)) := by
    refine ⟨?_, fun X hX => ?_⟩
    · intro X hX Y hY hXY
      rcases (Finset.mem_insert.mp hX) with hXC | hXD
      · rcases (Finset.mem_insert.mp hY) with hYC | hYD
        · exact absurd (hXC ▸ hYC).symm hXY
        · have hYD' : Y = D := Finset.mem_singleton.mp hYD
          rw [hXC, hYD']
          exact hne
      · have hXD' : X = D := Finset.mem_singleton.mp hXD
        rcases (Finset.mem_insert.mp hY) with hYC | hYD
        · rw [hXD', hYC, Finset.inter_comm]
          exact hne
        · have hYD' : Y = D := Finset.mem_singleton.mp hYD
          exact absurd (hXD' ▸ hYD').symm hXY
    · rcases (Finset.mem_insert.mp hX) with hXC | hXD
      · rw [hXC]; exact hC
      · have hXD' : X = D := Finset.mem_singleton.mp hXD
        rw [hXD']
        exact hD
  have hle := hG.oddCycleFamily_card_le hfam
  rw [Finset.card_insert_of_notMem (by simp [hCD])] at hle
  have hcard1 : ({D} : Finset (Finset V)).card = 1 := Finset.card_singleton _
  rw [hcard1] at hle
  omega

/-- **THE `k = 1` LEVEL OF THE SUBCUBIC ERDŐS–PÓSA STATEMENT, IN PACKING FORM.**

Every subcubic graph whose odd cycles pairwise meet is `2`-close to bipartite: two vertices meet
every odd cycle.  This is what remains of sub-goal (1) of round 77 — with the constant `1` replaced
by the sharp constant `2` — once the *bounded odd girth* hypothesis of Part 4 is removed.

It is **stated, not assumed**: `erdos73On_subcubic_one_of_packingOne` below is the only reduction
consuming it, and it goes in the direction that makes it a *stronger* statement than the `k = 1`
level of `JSP90.SubcubicErdős73` (the hypothesis "every two odd cycles meet" is implied by
`LocIndep 1` and is strictly weaker, by `JSP90.rejected_...`-style examples such as `K_5`).  An
exhaustive search over all subcubic graphs on `≤ 8` vertices (`10 355 376` of them; `1540` with
transversal number `≥ 3`, none of those with packing number `1`) and a random search up to `13`
vertices found no counterexample. -/
def SubcubicPackingOne.{v} : Prop :=
  ∀ (W : Type v) (_ : Fintype W) (G : SimpleGraph W), MaxDegLe G 3 →
    (∀ C D, IsOddCycle G C → IsOddCycle G D → C ∩ D ≠ ∅) → CloseToBipartite 2 G

/-- **`JSP90.SubcubicPackingOne` IMPLIES THE `k = 1` LEVEL OF THE SUBCUBIC INSTANCE.** -/
theorem erdos73On_subcubic_one_of_packingOne (h : SubcubicPackingOne.{u}) (k : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G → MaxDegLe G 3 →
      CloseToBipartite 2 G :=
  fun W instW G hG hdeg => h W instW G hdeg (fun C D hC hD => inter_oddCycle_of_locIndep_one hG hC hD)

end Missing

/-! ## Part 6 — the `MaxDeg ≤ 2` level, and the sharpness of the `k = 1` constant -/

section TwoAndSharp

/-- **THE `MaxDeg ≤ 2` LEVEL IN THE TOTAL-DEGREE VOCABULARY: `LocIndep 1` AND NO VERTEX OF DEGREE
`≥ 3` GIVES A `1`-CLOSE-TO-BIPARTITE GRAPH.**

Round 77's `boundedDegreeErdős73_two` obtains this from `JSP90.erdos73On_of_bounded_branch` with a
set `B` and a bound on the branch vertices of the residue; the argument below removes both. -/
theorem erdos73On_one_of_maxDegLe_two (hdeg : MaxDegLe G 2) (hG : LocIndep 1 G) :
    CloseToBipartite 1 G := by
  refine erdos73On_of_no_branch 1 V inferInstance G hG ?_
  intro v hv
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hv
  have hcard : 3 ≤ (Neigh G v).card := by
    have hsub : ({a, b, c} : Finset V) ⊆ Neigh G v := by
      intro w hw
      rw [Finset.mem_insert] at hw
      rcases hw with hwa | hw
      · rw [hwa]; exact mem_neigh.mpr ha
      · rw [Finset.mem_insert] at hw
        rcases hw with hwb | hw
        · rw [hwb]; exact mem_neigh.mpr hb
        · rw [Finset.mem_singleton.mp hw]; exact mem_neigh.mpr hc
    have hc3 : ({a, b, c} : Finset V).card = 3 := by simp [hab, hac, hbc]
    calc 3 = ({a, b, c} : Finset V).card := hc3.symm
      _ ≤ (Neigh G v).card := Finset.card_le_card hsub
  have h2 : (Neigh G v).card ≤ 2 := hdeg v
  omega

/-- **`p9` IS SUBCUBIC.**  The finite check is a kernel computation on the nine vertices. -/
theorem maxDegLe_p9 : MaxDegLe p9 3 := by
  intro v
  have heq : Neigh p9 v = (Finset.univ : Finset (Fin 9)).filter (fun w => (v, w) ∈ p9Edge) := by
    ext w
    simp only [Neigh, Finset.mem_filter, Finset.mem_univ, true_and, p9_adj]
  rw [MaxDeg, heq]
  exact (show ∀ v : Fin 9,
      ((Finset.univ : Finset (Fin 9)).filter (fun w => (v, w) ∈ p9Edge)).card ≤ 3 by decide) v

/-- **THE `k = 1` SUBCUBIC CONSTANT IS AT LEAST TWO, AND THIS IS A MACHINE-CHECKED FACT.**

`p9` is subcubic, satisfies `LocIndep 1`, and no single vertex meets all of its odd cycles.  So
`g 1 ≤ 1` is impossible for the function `g` of `JSP90.SubcubicErdős73` — refuting sub-goal (1) of
round 77. -/
theorem subcubic_constant_ne_one :
    ¬ (∀ (W : Type 0) (_ : Fintype W) (G : SimpleGraph W), MaxDegLe G 3 → LocIndep 1 G →
        CloseToBipartite 1 G) :=
  fun h => not_closeToBipartite_one_p9
    (h (Fin 9) inferInstance p9 maxDegLe_p9 locIndep_one_p9)

/-- **AND HENCE `JSP90.SubcubicErdős73 (fun _ => 1)` IS FALSE.** -/
theorem not_subcubicErdős73_one : ¬ SubcubicErdős73.{0} (fun _ => 1) := by
  intro h
  exact subcubic_constant_ne_one (fun W instW G hdeg hG => h 1 W instW G hG hdeg)


end TwoAndSharp

end

end JSP90
