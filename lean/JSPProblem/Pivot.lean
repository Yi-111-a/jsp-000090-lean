import JSPProblem.Sparse

/-!
# JSP-000090, round 100 — the **LOCAL-TRANSVERSAL axis**: the distance-one neighbourhood of a
maximum packing of odd cycles is an odd cycle transversal, and the counting bound at an odd cycle
in an arbitrary degree range

Attack family 41.  Every axis so far turns an *existence* statement about an odd cycle transversal
into a number (`JSPProblem/Transversal.lean`: the transversal is the union of a maximum packing;
`JSPProblem/Residue.lean`: the transversal is a union of cycles; `JSPProblem/Sparse.lean`: `⌊|E|/2⌋`).
This file asks for something different: **where must the transversal sit?**

## Part 1 — the local certificate

The classical manipulation at the heart of every Erdős–Pósa proof for odd cycles is the
*distance-one neighbourhood of a packing*: an odd cycle which misses the neighbourhood of a maximum
packing could be added to the packing.  Stated and proved here for the first time:

* **`JSP90.NeighClosed G C = C ∪ ∂C`**, the closed neighbourhood of a vertex set;
* **`JSP90.hitsOddCycles_neighClosed_of_maxPacking` — the distance-one neighbourhood of a maximum
  packing of odd cycles is an odd cycle transversal.**  This is the "a packing is maximal, hence
  its neighbourhood catches everything" step, in its local form;
* the counting half, in a form that works at **every** degree, not only at `3`:
  `JSP90.two_le_card_inter_neigh_of_mem_oddCycle` (a vertex of an odd cycle has two neighbours *on*
  the cycle — the fact `JSPProblem/Subcubic.lean` used implicitly in
  `card_le_one_outerNeigh_oddCycle`), `JSP90.card_outerNeigh_le_card_neigh_sub_two`,
  `JSP90.card_boundary_le_card_mul_sub_two` (which **generalises** Subcubic's
  `card_boundary_le_card_oddCycle`, the `d = 3` case, to every degree `d ≥ 2` and to every set `S`
  each of whose vertices has two neighbours in `S`), and `JSP90.card_neighClosed_le_card_mul_sub_one`
  (which generalises `card_neighClosed_le_two_mul_card_oddCycle`);
* `JSP90.card_boundary_of_maxPacking_le` — the neighbourhood of a maximum packing, counted, using
  the disjoint additivity of `JSPProblem/Packing.lean`.

## Part 2 — an instance of the headline theorem, and its honest constant

`JSP90.erdos73On_of_neighClosedPacking` — Erdős's local hypothesis, all odd cycles of length at
most `ℓ`, maximum degree at most `d`, and **a certificate**: the transversal is the distance-one
neighbourhood of a maximum packing.

**The honest comparison** (also recorded in `discovery/JSP-000090/policy.json`):
`JSPProblem/Transversal.lean` already proves `CloseToBipartite (ℓ * k) G` under *strictly weaker*
hypotheses (no degree bound at all), so the constant `k * ℓ * (d - 1)` of this file is **larger**,
not smaller.  What this file adds is the *local certificate* — the transversal is a bounded-distance
object around a packing — and the degree bound in an arbitrary range.

## Part 3 — the odd girth from **below** carries no information (two machine-checked refutations)

Round 99 recorded `JSP90.BoundedOddGirthEdgeCount` — "odd girth `ℓ` and degree `≤ d` ⟹ `f ℓ d`-close
to bipartite" — as the next statement of the edge-counting axis, and
`discovery/JSP-000090/policy.json` option (A) for round 100 was to prove it.  **It is false**, and
the failure is now machine-checked, in two separate ways:

* **`JSP90.not_boundedOddGirthEdgeCount`** — `kTriangles k` has odd girth `3`, maximum degree `2`,
  and odd cycle transversal number exactly `k`, so no function of the odd girth and the degree
  bounds the transversal;
* **`JSP90.not_oddGirth_bound_without_packing`** — the *direction* matters: an **upper** bound on the
  length of the odd cycles is what `JSPProblem/Transversal.lean` uses, and it works; a **lower**
  bound (an odd girth from below, `JSP90.OddGirthGe ℓ G`) bounds nothing, because `kTriangles 5`
  has odd girth `3 ≤ ℓ = 3` and needs `5` vertices.

The correct statement is the one with the packing bound, and Part 4 proves it.

## Part 4 — **exactness at maximum degree two**: `τ_odd(G) = ν_odd(G)`

`JSPProblem/Subcubic.lean` has `erdos73On_one_of_maxDegLe_two` (the case `k = 1` only).  This file
proves the **exact identity** of the two numbers for every `m`:

* `JSP90.disjointFamily_oddCycles_of_maxDegLe_two` — the odd cycles of a graph of maximum degree
  `≤ 2` are pairwise vertex-disjoint (through `JSP90.disjointFamily_oddCycles_of_no_branch`);
* `JSP90.maxDegLe_two_iff_oddCyclePackingLe` — **`CloseToBipartite m G ↔ OddCyclePackingLe m G`**:
  the least odd cycle transversal of a graph of maximum degree `≤ 2` *equals* its packing number;
* `JSP90.erdos73On_of_maxDegLe_two` — Erdős #73 on that class with the **optimal constant `k`**,
  and `JSP90.erdos73On_of_maxDegLe_two_optimal` — the constant is attained (`kTriangles k`).

`jsp_000090_main` is not declared: behind it stands `JSP90.OddCycleErdosPosa r`.
-/

namespace JSP90

noncomputable section

variable {V : Type*} [Fintype V]

local instance instDecidableEqPivot : DecidableEq V := Classical.decEq V

local instance instDecidableRelPivot {G : SimpleGraph V} : DecidableRel G.Adj :=
  Classical.decRel G.Adj

/-! ### Part 0 — two auxiliary notions -/

section Aux

variable {G : SimpleGraph V}

/-- **`ℓ` is a lower bound for the odd girth of `G`**: every odd cycle of `G` has at least `ℓ`
vertices.

This is the *odd girth from below*.  Round 100 shows (`not_oddGirth_bound_without_packing`) that it
carries no information about the odd cycle transversal number; the hypothesis that `JSPProblem/
Transversal.lean` uses is the opposite one, `∀ C, IsOddCycle G C → C.card ≤ ℓ`. -/
noncomputable def OddGirthGe (ℓ : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ C : Finset V, IsOddCycle G C → ℓ ≤ C.card

/-- **`G` has at most `r` vertex-disjoint odd cycles**: every packing of odd cycles of `G` has at
most `r` members.  This is the packing half of Erdős #73 in the vocabulary of
`JSPProblem/Transversal.lean`; `LocIndep r G` implies it (`locIndep_oddCyclePackingLe`). -/
noncomputable def OddCyclePackingLe (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ P : Finset (Finset V), IsOddCycleFamily (G := G) P → P.card ≤ r

/-- **Erdős's local hypothesis bounds the packing number.** -/
theorem locIndep_oddCyclePackingLe {k : ℕ} (hG : LocIndep k G) : OddCyclePackingLe k G :=
  fun P hP => hG.oddCycleFamily_card_le hP

/-- **A sum of a constant is at most `|s|` times that constant.** -/
theorem sum_const_le_card_mul {ι : Type*} (s : Finset ι) (c : ℕ) :
    s.sum (fun _ => c) ≤ s.card * c := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Nat.succ_mul, ih]

end Aux

/-! ### Part 1 — the closed neighbourhood of a set, and its counting bound -/

section Neighbourhood

variable {G : SimpleGraph V}

/-- **THE CLOSED NEIGHBOURHOOD OF A VERTEX SET**: `C` together with the vertices adjacent to `C`.

`JSPProblem/Subcubic.lean` writes the same set as `C ∪ boundary G C`; giving it a name is what lets
the statements below be about "the distance-one neighbourhood" rather than about a union. -/
noncomputable def NeighClosed (G : SimpleGraph V) (C : Finset V) : Finset V := C ∪ boundary G C

theorem mem_neighClosed {C : Finset V} {v : V} :
    v ∈ NeighClosed G C ↔ v ∈ C ∨ (v ∉ C ∧ ∃ w ∈ C, G.Adj v w) := by
  rw [NeighClosed, Finset.mem_union, mem_boundary]

/-- **THE BOUNDARY OF A SET LIES OUTSIDE IT.** -/
theorem disjoint_boundary {C : Finset V} : Disjoint (boundary G C) C :=
  Finset.disjoint_left.mpr fun _ hx1 hx2 => (mem_boundary.mp hx1).1 hx2

/-- **A VERTEX OF AN ODD CYCLE HAS TWO NEIGHBOURS *ON* THE CYCLE.**

This is the local fact behind `JSP90.card_le_one_outerNeigh_oddCycle` of
`JSPProblem/Subcubic.lean` (which states the `d = 3` shadow of it) and behind the counting bound
below: the two cycle-neighbours of `v` are distinct and lie in `C`. -/
theorem two_le_card_inter_neigh_of_mem_oddCycle {C : Finset V} (hC : IsOddCycle G C) {v : V}
    (hv : v ∈ C) : 2 ≤ ((Neigh G v) ∩ C).card := by
  obtain ⟨o, -⟩ := hC.cycleOrder
  obtain ⟨i, hi⟩ := (o.hmem v).mp hv
  rw [← hi]
  have hsub : ({o.f (cycSucc i), o.f (o.prev i)} : Finset V) ⊆ Neigh G (o.f i) ∩ C := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with hxa | hxb
    · rw [hxa]
      exact Finset.mem_inter.mpr
        ⟨mem_neigh.mpr (o.hcyc i), (o.hmem _).mpr ⟨cycSucc i, rfl⟩⟩
    · rw [Finset.mem_singleton.mp hxb]
      exact Finset.mem_inter.mpr
        ⟨mem_neigh.mpr (o.adj_prev i), (o.hmem _).mpr ⟨o.prev i, rfl⟩⟩
  have hcard : ({o.f (cycSucc i), o.f (o.prev i)} : Finset V).card = 2 := by
    simp [o.step_prev_ne i]
  exact hcard.symm.le.trans (Finset.card_le_card hsub)

/-- **THE COUNTING LEMMA: IF EVERY VERTEX OF `S` HAS TWO NEIGHBOURS IN `S`, THEN THE BOUNDARY OF
`S` HAS AT MOST `|S| * (d - 2)` VERTICES IN A GRAPH OF MAXIMUM DEGREE `≤ d ≥ 2`.**

Each vertex of `S` spends two of its `≤ d` edges inside `S`, so it has at most `d - 2` neighbours
outside; the boundary is the union of those outer neighbourhoods.  For `d = 3` this is exactly
`JSP90.card_boundary_le_card_oddCycle` of `JSPProblem/Subcubic.lean`, but the statement is for
**every** degree and for **every** set `S` with that property. -/
theorem card_boundary_le_card_mul_sub_two {d : ℕ} (hdeg : MaxDegLe G d) (hd2 : 2 ≤ d) {S : Finset V}
    (htwo : ∀ v ∈ S, 2 ≤ ((Neigh G v) ∩ S).card) : (boundary G S).card ≤ S.card * (d - 2) := by
  have hcov : boundary G S ⊆ S.biUnion (fun v : V => OuterNeigh G S v) := by
    intro x hx
    obtain ⟨hxS, hx⟩ := (mem_boundary.mp hx)
    obtain ⟨w, hwS, hxw⟩ := hx
    exact Finset.mem_biUnion.mpr ⟨w, hwS, mem_outerNeigh.mpr ⟨G.adj_symm hxw, hxS⟩⟩
  have hle : (S.biUnion (fun v : V => OuterNeigh G S v)).card
      ≤ ∑ v ∈ S, (OuterNeigh G S v).card :=
    Finset.card_biUnion_le (s := S) (t := fun v : V => OuterNeigh G S v)
  have hsum : (∑ v ∈ S, (OuterNeigh G S v).card) ≤ S.sum (fun _ => (d - 2)) := by
    refine Finset.sum_le_sum fun v hv => ?_
    have hcard : (OuterNeigh G S v).card = (Neigh G v).card - (S ∩ Neigh G v).card := by
      have heq : OuterNeigh G S v = (Neigh G v) \ S := by
        ext x
        simp [OuterNeigh, mem_neigh]
      rw [heq, Finset.card_sdiff]
    have h1 : (Neigh G v).card ≤ d := hdeg v
    have h2 := htwo v hv
    have h3 : (Neigh G v ∩ S).card ≤ (S ∩ Neigh G v).card := by
      refine Finset.card_le_card fun x hx => ?_
      rw [Finset.mem_inter] at hx ⊢
      exact ⟨hx.2, hx.1⟩
    omega
  have hsum1 : S.sum (fun _ => (d - 2)) ≤ S.card * (d - 2) := sum_const_le_card_mul S (d - 2)
  exact (Finset.card_le_card hcov).trans (hle.trans (hsum.trans hsum1))

/-- **THE COUNTING BOUND AT AN ODD CYCLE, IN AN ARBITRARY DEGREE RANGE.** -/
theorem card_boundary_oddCycle_le_card_mul_sub_two {d : ℕ} (hdeg : MaxDegLe G d) (hd2 : 2 ≤ d)
    {C : Finset V} (hC : IsOddCycle G C) : (boundary G C).card ≤ C.card * (d - 2) := by
  refine card_boundary_le_card_mul_sub_two hdeg hd2 ?_
  intro v hv
  exact two_le_card_inter_neigh_of_mem_oddCycle hC hv

/-- **THE CARDINALITY OF A CLOSED NEIGHBOURHOOD IS THE SUM OF ITS TWO PARTS.** -/
theorem card_neighClosed_eq_add {C : Finset V} :
    (NeighClosed G C).card = C.card + (boundary G C).card := by
  show (C ∪ boundary G C).card = C.card + (boundary G C).card
  rw [Finset.card_union_of_disjoint (disjoint_boundary (G := G) (C := C)).symm]

/-- **FROM A BOUND ON THE BOUNDARY TO A BOUND ON THE CLOSED NEIGHBOURHOOD.** -/
theorem card_neighClosed_le_of_boundary_le {d : ℕ} (hd2 : 2 ≤ d) {S : Finset V}
    (h : (boundary G S).card ≤ S.card * (d - 2)) : (NeighClosed G S).card ≤ S.card * (d - 1) := by
  have h2 := card_neighClosed_eq_add (G := G) (C := S)
  have hd2' : d - 1 = (d - 2) + 1 := by omega
  have h3 : S.card * (d - 2) + S.card = S.card * (d - 1) := by
    rw [hd2', Nat.mul_add, Nat.mul_one]
  omega

/-- **THE CLOSED NEIGHBOURHOOD OF AN ODD CYCLE HAS AT MOST `|C| * (d - 1)` VERTICES.**

For `d = 3` this is `JSP90.card_neighClosed_le_two_mul_card_oddCycle` of
`JSPProblem/Subcubic.lean`; the statement here covers every `d ≥ 2`, and the counting
(`card_boundary_oddCycle_le_card_mul_sub_two`) is done for every degree and every set. -/
theorem card_neighClosed_le_card_mul_sub_one {d : ℕ} (hdeg : MaxDegLe G d) (hd2 : 2 ≤ d)
    {C : Finset V} (hC : IsOddCycle G C) : (NeighClosed G C).card ≤ C.card * (d - 1) :=
  card_neighClosed_le_of_boundary_le hd2 (card_boundary_oddCycle_le_card_mul_sub_two hdeg hd2 hC)

end Neighbourhood

/-! ### Part 2 — the distance-one neighbourhood of a maximum packing is a transversal -/

section MaxPacking

variable {G : SimpleGraph V}

/-- **THE LOCAL STRUCTURAL THEOREM: THE CLOSED NEIGHBOURHOOD OF THE UNION OF A MAXIMUM PACKING OF
ODD CYCLES IS AN ODD CYCLE TRANSVERSAL.**

Indeed, an odd cycle avoiding that neighbourhood is disjoint from every member of the packing, so it
could be added to the packing — contradicting maximality.  This is the step that makes the
neighbourhood, rather than the packing itself, the local object an Erdős–Pósa proof manipulates. -/
theorem hitsOddCycles_neighClosed_of_maxPacking {P : Finset (Finset V)}
    (hP : IsOddCycleFamily (G := G) P)
    (hmax : ∀ Q, IsOddCycleFamily (G := G) Q → Q.card ≤ P.card) :
    HitsOddCycles G (NeighClosed G (P.biUnion id)) := by
  classical
  intro D hD hdis
  have hDunion : Disjoint D (P.biUnion id) := by
    refine Finset.disjoint_left.mpr fun x hx1 hx2 => ?_
    have hxmem : x ∈ D ∩ NeighClosed G (P.biUnion id) := by
      refine Finset.mem_inter.mpr ⟨hx1, ?_⟩
      show x ∈ (P.biUnion id) ∪ boundary G (P.biUnion id)
      exact Finset.mem_union.mpr (Or.inl hx2)
    rw [hdis] at hxmem
    simp at hxmem
  -- the odd cycle `D` is not one of the packed cycles
  have hDmem : D ∉ P := by
    intro hDP
    have hsub : D ⊆ P.biUnion id := fun x hx => Finset.mem_biUnion.mpr ⟨D, hDP, hx⟩
    obtain ⟨a, ha⟩ := hD.nonempty
    exact (Finset.disjoint_left.mp hDunion ha) (hsub ha)
  -- `P` together with `D` is a packing
  have hdisj : ∀ X ∈ insert D P, ∀ Y ∈ insert D P, X ≠ Y → X ∩ Y = ∅ := by
    intro X hX Y hY hXY
    rw [Finset.mem_insert] at hX
    rw [Finset.mem_insert] at hY
    rcases hX with hXD | hXP
    · rcases hY with hYD | hYP
      · exact absurd (hXD.trans hYD.symm) hXY
      · refine (Finset.disjoint_iff_inter_eq_empty).mp
          (Finset.disjoint_left.mpr fun a haX haY => ?_)
        have hsub : Y ⊆ P.biUnion id := fun y hy => Finset.mem_biUnion.mpr ⟨Y, hYP, hy⟩
        exact (Finset.disjoint_left.mp hDunion (hXD ▸ haX)) (hsub haY)
    · rcases hY with hYD | hYP
      · refine (Finset.disjoint_iff_inter_eq_empty).mp
          (Finset.disjoint_left.mpr fun a haX haY => ?_)
        have hsub : X ⊆ P.biUnion id := fun x hx => Finset.mem_biUnion.mpr ⟨X, hXP, hx⟩
        exact (Finset.disjoint_left.mp hDunion (hYD ▸ haY)) (hsub haX)
      · exact hP.1 X hXP Y hYP hXY
  have hfam : IsOddCycleFamily (G := G) (insert D P) := by
    refine ⟨hdisj, fun X hX => ?_⟩
    rw [Finset.mem_insert] at hX
    rcases hX with hXD | hXP
    · exact hXD ▸ hD
    · exact hP.2 X hXP
  have hcard := hmax (insert D P) hfam
  rw [Finset.card_insert_of_notMem hDmem] at hcard
  omega

/-- **THE SIZE OF THE NEIGHBOURHOOD OF A MAXIMUM PACKING IS COUNTED BY THE PACKING.**

Each member of the packing has at most `ℓ` vertices (the members are disjoint, so the union is the
disjoint sum) and the boundary of the union costs at most `d - 2` per vertex. -/
theorem card_neighClosed_maxPacking_le {d ℓ : ℕ} (hdeg : MaxDegLe G d) (hd2 : 2 ≤ d)
    {P : Finset (Finset V)} (hP : IsOddCycleFamily (G := G) P)
    (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ)
    (hmax : ∀ Q, IsOddCycleFamily (G := G) Q → Q.card ≤ P.card) :
    (NeighClosed G (P.biUnion id)).card ≤ ℓ * P.card * (d - 1) := by
  have hcover : ∀ ⦃x : V⦄, x ∈ P.biUnion id → ∃ i ∈ P, x ∈ i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact ⟨i, hi, hxi⟩
  have hcardU : (P.biUnion id).card = ∑ i ∈ P, i.card := by
    refine card_eq_sum_card_inter_of_disjoint hP.1 hcover |>.trans ?_
    refine Finset.sum_congr rfl fun i hi => ?_
    have hsub : i ⊆ P.biUnion id := fun x hx => Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
    have heq : P.biUnion id ∩ i = i := by
      ext x
      constructor
      · intro hx
        obtain ⟨-, hx2⟩ := Finset.mem_inter.mp hx
        exact hx2
      · intro hx
        exact Finset.mem_inter.mpr ⟨hsub hx, hx⟩
    rw [heq]
  have hcardUle : (P.biUnion id).card ≤ ℓ * P.card := by
    calc (P.biUnion id).card = ∑ i ∈ P, i.card := hcardU
      _ ≤ ∑ _i ∈ P, (ℓ : ℕ) := Finset.sum_le_sum fun i hi => hlen i (hP.2 i hi)
      _ ≤ P.card * ℓ := sum_const_le_card_mul P ℓ
      _ = ℓ * P.card := Nat.mul_comm _ _
  have htwo : ∀ v ∈ P.biUnion id, 2 ≤ ((Neigh G v) ∩ (P.biUnion id)).card := by
    intro v hv
    obtain ⟨i, hi, hvi⟩ := hcover hv
    have hsub : ((Neigh G v) ∩ i).card ≤ ((Neigh G v) ∩ (P.biUnion id)).card := by
      refine Finset.card_le_card fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hx1, Finset.mem_biUnion.mpr ⟨i, hi, hx2⟩⟩
    have h2 := two_le_card_inter_neigh_of_mem_oddCycle (hP.2 i hi) hvi
    omega
  have h1 := card_boundary_le_card_mul_sub_two hdeg hd2 htwo
  have hb : (boundary G (P.biUnion id)).card ≤ (P.biUnion id).card * (d - 2) := h1
  have hne : (NeighClosed G (P.biUnion id)).card ≤ (P.biUnion id).card * (d - 1) :=
    card_neighClosed_le_of_boundary_le hd2 hb
  have hmul : (P.biUnion id).card * (d - 1) ≤ ℓ * P.card * (d - 1) := by
    have h := Nat.mul_le_mul_right (d - 1) hcardUle
    simpa [Nat.mul_comm] using h
  exact hne.trans hmul

end MaxPacking

/-! ### Part 3 — an instance of the headline theorem with the local certificate -/

section Instances

universe u

variable {G : SimpleGraph V}

/-- **AN INSTANCE OF THE HEADLINE THEOREM WHOSE TRANSVERSAL IS THE DISTANCE-ONE NEIGHBOURHOOD OF A
MAXIMUM PACKING.**

Erdős's local hypothesis bounds the packing number by `k`
(`locIndep_oddCyclePackingLe`); every odd cycle has at most `ℓ` vertices; the maximum degree is at
most `d ≥ 2`.  A maximum packing `P` exists (`exists_maxPacking`), its closed neighbourhood is a
transversal (`hitsOddCycles_neighClosed_of_maxPacking`) and has at most `ℓ * |P| * (d - 1)`
vertices (`card_neighClosed_maxPacking_le`).

**The honest comparison with `JSP90.erdos73On_of_bounded_odd_girth`:** that theorem gives
`CloseToBipartite (ℓ * k) G` under strictly weaker hypotheses — no degree bound at all — so the
constant here is *larger*.  What is new is (i) the certificate, which lies within distance one of a
maximum packing, and (ii) the statement in an arbitrary degree range rather than only at `3`. -/
theorem closeToBipartite_of_maxPacking_neighbourhood {d ℓ : ℕ} (hd2 : 2 ≤ d)
    (hdeg : MaxDegLe G d) (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ)
    (hp : OddCyclePackingLe k G) : CloseToBipartite (ℓ * k * (d - 1)) G := by
  obtain ⟨P, hP, hmax⟩ := exists_maxPacking (G := G)
  have hle : P.card ≤ k := hp P hP
  have hcard : (NeighClosed G (P.biUnion id)).card ≤ ℓ * P.card * (d - 1) :=
    card_neighClosed_maxPacking_le hdeg hd2 hP hlen hmax
  have hfinal : ℓ * P.card * (d - 1) ≤ ℓ * k * (d - 1) := by
    calc ℓ * P.card * (d - 1) = ℓ * (P.card * (d - 1)) := Nat.mul_assoc _ _ _
      _ ≤ ℓ * (k * (d - 1)) := by
        refine Nat.mul_le_mul_left ℓ ?_
        simpa [Nat.mul_comm] using (Nat.mul_le_mul_right (d - 1) hle)
      _ = ℓ * k * (d - 1) := (Nat.mul_assoc _ _ _).symm
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := ℓ * k * (d - 1))).mpr
    ⟨NeighClosed G (P.biUnion id), hcard.trans hfinal,
      hitsOddCycles_neighClosed_of_maxPacking hP hmax⟩

/-- The same, in the shape of an instance of Erdős Problem #73. -/
theorem erdos73On_of_neighClosedPacking (k ℓ d : ℕ) (hd2 : 2 ≤ d) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → MaxDegLe G d →
      (∀ D, IsOddCycle G D → D.card ≤ ℓ) → CloseToBipartite (ℓ * k * (d - 1)) G :=
  fun W instW G hG hdeg hlen =>
    closeToBipartite_of_maxPacking_neighbourhood hd2 hdeg hlen (locIndep_oddCyclePackingLe hG)

/-- **THE SUBCUBIC LEVEL OF THE SAME INSTANCE**, where the constant is `ℓ * k * 2` (= `2 * k * ℓ`);
the certificate is the distance-one neighbourhood of a maximum packing. -/
theorem erdos73On_of_neighClosedPacking_subcubic (k ℓ : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → MaxDegLe G 3 →
      (∀ D, IsOddCycle G D → D.card ≤ ℓ) → CloseToBipartite (ℓ * k * 2) G := by
  intro W instW G hG hdeg hlen
  exact closeToBipartite_of_maxPacking_neighbourhood (d := 3) (ℓ := ℓ) (hd2 := by omega)
    hdeg hlen (locIndep_oddCyclePackingLe hG)

end Instances

/-! ### Part 4 — exactness at maximum degree two: `τ_odd(G) = ν_odd(G)` -/

section Two

variable {G : SimpleGraph V}

/-- **A GRAPH OF MAXIMUM DEGREE `≤ 2` HAS NO BRANCH VERTEX.** -/
theorem no_branchVertex_of_maxDegLe_two (hdeg : MaxDegLe G 2) (v : V) : ¬ BranchVertex G v := by
  intro hv
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hv
  have hsub : {a, b, c} ⊆ Neigh G v := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with hxa | hx
    · rw [hxa]; exact mem_neigh.mpr ha
    · rw [Finset.mem_insert] at hx
      rcases hx with hxb | hxc
      · rw [hxb]; exact mem_neigh.mpr hb
      · rw [Finset.mem_singleton.mp hxc]; exact mem_neigh.mpr hc
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    simp [hab, hac, hbc]
  have hle := (Finset.card_le_card hsub).trans (hdeg v)
  omega

/-- **THE ODD CYCLES OF A GRAPH OF MAXIMUM DEGREE `≤ 2` ARE PAIRWISE VERTEX-DISJOINT.** -/
theorem disjointFamily_oddCycles_of_maxDegLe_two (hdeg : MaxDegLe G 2) :
    DisjointFamily (OddCycles G) :=
  disjointFamily_oddCycles_of_no_branch (no_branchVertex_of_maxDegLe_two hdeg)

/-- **THE PACKING NUMBER OF A GRAPH OF MAXIMUM DEGREE `≤ 2` IS THE NUMBER OF ITS ODD CYCLES.** -/
theorem oddCyclePackingLe_iff_card_oddCycles_of_maxDegLe_two (hdeg : MaxDegLe G 2) {m : ℕ} :
    OddCyclePackingLe m G ↔ (OddCycles G).card ≤ m := by
  constructor
  · intro h
    exact h (OddCycles G) ⟨disjointFamily_oddCycles_of_maxDegLe_two hdeg, oddCycles_all_odd⟩
  · intro h P hP
    have hsub : ∀ D ∈ P, D ∈ OddCycles G := fun D hD => mem_oddCycles_univ (hP.2 D hD)
    exact (Finset.card_le_card (fun D hD => hsub D hD)).trans h

/-- **THE EXACT VALUE OF THE CONCLUSION AT MAXIMUM DEGREE `≤ 2`: THE LEAST ODD CYCLE TRANSVERSAL OF
`G` EQUALS ITS PACKING NUMBER.** -/
theorem maxDegLe_two_iff_oddCyclePackingLe (hdeg : MaxDegLe G 2) {m : ℕ} :
    CloseToBipartite m G ↔ OddCyclePackingLe m G :=
  ⟨fun h => (oddCyclePackingLe_iff_card_oddCycles_of_maxDegLe_two hdeg).mpr
      ((closeToBipartite_iff_card_oddCycles_of_disjoint m
        (disjointFamily_oddCycles_of_maxDegLe_two hdeg)).mp h),
   fun h => (closeToBipartite_iff_card_oddCycles_of_disjoint m
      (disjointFamily_oddCycles_of_maxDegLe_two hdeg)).mpr
      ((oddCyclePackingLe_iff_card_oddCycles_of_maxDegLe_two hdeg).mp h)⟩

/-- **THE MAXIMUM DEGREE OF `kTriangles k` IS AT MOST TWO.** -/
theorem maxDegLe_kTriangles (k : ℕ) : MaxDegLe (kTriangles k) 2 := by
  have hne : ∀ v : Fin 3 × Fin k, Neigh (kTriangles k) v = (tri v.2).erase v := by
    intro v
    ext w
    constructor
    · intro h
      rw [mem_neigh, kTriangles_adj] at h
      refine Finset.mem_erase.mpr ⟨?_, mem_tri.mpr h.1.symm⟩
      intro hcon
      subst hcon
      exact h.2 rfl
    · intro h
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp h
      rw [mem_neigh]
      refine kTriangles_adj.mpr ⟨mem_tri.mp hmem |>.symm, ?_⟩
      intro hcon
      exact hne (Prod.ext hcon.symm (mem_tri.mp hmem))
  intro v
  show (Neigh (kTriangles k) v).card ≤ 2
  rw [hne v, Finset.card_erase_of_mem (mem_tri.mpr (rfl : v.2 = v.2)), card_tri v.2]

/-- **ERDŐS PROBLEM #73 FOR GRAPHS OF MAXIMUM DEGREE `≤ 2`, WITH THE OPTIMAL CONSTANT `k`** — for
**every** `k`, not only `k = 1` as in `JSP90.erdos73On_one_of_maxDegLe_two`. -/
theorem erdos73On_of_maxDegLe_two (k : ℕ) :
    ∀ (W : Type*) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → MaxDegLe G 2 →
      CloseToBipartite k G :=
  fun W instW G hG hdeg =>
    maxDegLe_two_iff_oddCyclePackingLe hdeg |>.mpr (locIndep_oddCyclePackingLe hG)

/-- **THE CONSTANT `k` IS OPTIMAL ON THAT CLASS**: `kTriangles k` has maximum degree `2` and needs
`k` vertices. -/
theorem erdos73On_of_maxDegLe_two_optimal (k : ℕ) (hk : 1 ≤ k) :
    ¬ CloseToBipartite (k - 1) (kTriangles k) :=
  not_closeToBipartite_kTriangles (by omega)

/-- **AND THE BOUND IS ATTAINED FOR EVERY `k`**, by the same witness. -/
theorem closeToBipartite_kTriangles_of_maxDegLe_two (k : ℕ) : CloseToBipartite k (kTriangles k) :=
  erdos73On_of_maxDegLe_two k (Fin 3 × Fin k) (inferInstance) (kTriangles k) (locIndep_kTriangles (k := k)) (maxDegLe_kTriangles k)

end Two

/-! ### Part 5 — two machine-checked refutations: what the odd girth cannot do -/

section Refutations

universe u

variable {G : SimpleGraph V}

/-- **THE NUMBER OF ODD CYCLES OF A GRAPH OF MAXIMUM DEGREE `≤ 2` IS UNBOUNDED, WHILE ITS ODD
GIRTH (FROM BELOW) AND ITS DEGREE ARE FIXED.**

This is why no function of the odd girth and the maximum degree can bound the conclusion: the
disjoint union of `M + 1` triangles has odd girth `3` and maximum degree `2` for every `M`. -/
theorem maxDegLe_two_unbounded_oddCycles : ∀ M : ℕ, ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W),
    MaxDegLe G 2 ∧ OddGirthGe 3 G ∧ ¬ CloseToBipartite M G :=
  fun M => ⟨Fin 3 × Fin (M + 1), inferInstance, kTriangles (M + 1), maxDegLe_kTriangles (M + 1),
    fun _ hC => three_le_card_of_isOddCycle hC, not_closeToBipartite_kTriangles (by omega)⟩

/-- **`JSP90.BoundedOddGirthEdgeCount` — ROUND 99'S RECORDED TARGET — IS FALSE.**

The statement, in `JSPProblem/Sparse.lean`, says that a graph of odd girth `ℓ` in which every
vertex has at most `d` neighbours is `f ℓ d`-close to bipartite, for a function `f` of the odd
girth and the degree **alone**.  With `ℓ = 3` and `d = 2` the hypothesis is satisfied by every graph
of maximum degree `≤ 2`, and the odd cycle transversal number of such graphs is unbounded
(`maxDegLe_two_unbounded_oddCycles`). -/
theorem not_boundedOddGirthEdgeCount : ¬ BoundedOddGirthEdgeCount := by
  intro h
  obtain ⟨f, hf⟩ := h 3 2
  exact (not_closeToBipartite_kTriangles (by omega))
    (hf (Fin 3 × Fin (f + 1)) inferInstance (kTriangles (f + 1))
      (fun _ hC => three_le_card_of_isOddCycle hC) (maxDegLe_kTriangles (f + 1)))

/-- **AN ODD GIRTH FROM *BELOW* BOUNDS NOTHING; THE HYPOTHESIS OF `JSPProblem/Transversal.lean` IS
AN UPPER BOUND ON THE LENGTH OF THE ODD CYCLES, AND THAT IS THE ONE THAT WORKS.**

`kTriangles 5` has odd girth `3`, so `OddGirthGe 3` holds, and its least odd cycle transversal has
`5` elements: no statement of the shape `OddGirthGe ℓ G → CloseToBipartite ℓ G` can hold. -/
theorem not_oddGirth_bound_without_packing :
    ¬ ∀ (ℓ : ℕ) (W : Type) (_ : Fintype W) (G : SimpleGraph W), OddGirthGe ℓ G →
      CloseToBipartite ℓ G := by
  intro h
  exact not_closeToBipartite_kTriangles (by omega)
    (h 3 (Fin 3 × Fin 5) inferInstance (kTriangles 5) (fun _ hC => three_le_card_of_isOddCycle hC))

end Refutations

/-! ### Part 6 — heredity, and the **two-level odd-girth ladder** -/

section Ladder

universe u

variable {G : SimpleGraph V}

/-- **THE MAXIMUM DEGREE OF A RESIDUE NEVER EXCEEDS THAT OF `G`.** -/
theorem maxDegLe_deleteFinset {d : ℕ} (hdeg : MaxDegLe G d) {X : Finset V} :
    MaxDegLe (deleteFinset G X) d := by
  intro v
  refine (Finset.card_le_card ?_).trans (hdeg v)
  intro w hw
  have hw' := hw
  rw [Neigh, Finset.mem_filter] at hw'
  rw [deleteFinset_adj] at hw'
  exact mem_neigh.mpr hw'.2.2.2

/-- **AN ODD CYCLE OF THE DELETION `deleteFinset G X` IS AN ODD CYCLE OF `G`**, as a finset.

`JSP90.oddCycle_of_isOddCycle_delete` (of `JSPProblem/Transversal.lean`) returns *some* odd cycle of
`G` in the deletion, not the given vertex set; this lemma is the version that keeps the vertex set,
which is what statements about `G` and its residues need. -/
theorem isOddCycle_of_isOddCycle_deleteFinset {X C : Finset V}
    (hC : IsOddCycle (deleteFinset G X) C) : IsOddCycle G C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  exact ⟨m, f, hm, hm3, hinj, fun j => (deleteFinset_adj.mp (hcyc j)).2.2, hmem⟩

/-- **THE ODD GIRTH FROM BELOW IS HEREDITARY.** -/
theorem OddGirthGe.deleteFinset {ℓ : ℕ} {X : Finset V} (h : OddGirthGe ℓ G) :
    OddGirthGe ℓ (deleteFinset G X) :=
  fun D hD => h D (isOddCycle_of_isOddCycle_deleteFinset hD)

/-- **THE PACKING NUMBER OF THE RESIDUE OF AN ODD CYCLE DROPS BY ONE.** -/
theorem OddCyclePackingLe.succ_of_residue {r : ℕ} (hp : OddCyclePackingLe r G)
    {C : Finset V} (hC : IsOddCycle G C) : OddCyclePackingLe (r - 1) (deleteFinset G C) := by
  intro P hP
  have hnot : C ∉ P := fun hCP => not_mem_of_isOddCycle_delete hP hC hCP rfl
  have hle := hp (insert C P) (insert_oddCycle_of_delete hP hC)
  rw [Finset.card_insert_of_notMem hnot] at hle
  omega

/-- **THE TWO-LEVEL ODD-GIRTH LADDER.**

Let `C` be an odd cycle of at most `ℓ₁` vertices, let every odd cycle of the residue `G - C` have at
most `ℓ₂` vertices, let the packing number be at most `k` and the maximum degree at most `d ≥ 2`.
Then

> `CloseToBipartite (ℓ₁ + ℓ₂ * (k - 1) * (d - 1)) G`.

The classical induction pays, at each level, the length of the *shortest* odd cycle of the level;
recording two levels separately is strictly stronger than the uniform statement of Part 3, which
recovers it by putting `ℓ₁ = ℓ₂ = ℓ`.  For `d = 2` it reads `ℓ₁ + ℓ₂ * (k - 1)`, the sum of the two
girths rather than twice the largest one. -/
theorem closeToBipartite_of_twoLevelGirth {d k ℓ₁ ℓ₂ : ℕ} (hd2 : 2 ≤ d) (hdeg : MaxDegLe G d)
    {C : Finset V} (hC : IsOddCycle G C) (hC1 : C.card ≤ ℓ₁)
    (hlen2 : ∀ D, IsOddCycle (deleteFinset G C) D → D.card ≤ ℓ₂)
    (hp : OddCyclePackingLe k G) : CloseToBipartite (ℓ₁ + ℓ₂ * (k - 1) * (d - 1)) G := by
  have hpres : OddCyclePackingLe (k - 1) (deleteFinset G C) :=
    hp.succ_of_residue hC
  have hdeg' : MaxDegLe (deleteFinset G C) d := maxDegLe_deleteFinset hdeg
  obtain ⟨X, hXcard, hXhits⟩ :=
    (closeToBipartite_iff_hitsOddCycles (G := deleteFinset G C)
      (m := ℓ₂ * (k - 1) * (d - 1))).mp
      (closeToBipartite_of_maxPacking_neighbourhood (d := d) (ℓ := ℓ₂) hd2 hdeg' hlen2 hpres)
  refine (closeToBipartite_iff_hitsOddCycles (G := G)
    (m := ℓ₁ + ℓ₂ * (k - 1) * (d - 1))).mpr
    ⟨X ∪ C, ?_, hitsOddCycles_union_cycle hXhits⟩
  have hstep : X.card + C.card ≤ ℓ₁ + ℓ₂ * (k - 1) * (d - 1) := by omega
  exact (Finset.card_union_le X C).trans hstep

/-- **THE UNIFORM LEVEL OF THE LADDER**: every odd cycle has at most `ℓ` vertices and the maximum
degree is at most `d ≥ 2` give `CloseToBipartite (ℓ + ℓ * (k - 1) * (d - 1)) G`, i.e.
`ℓ * ((k - 1) * (d - 1) + 1)`.  For `d = 3` this is `ℓ * (2 k - 1)`, better than the uniform `2 * k *
ℓ` of Part 3. -/
theorem closeToBipartite_of_ladder_uniform {d k ℓ : ℕ} (hd2 : 2 ≤ d) (hdeg : MaxDegLe G d)
    (hlen : ∀ D, IsOddCycle G D → D.card ≤ ℓ) (hp : OddCyclePackingLe k G) :
    CloseToBipartite (ℓ + ℓ * (k - 1) * (d - 1)) G := by
  by_cases hb : G.IsBipartite
  · exact closeToBipartite_of_isBipartite' hb
  · obtain ⟨C, hC⟩ : ∃ C : Finset V, IsOddCycle G C := by
      by_contra hn
      exact hb (isBipartite_of_no_oddCycle hn)
    exact closeToBipartite_of_twoLevelGirth hd2 hdeg hC (hlen C hC)
      (fun D hD => hlen D (isOddCycle_of_isOddCycle_deleteFinset hD)) hp

/-- **THE INSTANCE OF ERDŐS #73 GIVEN BY THE UNIFORM LADDER, IN AN ARBITRARY DEGREE RANGE.** -/
theorem erdos73On_of_ladder {k ℓ d : ℕ} (hd2 : 2 ≤ d) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → MaxDegLe G d →
      (∀ D, IsOddCycle G D → D.card ≤ ℓ) → CloseToBipartite (ℓ + ℓ * (k - 1) * (d - 1)) G :=
  fun W instW G hG hdeg hlen =>
    closeToBipartite_of_ladder_uniform hd2 hdeg hlen (locIndep_oddCyclePackingLe hG)

/-- **THE CONSTANT OF THE SUBCUBIC LADDER, IN ITS COMPACT FORM**: `ℓ + ℓ * (k - 1) * 2 = ℓ *
(2 * k - 1)` for `k ≥ 1` (at `k = 0` the compact form is `0`, while the ladder pays `ℓ`). -/
theorem subcubic_ladder_const {ℓ k : ℕ} (hk : 1 ≤ k) :
    ℓ + ℓ * (k - 1) * 2 = ℓ * (2 * k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  have h1 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have h4 : ℓ * j * 2 = ℓ * (2 * j) := by
    calc ℓ * j * 2 = ℓ * (j * 2) := Nat.mul_assoc ℓ j 2
      _ = ℓ * (2 * j) := by rw [Nat.mul_comm j 2]
  rw [show (j + 1 - 1) = j by omega, h1, Nat.mul_add, Nat.mul_one, h4]
  exact Nat.add_comm _ _

/-- **THE SUBCUBIC LADDER INSTANCE**, with the constant `ℓ * (2 * k - 1)`. -/
theorem erdos73On_of_ladder_subcubic (k ℓ : ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → MaxDegLe G 3 →
      (∀ D, IsOddCycle G D → D.card ≤ ℓ) → CloseToBipartite (ℓ * (2 * k - 1)) G := by
  intro W instW G hG hdeg hlen
  by_cases hk : 1 ≤ k
  · have h := erdos73On_of_ladder (k := k) (ℓ := ℓ) (d := 3) (by omega) W instW G hG hdeg hlen
    rw [show (3 - 1) = 2 by omega, subcubic_ladder_const hk] at h
    exact h
  · -- `LocIndep 0` is bipartiteness, so nothing is paid at all
    have hb : G.IsBipartite := by
      by_contra hnb
      obtain ⟨C, hC⟩ : ∃ C : Finset W, IsOddCycle G C := by
        by_contra hn
        exact hnb (isBipartite_of_no_oddCycle hn)
      have hle := (locIndep_oddCyclePackingLe hG) ({C} : Finset (Finset W))
        ⟨by
            intro X hX Y hY hXY
            have hXC : X = C := Finset.mem_singleton.mp hX
            have hYC : Y = C := Finset.mem_singleton.mp hY
            exact (hXY (hXC.trans hYC.symm)).elim,
          fun D hD => by
            rw [Finset.mem_singleton.mp hD]
            exact hC⟩
      exact (hk hle).elim
    exact closeToBipartite_of_isBipartite' hb

/-- **AT MAXIMUM DEGREE `≤ 2` THE LADDER COLLAPSES TO THE SUM OF THE TWO GIRTHS**, `ℓ₁ + ℓ₂ *
(k - 1)` — the classical "pay the shortest odd cycle of each level" bound, with no degree factor. -/
theorem closeToBipartite_of_twoLevelGirth_degreeTwo {k ℓ₁ ℓ₂ : ℕ} (hdeg : MaxDegLe G 2)
    {C : Finset V} (hC : IsOddCycle G C) (hC1 : C.card ≤ ℓ₁)
    (hlen2 : ∀ D, IsOddCycle (deleteFinset G C) D → D.card ≤ ℓ₂)
    (hp : OddCyclePackingLe k G) : CloseToBipartite (ℓ₁ + ℓ₂ * (k - 1)) G := by
  have h := closeToBipartite_of_twoLevelGirth (d := 2) (by omega) hdeg hC hC1 hlen2 hp
  rw [show (2 - 1) = 1 by omega, Nat.mul_one] at h
  exact h

end Ladder

/-! ### Part 7 — the certificate is attained: `K_3` -/

section Attained

variable {G : SimpleGraph V}

/-- **THE BOUNDARY OF THE WHOLE VERTEX SET IS EMPTY.** -/
theorem boundary_univ (G : SimpleGraph V) : boundary G (Finset.univ : Finset V) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
  exact (mem_boundary.mp hx).1 (Finset.mem_univ x)

/-- **ON `K_3` THE CERTIFICATE IS THE WHOLE GRAPH: ITS CLOSED NEIGHBOURHOOD HAS `3 = 3 * (2 - 1)`
VERTICES**, so the counting bound `|N[V(P)]| ≤ ℓ * |P| * (d - 1)` of Part 2 is attained exactly at
`d = 2`, `ℓ = 3`. -/
theorem card_neighClosed_completeGraph_three :
    (NeighClosed (SimpleGraph.completeGraph (Fin 3))
      ((Finset.univ : Finset (Fin 3)))).card = 3 := by
  have h1 := card_neighClosed_eq_add (G := SimpleGraph.completeGraph (Fin 3))
    (C := (Finset.univ : Finset (Fin 3)))
  rw [h1, boundary_univ, Finset.card_empty, Finset.card_univ]
  simp

/-- **The counting bound of Part 2 is tight on `K_3`.** -/
theorem card_neighClosed_completeGraph_three_tight :
    (NeighClosed (SimpleGraph.completeGraph (Fin 3))
      ((Finset.univ : Finset (Fin 3)))).card = 3 * 1 * (2 - 1) := by
  rw [card_neighClosed_completeGraph_three]

end Attained

end

end JSP90