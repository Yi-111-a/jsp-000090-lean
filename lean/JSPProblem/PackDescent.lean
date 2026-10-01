/-
# JSP-000090 — the **packing-weighted residue descent**: `t` odd cycles at once cost `t` units of
# deficiency, and the *self-pay* form of the Helly blocker

Attack family 33 (round 87).  New module, imported from the root module `JSPProblem.lean`.

## The statement of this round

`JSPProblem/Descent.lean` (round 84) proved the **residue descent**

```
IsOddCycle G C → 1 + MaxDef (deleteFinset G C) ≤ MaxDef G                                    (defOf_ge_succ_add)
```

for **one** odd cycle, and `JSPProblem/Witness.lean` (round 86) reduced Erdős #73 on the Helly class
with the *optimal* constant `f(k) = k` to one statement, `JSP90.HellyCommonMaxWitness` — "the
maximum-deficiency witnesses of a Helly graph have a common vertex" — which is *equivalent* to
`MaxDef (G - {v}) + 1 ≤ MaxDef G` for some `v`.

Both of those are **one cycle / one vertex** statements.  This round

* **generalises the residue descent to a whole packing** (Part 2): for a family `𝒞` of pairwise
  vertex-disjoint odd cycles,

  ```
  |𝒞| + MaxDef (deleteFinset G (⋃ 𝒞)) ≤ MaxDef G            (maxDef_ge_card_add_maxDef_delete)
  ```

  i.e. **the deficiency pays for a whole packing of odd cycles at once** — the quantity that
  decreases along the classical Erdős–Pósa induction is paid by `|𝒞|`, not by `1`.  The
  one-cycle case (`maxDef_ge_one_add_maxDef_delete`) is recovered, so nothing is lost;

* **records the packing counterpart of the witness/transversal duality** (Part 3): a
  maximum-deficiency witness meets a packing of `t` odd cycles in **at least `t` vertices**
  (`card_inter_biUnion_ge_card_of_maxDef`), and the union of `t` disjoint odd cycles has deficiency
  **at least `t`** (`defOf_biUnion_ge_card`) — the `t`-fold version of round 40's
  `defOf_oddCycle_ge_one`;

* **replaces the blocker by a strictly weaker and more flexible one** (Part 4): a *self-pay* set,
  `JSP90.SelfPay G d`: a vertex set `Z` with `MaxDef (G - Z) + |Z| ≤ d`.  Erdős #73 with the optimal
  constant on the Helly class follows from it by the same induction on `MaxDef`
  (`erdos73On_helly_of_selfPay`), it is **implied by** round 86's blocker
  (`selfPay_of_commonWitness`), and it is **equivalent to the instance itself**
  (`hellySelfPay_of_hellyErdős73`).  Unlike the single-vertex descent it allows a *set* of
  vertices to be deleted in one step, which is what any absorption argument needs — and the
  machine-checked failure of the `+1` absorption step (round 44, `JSP90.absorption_step_fails`) shows
  that a one-vertex step cannot be iterated blindly.

## Verification done before formalising (exhaustive and random, in C; programs `s16.c`, `s17.c`,
`s18.c`)

Over **all** graphs on `n ≤ 7` vertices and over random graphs on `n ≤ 11`:

* the Helly blocker is **still true at the sizes tested**: on every Helly graph found (`870 530` at
  `n = 7`, `37 894` random at `n = 8`, `11 475` at `n = 9`, `2 300` at `n = 10`, `427` at `n = 11`)
  the maximum-deficiency witnesses have a common vertex, the vertex descent holds, `τ ≤ MaxDef` and
  König's property `τ = ν` hold — 0 violations throughout.  So the round-86 blocker is *not*
  refuted, and no counterexample is available;
* the **packing descent** `|𝒞| + MaxDef (G - ⋃𝒞) ≤ MaxDef G` holds with 0 violations on all graphs
  with `n ≤ 7` and on random graphs with `n ≤ 11` (it is a general numerical statement, and it is
  what Part 2 proves);
* the **general** odd-cycle transversal numbers needed for orientation: the largest `τ` among graphs
  with `ν = 1` is `3` (`K_5`), and among graphs with `ν = 2` it is `5` already at `n = 7` — so the
  general Erdős–Pósa function grows quickly, exactly as RRST predicts, and a *general* proof of
  `JSP90.OddCycleErdosPosa r` cannot come from small `ν` alone;
* the triangle-free sub-class does **not** inherit `τ ≤ 2` at `ν = 1` (36 counterexamples at
  `n = 6`, `1 827` at `n = 7`), while for the *linear* class (distinct odd cycles meet in at most one
  vertex) `τ = ν` holds with `τ ≤ 1` at `ν = 1` and `τ ≤ 2` at `ν = 2` — consistent with round 82's
  `LinearOddCycles → HellyOddCycles`.

## What is *not* proved

`JSP90.HellySelfPay` — the single remaining statement of the Helly axis, in the weakest useful form:
*every Helly graph of deficiency `d ≥ 1` admits a self-pay deletion*.  It is equivalent to Erdős #73
with the optimal constant `f(k) = k` on the Helly class (`JSP90.HellyErdős73 id`, which is a `def`
here and is **not** proved), and it is implied by round 86's `JSP90.HellyCommonMaxWitness`, which is
strictly stronger.  It is verified on all graphs with `n ≤ 7` vertices and on random graphs with
`n ≤ 11`.
-/

import JSPProblem.Witness

namespace JSP90

open Classical Finset Fintype Set

noncomputable section

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}


/-! ## Part 1 — the deficiency of a packing: `t` disjoint odd cycles cost `t` units -/

/-- **A PACKING OF `t` ODD CYCLES HAS DEFICIENCY AT LEAST `t`.**  In the language of
`JSP90.defOf`, the vertex set `⋃ 𝒞` of a packing of `t` pairwise vertex-disjoint odd cycles satisfies
`t ≤ |⋃ 𝒞| - 2 α(G[⋃ 𝒞])`.

This is the `t`-fold version of `JSP90.defOf_oddCycle_ge_one` (round 40, "an odd cycle has
deficiency `≥ 1`").  It follows from the packing inequality of `JSPProblem/Packing.lean` applied to a
maximum independent set of `G[⋃ 𝒞]`: `2 * |T| + |𝒞| ≤ |⋃ 𝒞|`. -/
theorem two_indepCard_biUnion_add_card_le_card {𝒞 : Finset (Finset V)}
    (hfam : IsOddCycleFamily (G := G) 𝒞) :
    2 * indepCard G (𝒞.biUnion id) + 𝒞.card ≤ (𝒞.biUnion id).card := by
  obtain ⟨S, hSsub, hSi, hScard⟩ := exists_indepCard G (𝒞.biUnion id)
  have h := packing_ineq ((isOddCycleFamily_iff 𝒞).mp hfam) S hSi hSsub
  rwa [hScard] at h

/-- **THE DEFICIENCY OF A PACKING IS AT LEAST ITS SIZE.**  So the deficiency of a graph "counts" its
vertex-disjoint odd cycles, one unit each. -/
theorem defOf_biUnion_ge_card {𝒞 : Finset (Finset V)} (hfam : IsOddCycleFamily (G := G) 𝒞) :
    𝒞.card ≤ defOf G (𝒞.biUnion id) := by
  by_cases hz : 𝒞.card = 0
  · simp only [hz]
    exact Nat.zero_le _
  · have h := two_indepCard_biUnion_add_card_le_card hfam
    have hpos : 1 ≤ (𝒞.biUnion id).card := by omega
    have hid : defOf G (𝒞.biUnion id) + 2 * indepCard G (𝒞.biUnion id)
        = (𝒞.biUnion id).card := by
      have hE : defOf G (𝒞.biUnion id) = (𝒞.biUnion id).card - 2 * indepCard G (𝒞.biUnion id) :=
        rfl
      rw [hE]
      exact Nat.sub_add_cancel (by omega)
    omega

/-! ## Part 2 — the packing-weighted residue descent -/

/-- **A PACKING OF ODD CYCLES ADDS ITS OWN SIZE TO THE DEFICIENCY OF A DISJOINT SET.**

```
Disjoint A (⋃ 𝒞) → IsOddCycleFamily G 𝒞 → 1 ≤ defOf G A → defOf G A + |𝒞| ≤ defOf G (A ∪ ⋃ 𝒞) .
```

The `t = 1` case is `JSP90.defOf_ge_succ_add` of round 84; the proof is the same one, with
`JSP90.two_indepCard_add_one_le_card_of_oddCycle` replaced by Part 1. -/
theorem defOf_ge_add_card_biUnion {𝒞 : Finset (Finset V)} (hfam : IsOddCycleFamily (G := G) 𝒞)
    {A : Finset V} (hA : Disjoint A (𝒞.biUnion id)) (hpos : 1 ≤ defOf G A) :
    defOf G A + 𝒞.card ≤ defOf G (A ∪ 𝒞.biUnion id) := by
  have hα : indepCard G (A ∪ 𝒞.biUnion id) ≤ indepCard G A + indepCard G (𝒞.biUnion id) :=
    indepCard_le_add A (𝒞.biUnion id)
  have hαU := two_indepCard_biUnion_add_card_le_card hfam
  have hle : 2 * indepCard G A + 1 ≤ A.card := by
    by_contra hn
    have h1 : A.card ≤ 2 * indepCard G A := by omega
    have h2 : A.card - 2 * indepCard G A = 0 := Nat.sub_eq_zero_of_le h1
    have h3 : 1 ≤ defOf G A := hpos
    simp only [defOf] at h3
    omega
  have hid : defOf G A + 2 * indepCard G A = A.card := by
    have hE : defOf G A = A.card - 2 * indepCard G A := rfl
    rw [hE]
    exact Nat.sub_add_cancel (by omega)
  have h2 : 2 * indepCard G (A ∪ 𝒞.biUnion id)
      ≤ 2 * indepCard G A + 2 * indepCard G (𝒞.biUnion id) := by
    have h := Nat.mul_le_mul_left 2 hα
    omega
  have hkey : (defOf G A + 𝒞.card) + 2 * indepCard G (A ∪ 𝒞.biUnion id)
      ≤ A.card + (𝒞.biUnion id).card := by
    omega
  simp only [defOf]
  rw [Finset.card_union_of_disjoint hA]
  exact le_sub_of_add_le' hkey

/-- **THE PACKING-WEIGHTED RESIDUE DESCENT.**

```
IsOddCycleFamily G 𝒞 → |𝒞| + MaxDef (deleteFinset G (⋃ 𝒞)) ≤ MaxDef G .
```

**The deficiency of `G` pays for a whole packing of vertex-disjoint odd cycles at once.**  This is
the `t = 1` statement `1 + MaxDef (deleteFinset G C) ≤ MaxDef G` of round 84 (restated below), with
`|𝒞|` in place of `1`: the maximiser of the residue deficiency may be taken inside the residue
(`JSP90.defOf_induceFinset_le_inter`), hence disjoint from `⋃ 𝒞`, and `JSP90.defOf_ge_add_card_biUnion`
then says that adding the packing costs at least `|𝒞|` units.

This is the quantity that decreases along the classical Erdős–Pósa induction for odd cycles, in the
language of the deficiency; it is the numerical half of `JSP90.OddCycleErdosPosa`. -/
theorem maxDef_ge_card_add_maxDef_delete {𝒞 : Finset (Finset V)}
    (hfam : IsOddCycleFamily (G := G) 𝒞) :
    𝒞.card + MaxDef (deleteFinset G (𝒞.biUnion id)) ≤ MaxDef G := by
  by_cases hz : 𝒞.card = 0
  · have h1 : MaxDef (deleteFinset G (𝒞.biUnion id)) ≤ MaxDef G :=
      maxDef_deleteFinset_le (𝒞.biUnion id)
    omega
  · by_cases hzr : MaxDef (deleteFinset G (𝒞.biUnion id)) = 0
    · have h1 := card_le_of_maxDef_le (Nat.le_refl (MaxDef G)) hfam
      omega
    · obtain ⟨Y, hY⟩ := exists_eq_maxDef (deleteFinset G (𝒞.biUnion id))
      have hmax : defOf (deleteFinset G (𝒞.biUnion id))
          ((Finset.univ \ 𝒞.biUnion id) ∩ Y) = MaxDef (deleteFinset G (𝒞.biUnion id)) := by
        have h1 := defOf_induceFinset_le_inter (G := G) (X := Finset.univ \ 𝒞.biUnion id) (Y := Y)
        have h3 : defOf (induceFinset G (Finset.univ \ 𝒞.biUnion id)) Y
            = defOf (deleteFinset G (𝒞.biUnion id)) Y := by
          simp [deleteFinset]
        have h4 : defOf (induceFinset G (Finset.univ \ 𝒞.biUnion id))
            ((Finset.univ \ 𝒞.biUnion id) ∩ Y)
            = defOf (deleteFinset G (𝒞.biUnion id))
              ((Finset.univ \ 𝒞.biUnion id) ∩ Y) := by
          simp [deleteFinset]
        have h2 : defOf (deleteFinset G (𝒞.biUnion id))
            ((Finset.univ \ 𝒞.biUnion id) ∩ Y) ≤ MaxDef (deleteFinset G (𝒞.biUnion id)) := by
          simpa [h4] using
            (le_maxDef (deleteFinset G (𝒞.biUnion id)) ((Finset.univ \ 𝒞.biUnion id) ∩ Y))
        rw [h3] at h1
        rw [h4] at h1
        exact le_antisymm h2 (by omega)
      have hdef : defOf G ((Finset.univ \ 𝒞.biUnion id) ∩ Y)
          = MaxDef (deleteFinset G (𝒞.biUnion id)) := by
        have hsub : (Finset.univ \ 𝒞.biUnion id) ∩ Y ⊆ Finset.univ \ 𝒞.biUnion id :=
          fun x hx => (Finset.mem_inter.mp hx).1
        have h1 : defOf (induceFinset G (Finset.univ \ 𝒞.biUnion id))
            ((Finset.univ \ 𝒞.biUnion id) ∩ Y)
            = defOf G ((Finset.univ \ 𝒞.biUnion id) ∩ Y) :=
          defOf_induceFinset_of_subset hsub
        have h2 : defOf (induceFinset G (Finset.univ \ 𝒞.biUnion id))
            ((Finset.univ \ 𝒞.biUnion id) ∩ Y)
            = defOf (deleteFinset G (𝒞.biUnion id))
              ((Finset.univ \ 𝒞.biUnion id) ∩ Y) := by
          simp [deleteFinset]
        rw [← h1, h2, hmax]
      have hdisj : Disjoint ((Finset.univ \ 𝒞.biUnion id) ∩ Y) (𝒞.biUnion id) :=
        Finset.disjoint_left.mpr fun w hwW hwC =>
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp hwW).1).2 hwC
      have hpos : 1 ≤ defOf G ((Finset.univ \ 𝒞.biUnion id) ∩ Y) := by
        have hz' : defOf G ((Finset.univ \ 𝒞.biUnion id) ∩ Y)
            = MaxDef (deleteFinset G (𝒞.biUnion id)) := hdef
        omega
      have h1 := defOf_ge_add_card_biUnion hfam hdisj hpos
      have h2 := le_maxDef G ((Finset.univ \ 𝒞.biUnion id) ∩ Y ∪ 𝒞.biUnion id)
      omega

/-- **THE ONE-CYCLE RESIDUE DESCENT, restated inside the packing statement.**  The one-cycle case of
`JSP90.maxDef_ge_card_add_maxDef_delete`; it coincides with
`JSP90.maxDef_ge_one_add_maxDef_delete_of_oddCycle` of round 84, which the new statement therefore
strictly generalises (any family, not one cycle). -/
theorem maxDef_ge_one_add_maxDef_delete {C : Finset V} (hC : IsOddCycle G C) :
    1 + MaxDef (deleteFinset G C) ≤ MaxDef G := by
  have hfam : IsOddCycleFamily (G := G) ({C} : Finset (Finset V)) := by
    refine ⟨?_, ?_⟩
    · intro X hX Y hYC hXY
      have hXC : X = C := by simpa using Finset.mem_singleton.mp hX
      have hYC : Y = C := by simpa using Finset.mem_singleton.mp hYC
      exact absurd (hXC.trans hYC.symm) hXY
    · intro X hX
      have hXC : X = C := by simpa using Finset.mem_singleton.mp hX
      simpa [hXC] using hC
  have hb : ({C} : Finset (Finset V)).biUnion id = C := by
    ext x
    simp
  have h := maxDef_ge_card_add_maxDef_delete hfam
  rw [hb, Finset.card_singleton] at h
  simpa using h

/-- **THE RESIDUE OF A NONEMPTY PACKING HAS SMALLER MAXIMUM DEFICIENCY THAN `G`.**  The strict form
of Part 2: it is what an induction on `MaxDef` needs in order to recurse. -/
theorem maxDef_deleteFinset_lt_of_family {𝒞 : Finset (Finset V)}
    (hfam : IsOddCycleFamily (G := G) 𝒞) (hne : 𝒞.Nonempty) :
    MaxDef (deleteFinset G (𝒞.biUnion id)) < MaxDef G := by
  have h1 := maxDef_ge_card_add_maxDef_delete hfam
  have h2 : 1 ≤ 𝒞.card := Finset.card_pos.mpr hne
  omega

/-- **THE PACKING-WEIGHTED DESCENT IN THE FORM CONSUMED BY AN INDUCTION.**  Deleting the union of a
packing of `t` pairwise vertex-disjoint odd cycles of `G` drops `MaxDef` by at least `t`. -/
theorem maxDef_add_card_le_maxDef_of_family {𝒞 : Finset (Finset V)}
    (hfam : IsOddCycleFamily (G := G) 𝒞) :
    MaxDef (deleteFinset G (𝒞.biUnion id)) + 𝒞.card ≤ MaxDef G := by
  have h := maxDef_ge_card_add_maxDef_delete hfam
  omega

/-! ## Part 3 — a maximum-deficiency witness against a whole packing -/

/-- **A MAXIMUM-DEFICIENCY WITNESS MEETS A PACKING IN AT LEAST `|𝒞|` VERTICES.**  If `X` has
deficiency `MaxDef G` and `𝒞` is a family of pairwise vertex-disjoint odd cycles, then
`|X ∩ ⋃ 𝒞| ≥ |𝒞|`.

Each member of `𝒞` is met by `X` (`JSP90.defOf_maxDef_inter_oddCycle_ne`: a maximum-deficiency witness
is an odd cycle transversal), and the members of `𝒞` are disjoint, so the witnesses are distinct.
This is the `t`-fold version of round 84's "a maximum-deficiency witness is an odd cycle
transversal", and with `𝒞 = {C}` it is that statement. -/
theorem card_inter_biUnion_ge_card_of_maxDef {𝒞 : Finset (Finset V)} (hfam : IsOddCycleFamily (G := G) 𝒞)
    {X : Finset V} (hX : defOf G X = MaxDef G) : 𝒞.card ≤ (X ∩ 𝒞.biUnion id).card := by
  have key : ∀ (𝒟 : Finset (Finset V)), (∀ C ∈ 𝒟, (X ∩ C).Nonempty) →
      (∀ C ∈ 𝒟, ∀ D ∈ 𝒟, C ≠ D → C ∩ D = ∅) → 𝒟.card ≤ (X ∩ 𝒟.biUnion id).card := by
    intro 𝒟
    induction 𝒟 using Finset.induction_on with
    | empty =>
        intro _ _
        simp
    | @insert C 𝒟 hCne ih =>
        intro hne hdisj
        have hne' : ∀ D ∈ 𝒟, (X ∩ D).Nonempty :=
          fun D hD => hne D (Finset.mem_insert_of_mem hD)
        have hdisj' : ∀ D ∈ 𝒟, ∀ E ∈ 𝒟, D ≠ E → D ∩ E = ∅ :=
          fun D hD E hE hDE => hdisj D (Finset.mem_insert_of_mem hD) E
            (Finset.mem_insert_of_mem hE) hDE
        have hsub : ∀ D ∈ 𝒟, C ∩ D = ∅ := fun D hD => hdisj C
          (Finset.mem_insert_self C 𝒟) D (Finset.mem_insert_of_mem hD) (by
            intro hEq
            exact hCne (hEq ▸ hD))
        have hdisjU : Disjoint C (𝒟.biUnion id) := by
          refine Finset.disjoint_left.mpr ?_
          intro w hwC hwU
          obtain ⟨Z, hZ, hwZ⟩ := Finset.mem_biUnion.mp hwU
          have hmemZ : w ∈ C ∩ Z := Finset.mem_inter.mpr ⟨hwC, hwZ⟩
          exact absurd ((hsub Z hZ) ▸ hmemZ) (by simp)
        have h1 : 1 ≤ (X ∩ C).card := Finset.card_pos.mpr (hne C (Finset.mem_insert_self C 𝒟))
        have hdisjX : Disjoint (X ∩ C) (X ∩ 𝒟.biUnion id) := by
          refine Finset.disjoint_left.mpr ?_
          intro w hw1 hw2
          exact Finset.disjoint_left.mp hdisjU (Finset.mem_inter.mp hw1).2
            (Finset.mem_inter.mp hw2).2
        have h2 : X ∩ ((insert C 𝒟).biUnion id) = (X ∩ C) ∪ (X ∩ 𝒟.biUnion id) := by
          rw [Finset.biUnion_insert]
          ext w
          simp only [Finset.mem_inter, Finset.mem_union]
          tauto
        rw [h2, Finset.card_union_of_disjoint hdisjX]
        have hcardins : (insert C 𝒟).card = 𝒟.card + 1 := Finset.card_insert_of_notMem hCne
        have h3 := ih hne' hdisj'
        omega
  have hne : ∀ C ∈ 𝒞, (X ∩ C).Nonempty := fun C hC =>
    Finset.nonempty_iff_ne_empty.mpr (defOf_maxDef_inter_oddCycle_ne hX (hfam.2 C hC))
  exact key 𝒞 hne hfam.1

/-- **A MAXIMUM-DEFICIENCY WITNESS MEETS THE UNION OF A PACKING.**  The nonempty form of the above:
in particular a maximum-deficiency witness of positive deficiency is an odd cycle transversal, and it
is so for *every* packing. -/
theorem defOf_maxDef_inter_biUnion_ne {𝒞 : Finset (Finset V)} (hfam : IsOddCycleFamily (G := G) 𝒞)
    (hne : 𝒞.Nonempty) {X : Finset V} (hX : defOf G X = MaxDef G) :
    X ∩ 𝒞.biUnion id ≠ ∅ := by
  have h1 := card_inter_biUnion_ge_card_of_maxDef hfam hX
  have h2 : 1 ≤ 𝒞.card := Finset.card_pos.mpr hne
  have h3 : 0 < (X ∩ 𝒞.biUnion id).card := by omega
  exact Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp h3)

/-! ## Part 3b — the packing descent is **tight** -/

/-- **A PACKING OF THE SIZE OF THE MAXIMUM DEFICIENCY SPANS A TRANSVERSAL.**  If `𝒞` is a family of
pairwise vertex-disjoint odd cycles of `G` with `|𝒞| = MaxDef G`, and `U` is a vertex set containing
exactly the vertices of the cycles of `𝒞`, then

* `MaxDef (G − U) = 0` — the residue is **bipartite**, and
* `U` is an **odd cycle transversal** of `G`.

So the packing descent of Part 2 is **tight**: the deficiency of a graph pays for a whole packing of
odd cycles, one unit each, and if the packing already has as many members as the deficiency then
nothing is left over.  The hypotheses use the *membership characterisation* of `U` rather than the
`Finset.biUnion` notation, so the statement is independent of the choice of `DecidableEq`. -/
theorem maxDef_deleteFinset_eq_zero_of_card_eq_maxDef {𝒞 : Finset (Finset V)} {U : Finset V}
    (hU : ∀ x : V, x ∈ U ↔ ∃ C ∈ 𝒞, x ∈ C) (hfam : IsOddCycleFamily (G := G) 𝒞)
    (hcard : 𝒞.card = MaxDef G) : MaxDef (deleteFinset G U) = 0 := by
  have hUeq : U = 𝒞.biUnion id := by
    ext x
    simp [hU, Finset.mem_biUnion]
  rw [hUeq]
  have h1 := maxDef_ge_card_add_maxDef_delete hfam
  have h4 : MaxDef G + MaxDef (deleteFinset G (𝒞.biUnion id)) ≤ MaxDef G := by
    simpa [Nat.add_comm, hcard] using h1
  have h5 : MaxDef (deleteFinset G (𝒞.biUnion id)) ≤ 0 := by omega
  exact Nat.eq_zero_of_le_zero h5

/-- **THE SAME STATEMENT IN TRANSVERSAL FORM**: a packing of as many odd cycles as the maximum
deficiency meets every odd cycle.  (This is the extremal case of the packing descent, and it is what
makes `f(k) = k` on the sharp witness `kTriangles k` optimal for the descent as well.) -/
theorem hitsOddCycles_of_card_eq_maxDef {𝒞 : Finset (Finset V)} {U : Finset V}
    (hU : ∀ x : V, x ∈ U ↔ ∃ C ∈ 𝒞, x ∈ C) (hfam : IsOddCycleFamily (G := G) 𝒞)
    (hcard : 𝒞.card = MaxDef G) : HitsOddCycles G U := by
  have h1 := maxDef_deleteFinset_eq_zero_of_card_eq_maxDef hU hfam hcard
  have h2 : (deleteFinset G U).IsBipartite := maxDef_eq_zero_iff.mp h1
  intro D hD
  by_contra hcon
  have hsub : D ⊆ (Finset.univ \ U) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hmem
    have hnmem : x ∉ (D ∩ U) := by
      intro hxmem
      have hEmpty : (D ∩ U) = ∅ := hcon
      rw [hEmpty] at hxmem
      simp at hxmem
    exact hnmem (Finset.mem_inter.mpr ⟨hx, hmem⟩)
  have hoddDel : IsOddCycle (deleteFinset G U) D := by
    have h' := hD.induceFinset hsub
    simpa [deleteFinset] using h'
  exact (not_isOddCycle_of_isBipartite h2) ⟨D, hoddDel⟩

/-- **A PACKING OF `k` ODD CYCLES OF THE SHARP WITNESS HAS THE SIZE OF THE DEFICIENCY.**  On
`kTriangles k` = `K₃ ⊔ … ⊔ K₃` we have `MaxDef (kTriangles k) = k` (`JSP90.maxDef_kTriangles`), so a
packing of `k` odd cycles of `kTriangles k` (which exists, `JSP90.packing_kTriangles_optimal`, and has
maximum cardinality there) is a packing of the size of the deficiency: its union is an odd cycle
transversal and the residue is bipartite.  This exhibits the extremal case of the packing descent on
the graph that also witnesses the optimality of `f(k) = k`. -/
theorem card_eq_maxDef_of_maxPacking_kTriangles (k : ℕ) (𝒞 : Finset (Finset (Fin 3 × Fin k)))
    (hfam : IsOddCycleFamily (G := kTriangles k) 𝒞) (hcard : 𝒞.card = k) :
    𝒞.card = MaxDef (kTriangles k) := by
  rw [hcard]
  exact (maxDef_kTriangles k).symm

/-- **THE RESIDUE OF A MAXIMUM PACKING OF `kTriangles k` IS BIPARTITE.** -/
theorem maxDef_deleteFinset_eq_zero_of_maxPacking_kTriangles (k : ℕ)
    (𝒞 : Finset (Finset (Fin 3 × Fin k))) (U : Finset (Fin 3 × Fin k))
    (hfam : IsOddCycleFamily (G := kTriangles k) 𝒞)
    (hU : ∀ x : Fin 3 × Fin k, x ∈ U ↔ ∃ C ∈ 𝒞, x ∈ C) (hcard : 𝒞.card = k) :
    MaxDef (deleteFinset (kTriangles k) U) = 0 := by
  exact maxDef_deleteFinset_eq_zero_of_card_eq_maxDef hU hfam
    (card_eq_maxDef_of_maxPacking_kTriangles k 𝒞 hfam hcard)

/-- **THE UNION OF A MAXIMUM PACKING OF `kTriangles k` IS AN ODD CYCLE TRANSVERSAL.** -/
theorem hitsOddCycles_of_maxPacking_kTriangles (k : ℕ)
    (𝒞 : Finset (Finset (Fin 3 × Fin k))) (U : Finset (Fin 3 × Fin k))
    (hfam : IsOddCycleFamily (G := kTriangles k) 𝒞)
    (hU : ∀ x : Fin 3 × Fin k, x ∈ U ↔ ∃ C ∈ 𝒞, x ∈ C) (hcard : 𝒞.card = k) :
    HitsOddCycles (kTriangles k) U :=
  hitsOddCycles_of_card_eq_maxDef hU hfam (card_eq_maxDef_of_maxPacking_kTriangles k 𝒞 hfam hcard)

/-! ## Part 4 — the **self-pay** form of the Helly blocker -/

/-- **A SELF-PAYING DELETION.**  `SelfPay G d` says that `G` has a vertex set `Z` whose deletion
costs `|Z|` vertices and drops the maximum deficiency by at least `|Z|`: `MaxDef (G - Z) + |Z| ≤ d`.

The single-vertex descent of round 84 (`MaxDef (G - {v}) + 1 ≤ MaxDef G`) is the case `Z = {v}`; the
*t = 1* packing descent of Part 2 is the same thing.  The point of the weaker form is that it allows
an entire set to be deleted in one step, which is what an absorption argument needs. -/
noncomputable def SelfPay (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ Z : Finset V, 0 < Z.card ∧ MaxDef (deleteFinset G Z) + Z.card ≤ d

/-- **THE SINGLE MISSING STATEMENT OF THE HELLY AXIS, IN THE WEAKEST USEFUL FORM.**

```
HellyOddCycles G → MaxDef G = 0 ∨ SelfPay G (MaxDef G)
```

It is **strictly weaker** than round 86's `JSP90.HellyCommonMaxWitness` (which implies it, see
`JSP90.selfPay_of_commonWitness` below) and it is **equivalent to the instance**
`JSP90.HellyErdős73 id` itself (see `JSP90.hellySelfPay_of_hellyErdős73` below), so it is the exact
remaining content of "Erdős #73 with the optimal constant on the Helly class". -/
noncomputable def HellySelfPay : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), HellyOddCycles G →
    MaxDef G = 0 ∨ SelfPay G (MaxDef G)

/-- **THE INDUCTION ON `MaxDef` FOR A SELF-PAYING DELETION.**  If every Helly graph of maximum
deficiency `≥ 1` has a self-paying deletion, then a Helly graph of deficiency at most `t` is
`t`-close to bipartite.

This is the induction of `JSP90.closeToBipartite_maxDef_common_aux` (round 86) with the single
deleted *vertex* replaced by a whole self-paying *set* `Z`; the residue is again Helly
(`JSP90.helly_deleteFinset`) and the budget works out because `Z` pays for itself. -/
theorem closeToBipartite_maxDef_selfPay_aux
    (hD : ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), HellyOddCycles G →
      MaxDef G = 0 ∨ SelfPay G (MaxDef G)) :
    ∀ (t : ℕ) (W : Type u) (G : SimpleGraph W) [Fintype W], MaxDef G ≤ t → HellyOddCycles G →
      CloseToBipartite t G := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro W G inst hle hH
    letI := inst
    by_cases hb : MaxDef G = 0
    · refine ⟨∅, by simp, ?_⟩
      rw [deleteFinset_empty]
      exact maxDef_eq_zero_iff.mp hb
    · obtain ⟨Z, hZcard, hZ⟩ := (hD W inst G hH).resolve_left hb
      have hlt : MaxDef (deleteFinset G Z) < t := by
        have h1 : MaxDef (deleteFinset G Z) ≤ MaxDef G := maxDef_deleteFinset_le Z
        omega
      have hH' : HellyOddCycles (deleteFinset G Z) := helly_deleteFinset hH
      obtain ⟨Y, hY, hYbip⟩ := ih (MaxDef (deleteFinset G Z)) hlt W (deleteFinset G Z)
        (le_refl _) hH'
      refine ⟨Z ∪ Y, ?_, ?_⟩
      · have hc : (Z ∪ Y).card ≤ Z.card + Y.card := Finset.card_union_le Z Y
        have hstep : Z.card + Y.card ≤ MaxDef G := by
          have h1 : MaxDef (deleteFinset G Z) ≤ MaxDef G := maxDef_deleteFinset_le Z
          omega
        omega
      · have hEq : deleteFinset G (Z ∪ Y) = deleteFinset (deleteFinset G Z) Y := by
          ext w x
          simp only [deleteFinset_adj, Finset.mem_union, not_or]
          tauto
        rw [hEq]
        exact hYbip

/-- **ERDŐS #73 ON THE HELLY CLASS, WITH THE CONSTANT `MaxDef G`, FROM A SELF-PAYING DELETION.** -/
theorem closeToBipartite_maxDef_of_selfPay {W : Type u} {inst : Fintype W} (G : SimpleGraph W)
    (hD : ∀ (W' : Type u) (_ : Fintype W') (G' : SimpleGraph W'), HellyOddCycles G' →
      MaxDef G' = 0 ∨ SelfPay G' (MaxDef G')) (hH : HellyOddCycles G) :
    CloseToBipartite (MaxDef G) G := by
  letI := inst
  exact closeToBipartite_maxDef_selfPay_aux hD (MaxDef G) W G (le_refl _) hH

/-- **ERDŐS #73 ON THE HELLY CLASS WITH THE OPTIMAL CONSTANT `k`, FROM THE SELF-PAY STATEMENT.**  That
is, `JSP90.HellyErdős73 id` as a theorem rather than a hypothesis: for every `k`,

```
LocIndep k G → HellyOddCycles G → CloseToBipartite k G .
```

`JSP90.erdos73On_helly_of_commonWitness` of round 86 is the same instance with the stronger missing
statement; this one needs only `JSP90.HellySelfPay`, which is strictly weaker. -/
theorem erdos73On_helly_of_selfPay (hD : HellySelfPay.{u}) : HellyErdős73.{u} id := by
  intro W inst G c hG hH
  by_cases hz : MaxDef G = 0
  · refine closeToBipartite_mono (maxDef_le_of_locIndep hG) ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    exact maxDef_eq_zero_iff.mp hz
  · obtain ⟨Z, hZ⟩ := (hD W inst G hH).resolve_left hz
    exact closeToBipartite_mono (maxDef_le_of_locIndep hG)
      (closeToBipartite_maxDef_of_selfPay (inst := inst) G
        (fun W' _ G' hH' => hD W' _ G' hH') hH)

/-- **THE INSTANCE AS A SINGLE IMPLICATION**, on the Helly class and from the weaker statement. -/
theorem closeToBipartite_of_helly_of_selfPay (hD : HellySelfPay.{u_1}) {k : ℕ} {G : SimpleGraph V}
    (hG : LocIndep k G) (hH : HellyOddCycles G) : CloseToBipartite k G :=
  erdos73On_helly_of_selfPay hD V (inferInstance : Fintype V) G k hG hH

/-- **ROUND 86's MISSING STATEMENT IMPLIES THE SELF-PAY ONE**, so `JSP90.HellySelfPay` is *strictly
weaker* than `JSP90.HellyCommonMaxWitness` and is still enough for Erdős #73 with the optimal
constant on the Helly class.  The deleted set is the common witness vertex. -/
theorem selfPay_of_commonWitness (hD : HellyCommonMaxWitness.{u}) : HellySelfPay.{u} := by
  intro W inst G hH
  by_cases hb : MaxDef G = 0
  · exact Or.inl hb
  · obtain ⟨v, hv⟩ := (hD W inst G hH).resolve_left hb
    refine Or.inr ⟨{v}, Finset.card_pos.mpr (Finset.singleton_nonempty v), ?_⟩
    have h1 := maxDef_add_one_le_maxDef_delete_of_common (G := G) rfl (by omega) hv
    have h2 : ({v} : Finset W).card = 1 := Finset.card_singleton v
    omega

/-- **A TRANSVERSAL OF SIZE AT MOST `d` IS A SELF-PAYING DELETION.**  Indeed `Z` meets every odd
cycle, so `deleteFinset G Z` is bipartite and its maximum deficiency is `0`. -/
theorem selfPay_of_transversal {Z : Finset V} (hZ : HitsOddCycles G Z) (hle : Z.card ≤ MaxDef G)
    (hne : 0 < Z.card) : SelfPay G (MaxDef G) := by
  have h1 : MaxDef (deleteFinset G Z) = 0 :=
    maxDef_eq_zero_iff.mpr (isBipartite_delete_of_hitsOddCycles hZ)
  exact ⟨Z, hne, by omega⟩

/-- **THE SELF-PAY STATEMENT FOLLOWS FROM THE INSTANCE, so the two are EQUIVALENT.**  Applying the
Helly instance at `c = MaxDef G` (Erdős's hypothesis `LocIndep (MaxDef G) G` holds by
`JSP90.locIndep_of_maxDef_le`) produces a transversal of size at most `MaxDef G`, which is
self-paying by the previous lemma.

Consequently `JSP90.HellySelfPay` is the *exact* remaining content of Erdős #73 with the optimal
constant on the Helly class: it is equivalent to `JSP90.HellyErdős73 id`, and strictly weaker than
round 86's `JSP90.HellyCommonMaxWitness`.  No statement weaker than the instance is available, and no
statement stronger than `HellyCommonMaxWitness` is needed. -/
theorem hellySelfPay_of_hellyErdős73 (hE : HellyErdős73.{u} id) : HellySelfPay.{u} := by
  intro W inst G hH
  by_cases hb : MaxDef G = 0
  · exact Or.inl hb
  · obtain ⟨Z, hZ, hZhits⟩ := (closeToBipartite_iff_hitsOddCycles (m := MaxDef G)).mp
      (hE W inst G (MaxDef G) (locIndep_of_maxDef_le (Nat.le_refl (MaxDef G))) hH)
    have hne : 0 < Z.card := by
      by_contra hcon
      have hZ0 : Z = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hZ0
      have hnone : ¬ ∃ C : Finset W, IsOddCycle G C := by
        rintro ⟨C, hC⟩
        have h := hZhits C hC
        rw [Finset.inter_empty] at h
        exact h rfl
      exact hb (maxDef_eq_zero_iff.mpr (isBipartite_of_no_oddCycle hnone))
    exact Or.inr (selfPay_of_transversal hZhits hZ hne)

end

end JSP90
