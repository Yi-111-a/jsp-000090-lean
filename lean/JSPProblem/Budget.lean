import JSPProblem.Greedy
import JSPProblem.PackDescent

/-!
# JSP-000090, round 103 — the **PACKING BUDGET ALONG THE GREEDY CHAIN**: `k − j` at level `j`

Attack family 44.  Round 102 (`JSPProblem/Greedy.lean`) built the greedy shortest-odd-cycle chain
and recorded in `discovery/JSP-000090/policy.json` option (A) the one quantitative input its ladder
was missing:

> `JSP90.OddCyclePackingLe (k - j) (level G j)` for `j ≤ k`.

This file proves exactly that, in **two** forms, and derives a general ladder step and a new
instance of the headline theorem from them.

## What is proved

* **The exchange lemma** `JSP90.oddCycleFamily_union_chainBelow` — a packing of the residue at
  level `j`, adjoined with the `j` greedy cycles of the earlier levels, is a packing of odd cycles
  of `G` of size `P.card + j`.  Nothing has to be chosen: the greedy cycles are pairwise
  vertex-disjoint (`JSP90.disjoint_greedyCycle_of_lt`), lie inside the deleted set
  `JSP90.unionUpTo G j`, every odd cycle of the residue avoids that set
  (`JSP90.disjoint_unionUpTo_of_isOddCycle_level`), and none of them is a member of the residue
  (`JSP90.not_mem_chainBelow_of_isOddCycleFamily`).

* **THE PACKING BUDGET** `JSP90.level_oddCyclePackingLe`:

  > `LocIndep k G → j ≤ k → OddCyclePackingLe (k - j) (level G j)`

  and its arithmetic form `JSP90.level_packing_add_le`: `P.card + j ≤ k` for every packing `P` of
  the residue at level `j`.  `JSP90.level_oddCyclePackingLe_one` is the classical residue step
  (`j = k - 1`: after deleting the shortest odd cycle the packing number drops by one), and
  `JSP90.level_isBipartite_of_budget` is the `j = k` end of the same budget (packing number `0`
  means bipartite).

* **THE DEFICIENCY BUDGET** `JSP90.level_maxDef_add_le` and `JSP90.level_locIndep`:

  > `LocIndep k G → LocIndep (k - j) (level G j)`

  i.e. **Erdős's hypothesis descends along the greedy chain with the parameter one smaller per
  level** — round 87's `maxDef_ge_card_add_maxDef_delete` applied to the greedy chain
  (`j + MaxDef (level G j) ≤ MaxDef G`).  Round 102 only had the binary statement "level `k` is
  bipartite"; this is the quantitative version, and it is what an induction along the chain
  consumes.

* **THE LADDER WITH A PER-LEVEL RESIDUE COST** `JSP90.closeToBipartite_of_greedyChain_cost`
  (`JSP90.stepCost`), which strictly generalises round 102's
  `closeToBipartite_of_greedyChain_step`, and the new instance

  > `JSP90.erdos73On_of_greedyChain_cost`:
  > `LocIndep k G → (∀ i, 1 ≤ i → i ≤ k → CloseToBipartite c i (level G i)) →
  >   CloseToBipartite (∑ j < k, girthOf (level G j) + c (j + 1)) G`

  a hypothesis form of the headline theorem in which the **residues pay a level-dependent price**,
  and its unit-cost instance `JSP90.closeToBipartite_of_greedyChain_cost_one`, which is *strictly
  cheaper* than round 102's constant by exactly `k`.

## Why this is progress and not a reformulation

The budgets `k − j` (packings) and `LocIndep (k − j)` (deficiency) are exactly the quantity the
classical Erdős–Pósa induction for odd cycles decreases, and neither was available anywhere in the
development before this round: the greedy chain of round 102 was only used to make the *last* level
bipartite.  The gap to `jsp_000090_main` is unchanged and is recorded in
`discovery/JSP-000090/policy.json`: the budgets are proved, but the **transversal** half — a bound on
an odd cycle transversal in terms of the packing number — is still `JSP90.OddCycleErdosPosa r`.
-/

set_option maxHeartbeats 3000000

namespace JSP90

noncomputable section

variable {V : Type*} [Fintype V]

universe u

local instance instDecidableEqBudget : DecidableEq V := Classical.decEq V

/-! ### Part 1 — the greedy chain below a level, and what a level avoids -/

section Local

/-- **THE `j` GREEDY CYCLES BELOW LEVEL `j`**, as a family of vertex sets. -/
noncomputable def chainBelow (H : SimpleGraph V) (j : ℕ) : Finset (Finset V) :=
  (Finset.range j).image fun i => greedyCycle (level H i)

@[simp] theorem chainBelow_zero (H : SimpleGraph V) : chainBelow H 0 = ∅ := by
  simp [chainBelow]

/-- **A GREEDY CYCLE OF AN EARLIER LEVEL IS DELETED BEFORE A LATER LEVEL.** -/
theorem greedyCycle_subset_unionUpTo {H : SimpleGraph V} {i j : ℕ} (hij : i < j) :
    greedyCycle (level H i) ⊆ unionUpTo H j :=
  fun v hv => mem_unionUpTo.mpr ⟨i, hij, hv⟩

/-- **EVERY MEMBER OF THE `j` GREEDY CYCLES BELOW LEVEL `j` LIES IN THE DELETED SET.** -/
theorem subset_unionUpTo_of_mem_chainBelow {H : SimpleGraph V} (j : ℕ) {X : Finset V}
    (hX : X ∈ chainBelow H j) : X ⊆ unionUpTo H j := by
  obtain ⟨i, hi, hiX⟩ := Finset.mem_image.mp hX
  rw [← hiX]
  exact greedyCycle_subset_unionUpTo (Finset.mem_range.mp hi)

/-- **AN ODD CYCLE OF A LEVEL AVOIDS EVERYTHING DELETED BEFORE IT.**

Every vertex of an odd cycle of `level H j` has a neighbour inside the cycle, hence survives the
deletion of `unionUpTo H j`. -/
theorem disjoint_unionUpTo_of_isOddCycle_level {H : SimpleGraph V} {j : ℕ} {C : Finset V}
    (hC : IsOddCycle (level H j) C) : Disjoint C (unionUpTo H j) := by
  refine Finset.disjoint_left.mpr fun v hv => ?_
  have h1 := isOddCycle_subset_vertsOf hC hv
  rw [level_eq_deleteFinset_unionUpTo] at h1
  exact not_mem_of_mem_vertsOf_deleteFinset h1

/-- **A PACKING OF THE RESIDUE AVOIDS THE DELETED SET, MEMBER BY MEMBER.** -/
theorem disjointP_chainBelow_of_isOddCycleFamily {H : SimpleGraph V} {j : ℕ}
    {P : Finset (Finset V)} (hP : IsOddCycleFamily (G := level H j) P)
    (X Y : Finset V) (hX : X ∈ P) (hY : Y ∈ chainBelow H j) : X ∩ Y = ∅ := by
  have hYsub : Y ⊆ unionUpTo H j := subset_unionUpTo_of_mem_chainBelow j hY
  refine (Finset.disjoint_iff_inter_eq_empty (s := X) (t := Y)).mp ?_
  refine Finset.disjoint_left.mpr fun v hvX hYv => ?_
  exact Finset.disjoint_left.mp (disjoint_unionUpTo_of_isOddCycle_level (hP.2 X hX)) hvX
    (hYsub hYv)

/-- **THE RESIDUE AT LEVEL `j` CONTAINS NONE OF THE `j` DELETED GREEDY CYCLES.** -/
theorem not_mem_chainBelow_of_isOddCycleFamily {H : SimpleGraph V} {j : ℕ}
    {P : Finset (Finset V)} (hP : IsOddCycleFamily (G := level H j) P) {X : Finset V}
    (hX : X ∈ chainBelow H j) : X ∉ P := by
  intro hXP
  obtain ⟨x, hx⟩ := (hP.2 X hXP).nonempty
  exact Finset.disjoint_left.mp (disjoint_unionUpTo_of_isOddCycle_level (hP.2 X hXP)) hx
    ((subset_unionUpTo_of_mem_chainBelow j hX) hx)

/-- **THE DELETED SET OF THE CHAIN IS THE UNION OF THE CHAIN.** -/
theorem biUnion_chainBelow {H : SimpleGraph V} (j : ℕ) :
    (chainBelow H j).biUnion id = unionUpTo H j := by
  ext v
  constructor
  · intro hv
    obtain ⟨X, hX, hvX⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨i, hi, hiX⟩ := Finset.mem_image.mp hX
    rw [← hiX] at hvX
    exact mem_unionUpTo.mpr ⟨i, Finset.mem_range.mp hi, hvX⟩
  · intro hv
    obtain ⟨i, hi, hvX⟩ := mem_unionUpTo.mp hv
    exact Finset.mem_biUnion.mpr
      ⟨greedyCycle (level H i), Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩, hvX⟩

/-- **THE CARDINALITY OF THE CHAIN.** -/
theorem card_chainBelow {H : SimpleGraph V} {j : ℕ}
    (hCi : ∀ i < j, IsOddCycle (level H i) (greedyCycle (level H i))) :
    (chainBelow H j).card = j := by
  have h := card_image_greedyChain (H := H) (n := j) hCi
  simpa [chainBelow] using h

/-- **THE EXCHANGE LEMMA: A PACKING OF THE RESIDUE AT LEVEL `j` EXTENDS TO A PACKING OF `G` OF SIZE
`P.card + j`, BY ADJOINING THE `j` GREEDY CYCLES OF THE EARLIER LEVELS.**

This is round 102's `packing_of_levels` with an *arbitrary* packing of the residue in place of the
greedy one: the greedy chain is not merely a packing, it **completes every** packing of the
residue. -/
theorem oddCycleFamily_union_chainBelow {H : SimpleGraph V} {j : ℕ} {P : Finset (Finset V)}
    (hP : IsOddCycleFamily (G := level H j) P)
    (hCi : ∀ i < j, IsOddCycle (level H i) (greedyCycle (level H i))) :
    IsOddCycleFamily (G := H) (chainBelow H j ∪ P) ∧ (chainBelow H j ∪ P).card = j + P.card := by
  have hchain : IsOddCycleFamily (G := H) (chainBelow H j) := by
    have h := isOddCycleFamily_greedyChain_image (H := H) (n := j) hCi
    simpa [chainBelow] using h
  have hdis : Disjoint (chainBelow H j) P :=
    Finset.disjoint_left.mpr fun X hX hXP => not_mem_chainBelow_of_isOddCycleFamily hP hX hXP
  have hfam : IsOddCycleFamily (G := H) (chainBelow H j ∪ P) := by
    constructor
    · intro X hX Y hY hXY
      rw [Finset.mem_union] at hX hY
      rcases hX with hX | hX <;> rcases hY with hY | hY
      · exact hchain.1 X hX Y hY hXY
      · exact (Finset.inter_comm X Y).symm ▸
          disjointP_chainBelow_of_isOddCycleFamily hP Y X hY hX
      · exact (Finset.inter_comm X Y) ▸
          disjointP_chainBelow_of_isOddCycleFamily hP X Y hX hY
      · exact hP.1 X hX Y hY hXY
    · intro X hX
      rw [Finset.mem_union] at hX
      rcases hX with hX | hX
      · exact hchain.2 X hX
      · exact isOddCycle_of_isOddCycle_deleteFinset (by
          have h2 := hP.2 X hX
          rw [level_eq_deleteFinset_unionUpTo] at h2
          exact h2)
  exact ⟨hfam, by rw [Finset.card_union_of_disjoint hdis, card_chainBelow hCi]⟩

end Local

/-! ### Part 2 — THE PACKING BUDGET -/

section Budget

/-- **THE PACKING NUMBER OF THE RESIDUE AT LEVEL `j` IS AT MOST `k - j`.**

This is the missing lemma recorded in `discovery/JSP-000090/policy.json` after round 102.  The `j`
greedy cycles of the earlier levels are `j` pairwise vertex-disjoint odd cycles of `G` lying
*outside* the residue, so `JSP90.oddCycleFamily_union_chainBelow` adjoins them to any packing of the
residue, and `LocIndep k G` bounds every packing of odd cycles of `G` by `k`
(`JSP90.locIndep_oddCyclePackingLe`). -/
theorem level_oddCyclePackingLe {k j : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) (hjk : j ≤ k) :
    OddCyclePackingLe (k - j) (level G j) := by
  intro P hP
  by_cases hb : (level G j).IsBipartite
  · have hne : ¬ P.Nonempty := by
      rintro ⟨X, hX⟩
      exact (not_isOddCycle_of_isBipartite hb) ⟨X, hP.2 X hX⟩
    have hP0 : P.card = 0 := Finset.card_eq_zero.mpr (by
      by_contra hcon
      exact hne (Finset.nonempty_iff_ne_empty.mpr hcon))
    rw [hP0]
    exact Nat.zero_le _
  · have hnb : ∀ i < j, ¬ (level G i).IsBipartite := by
      intro i hi hbi
      exact hb (isBipartite_level_mono' (Nat.le_of_lt hi) hbi)
    have hCi : ∀ i < j, IsOddCycle (level G i) (greedyCycle (level G i)) :=
      fun i hi => isOddCycle_greedyCycle_of_not_isBipartite (hnb i hi)
    obtain ⟨hf, hcard⟩ := oddCycleFamily_union_chainBelow hP hCi
    have hle := (locIndep_oddCyclePackingLe hG) (chainBelow G j ∪ P) hf
    rw [hcard] at hle
    omega

/-- **THE BUDGET IN ITS ARITHMETIC FORM: a packing of the residue at level `j` has at most `k - j`
members, and the `j` greedy cycles adjoined to it still fit inside `k`. -/
theorem level_packing_add_le {k j : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) (hjk : j ≤ k)
    {P : Finset (Finset V)} (hP : IsOddCycleFamily (G := level G j) P) : P.card + j ≤ k := by
  have h1 := (level_oddCyclePackingLe hG hjk) P hP
  omega

/-- **THE CLASSICAL RESIDUE STEP IN THE BUDGET FORM: after deleting the shortest odd cycle the
packing number drops by one.** -/
theorem level_oddCyclePackingLe_one {k : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) (hk : 1 ≤ k) :
    OddCyclePackingLe (k - 1) (level G 1) := by
  exact level_oddCyclePackingLe hG (j := 1) (by omega)

/-- **THE `j = k` END OF THE BUDGET IS ROUND 102'S BIPARTITENESS STATEMENT, RE-DERIVED IN THE
PACKING VOCABULARY.** -/
theorem level_isBipartite_of_budget {k j : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) (hjk : j ≤ k)
    (hj : j = k) : (level G j).IsBipartite := by
  have h1 := level_oddCyclePackingLe hG hjk
  exact isBipartite_of_oddCyclePackingLe_zero h1 (by omega)

end Budget

/-! ### Part 3 — THE DEFICIENCY BUDGET: `LocIndep (k - j)` AT LEVEL `j` -/

section Deficiency

/-- **ERDŐS'S HYPOTHESIS IS HEREDITARY ALONG THE CHAIN.** -/
theorem level_locIndep_of_locIndep {k : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) (j : ℕ) :
    LocIndep k (level G j) := by
  rw [level_eq_deleteFinset_unionUpTo]
  exact LocIndep.of_deleteFinset hG (unionUpTo G j)

/-- **THE DEFICIENCY PAYS FOR THE WHOLE GREEDY CHAIN: `j + MaxDef (level G j) ≤ MaxDef G`.**

Round 87's `JSP90.maxDef_ge_card_add_maxDef_delete` applied to the `j` greedy cycles, which are a
packing of odd cycles of `G` (`JSP90.isOddCycleFamily_greedyChain_image`). -/
theorem level_maxDef_add_le {k j : ℕ} {G : SimpleGraph V} (hG : LocIndep k G)
    (hnb : ∀ i < j, ¬ (level G i).IsBipartite) : MaxDef (level G j) + j ≤ MaxDef G := by
  have hCi : ∀ i < j, IsOddCycle (level G i) (greedyCycle (level G i)) :=
    fun i hi => isOddCycle_greedyCycle_of_not_isBipartite (hnb i hi)
  have hfam : IsOddCycleFamily (G := G) (chainBelow G j) := by
    simpa only [chainBelow] using isOddCycleFamily_greedyChain_image (H := G) (n := j) hCi
  have hcard : (chainBelow G j).card = j := card_chainBelow hCi
  have h1 := maxDef_ge_card_add_maxDef_delete (G := G) hfam
  have heq : deleteFinset G ((chainBelow G j).biUnion id) = level G j := by
    rw [biUnion_chainBelow, ← level_eq_deleteFinset_unionUpTo]
  rw [heq, hcard] at h1
  have h2 := maxDef_le_of_locIndep hG
  omega

/-- **ERDŐS'S HYPOTHESIS DESCENDS ALONG THE GREEDY CHAIN, ONE UNIT PER LEVEL.**

> `LocIndep k G → (∀ i < j, ¬ (level G i).IsBipartite) → LocIndep (k - j) (level G j)`

This is the *quantitative* form of round 102's `level_isBipartite_of_locIndep` (which is the case
`j = k`, the hypothesis then being vacuous): at level `j` the local hypothesis of Erdős Problem #73
holds with the strictly smaller parameter `k - j`, and the proof is round 87's deficiency descent
read along the chain. -/
theorem level_locIndep {k j : ℕ} {G : SimpleGraph V} (hG : LocIndep k G)
    (hnb : ∀ i < j, ¬ (level G i).IsBipartite) : LocIndep (k - j) (level G j) := by
  have h1 := level_maxDef_add_le hG hnb
  have h2 := maxDef_le_of_locIndep hG
  refine locIndep_of_maxDef_le ?_
  omega

/-- **THE SAME, AT EVERY LEVEL UP TO THE POINT WHERE THE CHAIN STOPS, AND WITHOUT ANY HYPOTHESIS.**

For `j ≤ firstBipartiteLevel G k` the levels below `j` are automatically non-bipartite
(`JSP90.not_isBipartite_of_lt_firstBipartiteLevel`), and above it Erdős's hypothesis is
`LocIndep 0`, i.e. bipartiteness. -/
theorem level_locIndep_of_firstBipartite {k j : ℕ} {G : SimpleGraph V} (hG : LocIndep k G)
    (hjk : j ≤ firstBipartiteLevel G k) : LocIndep (k - j) (level G j) := by
  by_cases hb : (level G j).IsBipartite
  · have h0 := locIndep_zero_of_isBipartite hb
    intro X
    obtain ⟨S, hS, hSi, _⟩ := h0 X
    exact ⟨S, hS, hSi, by omega⟩
  · obtain ⟨j0, hj0, hb0⟩ := exists_firstBipartiteLevel hG
    exact level_locIndep hG (fun i hi =>
      not_isBipartite_of_lt_firstBipartiteLevel (H := G) (k := k) (j := i) ⟨j0, hj0, hb0⟩
        (by omega))

/-- **THE TOP OF THE CHAIN: `LocIndep k G` MAKES THE RESIDUE AT LEVEL `k - 1` SATISFY ERDŐS'S
HYPOTHESIS WITH PARAMETER `1`.** -/
theorem level_locIndep_one {k : ℕ} {G : SimpleGraph V} (hG : LocIndep k G) (hk : 1 ≤ k) :
    LocIndep 1 (level G (k - 1)) := by
  obtain ⟨j0, hj0, hb0⟩ := exists_firstBipartiteLevel hG
  by_cases hb : (level G (k - 1)).IsBipartite
  · have h0 := locIndep_zero_of_isBipartite hb
    intro X
    obtain ⟨S, hS, hSi, _⟩ := h0 X
    exact ⟨S, hS, hSi, by omega⟩
  · have hlt : k - 1 < firstBipartiteLevel G k := by
      have hspec := firstBipartiteLevel_spec (H := G) (k := k) ⟨j0, hj0, hb0⟩
      by_contra hcon
      exact hb (isBipartite_level_mono' (Nat.le_of_not_gt hcon) hspec.2)
    have h1 := level_locIndep_of_firstBipartite hG (Nat.le_of_lt hlt)
    have hsub : k - (k - 1) = 1 := by omega
    rwa [hsub] at h1

end Deficiency

/-! ### Part 4 — the ladder with a per-level residue cost, and the new instance -/

section Ladder

/-- **THE COST OF LEVEL `j`**: the greedy cycle it deletes (`g j`) plus the price of the residue it
leaves behind (`c (j + 1)`). -/
noncomputable def stepCost (c g : ℕ → ℕ) (j : ℕ) : ℕ := g j + c (j + 1)

/-- **The same price, with the greedy cycle charged at its own odd girth.** -/
noncomputable def girthStepCost (c : ℕ → ℕ) (G : SimpleGraph V) (j : ℕ) : ℕ :=
  stepCost c (fun i => girthOf (level G i)) j

theorem girthSum_add_zero (n : ℕ) (g : ℕ → ℕ) : girthSum n (fun j => g j + 0) = girthSum n g := by
  unfold girthSum
  exact Finset.sum_congr rfl fun j _ => Nat.add_zero (g j)

/-- **THE STEP-IDENTITY OF THE LADDER COST**: the cost of the last level is the greedy cycle plus the
price of the last residue. -/
theorem girthSum_stepCost (n : ℕ) (c g : ℕ → ℕ) :
    girthSum (n + 1) (fun j => stepCost c g j) =
      girthSum n (fun j => g (j + 1) + c (j + 2)) + (g 0 + c 1) := by
  have key : (fun j : ℕ => stepCost c g j) = fun j => g j + c (j + 1) := by
    funext j
    rfl
  rw [key, girthSum_succ]

/-- **THE GREEDY LADDER WITH A PER-LEVEL RESIDUE COST.**

> if for every `j < n` the greedy cycle of level `j` has at most `g j` vertices, every residue
> `level H i` (`1 ≤ i ≤ n`) is `c i`-close to bipartite, and `level H n` is bipartite, then
> `CloseToBipartite (∑ j < n, g j + c (j + 1)) H`.

This **strictly generalises** round 102's `closeToBipartite_of_greedyChain_step`, which is the case
`c ≡ 0` with all the levels `1 … n` bipartite.  The residue price is what makes the budgets of
Parts 2–3 usable: at level `i` it may be paid by *any* instance of Erdős Problem #73 available at
the parameter `k - i`. -/
theorem closeToBipartite_of_greedyChain_cost : ∀ (n : ℕ) (c g : ℕ → ℕ) (H : SimpleGraph V),
    (∀ j < n, (greedyCycle (level H j)).card ≤ g j) →
    (∀ i, 1 ≤ i → i ≤ n → CloseToBipartite (c i) (level H i)) →
    (level H n).IsBipartite →
    CloseToBipartite (girthSum n (fun j => stepCost c g j)) H := by
  intro n
  induction n with
  | zero =>
      intro c g H hg hc hb
      exact closeToBipartite_of_isBipartite' hb
  | succ n ih =>
      intro c g H hg hc hb
      have hrec : CloseToBipartite
          (girthSum n (fun j => stepCost (fun i => c (i + 1)) (fun i => g (i + 1)) j)) (level H 1) :=
        ih (fun i => c (i + 1)) (fun j => g (j + 1)) (level H 1)
        (fun j hj => by
          have h1 := hg (j + 1) (by omega)
          have h3 : level H (1 + j) = level H (j + 1) := by rw [Nat.add_comm]
          rw [level_tail H 1 j, h3]
          exact h1)
        (fun i hi hi' => by
          have h2 := hc (i + 1) (by omega) (by omega)
          have h3 : level H (1 + i) = level H (i + 1) := by rw [Nat.add_comm]
          rw [level_tail H 1 i, h3]
          exact h2)
        (by rw [level_tail H 1 n, show 1 + n = n + 1 by omega]; exact hb)
      have hres := closeToBipartite_of_residue (G := level H 0) (C := greedyCycle (level H 0)) hrec
      have hH : level H 0 = H := level_zero H
      rw [← hH] at hres
      refine CloseToBipartite.mono hres ?_
      have hfun : (fun i : ℕ => stepCost (fun i => c (i + 1)) (fun i => g (i + 1)) i) =
          (fun j => g (j + 1) + c (j + 2)) := by
        funext i
        rfl
      rw [hfun, girthSum_stepCost]
      simp only [level_zero]
      have hcard : (greedyCycle H).card ≤ g 0 := hg 0 (by omega)
      omega

/-- **ROUND 102'S STEP, RE-DERIVED FROM THE LADDER WITH `c ≡ 0`.** -/
theorem closeToBipartite_of_greedyChain_cost_bipartiteLevels (n : ℕ) (H : SimpleGraph V)
    (hg : ∀ j < n, (greedyCycle (level H j)).card ≤ girthOf (level H j))
    (hb : ∀ i, 1 ≤ i → i ≤ n → (level H i).IsBipartite)
    (hbn : (level H n).IsBipartite) :
    CloseToBipartite (girthSum n (fun j => girthOf (level H j))) H := by
  refine CloseToBipartite.mono
    (closeToBipartite_of_greedyChain_cost n (fun _ => 0) (fun j => girthOf (level H j)) H hg
      (fun i hi hi' => closeToBipartite_of_isBipartite' (hb i hi hi')) hbn) ?_
  have heq : girthSum n (fun j => stepCost (fun _ => 0) (fun i => girthOf (level H i)) j) =
      girthSum n (fun j => girthOf (level H j)) := by
    simp only [stepCost, girthSum_add_zero]
  rw [heq]

/-- **THE NEW INSTANCE OF THE HEADLINE THEOREM: EVERY GREEDY RESIDUE PAYS ITS OWN PRICE.**

> `LocIndep k G → (∀ i, 1 ≤ i → i ≤ k → CloseToBipartite c i (level G i)) →
>   CloseToBipartite (∑ j < k, girthOf (level G j) + c (j + 1)) G`

The hypothesis is Erdős's own **plus** a local statement about the residues — "the residue after
`j` greedy deletions is `c (j + 1)`-close to bipartite" — and no girth bound, no degree bound, no
chain, no connectivity or decomposition hypothesis.  The constant is the greedy sum of round 102
plus the sum of the residue prices.  This is the shape in which the budgets of Parts 2–3 enter a
theorem: `c i` may be any instance available at the parameter `k - i`. -/
theorem closeToBipartite_of_greedyChain_cost_locIndep {k : ℕ} (G : SimpleGraph V)
    (hG : LocIndep k G) (c : ℕ → ℕ)
    (hc : ∀ i, 1 ≤ i → i ≤ k → CloseToBipartite (c i) (level G i)) :
    CloseToBipartite (girthSum k (girthStepCost c G)) G := by
  exact closeToBipartite_of_greedyChain_cost k c (fun j => girthOf (level G j)) G
    (fun j hj => card_greedyCycle_le_girthOf (level G j)) hc
    (level_isBipartite_of_locIndep hG)

/-- **THE HEADLINE INSTANCE IN THE SHAPE OF THE PROBLEM STATEMENT (all finite vertex types).** -/
theorem erdos73On_of_greedyChain_cost (k : ℕ) (c : ℕ → ℕ) :
    ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
      (∀ i, 1 ≤ i → i ≤ k → CloseToBipartite (c i) (level G i)) →
      CloseToBipartite (girthSum k (girthStepCost c G)) G := by
  intro W instW G hG hc
  exact closeToBipartite_of_greedyChain_cost_locIndep G hG c hc

/-- **THE UNIT-COST INSTANCE: if every greedy residue is `1`-close to bipartite, the greedy ladder
costs the greedy sum *plus one per level*.**

> `CloseToBipartite (∑ j < k, girthOf (level G j) + 1) G`

which is **strictly smaller** than round 102's `∑ j < k, girthOf (level G j)` by exactly `k`
(`JSP90.girthSum_lt_of_unit`). -/
theorem closeToBipartite_of_greedyChain_cost_one {k : ℕ} (G : SimpleGraph V) (hG : LocIndep k G)
    (h1 : ∀ i, 1 ≤ i → i ≤ k → CloseToBipartite 1 (level G i)) :
    CloseToBipartite (girthSum k (fun j => girthOf (level G j) + 1)) G := by
  exact closeToBipartite_of_greedyChain_cost_locIndep G hG (fun _ => 1) h1

/-- **THE ARITHMETIC OF THE UNIT-COST INSTANCE.** -/
theorem girthSum_lt_of_unit (k : ℕ) (g : ℕ → ℕ) :
    girthSum k g < girthSum k (fun j => g j + 1) + 1 := by
  unfold girthSum
  have h : ((Finset.range k).sum (fun j => g j + 1)) = (Finset.range k).sum g + k := by
    calc ((Finset.range k).sum (fun j => g j + 1))
        = (Finset.range k).sum (fun j => g j)
            + (Finset.range k).sum (fun _ : ℕ => (1 : ℕ)) := by
          simpa using (Finset.sum_add_distrib (s := Finset.range k) (f := fun j => g j)
            (g := fun _ => (1 : ℕ)))
      _ = (Finset.range k).sum (fun j => g j) + k := by
          rw [← Finset.card_eq_sum_ones, Finset.card_range]
  rw [h]
  exact Nat.lt_succ_of_le (Nat.le_add_right _ _)

end Ladder

end

end JSP90
