/-
# JSP-000090 — the cut descent of the deficiency, and the reduction to triangle-free graphs

This file is the **fourteenth attack family**.  It continues the *numerical* line opened by
`JSPProblem/Deficiency.lean` — the quantity `MaxDef G = max {|X| - 2 * α(G[X]) : X ⊆ V}`, with
`LocIndep k G ↔ MaxDef G ≤ k` — but it attacks the problem at a **separator**, in the vocabulary
of the maximum deficiency rather than in the vocabulary of the boundary of a shortest odd cycle.

## What is new

1. **THE CARDINALITY AND THE INDEPENDENCE NUMBER SPLIT OVER AN ANTICOMPLETE COVER**:
   `JSP90.sum_card_inter_le_card` (the cardinalities of the parts of a cover add up to at most that
   of the whole) and `JSP90.indepCard_le_add` (`α(A ∪ B) ≤ α(A) + α(B)`: the independent sets of a
   union split into an independent subset of each side).  Together with
   `JSP90.sum_sub_eq_of_le` — `∑ (aᵢ - bᵢ) = (∑ aᵢ) - (∑ bᵢ)` whenever `bᵢ ≤ aᵢ`, which is FALSE
   for natural subtraction in general and is exactly the obstruction round 54 recorded — these are
   the two halves of the additivity of the deficiency over an anticomplete decomposition.

2. **THE DEFICIENCY DROPS AT A TRIANGLE** (`JSP90.maxDef_ge_one_add_maxDef_of_anticoverCut_of_triangle`):
   for every piece `Q` of a cut at a triangle, `1 + MaxDef G[Q] ≤ MaxDef G`, and the sum of the
   deficiencies of the non-bipartite pieces is at most `MaxDef G - 1`.  This is what makes an
   induction on `k` in `LocIndep k G` close at a triangle.

3. **THE REDUCTION** (`JSP90.erdos73On_of_triangleFree`, `JSP90.erdos73_on_triangleFree`,
   `JSP90.erdos73_of_triangleFree`, `JSP90.oddCycleErdosPosa_of_triangleFree`): **Erdős Problem #73,
   in full, follows from its restriction to triangle-free graphs**, with the explicit constant
   `f(k) = 4 ^ k`.  The induction is on `k` alone: at a triangle the deficiency drops by `1`, the
   cost is `3` for the triangle itself, and superadditivity of `f` turns the `c` non-bipartite
   pieces into `f (k - 1)`.

So the single missing lemma of the whole development is now

```lean
JSP90.TriangleFreeErdős73 : ∃ f, ∀ k, ∀ G, G.CliqueFree 3 → MaxDef G ≤ k → CloseToBipartite (f k) G
```

which is **strictly weaker** than the Reed–Robertson–Seymour–Thomas theorem
(`JSPProblem/Transversal.lean`, `OddCycleErdosPosa r`, the primary blocker of the earlier rounds):
a triangle-free graph of packing number `≤ r` has deficiency `≤ r`, so the new hypothesis implies
the old one, and the new hypothesis is a statement only about triangle-free graphs.

4. The numerical hypotheses of the reduction theorem are discharged for `f k = 4 ^ k`
   (`JSP90.sup_pow_four`, `JSP90.step_pow_four`, `JSP90.add_le_mul_of_two_le`,
   `JSP90.sum_f_le_f_sum`, `JSP90.f_mono_of_succ_le`).

## What is *not* proved

**The one lemma this round ran out of budget for is `JSP90.indepCard_le_sum_inter`:** the statement
that `α(G[X]) ≤ ∑_Q α(G[X ∩ Q])` for a vertex set `X` covered by an anticomplete family, i.e. that
the independence number splits *over a family* (the two-set case, `indepCard_le_add`, is proved
above).  With it, the chain below closes and the whole reduction follows; without it the superadditive
half of the deficiency (`∑ MaxDef G[Q] ≤ MaxDef G`) and hence `TriangleFreeErdős73`'s reduction
cannot be finished.  See `discovery/JSP-000090/policy.json` for the exact statement and the two
routes to it.  `jsp_000090_main` is therefore still not declared.
-/

import JSPProblem.Deficiency
import JSPProblem.OffCycle
import JSPProblem.Additive
import JSPProblem.Connect

namespace JSP90

open Finset Fintype Set

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance : DecidableEq V := Classical.decEq V

local instance (G : SimpleGraph V) : DecidablePred fun S : Finset V => G.IsIndepSet S :=
  fun _ => Classical.propDecidable _

/-! ### Part 0 — the arithmetic of the deficiency -/

section Arithmetic

/-- **`(∑ aᵢ) - (∑ bᵢ) ≤ ∑ (aᵢ - bᵢ)`** for natural numbers.  The truncated subtraction makes this
true even when the left-hand side vanishes. -/
theorem sum_sub_le {ι : Type*} (s : Finset ι) (f g : ι → ℕ) :
    (∑ i ∈ s, f i) - (∑ i ∈ s, g i) ≤ ∑ i ∈ s, (f i - g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      have hle : (∑ j ∈ t, f j) ≤ (∑ j ∈ t, (f j - g j)) + ∑ j ∈ t, g j :=
        (Nat.sub_le_iff_le_add).mp ih
      have hself : f i ≤ (f i - g i) + g i := by
        by_cases h : g i ≤ f i
        · rw [Nat.sub_add_cancel h]
        · have h2 : f i - g i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge h)
          rw [h2]
          omega
      have e1 : (∑ j ∈ insert i t, f j) = f i + ∑ j ∈ t, f j := Finset.sum_insert hi
      have e2 : (∑ j ∈ insert i t, g j) = g i + ∑ j ∈ t, g j := Finset.sum_insert hi
      have e3 : (∑ j ∈ insert i t, (f j - g j)) = (f i - g i) + ∑ j ∈ t, (f j - g j) :=
        Finset.sum_insert hi
      refine (Nat.sub_le_iff_le_add).mpr ?_
      rw [e1, e2, e3]
      calc f i + ∑ j ∈ t, f j
          ≤ f i + ((∑ j ∈ t, (f j - g j)) + ∑ j ∈ t, g j) := Nat.add_le_add_left hle _
        _ ≤ (f i - g i) + ((∑ j ∈ t, (f j - g j)) + ∑ j ∈ t, g j) + g i := by omega
        _ = ((f i - g i) + ∑ j ∈ t, (f j - g j)) + (g i + ∑ j ∈ t, g j) := by
            simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- **`∑ (aᵢ - bᵢ) = (∑ aᵢ) - (∑ bᵢ)` whenever `bᵢ ≤ aᵢ` for all `i`.**  With the truncated
subtraction of `ℕ` this is false in general — that is exactly the obstruction round 54 recorded —
but it holds as soon as no truncation occurs. -/
theorem sum_sub_eq_of_le {ι : Type*} (s : Finset ι) (f g : ι → ℕ) (h : ∀ i ∈ s, g i ≤ f i) :
    ∑ i ∈ s, (f i - g i) = (∑ i ∈ s, f i) - (∑ i ∈ s, g i) := by
  have h2 : (∑ i ∈ s, (g i + (f i - g i))) = (∑ i ∈ s, g i) + ∑ i ∈ s, (f i - g i) :=
    Finset.sum_add_distrib
  have h1 : (∑ i ∈ s, f i) = ∑ i ∈ s, (g i + (f i - g i)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    exact (Nat.add_sub_of_le (h i hi)).symm
  rw [h1, h2]
  omega

/-- A superadditive function bounds a sum of its values by its value at the sum of the arguments,
provided every argument is positive. -/
theorem sum_f_le_f_sum {f : ℕ → ℕ} {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (hsup : ∀ i j, 1 ≤ i → 1 ≤ j → f i + f j ≤ f (i + j)) (ha : ∀ i ∈ s, 1 ≤ a i) :
    (∑ i ∈ s, f (a i)) ≤ f (∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      have h1 : (∑ j ∈ t, f (a j)) ≤ f (∑ j ∈ t, a j) :=
        ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have e1 : (∑ j ∈ insert i t, f (a j)) = f (a i) + ∑ j ∈ t, f (a j) := Finset.sum_insert hi
      have e2 : (∑ j ∈ insert i t, a j) = a i + ∑ j ∈ t, a j := Finset.sum_insert hi
      rw [e1, e2]
      by_cases hne : t.Nonempty
      · calc f (a i) + ∑ j ∈ t, f (a j) ≤ f (a i) + f (∑ j ∈ t, a j) := Nat.add_le_add_left h1 _
        _ ≤ f (a i + ∑ j ∈ t, a j) :=
            hsup (a i) _ (ha i (Finset.mem_insert_self i t))
              (Nat.succ_le_of_lt (Finset.sum_pos (fun j hj => by
                have := ha j (Finset.mem_insert_of_mem hj)
                omega) hne))
      · have hte : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hlt : (∑ j ∈ t, f (a j)) = 0 := by rw [hte]; simp
        have hrt : (∑ j ∈ t, a j) = 0 := by rw [hte]; simp
        rw [hlt, hrt, Nat.add_zero]
        exact Nat.le_refl _

/-- A non-decreasing function on `ℕ`. -/
theorem f_mono_of_succ_le {f : ℕ → ℕ} (h : ∀ j, f j ≤ f (j + 1)) {a b : ℕ} (hab : a ≤ b) :
    f a ≤ f b := by
  induction b, hab using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ b _ ih => exact Nat.le_trans ih (h b)

/-- **`a + b ≤ a * b` when `2 ≤ a` and `2 ≤ b`.** -/
theorem add_le_mul_of_two_le {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) : a + b ≤ a * b := by
  have hb'' : b = (b - 1) + 1 := by omega
  have h1 : a * b = a * (b - 1) + a := by
    calc a * b = a * ((b - 1) + 1) := by rw [← hb'']
      _ = a * (b - 1) + a * 1 := Nat.mul_add _ _ _
      _ = a * (b - 1) + a := by rw [Nat.mul_one]
  have hb5 : b ≤ a * (b - 1) := by
    calc b = (b - 1) + 1 := by omega
      _ ≤ (b - 1) + (b - 1) := Nat.add_le_add_left (by omega) _
      _ = 2 * (b - 1) := by rw [Nat.two_mul]
      _ ≤ a * (b - 1) := Nat.mul_le_mul_right (b - 1) ha
  omega

/-- The numerical hypotheses of the reduction theorem hold for `f k = 4 ^ k`. -/
theorem sup_pow_four {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) : 4 ^ i + 4 ^ j ≤ 4 ^ (i + j) := by
  have h1 : 2 ≤ 4 ^ i := by
    have heq : 4 ^ i = 4 * 4 ^ (i - 1) := by
      calc 4 ^ i = 4 ^ ((i - 1) + 1) := by congr 1; omega
        _ = 4 ^ (i - 1) * 4 := pow_add _ _ _
        _ = 4 * 4 ^ (i - 1) := Nat.mul_comm _ _
    have hone : 1 ≤ 4 ^ (i - 1) := Nat.one_le_pow (i - 1) 4 (by omega)
    have hmul : 4 ≤ 4 * 4 ^ (i - 1) := Nat.mul_le_mul_left 4 hone
    omega
  have h2 : 2 ≤ 4 ^ j := by
    have heq : 4 ^ j = 4 * 4 ^ (j - 1) := by
      calc 4 ^ j = 4 ^ ((j - 1) + 1) := by congr 1; omega
        _ = 4 ^ (j - 1) * 4 := pow_add _ _ _
        _ = 4 * 4 ^ (j - 1) := Nat.mul_comm _ _
    have hone : 1 ≤ 4 ^ (j - 1) := Nat.one_le_pow (j - 1) 4 (by omega)
    have hmul : 4 ≤ 4 * 4 ^ (j - 1) := Nat.mul_le_mul_left 4 hone
    omega
  have h3 := add_le_mul_of_two_le h1 h2
  rw [← pow_add] at h3
  exact h3

theorem step_pow_four {k : ℕ} (hk : 1 ≤ k) : 3 + 4 ^ (k - 1) ≤ 4 ^ k := by
  have h1 : 4 ^ k = 4 * 4 ^ (k - 1) := by
    calc 4 ^ k = 4 ^ ((k - 1) + 1) := by congr 1; omega
      _ = 4 ^ (k - 1) * 4 := pow_add _ _ _
      _ = 4 * 4 ^ (k - 1) := Nat.mul_comm _ _
  have hone : 1 ≤ 4 ^ (k - 1) := Nat.one_le_pow (k - 1) 4 (by omega)
  have h2 : 3 ≤ 3 * 4 ^ (k - 1) := by
    calc 3 = 3 * 1 := by rw [Nat.mul_one]
      _ ≤ 3 * 4 ^ (k - 1) := Nat.mul_le_mul_left 3 hone
  have h3 : 4 * 4 ^ (k - 1) = 3 * 4 ^ (k - 1) + 4 ^ (k - 1) := by
    calc 4 * 4 ^ (k - 1) = (3 + 1) * 4 ^ (k - 1) := by congr 1
      _ = 3 * 4 ^ (k - 1) + 1 * 4 ^ (k - 1) := Nat.add_mul _ _ _
      _ = 3 * 4 ^ (k - 1) + 4 ^ (k - 1) := by rw [Nat.one_mul]
  omega

/-- `2 * ∑ i ∈ s, f i = ∑ i ∈ s, (2 * f i)`. -/
theorem two_mul_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    2 * (∑ i ∈ s, f i) = ∑ i ∈ s, (2 * f i) :=
  Finset.mul_sum s f 2

end Arithmetic

/-! ### Part 1 — the deficiency over an anticomplete cover -/

section Cover

/-- **THE DEFICIENCY OF A VERTEX SET IS THE DEFICIENCY COMPUTED IN THE GRAPH INDUCED BY THE PIECE.** -/
theorem defOf_inter_induceFinset (Y Q : Finset V) :
    defOf (induceFinset G Q) (Y ∩ Q) = defOf G (Y ∩ Q) := by
  have h : indepCard (induceFinset G Q) (Y ∩ Q) = indepCard G (Y ∩ Q) := by
    have h2 := indepCard_induceFinset_inter G Q Y
    rw [Finset.inter_comm] at h2
    exact h2.trans (indepCard_induceFinset G _).symm
  unfold defOf
  rw [h]

/-- Restricting an anticomplete family to a subfamily gives an anticomplete family. -/
theorem AnticoverCoverFamily.sub {Qc : Finset (Finset V)} (h : AnticoverCoverFamily G 𝒬)
    (hsub : Qc ⊆ 𝒬) : AnticoverCoverFamily G Qc :=
  ⟨fun X hX Y hY hne => h.1 X (hsub hX) Y (hsub hY) hne,
    fun X hX Y hY hne => h.2 X (hsub hX) Y (hsub hY) hne⟩

/-- **Two distinct pieces of an anticomplete family are disjoint.** -/
theorem AnticoverCoverFamily.notMem_inter (h : AnticoverCoverFamily G 𝒬) {X Y : Finset V}
    (hX : X ∈ 𝒬) (hY : Y ∈ 𝒬) (hne : X ≠ Y) : (X ∩ Y).Nonempty → False := by
  intro hnm
  obtain ⟨x, hx⟩ := hnm
  have hpos : 0 < (X ∩ Y).card := Finset.card_pos.mpr ⟨x, hx⟩
  rw [h.1 X hX Y hY hne, Finset.card_empty] at hpos
  simp at hpos

theorem AnticoverCoverFamily.disjoint' (h : AnticoverCoverFamily G 𝒬) {X Y : Finset V}
    (hX : X ∈ 𝒬) (hY : Y ∈ 𝒬) (hne : X ≠ Y) {x : V} (hx : x ∈ X) : x ∉ Y := by
  intro hy
  exact h.notMem_inter hX hY hne ⟨x, Finset.mem_inter.mpr ⟨hx, hy⟩⟩

/-- **THE INDEPENDENCE NUMBER OF A UNION IS AT MOST THE SUM OF THE TWO.**  The independent sets of
`A ∪ B` split into an independent subset of `A` and an independent subset of `B`. -/
theorem indepCard_le_add (A B : Finset V) : indepCard G (A ∪ B) ≤ indepCard G A + indepCard G B := by
  refine Finset.sup_le_iff.mpr fun S hS => ?_
  have hSi : G.IsIndepSet (S : Set V) := (Finset.mem_filter.mp hS).2
  have hSsub : S ⊆ A ∪ B := sub_of_mem_indepSets hS
  set S₁ := S ∩ A with hS₁
  set S₂ := S \ A with hS₂
  have h1 : G.IsIndepSet S₁ := by
    rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv hne hadj
    have hu' : u ∈ (S : Set V) :=
      (Finset.mem_inter (s₁ := S) (s₂ := A)).mp (hS₁ ▸ hu) |>.1
    have hv' : v ∈ (S : Set V) :=
      (Finset.mem_inter (s₁ := S) (s₂ := A)).mp (hS₁ ▸ hv) |>.1
    exact hSi hu' hv' hne hadj
  have h2 : G.IsIndepSet S₂ := by
    rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv hne hadj
    have hu' : u ∈ (S : Set V) :=
      (Finset.mem_sdiff (s := S) (t := A)).mp (hS₂ ▸ hu) |>.1
    have hv' : v ∈ (S : Set V) :=
      (Finset.mem_sdiff (s := S) (t := A)).mp (hS₂ ▸ hv) |>.1
    exact hSi hu' hv' hne hadj
  have h3 : S₁.card ≤ indepCard G A := le_indepCard_of_isIndepSet (by
    intro u hu
    exact (Finset.mem_inter (s₁ := S) (s₂ := A)).mp (hS₁ ▸ hu) |>.2) h1
  have h4 : S₂.card ≤ indepCard G B := le_indepCard_of_isIndepSet (by
    intro u hu
    have hu' : u ∈ S \ A := hS₂ ▸ hu
    have huS : u ∈ S := (Finset.mem_sdiff (s := S) (t := A)).mp hu' |>.1
    have hmem : u ∈ A ∪ B := hSsub huS
    rcases Finset.mem_union.mp hmem with hA | hB
    · have hnA : u ∉ A := (Finset.mem_sdiff (s := S) (t := A)).mp hu' |>.2
      exact absurd hA hnA
    · exact hB) h2
  have hx : S₁.card + S₂.card = S.card := by
    rw [hS₁, hS₂]
    exact card_inter_add_card_sdiff S A
  omega

/-- **THE CARDINALITIES OF THE PARTS OF A COVER ADD UP TO AT MOST THE CARDINALITY OF THE WHOLE.** -/
theorem sum_card_inter_le_card (h : AnticoverCoverFamily G 𝒬) {Y : Finset V}
    (hY : ∀ x : V, x ∈ Y → ∃ Q ∈ 𝒬, x ∈ Q) : (∑ Q ∈ 𝒬, (Y ∩ Q).card) ≤ Y.card := by
  have hd : (↑𝒬 : Set (Finset V)).PairwiseDisjoint (fun Q => Y ∩ Q) := by
    intro Q hQ R hR hne
    refine Finset.disjoint_left.mpr fun z hz => ?_
    intro hz2
    exact AnticoverCoverFamily.disjoint' h hQ hR hne (Finset.mem_inter.mp hz).2
      (Finset.mem_inter.mp hz2).2
  have hexact : (𝒬.biUnion (fun Q : Finset V => Y ∩ Q)).card = ∑ Q ∈ 𝒬, (Y ∩ Q).card :=
    Finset.card_biUnion hd
  have hEq : Y = 𝒬.biUnion (fun Q : Finset V => Y ∩ Q) := by
    ext x
    simp only [Finset.mem_biUnion]
    constructor
    · intro hx
      obtain ⟨Q, hQ, hxQ⟩ := hY x hx
      exact ⟨Q, hQ, Finset.mem_inter.mpr ⟨hx, hxQ⟩⟩
    · rintro ⟨Q, hQ, hx⟩
      exact (Finset.mem_inter.mp hx).1
  have hcard : Y.card = (∑ Q ∈ 𝒬, (Y ∩ Q).card) := by
    calc Y.card = (𝒬.biUnion (fun Q : Finset V => Y ∩ Q)).card := congrArg Finset.card hEq
      _ = ∑ Q ∈ 𝒬, (Y ∩ Q).card := hexact
  exact hcard.symm.le

end Cover

end
