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

/-- **Membership in `s \ (t ∪ u)`, read off in the two ways.**  The `.2.2` projections of
`Finset.mem_sdiff` do not elaborate in this Mathlib revision (the `¬` on the right of the pair is a
function, not an `And`), so the two facts are named once and for all here. -/
theorem mem_sdiff_union (s t u : Finset V) : s \ (t ∪ u) = (s \ t) \ u := by
  ext x
  constructor
  · intro hx
    have hxs : x ∈ s := (Finset.mem_sdiff.mp hx).1
    have hnxtu : x ∉ t ∪ u := (Finset.mem_sdiff.mp hx).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨hxs, ?_⟩, ?_⟩
    · intro hxt
      exact hnxtu (Finset.mem_union.mpr (Or.inl hxt))
    · intro hxu
      exact hnxtu (Finset.mem_union.mpr (Or.inr hxu))
  · intro hx
    have hst : x ∈ s \ t := (Finset.mem_sdiff.mp hx).1
    have hnxt : x ∉ t := (Finset.mem_sdiff.mp hst).2
    have hnxtu : x ∉ u := (Finset.mem_sdiff.mp hx).2
    have hxs : x ∈ s := (Finset.mem_sdiff.mp hst).1
    apply Finset.mem_sdiff.mpr
    refine ⟨hxs, ?_⟩
    intro hxtu
    rcases Finset.mem_union.mp hxtu with hxt | hxu
    · exact hnxt hxt
    · exact hnxtu hxu

theorem sdiff_union_swap (s t u : Finset V) :
    s \ (t ∪ u) = (s \ u) \ t := by
  ext x
  constructor
  · intro hx
    have hxs : x ∈ s := (Finset.mem_sdiff.mp hx).1
    have hnxtu : x ∉ t ∪ u := (Finset.mem_sdiff.mp hx).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨hxs, ?_⟩, ?_⟩
    · intro hxu
      exact hnxtu (Finset.mem_union.mpr (Or.inr hxu))
    · intro hxt
      exact hnxtu (Finset.mem_union.mpr (Or.inl hxt))
  · intro hx
    have hsut : x ∈ s \ u := (Finset.mem_sdiff.mp hx).1
    have hnu : x ∉ u := (Finset.mem_sdiff.mp hsut).2
    have hnt : x ∉ t := (Finset.mem_sdiff.mp hx).2
    have hs : x ∈ s := (Finset.mem_sdiff.mp hsut).1
    apply Finset.mem_sdiff.mpr
    refine ⟨hs, ?_⟩
    intro hxtu
    rcases Finset.mem_union.mp hxtu with hxt' | hxu
    · exact hnt hxt'
    · exact hnu hxu

/-- **Cutting twice at the same set.**  If `t` is disjoint from `u`, then
`(t ∪ u) \ (t ∪ w) = u \ w`: the vertices lost are exactly the vertices of `w` inside `u`. -/
theorem sdiff_sdiff_union (t u w : Finset V) (h : Disjoint t u) :
    (t ∪ u) \ (t ∪ w) = u \ w := by
  have htu : ∀ x : V, x ∈ t → x ∉ u := Finset.disjoint_left.mp h
  ext x
  constructor
  · intro hx
    have hxTU := (Finset.mem_sdiff.mp hx).1
    have hxnTW := (Finset.mem_sdiff.mp hx).2
    have hxnT : x ∉ t := fun hxT => hxnTW (Finset.mem_union.mpr (Or.inl hxT))
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · rcases Finset.mem_union.mp hxTU with hxT | hxU
      · exact absurd hxT hxnT
      · exact hxU
    · intro hxW
      exact hxnTW (Finset.mem_union.mpr (Or.inr hxW))
  · intro hx
    have hxU := (Finset.mem_sdiff.mp hx).1
    have hxW := (Finset.mem_sdiff.mp hx).2
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr (Or.inr hxU), ?_⟩
    intro hxnTW
    rcases Finset.mem_union.mp hxnTW with hxT | hxW'
    · exact htu x hxT hxU
    · exact hxW hxW'

theorem mem_sdiff_union_left {s t u : Finset V} {x : V} (hx : x ∈ s \ (t ∪ u)) :
    x ∈ s ∧ x ∉ t := by
  refine And.intro (Finset.mem_sdiff.mp hx).1 ?_
  intro hxT
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union.mpr (Or.inl hxT))

theorem mem_sdiff_union_right {s t u : Finset V} {x : V} (hx : x ∈ s \ (t ∪ u)) : x ∉ u := by
  intro hxU
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union.mpr (Or.inr hxU))

theorem mem_sdiff_union_both {s t u : Finset V} {x : V} (hx : x ∈ s \ (t ∪ u)) : x ∉ t ∧ x ∉ u := by
  refine And.intro ?_ (mem_sdiff_union_right hx)
  intro hxT
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union.mpr (Or.inl hxT))

/-! ### Part 2 — the independence number splits over a *family* of pieces -/

section Family

/-- **The truncated subtraction is monotone in the right places.**  This is the single arithmetic
step used below; `omega` of this build does not do it. -/
theorem sub_sub_le_sub_sub {p p' q q' : ℕ} (hp : p ≤ p') (hq : q' ≤ q) :
    p - q ≤ p' - q' :=
  Nat.sub_le_sub_right hp q |>.trans (Nat.sub_le_sub_left hq p')

/-- **`x ∈ s` and `x ∈ s \ t` imply `x ∉ t`** — the shape used to read a hypothesis about `s`
into one about `s \ t`. -/
theorem notMem_of_mem_sdiff {s t : Finset V} {x : V} (h1 : x ∈ s) (h2 : x ∈ s \ t) : x ∉ t := by
  intro hxt
  exact (Finset.mem_sdiff.mp h2).2 hxt

/-- **`(s \ t) \ u = s \ (t ∪ u)`**. -/
theorem sdiff_sdiff_eq (s t u : Finset V) : (s \ t) \ u = s \ (t ∪ u) := by
  ext x
  constructor
  · intro hx
    have hst : x ∈ s \ t := (Finset.mem_sdiff.mp hx).1
    have hnu : x ∉ u := (Finset.mem_sdiff.mp hx).2
    have hs : x ∈ s := by
      have : x ∈ s := (Finset.mem_sdiff.mp hst).1
      exact this
    refine Finset.mem_sdiff.mpr ⟨hs, ?_⟩
    intro hxTU
    rcases Finset.mem_union.mp hxTU with hxt | hxu
    · exact (Finset.mem_sdiff.mp hst).2 hxt
    · exact hnu hxu
  · intro hx
    have hs : x ∈ s := (Finset.mem_sdiff.mp hx).1
    have hntu : x ∉ t ∪ u := (Finset.mem_sdiff.mp hx).2
    have hnu : x ∉ u := by
      intro hxu
      exact hntu (Finset.mem_union.mpr (Or.inr hxu))
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · refine Finset.mem_sdiff.mpr ⟨hs, ?_⟩
      intro hxt
      exact hntu (Finset.mem_union.mpr (Or.inl hxt))
    · exact hnu

/-- **The right side of a difference is monotone**: if `u ⊆ t` then `x ∉ t` implies `x ∉ u`. -/
theorem notMem_of_subset {t u : Finset V} {x : V} (h : u ⊆ t) (hx : x ∉ t) : x ∉ u := by
  intro hxu
  exact hx (h hxu)

theorem mem_union_left' (a b : Finset V) {x : V} (h : x ∈ a) : x ∈ a ∪ b := by
  show x ∈ a ∪ b
  rw [Finset.mem_union]
  exact Or.inl h

theorem mem_union_right' (a b : Finset V) {x : V} (h : x ∈ b) : x ∈ a ∪ b := by
  show x ∈ a ∪ b
  rw [Finset.mem_union]
  exact Or.inr h

/-- **THE INDEPENDENCE NUMBER OF A COVERED VERTEX SET SPLITS OVER THE FAMILY.**

For a family of pieces which is pairwise disjoint and pairwise anticomplete and which covers `X`,

```lean
indepCard G X ≤ ∑ Q ∈ 𝒬, indepCard G (X ∩ Q)
```

This is the family version of `indepCard_le_add` (the two-set case), proved by induction on the
family with `indepCard_le_add` as the merge step: the induction hypothesis is applied to
`X \ Q`, which the rest of the family still covers because the pieces are disjoint. -/
theorem indepCard_le_sum_inter : ∀ (𝒬 : Finset (Finset V)) (h : AnticoverCoverFamily G 𝒬)
    (X : Finset V), (∀ x : V, x ∈ X → ∃ Q ∈ 𝒬, x ∈ Q) →
    indepCard G X ≤ ∑ Q ∈ 𝒬, indepCard G (X ∩ Q) := by
  intro 𝒬
  induction 𝒬 using Finset.induction_on with
  | empty =>
      intro h X hX
      have hXempty : X = ∅ := by
        ext x
        constructor
        · intro hx
          obtain ⟨Q, hQ, hxQ⟩ := hX x hx
          exact absurd hQ (by simp)
        · intro hx
          exact absurd hx (by simp)
      rw [hXempty, indepCard_empty]
      simp
  | @insert Q t hQ ih =>
      intro h X hX
      have hsub : AnticoverCoverFamily G t := h.sub (Finset.subset_insert Q t)
      have hX' : ∀ x : V, x ∈ X \ Q → ∃ P ∈ t, x ∈ P := by
        intro x hx
        obtain ⟨P, hP, hxP⟩ := hX x (Finset.mem_sdiff.mp hx).1
        rcases Finset.mem_insert.mp hP with rfl | hP'
        · exact absurd hxP (Finset.mem_sdiff.mp hx).2
        · exact ⟨P, hP', hxP⟩
      have h1 := ih hsub (X \ Q) hX'
      have hle : indepCard G (X \ Q) ≤ ∑ P ∈ t, indepCard G (X ∩ P) :=
        h1.trans (Finset.sum_le_sum fun P hP => indepCard_le_of_subset (fun z hz => by
          rcases Finset.mem_inter.mp hz with ⟨hz1, hz2⟩
          exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hz1).1, hz2⟩))
      have h3 : indepCard G X ≤ indepCard G (X ∩ Q) + indepCard G (X \ Q) := by
        have heq : X = (X ∩ Q) ∪ (X \ Q) :=
          ((Finset.union_comm _ _).symm.trans (Finset.sdiff_union_inter X Q)).symm
        calc indepCard G X = indepCard G ((X ∩ Q) ∪ (X \ Q)) := congrArg (indepCard G) heq
          _ ≤ indepCard G (X ∩ Q) + indepCard G (X \ Q) := indepCard_le_add _ _
      rw [Finset.sum_insert hQ]
      omega

end Family

/-! ### Part 3 — the deficiency drops by one at a triangle -/

section Triangle

/-- **The independence number of a nonempty clique is `1`.** -/
theorem indepCard_eq_one_of_clique {T : Finset V} (hT : T.Nonempty) (hcl : G.IsClique T) :
    indepCard G T = 1 := by
  refine le_antisymm ?_ (Nat.succ_le_of_lt (indepCard_pos hT))
  show (indepSets G T).sup Finset.card ≤ 1
  refine Finset.sup_le_iff.mpr fun S hS =>
    indep_card_le_one_of_clique hcl (Finset.mem_filter.mp hS).2 (sub_of_mem_indepSets hS)

/-- **A `3`-clique has deficiency `1`** — the smallest positive value of `defOf`. -/
theorem defOf_eq_one_of_clique_card_three {T : Finset V} (hT : T.Nonempty) (hcl : G.IsClique T)
    (hcard : T.card = 3) : defOf G T = 1 := by
  have hα : indepCard G T = 1 := indepCard_eq_one_of_clique hT hcl
  show T.card - 2 * indepCard G T = 1
  have h1 : T.card - 2 * indepCard G T = 3 - 2 * 1 := by rw [hcard, hα]
  omega

/-- **THE DEFICIENCY DROPS BY ONE WHEN A `3`-CLIQUE IS ADDED.**  If `T` is a `3`-clique disjoint from
`Y`, then `defOf G (Y ∪ T) ≥ defOf G Y + 1`, provided no truncation occurs on `Y`
(`2 α(G[Y]) ≤ |Y|`, which is automatic as soon as the deficiency of `Y` is positive).

The proof is combinatorial: `|Y ∪ T| = |Y| + 3` and
`α(G[Y ∪ T]) ≤ α(G[Y]) + α(G[T]) = α(G[Y]) + 1`, because a `3`-clique carries an independent set
of size `1`. -/
theorem defOf_ge_add_one_defOf_of_add_clique {T Y : Finset V} (hcl : G.IsClique T)
    (hT : T.Nonempty) (hdisj : Disjoint Y T) (hcard : T.card = 3)
    (hnt : 2 * indepCard G Y ≤ Y.card) :
    defOf G Y + 1 ≤ defOf G (Y ∪ T) := by
  have hαT : indepCard G T = 1 := indepCard_eq_one_of_clique hT hcl
  have hdisj' : ∀ ⦃x : V⦄, x ∈ Y → x ∈ T → False := Finset.disjoint_left.mp hdisj
  have hcardU : (Y ∪ T).card = Y.card + 3 := by
    have hd : Disjoint T Y := Finset.disjoint_left.mpr fun _ hxT hxY => hdisj' hxY hxT
    calc (Y ∪ T).card = (T ∪ Y).card := by rw [Finset.union_comm]
      _ = T.card + Y.card := Finset.card_union_of_disjoint hd
      _ = Y.card + 3 := by rw [hcard, Nat.add_comm]
  have hα : 2 * indepCard G (Y ∪ T) ≤ 2 * indepCard G Y + 2 := by
    have h := Nat.mul_le_mul_left 2 (indepCard_le_add (G := G) Y T)
    rw [Nat.mul_add, hαT, Nat.mul_one] at h
    exact h
  have h2 : Y.card + 3 - (2 * indepCard G Y + 2) = (Y.card + 1) - 2 * indepCard G Y := by
    calc Y.card + 3 - (2 * indepCard G Y + 2)
        = ((Y.card + 1) + 2) - (2 * indepCard G Y + 2) := by omega
      _ = (Y.card + 1) - 2 * indepCard G Y := Nat.add_sub_add_right _ _ _
  have h3 : (Y.card + 1) - 2 * indepCard G Y = defOf G Y + 1 := by
    show Y.card.succ - 2 * indepCard G Y = (Y.card - 2 * indepCard G Y) + 1
    exact Nat.succ_sub hnt
  have hcardU' : Y.card + 3 ≤ (Y ∪ T).card := by rw [hcardU]
  have hle : (Y.card + 1) - 2 * indepCard G Y ≤ (Y ∪ T).card - 2 * indepCard G (Y ∪ T) := by
    have h1 := sub_sub_le_sub_sub hcardU' hα
    rw [h2] at h1
    exact h1
  calc defOf G Y + 1 = (Y.card + 1) - 2 * indepCard G Y := h3.symm
    _ ≤ (Y ∪ T).card - 2 * indepCard G (Y ∪ T) := hle

/-! ### Part 3b — the maximum deficiency *inside* a vertex set -/

section MaxDefIn

/-- **`MaxDefIn G U`**, the maximum deficiency `|Y| - 2 α(G[Y])` over the vertex sets `Y ⊆ U`.

`MaxDef G` is `MaxDefIn G univ`, and `MaxDefIn` is the quantity an induction on Erdős's parameter
needs: it is the deficiency of a vertex set of a graph, measured in the whole graph. -/
noncomputable def maxDefIn (G : SimpleGraph V) (U : Finset V) : ℕ := (U.powerset).sup (defOf G)

/-- A vertex set of deficiency at most `maxDefIn G U` lies in `U`. -/
theorem le_maxDefIn (G : SimpleGraph V) (U : Finset V) {Y : Finset V} (hYU : Y ⊆ U) :
    defOf G Y ≤ maxDefIn G U :=
  Finset.le_sup (Finset.mem_powerset.mpr hYU)

/-- **`maxDefIn G U` is attained by a vertex set of `U`.** -/
theorem exists_eq_maxDefIn (G : SimpleGraph V) (U : Finset V) :
    ∃ Y : Finset V, Y ⊆ U ∧ defOf G Y = maxDefIn G U := by
  by_cases hpos : 0 < maxDefIn G U
  · have hmax : ∃ Y ∈ U.powerset, maxDefIn G U ≤ defOf G Y :=
      (Finset.le_sup_iff (s := U.powerset) (f := defOf G) (a := maxDefIn G U) hpos).mp
        (Nat.le_refl _)
    obtain ⟨Y, hY, hle⟩ := hmax
    exact ⟨Y, Finset.mem_powerset.mp hY, le_antisymm (le_maxDefIn G U (Finset.mem_powerset.mp hY))
      hle⟩
  · refine ⟨∅, Finset.empty_subset _, le_antisymm (le_maxDefIn G U (Finset.empty_subset _)) ?_⟩
    have h0 : maxDefIn G U = 0 := by omega
    rw [h0]
    exact Nat.zero_le _

/-- `maxDefIn` is monotone in the vertex set. -/
theorem maxDefIn_mono (G : SimpleGraph V) {U U' : Finset V} (hUU' : U ⊆ U') :
    maxDefIn G U ≤ maxDefIn G U' := by
  show (U.powerset).sup (defOf G) ≤ (U'.powerset).sup (defOf G)
  refine Finset.sup_le_iff.mpr fun Y hY => ?_
  have hYU' : Y ∈ U'.powerset := by
    apply Finset.mem_powerset.mpr
    show Y ⊆ U'
    intro x hx
    exact hUU' (Finset.mem_powerset.mp hY hx)
  exact Finset.le_sup hYU'

/-- The deficiency of a vertex set of `U` is the same in `G` and in `G[U]`. -/
theorem defOf_induceFinset_of_subset {Y : Finset V} (hYU : Y ⊆ U) :
    defOf (induceFinset G U) Y = defOf G Y := by
  have heq : Y ∩ U = Y := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_inter.mp hx).1
    · intro hx
      exact Finset.mem_inter.mpr ⟨hx, hYU hx⟩
  rw [← heq]
  exact defOf_inter_induceFinset (Y := Y) (Q := U)

theorem maxDefIn_induceFinset_eq (G : SimpleGraph V) (U : Finset V) :
    maxDefIn (induceFinset G U) U = maxDefIn G U := by
  refine le_antisymm ?_ ?_
  · show (U.powerset).sup (defOf (induceFinset G U)) ≤ (U.powerset).sup (defOf G)
    refine Finset.sup_le_iff.mpr fun Y hY => ?_
    have hYU : Y ⊆ U := Finset.mem_powerset.mp hY
    rw [defOf_induceFinset_of_subset hYU]
    exact Finset.le_sup hY
  · show (U.powerset).sup (defOf G) ≤ (U.powerset).sup (defOf (induceFinset G U))
    refine Finset.sup_le_iff.mpr fun Y hY => ?_
    have hYU : Y ⊆ U := Finset.mem_powerset.mp hY
    rw [← defOf_induceFinset_of_subset hYU]
    exact Finset.le_sup hY

/-- **THE MAXIMUM DEFICIENCY INSIDE `U` DROPS BY ONE AT A `3`-CLIQUE.**  If `T` is a `3`-clique
disjoint from `U`, then

```lean
1 + maxDefIn G U ≤ maxDefIn G (U ∪ T)
```

This is *the* step that makes an induction on `k` in Erdős's hypothesis close: cutting the graph
at a triangle costs exactly one unit of deficiency, whatever the size of `U`. -/
theorem maxDefIn_ge_one_add_maxDefIn_of_clique {T U : Finset V} (hcl : G.IsClique T)
    (hcard : T.card = 3) (hdisj : Disjoint U T) :
    1 + maxDefIn G U ≤ maxDefIn G (U ∪ T) := by
  have hT : T.Nonempty := by
    by_contra hc
    have hcard0 : T.card = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hc, Finset.card_empty]
    omega
  have hdisj' : ∀ ⦃x : V⦄, x ∈ U → x ∈ T → False := Finset.disjoint_left.mp hdisj
  obtain ⟨Y, hYU, hY⟩ := exists_eq_maxDefIn G U
  have hYT : Y ⊆ U ∪ T := fun z hz => Finset.mem_union.mpr (Or.inl (hYU hz))
  by_cases hz : maxDefIn G U = 0
  · rw [hz]
    have hsubT : T ⊆ U ∪ T := fun z hz => Finset.mem_union.mpr (Or.inr hz)
    exact le_trans (show (1 : ℕ) ≤ defOf G T from
        (defOf_eq_one_of_clique_card_three hT hcl hcard).ge)
      (le_maxDefIn G (U ∪ T) hsubT)
  · have hnt : 2 * indepCard G Y ≤ Y.card := by
      have hpos : 0 < Y.card - 2 * indepCard G Y := by
        have h' : Y.card - 2 * indepCard G Y = maxDefIn G U := hY
        omega
      rw [Nat.sub_pos_iff_lt] at hpos
      omega
    have h1 : defOf G Y + 1 ≤ defOf G (Y ∪ T) :=
      defOf_ge_add_one_defOf_of_add_clique hcl hT
        (Finset.disjoint_left.mpr fun z hzY hzT => hdisj' (hYU hzY) hzT) hcard hnt
    calc 1 + maxDefIn G U = 1 + defOf G Y := by rw [hY]
      _ ≤ defOf G (Y ∪ T) := by omega
      _ ≤ maxDefIn G (U ∪ T) := by
        apply le_maxDefIn G (U ∪ T)
        intro z hz
        rcases Finset.mem_union.mp hz with h1 | h2
        · exact Finset.mem_union.mpr (Or.inl (hYU h1))
        · exact Finset.mem_union.mpr (Or.inr h2)

end MaxDefIn

/-- The corner of the triangle descent that the reduction uses: if `T` is a `3`-clique of `G`, `U` is
disjoint from it and `U ⊆ W`, then the deficiency inside `U` is at most the deficiency inside `W`
minus one. -/
theorem maxDefIn_ge_one_add_maxDefIn_of_clique_sub {T U W : Finset V} (hcl : G.IsClique T)
    (hcard : T.card = 3) (hdisj : Disjoint U T) (hUW : U ⊆ W) (hTW : T ⊆ W) :
    1 + maxDefIn G U ≤ maxDefIn G W := by
  have hUW' : U ∪ T ⊆ W := by
    intro z hz
    rcases Finset.mem_union.mp hz with h1 | h2
    · exact hUW h1
    · exact hTW h2
  exact le_trans (maxDefIn_ge_one_add_maxDefIn_of_clique hcl hcard hdisj) (maxDefIn_mono G hUW')

end Triangle

/-! ### Part 4 — a cut of `G` at a triangle, and the reduction to triangle-free graphs -/

section TriangleCut

/-- **A CUT OF `G` AT A SET `T`.**  The pieces `𝒬` are pairwise disjoint and pairwise anticomplete;
each of them is disjoint from `T` and anticomplete to it; and together they cover `V \ T`.

This is the shape of the *connected components of `G − T`*, provided `T` separates: no edge joins
`T` to the pieces.  The four fields are, in order: `AnticoverCoverFamily G 𝒬`, the disjointness of
the pieces from `T`, the anticompleteness of `T` to the pieces, and the covering of `V \ T`. -/
def AnticoverCut (G : SimpleGraph V) (T : Finset V) (𝒬 : Finset (Finset V)) : Prop :=
  AnticoverCoverFamily G 𝒬 ∧ (∀ Q ∈ 𝒬, Disjoint Q T) ∧
    (∀ Q ∈ 𝒬, ∀ x ∈ T, ∀ y ∈ Q, ¬ G.Adj x y) ∧
    (∀ x : V, x ∉ T → ∃ Q ∈ 𝒬, x ∈ Q)

/-- **THE PIECES OF A CUT ARE ANTICOMPLETE TO `T`.** -/
theorem AnticoverCut.anticomplete_to_T (h : AnticoverCut G T 𝒬) {Q : Finset V} (hQ : Q ∈ 𝒬)
    {x : V} (hxT : x ∈ T) {y : V} (hyQ : y ∈ Q) : ¬ G.Adj x y :=
  h.2.2.1 Q hQ x hxT y hyQ

/-- **NEW INSTANCE OF THE HEADLINE THEOREM, OVER A CUT AT A `3`-CLIQUE.**

Suppose `T` is a triangle and the vertices of `V \ T` split anticompletely into pieces `𝒬`, each
disjoint from `T`, anticomplete to it, and `m`-close to bipartite.  Then

```lean
LocIndep k G → CloseToBipartite (3 + k * m) G
```

The constant is **independent of the number of pieces**: at most `k` of them are non-bipartite, by
`card_nonBipartiteParts_le_cover`, and the rest cost nothing.  No bound is assumed on the odd
girth, on the packing weight, or on the number of branch vertices. -/
theorem closeToBipartite_of_anticoverCut {k m : ℕ} (hG : LocIndep k G) (T : Finset V)
    (𝒬 : Finset (Finset V)) (h : AnticoverCut G T 𝒬) (hcard : T.card = 3)
    (hm : ∀ Q ∈ 𝒬, CloseToBipartite m (induceFinset G Q))
    [DecidablePred fun X => ¬ (induceFinset G X).IsBipartite] :
    CloseToBipartite (3 + k * m) G := by
  classical
  set N : Finset (Finset V) := 𝒬.filter (fun X => ¬ (induceFinset G X).IsBipartite) with hNdef
  have hcard'' : N.card ≤ k := by
    rw [hNdef]
    exact card_nonBipartiteParts_le_cover hG h.1
  have hdis' : ∀ X ∈ N, ∀ Y ∈ N, X ≠ Y → X ∩ Y = ∅ := by
    intro X hX Y hY hne
    exact h.1.1 X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hne
  have hedge' : ∀ X ∈ N, ∀ Y ∈ N, X ≠ Y → ∀ (x : V), x ∈ X → ∀ (y : V), y ∈ Y → ¬ G.Adj x y := by
    intro X hX Y hY hne x hx y hy
    exact h.1.2 X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hne x hx y hy
  have hfam : AnticoverFamily G N :=
    ⟨hdis', hedge',
      fun X hX => by
        have hnb : ¬ (induceFinset G X).IsBipartite := (Finset.mem_filter.mp hX).2
        have hex2 : ∃ C, IsOddCycle (induceFinset G X) C := by
          by_contra hcon2
          exact hnb (isBipartite_of_no_oddCycle hcon2)
        obtain ⟨C, hC⟩ := hex2
        exact ⟨C, hC.of_induceFinset, isOddCycle_sub_induceFinset hC⟩⟩
  have hm' : ∀ (X : Finset V), X ∈ N → CloseToBipartite m (induceFinset G X) := by
    intro X hX
    exact hm X (Finset.mem_filter.mp hX).1
  have h1 := closeToBipartite_of_anticoverFamily_cost (c := fun _ => m) hfam hm'
  obtain ⟨X₁, hX₁card, hX₁b⟩ := h1
  have hsum : (∑ X ∈ N, m) ≤ m * N.card := by
    have h : (∑ X ∈ N, m) = N.card * m := by simp
    rw [h, Nat.mul_comm]
  have hX₁bound : X₁.card ≤ m * k := by
    have h1' : X₁.card ≤ m * N.card := le_trans hX₁card hsum
    have h2 : m * N.card ≤ m * k := Nat.mul_le_mul_left m hcard''
    omega
  set NN : Finset V := N.biUnion (id : Finset V → Finset V) with hNN
  set Z : Finset V := X₁ ∩ NN with hZdef
  have hZsub : Z ⊆ NN := by
    show X₁ ∩ NN ⊆ NN
    exact Finset.inter_subset_right
  have hZcard : Z.card ≤ m * k := by
    have h1 : Z.card ≤ X₁.card := by
      show (X₁ ∩ NN).card ≤ X₁.card
      exact Finset.card_le_card (Finset.inter_subset_left : X₁ ∩ NN ⊆ X₁)
    exact le_trans h1 hX₁bound
  have hNbip : (induceFinset G (NN \ Z)).IsBipartite := by
    have heq : NN \ Z = NN \ X₁ := by
      ext x
      simp only [Finset.mem_sdiff, hNN, hZdef, Finset.mem_inter]
      tauto
    rw [heq, ← deleteFinset_induceFinset]
    exact hX₁b
  have hB : (induceFinset G ((Finset.univ : Finset V) \ (T ∪ NN))).IsBipartite := by
    refine isBipartite_of_no_oddCycle ?_
    rintro ⟨C, hC⟩
    have hC' : IsOddCycle G C := hC.of_induceFinset
    have hCsub : C ⊆ (Finset.univ : Finset V) \ (T ∪ NN) :=
      isOddCycle_sub_induceFinset (s := (Finset.univ : Finset V) \ (T ∪ NN)) hC
    have hxcov : ∀ x : V, x ∈ (Finset.univ : Finset V) \ (T ∪ NN) → ∃ Q ∈ 𝒬, x ∈ Q := by
      intro x hx
      have hh := Finset.mem_sdiff.mp hx
      have hxT : x ∉ T := fun hxT => hh.2 (mem_union_left' T NN hxT)
      exact h.2.2.2 x hxT
    obtain ⟨X, hX, hCX⟩ := isOddCycle_sub_anticoverCover
      ((Finset.univ : Finset V) \ (T ∪ NN)) h.1 hxcov hC' hCsub
    have hCX' : IsOddCycle (induceFinset G X) C := hC'.induceFinset (s := X) hCX
    by_cases hXbip : (induceFinset G X).IsBipartite
    · exact absurd ⟨C, hCX'⟩ (JSP90.not_isOddCycle_of_isBipartite hXbip)
    · have hXU : X ⊆ NN := by
        show X ⊆ N.biUnion (id : Finset V → Finset V)
        exact fun x hx => Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, hXbip⟩, hx⟩
      have h3 := isOddCycle_card_ge_three hCX'
      have hpos : 0 < C.card := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      exact False.elim ((Finset.mem_sdiff.mp (hCsub hx)).2
        (mem_union_right' T NN (hXU (hCX hx))))
  have hA : CloseToBipartite (3 + k * m) (induceFinset G (T ∪ NN)) := by
    refine ⟨T ∪ Z, ?_, ?_⟩
    · have h1 : (T ∪ Z).card ≤ T.card + Z.card := Finset.card_union_le _ _
      have h2 : T.card + Z.card ≤ 3 + k * m := by
        rw [hcard]
        have h3 : m * k ≤ k * m := Nat.le_of_eq (Nat.mul_comm m k)
        omega
      omega
    · have hdel : deleteFinset (induceFinset G (T ∪ NN)) (T ∪ Z)
          = induceFinset G ((T ∪ NN) \ (T ∪ Z)) := deleteFinset_induceFinset _ _
      rw [hdel]
      have hsub : (T ∪ NN) \ (T ∪ Z) ⊆ NN \ Z := by
        intro x hx
        have hh := Finset.mem_sdiff.mp hx
        refine Finset.mem_sdiff.mpr ⟨?_, fun hx' => hh.2 (mem_union_right' T Z hx')⟩
        rcases Finset.mem_union.mp hh.1 with hxT | hxN
        · exact absurd hxT (fun h => hh.2 (mem_union_left' T Z h))
        · exact hxN
      exact isBipartite_induceFinset_of_isBipartite hNbip hsub
  have hAB : Anticover G (T ∪ NN) ((Finset.univ : Finset V) \ (T ∪ NN)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hxA hxB
      exact absurd hxA (Finset.mem_sdiff.mp hxB).2
    · ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    · intro v hvA w hwB hv
      have hwBnot : ¬ w ∈ T ∪ NN := fun h => (Finset.mem_sdiff.mp hwB).2 h
      rcases Finset.mem_union.mp hvA with hvT | hvN
      · obtain ⟨Q, hQ, hwQ⟩ := h.2.2.2 w (fun h => hwBnot (mem_union_left' T NN h))
        exact h.2.2.1 Q hQ v hvT w hwQ hv
      · obtain ⟨X, hXin, hvX⟩ := Finset.mem_biUnion.mp hvN
        have hXsub : X ⊆ NN := by
          show X ⊆ N.biUnion (id : Finset V → Finset V)
          exact fun x hx => Finset.mem_biUnion.mpr ⟨X, hXin, hx⟩
        obtain ⟨Y, hYin, hwY⟩ := h.2.2.2 w (fun h => hwBnot (mem_union_left' T NN h))
        have hne : X ≠ Y := by
          intro hXY
          have hthis : w ∈ NN := hXsub (hXY ▸ hwY)
          exact False.elim (hwBnot (mem_union_right' T NN hthis))
        exact h.1.2 X (Finset.mem_filter.mp hXin).1 Y hYin hne v hvX w hwY hv
  have hB0 : CloseToBipartite 0 (induceFinset G ((Finset.univ : Finset V) \ (T ∪ NN))) :=
    closeToBipartite_zero_of_isBipartite hB
  have hfin := closeToBipartite_of_anticover hAB hA hB0
  rwa [Nat.add_zero] at hfin

/-- **A `CloseToBipartite` BOUND READ ON A SUBGRAPH.**  If `G` is `m`-close to bipartite then so
is `G[U]`, for every vertex set `U`, with the *same* constant.  This is the bridge that lets the
whole-graph instance below be read on a vertex set, which is the form the triangle descent needs:
the whole content of the problem sits in some `U ⊆ V`.

The witness is `Y ∩ U` where `Y` is the witness for `G`; the key identity is
`U \ (Y ∩ U) = U \ Y`, so the residue of the subgraph is the residue of the whole graph intersected
with `U`, hence an induced subgraph of a bipartite graph. -/
theorem closeToBipartite_sub_induceFinset {m : ℕ} (h : CloseToBipartite m G) (U : Finset V) :
    CloseToBipartite m (induceFinset G U) := by
  obtain ⟨Y, hY, hYb⟩ := h
  have hYb' : (induceFinset G ((Finset.univ : Finset V) \ Y)).IsBipartite := by
    have hdel : deleteFinset (induceFinset G (Finset.univ : Finset V)) Y
        = induceFinset G ((Finset.univ : Finset V) \ Y) := deleteFinset_induceFinset _ _
    rw [induceFinset_univ] at hdel
    rw [← hdel]
    exact hYb
  refine ⟨Y ∩ U, ?_, ?_⟩
  · exact le_trans (Finset.card_le_card (Finset.inter_subset_left : Y ∩ U ⊆ Y)) hY
  · have hdel : deleteFinset (induceFinset G U) (Y ∩ U)
        = induceFinset G (U \ (Y ∩ U)) := deleteFinset_induceFinset _ _
    rw [hdel]
    have heq : U \ (Y ∩ U) = U \ Y := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [heq]
    refine isBipartite_induceFinset_of_isBipartite hYb' ?_
    intro x hx
    have hh := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hh.2⟩

/-- **THE CUT INSTANCE, READ ON A VERTEX SET.**  With the hypotheses of
`closeToBipartite_of_anticoverCut` — the whole content of the problem sits in some `U ⊆ V` — the
same bound, with the same constant `3 + k * m`, holds for `G[U]`.  This is the form in which the
induction of the reduction to triangle-free graphs consumes the instance. -/
theorem closeToBipartite_of_anticoverCut_on {k m : ℕ} (hG : LocIndep k G) (T : Finset V)
    (𝒬 : Finset (Finset V)) (h : AnticoverCut G T 𝒬) (hcard : T.card = 3)
    (hm : ∀ Q ∈ 𝒬, CloseToBipartite m (induceFinset G Q)) (U : Finset V)
    [DecidablePred fun X => ¬ (induceFinset G X).IsBipartite] :
    CloseToBipartite (3 + k * m) (induceFinset G U) :=
  closeToBipartite_sub_induceFinset (closeToBipartite_of_anticoverCut hG T 𝒬 h hcard hm) U

end TriangleCut


end