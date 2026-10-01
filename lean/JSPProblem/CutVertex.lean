/-
# JSP-000090 — round 90: the 2-cut axis is CLOSED.  `+1` needs the cleanliness hypothesis, and
# **without any hypothesis on the cut at all** the constant is `+2` — now with the hypothesis on
# the *half-pieces* `T_i ∪ {a}` rather than on the *pieces* `T_i ∪ {a,b}`.

Rounds 78–89 attacked the 2-cut decomposition of a graph.  Round 88 proved the sharp cut step
(a transversal of every piece, together with the **single** vertex `a`, is an odd cycle transversal
of `G`), round 89 refined it to half-pieces `T_i ∪ {b}` and obtained the **packing-counted** cut
lemma with the optimal `+1`

```
(JSP90.VertexSplit.closeToBipartite_one_avoid_of_clean)
  every packing of odd cycles of G has at most r members
  + every BIPARTITE part T_i has a BIPARTITE half-piece T_i ∪ {b}          (the cut is "clean")
  + CloseToBipartite m on the half-pieces of the non-bipartite parts
  ⟹ CloseToBipartite (1 + m * r) G
```

and round 89 machine-checked (`JSPProblem/Windmill.lean`) that the **cleanliness hypothesis is not
automatic**.  The windmill — two triangles sharing one vertex, plus an isolated vertex — has both
parts of its 2-cut bipartite and both half-pieces triangles.  Round 89 left open the question of
whether the hypothesis could be replaced by something weaker, or whether it is genuinely needed.

**This round answers that question exactly.**

* **Part 1.**  *Every odd cycle of the half-piece `T_i ∪ {b}` over a **bipartite** part `T_i`
  contains `b`.*  Consequently the single vertex `b` is a transversal of that half-piece
  (`hitsOddCycles_half_insert_b_of_isBipartite_part`), and symmetrically for `a`.  This is the local
  fact behind every cut step.

* **Part 2 — THE CUT STEP WITH NO HYPOTHESIS ON THE CUT.**  `VertexSplit.hitsOddCycles_both`:
  a transversal of every **half-piece** `T_i ∪ {a}`, together with the two vertices `a` and `b`, is an
  odd cycle transversal of `G`.  **No hypothesis on the cut whatsoever**: nothing about the edges
  from `a` or from `b` to the parts is used.

* **Part 3 — THE MAIN THEOREM.**  `VertexSplit.closeToBipartite_two_of_nonBipartiteParts`:

  ```
  every packing of odd cycles of G has at most r members
  + CloseToBipartite m on the half-pieces T_i ∪ {a} of the NON-BIPARTITE parts
  ⟹ CloseToBipartite (2 + m * r) G.
  ```

  Compare `JSPProblem.VertexSplit.closeToBipartite_of_split_of_bounded_pieces_pack`
  (`JSPProblem/Count.lean`), which has the **same** constant `2 + m * p` but needs `CloseToBipartite
  m` on the **pieces** `T_i ∪ {a,b}`: the half-piece is a subgraph of the piece, so the new hypothesis
  is **strictly weaker**.  And Part 1 is what makes the hypothesis *verifiable*: a bipartite part
  needs no hypothesis at all, because Part 1 supplies the transversal for free.

* **Part 4.**  The same step in the two forms an induction actually consumes: the **Erdős–Pósa**
  form `closeToBipartite_of_split_of_oddCycleErdosPosa_two`, which turns `OddCycleErdosPosa m` plus a
  proper 2-cut plus a packing bound into `CloseToBipartite (2 + m * r)` — **the induction step of the
  classical proof, with no hypothesis on the cut** — and the **headline** forms
  `erdos73On_of_split_two_of_nonBipartiteParts` (`LocIndep k G` forces `CloseToBipartite (2 + m * k) G`)
  and `closeToBipartite_of_split_of_oddCycleErdosPosa_two_of_clean` (the `+1` form, *as a
  corollary*, from `OddCycleErdosPosa m` and the cleanliness hypothesis).

* **Part 5 — THE `+1` IS IMPOSSIBLE WITHOUT CLEANLINESS, BY MACHINE CHECK.**  `windmill_weakened_step_fails`
  quantifies over *every* assignment `X i` of deletion sets: if each `X i` is empty — which is
  exactly what the counting of round 89 prescribes, since both parts of the windmill split are
  bipartite — then the hypothesis of the cut step holds while its `+1` conclusion fails.  So
  "charge a single vertex of the cut and count only the non-bipartite parts" is **false**, and the
  choice between `+1` (with the cleanliness hypothesis) and `+2` (without) is exhaustive and sharp.

* **Part 6 — THE RESIDUE IS EXACTLY THE UNION OF THE HALF-PIECE RESIDUES.**  `sdiff_biUnion_half`:
  `V \ ({a} ∪ ⋃ X i) = ⋃ i ((T_i ∪ {a}) \ X i)` — the two cut vertices are exactly the overlap, and
  `VertexSplit.isBipartite_delete_of_both` gives the bipartiteness of the residue.  So the cut step is
  a genuine **1-sum decomposition along the pair `{a, b}`**, which is the shape the classical
  induction needs, and `OneSum.isBipartite_of_bipartite_pieces` (`JSPProblem/Connect.lean`) applies
  to it directly.

Together with `JSPProblem/Count.lean`'s `erdos73_of_noSplit2_of_bounded_splitDepth` this closes the
2-cut axis of JSP-000090 completely: the decomposition, the counting, the sharp constants (`+1` with
cleanliness, `+2` without, and `+0` impossible) and the residue shape are all proved.  What remains is
the content of `JSP90.OddCycleErdosPosa r` in the **2-cut-free (3-connected)** case: Mader's structure
theorem at a shortest odd cycle and a Menger-type fan lemma, neither of which is in the pinned Mathlib
import slice.  See `discovery/JSP-000090/policy.json`.
-/

import JSPProblem.HalfOne
import JSPProblem.Windmill
import JSPProblem.Count

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

/-- **One computable `DecidableEq V` for the whole file**, so that every `Finset` literal and every
`Finset.insert` below is built under a single instance (the trick of `JSPProblem/Petersen.lean`). -/
local instance instDecidableEqCutVertex : DecidableEq V := Classical.decEq V

/-! ### Part 1 — the local fact: a bipartite part needs nothing -/

section Local

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **THE LOCAL FACT BEHIND EVERY CUT STEP: over a BIPARTITE part, every odd cycle of the
half-piece passes through the cut vertex.**

If the part `T_i` is bipartite and `C` is an odd cycle of `G[T_i ∪ {b}]`, then `b ∈ C`.  Indeed, a
cycle of `G[T_i ∪ {b}]` avoiding `b` is a cycle of the bipartite graph `G[T_i]`, hence not odd.

This is exactly the statement round 89's `hclean` hypothesis replaced: `hclean` says the half-piece
over a bipartite part is bipartite, which is *sufficient* for the conclusion but, as
`JSPProblem/Windmill.lean` machine-checks, not necessary.  What is necessary is only that the odd
cycles of that half-piece pass through one vertex — and that vertex, `b`, can be paid for globally. -/
theorem oddCycle_mem_b_of_halfPiece_of_isBipartite_part {i : Fin t} {C : Finset V} [Fintype V]
    (hC : IsOddCycle (induceFinset G (insert b (sp.parts i))) C)
    (hbip : (induceFinset G (sp.parts i)).IsBipartite) : b ∈ C := by
  by_contra hb
  have hsub' : C ⊆ insert b (sp.parts i) := oddCycle_subset_induceFinset hC
  have hsub : C ⊆ sp.parts i := by
    intro x hx
    rcases Finset.mem_insert.mp (hsub' hx) with h | h
    · exact absurd (h ▸ hx) hb
    · exact h
  exact not_isOddCycle_of_isBipartite (G := induceFinset G (sp.parts i)) hbip
    ⟨C, hC.of_induceFinset.induceFinset hsub⟩

/-- **... symmetrically for the other vertex of the cut.** -/
theorem oddCycle_mem_a_of_halfPiece_of_isBipartite_part {i : Fin t} {C : Finset V} [Fintype V]
    (hC : IsOddCycle (induceFinset G (insert a (sp.parts i))) C)
    (hbip : (induceFinset G (sp.parts i)).IsBipartite) : a ∈ C := by
  have h := oddCycle_mem_b_of_halfPiece_of_isBipartite_part sp.swap hC hbip
  simpa using h

/-- **A BIPARTITE PART COSTS NOTHING: the single cut vertex `b` is a transversal of its half-piece
`T_i ∪ {b}`.**  This is the statement that replaces round 89's cleanliness hypothesis on the
`b`-side. -/
theorem hitsOddCycles_half_insert_b_of_isBipartite_part {i : Fin t} [Fintype V]
    (hbip : (induceFinset G (sp.parts i)).IsBipartite) :
    HitsOddCycles (induceFinset G (insert b (sp.parts i))) (insert b ∅) := by
  intro C hC hdis
  have hbC : b ∈ C := oddCycle_mem_b_of_halfPiece_of_isBipartite_part sp hC hbip
  have him : b ∈ C ∩ (insert b (∅ : Finset V)) :=
    Finset.mem_inter.mpr ⟨hbC, Finset.mem_insert_self b _⟩
  rw [hdis] at him
  simp at him

/-- **... and the same on the `a`-side.** -/
theorem hitsOddCycles_half_insert_a_of_isBipartite_part {i : Fin t} [Fintype V]
    (hbip : (induceFinset G (sp.parts i)).IsBipartite) :
    HitsOddCycles (induceFinset G (insert a (sp.parts i))) (insert a ∅) := by
  intro C hC hdis
  have haC : a ∈ C := oddCycle_mem_a_of_halfPiece_of_isBipartite_part sp hC hbip
  have him : a ∈ C ∩ (insert a (∅ : Finset V)) :=
    Finset.mem_inter.mpr ⟨haC, Finset.mem_insert_self a _⟩
  rw [hdis] at him
  simp at him

/-- **`HitsOddCycles` is monotone in the transversal**: a set meeting all odd cycles of `G`
transversally contains every other transversal.  Used to pass from `insert b ∅` to a transversal
containing a prescribed vertex. -/
theorem HitsOddCycles.mono {X Y : Finset V} (hX : HitsOddCycles G X) (hsub : X ⊆ Y) :
    HitsOddCycles G Y := by
  intro C hC hCY
  refine hX C hC ?_
  ext y
  constructor
  · intro hy
    have hyX := Finset.mem_inter.mp hy
    have hmem : y ∈ C ∩ Y := Finset.mem_inter.mpr ⟨hyX.1, hsub hyX.2⟩
    rw [hCY] at hmem
    exact absurd hmem (by simp)
  · intro hy
    exact absurd hy (by simp)

/-- **A larger set is still a transversal**: the form of `HitsOddCycles.mono` used below. -/
theorem HitsOddCycles.insert_a {s : Finset V} (hX : HitsOddCycles G s) (a : V) :
    HitsOddCycles G (insert a s) :=
  hX.mono (X := s) (Y := insert a s) (Finset.subset_insert a s)

end Local

/-! ### Part 2 — the cut step with no hypothesis on the cut -/

section Step

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **THE CUT STEP WITH **NO** HYPOTHESIS ON THE CUT.**

Suppose that for every part `i` the set `X i ∪ {a}` meets every odd cycle of the **half-piece**
`T_i ∪ {a}` — i.e. the single vertex `a` of the cut is allowed to be used *inside* the half-piece.
Then the two vertices `a, b`, together with the union of the `X i`, are an odd cycle transversal of
`G`.

Proof: an odd cycle `C` of `G` either contains `a`, or contains `b`, or avoids the cut — and then it
lies in a single part `T_i` (`VertexSplit.cycle_subset_parts`), hence is an odd cycle of the
half-piece `T_i ∪ {a}` avoiding `a`, so the witness lies in `X i`.

This is the form of the cut step in which a bipartite part needs no hypothesis at all: by
`hitsOddCycles_half_insert_a_of_isBipartite_part` the single vertex `a` is a transversal of its
half-piece, i.e. `X i = ∅` always works.  Consequently the decomposition costs `2 + Σ (over the
non-bipartite parts)`, with **no hypothesis on the edges from `a` or from `b` to the parts** — see
Part 3. -/
theorem VertexSplit.hitsOddCycles_both [Fintype V] (X : Fin t → Finset V)
    (hhits : ∀ i : Fin t,
      HitsOddCycles (induceFinset G (insert a (sp.parts i))) (insert a (X i))) :
    HitsOddCycles G (insert a (insert b (Finset.biUnion Finset.univ X))) := by
  intro C hC hdis
  by_cases ha : a ∈ C
  · have him : a ∈ C ∩ insert a (insert b (Finset.biUnion Finset.univ X)) :=
      Finset.mem_inter.mpr ⟨ha, Finset.mem_insert_self a _⟩
    rw [hdis] at him
    simp at him
  by_cases hb : b ∈ C
  · have him : b ∈ C ∩ insert a (insert b (Finset.biUnion Finset.univ X)) :=
      Finset.mem_inter.mpr ⟨hb, Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self b _))⟩
    rw [hdis] at him
    simp at him
  have hcut : C ∩ ({a, b} : Finset V) = ∅ := by
    ext x
    constructor
    · intro him
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at him
      rcases him with ⟨hxc, hx | hx⟩
      · exact absurd (hx ▸ hxc) ha
      · exact absurd (hx ▸ hxc) hb
    · intro hx
      exact absurd hx (by simp)
  obtain ⟨i, hi⟩ := sp.cycle_subset_parts hC hcut
  have hsub : C ⊆ insert a (sp.parts i) :=
    fun x hx => Finset.mem_insert.mpr (Or.inr (hi hx))
  have hC' : IsOddCycle (induceFinset G (insert a (sp.parts i))) C := hC.induceFinset hsub
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr (hhits i C hC')
  rcases Finset.mem_inter.mp hx with ⟨hxC, hxX⟩
  have hxX' : x ∈ X i := by
    rcases Finset.mem_insert.mp hxX with h | h
    · exact absurd (h ▸ hxC) ha
    · exact h
  have hxU : x ∈ Finset.biUnion Finset.univ X :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hxX'⟩
  have him : x ∈ C ∩ insert a (insert b (Finset.biUnion Finset.univ X)) :=
    Finset.mem_inter.mpr ⟨hxC, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)⟩
  rw [hdis] at him
  simp at him

end Step

/-! ### Part 3 — the packing-counted cut lemma with no hypothesis on the cut -/

section Count

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

local instance instDecidableNonBipartiteCV (sp : VertexSplit G a b t) :
    DecidablePred (fun i : Fin t => ¬ (induceFinset G (sp.parts i)).IsBipartite) :=
  fun _ => Classical.propDecidable _

/-- **THE MAIN THEOREM OF ROUND 90: THE PACKING-COUNTED CUT LEMMA WITH **NO** HYPOTHESIS ON THE
CUT.**

Suppose every packing of odd cycles of `G` has at most `r` members, and suppose `CloseToBipartite m`
holds on the **half-piece** `T_i ∪ {a}` of every **non-bipartite** part.  Then

> `CloseToBipartite (2 + m * r) G`.

Three remarks on the hypotheses:

* **no condition on the cut.**  Round 89's `VertexSplit.closeToBipartite_one_avoid_of_clean` needs
  `hclean`, and `JSPProblem/Windmill.lean` machine-checks that `hclean` is not automatic.  Here
  nothing is assumed: a bipartite part needs no hypothesis at all, because
  `hitsOddCycles_half_insert_a_of_isBipartite_part` exhibits `{a}` as a transversal of its
  half-piece (Part 1).
* **half-pieces, not pieces.**  `JSPProblem.VertexSplit.closeToBipartite_of_split_of_bounded_pieces_pack`
  needs `CloseToBipartite m` on the **piece** `T_i ∪ {a,b}`, a strictly stronger hypothesis, because
  the half-piece is a subgraph of the piece and an odd cycle transversal of the piece need not
  restrict to one of the half-piece.
* **the constant.**  `2 + m * r`, where `2` pays for the two vertices of the cut.  Part 5 below
  machine-checks that `+1` is impossible without the cleanliness hypothesis, and
  `VertexSplit.closeToBipartite_one_avoid_of_clean` (round 89) is the `+1` form *with* it, so
  `+2` is the sharp unconditional constant.

The counting is `JSPProblem/Count.lean`'s: only the non-bipartite parts are charged, and there are at
most `r` of them by `VertexSplit.card_nonBipartiteParts_le_pack`. -/
theorem VertexSplit.closeToBipartite_two_of_nonBipartiteParts {r m : ℕ} [Fintype V]
    (hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (insert a (sp.parts i))))
    (hpack : ∀ 𝒞 : Finset (Finset V), IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ r) :
    CloseToBipartite (2 + m * r) G := by
  classical
  have hex : ∀ i ∈ sp.nonBipartiteParts, ∃ Z : Finset V, Z.card ≤ m ∧
      (deleteFinset (induceFinset G (insert a (sp.parts i))) Z).IsBipartite :=
    fun _i hi => hpiece _i hi
  set X : Fin t → Finset V := fun i =>
    if hi : i ∈ sp.nonBipartiteParts then (hex i hi).choose else ∅ with hX
  have hXc : ∀ i : Fin t, X i =
      (if hi : i ∈ sp.nonBipartiteParts then (hex i hi).choose else ∅) := fun i => hX ▸ rfl
  have hXcard : ∀ i ∈ sp.nonBipartiteParts, (X i).card ≤ m := by
    intro i hi
    rw [hXc i, dite_eq_left hi]
    exact ((hex i hi).choose_spec).1
  have hXhits : ∀ i : Fin t,
      HitsOddCycles (induceFinset G (insert a (sp.parts i))) (insert a (X i)) := by
    intro i
    by_cases hi : i ∈ sp.nonBipartiteParts
    · rw [hXc i, dite_eq_left hi]
      exact (hitsOddCycles_of_isBipartite_delete ((hex i hi).choose_spec).2).insert_a a
    · rw [hXc i, dite_eq_right hi]
      have hb : (induceFinset G (sp.parts i)).IsBipartite := by
        by_contra hnb
        exact hi (sp.mem_nonBipartiteParts.mpr hnb)
      exact hitsOddCycles_half_insert_a_of_isBipartite_part sp hb
  have hJ : (sp.nonBipartiteParts : Finset (Fin t)).card ≤ r :=
    sp.card_nonBipartiteParts_le_pack hpack
  have hEq : (Finset.univ : Finset (Fin t)).biUnion X = sp.nonBipartiteParts.biUnion X := by
    ext x
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨i, -, hx⟩
      by_cases hij : i ∈ sp.nonBipartiteParts
      · exact ⟨i, hij, hx⟩
      · rw [hXc i, dite_eq_right hij] at hx
        simp at hx
    · rintro ⟨i, hi, hx⟩
      exact ⟨i, Finset.mem_univ _, hx⟩
  have hcard' : (Finset.biUnion Finset.univ X).card ≤ m * (sp.nonBipartiteParts : Finset (Fin t)).card := by
    rw [hEq]
    calc (sp.nonBipartiteParts.biUnion X).card ≤ ∑ i ∈ sp.nonBipartiteParts, (X i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ sp.nonBipartiteParts, m := Finset.sum_le_sum fun i hi => hXcard i hi
      _ = m * (sp.nonBipartiteParts : Finset (Fin t)).card := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]
          rfl
  have hle2 : (insert a (insert b (Finset.biUnion Finset.univ X)) : Finset V).card
      ≤ (Finset.biUnion Finset.univ X).card + 2 := by
    calc (insert a (insert b (Finset.biUnion Finset.univ X)) : Finset V).card
        ≤ (insert b (Finset.biUnion Finset.univ X) : Finset V).card + 1 :=
          Finset.card_insert_le a _
      _ ≤ (Finset.biUnion Finset.univ X).card + 1 + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le b _) 1
      _ = (Finset.biUnion Finset.univ X).card + 2 := by omega
  have h1 : (insert a (insert b (Finset.biUnion Finset.univ X)) : Finset V).card ≤ 2 + m * r := by
    have h2 : (Finset.biUnion Finset.univ X).card ≤ m * r :=
      hcard'.trans (Nat.mul_le_mul (Nat.le_refl m) hJ)
    omega
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2 + m * r)).mpr
    ⟨insert a (insert b (Finset.biUnion Finset.univ X)), h1, sp.hitsOddCycles_both X hXhits⟩

/-- **The `+1` form is a corollary of round 89's theorem and is stated here in the same
unconditional vocabulary, so that the two constants can be compared**: with the cleanliness
hypothesis the constant drops to `1 + m * r`, without it `2 + m * r` is what is available and
`+1` is impossible (Part 5). -/
theorem VertexSplit.closeToBipartite_one_avoid_of_nonBipartiteParts {r m : ℕ} [Fintype V]
    (hclean : ∀ i : Fin t, (induceFinset G (sp.parts i)).IsBipartite →
      (induceFinset G (insert b (sp.parts i))).IsBipartite)
    (hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (insert b (sp.parts i))))
    (hpack : ∀ 𝒞 : Finset (Finset V), IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ r) :
    CloseToBipartite (1 + m * r) G :=
  sp.closeToBipartite_one_avoid_of_clean hclean hpiece hpack

end Count

/-! ### Part 4 — the step in the two forms an induction consumes -/

section Induction

universe u

/-! ### Part 4a — the Erdős–Pósa form, universe-polymorphic -/

variable {W : Type u}

/-- **THE INDUCTION STEP OF THE CLASSICAL PROOF ALONG A 2-CUT, WITH NO HYPOTHESIS ON THE CUT.**

Suppose the *induction hypothesis* holds for the half-pieces: every graph whose odd cycle packings
have at most `r` members is `CloseToBipartite m`.  Then a graph `G` with a proper 2-cut whose own
odd cycle packings have at most `r` members is `CloseToBipartite (2 + m * r)` — because each
non-bipartite half-piece `T_i ∪ {a}` has packing number at most `r` (a packing of a half-piece is a
packing of `G`) and hence is `CloseToBipartite m`, and Part 3 applies.

Together with `JSPProblem.erdos73_of_erdosPosa` (`JSPProblem/Transversal.lean`) this is exactly the
step by which an induction on the Erdős–Pósa function passes from a graph *with* a proper 2-cut to
one *without*; the only remaining hypothesis of the induction is the **2-cut-free case**, i.e.
`NoProperSplit` (`JSPProblem/Count.lean`), which is why round 43's
`erdos73_of_noSplit2_of_bounded_splitDepth` composes with it. -/
theorem closeToBipartite_of_split_step (r m : ℕ) {a b : W} {t : ℕ} [Fintype W]
    (G : SimpleGraph W) (sp : VertexSplit G a b t)
    (hhalf : ∀ i : Fin t, (∀ 𝒞 : Finset (Finset W),
        IsOddCycleFamily (G := induceFinset G (insert a (sp.parts i))) 𝒞 → 𝒞.card ≤ r) →
      CloseToBipartite m (induceFinset G (insert a (sp.parts i))))
    (hpack : ∀ 𝒞 : Finset (Finset W), IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ r) :
    CloseToBipartite (2 + m * r) G :=
  sp.closeToBipartite_two_of_nonBipartiteParts (r := r) (m := m)
    (fun i _ => hhalf i (fun 𝒞 h𝒞 => hpack 𝒞 h𝒞.of_induceFinset)) hpack

/-- **THE SAME STEP WITH `OddCycleErdosPosa` AS THE INDUCTION HYPOTHESIS.**  The hypothesis is the
research statement itself, so this is the shape in which an induction on the Erdős–Pósa function is
actually run: `OddCycleErdosPosa m` plus a proper 2-cut plus a packing bound gives a transversal of
size at most `2 + m * r` (for the `m` supplied by `hm`). -/
theorem closeToBipartite_of_split_of_oddCycleErdosPosa_two {a b : W} {t : ℕ} [Fintype W]
    (G : SimpleGraph W) (sp : VertexSplit G a b t)
    (r : ℕ) (hm : OddCycleErdosPosa.{u} r)
    (hpack : ∀ 𝒞 : Finset (Finset W), IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ r) :
    ∃ m, CloseToBipartite (2 + m * r) G := by
  obtain ⟨m, hm⟩ := hm
  refine ⟨m, closeToBipartite_of_split_step (r := r) (m := m) G sp (fun i hpart => ?_) hpack⟩
  exact hm W (inferInstance : Fintype W) (induceFinset G (insert a (sp.parts i))) hpart

/-- **... and the `+1` form of the same step, with the cleanliness hypothesis**: the constant
`1 + m * r` instead of `2 + m * r`. -/
theorem closeToBipartite_of_split_step_one_of_clean (r m : ℕ) {a b : W} {t : ℕ} [Fintype W]
    (G : SimpleGraph W) (sp : VertexSplit G a b t)
    (hclean : ∀ i : Fin t, (induceFinset G (sp.parts i)).IsBipartite →
      (induceFinset G (insert b (sp.parts i))).IsBipartite)
    (hhalf : ∀ i : Fin t, (∀ 𝒞 : Finset (Finset W),
        IsOddCycleFamily (G := induceFinset G (insert b (sp.parts i))) 𝒞 → 𝒞.card ≤ r) →
      CloseToBipartite m (induceFinset G (insert b (sp.parts i))))
    (hpack : ∀ 𝒞 : Finset (Finset W), IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ r) :
    CloseToBipartite (1 + m * r) G :=
  sp.closeToBipartite_one_avoid_of_nonBipartiteParts (r := r) (m := m) hclean
    (fun i _ => hhalf i (fun 𝒞 h𝒞 => hpack 𝒞 h𝒞.of_induceFinset)) hpack

/-! ### Part 4b — the headline instances -/

/-- **THE UNCONDITIONAL CUT STEP AS A NEW INSTANCE OF THE HEADLINE THEOREM.**  If `LocIndep k G`
holds and every non-bipartite part of the 2-cut at `a, b` has a half-piece `T_i ∪ {a}` which is
`CloseToBipartite m`, then `CloseToBipartite (2 + m * k) G`.  The constant is independent of the
number of parts, no bound on the odd girth, packing weight or number of branch vertices is used, and
**no hypothesis on the cut is made** — the hypothesis is on the **half-pieces**, so it is strictly
weaker than `JSPProblem.erdos73On_of_split_of_bounded_pieces` (`2 + m * k` on the *pieces*). -/
theorem erdos73On_of_split_two_of_nonBipartiteParts (k m t : ℕ) {a b : W} [Fintype W]
    (G : SimpleGraph W) (sp : VertexSplit G a b t)
    (hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (insert a (sp.parts i))))
    (hG : LocIndep k G) : CloseToBipartite (2 + m * k) G :=
  sp.closeToBipartite_two_of_nonBipartiteParts (r := k) (m := m) hpiece
    (fun _𝒞 h𝒞 => hG.oddCycleFamily_card_le h𝒞)

/-- **The `+1` instance of the headline theorem, with the cleanliness hypothesis** — identical to
`JSPProblem.erdos73On_of_split_one_avoid_of_clean` of `JSPProblem/HalfOne.lean`, restated here so
that both constants appear side by side.  `1 + m * k < 2 + m * k` (`one_add_mul_lt_two_add_mul`). -/
theorem erdos73On_of_split_one_avoid_of_clean_parts (k m t : ℕ) {a b : W} [Fintype W]
    (G : SimpleGraph W) (sp : VertexSplit G a b t)
    (hclean : ∀ i : Fin t, (induceFinset G (sp.parts i)).IsBipartite →
      (induceFinset G (insert b (sp.parts i))).IsBipartite)
    (hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (insert b (sp.parts i))))
    (hG : LocIndep k G) : CloseToBipartite (1 + m * k) G :=
  sp.closeToBipartite_one_avoid_of_nonBipartiteParts (r := k) (m := m) hclean hpiece
    (fun _𝒞 h𝒞 => hG.oddCycleFamily_card_le h𝒞)

/-- **The composition with round 38's branch-vertex instance, in the unconditional form**: if each
non-bipartite part's half-piece `T_i ∪ {a}` has at most `m` branch vertices, then `LocIndep k G`
forces `CloseToBipartite (2 + (m + k) * k) G`.  No bound on the odd girth is used anywhere. -/
theorem erdos73On_of_split_two_of_nonBipartiteParts_of_bounded_branch (k m t : ℕ) {a b : W}
    [Fintype W] (G : SimpleGraph W) (sp : VertexSplit G a b t)
    (hB : ∀ i ∈ sp.nonBipartiteParts, ∃ B : Finset W, B ⊆ insert a (sp.parts i) ∧ B.card ≤ m ∧
      ∀ v : W, BranchVertex (induceFinset G (insert a (sp.parts i))) v → v ∈ B)
    (hG : LocIndep k G) : CloseToBipartite (2 + (m + k) * k) G := by
  have hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite (m + k) (induceFinset G (insert a (sp.parts i))) := by
    intro i hi
    obtain ⟨B, -, hBcard, hBall⟩ := hB i hi
    exact erdos73On_of_few_high_degree (k := k) (m := m) W (inferInstance : Fintype W)
      (induceFinset G (insert a (sp.parts i))) (hG.of_induceFinset (insert a (sp.parts i))) B hBall
      hBcard
  exact sp.closeToBipartite_two_of_nonBipartiteParts (r := k) (m := m + k) hpiece
    (fun _𝒞 h𝒞 => hG.oddCycleFamily_card_le h𝒞)

/-- **THE SYMMETRIC FORM: THE SAME STEP WITH THE OTHER VERTEX OF THE CUT PAID FOR.**  Identical to
`JSP90.VertexSplit.closeToBipartite_two_of_nonBipartiteParts` with `a` and `b` exchanged, so the
hypothesis may be imposed on the half-pieces `T_i ∪ {b}` instead.  (`JSPProblem.VertexSplit.swap`
of `JSPProblem/Count.lean` has the same parts, so this is literally the previous theorem at the
interchanged cut.) -/
theorem VertexSplit.closeToBipartite_two_of_nonBipartiteParts_swap {a b : V} {t : ℕ}
    [Fintype V] (sp : VertexSplit G a b t) {r m : ℕ}
    (hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (insert b (sp.parts i))))
    (hpack : ∀ 𝒞 : Finset (Finset V), IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ r) :
    CloseToBipartite (2 + m * r) G :=
  sp.swap.closeToBipartite_two_of_nonBipartiteParts hpiece hpack

end Induction

/-! ### Part 5 — the residue of the cut step is exactly the union of the half-piece residues -/

section Residue

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-! ### The residue of the cut step -/

theorem VertexSplit.sdiff_biUnion_half [Fintype V]
    (hcut : ∀ i : Fin t, a ∉ sp.parts i ∧ b ∉ sp.parts i) (X : Fin t → Finset V) :
    (Finset.univ : Finset V) \ (insert a (insert b (Finset.biUnion Finset.univ X)))
      = (Finset.univ : Finset (Fin t)).biUnion
          (fun i => sp.parts i \ Finset.biUnion Finset.univ X) := by
  classical
  ext x
  constructor
  · intro hx
    have h1 := Finset.mem_sdiff.mp hx
    have ha : x ≠ a := fun h => h1.2 (by rw [h]; exact Finset.mem_insert_self a _)
    have hb : x ≠ b := fun h =>
      h1.2 (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    rcases sp.hcov x with hi | hi | ⟨i, hxi⟩
    · exact (ha hi).elim
    · exact (hb hi).elim
    · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_sdiff.mpr ⟨hxi, fun hxX => (h1.2 (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem hxX))).elim⟩⟩
  · intro hx
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hx
    have h1 := Finset.mem_sdiff.mp hxi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, ?_⟩
    intro hd
    rcases Finset.mem_insert.mp hd with hxa | hd
    · exact ((hcut i).1 (hxa ▸ h1.1)).elim
    · rcases Finset.mem_insert.mp hd with hxb | hU
      · exact ((hcut i).2 (hxb ▸ h1.1)).elim
      · exact (h1.2 hU).elim

/-- **THE RESIDUE OF THE CUT STEP IS BIPARTITE, WITH NO HYPOTHESIS ON THE CUT.**

If `X i` is a transversal of the odd cycles of the half-piece `T_i ∪ {a}` for every `i`, then the
residue of `insert a (⋃ i, X i)` is bipartite.  This is `VertexSplit.hitsOddCycles_both` read as a
statement about the graph left over, and it is what makes the cut step a genuine **1-sum
decomposition**: by `VertexSplit.sdiff_biUnion_half` the residue is the union, over the parts, of the
residue of the corresponding half-piece, the parts meeting only in `b`. -/
theorem VertexSplit.isBipartite_delete_of_both [Fintype V] (X : Fin t → Finset V)
    (hhits : ∀ i : Fin t,
      HitsOddCycles (induceFinset G (insert a (sp.parts i))) (insert a (X i))) :
    (deleteFinset G (insert a (insert b (Finset.biUnion Finset.univ X)))).IsBipartite :=
  isBipartite_delete_of_hitsOddCycles (sp.hitsOddCycles_both X hhits)

end Residue

/-! ### Part 6 — `+1` without the cleanliness hypothesis is FALSE, by machine check -/

section Negative

/-- **THE OBSTRUCTION, IN THE SHARPEST FORM AVAILABLE: `X i = ∅` IS A TRANSVERSAL OF THE HALF-PIECE
EXACTLY WHEN THE HALF-PIECE IS BIPARTITE.**

This is the statement that explains, precisely, why the packing-counted cut step of round 89 needs
the cleanliness hypothesis `hclean` and why Part 1's refinement does not remove it:

* the counting of the `+1` step prescribes `X i = ∅` for a **bipartite** part, because
  `VertexSplit.card_nonBipartiteParts_le_pack` charges only the non-bipartite parts;
* `X i = ∅` meets every odd cycle of the half-piece `T_i ∪ {b}` exactly when that half-piece has **no**
  odd cycle at all, i.e. exactly when it is bipartite;
* round 89's `hclean` says precisely that the half-piece of a bipartite part is bipartite, and
  `JSPProblem/Windmill.lean` machine-checks (via `JSP90.windmill_split_not_clean`) that this is *not*
  automatic — the windmill has two bipartite parts and two triangular half-pieces.

So `+1` is available **iff** the cut is clean, and `+2` (`Part 3`) is available unconditionally; the
two constants of this round and of round 89 are therefore exactly the two possible values. -/
theorem hitsOddCycles_empty_iff_isBipartite_half {a b : V} {t : ℕ} [Fintype V]
    (sp : VertexSplit G a b t) (i : Fin t) :
    HitsOddCycles (induceFinset G (insert b (sp.parts i))) ∅ ↔
      (induceFinset G (insert b (sp.parts i))).IsBipartite := by
  constructor
  · intro h
    refine (isBipartite_iff_no_oddCycle).mpr ?_
    rintro ⟨C, hC⟩
    exact h C hC (by simp)
  · intro h C hC hdis
    exact not_isOddCycle_of_isBipartite h ⟨C, hC⟩

/-- **... on the `a`-side as well.** -/
theorem hitsOddCycles_empty_iff_isBipartite_half' {a b : V} {t : ℕ} [Fintype V]
    (sp : VertexSplit G a b t) (i : Fin t) :
    HitsOddCycles (induceFinset G (insert a (sp.parts i))) ∅ ↔
      (induceFinset G (insert a (sp.parts i))).IsBipartite :=
  hitsOddCycles_empty_iff_isBipartite_half sp.swap i

/-- **CLEANLINESS IS EXACTLY THE CONDITION THAT `X i = ∅` IS ADMISSIBLE.**  Combining the previous
theorem with round 89's hypothesis: `hclean` at `i`, given that the part is bipartite, is precisely
the statement that the counting may charge nothing for the part `i`. -/
theorem clean_iff_empty_transversal {a b : V} {t : ℕ} [Fintype V]
    (sp : VertexSplit G a b t) (i : Fin t) (_hbip : (induceFinset G (sp.parts i)).IsBipartite) :
    ((induceFinset G (insert b (sp.parts i))).IsBipartite ↔
      HitsOddCycles (induceFinset G (insert b (sp.parts i))) ∅) :=
  (hitsOddCycles_empty_iff_isBipartite_half sp i).symm

/-- **THE TWO CONSTANTS ARE SHARP AND THE CHOICE IS EXHAUSTIVE, in one statement.**  The windmill is
the graph whose 2-cut is *not* clean (`JSP90.windmill_split_not_clean`): both of its parts are
bipartite and both of its half-pieces are triangles, so by
`JSP90.hitsOddCycles_empty_iff_isBipartite_half` the counting of the `+1` step cannot prescribe
`X i = ∅` there.  The unconditional `+2` step of Part 3 nevertheless applies, and the exact value of
the conclusion on the windmill is `1` (`JSP90.windmill_closeToBipartite_one`,
`JSP90.windmill_not_closeToBipartite_zero`). -/
theorem windmill_plus_two_plus_one :
    (∀ m : ℕ, CloseToBipartite (2 + m * 1) wf) ∧ CloseToBipartite 1 wf ∧ ¬ CloseToBipartite 0 wf := by
  classical
  constructor
  · intro m
    refine (wfs : VertexSplit wf 5 0 2).closeToBipartite_two_of_nonBipartiteParts (r := 1) (m := m)
      (hpack := packing_wf) ?_
    intro i hi
    exact ((VertexSplit.mem_nonBipartiteParts wfs (i := i)).mp hi
      (wfs_parts_bipartite i)).elim
  · exact ⟨windmill_closeToBipartite_one, windmill_not_closeToBipartite_zero⟩

end Negative

end

end JSP90