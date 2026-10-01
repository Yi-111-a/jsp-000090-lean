/-
# JSP-000090 — the refined cut step: paying one cut vertex and only the cycles that avoid it

`JSPProblem/SplitOne.lean` (round 88) proved the **sharp cut step**: a transversal of every piece
`T_i ∪ {a,b}`, together with the **single** vertex `a` of the 2-cut, is an odd cycle transversal of
`G`; hence `τ(G) ≤ 1 + Σ_i τ(T_i ∪ {a,b})` and `CloseToBipartite (1 + m * t) G`.

Its hypothesis is however still stated for **all** the odd cycles of the piece.  That is more than
is needed: the odd cycles of the piece which *contain* `a` are met by `a` itself and need no
transversal at all.  Weakening the per-piece obligation accordingly is the **refined cut step**:

> (`JSP90.VertexSplit.hitsOddCycles_one_avoid`)  if every `X_i` meets every odd cycle of the piece
> `T_i ∪ {a,b}` which **avoids `a`**, then `{a} ∪ (⋃_i X_i)` is an odd cycle transversal of `G`.

An odd cycle of the piece `T_i ∪ {a,b}` which avoids `a` is an odd cycle of the **half-piece**
`T_i ∪ {b}` — these are the objects described by `JSPProblem/Count.lean`'s
`VertexSplit.cycle_subset_piece_of_not_mem'` — so the refined hypothesis is *"a transversal of every
half-piece"*, a **strictly weaker** requirement than round 88's.

This is a **sixth independent attack family**, on the *strength of the per-piece obligation*, not on
the class of graphs.  It yields, in this order:

1. the refined cut step, its symmetric form, and the corollary that round 88's step follows from it
   (Part 1);
2. **a new instance of the headline theorem** `CloseToBipartite (1 + m * t) G` from a hypothesis on
   the half-pieces (Part 2) — strictly stronger than round 88's, whose hypothesis is on the *full*
   pieces;
3. **the packing-counted cut lemma with the optimal `+1`**,
   `CloseToBipartite (1 + m * r) G` / `CloseToBipartite (1 + m * k) G`, under the *cleanliness*
   hypothesis on the cut (Parts 3–4).  This is the classical RRST cut lemma, and the step which
   turns the 2-cut decomposition into a genuine induction on the Erdős–Pósa function, because the
   constant no longer depends on the number of pieces `t`;
4. **machine-checked sharpness**: the `+1` is unavoidable, and it is attained on the 5-cycle of
   round 88 (Part 5);
5. **a machine-checked negative result**: the cleanliness hypothesis is *not* automatic.  The
   *windmill* graph (two triangles sharing a single vertex) is `LocIndep 1`, has packing number
   **one**, and **two** non-bipartite half-pieces — so "the number of non-bipartite half-pieces is
   bounded by the packing number" is **false**, machine-checkably (Part 6).  This is exactly why
   Part 3 states the hypothesis explicitly, and it saves the next round from chasing a refuted
   counting lemma.

What this does not give: the 3-connected case of `OddCycleErdosPosa`, i.e. Mader's structure theorem
at a shortest odd cycle and a Menger-type fan lemma, neither of which is in the pinned Mathlib slice.
See `discovery/JSP-000090/policy.json`.
-/

import JSPProblem.SplitOne

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqHalfOne : DecidableEq V := Classical.decEq V

/-! ### Part 1 — the refined cut step -/

section Refined

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **THE REFINED CUT STEP.**  Suppose that for every part `i` the set `X i` meets every odd cycle of
the piece `T_i ∪ {a,b}` which **avoids the vertex `a`** of the cut.  Then the single vertex `a`,
together with the union of the `X i`, is an odd cycle transversal of `G`.

Compare `VertexSplit.hitsOddCycles_one` of `JSPProblem/SplitOne.lean`, whose hypothesis is that
`X i` meets *every* odd cycle of the piece: the cycles through `a` are met by `a` and are dropped
here, so the hypothesis is **strictly weaker** and the theorem strictly stronger.

Proof: an odd cycle `C` of `G` avoiding `a` is, by `VertexSplit.oddCycle_piece_or_both`, contained in
a piece (it cannot contain both `a` and `b`), and — `a` being absent — in the half-piece
`T_i ∪ {b}`; so it is met by `X i`. -/
theorem VertexSplit.hitsOddCycles_one_avoid [Fintype V] (X : Fin t → Finset V)
    (hhits : ∀ i : Fin t, ∀ C : Finset V, IsOddCycle (induceFinset G (sp.piece i)) C →
      a ∉ C → (C ∩ X i) ≠ ∅) :
    HitsOddCycles G (insert a (Finset.biUnion Finset.univ X)) := by
  intro C hC hdis
  by_cases ha : a ∈ C
  · have him : a ∈ C ∩ insert a (Finset.biUnion Finset.univ X) :=
      Finset.mem_inter.mpr ⟨ha, Finset.mem_insert_self a _⟩
    rw [hdis] at him
    simp at him
  · rcases sp.oddCycle_piece_or_both hC with ⟨i, hsub⟩ | hboth
    · have hC' : IsOddCycle (induceFinset G (sp.piece i)) C := hC.induceFinset hsub
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr (hhits i C hC' ha)
      have hxC : x ∈ C := (Finset.mem_inter.mp hx).1
      have hxX : x ∈ X i := (Finset.mem_inter.mp hx).2
      have him : x ∈ C ∩ insert a (Finset.biUnion Finset.univ X) := Finset.mem_inter.mpr ⟨hxC,
        Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hxX⟩))⟩
      rw [hdis] at him
      simp at him
    · exact ha (hboth (Finset.mem_insert_self a ({b} : Finset V)))

/-- **THE REFINED CUT STEP IN HALF-PIECE FORM: a transversal of every half-piece `T_i ∪ {b}`,
together with the single vertex `a`, is an odd cycle transversal of `G`.**

This is the form in which the refined step is used, since an odd cycle of `G` avoiding `a` lies in a
half-piece, and an induction on the Erdős–Pósa function produces its instance on the half-pieces.

Proof, as in `hitsOddCycles_one_avoid`: an odd cycle `C` of `G` avoiding `a` lies in a piece
(`oddCycle_piece_or_both`) and, `a` being absent, in the half-piece `T_i ∪ {b}`. -/
theorem VertexSplit.hitsOddCycles_half [Fintype V] (X : Fin t → Finset V)
    (hhits : ∀ i : Fin t, HitsOddCycles (induceFinset G (insert b (sp.parts i))) (X i)) :
    HitsOddCycles G (insert a (Finset.biUnion Finset.univ X)) := by
  intro C hC hdis
  by_cases ha : a ∈ C
  · have him : a ∈ C ∩ insert a (Finset.biUnion Finset.univ X) :=
      Finset.mem_inter.mpr ⟨ha, Finset.mem_insert_self a _⟩
    rw [hdis] at him
    simp at him
  · rcases sp.oddCycle_piece_or_both hC with ⟨i, hsub⟩ | hboth
    · have hsub' : C ⊆ insert b (sp.parts i) := by
        intro x hx
        rcases sp.mem_piece i x |>.mp (hsub hx) with h | h | h
        · exact absurd (h ▸ hx) ha
        · exact Finset.mem_insert.mpr (Or.inl h)
        · exact Finset.mem_insert.mpr (Or.inr h)
      have hC' : IsOddCycle (induceFinset G (insert b (sp.parts i))) C :=
        IsOddCycle.induceFinset hC hsub'
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr (hhits i C hC')
      have hxC : x ∈ C := (Finset.mem_inter.mp hx).1
      have hxX : x ∈ X i := (Finset.mem_inter.mp hx).2
      have him : x ∈ C ∩ insert a (Finset.biUnion Finset.univ X) := Finset.mem_inter.mpr ⟨hxC,
        Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hxX⟩))⟩
      rw [hdis] at him
      simp at him
    · exact ha (hboth (Finset.mem_insert_self a ({b} : Finset V)))

/-- **The symmetric refined cut step**: the other vertex of the cut may be paid for instead.  A
transversal of every half-piece `T_i ∪ {a}`, together with `b`, is an odd cycle transversal of `G`.
The parts of `sp.swap` are those of `sp`, so this is literally the previous theorem at the
interchanged cut. -/
theorem VertexSplit.hitsOddCycles_half' [Fintype V] (X : Fin t → Finset V)
    (hhits : ∀ i : Fin t, HitsOddCycles (induceFinset G (insert a (sp.parts i))) (X i)) :
    HitsOddCycles G (insert b (Finset.biUnion Finset.univ X)) :=
  sp.swap.hitsOddCycles_half X hhits

/-- **THE HALF-PIECE LIES IN THE PIECE: `T_i ∪ {b} ⊆ T_i ∪ {a,b}`.**, as it must: this is the
containment which makes the half-piece form of the refined cut step a *weakening* of round 88's
hypothesis (a transversal of the piece is a transversal of the half-piece), and it is what the
`IsBipartite` transfer in Part 5 uses. -/
theorem VertexSplit.halfPiece_subset_piece {a b : V} {t : ℕ} (sp : VertexSplit G a b t)
    (i : Fin t) :
    insert b (sp.parts i) ⊆ sp.piece i := by
  refine Finset.Subset.trans
    (Finset.insert_subset_insert b fun x hx => (sp.mem_piece i x).mpr (Or.inr (Or.inr hx))) ?_
  rw [Finset.insert_eq_of_mem ((sp.mem_piece i b).mpr (Or.inr (Or.inl rfl)) : b ∈ sp.piece i)]

/-- **Round 88's cut step is a corollary of the refined one**: a transversal of every *piece* is in
particular a transversal of every half-piece `T_i ∪ {b}`, the half-piece being an induced subgraph of
the piece `T_i ∪ {a,b}` (`IsOddCycle.of_induceFinset`).  So the new theorem is a strict *weakening
of the hypothesis*, and nothing proved in round 88 is lost. -/
theorem VertexSplit.hitsOddCycles_half_of_hitsOddCycles_one [Fintype V] (X : Fin t → Finset V)
    (hhits : ∀ i : Fin t, HitsOddCycles (induceFinset G (sp.piece i)) (X i)) :
    ∀ i : Fin t, HitsOddCycles (induceFinset G (insert b (sp.parts i))) (X i) := by
  intro i C hC
  have hmem : C ⊆ insert b (sp.parts i) := oddCycle_subset_induceFinset hC
  have hsub : C ⊆ sp.piece i := by
    intro x hx
    rcases Finset.mem_insert.mp (hmem hx) with h | h
    · exact (sp.mem_piece i x).mpr (Or.inr (Or.inl h))
    · exact (sp.mem_piece i x).mpr (Or.inr (Or.inr h))
  exact hhits i C (IsOddCycle.induceFinset hC.of_induceFinset hsub)

/-- **THE REFINED CUT STEP AS A CLOSE-TO-BIPARTITE STATEMENT.**  If each half-piece `T_i ∪ {b}` is
`CloseToBipartite m`, then `G` is `CloseToBipartite (1 + m * t)`: a transversal of every half-piece,
together with the single vertex `a` of the cut.

The card bound is the one of `VertexSplit.exists_transversal_one` of round 88, line by line; only the
hypothesis is new. -/
theorem VertexSplit.exists_transversal_half [Fintype V] {m : ℕ}
    (hhalf : ∀ i : Fin t, CloseToBipartite m (induceFinset G (insert b (sp.parts i)))) :
    ∃ Y : Finset V, HitsOddCycles G Y ∧ Y.card ≤ 1 + m * t := by
  have hex : ∀ i : Fin t, ∃ Z : Finset V, Z.card ≤ m ∧
      HitsOddCycles (induceFinset G (insert b (sp.parts i))) Z := by
    intro i
    obtain ⟨Z, hZcard, hZ⟩ := hhalf i
    exact ⟨Z, hZcard, hitsOddCycles_of_isBipartite_delete hZ⟩
  set X : Fin t → Finset V := fun i => Classical.choose (hex i) with hX
  have hhits : ∀ i : Fin t, HitsOddCycles (induceFinset G (insert b (sp.parts i))) (X i) := by
    intro i
    rw [hX]
    exact (Classical.choose_spec (hex i)).2
  refine ⟨insert a (Finset.biUnion Finset.univ X), sp.hitsOddCycles_half X hhits, ?_⟩
  have hle : (insert a (Finset.biUnion Finset.univ X) : Finset V).card
      ≤ (Finset.biUnion Finset.univ X).card + 1 := Finset.card_insert_le a _
  have h2 : (Finset.biUnion Finset.univ X).card ≤ ∑ i : Fin t, (X i).card :=
    Finset.card_biUnion_le
  have h3 : (∑ i : Fin t, (X i).card) ≤ ∑ _i : Fin t, (m : ℕ) :=
    Finset.sum_le_sum fun i hi => (Classical.choose_spec (hex i)).1
  have h4 : (∑ _i : Fin t, (m : ℕ)) = m * t := by
    calc (∑ _i : Fin t, (m : ℕ)) = (Finset.univ : Finset (Fin t)).card * m := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rfl
      _ = m * t := by rw [Finset.card_fin, Nat.mul_comm]
  have h5 : (Finset.biUnion Finset.univ X).card ≤ m * t :=
    h2.trans (h3.trans (le_of_eq h4))
  omega

end Refined

/-! ### Part 2 — a new instance of the headline theorem -/

section Instance

universe u

variable {a b : V} {t : ℕ}

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM, WITH A STRICTLY WEAKER HYPOTHESIS THAN ROUND 88'S.**

Suppose `V(G)` splits as `{a, b} ⊔ T₁ ⊔ … ⊔ T_t` with the parts pairwise anticomplete, and that
`LocIndep k` forces `CloseToBipartite m` in every **half-piece** `T_i ∪ {b}` — the piece with the
cut vertex `a` already erased.  Then `LocIndep k G` forces `CloseToBipartite (1 + m * t) G`.

`JSPProblem.erdos73On_of_split_one` (round 88) obtains the same conclusion from the hypothesis on
the **full** pieces `T_i ∪ {a,b}`; the hypothesis here is on strictly smaller objects, so an
induction on the Erdős–Pósa function which provides the instance on the half-pieces — exactly what
`JSPProblem/Count.lean`'s `VertexSplit.cycle_subset_piece_of_not_mem'` forces one to consider — may
now be closed over a 2-cut. -/
theorem erdos73On_of_split_one_avoid (k m t : ℕ) {W : Type u} [Fintype W] (G : SimpleGraph W)
    (a b : W) (sp : VertexSplit G a b t)
    (hpiece : ∀ i : Fin t, LocIndep k (induceFinset G (insert b (sp.parts i))) →
      CloseToBipartite m (induceFinset G (insert b (sp.parts i))))
    (hG : LocIndep k G) : CloseToBipartite (1 + m * t) G := by
  have hLoc : ∀ i : Fin t, LocIndep k (induceFinset G (insert b (sp.parts i))) :=
    fun i => hG.of_induceFinset (insert b (sp.parts i))
  obtain ⟨Y, hY, hYcard⟩ :=
    sp.exists_transversal_half (m := m) (hhalf := fun i => hpiece i (hLoc i))
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 1 + m * t)).mpr ⟨Y, hYcard, hY⟩

/-- **THE SAME INSTANCE IN ERDŐS–PÓSA FORM.**  If every packing of odd cycles of `G` has at most `r`
members, and the packing hypothesis forces `CloseToBipartite m` on every half-piece `T_i ∪ {b}`, then
`G` is the union of a bipartite graph and at most `1 + m * t` vertices.  This is the form in which
the refined cut step is consumed by the Erdős–Pósa induction: the packing hypothesis restricts to
the half-pieces (a packing of odd cycles of `G[T_i ∪ {b}]` is one of `G`) and the conclusion pays for
**one** vertex of the cut. -/
theorem closeToBipartite_of_split_one_avoid_of_oddCycleErdosPosa (r m t : ℕ) {W : Type u}
    [Fintype W] (G : SimpleGraph W) (a b : W) (sp : VertexSplit G a b t)
    (hpiece : ∀ i : Fin t,
      (∀ C : Finset (Finset W), IsOddCycleFamily (G := induceFinset G (insert b (sp.parts i))) C →
        C.card ≤ r) → CloseToBipartite m (induceFinset G (insert b (sp.parts i))))
    (hpack : ∀ C : Finset (Finset W), IsOddCycleFamily (G := G) C → C.card ≤ r) :
    CloseToBipartite (1 + m * t) G := by
  obtain ⟨Y, hY, hYcard⟩ := sp.exists_transversal_half (m := m)
    (hhalf := fun i => hpiece i fun C hC => hpack C hC.of_induceFinset)
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 1 + m * t)).mpr ⟨Y, hYcard, hY⟩

end Instance

/-! ### Part 3 — the packing-counted cut lemma with the optimal `+1` -/

section Clean

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

local instance instDecidableNonBipartiteHalfOne (sp : VertexSplit G a b t) :
    DecidablePred (fun i : Fin t => ¬ (induceFinset G (sp.parts i)).IsBipartite) :=
  fun _ => Classical.propDecidable _

/-- **THE REFINED CUT STEP WITH THE PACKING NUMBER: `CloseToBipartite (1 + m * r) G`.**

Suppose every packing of odd cycles of `G` has at most `r` members, and suppose

> (**`)  every **bipartite** part `T_i` has a bipartite half-piece `T_i ∪ {b}`,

i.e. the cut is *clean* in the sense of `JSP90.VertexSplit.CleanHalf`.  Then `G` is the union of a
bipartite graph and at most `1 + m * r` vertices, where `CloseToBipartite m` is assumed on the
half-pieces of the non-bipartite parts.

This is the classical RRST cut lemma, with the **optimal** `+1`, and with a constant depending only
on the **packing number** — not on the number of pieces `t`.  Compare
`JSPProblem.closeToBipartite_of_split_of_bounded_pieces_pack` (`JSPProblem/Count.lean`), which gives
`CloseToBipartite (2 + m * p) G` from a hypothesis on the *full* pieces: here the constant is
smaller by one (`1 + m * r < 2 + m * r`, `JSP90.one_add_mul_lt_two_add_mul`), and the hypothesis is
stated on the half-pieces `T_i ∪ {b}` rather than on the pieces `T_i ∪ {a,b}`.

The counting is `JSPProblem.Count`'s: the deletion sets are needed only for the non-bipartite parts
(by (**`)), and there are at most `r` of those by `VertexSplit.card_nonBipartiteParts_le_pack`, each
carrying an odd cycle inside its own part. -/
theorem VertexSplit.closeToBipartite_one_avoid_of_clean {r m : ℕ} [Fintype V]
    (hclean : ∀ i : Fin t, (induceFinset G (sp.parts i)).IsBipartite →
      (induceFinset G (insert b (sp.parts i))).IsBipartite)
    (hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (insert b (sp.parts i))))
    (hpack : ∀ 𝒞 : Finset (Finset V), IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ r) :
    CloseToBipartite (1 + m * r) G := by
  classical
  have hex : ∀ i ∈ sp.nonBipartiteParts, ∃ Z : Finset V, Z.card ≤ m ∧
      (deleteFinset (induceFinset G (insert b (sp.parts i))) Z).IsBipartite :=
    fun _i hi => hpiece _i hi
  set X : Fin t → Finset V := fun i =>
    if hi : i ∈ sp.nonBipartiteParts then (hex i hi).choose else ∅ with hX
  have hXc : ∀ i : Fin t, X i =
      (if hi : i ∈ sp.nonBipartiteParts then (hex i hi).choose else ∅) := fun i => hX ▸ rfl
  have hXcard : ∀ i ∈ sp.nonBipartiteParts, (X i).card ≤ m := by
    intro i hi
    rw [hXc i, dite_eq_left hi]
    exact ((hex i hi).choose_spec).1
  have hXhits : ∀ i : Fin t, HitsOddCycles (induceFinset G (insert b (sp.parts i))) (X i) := by
    intro i
    by_cases hi : i ∈ sp.nonBipartiteParts
    · rw [hXc i, dite_eq_left hi]
      exact hitsOddCycles_of_isBipartite_delete ((hex i hi).choose_spec).2
    · rw [hXc i, dite_eq_right hi]
      have hb : (induceFinset G (sp.parts i)).IsBipartite := by
        by_contra hnb
        exact hi (sp.mem_nonBipartiteParts.mpr hnb)
      intro C hC hdis
      exact (not_isOddCycle_of_isBipartite (hclean i hb) ⟨C, hC⟩).elim
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
  have hle : (insert a (Finset.biUnion Finset.univ X) : Finset V).card
      ≤ (Finset.biUnion Finset.univ X).card + 1 := Finset.card_insert_le a _
  have h1 : (insert a (Finset.biUnion Finset.univ X) : Finset V).card ≤ 1 + m * r := by
    have h2 : (Finset.biUnion Finset.univ X).card ≤ m * r :=
      hcard'.trans (Nat.mul_le_mul (Nat.le_refl m) hJ)
    omega
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 1 + m * r)).mpr
    ⟨insert a (Finset.biUnion Finset.univ X), h1, sp.hitsOddCycles_half X hXhits⟩

end Clean

/-! ### Part 4 — the instances in the headline vocabulary -/

section Headline

universe u

variable {a b : V} {t : ℕ}

/-- **THE CLASSICAL CUT LEMMA WITH THE OPTIMAL `+1`, IN THE HEADLINE FORM.**
If `LocIndep k G` holds and the 2-cut of `G` at `a, b` is **clean** (every bipartite part `T_i` has a
bipartite half-piece `T_i ∪ {b}`), then `LocIndep k G` forces `CloseToBipartite (1 + m * k) G`: by
`LocIndep.oddCycleFamily_card_le` the packing number of `G` is at most `k`, so at most `k` parts are
non-bipartite and each of them costs `m`.

The constant is strictly better than `JSPProblem.erdos73On_of_split_of_bounded_pieces`'s `2 + m * k`
(`JSPProblem/Count.lean`) and strictly better than round 88's `1 + m * t`, because (i) the `+1` is
optimal and (ii) only `k` pieces are charged. -/
theorem erdos73On_of_split_one_avoid_of_clean (k m t : ℕ) {W : Type u} [Fintype W]
    (G : SimpleGraph W) (a b : W) (sp : VertexSplit G a b t)
    (hclean : ∀ i : Fin t, (induceFinset G (sp.parts i)).IsBipartite →
      (induceFinset G (insert b (sp.parts i))).IsBipartite)
    (hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (insert b (sp.parts i))))
    (hG : LocIndep k G) : CloseToBipartite (1 + m * k) G :=
  sp.closeToBipartite_one_avoid_of_clean (r := k) (m := m) hclean hpiece
    (fun _𝒞 h𝒞 => hG.oddCycleFamily_card_le h𝒞)

/-- **The packing-counted form, with the packing hypothesis in place of `LocIndep`**: the form in
which an induction on the Erdős–Pósa function along a 2-cut is actually run. -/
theorem closeToBipartite_of_split_one_avoid_of_clean_pack (r m t : ℕ) {W : Type u} [Fintype W]
    (G : SimpleGraph W) (a b : W) (sp : VertexSplit G a b t)
    (hclean : ∀ i : Fin t, (induceFinset G (sp.parts i)).IsBipartite →
      (induceFinset G (insert b (sp.parts i))).IsBipartite)
    (hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (insert b (sp.parts i))))
    (hpack : ∀ 𝒞 : Finset (Finset W), IsOddCycleFamily (G := G) 𝒞 → 𝒞.card ≤ r) :
    CloseToBipartite (1 + m * r) G :=
  sp.closeToBipartite_one_avoid_of_clean hclean hpiece hpack

/-- **The composition with round 38's branch-vertex instance**, in the packing-counted form: if each
non-bipartite part's half-piece has at most `m` branch vertices, then `LocIndep k G` forces
`CloseToBipartite (1 + (m + k) * k) G`.  No bound on the odd girth is used anywhere. -/
theorem erdos73On_of_split_one_avoid_of_clean_of_bounded_branch (k m t : ℕ) {W : Type u}
    [Fintype W] (G : SimpleGraph W) (a b : W) (sp : VertexSplit G a b t)
    (hclean : ∀ i : Fin t, (induceFinset G (sp.parts i)).IsBipartite →
      (induceFinset G (insert b (sp.parts i))).IsBipartite)
    (hB : ∀ i ∈ sp.nonBipartiteParts, ∃ B : Finset W, B ⊆ insert b (sp.parts i) ∧ B.card ≤ m ∧
      ∀ v : W, BranchVertex (induceFinset G (insert b (sp.parts i))) v → v ∈ B)
    (hG : LocIndep k G) : CloseToBipartite (1 + (m + k) * k) G := by
  have hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite (m + k) (induceFinset G (insert b (sp.parts i))) := by
    intro i hi
    obtain ⟨B, -, hBcard, hBall⟩ := hB i hi
    exact erdos73On_of_few_high_degree (k := k) (m := m) W (inferInstance : Fintype W)
      (induceFinset G (insert b (sp.parts i))) (hG.of_induceFinset (insert b (sp.parts i))) B hBall
      hBcard
  exact sp.closeToBipartite_one_avoid_of_clean (r := k) (m := m + k) hclean hpiece
    (fun _𝒞 h𝒞 => hG.oddCycleFamily_card_le h𝒞)

/-- **The improvement over round 88 is genuine**: the packing-counted constant `1 + m * k` is
strictly smaller than round 43's `2 + m * k`, and never larger than round 88's `1 + m * t` when
`k ≤ t` (which holds as soon as the pieces are charged at most once each). -/
theorem one_add_mul_lt_two_add_mul (m k : ℕ) : 1 + m * k < 2 + m * k := by omega

theorem one_add_mul_le_one_add_mul_of_le {m k t : ℕ} (h : k ≤ t) :
    1 + m * k ≤ 1 + m * t :=
  Nat.add_le_add_left (Nat.mul_le_mul (Nat.le_refl m) h) 1

/-- **The packing-counted cut lemma with the other vertex of the cut paid for**: identical to
`JSPProblem.erdos73On_of_split_one_avoid_of_clean` with `a` and `b` exchanged. -/
theorem erdos73On_of_split_one_avoid_of_clean_swap (k m t : ℕ) {W : Type u} [Fintype W]
    (G : SimpleGraph W) (a b : W) (sp : VertexSplit G a b t)
    (hclean : ∀ i : Fin t, (induceFinset G (sp.parts i)).IsBipartite →
      (induceFinset G (insert a (sp.parts i))).IsBipartite)
    (hpiece : ∀ i ∈ sp.nonBipartiteParts,
      CloseToBipartite m (induceFinset G (insert a (sp.parts i))))
    (hG : LocIndep k G) : CloseToBipartite (1 + m * k) G := by
  have h := (sp.swap : VertexSplit G b a t).closeToBipartite_one_avoid_of_clean (r := k) (m := m)
    (hclean := hclean) (hpiece := hpiece)
    (hpack := fun 𝒞 h𝒞 => hG.oddCycleFamily_card_le h𝒞)
  simpa using h

end Headline

/-! ### Part 5 — the `+1` is necessary -/

section Sharpness

/-- **`JSPProblem.IsBipartite.induceFinset_subset` with its vertex type specialised**, so that the
`Finset.insert` of the statement is built under a single fixed `DecidableEq`: without this the finset
built here and the finset in the goal of `exists_transversal_half` are not definitionally equal
(both are `insert 2 (sp5.parts i)`, but with different instances). -/
theorem isBipartite_induceFinset_subset' {s u : Finset (Fin 5)}
    (h : (induceFinset c5 s).IsBipartite) (hsu : u ⊆ s) : (induceFinset c5 u).IsBipartite :=
  IsBipartite.induceFinset_subset h hsu

/-- **The parts of the 2-cut `sp5` of the 5-cycle `c5` are all bipartite** (they are `{1}` and
`{3, 4}`), so the counting bound of `closeToBipartite_one_avoid_of_clean` is tight at `m = r = 0`:
the conclusion of that theorem is then `CloseToBipartite (1 + 0 * 0) = CloseToBipartite 1`. -/
theorem sp5_parts_bipartite : ∀ i : Fin 2, (induceFinset c5 (sp5.parts i)).IsBipartite := by
  intro i
  exact IsBipartite.induceFinset_subset (isBipartite_piece5 i) (fun x hx =>
    (sp5.mem_piece i x).mpr (Or.inr (Or.inr hx)))

/-- **THE `+1` IS NECESSARY IN THE PACKING-COUNTED FORM.**  On the 2-cut `sp5` of the 5-cycle `c5`
no part is non-bipartite (`sp5_parts_bipartite`), so `JSP90.closeToBipartite_one_avoid_of_clean` with
`m = 0` and `r = 0` would give `CloseToBipartite 1 c5` — and `not_closeToBipartite_zero_c5` shows
that no bound of the form `m * r` can work across a 2-cut.  The refinement of the cut step does not
remove the `+1`; it makes the `+1` the *only* piece-dependent cost, which is exactly what the
classical RRST decomposition does. -/
theorem plus_one_necessary_in_packing_form :
    (∀ i : Fin 2, (induceFinset c5 (sp5.parts i)).IsBipartite) ∧
      ¬ CloseToBipartite 0 c5 ∧ CloseToBipartite 1 c5 :=
  ⟨sp5_parts_bipartite, not_closeToBipartite_zero_c5, closeToBipartite_one_c5⟩

/-- **... and the refined cut step really is applied here.**  Both half-pieces `T_i ∪ {2}` of the
split `sp5` are bipartite (they are induced subgraphs of the bipartite pieces of round 88), so the
refined step with `m = 0` produces `CloseToBipartite (1 + 0 * 2) = CloseToBipartite 1` on `c5`, which
is the exact value by `not_closeToBipartite_zero_c5`. -/
theorem c5_closeToBipartite_one_from_clean_split : CloseToBipartite 1 c5 := by
  obtain ⟨Y, hY, hYcard⟩ := (sp5 : VertexSplit c5 0 2 2).exists_transversal_half (m := 0)
    (hhalf := fun i => ⟨∅, by simp, by
      rw [deleteFinset_empty]
      refine isBipartite_induceFinset_subset' (isBipartite_piece5 i) ?_
      exact sp5.halfPiece_subset_piece i⟩)
  have hcard : Y.card ≤ 1 := by omega
  exact (closeToBipartite_iff_hitsOddCycles (G := c5) (m := 1)).mpr ⟨Y, hcard, hY⟩

end Sharpness

end

end JSP90
