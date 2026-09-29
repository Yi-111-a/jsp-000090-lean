/-
# JSP-000090 — the 2-cut decomposition of the odd cycle transversal

`JSPProblem/Transversal.lean` reduced the whole of Erdős Problem #73 (Reed 1999, *Mangoes and
Blueberries*, Combinatorica 19 (1999) 267–296) to the single research statement
`OddCycleErdosPosa r`, and `JSPProblem/Packing.lean` proved the packing half of it.  The local
structure of `G` at a shortest odd cycle is available (`JSPProblem/Fan.lean`,
`JSPProblem/Chord.lean`), and the residue induction step is available
(`JSPProblem/Residue.lean`), but both of those need one *global* tool which this development does
not have: **the decomposition of `G` along a small separator**.

This file is that tool, and it is a fourth independent attack family.  It is the backbone of every
classical proof of the Erdős–Pósa property for odd cycles: the difficulty of the theorem is
entirely concentrated in the graphs with *no* 2-cut, i.e. in the 3-connected case.

The statement, in the vocabulary of this development, is that `V(G)` splits as

```
V = {a, b} ⊔ T₁ ⊔ … ⊔ T_t      (t ≥ 2,  the T_i pairwise anticomplete)
```

which is exactly "`G - {a,b}` is a disjoint union of `t ≥ 2` induced subgraphs with no edges
between them", i.e. `{a, b}` is a vertex cut.  It is formalised *without* any connectivity API
(none of it is in the pinned import slice): a split is a partition of `V \ {a, b}` into `t`
nonempty pairwise anticomplete parts (`VertexSplit`).  What is proved:

* **`VertexSplit.cycle_subset_parts`** — a cycle of `G` which avoids the two vertices of the cut
  lies in a *single* part.  Consequently every odd cycle of `G` either lies in one *piece*
  (`T_i ∪ {a, b}`) or meets the cut (`VertexSplit.oddCycle_piece_or_avoid`): **an odd cycle cannot
  use two parts at once**.  This is what makes a transversal of the pieces a transversal of `G`.
* **`VertexSplit.hitsOddCycles` / `VertexSplit.exists_transversal` / `erdos73On_of_split`** — the
  transversal and the conclusion of Erdős #73 are *additive* over a 2-cut, up to the two vertices
  of the cut.  `erdos73On_of_split` is a **new instance of the headline theorem**: if Erdős #73
  holds with the constant `m` on a class of graphs, it holds on the class of graphs admitting such
  a split, with the constant `m * t + 2`.  This is the reduction "the theorem reduces to the
  3-connected case", and it is the step an induction on the Erdős–Pósa function has to make.
* **`VertexSplit.part_unique` / `oddCycle_piece_unique`** — an odd cycle which avoids the cut lies
  in **exactly one** piece, which is the bookkeeping an Erdős–Pósa argument along a separator needs
  in order to charge each cycle to a single piece.
* **`VertexSplit.isBipartite_of_split`** — the *parity* form of the same decomposition: if every
  piece is bipartite and in every piece the two vertices of the cut lie in the **same** class, then
  `G` is bipartite.  Equivalently (**`VertexSplit.not_isBipartite_of_split`**): if `G` is not
  bipartite and every piece is bipartite, then no 2-colouring of the pieces can agree on `a` and
  `b` — `G` is glued along the cut only.  This is the classical 2-cut parity lemma, and it is the
  reason a 3-connected non-bipartite graph is the hard case of the theorem.
* **`packing_le_of_split`** — the *packing* half: the Erdős–Pósa hypothesis (a bound on the odd
  cycle packing number) restricts to every piece, so an induction along a 2-cut decomposition goes
  through.
* **`erdos73On_of_split_of_bounded_branch`** — a **second new instance of the headline theorem**,
  obtained by composing `erdos73On_of_split` with the branch-vertex instance of
  `JSPProblem/Branch.lean`: if `G` has a 2-cut whose `t` pieces have at most `m` branch vertices
  each, then `LocIndep k G` forces `CloseToBipartite (2 + (m + k) * t) G`, still with **no bound
  on the odd girth**.

What this does *not* give: the two vertices of the cut are charged in full (`+ 2`), whereas the
sharp step would charge only one of them (that needs the "a cycle meeting exactly one vertex of
the cut lies in a piece" companion of `cycle_subset_parts`); the packing half is only the
restriction of the bound to the pieces, not the full decomposition `card ≤ 2 + t * r`; and the
theorem is only reduced to the 3-connected case, whose Erdős–Pósa statement is still the blocker.
See `discovery/JSP-000090/policy.json`.
-/

import JSPProblem.Residue
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqSplit : DecidableEq V := Classical.decEq V

/-! ### A 2-cut split -/

section VertexSplit

/-- A **2-cut split** of `G` at the pair of vertices `a, b` into `t` parts: every vertex of `G`
is either one of the two vertices of the cut or lies in one of the `t` nonempty parts, the parts
are pairwise disjoint, two distinct parts are **anticomplete** (no edge joins them), and `a`, `b`
are not adjacent.  Equivalently, `G - {a,b}` is a disjoint union of `t ≥ 2` induced subgraphs
with no edges between them, i.e. `{a, b}` is a vertex cut.

This is the standard object of the decomposition theory behind the proofs of the Erdős–Pósa
property for odd cycles.  It is stated directly, as a partition into anticomplete parts, so that
no connectivity API is needed. -/
structure VertexSplit (G : SimpleGraph V) (a b : V) (t : ℕ) where
  /-- the `t` parts of `V \ {a, b}` -/
  parts : Fin t → Finset V
  /-- no part is empty: the cut really separates `t ≥ 2` nonempty pieces -/
  hne : ∀ i : Fin t, (parts i).Nonempty
  /-- the parts are pairwise disjoint -/
  hdisj : ∀ i j : Fin t, i ≠ j → parts i ∩ parts j = ∅
  /-- the parts, together with the two vertices of the cut, exhaust the vertices of `G` -/
  hcov : ∀ x : V, x = a ∨ x = b ∨ (∃ i : Fin t, x ∈ parts i)
  /-- two distinct parts are anticomplete -/
  hanti : ∀ i j : Fin t, i ≠ j → ∀ x ∈ parts i, ∀ y ∈ parts j, ¬ G.Adj x y
  /-- the cut is *proper*: the two vertices of the cut are not adjacent, so two distinct pieces
  overlap in at most those two vertices -/
  hnadj : ¬ G.Adj a b

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **The piece at the part `i`**: the part together with the two vertices of the cut.  Every cycle
of `G` which avoids the cut is contained in a piece (`VertexSplit.oddCycle_piece_or_avoid`). -/
def VertexSplit.piece (sp : VertexSplit G a b t) (i : Fin t) : Finset V :=
  insert a (insert b (sp.parts i))

/-- The set built from a family of transversals of the pieces: their union together with the two
vertices of the cut. -/
def VertexSplit.cutSet (sp : VertexSplit G a b t) (X : Fin t → Finset V) : Finset V :=
  insert a (insert b (Finset.biUnion Finset.univ X))

@[simp] theorem VertexSplit.mem_piece (sp : VertexSplit G a b t) (i : Fin t) (x : V) :
    x ∈ sp.piece i ↔ x = a ∨ x = b ∨ x ∈ sp.parts i := by
  simp [VertexSplit.piece]

@[simp] theorem VertexSplit.mem_cutSet (sp : VertexSplit G a b t) (X : Fin t → Finset V)
    (x : V) : x ∈ sp.cutSet X ↔ x = a ∨ x = b ∨ (∃ i, x ∈ X i) := by
  simp only [cutSet, Finset.mem_insert]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp h
      exact Or.inr (Or.inr ⟨i, hxi⟩)
  · rintro (h | h | ⟨i, hxi⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hxi⟩))

/-- A vertex which is neither of the two vertices of the cut lies in some part. -/
theorem VertexSplit.mem_parts_of_not_mem_cut (sp : VertexSplit G a b t) (x : V)
    (ha : x ≠ a) (hb : x ≠ b) : ∃ i : Fin t, x ∈ sp.parts i := by
  rcases sp.hcov x with h | h | h
  · exact absurd h ha
  · exact absurd h hb
  · exact h

/-- **Neighbours stay in the same part**: if `x` lies in the part `i` and is adjacent to `y`, and
neither of them is a vertex of the cut, then `y` lies in the part `i` as well.  This is what makes
the parts behave like the connected components of `G - {a,b}`. -/
theorem VertexSplit.mem_part_of_adj (sp : VertexSplit G a b t) {x y : V} (hadj : G.Adj x y)
    {i : Fin t} (hi : x ∈ sp.parts i) (hx : x ≠ a) (hx' : x ≠ b) (hy : y ≠ a) (hy' : y ≠ b) :
    y ∈ sp.parts i := by
  obtain ⟨j, hj⟩ := sp.mem_parts_of_not_mem_cut y hy hy'
  by_cases hji : j = i
  · rwa [hji] at hj
  · exact absurd hadj.symm (sp.hanti j i hji y hj x hi)

end VertexSplit

/-! ### Odd cycles do not run through two parts -/

section Cycles

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- An odd cycle of an induced subgraph of `G` is an odd cycle of `G`. -/
theorem IsOddCycle.of_induceFinset [Fintype V] {s C : Finset V}
    (hC : IsOddCycle (induceFinset G s) C) : IsOddCycle G C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  refine ⟨m, f, hm, hm3, hinj, fun j => (induce_adj.mp (hcyc j)).2.2, hCmem⟩

/-- An odd cycle of `G` contained in `s` is an odd cycle of the induced subgraph `G[s]`. -/
theorem IsOddCycle.induceFinset [Fintype V] {s C : Finset V} (hC : IsOddCycle G C) (hsub : C ⊆ s) :
    IsOddCycle (induceFinset G s) C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  refine ⟨m, f, hm, hm3, hinj, fun j => ?_, hCmem⟩
  refine induce_adj.mpr ⟨?_, ?_, hcyc j⟩
  · exact hsub ((hCmem _).mpr ⟨j, rfl⟩)
  · exact hsub ((hCmem _).mpr ⟨cycSucc j, rfl⟩)

/-- **A cycle of `G` which avoids the two vertices of the cut lies in a single part.**

The proof walks once around the cycle: `g t = f (t mod m)` enumerates the vertices of the cycle in
cyclic order, consecutive ones are adjacent, and all of them avoid the cut.  Hence all of them lie
in the part of `g 0`, by `VertexSplit.mem_part_of_adj`. -/
theorem VertexSplit.cycle_subset_parts {C : Finset V} (hC : IsOddCycle G C)
    (hcut : C ∩ ({a, b} : Finset V) = ∅) : ∃ i : Fin t, C ⊆ sp.parts i := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hfx : ∀ j : Fin m, ¬ (f j ∈ ({a, b} : Finset V)) := by
    intro j hmem
    have hmemC : f j ∈ C := (hCmem (f j)).mpr ⟨j, rfl⟩
    have him : f j ∈ C ∩ ({a, b} : Finset V) := Finset.mem_inter.mpr ⟨hmemC, hmem⟩
    rw [hcut] at him
    exact absurd him (by simp)
  have hmod : ∀ s : ℕ, (s % m + 1) % m = (s + 1) % m := by
    intro s
    calc (s % m + 1) % m
        = ((s % m + 1) + m * (s / m)) % m := by rw [Nat.add_mul_mod_self_left]
      _ = (s + 1) % m := by
          have h2 : (s % m + 1) + m * (s / m) = s + 1 := by
            have h3 := Nat.mod_add_div s m
            omega
          rw [h2]
  let mk : ℕ → Fin m := fun t => ⟨t % m, Nat.mod_lt _ (by omega)⟩
  have hne : ∀ t : ℕ, f (mk t) ≠ a ∧ f (mk t) ≠ b := by
    intro t
    refine ⟨fun hcon => hfx (mk t) (by simp [hcon]), fun hcon => hfx (mk t) (by simp [hcon])⟩
  have hstep : ∀ t : ℕ, G.Adj (f (mk t)) (f (mk (t + 1))) := by
    intro t
    have h := hcyc (mk t)
    have hval : (t % m + 1) % m = (t + 1) % m := hmod t
    have heq : f (cycSucc (mk t)) = f (mk (t + 1)) := congrArg f (Fin.ext hval)
    rw [heq] at h
    exact h
  obtain ⟨i₀, hi₀⟩ := sp.mem_parts_of_not_mem_cut (f (mk 0)) (fun h => (hne 0).1 h)
    (fun h => (hne 0).2 h)
  have hmem_all : ∀ t : ℕ, f (mk t) ∈ sp.parts i₀ := by
    intro t
    induction t with
    | zero => exact hi₀
    | succ t ih =>
        have hne' := hne (t + 1)
        exact sp.mem_part_of_adj (hstep t) ih (hne t).1 (hne t).2 hne'.1 hne'.2
  refine ⟨i₀, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := (hCmem x).mp hx
  have hval : mk j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  exact hj ▸ (congrArg f hval ▸ hmem_all j.val)

/-- **Every odd cycle of `G` is contained in a piece, or meets the two vertices of the cut.**
This is the local half of the 2-cut decomposition: an odd cycle which stays away from the cut
cannot use two parts at once.  The only odd cycles of `G` which are not odd cycles of a piece are
the ones running through *both* `a` and `b` — the two "bridges" between the parts. -/
theorem VertexSplit.oddCycle_piece_or_avoid {C : Finset V} (hC : IsOddCycle G C) :
    (∃ i : Fin t, C ⊆ sp.piece i) ∨ C ∩ ({a, b} : Finset V) ≠ ∅ := by
  by_cases hcut : C ∩ ({a, b} : Finset V) = ∅
  · obtain ⟨i, hi⟩ := sp.cycle_subset_parts hC hcut
    refine Or.inl ⟨i, fun x hx => ?_⟩
    exact (sp.mem_piece i x).mpr (Or.inr (Or.inr (hi hx)))
  · exact Or.inr hcut

/-- **The part of a cycle which avoids the cut is unique.**  Two parts of a split are disjoint, so a
cycle which avoids the two vertices of the cut cannot be contained in two of them. -/
theorem VertexSplit.part_unique {C : Finset V} (hC : IsOddCycle G C)
    (hcut : C ∩ ({a, b} : Finset V) = ∅) {i j : Fin t} (hi : C ⊆ sp.parts i) (hj : C ⊆ sp.parts j) :
    i = j := by
  by_contra hij
  obtain ⟨x, hx⟩ := hC.nonempty
  have hx' : x ∈ sp.parts i ∩ sp.parts j := Finset.mem_inter.mpr ⟨hi hx, hj hx⟩
  rw [sp.hdisj i j hij] at hx'
  exact absurd hx' (by simp)

/-- **An odd cycle of `G` which avoids the two vertices of a 2-cut lies in *exactly one* piece.**
Uniqueness is what lets an odd cycle be charged to a single piece, which is the bookkeeping an
Erdős–Pósa argument along a separator needs. -/
theorem VertexSplit.oddCycle_piece_unique {C : Finset V} (hC : IsOddCycle G C)
    (hcut : C ∩ ({a, b} : Finset V) = ∅) : ∃! i : Fin t, C ⊆ sp.piece i := by
  have hne : ∀ x : V, x ∈ C → x ≠ a ∧ x ≠ b := by
    intro x hx
    constructor
    · intro hcon
      have him : x ∈ C ∩ ({a, b} : Finset V) := by
        refine Finset.mem_inter.mpr ⟨hx, ?_⟩
        rw [hcon]
        exact Finset.mem_insert.mpr (Or.inl rfl)
      rw [hcut] at him
      exact absurd him (by simp)
    · intro hcon
      have him : x ∈ C ∩ ({a, b} : Finset V) := by
        refine Finset.mem_inter.mpr ⟨hx, ?_⟩
        rw [hcon]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self b))
      rw [hcut] at him
      exact absurd him (by simp)
  obtain ⟨i, hi⟩ := sp.cycle_subset_parts hC hcut
  refine ⟨i, fun x hx => (sp.mem_piece i x).mpr (Or.inr (Or.inr (hi hx))), ?_⟩
  intro j hj
  have hj' : C ⊆ sp.parts j := by
    intro x hx
    rcases (sp.mem_piece j x).mp (hj hx) with h | h | h
    · exact False.elim (absurd h ((hne x hx).1))
    · exact False.elim (absurd h ((hne x hx).2))
    · exact h
  exact sp.part_unique hC hcut hj' hi

end Cycles

/-! ### Transversals are additive over a 2-cut -/

section Transversal

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **A set meeting every odd cycle of every piece, together with the two vertices of the cut, is
an odd cycle transversal of `G`.**  This is the global half of the 2-cut decomposition, and the
reason the Erdős–Pósa statement is closed under cutting along a 2-cut. -/
theorem VertexSplit.hitsOddCycles [Fintype V] (X : Fin t → Finset V)
    (hhits : ∀ i : Fin t, HitsOddCycles (induceFinset G (sp.piece i)) (X i)) :
    HitsOddCycles G (sp.cutSet X) := by
  intro C hC
  rcases sp.oddCycle_piece_or_avoid hC with ⟨i, hsub⟩ | hne
  · have hC' : IsOddCycle (induceFinset G (sp.piece i)) C := hC.induceFinset hsub
    have hne' : (C ∩ X i).Nonempty := Finset.nonempty_iff_ne_empty.mpr (hhits i C hC')
    obtain ⟨x, hx⟩ := hne'
    have hxC : x ∈ C := (Finset.mem_inter.mp hx).1
    have hxX : x ∈ X i := (Finset.mem_inter.mp hx).2
    have hmem : x ∈ C ∩ sp.cutSet X :=
      Finset.mem_inter.mpr ⟨hxC, (sp.mem_cutSet X x).mpr (Or.inr (Or.inr ⟨i, hxX⟩))⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨x, hmem⟩
  · have hne' : (C ∩ ({a, b} : Finset V)).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨x, hx⟩ := hne'
    have hxC : x ∈ C := (Finset.mem_inter.mp hx).1
    have hxab : x ∈ ({a, b} : Finset V) := (Finset.mem_inter.mp hx).2
    have hxab' : x = a ∨ x = b := by
      rcases Finset.mem_insert.mp hxab with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    have hxab'' : x = a ∨ x = b ∨ (∃ i : Fin t, x ∈ X i) := by
      rcases hxab' with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hmem : x ∈ C ∩ sp.cutSet X :=
      Finset.mem_inter.mpr ⟨hxC, (sp.mem_cutSet X x).mpr hxab''⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨x, hmem⟩

/-- **A 2-cut decomposition of odd cycle transversals.**  If each piece `T_i ∪ {a,b}` has an odd
cycle transversal of at most `m` vertices, then `G` has an odd cycle transversal of at most
`2 + m * t` vertices: one transversal per piece, plus the two vertices of the cut. -/
theorem VertexSplit.exists_transversal [Fintype V] {m : ℕ} (X : Fin t → Finset V)
    (hhits : ∀ i : Fin t, HitsOddCycles (induceFinset G (sp.piece i)) (X i))
    (hcard : ∀ i : Fin t, (X i).card ≤ m) :
    ∃ Y : Finset V, HitsOddCycles G Y ∧ Y.card ≤ 2 + m * t := by
  refine ⟨sp.cutSet X, sp.hitsOddCycles X hhits, ?_⟩
  have ha : (insert a (insert b (Finset.biUnion Finset.univ X)) : Finset V).card
      ≤ (insert b (Finset.biUnion Finset.univ X) : Finset V).card + 1 :=
    Finset.card_insert_le a _
  have hb : (insert b (Finset.biUnion Finset.univ X) : Finset V).card
      ≤ (Finset.biUnion Finset.univ X).card + 1 := Finset.card_insert_le b _
  have h1 : (sp.cutSet X).card ≤ (Finset.biUnion Finset.univ X).card + 2 := by
    unfold cutSet
    omega
  have h2 : (Finset.biUnion Finset.univ X).card ≤ ∑ i : Fin t, (X i).card :=
    Finset.card_biUnion_le
  have h3 : (∑ i : Fin t, (X i).card) ≤ ∑ _i : Fin t, (m : ℕ) :=
    Finset.sum_le_sum fun i hi => hcard i
  have h4 : (∑ _i : Fin t, (m : ℕ)) = m * t := by
    calc (∑ _i : Fin t, (m : ℕ)) = (Finset.univ : Finset (Fin t)).card * m := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rfl
      _ = m * t := by rw [Finset.card_fin, Nat.mul_comm]
  have h5 : (Finset.biUnion Finset.univ X).card + 2 ≤ m * t + 2 := by
    have h6 : (Finset.biUnion Finset.univ X).card ≤ m * t :=
      h2.trans (h3.trans (le_of_eq h4))
    omega
  have h7 : m * t + 2 = 2 + m * t := Nat.add_comm _ _
  exact h1.trans (h5.trans h7.le)

/-- **A new instance of the headline theorem: Erdős Problem #73 is closed under 2-cut
decomposition.**  Suppose `V(G)` splits as `{a, b} ⊔ T₁ ⊔ … ⊔ T_t` with the parts pairwise
anticomplete, and suppose Erdős's local hypothesis `LocIndep k` forces `CloseToBipartite m` in
every class of graphs in which it is assumed — here: in the pieces `T_i ∪ {a,b}`, which is exactly
what an induction on the Erdős–Pósa function needs.  Then `LocIndep k G` forces
`CloseToBipartite (m * t + 2) G`: a transversal of every piece, together with the two vertices of
the cut, is a transversal of `G`.

This is a *reduction*, not the theorem: it says that everything in the Erdős–Pósa proof happens
in graphs with **no** 2-cut.  Together with `VertexSplit.not_isBipartite_of_split` below it is the
exact place where the remaining difficulty of `OddCycleErdosPosa` is concentrated. -/
theorem erdos73On_of_split (k m t : ℕ) [Fintype V] (sp : VertexSplit G a b t)
    (hpiece : ∀ i : Fin t, LocIndep k (induceFinset G (sp.piece i)) →
      CloseToBipartite m (induceFinset G (sp.piece i)))
    (hG : LocIndep k G) : CloseToBipartite (m * t + 2) G := by
  have hLoc : ∀ i : Fin t, LocIndep k (induceFinset G (sp.piece i)) :=
    fun i => hG.of_induceFinset (sp.piece i)
  obtain ⟨X, hX, hhits⟩ := sp.exists_transversal (m := m)
    (X := fun i => Classical.choose (hpiece i (hLoc i)))
    (fun i => hitsOddCycles_of_isBipartite_delete ((hpiece i (hLoc i)).choose_spec.2))
    (fun i => (hpiece i (hLoc i)).choose_spec.1)
  have hcard' : X.card ≤ m * t + 2 := by omega
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := m * t + 2)).mpr ⟨X, hcard', hX⟩

end Transversal

/-! ### Bipartiteness is additive over a 2-cut: the 2-cut parity lemma -/

section Parity

/-- `c` is a proper 2-colouring of the whole graph `G` (with the codomain `Bool`). -/
def Good2 (G : SimpleGraph V) (c : V → Bool) : Prop := ∀ ⦃x y : V⦄, G.Adj x y → c x ≠ c y

/-- `c` is a proper 2-colouring of the subgraph of `G` induced by the vertex set `s`. -/
def Good2On (G : SimpleGraph V) (c : V → Bool) (s : Finset V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ s → y ∈ s → G.Adj x y → c x ≠ c y

/-- **Rescaling a 2-colouring at one vertex.**  `flipCol c u v` is `c v` flipped exactly when
`c v = c u`, so it is a 2-colouring again, and it sends `u` — and every vertex coloured like `u` —
to `false`.  This is the operation which makes the two vertices of a 2-cut comparable. -/
def flipCol (c : V → Bool) (u : V) : V → Bool := fun v => if c v = c u then false else true

theorem Good2On.flip {c : V → Bool} {s : Finset V} (h : Good2On G c s) (u : V) :
    Good2On G (flipCol c u) s := by
  intro x y hx hy hadj
  have hc : c x ≠ c y := h hx hy hadj
  by_cases hx' : c x = c u
  · have hy' : c y ≠ c u := fun hxy => hc (hx'.trans hxy.symm)
    simp [flipCol, hx', hy']
  · have hy' : c y = c u := by
      by_contra hne
      cases hcy : c y <;> cases hcu : c u <;> simp_all
    simp [flipCol, hx', hy']

theorem Good2On.of_induceFinset [Fintype V] {c : V → Bool} {s : Finset V}
    (h : Good2On (induceFinset G s) c s) : Good2On G c s := by
  intro x y hx hy hadj
  exact h hx hy (induce_adj.mpr ⟨hx, hy, hadj⟩)

/-- A proper 2-colouring, in the `Bool` convention, is a 2-colouring in Mathlib's. -/
theorem Good2.isBipartite {c : V → Bool} (h : Good2 G c) : G.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if c v then (1 : Fin 2) else 0) ?_⟩
  intro x y hadj
  have hne : c x ≠ c y := h hadj
  cases hcx : c x <;> cases hcy : c y
  · exact absurd (hne (hcx.trans hcy.symm)) (by decide)
  · simp
  · simp
  · exact absurd (hne (hcx.trans hcy.symm)) (by decide)

/-- **A bipartite graph has a 2-colouring in the `Bool` convention**: the one side `true`, the
other `false`. -/
theorem exists_good2 (h : G.IsBipartite) : ∃ c : V → Bool, Good2 G c := by
  classical
  obtain ⟨s, t, hb⟩ := SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mp h
  refine ⟨fun v => if v ∈ s then false else true, ?_⟩
  intro x y hadj
  rcases hb.mem_of_adj hadj with h | h
  · have hxs : x ∈ s := h.1
    have hys : ¬ (y ∈ s) := fun hys => Set.disjoint_left.mp hb.disjoint hys h.2
    simp [hxs, hys]
  · have hxt : ¬ (x ∈ s) := fun hxt => Set.disjoint_left.mp hb.disjoint hxt h.1
    have hys : y ∈ s := h.2
    simp [hxt, hys]

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **The 2-cut parity lemma.**  If every piece `T_i ∪ {a,b}` admits the same 2-colouring `c`, and
`c` agrees on the two vertices `a` and `b` of the cut, then `G` is bipartite.

The colouring is glued from the pieces: two distinct parts are anticomplete, so their colours never
interfere, and the two vertices of the cut are the only vertices two pieces can share, so it
suffices that they carry the same colour.  This is the classical parity statement behind every
decomposition of a graph along a small separator. -/
theorem VertexSplit.isBipartite_of_split (c : V → Bool)
    (hc : ∀ i : Fin t, Good2On G c (sp.piece i)) (hca : c a = c b) : G.IsBipartite := by
  have hd : ∀ i : Fin t, Good2On G (flipCol c a) (sp.piece i) := fun i => (hc i).flip a
  have hcutval : ∀ u : V, u = a ∨ u = b → flipCol c a u = false := by
    intro u hu
    rcases hu with rfl | rfl
    · simp [flipCol]
    · simp [flipCol, hca]
  refine Good2.isBipartite (c := flipCol c a) ?_
  intro x y hadj
  by_cases hxc : x = a ∨ x = b
  · by_cases hyc : y = a ∨ y = b
    · rcases hxc with hx' | hx'
      · rcases hyc with hy' | hy'
        · rw [hx', hy'] at hadj
          exact (G.irrefl hadj).elim
        · rw [hx', hy'] at hadj
          exact (sp.hnadj hadj).elim
      · rcases hyc with hy' | hy'
        · rw [hx', hy'] at hadj
          exact (sp.hnadj hadj.symm).elim
        · rw [hx', hy'] at hadj
          exact (G.irrefl hadj).elim
    · obtain ⟨i, hyi⟩ := sp.mem_parts_of_not_mem_cut y (fun h => hyc (Or.inl h))
        (fun h => hyc (Or.inr h))
      have hxmem : x ∈ sp.piece i := by
        rcases hxc with hx' | hx'
        · exact (sp.mem_piece i x).mpr (Or.inl hx')
        · exact (sp.mem_piece i x).mpr (Or.inr (Or.inl hx'))
      have h1 := hd i hxmem ((sp.mem_piece i y).mpr (Or.inr (Or.inr hyi))) hadj
      rw [hcutval x hxc] at h1 ⊢
      exact h1
  · by_cases hyc : y = a ∨ y = b
    · obtain ⟨i, hxi⟩ := sp.mem_parts_of_not_mem_cut x (fun h => hxc (Or.inl h))
        (fun h => hxc (Or.inr h))
      have hymem : y ∈ sp.piece i := by
        rcases hyc with hy' | hy'
        · exact (sp.mem_piece i y).mpr (Or.inl hy')
        · exact (sp.mem_piece i y).mpr (Or.inr (Or.inl hy'))
      have h1 := hd i ((sp.mem_piece i x).mpr (Or.inr (Or.inr hxi))) hymem hadj
      rw [hcutval y hyc] at h1 ⊢
      exact h1
    · obtain ⟨i, hxi⟩ := sp.mem_parts_of_not_mem_cut x (fun h => hxc (Or.inl h))
        (fun h => hxc (Or.inr h))
      obtain ⟨j, hyj⟩ := sp.mem_parts_of_not_mem_cut y (fun h => hyc (Or.inl h))
        (fun h => hyc (Or.inr h))
      by_cases hij : i = j
      · have h1 := hd i ((sp.mem_piece i x).mpr (Or.inr (Or.inr hxi)))
          ((sp.mem_piece i y).mpr (Or.inr (Or.inr (hij ▸ hyj)))) hadj
        exact h1
      · exact (sp.hanti i j hij x hxi y hyj hadj).elim

/-- **The 2-cut parity lemma, contraposed**: if `G` is not bipartite and every piece of the split
admits *one* 2-colouring `c`, then `c` separates `a` from `b` in that piece — no 2-colouring of
the pieces can agree on the two vertices of the cut.  This is the structural reason why a
3-connected non-bipartite graph (no 2-cut at all) is the hard case of the Erdős–Pósa property. -/
theorem VertexSplit.not_isBipartite_of_split (c : V → Bool)
    (hc : ∀ i : Fin t, Good2On G c (sp.piece i)) (hnb : ¬ G.IsBipartite) : c a ≠ c b := by
  by_contra hcon
  exact hnb (sp.isBipartite_of_split c hc hcon)

end Parity

/-! ### The packing half of the decomposition -/

section Packing

variable {a b : V} {t : ℕ} (sp : VertexSplit G a b t)

/-- **An odd cycle family of an induced subgraph is an odd cycle family of `G`**: the finsets are
the same, they are still pairwise vertex-disjoint, and their cycles are odd cycles of `G`. -/
theorem IsOddCycleFamily.of_induceFinset [Fintype V] {s : Finset V} {C : Finset (Finset V)}
    (hC : IsOddCycleFamily (G := induceFinset G s) C) : IsOddCycleFamily (G := G) C :=
  ⟨hC.1, fun D hD => (hC.2 D hD).of_induceFinset⟩

/-- **The odd cycle packing bound restricts to every piece of a split.**  If every packing of odd
cycles of `G` has at most `r` members, then so does every packing of odd cycles of a piece — the
hypothesis of the Erdős–Pósa induction (`OddCycleErdosPosa`) therefore restricts along a 2-cut
decomposition, which is what makes the induction on the pieces of `erdos73On_of_split` go through. -/
theorem packing_le_of_split [Fintype V] {r : ℕ}
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r) (i : Fin t)
    {C : Finset (Finset V)} (hC : IsOddCycleFamily (G := induceFinset G (sp.piece i)) C) :
    C.card ≤ r :=
  hpack C hC.of_induceFinset

/-- **A new instance of the headline theorem, obtained by composing `erdos73On_of_split` with
`erdos73On_of_few_high_degree` of round 38.**  Suppose `V(G)` splits as
`{a, b} ⊔ T₁ ⊔ … ⊔ T_t` with the parts pairwise anticomplete, and suppose every piece has at most
`m` branch vertices (three pairwise distinct neighbours).  Then Erdős's local hypothesis
`LocIndep k G` forces `CloseToBipartite (2 + (m + k) * t) G`: each piece is `m + k` vertices away
from bipartite, and a transversal of the pieces, together with the two vertices of the cut, is a
transversal of `G`.

As in round 38, there is **no bound on the odd girth** here: the two hypotheses are the two
independent structural bounds of this development, and this theorem is their composition across a
vertex cut. -/
theorem erdos73On_of_split_of_bounded_branch (k m t : ℕ) [Fintype V] (sp : VertexSplit G a b t)
    (hB : ∀ i : Fin t, ∃ B : Finset V, B ⊆ sp.piece i ∧ B.card ≤ m ∧
      ∀ v : V, BranchVertex (induceFinset G (sp.piece i)) v → v ∈ B)
    (hG : LocIndep k G) : CloseToBipartite (2 + (m + k) * t) G := by
  have hpiece : ∀ i : Fin t, LocIndep k (induceFinset G (sp.piece i)) →
      CloseToBipartite (m + k) (induceFinset G (sp.piece i)) := by
    intro i hLoc
    obtain ⟨B, -, hBcard, hBall⟩ := hB i
    exact erdos73On_of_few_high_degree (k := k) (m := m) V (inferInstance : Fintype V)
      (induceFinset G (sp.piece i)) hLoc B hBall hBcard
  have h := erdos73On_of_split (k := k) (m := m + k) (t := t) sp hpiece hG
  simpa [Nat.add_comm] using h

end Packing

end
