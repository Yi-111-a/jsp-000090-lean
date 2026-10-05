import JSPProblem.TriResidue

/-!
# JSP-000090, round 171 — `JSPProblem/TriEight.lean`: **THE EIGHT-VERTEX TRANSFER, PROVED**

Attack family 92 (the EIGHT-VERTEX INSTANCE).  Rounds 167–168 proved the counting step of the
eight-vertex triangle case (`lean/JSPProblem/TriFiveLang.lean` + `JSPProblem/TriFive.lean`, the
theorem `JSP90.loc8_lemma`, over a five-point residue `K_{2,3}`) and the bridge that every triangle
has a bipartite residue (`JSPProblem/TriResidue.lean`, with no bound on the order at all).  Round 170
built the `Fin 8` transfer machinery and left the transfer itself (`JSP90.triCaseEight`) uncompiled.
**This round repairs the four tactic steps round 170 named, installs the transfer, and derives the
first instance of the headline theorem at order eight.**

## What this file is

**THE `Fin 8` TRANSFER, COMPLETE**: every reading of the language of
`lean/JSPProblem/TriFiveLang.lean` that a transfer of a graph into it needs, in both directions (each
of them a statement over `Fin` types only, so `decide` or `Nat`-arithmetic closes it), **and** the
transfer itself:

```lean
JSP90.triCaseEight (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 8) {T : Finset V}
    (hT : G.IsNClique 3 T) : ∃ t ∈ T, (deleteFinset G (T \ {t})).IsBipartite
```

and, in Part 2, the consequence

```lean
JSP90.closeToBipartite_two_of_shortest_three_of_locIndep_one_card_le_eight
    LocIndep 1 G → |V| ≤ 8 → (a shortest odd cycle C of G has C.card = 3) → CloseToBipartite 2 G
```

with its transversal and `tauOdd` forms.  `#print axioms` on every theorem of this file reports only
`[propext, Classical.choice, Quot.sound]`.

### The four repairs of round 170

1. **`JSP90.card_six_inv` / `JSP90.mem_six_inv`.**  The finset equalities are now closed by `simp`
   (`Finset.mem_image` distributes over `Finset.mem_insert`), and the six branches are built by hand.
2. **`JSP90.hxpt_inj`.**  The case split must precede any `obtain ⟨iv, _⟩ := i`, which *deletes* the
   name `i`; and in the last branch one needs the values of the indices, not `omega` on an
   injectivity that is what one is proving.  The repair is `JSP90.hxpt_val`, the if-chain read off at
   an index, after which `rw [hi, hj] at hij'` matches the literals.
3. **The reading `JSP90.hsT`.**  `JSP90.sBit_maskOf` is stated with `sBit = decide (s.testBit _ = true)`,
   so it must be lifted back to `Nat.testBit` by `JSP90.decide_eq_true_of_bool` — the three-step form
   of round 170's note.
4. **The badness transfer.**  `crossM` is not `adj8n` syntactically, so
   `JSP90.crossM_of_adj8n` (new here) is the bridge, and the two `hAdj` steps use `rw [hk]`.

### One further obstruction, found by the 64-case correspondence and fixed here

`Nat.testBit_zero` is `@[simp]` and is *more specific* than `JSP90.cellsOf_bit_nat`, so `simp` reduces
bit `0` of the cells to `(cellsOf w).val % 2 = 1` before the reading can fire — two of the sixty-four
cases could not be closed.  The fix is `JSP90.hmod0`, the same statement in the modulus form, plus
`JSP90.hwAll` (the six cell values in one hypothesis), which is also what makes the `Fin`-literal
arguments of the other five cases match.

## Part 0 — the readings, all closed by `decide` or by `Nat`-arithmetic

`lean/JSPProblem/TriFiveLang.lean` packs the local structure into numbers: the six cells of `G[X]`
as the bits of `A : Fin 64` and each neighbour set as a mask `Fin 32`.  The transfer therefore has to
move data *through* the bits, and this file provides both directions:

* `JSP90.properM_get`, `JSP90.okMono_read`, `JSP90.meetBoth_read`, `JSP90.tripleEmpty_read`,
  `JSP90.crossM_split` — read a `Bool` of the language back into facts about the bits;
* `JSP90.maskOf`, `JSP90.cellsOf` with `JSP90.sBit_maskOf`, `JSP90.cellsOf_bit` — pack a `Bool`
  function of the graph into those numbers, with the two readings;
* `JSP90.exists_ind3n_of_hasInd3m`, `JSP90.ind3n_get`, `JSP90.ind3n_of_nadj`,
  `JSP90.noInd36_false_of_ind3n` — the bridge between the six-element subsets of
  `JSP90.hasInd3m` and the cheap form `JSP90.noInd36`;
* `JSP90.sort3`, `JSP90.card_six_inv`, `JSP90.mem_six_inv`, `JSP90.sixMaskOf`,
  `JSP90.sixMask_bit_true` — the vertex-set bookkeeping of the three six-element subsets.

Every statement of the first list quantifies only over `Fin` types, so `decide` closes them; that
is what keeps the bit arithmetic out of the proof.  **Two readings of the language are new and both
were checked by `decide` before use**, and one of them refutes the naive reading:

* `JSP90.okMono_read`: `okMono i s = true` says the neighbour set is **monochromatic**, and the
  statement records **which colour**.  The first version of this file stated the weaker (and
  **false**) "`{s} = 0` or all of its bits are set"; `decide` refuted it, and correctly:
  `i &&& s = 0` says that no point of the set carries the colour `true`, not that the set is empty.
* `JSP90.sixMaskOf`: the masks `231, 235, 243` of `JSP90.sixMasks` are **not** `231 + 4 * (r - 2)`
  (`231 + 8 = 239` keeps the bit of `2`, so `four` is wrong), which is why the arithmetic form is
  refused and `JSP90.sixMask_bit_true` is stated with `JSP90.sixMaskOf`.

## Part 1 — `JSP90.triCaseEight`, the transfer

See the docstring of `JSP90.triCaseEight`.  Behind it: the five- and seven-cycle cases at `|V| ≤ 8`,
which are still open, so `JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight` and
`jsp_000090_main` remain deliberately **not** declared.
-/

namespace JSP90

open Finset Fintype Set SimpleGraph

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

local instance t8Dec : DecidableEq V := Classical.decEq V

local instance t8Adj : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _

/-! ## Part 0 — the readings the transfer consumes, all closed by `decide`

`lean/JSPProblem/TriFiveLang.lean` packs the local structure into numbers: the six cells of `G[X]`
as the bits of `A : Fin 64` and each neighbour set as a mask `Fin 32`.  The transfer therefore has to
move data *through* the bits, and the two directions are:

* `JSP90.properM_get`, `JSP90.okMono_read`, `JSP90.meetBoth_read`, `JSP90.tripleEmpty_read` — read a
  `Bool` of the language back into facts about the bits;
* `JSP90.maskOf`, `JSP90.cellsOf` — pack a `Bool` function of the graph into those numbers, with
  `JSP90.sBit_maskOf` and `JSP90.cellsOf_bit` as the two readings.

Every statement in this part quantifies only over `Fin` types, so `decide` closes them; that is what
keeps the bit arithmetic out of the proof. -/

/-- **A PROPER COLOURING INDEX SEPARATES THE ENDS OF EVERY CELL.** -/
theorem properM_get : ∀ (A : Fin 64) (i : Fin 16) (p q : Fin 5),
    properM A i.val = true → crossM A p.val q.val = true →
    i.val.testBit p.val ≠ i.val.testBit q.val := by
  decide

/-- **THE CELLS ARE THE CROSS PAIRS.** -/
theorem crossM_split (A : Fin 64) (p q : Nat) (h : crossM A p q = true) :
    (p < 2 ∧ 2 ≤ q) ∨ (q < 2 ∧ 2 ≤ p) := by
  by_cases hp : p < 2 <;> by_cases hq : q < 2 <;> simp [crossM, hp, hq] at h
  · exact Or.inl ⟨hp, by omega⟩
  · exact Or.inr ⟨hq, by omega⟩

/-- **MONOCHROMATICITY, READ BACK**: the neighbour set is monochromatic under the colouring index,
with a colour which the second alternative records.  (The first reading of this statement, "the
mask is empty or all of its bits are set", is **false** and was refuted by `decide`: `i &&& s = 0`
says that no point of the set carries the colour `true`, not that the set is empty.  Monochromatic
is exactly what the transfer needs, and it is the *colour* that has to be recorded.) -/
theorem okMono_read : ∀ (i : Fin 16) (s : Fin 32), okMono i.val s.val = true →
    (∀ k : Fin 5, s.val.testBit k.val = true → i.val.testBit k.val = false)
      ∨ (∀ k : Fin 5, s.val.testBit k.val = true → i.val.testBit k.val = true) := by
  decide

/-- **MEETING BOTH COLOUR CLASSES, READ BACK.** -/
theorem meetBoth_read : ∀ s : Fin 32, meetBoth s.val = true →
    (∃ k : Fin 5, k.val < 2 ∧ s.val.testBit k.val = true)
      ∧ (∃ k : Fin 5, 2 ≤ k.val ∧ s.val.testBit k.val = true) := by
  decide

/-- **EMPTY TRIPLE INTERSECTION, READ BACK.** -/
theorem tripleEmpty_read : ∀ s0 s1 s2 : Fin 32, tripleEmpty s0.val s1.val s2.val = true →
    ∀ k : Fin 5, ¬ (s0.val.testBit k.val = true ∧ s1.val.testBit k.val = true
      ∧ s2.val.testBit k.val = true) := by
  decide

/-- **MEETING BOTH COLOUR CLASSES, READ FORWARD.** -/
theorem meetBoth_of (s : Fin 32) (h0 : s.val.testBit 0 = true ∨ s.val.testBit 1 = true)
    (h1 : s.val.testBit 2 = true ∨ s.val.testBit 3 = true ∨ s.val.testBit 4 = true) :
    meetBoth s.val = true := by
  refine Bool.and_eq_true_iff.mpr ⟨(Bool.or_eq_true _ _).mpr h0, ?_⟩
  refine (Bool.or_eq_true (s.val.testBit 2 || s.val.testBit 3) (s.val.testBit 4)).mpr ?_
  rcases h1 with h | h | h
  · exact Or.inl ((Bool.or_eq_true (s.val.testBit 2) (s.val.testBit 3)).mpr (Or.inl h))
  · exact Or.inl ((Bool.or_eq_true (s.val.testBit 2) (s.val.testBit 3)).mpr (Or.inr h))
  · exact Or.inr h

/-- **EMPTY TRIPLE INTERSECTION, READ FORWARD.** -/
theorem tripleEmpty_of (s0 s1 s2 : Fin 32)
    (h : ∀ k : Fin 5, ¬ (s0.val.testBit k.val = true ∧ s1.val.testBit k.val = true
      ∧ s2.val.testBit k.val = true)) : tripleEmpty s0.val s1.val s2.val = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have i5 : i < 5 := List.mem_range.mp hi
  refine decide_eq_true (Bool.eq_false_of_not_eq_true ?_)
  intro hpos
  have hpos1 := Bool.and_eq_true_iff.mp hpos
  have hpos2 := Bool.and_eq_true_iff.mp hpos1.1
  exact h ⟨i, i5⟩ ⟨hpos2.1, hpos2.2, hpos1.2⟩

/-! ### Packing a neighbour set into a mask -/

theorem ite_one_le : ∀ b : Bool, (if b then 1 else 0 : ℕ) ≤ 1 := by
  intro b
  cases b <;> simp

/-- **THE MASK OF A NEIGHBOUR SET ON THE FIVE POINTS OF THE RESIDUE.** -/
def maskOf (f : Fin 5 → Bool) : Fin 32 :=
  ⟨((if f 0 then 1 else 0) + (if f 1 then 2 else 0) + (if f 2 then 4 else 0)
      + (if f 3 then 8 else 0) + (if f 4 then 16 else 0)), by
    have h0 : (if f 0 then 1 else 0 : ℕ) ≤ 1 := ite_one_le _
    have h1 : (if f 1 then 2 else 0 : ℕ) ≤ 2 := by cases f 1 <;> simp
    have h2 : (if f 2 then 4 else 0 : ℕ) ≤ 4 := by cases f 2 <;> simp
    have h3 : (if f 3 then 8 else 0 : ℕ) ≤ 8 := by cases f 3 <;> simp
    have h4 : (if f 4 then 16 else 0 : ℕ) ≤ 16 := by cases f 4 <;> simp
    omega⟩

/-- **THE MASK, READ BACK.** -/
theorem sBit_maskOf (f : Fin 5 → Bool) (k : Fin 5) : sBit (maskOf f).val k.val = f k := by
  fin_cases k <;>
    by_cases h0 : f 0 = true <;> by_cases h1 : f 1 = true <;> by_cases h2 : f 2 = true <;>
    by_cases h3 : f 3 = true <;> by_cases h4 : f 4 = true <;>
    simp [sBit, maskOf, h0, h1, h2, h3, h4] <;> decide

/-- **THE SIX CELLS OF `G[X]` PACKED INTO `A : Fin 64`**, in the order of
`JSP90.crossM`: cell `3 * p + (q - 2)` is the pair `p ∈ {0,1}`, `q ∈ {2,3,4}`. -/
def cellsOf (w : Fin 6 → Bool) : Fin 64 :=
  ⟨((if w 0 then 1 else 0) + (if w 1 then 2 else 0) + (if w 2 then 4 else 0)
      + (if w 3 then 8 else 0) + (if w 4 then 16 else 0) + (if w 5 then 32 else 0)), by
    have h0 : (if w 0 then 1 else 0 : ℕ) ≤ 1 := ite_one_le _
    have h1 : (if w 1 then 2 else 0 : ℕ) ≤ 2 := by cases w 1 <;> simp
    have h2 : (if w 2 then 4 else 0 : ℕ) ≤ 4 := by cases w 2 <;> simp
    have h3 : (if w 3 then 8 else 0 : ℕ) ≤ 8 := by cases w 3 <;> simp
    have h4 : (if w 4 then 16 else 0 : ℕ) ≤ 16 := by cases w 4 <;> simp
    have h5 : (if w 5 then 32 else 0 : ℕ) ≤ 32 := by cases w 5 <;> simp
    omega⟩

/-- **THE MASK, READ BACK AT A NATURAL INDEX** — the form `JSP90.adj8n` uses. -/
theorem sBit_maskOf_nat (f : Fin 5 → Bool) (j : Nat) (hj : j < 5) :
    sBit (maskOf f).val j = f ⟨j, hj⟩ := by
  simpa only [Fin.val_mk] using (sBit_maskOf f ⟨j, hj⟩)

/-- **THE CELLS, READ BACK.** -/
theorem cellsOf_bit (w : Fin 6 → Bool) (j : Fin 6) : (cellsOf w).val.testBit j.val = w j := by
  fin_cases j <;>
    by_cases h0 : w 0 = true <;> by_cases h1 : w 1 = true <;> by_cases h2 : w 2 = true <;>
    by_cases h3 : w 3 = true <;> by_cases h4 : w 4 = true <;> by_cases h5 : w 5 = true <;>
    simp [cellsOf, h0, h1, h2, h3, h4, h5] <;> decide

/-- **THE CELLS, READ BACK AT A NATURAL INDEX** — the form `JSP90.crossM` uses. -/
theorem cellsOf_bit_nat (w : Fin 6 → Bool) (j : Nat) (hj : j < 6) :
    (cellsOf w).val.testBit j = w ⟨j, hj⟩ := by
  simpa only [Fin.val_mk] using (cellsOf_bit w ⟨j, hj⟩)

/-! ### The six-element subsets: Erdős's hypothesis produces the independent triple -/

/-- **AN INDEPENDENT TRIPLE, READ BACK OUT OF `ind3n`.** -/
theorem ind3n_get {A : Fin 64} {s0 s1 s2 : Fin 32} {a b c : Nat}
    (h : ind3n A s0.val s1.val s2.val a b c = true) :
    (decide (a < b) = true) ∧ (decide (b < c) = true)
      ∧ (! adj8n A s0.val s1.val s2.val a b) = true
      ∧ (! adj8n A s0.val s1.val s2.val a c) = true
      ∧ (! adj8n A s0.val s1.val s2.val b c) = true := by
  unfold ind3n at h
  obtain ⟨h1, hT⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h2, hS⟩ := Bool.and_eq_true_iff.mp h1
  obtain ⟨h3, hR⟩ := Bool.and_eq_true_iff.mp h2
  obtain ⟨hab, hbc⟩ := Bool.and_eq_true_iff.mp h3
  exact ⟨hab, hbc, hR, hS, hT⟩

/-- **AN INDEPENDENT TRIPLE INSIDE A SIX-ELEMENT SUBSET GIVES THREE POINTS.**  This is the direction
the transfer needs: from `hasInd3m` back to a sorted independent triple. -/
theorem exists_ind3n_of_hasInd3m {A : Fin 64} {s0 s1 s2 : Fin 32} {X : Nat}
    (h : hasInd3m A s0.val s1.val s2.val X = true) :
    ∃ a b c : Nat, a < b ∧ b < c ∧ c < 8
      ∧ ((X >>> a) &&& 1 == 1) = true ∧ ((X >>> b) &&& 1 == 1) = true
      ∧ ((X >>> c) &&& 1 == 1) = true
      ∧ ind3n A s0.val s1.val s2.val a b c = true := by
  unfold hasInd3m at h
  obtain ⟨a, ham, ha⟩ := List.any_eq_true.mp h
  obtain ⟨hXa, ha1⟩ := Bool.and_eq_true_iff.mp ha
  obtain ⟨b, hbm, hb⟩ := List.any_eq_true.mp ha1
  obtain ⟨hb1, hcs⟩ := Bool.and_eq_true_iff.mp hb
  obtain ⟨hXb, hnab⟩ := Bool.and_eq_true_iff.mp hb1
  obtain ⟨c, hcm, hcn⟩ := List.any_eq_true.mp hcs
  obtain ⟨hXc, h3⟩ := Bool.and_eq_true_iff.mp hcn
  obtain ⟨hab, hbc', hnab', hnac', hnbc'⟩ := ind3n_get h3
  have hc8 : c < 8 := by
    have := List.mem_range.mp hcm
    omega
  exact ⟨a, b, c, of_decide_eq_true hab, of_decide_eq_true hbc', hc8, hXa, hXb, hXc, h3⟩

/-- **AN INDEPENDENT TRIPLE AMONG `{0, 1, r} + {5, 6, 7}` DEFEATS `noInd36`.**  The triangle `5, 6, 7`
is a clique, so such a triple carries at most one point of it and at least two of `{0, 1, r}` — the
ten candidates guarded by `JSP90.noInd36`. -/
theorem noInd36_false_of_ind3n (A : Fin 64) (s0 s1 s2 : Fin 32) {a b c r : Nat}
    (hr : 2 ≤ r) (hr5 : r < 5) (h3 : ind3n A s0.val s1.val s2.val a b c = true)
    (hab : a < b) (hbc : b < c) (hc : c < 8)
    (hmem : ∀ z : Nat, z = a ∨ z = b ∨ z = c → z = 0 ∨ z = 1 ∨ z = r ∨ (5 ≤ z ∧ z < 8)) :
    noInd36 A s0.val s1.val s2 r = false := by
  have h3' := ind3n_get h3
  -- at most one of the three points lies in the triangle
  have h5ab : ¬ (5 ≤ a ∧ 5 ≤ b) := by
    intro h
    have hcl : adj8n A s0.val s1.val s2.val a b = true :=
      clique_T A s0 s1 s2 a b h.1 h.2 hab
    simp [hcl] at h3'
  have h5bc : ¬ (5 ≤ b ∧ 5 ≤ c) := by
    intro h
    have hcl : adj8n A s0.val s1.val s2.val b c = true :=
      clique_T A s0 s1 s2 b c h.1 h.2 hbc
    simp [hcl] at h3'
  have ha' := hmem a (Or.inl rfl)
  have hb' := hmem b (Or.inr (Or.inl rfl))
  have hc' := hmem c (Or.inr (Or.inr rfl))
  rcases hc' with hc0 | hc1 | hcr | hc5
  · -- `c = 0`: impossible, `a < b < 0`
    have hb0 : b = 0 := by omega
    have ha0 : a = 0 := by omega
    omega
  · -- `c = 1`: then `a = b = 0`
    have hb0 : b = 0 := by omega
    have ha0 : a = 0 := by omega
    omega
  · -- `c = r`: then `a, b ∈ {0, 1}`, so `(a, b, c) = (0, 1, r)`
    have ha0 : a = 0 := by
      rcases ha' with h | h | h | h
      · exact h
      · omega
      · omega
      · omega
    have hb1 : b = 1 := by
      rcases hb' with h | h | h | h
      · omega
      · exact h
      · omega
      · omega
    subst ha0
    subst hb1
    subst hcr
    simp [noInd36, h3]
  · -- `c ∈ {5, 6, 7}`: then `a, b ∈ {0, 1, r}`, in one of the three orders
    have hb5 : ¬ (5 ≤ b) := by
      intro h
      exact h5bc ⟨h, hc5.1⟩
    have ha0 : a = 0 ∨ a = 1 ∨ a = r := by
      rcases ha' with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd ⟨h.1, by omega⟩ h5ab
    have hb0 : b = 0 ∨ b = 1 ∨ b = r := by
      rcases hb' with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd h.1 hb5
    have hc56 : c = 5 ∨ c = 6 ∨ c = 7 := by omega
    rcases ha0 with haa | haa | haa <;> rcases hb0 with hbb | hbb | hbb
    · exact absurd hab (by simp [haa, hbb])
    · subst haa
      subst hbb
      rcases hc56 with rfl | rfl | rfl <;> simp [noInd36, h3]
    · subst haa
      subst hbb
      rcases hc56 with rfl | rfl | rfl <;> simp [noInd36, h3]
    · exact absurd hab (by simp [haa, hbb])
    · exact absurd hab (by simp [haa, hbb])
    · subst haa
      subst hbb
      rcases hc56 with rfl | rfl | rfl <;> simp [noInd36, h3]
    · exact absurd hab (by omega)
    · exact absurd hab (by omega)
    · exact absurd hab (by simp [haa, hbb])

/-! ### Three distinct points, sorted -/

theorem sort3 : ∀ u1 u2 u3 : Fin 8, u1 ≠ u2 → u1 ≠ u3 → u2 ≠ u3 →
    ∃ a b c : Fin 8, a.val < b.val ∧ b.val < c.val
      ∧ a ∈ ({u1, u2, u3} : Finset (Fin 8))
      ∧ b ∈ ({u1, u2, u3} : Finset (Fin 8))
      ∧ c ∈ ({u1, u2, u3} : Finset (Fin 8)) := by
  intro u1 u2 u3 h12 h13 h23
  by_cases h1 : u1.val < u2.val
  · by_cases h2 : u1.val < u3.val
    · by_cases h3 : u2.val < u3.val
      · exact ⟨u1, u2, u3, h1, h3, by simp, by simp, by simp⟩
      · exact ⟨u1, u3, u2, h2, by omega, by simp, by simp, by simp⟩
    · have e1 : u3.val < u1.val := by omega
      have e2 : u1.val < u2.val := by omega
      exact ⟨u3, u1, u2, e1, e2, by simp, by simp, by simp⟩
  · by_cases h2 : u2.val < u3.val
    · by_cases h3 : u1.val < u3.val
      · exact ⟨u2, u1, u3, by omega, by omega, by simp, by simp, by simp⟩
      · exact ⟨u2, u3, u1, h2, by omega, by simp, by simp, by simp⟩
    · have e1 : u3.val < u2.val := by omega
      have e2 : u2.val < u1.val := by omega
      exact ⟨u3, u2, u1, e1, e2, by simp, by simp, by simp⟩

/-- **AN INDEPENDENT TRIPLE IN THE `Fin 8` LANGUAGE.** -/
theorem ind3n_of_nadj {A : Fin 64} {s0 s1 s2 : Fin 32} {a b c : Nat} (hab : a < b) (hbc : b < c)
    (h1 : (! adj8n A s0.val s1.val s2.val a b) = true)
    (h2 : (! adj8n A s0.val s1.val s2.val a c) = true)
    (h3 : (! adj8n A s0.val s1.val s2.val b c) = true) :
    ind3n A s0.val s1.val s2.val a b c = true := by
  unfold ind3n
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ofDecideTrue hab
  · exact ofDecideTrue hbc
  · exact h1
  · exact h2
  · exact h3

/-- **THE MASK OF THE SIX-ELEMENT SUBSET `T + {0, 1, r}`**, for `r = 2, 3, 4`.  (The masks
`231, 235, 243` of `JSP90.sixMasks`; the arithmetic `231 + 4 * (r - 2)` is *not* usable, because
`231 + 8 = 239` keeps the bit of `2` and is not the mask of `T + {0, 1, 4}`.) -/
def sixMaskOf (r : Nat) : Nat := 231 + (if r = 3 then 4 else if r = 4 then 12 else 0)

/-- **THE THREE SIX-ELEMENT SUBSETS, IN THE FORM THE TRANSFER READS.** -/
theorem sixMask_bit_true : ∀ (r k : Fin 8), 2 ≤ r.val → r.val ≤ 4 →
    (k.val = 0 ∨ k.val = 1 ∨ k.val = r.val ∨ (5 ≤ k.val ∧ k.val < 8)) →
    ((sixMaskOf r.val >>> k.val) &&& 1 == 1) = true := by
  decide

/-- **TWO POINTS OF DIFFERENT COLOURS ARE DIFFERENT.** -/
theorem ne_of_col_ne {d : V → Fin 2} {x y : V} (h1 : d x = 0) (h2 : d y = 1) : x ≠ y := by
  intro h
  exact absurd (h1.symm.trans (h ▸ h2)) (by decide)

/-- **THE TWO COLOURS ARE `0` AND `1`.** -/
theorem fin2_cases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide

/-- **ADJACENCY IS SYMMETRIC, AS AN EQUATION** — the form `simp` consumes (`G.adj_comm` is an
`Iff`, which `simp` will not rewrite with, and the `Fin 8` correspondence below needs the
symmetry *inside* a `decide`). -/
theorem adj_comm_eq : ∀ x y : V, G.Adj x y = G.Adj y x :=
  fun x y => propext (G.adj_comm x y)

/-- **`decide` COMMUTES WITH THE SYMMETRY OF ADJACENCY.** -/
theorem decide_adj_comm : ∀ x y : V, decide (G.Adj x y) = decide (G.Adj y x) := by
  intro x y
  by_cases h : G.Adj x y
  · have h2 : G.Adj y x := (G.adj_comm x y).mp h
    simp [h, h2]
  · have h2 : ¬ G.Adj y x := fun hh => h ((G.adj_comm y x).mp hh)
    simp [h, h2]

/-! ## Part 0 bis — the six-element subsets as vertex sets -/

/-- **THE CARD OF THE SIX-ELEMENT SUBSET, FROM THE INJECTIVITY OF THE INDEXING.** -/
theorem card_six_inv (inv : Fin 8 → V) (hinv : Function.Injective inv) (r : Fin 8)
    (hr : r.val = 2 ∨ r.val = 3 ∨ r.val = 4) :
    ({inv 0, inv 1, inv r, inv 5, inv 6, inv 7} : Finset V).card = 6 := by
  have hr' : r = 2 ∨ r = 3 ∨ r = 4 := by
    rcases hr with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases hr' with rfl | rfl | rfl
  · have hc : ({0, 1, 2, 5, 6, 7} : Finset (Fin 8)).card = 6 := by decide
    have h1 := Finset.card_image_of_injective (s := ({0, 1, 2, 5, 6, 7} : Finset (Fin 8))) hinv
    have h2 : (({0, 1, 2, 5, 6, 7} : Finset (Fin 8)).image inv)
        = ({inv 0, inv 1, inv 2, inv 5, inv 6, inv 7} : Finset V) := by simp
    rw [← h2]
    exact h1.trans hc
  · have hc : ({0, 1, 3, 5, 6, 7} : Finset (Fin 8)).card = 6 := by decide
    have h1 := Finset.card_image_of_injective (s := ({0, 1, 3, 5, 6, 7} : Finset (Fin 8))) hinv
    have h2 : (({0, 1, 3, 5, 6, 7} : Finset (Fin 8)).image inv)
        = ({inv 0, inv 1, inv 3, inv 5, inv 6, inv 7} : Finset V) := by simp
    rw [← h2]
    exact h1.trans hc
  · have hc : ({0, 1, 4, 5, 6, 7} : Finset (Fin 8)).card = 6 := by decide
    have h1 := Finset.card_image_of_injective (s := ({0, 1, 4, 5, 6, 7} : Finset (Fin 8))) hinv
    have h2 : (({0, 1, 4, 5, 6, 7} : Finset (Fin 8)).image inv)
        = ({inv 0, inv 1, inv 4, inv 5, inv 6, inv 7} : Finset V) := by simp
    rw [← h2]
    exact h1.trans hc

/-- **MEMBERSHIP OF THE SIX-ELEMENT SUBSET, IN THE READING THE TRANSFER NEEDS.** -/
theorem mem_six_inv (inv : Fin 8 → V) (r : Fin 8) (y : V) :
    y ∈ ({inv 0, inv 1, inv r, inv 5, inv 6, inv 7} : Finset V) → ∃ i : Fin 8, inv i = y ∧
      (i.val = 0 ∨ i.val = 1 ∨ i.val = r.val ∨ (5 ≤ i.val ∧ i.val < 8)) := by
  intro hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with h | h | h | h | h | h
  · exact ⟨0, h.symm, Or.inl rfl⟩
  · exact ⟨1, h.symm, Or.inr (Or.inl rfl)⟩
  · exact ⟨r, h.symm, Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨5, h.symm, Or.inr (Or.inr (Or.inr ⟨by decide, by decide⟩))⟩
  · exact ⟨6, h.symm, Or.inr (Or.inr (Or.inr ⟨by decide, by decide⟩))⟩
  · exact ⟨7, h.symm, Or.inr (Or.inr (Or.inr ⟨by decide, by decide⟩))⟩

/-! ### Part 0 ter — the two small `Bool` facts the transfer needs -/

/-- **`decide (b = true) = b` for a `Bool`** — this is what turns the reading of the mask
(`JSP90.sBit_maskOf`, stated with `sBit = decide (s.testBit _ = true)`) back into a statement about
`Nat.testBit`. -/
theorem decide_eq_true_of_bool : ∀ b : Bool, decide (b = true) = b := by
  intro b
  cases b <;> rfl

/-- **INSIDE THE RESIDUE, `adj8n` IS `crossM`.** -/
theorem crossM_of_adj8n {A : Fin 64} {s0 s1 s2 : Fin 32} {i j : Nat} (hi : i < 5) (hj : j < 5)
    (h : adj8n A s0.val s1.val s2.val i j = true) : crossM A i j = true := by
  have h' := h
  simp only [adj8n, if_pos hi, if_pos hj] at h'
  exact h'

/-! ## Part 1 — **THE TRIANGLE CASE AT EIGHT VERTICES** -/

/-- **THE TRIANGLE CASE OF THE EIGHT-VERTEX AXIS.**  At `LocIndep 1` and `|V| ≤ 8` a triangle `T`
has a vertex `t ∈ T` such that `G[(V \ T) + {t}]` is bipartite, i.e.

```lean
LocIndep 1 G → Fintype.card V ≤ 8 → G.IsNClique 3 T → ∃ t ∈ T, (deleteFinset G (T \ {t})).IsBipartite
```

This is the transfer of `policy.json` ("NEXT ROUND"), the one gap between the counting step
`JSP90.loc8_lemma` (round 167) and the eight-vertex instance of Erdős #73.  The proof is the
graph-to-`Fin 8` correspondence

* `xpt : Fin 5 → V` — the five points of the residue `X = V \ T`, `0, 1` in the colour class of
  **two** points and `2, 3, 4` in the other, which has **three** (`JSP90.card_cls_ge_two` at
  `|V| = 8`; the two classes are swapped by `opp2 ∘ d` when needed);
* `tpt : Fin 3 → V` — the three vertices of `T`, carried by `5, 6, 7`;
* `inv : Fin 8 → V` — the bijection `i ↦ xpt i` for `i < 5` and `i ↦ tpt (i - 5)` otherwise;
* `A : Fin 64` — the six cells of `G[X]` (the residue sits inside `K_{2,3}`);
* `s0 s1 s2 : Fin 32` — the three neighbour sets as masks,

with `adj8n A s0.val s1.val s2.val i.val j.val = decide (G.Adj (inv i) (inv j))` for all `i, j`,
the three hypotheses transferred (`meetBoth` via `JSP90.exists_adjIn_color`, `tripleEmpty` via
`JSP90.card_adjIn_le_two_of_isNClique_three`, and badness via `JSP90.properM_get` +
`JSP90.okMono_read`), and Erdős's hypothesis read on the three six-element subsets
`T + {0, 1, 2}`, `T + {0, 1, 3}`, `T + {0, 1, 4}` against `JSP90.loc8_lemma`. -/
theorem triCaseEight (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 8) {T : Finset V}
    (hT : G.IsNClique 3 T) : ∃ t ∈ T, (deleteFinset G (T \ {t})).IsBipartite := by
  obtain ⟨d, hd⟩ := isBipartite_delete_of_isNClique_three_of_locIndep_one hG hT
  have hd' : ∀ {v w : V}, v ∉ T → w ∉ T → G.Adj v w → d v ≠ d w := by
    intro v w hv hw hvw
    exact hd (show (deleteFinset G T).Adj v w from (deleteFinset_adj).mpr ⟨hv, hw, hvw⟩)
  by_cases hex : ∃ t ∈ T, (deleteFinset G (T \ {t})).IsBipartite
  · exact hex
  have hbad : ∀ t ∈ T, ¬ (deleteFinset G (T \ {t})).IsBipartite :=
    fun t ht h => hex ⟨t, ht, h⟩
  by_cases h7 : Fintype.card V ≤ 7
  · exact triCase hG h7 hT ⟨d, hd⟩
  obtain ⟨hcl, hTc3⟩ := G.isNClique_iff.mp hT
  have hV8 : Fintype.card V = 8 := by
    have h1 := Finset.card_le_univ T
    have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    have h4 : T.card = 3 := hTc3
    omega
  have hall0 : ∀ t ∈ T, ∃ x, G.Adj t x ∧ x ∉ T ∧ d x = 0 :=
    fun t ht => exists_adjIn_color ht hd' (hbad t ht)
  have hall1 : ∀ t ∈ T, ∃ x, G.Adj t x ∧ x ∉ T ∧ d x = 1 :=
    fun t ht => exists_adjIn_color ht hd' (hbad t ht)
  have hc0 : 2 ≤ (cls T d 0).card := card_cls_ge_two hG hT hd' hall0 hbad
  have hc1 : 2 ≤ (cls T d 1).card := card_cls_ge_two hG hT hd' hall1 hbad
  have hcardX : (Residue T).card = 5 := by
    have h1 := Finset.card_sdiff_of_subset (Finset.subset_univ T)
    have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    have h4 : T.card = 3 := hTc3
    rw [Residue]
    omega
  have hsub : cls T d 0 ∪ cls T d 1 ⊆ Residue T :=
    Finset.union_subset (fun x hx => mem_residue_of_notMem_set (mem_cls.mp hx).1)
      (fun x hx => mem_residue_of_notMem_set (mem_cls.mp hx).1)
  have hdisj : Disjoint (cls T d 0) (cls T d 1) := by
    refine Finset.disjoint_left.mpr (fun x h0 h1 => ?_)
    obtain ⟨-, hdx⟩ := mem_cls.mp h0
    obtain ⟨-, hdx'⟩ := mem_cls.mp h1
    exact absurd (hdx'.symm.trans hdx) (by decide)
  have hcovd : ∀ y : V, y ∉ T → y ∈ cls T d 0 ∨ y ∈ cls T d 1 := by
    intro y hyT
    rcases fin2_cases (d y) with h | h
    · exact Or.inl (mem_cls.mpr ⟨hyT, h⟩)
    · exact Or.inr (mem_cls.mpr ⟨hyT, h⟩)
  have hunion : cls T d 0 ∪ cls T d 1 = Residue T := by
    ext y
    simp only [Finset.mem_union, mem_cls, mem_residue]
    constructor
    · intro hy
      rcases hy with hy | hy
      · exact hy.1
      · exact hy.1
    · intro hy
      rcases fin2_cases (d y) with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
  have hsumcard : (cls T d 0).card + (cls T d 1).card = 5 := by
    have hu := Finset.card_union_of_disjoint hdisj
    rw [hunion, hcardX] at hu
    exact hu.symm
  have hex_or : (cls T d 0).card = 2 ∨ (cls T d 1).card = 2 := by
    rcases le_or_gt (cls T d 0).card 2 with h | h
    · have h2 : (cls T d 0).card = 2 := by omega
      exact Or.inl h2
    · have h3 : (cls T d 1).card = 2 := by omega
      exact Or.inr h3
  have hopp_inj : ∀ i j : Fin 2, opp2 i = opp2 j → i = j := by
    intro i j h
    have h' := congrArg opp2 h
    simp only [opp2_involutive] at h'
    exact h'
  have main : ∀ (dd : V → Fin 2),
      (∀ {v w : V}, v ∉ T → w ∉ T → G.Adj v w → dd v ≠ dd w) →
      (cls T dd 0).card = 2 → (cls T dd 1).card = 3 →
      ∃ t ∈ T, (deleteFinset G (T \ {t})).IsBipartite := by
    intro dd hdd' hd2 hd3
    obtain ⟨p0, p1, hp01, hP⟩ := Finset.card_eq_two.mp hd2
    obtain ⟨q0, q1, q2, hq01, hq02, hq12, hQ⟩ := Finset.card_eq_three.mp hd3
    have hp0in : p0 ∈ cls T dd 0 := by rw [hP]; simp
    have hp1in : p1 ∈ cls T dd 0 := by rw [hP]; simp
    have hq0in : q0 ∈ cls T dd 1 := by rw [hQ]; simp
    have hq1in : q1 ∈ cls T dd 1 := by rw [hQ]; simp
    have hq2in : q2 ∈ cls T dd 1 := by rw [hQ]; simp
    have hp0mem : p0 ∈ Residue T := mem_residue_of_notMem_set (mem_cls.mp hp0in).1
    have hp1mem : p1 ∈ Residue T := mem_residue_of_notMem_set (mem_cls.mp hp1in).1
    have hq0mem : q0 ∈ Residue T := mem_residue_of_notMem_set (mem_cls.mp hq0in).1
    have hq1mem : q1 ∈ Residue T := mem_residue_of_notMem_set (mem_cls.mp hq1in).1
    have hq2mem : q2 ∈ Residue T := mem_residue_of_notMem_set (mem_cls.mp hq2in).1
    have hp0d : dd p0 = 0 := (mem_cls.mp hp0in).2
    have hp1d : dd p1 = 0 := (mem_cls.mp hp1in).2
    have hq0d : dd q0 = 1 := (mem_cls.mp hq0in).2
    have hq1d : dd q1 = 1 := (mem_cls.mp hq1in).2
    have hq2d : dd q2 = 1 := (mem_cls.mp hq2in).2
    let xpt : Fin 5 → V := fun i =>
      if h : i.val = 0 then p0 else if h' : i.val = 1 then p1
        else if h'' : i.val = 2 then q0 else if h''' : i.val = 3 then q1 else q2
    have hxpt0 : xpt 0 = p0 := by simp [xpt]
    have hxpt1 : xpt 1 = p1 := by simp [xpt]
    have hxpt2 : xpt 2 = q0 := by simp [xpt]
    have hxpt3 : xpt 3 = q1 := by simp [xpt]
    have hxpt4 : xpt 4 = q2 := by simp [xpt]
    have hxpt_mem : ∀ i, xpt i ∈ Residue T := by
      intro i
      fin_cases i
      · exact hp0mem
      · exact hp1mem
      · exact hq0mem
      · exact hq1mem
      · exact hq2mem
    have hidx : ∀ i : Fin 5, (dd (xpt i) = 0 ∧ i.val < 2) ∨ (dd (xpt i) = 1 ∧ 2 ≤ i.val) := by
      intro i
      fin_cases i
      · exact Or.inl ⟨by simp [xpt, hp0d], by decide⟩
      · exact Or.inl ⟨by simp [xpt, hp1d], by decide⟩
      · exact Or.inr ⟨by simp [xpt, hq0d], by decide⟩
      · exact Or.inr ⟨by simp [xpt, hq1d], by decide⟩
      · exact Or.inr ⟨by simp [xpt, hq2d], by decide⟩
    have hclass : ∀ i : Fin 5, (i.val < 2) = (dd (xpt i) = 0) := by
      intro i
      fin_cases i <;> simp [xpt, hp0d, hp1d, hq0d, hq1d, hq2d]
    have hxpt_val : ∀ i : Fin 5, xpt i = (if i.val = 0 then p0 else if i.val = 1 then p1
        else if i.val = 2 then q0 else if i.val = 3 then q1 else q2) := by
      intro i
      fin_cases i <;> simp [xpt]
    have hxpt_inj : Function.Injective xpt := by
      intro i j hij
      have hcl : (i.val < 2) ↔ (j.val < 2) := by
        have hdd : dd (xpt i) = dd (xpt j) := by rw [hij]
        constructor
        · intro h
          rw [hclass j]
          exact hdd ▸ (hclass i).mp h
        · intro h
          rw [hclass i]
          exact hdd ▸ (hclass j).mp h
      have hij' : (if i.val = 0 then p0 else if i.val = 1 then p1
          else if i.val = 2 then q0 else if i.val = 3 then q1 else q2)
          = (if j.val = 0 then p0 else if j.val = 1 then p1
          else if j.val = 2 then q0 else if j.val = 3 then q1 else q2) := by
        rw [hxpt_val i, hxpt_val j] at hij
        exact hij
      by_cases hi2 : i.val < 2
      · by_cases hj2 : j.val < 2
        · have hi : i.val = 0 ∨ i.val = 1 := by omega
          have hj : j.val = 0 ∨ j.val = 1 := by omega
          rcases hi with hi | hi <;> rcases hj with hj | hj
          · rw [hi, hj] at hij'
            exact Fin.ext (by omega)
          · rw [hi, hj] at hij'
            exact absurd hij' hp01
          · rw [hi, hj] at hij'
            exact absurd hij' hp01.symm
          · rw [hi, hj] at hij'
            exact Fin.ext (by omega)
        · exact (hj2 (hcl.mp hi2)).elim
      · by_cases hj2 : j.val < 2
        · exact (hi2 (hcl.mpr hj2)).elim
        · have hi : i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
          have hj : j.val = 2 ∨ j.val = 3 ∨ j.val = 4 := by omega
          rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj
          · rw [hi, hj] at hij'
            exact Fin.ext (by omega)
          · rw [hi, hj] at hij'
            exact absurd hij' hq01
          · rw [hi, hj] at hij'
            exact absurd hij' hq02
          · rw [hi, hj] at hij'
            exact absurd hij' hq01.symm
          · rw [hi, hj] at hij'
            exact Fin.ext (by omega)
          · rw [hi, hj] at hij'
            exact absurd hij' hq12
          · rw [hi, hj] at hij'
            exact absurd hij' hq02.symm
          · rw [hi, hj] at hij'
            exact absurd hij' hq12.symm
          · rw [hi, hj] at hij'
            exact Fin.ext (by omega)
    have hxpt_notMem : ∀ i : Fin 5, xpt i ∉ T := fun i => mem_residue.mp (hxpt_mem i)
    obtain ⟨a, b, c, hab, hac, hbc, hTabc⟩ := Finset.card_eq_three.mp hTc3
    let tpt : Fin 3 → V := fun t => if h : t.val = 0 then a else if h' : t.val = 1 then b else c
    have htpt0 : tpt 0 = a := by simp [tpt]
    have htpt1 : tpt 1 = b := by simp [tpt]
    have htpt2 : tpt 2 = c := by simp [tpt]
    have haT : a ∈ T := by rw [hTabc]; simp
    have hbT : b ∈ T := by rw [hTabc]; simp
    have hcT : c ∈ T := by rw [hTabc]; simp
    have htpt_mem : ∀ t, tpt t ∈ T := by
      intro t
      fin_cases t
      · exact haT
      · exact hbT
      · exact hcT
    have htpt_inj : Function.Injective tpt := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij
      all_goals
        first
        | exact rfl
        | exact absurd hij hab
        | exact absurd hij hab.symm
        | exact absurd hij hac
        | exact absurd hij hac.symm
        | exact absurd hij hbc
        | exact absurd hij hbc.symm
    let inv : Fin 8 → V := fun i =>
      if h : i.val < 5 then xpt ⟨i.val, h⟩ else tpt ⟨i.val - 5, by omega⟩
    have invX : ∀ (k : Fin 8) (hk : (k : ℕ) < 5), inv k = xpt ⟨k.val, hk⟩ := by
      intro k hk
      obtain ⟨kv, kvlt⟩ := k
      simp only [Fin.val_mk] at hk ⊢
      have hkv : kv = 0 ∨ kv = 1 ∨ kv = 2 ∨ kv = 3 ∨ kv = 4 := by omega
      rcases hkv with rfl | rfl | rfl | rfl | rfl <;> simp [inv]
    have invT : ∀ (k : Fin 8) (hk : ¬ (k : ℕ) < 5),
        inv k = tpt ⟨k.val - 5, by omega⟩ := by
      intro k hk
      obtain ⟨kv, kvlt⟩ := k
      simp only [Fin.val_mk] at hk ⊢
      have hkv : kv = 5 ∨ kv = 6 ∨ kv = 7 := by omega
      rcases hkv with rfl | rfl | rfl <;> simp [inv]
    have inv_inj : Function.Injective inv := by
      intro i j hij
      by_cases hi4 : (i : ℕ) < 5
      · by_cases hj4 : (j : ℕ) < 5
        · have hEq : xpt ⟨i.val, hi4⟩ = xpt ⟨j.val, hj4⟩ := by
            rw [← invX i hi4, hij, invX j hj4]
          have hEq5 : (⟨i.val, hi4⟩ : Fin 5) = ⟨j.val, hj4⟩ := hxpt_inj hEq
          refine Fin.val_injective ?_
          simpa using congrArg Fin.val hEq5
        · have hEq : xpt ⟨i.val, hi4⟩ = tpt ⟨j.val - 5, by omega⟩ := by
            rw [← invX i hi4, hij, invT j hj4]
          exact absurd (hEq ▸ htpt_mem ⟨j.val - 5, by omega⟩) (hxpt_notMem ⟨i.val, hi4⟩)
      · by_cases hj4 : j.val < 5
        · have hEq : tpt ⟨i.val - 5, by omega⟩ = xpt ⟨j.val, hj4⟩ := by
            rw [← invT i hi4, hij, invX j hj4]
          exact absurd (hEq ▸ htpt_mem ⟨i.val - 5, by omega⟩) (hxpt_notMem ⟨j.val, hj4⟩)
        · have hEq : tpt ⟨i.val - 5, by omega⟩ = tpt ⟨j.val - 5, by omega⟩ := by
            rw [← invT i hi4, hij, invT j hj4]
          have hEq3 : (⟨i.val - 5, by omega⟩ : Fin 3) = ⟨j.val - 5, by omega⟩ := htpt_inj hEq
          refine Fin.val_injective ?_
          have h2 : (i : ℕ) - 5 = (j : ℕ) - 5 := congrArg Fin.val hEq3
          omega
    have inv_surj : ∀ x : V, ∃ i : Fin 8, inv i = x := by
      intro x
      by_cases hxT : x ∈ T
      · rw [hTabc] at hxT
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
        rcases hxT with rfl | rfl | rfl
        · exact ⟨5, by rw [invT 5 (by decide)]; exact htpt0⟩
        · exact ⟨6, by rw [invT 6 (by decide)]; exact htpt1⟩
        · exact ⟨7, by rw [invT 7 (by decide)]; exact htpt2⟩
      · have hcov : ∀ y : V, y ∉ T → y ∈ cls T dd 0 ∨ y ∈ cls T dd 1 := by
          intro y hyT
          rcases fin2_cases (dd y) with h | h
          · exact Or.inl (mem_cls.mpr ⟨hyT, h⟩)
          · exact Or.inr (mem_cls.mpr ⟨hyT, h⟩)
        have hxcls : x ∈ cls T dd 0 ∨ x ∈ cls T dd 1 := hcov x hxT
        rcases hxcls with hx | hx
        · rw [hP] at hx
          rcases Finset.mem_insert.mp hx with h | h
          · subst h
            exact ⟨0, (invX 0 (by decide)).trans hxpt0⟩
          · have h' : x = p1 := Finset.mem_singleton.mp h
            subst h'
            exact ⟨1, (invX 1 (by decide)).trans hxpt1⟩
        · rw [hQ] at hx
          rcases Finset.mem_insert.mp hx with h | h
          · subst h
            exact ⟨2, (invX 2 (by decide)).trans hxpt2⟩
          · rcases Finset.mem_insert.mp h with h | h
            · subst h
              exact ⟨3, (invX 3 (by decide)).trans hxpt3⟩
            · have h' : x = q2 := Finset.mem_singleton.mp h
              subst h'
              exact ⟨4, (invX 4 (by decide)).trans hxpt4⟩
    let finv : V → Fin 8 := fun v => Classical.choose (inv_surj v)
    have finv_spec : ∀ v, inv (finv v) = v := fun v => Classical.choose_spec (inv_surj v)
    have hfinv5 : ∀ v : V, v ∉ T → (finv v).val < 5 := by
      intro v hvT
      by_contra hc
      have hge : 5 ≤ (finv v).val := by omega
      have hvv : inv (finv v) = tpt ⟨(finv v).val - 5, by omega⟩ := invT _ (by omega)
      have hmem : v ∈ T := by
        rw [← finv_spec v, hvv]
        exact htpt_mem ⟨(finv v).val - 5, by omega⟩
      exact hvT hmem
    let w : Fin 6 → Bool := fun k =>
      if h : k.val = 0 then decide (G.Adj p0 q0)
        else if h' : k.val = 1 then decide (G.Adj p0 q1)
          else if h'' : k.val = 2 then decide (G.Adj p0 q2)
            else if h''' : k.val = 3 then decide (G.Adj p1 q0)
              else if h'''' : k.val = 4 then decide (G.Adj p1 q1) else decide (G.Adj p1 q2)
    let A : Fin 64 := cellsOf w
    let s0 : Fin 32 := maskOf (fun k => decide (G.Adj (xpt k) (tpt 0)))
    let s1 : Fin 32 := maskOf (fun k => decide (G.Adj (xpt k) (tpt 1)))
    let s2 : Fin 32 := maskOf (fun k => decide (G.Adj (xpt k) (tpt 2)))
    have hsT : ∀ (t : Fin 3) (k : Fin 5),
        (maskOf (fun j => decide (G.Adj (xpt j) (tpt t)))).val.testBit k.val
          = decide (G.Adj (xpt k) (tpt t)) := by
      intro t k
      have h1 := sBit_maskOf (fun j => decide (G.Adj (xpt j) (tpt t))) k
      rw [sBit] at h1
      exact (decide_eq_true_of_bool
        ((maskOf (fun j => decide (G.Adj (xpt j) (tpt t)))).val.testBit k.val)).symm.trans h1
    have hs0 : ∀ k : Fin 5, s0.val.testBit k.val = decide (G.Adj (xpt k) (tpt 0)) := hsT 0
    have hs1 : ∀ k : Fin 5, s1.val.testBit k.val = decide (G.Adj (xpt k) (tpt 1)) := hsT 1
    have hs2 : ∀ k : Fin 5, s2.val.testBit k.val = decide (G.Adj (xpt k) (tpt 2)) := hsT 2
    have hnp01 : ¬ G.Adj p0 p1 := by
      intro hh
      exact hdd' (hxpt_notMem 0) (hxpt_notMem 1) (by rw [hxpt0, hxpt1]; exact hh)
        (hp0d.trans hp1d.symm)
    have hnp10 : ¬ G.Adj p1 p0 := by
      intro hh
      exact hdd' (hxpt_notMem 1) (hxpt_notMem 0) (by rw [hxpt1, hxpt0]; exact hh)
        (hp1d.trans hp0d.symm)
    have hnq01 : ¬ G.Adj q0 q1 := by
      intro hh
      exact hdd' (hxpt_notMem 2) (hxpt_notMem 3) (by rw [hxpt2, hxpt3]; exact hh)
        (hq0d.trans hq1d.symm)
    have hnq02 : ¬ G.Adj q0 q2 := by
      intro hh
      exact hdd' (hxpt_notMem 2) (hxpt_notMem 4) (by rw [hxpt2, hxpt4]; exact hh)
        (hq0d.trans hq2d.symm)
    have hnq12 : ¬ G.Adj q1 q2 := by
      intro hh
      exact hdd' (hxpt_notMem 3) (hxpt_notMem 4) (by rw [hxpt3, hxpt4]; exact hh)
        (hq1d.trans hq2d.symm)
    have hnq10 : ¬ G.Adj q1 q0 := by
      intro hh
      exact hdd' (hxpt_notMem 3) (hxpt_notMem 2) (by rw [hxpt3, hxpt2]; exact hh)
        (hq1d.trans hq0d.symm)
    have hnq20 : ¬ G.Adj q2 q0 := by
      intro hh
      exact hdd' (hxpt_notMem 4) (hxpt_notMem 2) (by rw [hxpt4, hxpt2]; exact hh)
        (hq2d.trans hq0d.symm)
    have hnq21 : ¬ G.Adj q2 q1 := by
      intro hh
      exact hdd' (hxpt_notMem 4) (hxpt_notMem 3) (by rw [hxpt4, hxpt3]; exact hh)
        (hq2d.trans hq1d.symm)
    have hwAll : ∀ k : Fin 6, w k = (if k.val = 0 then decide (G.Adj p0 q0)
        else if k.val = 1 then decide (G.Adj p0 q1)
        else if k.val = 2 then decide (G.Adj p0 q2)
        else if k.val = 3 then decide (G.Adj p1 q0)
        else if k.val = 4 then decide (G.Adj p1 q1) else decide (G.Adj p1 q2)) := by
      intro k
      fin_cases k <;> simp [w]
    have hj0 : (0 : ℕ) < 6 := by decide
    have hmod0 : ((cellsOf w).val : ℕ) % 2 = 1 ↔ G.Adj p0 q0 := by
      have h1 := cellsOf_bit_nat w 0 hj0
      have hw0 : w ⟨0, hj0⟩ = decide (G.Adj p0 q0) := by simp [w]
      constructor
      · intro hm
        have ht : (cellsOf w).val.testBit 0 = true := Nat.mod_two_eq_one_iff_testBit_zero.mp hm
        rw [h1, hw0] at ht
        exact of_decide_eq_true ht
      · intro hp
        have ht : (cellsOf w).val.testBit 0 = true := by
          rw [h1, hw0]
          exact decide_eq_true hp
        exact Nat.mod_two_eq_one_iff_testBit_zero.mpr ht
    have habAdj : G.Adj a b := hcl haT hbT hab
    have hacAdj : G.Adj a c := hcl haT hcT hac
    have hbcAdj : G.Adj b c := hcl hbT hcT hbc
    have hadj8 : ∀ (i j : Fin 8), adj8n A s0.val s1.val s2.val i.val j.val
        = decide (G.Adj (inv i) (inv j)) := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [adj8n, sOf, s0, s1, s2, sBit_maskOf_nat, inv, xpt, tpt,
          crossM, A, hwAll, cellsOf_bit_nat,
          hxpt0, hxpt1, hxpt2, hxpt3, hxpt4,
          htpt0, htpt1, htpt2, hnp01, hnp10, hnq01, hnq10, hnq02, hnq12, hnq20, hnq21,
          habAdj, hacAdj, hbcAdj, adj_comm_eq, hmod0]
    have hmeet : ∀ t : Fin 3,
        meetBoth (maskOf (fun k => decide (G.Adj (xpt k) (tpt t)))).val = true := by
      intro t
      obtain ⟨x, hx1, hxT, hx0⟩ :=
        exists_adjIn_color (d := dd) (htpt_mem t) hdd' (hbad (tpt t) (htpt_mem t)) (i := 0)
      have hx0' : x ∈ cls T dd 0 := mem_cls.mpr ⟨hxT, hx0⟩
      have hkOf : ∀ (x : V) (hx : x ∈ cls T dd 0), ∃ k : Fin 5, xpt k = x ∧ k.val < 2 := by
        intro x hx
        rw [hP] at hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact ⟨0, h.symm, by decide⟩
        · exact ⟨1, (Finset.mem_singleton.mp h).symm, by decide⟩
      obtain ⟨k, hk, hk0⟩ := hkOf x hx0'
      have hsbit : (maskOf (fun j => decide (G.Adj (xpt j) (tpt t)))).val.testBit k.val = true := by
        have hAdj : G.Adj (xpt k) (tpt t) := by rw [hk]; exact (G.adj_comm (tpt t) x).mp hx1
        rw [hsT t k, decide_eq_true hAdj]
      obtain ⟨y, hy1, hyT, hy1'⟩ :=
        exists_adjIn_color (d := dd) (htpt_mem t) hdd' (hbad (tpt t) (htpt_mem t)) (i := 1)
      have hy1'' : y ∈ cls T dd 1 := mem_cls.mpr ⟨hyT, hy1'⟩
      have hkOf' : ∀ (x : V) (hx : x ∈ cls T dd 1), ∃ k : Fin 5, xpt k = x ∧ 2 ≤ k.val := by
        intro x hx
        rw [hQ] at hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact ⟨2, h.symm, by decide⟩
        · rcases Finset.mem_insert.mp h with h | h
          · exact ⟨3, h.symm, by decide⟩
          · exact ⟨4, (Finset.mem_singleton.mp h).symm, by decide⟩
      obtain ⟨k', hk', hk2⟩ := hkOf' y hy1''
      have hsbit' : (maskOf (fun j => decide (G.Adj (xpt j) (tpt t)))).val.testBit k'.val = true := by
        have hAdj : G.Adj (xpt k') (tpt t) := by rw [hk']; exact (G.adj_comm (tpt t) y).mp hy1
        rw [hsT t k', decide_eq_true hAdj]
      refine meetBoth_of _ ?_ ?_
      · have hsplit : k.val = 0 ∨ k.val = 1 := by omega
        rcases hsplit with h | h
        · rw [h] at hsbit
          exact Or.inl hsbit
        · rw [h] at hsbit
          exact Or.inr hsbit
      · have hsplit : k'.val = 2 ∨ k'.val = 3 ∨ k'.val = 4 := by omega
        rcases hsplit with h | h | h
        · rw [h] at hsbit'
          exact Or.inl hsbit'
        · rw [h] at hsbit'
          exact Or.inr (Or.inl hsbit')
        · rw [h] at hsbit'
          exact Or.inr (Or.inr hsbit')
    have htri : ∀ k : Fin 5,
        ¬ ((maskOf (fun j => decide (G.Adj (xpt j) (tpt 0)))).val.testBit k.val = true
          ∧ (maskOf (fun j => decide (G.Adj (xpt j) (tpt 1)))).val.testBit k.val = true
          ∧ (maskOf (fun j => decide (G.Adj (xpt j) (tpt 2)))).val.testBit k.val = true) := by
      intro k
      rintro ⟨h0, h1, h2⟩
      have hAdj0 : G.Adj (xpt k) (tpt 0) := of_decide_eq_true ((hs0 k) ▸ h0)
      have hAdj1 : G.Adj (xpt k) (tpt 1) := of_decide_eq_true ((hs1 k) ▸ h1)
      have hAdj2 : G.Adj (xpt k) (tpt 2) := of_decide_eq_true ((hs2 k) ▸ h2)
      have hsub' : T ⊆ AdjIn G (xpt k) T := by
        intro w hw
        rw [hTabc] at hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with hw | hw | hw
        · subst hw
          exact mem_adjIn.mpr ⟨by rw [hTabc]; simp, by simpa [htpt0] using hAdj0⟩
        · subst hw
          exact mem_adjIn.mpr ⟨by rw [hTabc]; simp, by simpa [htpt1] using hAdj1⟩
        · subst hw
          exact mem_adjIn.mpr ⟨by rw [hTabc]; simp, by simpa [htpt2] using hAdj2⟩
      have hle := card_adjIn_le_two_of_isNClique_three hG hT (x := xpt k) (hxpt_notMem k)
      have hcard := Finset.card_le_card hsub'
      have h3 : T.card = 3 := hTc3
      omega
    have hbadM : ∀ t : Fin 3,
        badM A (maskOf (fun j => decide (G.Adj (xpt j) (tpt t)))).val = true := by
      intro t
      by_contra hn
      have hnb : badM A (maskOf (fun j => decide (G.Adj (xpt j) (tpt t)))).val = false := by
        simpa using hn
      obtain ⟨i, hi, hm⟩ :=
        exists_of_not_badM A (maskOf (fun j => decide (G.Adj (xpt j) (tpt t)))) hnb
      have himono : okMono i (maskOf (fun j => decide (G.Adj (xpt j) (tpt t)))).val = true :=
        (Bool.and_eq_true_iff.mp hm).1
      have hiprop : properM A i = true := (Bool.and_eq_true_iff.mp hm).2
      have hi16 : i < 16 := by
        have hh := List.mem_range.mp hi
        omega
      let e : V → Fin 2 := fun v =>
        if hv : (finv v).val < 5 then bitCol (i.testBit (⟨(finv v).val, hv⟩ : Fin 5)) else 0
      have heproper : ∀ {v w : V}, v ∉ T → w ∉ T → G.Adj v w → e v ≠ e w := by
        intro v w hvT hwT hAdj
        have h4v := hfinv5 v hvT
        have h4w := hfinv5 w hwT
        have hc : crossM A (⟨(finv v).val, h4v⟩ : Fin 5) (⟨(finv w).val, h4w⟩ : Fin 5) = true := by
          have hAdj : adj8n A s0.val s1.val s2.val (finv v).val (finv w).val = true := by
            have h := hadj8 (finv v) (finv w)
            rw [finv_spec v, finv_spec w] at h
            rw [h]
            exact decide_eq_true hAdj
          simpa only [Fin.val_mk] using crossM_of_adj8n h4v h4w hAdj
        simp only [e, dif_pos h4v, dif_pos h4w]
        exact fun heq => properM_get A ⟨i, hi16⟩ (⟨(finv v).val, h4v⟩ : Fin 5)
          (⟨(finv w).val, h4w⟩ : Fin 5) hiprop hc (bitCol_inj _ _ heq)
      rcases okMono_read ⟨i, hi16⟩ (maskOf (fun j => decide (G.Adj (xpt j) (tpt t)))) himono with
        hmono0 | hmono1
      · refine hbad (tpt t) (htpt_mem t)
          (isBipartite_of_adjIn_mono (T := T) (t := tpt t) (ht := htpt_mem t) heproper (i := 0) ?_)
        intro x hx hxT
        have h4 : (finv x).val < 5 := hfinv5 x hxT
        have hj : xpt ⟨(finv x).val, h4⟩ = x := by
          rw [← invX _ h4]
          exact finv_spec x
        have hsx : (maskOf (fun j => decide (G.Adj (xpt j) (tpt t)))).val.testBit
            ((⟨(finv x).val, h4⟩ : Fin 5).val) = true := by
          have hAdj : G.Adj (xpt ⟨(finv x).val, h4⟩) (tpt t) := by
            rw [hj]
            exact (G.adj_comm (tpt t) x).mp hx
          rw [hsT t ⟨(finv x).val, h4⟩, decide_eq_true hAdj]
        have hb := hmono0 ⟨(finv x).val, h4⟩ hsx
        simp only [e, dif_pos h4, hb, bitCol_false]
      · refine hbad (tpt t) (htpt_mem t)
          (isBipartite_of_adjIn_mono (T := T) (t := tpt t) (ht := htpt_mem t) heproper (i := 1) ?_)
        intro x hx hxT
        have h4 : (finv x).val < 5 := hfinv5 x hxT
        have hj : xpt ⟨(finv x).val, h4⟩ = x := by
          rw [← invX _ h4]
          exact finv_spec x
        have hsx : (maskOf (fun j => decide (G.Adj (xpt j) (tpt t)))).val.testBit
            ((⟨(finv x).val, h4⟩ : Fin 5).val) = true := by
          have hAdj : G.Adj (xpt ⟨(finv x).val, h4⟩) (tpt t) := by
            rw [hj]
            exact (G.adj_comm (tpt t) x).mp hx
          rw [hsT t ⟨(finv x).val, h4⟩, decide_eq_true hAdj]
        have hb := hmono1 ⟨(finv x).val, h4⟩ hsx
        simp only [e, dif_pos h4, hb, bitCol_true]
    have key : ∀ (r : Fin 8) (hr : r.val = 2 ∨ r.val = 3 ∨ r.val = 4),
        noInd36 A s0.val s1.val s2 r.val = false := by
      intro r hr
      have hr2 : 2 ≤ r.val := by rcases hr with h | h | h <;> omega
      have hr4 : r.val ≤ 4 := by rcases hr with h | h | h <;> omega
      have hWcard := card_six_inv inv inv_inj r hr
      obtain ⟨S₀, hS₀sub, hS₀ind, hb⟩ :=
        hG ({inv 0, inv 1, inv r, inv 5, inv 6, inv 7} : Finset V)
      have hcard : 2 * S₀.card + 1 ≥ 6 := by simpa [hWcard] using hb
      obtain ⟨x1, x2, x3, hx1, hx2, hx3, h12, h23, h13⟩ :=
        three_distinct_of_card_ge_three S₀ (by omega)
      obtain ⟨u1, hu1⟩ := inv_surj x1
      obtain ⟨u2, hu2⟩ := inv_surj x2
      obtain ⟨u3, hu3⟩ := inv_surj x3
      have hu1inj : u1 ≠ u2 := by
        intro h
        exact h12 (calc x1 = inv u1 := hu1.symm
          _ = inv u2 := by rw [h]
          _ = x2 := hu2)
      have hu1inj' : u1 ≠ u3 := by
        intro h
        exact h13 (calc x1 = inv u1 := hu1.symm
          _ = inv u3 := by rw [h]
          _ = x3 := hu3)
      have hu2inj : u2 ≠ u3 := by
        intro h
        exact h23 (calc x2 = inv u2 := hu2.symm
          _ = inv u3 := by rw [h]
          _ = x3 := hu3)
      obtain ⟨a, b, c, hab', hbc', haM, hbM, hcM⟩ :=
        sort3 u1 u2 u3 hu1inj hu1inj' hu2inj
      have mem3 : ∀ p : Fin 8, p ∈ ({u1, u2, u3} : Finset (Fin 8)) →
          p = u1 ∨ p = u2 ∨ p = u3 := by
        intro p hp
        have hset : ({u1, u2, u3} : Finset (Fin 8)) = insert u1 (insert u2 (singleton u3)) := rfl
        rw [hset] at hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        exact hp
      have ha'0 : a = u1 ∨ a = u2 ∨ a = u3 := mem3 a haM
      have hb'0 : b = u1 ∨ b = u2 ∨ b = u3 := mem3 b hbM
      have hc'0 : c = u1 ∨ c = u2 ∨ c = u3 := mem3 c hcM
      have hvalOf : ∀ (p : Fin 8) (hp : p = u1 ∨ p = u2 ∨ p = u3) (y : V) (hxy : inv p = y)
          (hy : y ∈ ({inv 0, inv 1, inv r, inv 5, inv 6, inv 7} : Finset V)),
          p.val = 0 ∨ p.val = 1 ∨ p.val = r.val ∨ (5 ≤ p.val ∧ p.val < 8) := by
        intro p hp y hxy hy
        obtain ⟨i, hi, hii⟩ := mem_six_inv inv r y hy
        have hieq : i = p := inv_inj (by rw [hxy, hi])
        rwa [hieq] at hii
      have invMem : ∀ p : Fin 8, p = u1 ∨ p = u2 ∨ p = u3 →
          inv p ∈ ({inv 0, inv 1, inv r, inv 5, inv 6, inv 7} : Finset V) := by
        intro p hp
        rcases hp with rfl | rfl | rfl
        · rw [hu1]; exact hS₀sub hx1
        · rw [hu2]; exact hS₀sub hx2
        · rw [hu3]; exact hS₀sub hx3
      have ha' := hvalOf a ha'0 (inv a) rfl (invMem a ha'0)
      have hb' := hvalOf b hb'0 (inv b) rfl (invMem b hb'0)
      have hc' := hvalOf c hc'0 (inv c) rfl (invMem c hc'0)
      have hSind : ∀ x ∈ S₀, ∀ y ∈ S₀, x ≠ y → ¬ G.Adj x y := by
        intro x hx y hy hne
        exact hS₀ind hx hy hne
      have hmem : ∀ z : Nat, z = a.val ∨ z = b.val ∨ z = c.val →
          z = 0 ∨ z = 1 ∨ z = r.val ∨ (5 ≤ z ∧ z < 8) := by
        intro z hz
        rcases hz with rfl | rfl | rfl
        · exact ha'
        · exact hb'
        · exact hc'
      have hneFin : ∀ {p q : Fin 8}, p.val < q.val → p ≠ q := by
        intro p q h hcon
        exact absurd (congrArg Fin.val hcon) (by omega)
      have hInvAdj : ∀ {p q : Fin 8}, p = u1 ∨ p = u2 ∨ p = u3 → q = u1 ∨ q = u2 ∨ q = u3 →
          p ≠ q → G.Adj (inv p) (inv q) → False := by
        intro p q hp hq hpq hh
        rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
        · exact absurd rfl hpq
        · rw [hu1, hu2] at hh
          exact hSind x1 hx1 x2 hx2 h12 hh
        · rw [hu1, hu3] at hh
          exact hSind x1 hx1 x3 hx3 h13 hh
        · rw [hu2, hu1] at hh
          exact hSind x2 hx2 x1 hx1 (Ne.symm h12) hh
        · exact absurd rfl hpq
        · rw [hu2, hu3] at hh
          exact hSind x2 hx2 x3 hx3 h23 hh
        · rw [hu3, hu1] at hh
          exact hSind x3 hx3 x1 hx1 (Ne.symm h13) hh
        · rw [hu3, hu2] at hh
          exact hSind x3 hx3 x2 hx2 (Ne.symm h23) hh
        · exact absurd rfl hpq
      have hnab : (! adj8n A s0.val s1.val s2.val a.val b.val) = true := by
        have hnot : ¬ adj8n A s0.val s1.val s2.val a.val b.val := by
          rw [hadj8 a b]
          exact fun hh' => hInvAdj ha'0 hb'0 (hneFin hab') (of_decide_eq_true hh')
        simp [hnot]
      have hnac : (! adj8n A s0.val s1.val s2.val a.val c.val) = true := by
        have hnot : ¬ adj8n A s0.val s1.val s2.val a.val c.val := by
          rw [hadj8 a c]
          exact fun hh' => hInvAdj ha'0 hc'0 (hneFin (by omega)) (of_decide_eq_true hh')
        simp [hnot]
      have hnbc : (! adj8n A s0.val s1.val s2.val b.val c.val) = true := by
        have hnot : ¬ adj8n A s0.val s1.val s2.val b.val c.val := by
          rw [hadj8 b c]
          exact fun hh' => hInvAdj hb'0 hc'0 (hneFin hbc') (of_decide_eq_true hh')
        simp [hnot]
      have h3 : ind3n A s0.val s1.val s2.val a.val b.val c.val = true :=
        ind3n_of_nadj hab' hbc' hnab hnac hnbc
      exact noInd36_false_of_ind3n A s0 s1 s2 hr2 (by omega) h3 hab' hbc' c.isLt hmem
    have hE2 : noInd36 A s0.val s1.val s2 2 = false := key 2 (Or.inl rfl)
    have hE3 : noInd36 A s0.val s1.val s2 3 = false := key 3 (Or.inr (Or.inl rfl))
    have hE4 : noInd36 A s0.val s1.val s2 4 = false := key 4 (Or.inr (Or.inr rfl))
    have hyps : hyps8n A s0.val s1.val s2.val = true := by
      refine Bool.and_eq_true_iff.mpr ⟨
        Bool.and_eq_true_iff.mpr ⟨
          Bool.and_eq_true_iff.mpr ⟨
            Bool.and_eq_true_iff.mpr ⟨
              Bool.and_eq_true_iff.mpr
                ⟨Bool.and_eq_true_iff.mpr ⟨hmeet 0, hmeet 1⟩, hmeet 2⟩,
              tripleEmpty_of s0 s1 s2 htri⟩, hbadM 0⟩, hbadM 1⟩, hbadM 2⟩
    have hcontra : badSix' A s0.val s1.val s2.val = false := by
      simp [badSix', hE2, hE3, hE4]
    have hcontra' := loc8_lemma A s0 s1 s2 hyps
    rw [hcontra] at hcontra'
    exact Bool.noConfusion hcontra'
  rcases hex_or with hc | hc
  · exact main d hd' hc (by omega)
  · refine main (fun v => opp2 (d v)) ?_ ?_ ?_
    · intro v w hv hw hh hve
      exact hd' hv hw hh (hopp_inj _ _ hve)
    · have hcls0 : cls T (fun v => opp2 (d v)) 0 = cls T d 1 := by
        ext z
        simp only [mem_cls]
        constructor
        · rintro ⟨hz, hzz⟩
          exact ⟨hz, hopp_inj _ _ (hzz.trans opp2_one.symm)⟩
        · rintro ⟨hz, hzz⟩
          refine ⟨hz, ?_⟩
          rw [hzz]
          exact opp2_one
      rw [hcls0, hc]
    · have hcls1 : cls T (fun v => opp2 (d v)) 1 = cls T d 0 := by
        ext z
        simp only [mem_cls]
        constructor
        · rintro ⟨hz, hzz⟩
          exact ⟨hz, hopp_inj _ _ (hzz.trans opp2_zero.symm)⟩
        · rintro ⟨hz, hzz⟩
          refine ⟨hz, ?_⟩
          rw [hzz]
          exact opp2_zero
      rw [hcls1]
      omega

/-! ## Part 2 — **THE EIGHT-VERTEX INSTANCE WITH A SHORTEST ODD THREE-CYCLE**, with the constant `2`

`JSP90.triCaseEight` is the *triangle* case of the eight-vertex axis: it turns the counting step
`JSP90.loc8_lemma` into the statement "at `LocIndep 1` and `|V| ≤ 8` a triangle `T` has a vertex `t`
whose removal together with the other two leaves a bipartite graph".  Combined with round 166's
`JSP90.closeToBipartite_of_residue` (`lean/JSPProblem/Residue.lean`) this is already an instance of
the headline theorem, in the case where a shortest odd cycle has three vertices:

```lean
LocIndep 1 G → |V| ≤ 8 → (a shortest odd cycle C of G has C.card = 3) → CloseToBipartite 2 G
```

together with its transversal form (`∃ X, X.card ≤ 2 ∧ HitsOddCycles G X`), its `tauOdd` form
(`tauOdd G ≤ 2`) and its piece form (`V = ⋃ Wᵢ`, each `|Wᵢ| ≤ 8` ⟹ `CloseToBipartite 2 (G[Wᵢ])`).
The five- and seven-cycle cases at order eight remain open, so
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_eight` is deliberately **not** declared. -/

/-- **THE EIGHT-VERTEX INSTANCE IN THE CASE OF A SHORTEST ODD THREE-CYCLE, WITH THE CONSTANT `2`.** -/
theorem closeToBipartite_two_of_shortest_three_of_locIndep_one_card_le_eight
    (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 8) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (hC3 : C.card = 3) :
    CloseToBipartite 2 G := by
  have hT : G.IsNClique 3 C := isNClique_three_of_isOddCycle hC hC3
  obtain ⟨t, ht, hres⟩ := triCaseEight hG hV hT
  have hcard : (C \ {t}).card = 2 := by
    have h1 : ({t} : Finset V).card = 1 := Finset.card_singleton t
    have h2 := Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr ht)
    omega
  have hres' : CloseToBipartite 0 (deleteFinset G (C \ {t})) := by
    refine ⟨∅, by simp, ?_⟩
    simpa [deleteFinset_empty] using hres
  obtain ⟨X, hX, hbis⟩ := closeToBipartite_of_residue (C := C \ {t}) (q := 0) hres'
  exact ⟨X, by omega, hbis⟩

/-- **A TWO-ELEMENT ODD CYCLE TRANSVERSAL AT ORDER EIGHT, SHORTEST ODD CYCLE OF LENGTH THREE.** -/
theorem exists_hitsOddCycles_two_of_shortest_three_of_locIndep_one_card_le_eight
    (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 8) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (hC3 : C.card = 3) :
    ∃ X : Finset V, X.card ≤ 2 ∧ HitsOddCycles G X :=
  (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2)).mp
    (closeToBipartite_two_of_shortest_three_of_locIndep_one_card_le_eight hG hV hC hshort hC3)

/-- **THE SAME STATEMENT IN THE `tauOdd` FORM.** -/
theorem tauOdd_le_two_of_shortest_three_of_locIndep_one_card_le_eight
    (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 8) {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (hC3 : C.card = 3) :
    tauOdd G ≤ 2 :=
  (closeToBipartite_iff_tauOdd_le (G := G) (m := 2)).mp
    (closeToBipartite_two_of_shortest_three_of_locIndep_one_card_le_eight hG hV hC hshort hC3)

end
end JSP90
