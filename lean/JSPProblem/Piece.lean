/-
# JSP-000090 — `JSPProblem/Piece.lean`: the CUT-VERTEX PIECE axis, and the ONE-SIDED 1-CUT IS FREE

Round 109 (`JSPProblem/Chain.lean`) localised the remaining gap of the 1-cut axis very precisely:

* `JSP90.OneSplit.packing_part_le` — the *decrease* `r + 1 - s` at a 1-cut with `s` non-bipartite
  **parts**;
* `JSP90.OneSplit.packing_part_no_decrease_of_oneSide` — the descent **stalls** at a one-sided
  1-cut (`s = 1`);
* `JSP90.hardCert_isBipartite_of_packing_le` — the hard half of the block-cut bound is a theorem.

The two statements together leave exactly one object uncontrolled: **the one-sided chains** — cut
vertices with a single non-bipartite side.  `policy.json` recorded that they "cannot be bounded by
the packing number (a triangle with a pendant path has packing number `1` and arbitrarily long such
chains)", and that controlling them "needs the block-cut tree (or the classical short-`C`-path
lemma)", neither of which exists in the pinned Mathlib.

**This round shows that the block-cut tree is not needed at all.**  The object to control is not the
*part* but the ***piece*** `T_i ∪ {v}` — the part together with the cut vertex — and the two notions
differ in exactly the direction that matters:

* an odd cycle of `G` which **avoids** `v` lies in a part (`JSPProblem/Connect.lean`
  `OneSplit.cycle_subset_part`);
* an odd cycle of `G` which **meets** `v` lies in a *piece* — and this is exactly the structural
  lemma round 109 was missing.  It is `JSP90.OneSplit.cycle_subset_piece`, Part 1 below.

Once every odd cycle of `G` is an odd cycle of *some piece*, two things follow, both statements
about the whole graph rather than about one level of a decomposition.

## What is proved

| result | content |
| --- | --- |
| **`OneSplit.cycle_subset_piece`** | **THE MISSING STRUCTURAL LEMMA: an odd cycle containing the cut vertex `v` lies in `T_i ∪ {v}` for a single `i`** |
| `OneSplit.mem_part_of_adj` | the propagation step: two adjacent vertices avoiding `v`, one in the part `i`, both in the part `i` |
| `OneSplit.oddCycle_piece`, `OneSplit.isOddCycle_iff_pieces` | **the odd cycles of `G` are exactly the union of the odd cycles of the pieces** — the complete local structure at a cut vertex, in both directions |
| `deleteFinset_induceFinset_eq`, `isBipartite_deleteFinset_induceFinset` | the one-line bridge that moves the conclusion of Erdős #73 between `G` and a piece |
| `closeToBipartite_piece_of_closeToBipartite`, `closeToBipartite_pieces_of_closeToBipartite` | **MONOTONICITY AT A CUT VERTEX AT THE SAME CONSTANT: `CloseToBipartite m G` forces `CloseToBipartite m` on *every* piece** — the direction a cut-vertex induction needs |
| `closeToBipartite_of_1split_bounded_pieces` | **THE COMPOSITION RULE OF THE PIECE AXIS, WITHOUT THE `+1`: every piece `m`-close gives `CloseToBipartite (m * t) G`**, against the `1 + m * k` of `JSPProblem/Connect.lean` — the cut vertex is never charged |
| `closeToBipartite_of_1split_twoPieces` | **the sharp two-piece composition: if exactly two pieces are non-bipartite, both `m`-close, then `CloseToBipartite (2 * m) G`, independently of `t`** — the first constant on this axis that does not grow with the number of parts |
| `closeToBipartite_of_1split_nonBipartitePieces` | **only the non-bipartite pieces are charged**, constant `∑_{i ∈ nonBipartitePieces} m`, again with **no `+1`** |
| **`closeToBipartite_iff_of_oneNonBipartitePiece`** | **THE ONE-SIDED 1-CUT IS FREE: `CloseToBipartite m G ↔ CloseToBipartite m (T_{i₀} ∪ {v})`** when that piece is the only non-bipartite one.  The one-sided chains of `policy.json` are deleted **at zero cost**, and no tree and no path is needed |
| `isOddCycle_iff_of_oneNonBipartitePiece`, `hitsOddCycles_iff_of_oneNonBipartitePiece`, `not_isBipartite_of_oneNonBipartitePiece`, `locIndep_of_oneNonBipartitePiece` | **the reduction loses nothing at all**: the odd cycles of `G` *are* the odd cycles of the single non-bipartite piece, as the same finsets, and so are the odd cycle transversals |
| **`closeToBipartite_iff_of_twoSideCuts`** | **the reduction ITERATES**: two successive one-sided cuts reduce `G` to a single induced subgraph with `CloseToBipartite m` preserved in both directions — the classical block-cut reduction, machine-checked |
| `closeToBipartite_of_oneSideCut`, `hitsOddCycles_of_oneSideCut` | the one-step form in the `LocIndep` language: the hypothesis is checked on a strictly smaller graph and the constant does not grow |
| `erdos73On_of_1split_of_bounded_PIECES`, `oddCycleErdosPosa_of_1split_of_bounded_PIECES`, `erdos73On_of_1split_pieces_of_locIndep_sub` | **new instances of the headline theorem along the piece axis**, hypothesis on the *pieces*, constant `m * t`, **without** the `+1` and **without** the `|non-bipartite parts| ≤ k` counting step |

## A machine-checked obstruction: the piece count is *not* controlled by `k`

The piece axis buys the removal of the `+1`, the sharp `2 * m` constant and the exact one-sided
`iff`, but it does **not** buy a bound `|non-bipartite pieces| ≤ f(k)`, and this is machine-checked
on the graph `JSPProblem/Windmill.lean` already provides.  `JSP90.wf_oneSplit` is a **1-cut** of the
windmill at its central vertex `0` with the parts `{1, 2}`, `{3, 4}`, `{5}` (that file only had the
*2-cut* `{0, 5}`), and

* `JSP90.not_isBipartite_wf_piece_0`, `JSP90.not_isBipartite_wf_piece_1` — **two of its three
  pieces are non-bipartite**, each carrying one of the two triangles;
* **`JSP90.wf_locIndep_one_two_nonBipartitePieces`** — with `locIndep_one_wf`, `LocIndep 1 wf` holds
  and the cut has **two** non-bipartite pieces, i.e. more than `k = 1`.  So the hypothesis
  `|non-bipartite pieces| ≤ k` of the natural Erdős #73 instance along this axis is **false**, and
  `pieces` is a strictly finer notion than `parts`.

## What this does not give

The reduction of Parts 3–6 is *free*, but it is a reduction, not a bound: it says the difficulty of
`G` is the difficulty of one piece, and a piece is an arbitrary graph again.  A **chain** of
one-sided cuts (Part 6) therefore still ends at an arbitrary graph, and no bound on its transversal
number is obtained.  That is the classical block-cut reduction, now machine-checked; behind it
stands `JSP90.OddCycleErdosPosa r` for graphs with **no** cut vertex, i.e. 2-connected graphs, where
Mader's structure theorem and a Menger-type fan lemma are needed.  See
`discovery/JSP-000090/policy.json`.

## Toolchain notes

* `Nat.strong_induction_on` on a term `s` generalised over a goal of the form `P s` — with the
  surrounding `intro s hs1 hs2` — yields `ih (s - 1) (proof) hs1' hs2'`; the propagation `hrun` of
  `JSPProblem/SplitOne.lean` transfers verbatim.
* The index of `v` in the cyclic ordering enters through `hkey : ∀ s, f (mk s) = v ↔ s % m = j₀.val`
  and the companion `hnv : j₀.val < s → s < j₀.val + m → f (mk s) ≠ v`; together they are what lets
  the propagation ignore `v`.  Note that `v ∈ sp.parts i` is **not** refutable from a bare
  `OneSplit` (`OneSplit G v 1` with `parts 0 = univ` exists), so the step must obtain
  `f (mk (s-1)) ≠ v` from the interval, not from the part.
* `Finset.disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅`, so `.mp` (not `.mpr`) builds the
  equation from a `Disjoint`; `Iff.mpr` is elaborated *backwards*, so write the expected type first.
* `Finset.nonempty_iff_ne_empty : s.Nonempty ↔ s ≠ ∅` — give it `(s := …)` explicitly, or the
  `.mpr`/`.mp` direction is elaborated against the wrong side of the equivalence; `x ∈ s ∩ t` is a
  `Multiset` membership, so `hx.1` is not a projection: use `Finset.mem_inter.mp hx`.
* `Finset.mem_union_left (t) (h : a ∈ s) : a ∈ s ∪ t` has `s` implicit and unannotated, so write the
  union membership as `Finset.mem_union.mpr (Or.inl …)` with an expected type.
* `¬ ¬ p → p` is `not_not.mp`, and it is *not* `Classical.byContradiction`; in a
  `by_cases`-free branch use `not_not.mp (fun hn => … hn)`.
* `Finset.ext z` + `fin_cases z` + `simp` is the reliable way to prove `s ∩ t = ∅` for literal finsets
  here: `decide` gets stuck in `List.filter … |>.isPerm`, and `Finset.mem_inter.mp` re-synthesises
  a *different* `DecidableEq` instance from the one baked into the literal.
* A theorem whose first binder is `[Fintype V]` is **not** put in the namespace of its `OneSplit`
  argument: `JSP90.closeToBipartite_of_1split_bounded_pieces sp h`, not `sp.…`.
-/

import JSPProblem.Chain
import JSPProblem.Windmill

namespace JSP90

open Finset Fintype Set

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqPiece : DecidableEq V := Classical.decEq V

/-! ### Part 0 — the elementary bridge: a piece of a deletion -/

/-- **Deleting `X` from the induced subgraph on `S` is the induced subgraph on `S` of the deletion
of `X`.**  This is the one-line bridge that lets the conclusion of Erdős #73 move from `G` to a
piece and back. -/
theorem deleteFinset_induceFinset_eq [Fintype V] (H : SimpleGraph V) (S X : Finset V) :
    deleteFinset (induceFinset H S) X = induceFinset (deleteFinset H X) S := by
  ext a b
  simp [deleteFinset_adj, induce_adj, and_comm, and_left_comm, and_assoc]

/-- **A bipartite deletion stays bipartite when one restricts to an induced subgraph.** -/
theorem isBipartite_deleteFinset_induceFinset [Fintype V] {S X : Finset V}
    (h : (deleteFinset G X).IsBipartite) :
    (deleteFinset (induceFinset G S) X).IsBipartite := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun {a b} hadj => ?_⟩
  rw [deleteFinset_adj] at hadj
  have hadj' := induce_adj.mp hadj.2.2
  refine hc ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, hadj.1⟩,
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hadj.2.1⟩, hadj'.2.2⟩

/-! ### Part 1 — THE MISSING STRUCTURAL LEMMA -/

section CyclePiece

variable {v : V} {t : ℕ} (sp : OneSplit G v t)

/-- **Two adjacent vertices which both avoid the cut vertex and one of which lies in the part `i`
both lie in the part `i`.**  This is the propagation step: no edge joins two distinct parts
(`OneSplit.hanti`). -/
theorem OneSplit.mem_part_of_adj {x y : V} {i : Fin t} (hAdj : G.Adj x y) (hx : x ∈ sp.parts i)
    (hxv : x ≠ v) (hyv : y ≠ v) : y ∈ sp.parts i := by
  obtain ⟨j, hj⟩ := sp.mem_parts hyv
  by_contra hc
  have hne : j ≠ i := fun h => hc (h ▸ hj)
  exact (sp.hanti i j (Ne.symm hne) x hx y hj) hAdj

/-- **THE MISSING STRUCTURAL LEMMA: AN ODD CYCLE WHICH CONTAINS THE CUT VERTEX `v` LIES IN A SINGLE
PIECE `T_i ∪ {v}`.**

Together with `JSPProblem/Connect.lean` `OneSplit.cycle_subset_part` (a cycle *avoiding* `v` lies in
a part) this is the **complete local structure at a cut vertex**: *every* cycle of `G` lies in a
piece.

The reason is that a simple cycle meets `v` exactly once, so cutting the cyclic order at that index
leaves a **path** whose vertices all avoid `v`; no edge joins two distinct parts, so the whole path
lies in one part.  The proof performs the corresponding propagation on the `ℕ`-indexed model
`mk s = s % m` of the cyclic order: the vertices of the cycle equal to `v` are exactly the indices
congruent to `j₀.val`, so on the interval `[j₀.val + 1, j₀.val + m - 1]` — which contains one
representative of every other residue class — no vertex is `v` and the propagation runs in a
straight line. -/
theorem OneSplit.cycle_subset_piece {C : Finset V} (hC : IsOddCycle G C) (hv : v ∈ C) :
    ∃ i : Fin t, C ⊆ insert v (sp.parts i) := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hmpos : 0 < m := lt_of_lt_of_le (by omega : 0 < 3) hm3
  let mk : ℕ → Fin m := fun s => ⟨s % m, Nat.mod_lt _ (by omega)⟩
  have hmod : ∀ s : ℕ, (s % m + 1) % m = (s + 1) % m := by
    intro s
    calc (s % m + 1) % m
        = ((s % m + 1) + m * (s / m)) % m := by rw [Nat.add_mul_mod_self_left]
      _ = (s + 1) % m := by
          have h2 : (s % m + 1) + m * (s / m) = s + 1 := by
            have h3 := Nat.mod_add_div s m
            omega
          rw [h2]
  have hstep : ∀ s : ℕ, G.Adj (f (mk s)) (f (mk (s + 1))) := by
    intro s
    have h := hcyc (mk s)
    have hval : (s % m + 1) % m = (s + 1) % m := hmod s
    have heq : f (cycSucc (mk s)) = f (mk (s + 1)) := congrArg f (Fin.ext hval)
    rw [heq] at h
    exact h
  have hmk : ∀ p q : ℕ, p % m = q % m → mk p = mk q := by
    intro p q h
    exact Fin.ext h
  have hmk_wrap : ∀ q : ℕ, q < m → mk (q + m) = mk q := by
    intro q hq
    refine Fin.ext ?_
    show (q + m) % m = q % m
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  have hmemC : ∀ s : ℕ, f (mk s) ∈ C := fun s => (hCmem (f (mk s))).mpr ⟨mk s, rfl⟩
  obtain ⟨j₀, hj₀⟩ := (hCmem v).mp hv
  have hv₀ : f (mk j₀.val) = v := by
    have hval : mk j₀.val = j₀ := Fin.ext (Nat.mod_eq_of_lt j₀.isLt)
    rw [hval]
    exact hj₀
  -- the vertices of the cycle equal to `v` are exactly the indices congruent to `j₀.val`
  have hkey : ∀ s : ℕ, f (mk s) = v ↔ s % m = j₀.val := by
    intro s
    constructor
    · intro h
      have hval : s % m = j₀.val % m := by
        have hmk' : mk s = mk j₀.val := hinj (h ▸ hv₀.symm)
        exact congrArg Fin.val hmk'
      rw [Nat.mod_eq_of_lt j₀.isLt] at hval
      exact hval
    · intro h
      have hval : mk s = mk j₀.val := hmk s j₀.val
        (by rw [Nat.mod_eq_of_lt j₀.isLt]; exact h)
      exact (congrArg f hval).trans hv₀
  -- on the interval strictly between `j₀.val` and `j₀.val + m` no vertex is `v`
  have hnv : ∀ s : ℕ, j₀.val < s → s < j₀.val + m → f (mk s) ≠ v := by
    intro s hs1 hs2 hcon
    have hmod' : s % m ≠ j₀.val := by
      rcases lt_or_ge s m with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt]
        omega
      · have hne0 : s / m ≠ 0 := by
          intro hc
          rcases Nat.div_eq_zero_iff.mp hc with hm | hlt
          · exact absurd hm (Nat.ne_of_gt hmpos)
          · exact absurd hlt (Nat.not_lt_of_ge hge)
        have hmul : m ≤ m * (s / m) := by
          simpa using Nat.mul_le_mul_left m (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne0))
        have h3 := Nat.mod_add_div s m
        omega
    exact hmod' ((hkey s).mp hcon)
  -- the part of the first vertex after `v`
  obtain ⟨i₀, hi₀⟩ := sp.mem_parts (hnv (j₀.val + 1) (by omega) (by omega))
  -- the propagation, along the whole interval
  have hrun : ∀ s : ℕ, j₀.val + 1 ≤ s → s ≤ j₀.val + m - 1 →
      f (mk s) ∈ sp.parts i₀ := by
    intro s hs1 hs2
    induction s using Nat.strong_induction_on with
    | _ s ih =>
        by_cases hs : s = j₀.val + 1
        · rw [hs]
          exact hi₀
        · have hprev : j₀.val + 1 ≤ s - 1 := by omega
          have hval : mk (s - 1 + 1) = mk s := by congr 1; omega
          have hadj := hstep (s - 1)
          rw [hval] at hadj
          have hx : f (mk (s - 1)) ∈ sp.parts i₀ := ih (s - 1) (by omega) hprev (by omega)
          exact sp.mem_part_of_adj hadj hx (hnv (s - 1) (by omega) (by omega))
            (hnv s (by omega) (by omega))
  refine ⟨i₀, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := (hCmem x).mp hx
  by_cases hxv : f j = v
  · -- the case `x = v`
    have hxvv : x = v := by rw [← hj]; exact hxv
    rw [hxvv]
    exact Finset.mem_insert_self v _
  · -- `f j ≠ v`: the representative of `j.val` in the interval `[j₀.val+1, j₀.val+m-1]` is
    -- either `j.val` itself or `j.val + m`
    have hjlt : j.val < m := j.isLt
    have hmj : mk j.val = j := Fin.ext (Nat.mod_eq_of_lt hjlt)
    have hne' : j.val ≠ j₀.val := fun h => hxv (by
      have hmk' : mk j.val = mk j₀.val :=
        hmk j.val j₀.val (by rw [h, Nat.mod_eq_of_lt j₀.isLt])
      rw [← hmj, ← hv₀]
      exact congrArg f hmk')
    have hmem : f (mk j.val) ∈ sp.parts i₀ := by
      by_cases hgt : j₀.val < j.val
      · exact hrun j.val (by omega) (by omega)
      · have h3 := hrun (j.val + m) (by omega) (by omega)
        rw [hmk_wrap j.val hjlt] at h3
        exact h3
    rw [hmj] at hmem
    rw [← hj]
    exact Finset.mem_insert_of_mem hmem

end CyclePiece

/-! ### Part 2 — the odd cycles of `G` are the odd cycles of the pieces -/

section OddCycles

variable {v : V} {t : ℕ} (sp : OneSplit G v t)

/-- **AN ODD CYCLE OF `G` IS AN ODD CYCLE OF ONE PIECE.**  The complete local structure at a cut
vertex, in the direction that matters: every odd cycle of `G` lives in a single piece
`T_i ∪ {v}`. -/
theorem OneSplit.oddCycle_piece [Fintype V] {C : Finset V} (hC : IsOddCycle G C) :
    ∃ i : Fin t, IsOddCycle (induceFinset G (insert v (sp.parts i))) C ∧
      C ⊆ insert v (sp.parts i) := by
  by_cases hv : v ∈ C
  · obtain ⟨i, hi⟩ := sp.cycle_subset_piece hC hv
    exact ⟨i, hC.induceFinset hi, hi⟩
  · have hd : Disjoint C ({v} : Finset V) := Finset.disjoint_singleton_right.mpr hv
    have hvc : C ∩ ({v} : Finset V) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty (s := C) (t := {v}) |>.mp hd
    obtain ⟨i, hi⟩ := sp.cycle_subset_part hC hvc
    exact ⟨i, hC.induceFinset (fun y hy => Finset.mem_insert_of_mem (hi hy)),
      fun y hy => Finset.mem_insert_of_mem (hi hy)⟩

/-- **THE COMPLETE LOCAL STRUCTURE AT A CUT VERTEX, AS AN EQUIVALENCE: the odd cycles of `G` are
exactly the odd cycles of the pieces.**

The reverse direction of `OneSplit.oddCycle_piece`: the pieces are induced subgraphs of `G`, so an
odd cycle of a piece is an odd cycle of `G`.  Nothing is lost by passing from `G` to the pieces —
this is the 1-cut analogue of `JSP90.hitsOddCycles_iff_hitsMono` (round 93) for the max-cut axis. -/
theorem OneSplit.isOddCycle_iff_pieces [Fintype V] {C : Finset V} :
    IsOddCycle G C ↔ ∃ i : Fin t, IsOddCycle (induceFinset G (insert v (sp.parts i))) C := by
  constructor
  · intro hC
    obtain ⟨i, hi, -⟩ := sp.oddCycle_piece hC
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact hi.of_induceFinset

end OddCycles

/-! ### Part 3 — the composition rule, and the exact characterisation at a cut vertex -/

section Composition

variable {v : V} {t : ℕ} (sp : OneSplit G v t)

/-- **`CloseToBipartite` descends to a piece.**  The hypothesis of Erdős #73, restricted to the
piece `T_i ∪ {v}`, gives the conclusion there — the induction step of the classical proof, in the
form in which it is actually used. -/
theorem closeToBipartite_piece_of_closeToBipartite [Fintype V] {m : ℕ} {i : Fin t}
    (hG : CloseToBipartite m G) :
    CloseToBipartite m (induceFinset G (insert v (sp.parts i))) := by
  obtain ⟨X, hX, hb⟩ := hG
  exact ⟨X, hX, isBipartite_deleteFinset_induceFinset hb⟩

/-- **THE COMPOSITION RULE OF THE PIECE AXIS, WITHOUT THE `+1`: if every piece `T_i ∪ {v}` of a
1-cut is `m`-close to bipartite then so is `G`.**

Compare `JSPProblem/Connect.lean` `closeToBipartite_of_1split_of_bounded_pieces`
(`CloseToBipartite (1 + m * k) G`): there, an odd cycle which **meets** `v` must be hit by `v`
itself, because only the *parts* were assumed to be close.  Here the pieces contain `v`, so the
cut vertex is **never charged**, and the constant is `m * t` with no `+1`.  The number `t` of parts
enters instead of `k`, which Part 5 shows cannot be replaced by a function of `k`. -/
theorem closeToBipartite_of_1split_bounded_pieces {m : ℕ} [Fintype V] (sp : OneSplit G v t)
    (h : ∀ i : Fin t, CloseToBipartite m (induceFinset G (insert v (sp.parts i)))) :
    CloseToBipartite (m * t) G := by
  classical
  have hex : ∀ i : Fin t, ∃ Z : Finset V, Z.card ≤ m ∧
      (deleteFinset (induceFinset G (insert v (sp.parts i))) Z).IsBipartite := fun i => h i
  set Z : Fin t → Finset V := fun i => (hex i).choose with hZdef
  have hZc : ∀ i : Fin t, Z i = (hex i).choose := fun i => hZdef ▸ rfl
  have hZcard : ∀ i : Fin t, (Z i).card ≤ m := by
    intro i
    rw [hZc i]
    exact ((hex i).choose_spec).1
  have hZhits : ∀ i : Fin t, HitsOddCycles (induceFinset G (insert v (sp.parts i))) (Z i) := by
    intro i
    rw [hZc i]
    exact hitsOddCycles_of_isBipartite_delete ((hex i).choose_spec).2
  set Y : Finset V := (Finset.univ : Finset (Fin t)).biUnion Z with hYdef
  have hYsub : ∀ i : Fin t, Z i ⊆ Y := by
    intro i
    exact fun x hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  have hYhits : HitsOddCycles G Y := by
    intro C hC hdis
    obtain ⟨i, hi, -⟩ := sp.oddCycle_piece hC
    have hne : (C ∩ Z i) ≠ ∅ := hZhits i C hi
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty (s := C ∩ Z i) |>.mpr hne
    have hxm := Finset.mem_inter.mp hx
    have hne'' : (C ∩ Y).Nonempty :=
      ⟨x, Finset.mem_inter.mpr ⟨hxm.1, hYsub i hxm.2⟩⟩
    have hne' : C ∩ Y ≠ ∅ := Finset.nonempty_iff_ne_empty (s := C ∩ Y) |>.mp hne''
    rw [hdis] at hne'
    simp at hne'
  have hYcard : Y.card ≤ m * t := by
    have h1 : Y.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)), (Z i).card :=
      Finset.card_biUnion_le
    have h2 : (∑ i ∈ (Finset.univ : Finset (Fin t)), (Z i).card)
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)), m :=
      Finset.sum_le_sum fun i _ => hZcard i
    have h3 : (∑ i ∈ (Finset.univ : Finset (Fin t)), m) = m * t := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      exact Nat.mul_comm _ _
    omega
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := m * t)).mpr ⟨Y, hYcard, hYhits⟩

/-- **MONOTONICITY ALONG A CUT VERTEX, AT THE *SAME* CONSTANT.**  `CloseToBipartite m G` forces
`CloseToBipartite m` on **every** piece `T_i ∪ {v}`.

An odd cycle of a piece is an odd cycle of `G`, so a transversal of `G` is a transversal of each
piece; the odd cycle transversal number of a graph dominates that of each of its induced
subgraphs, and the pieces are induced subgraphs.  **This is the direction a cut-vertex induction
needs**: the hypothesis descends to the pieces with no loss at all, and the *conclusion* is the
part which costs something (`closeToBipartite_of_1split_bounded_pieces`).

**A statement that looks natural and is FALSE.**  It is tempting to combine the two directions into
the biconditional `CloseToBipartite m G ↔ ∀ i, CloseToBipartite m (T_i ∪ {v})`.  The forward
direction is the theorem just proved; the backward one fails, and the composition `m * t` cannot be
replaced by `m`: take two vertex-disjoint triangles, each carrying a pendant vertex at the common
cut vertex `v`.  Each piece is a triangle with a pendant, hence `1`-close to bipartite, but the two
triangles are disjoint and neither meets `v`, so `G` is not `1`-close.  The exact `iff` that *is*
true is the **one-sided** one, `JSP90.closeToBipartite_iff_of_oneNonBipartitePiece`. -/
theorem closeToBipartite_pieces_of_closeToBipartite {m : ℕ} [Fintype V] (sp : OneSplit G v t)
    (h : CloseToBipartite m G) :
    ∀ i : Fin t, CloseToBipartite m (induceFinset G (insert v (sp.parts i))) := by
  intro i
  obtain ⟨X, hX, hb⟩ := h
  exact ⟨X, hX, isBipartite_deleteFinset_induceFinset hb⟩

/-- **THE SHARP TWO-PIECE COMPOSITION.**  If exactly two pieces of a 1-cut are non-bipartite, both
being `m`-close to bipartite, then `G` is `2 * m`-close to bipartite — **independently of `t`**.

This is the first constant on this axis that does not grow with the number of parts, and it is the
form in which the block-cut tree is used: a chain of 1-cuts meets a *bounded* number of non-bipartite
pieces at each level. -/
theorem closeToBipartite_of_1split_twoPieces {m : ℕ} {i₀ i₁ : Fin t} [Fintype V]
    (sp : OneSplit G v t) (hne : i₀ ≠ i₁)
    (h0 : CloseToBipartite m (induceFinset G (insert v (sp.parts i₀))))
    (h1 : CloseToBipartite m (induceFinset G (insert v (sp.parts i₁))))
    (hrest : ∀ i : Fin t, ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite →
        i = i₀ ∨ i = i₁) : CloseToBipartite (2 * m) G := by
  classical
  obtain ⟨Z₀, hZ₀, hb₀⟩ := h0
  obtain ⟨Z₁, hZ₁, hb₁⟩ := h1
  set Y : Finset V := Z₀ ∪ Z₁ with hYdef
  have step : ∀ (H : SimpleGraph V) (W : Finset V), HitsOddCycles H W → W ⊆ Y →
      ∀ (C' : Finset V), IsOddCycle H C' → C' ∩ Y = ∅ → HitsOddCycles G Y := by
    intro H W hW hsub C' hC' hdisY
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty (s := C' ∩ W) |>.mpr (hW C' hC')
    have hxm := Finset.mem_inter.mp hx
    have hbad : x ∈ C' ∩ Y := Finset.mem_inter.mpr ⟨hxm.1, hsub hxm.2⟩
    rw [hdisY] at hbad
    simp at hbad
  have hYhits : HitsOddCycles G Y := by
    intro C hC hdis
    obtain ⟨i, hi, -⟩ := sp.oddCycle_piece hC
    have hnb : ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite :=
      fun hb => (not_isOddCycle_of_isBipartite hb) ⟨C, hi⟩
    rcases hrest i hnb with heq | heq
    · rw [heq] at hi
      exact (step (induceFinset G (insert v (sp.parts i₀))) Z₀
        (hitsOddCycles_of_isBipartite_delete
          (G := induceFinset G (insert v (sp.parts i₀))) hb₀)
        (by rw [hYdef]; exact Finset.subset_union_left) C hi hdis) C hC hdis
    · rw [heq] at hi
      exact (step (induceFinset G (insert v (sp.parts i₁))) Z₁
        (hitsOddCycles_of_isBipartite_delete
          (G := induceFinset G (insert v (sp.parts i₁))) hb₁)
        (by rw [hYdef]; exact Finset.subset_union_right) C hi hdis) C hC hdis
  have hYcard : Y.card ≤ 2 * m := by
    have h1 : (Z₀ ∪ Z₁).card ≤ Z₀.card + Z₁.card := Finset.card_union_le _ _
    rw [hYdef]
    omega
  exact (closeToBipartite_iff_hitsOddCycles (G := G) (m := 2 * m)).mpr
    ⟨Y, hYcard, hYhits⟩

end Composition

/-! ### Part 4 — only the non-bipartite pieces are charged -/

section NonBipartitePieces

variable {v : V} {t : ℕ} (sp : OneSplit G v t)

local instance instDecidablePredNBP : DecidablePred fun i : Fin t =>
    ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite := fun _ => Classical.propDecidable _

/-- **THE COMPOSITION RULE CHARGING ONLY THE NON-BIPARTITE PIECES, WITH NO `+1` FOR THE CUT
VERTEX:**

> every non-bipartite piece `T_i ∪ {v}` being `m`-close to bipartite gives
> `CloseToBipartite (∑_{i ∈ nonBipartitePieces} m) G`.

This is the strict improvement on `JSPProblem/Connect.lean`
`closeToBipartite_of_1split_of_bounded_pieces` (`1 + m * k`): the pieces contain `v`, so no vertex
is charged for the cut itself, and only the pieces which actually carry an odd cycle are paid for. -/
theorem closeToBipartite_of_1split_nonBipartitePieces {m : ℕ} [Fintype V] (sp : OneSplit G v t)
    (h : ∀ i ∈ sp.nonBipartitePieces,
      CloseToBipartite m (induceFinset G (insert v (sp.parts i)))) :
    CloseToBipartite (∑ i ∈ sp.nonBipartitePieces, m) G := by
  classical
  have hmemf : ∀ i : Fin t, i ∈ sp.nonBipartitePieces →
      ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hex : ∀ i : Fin t, ∃ Z : Finset V, Z.card ≤ m ∧
      (deleteFinset (induceFinset G (insert v (sp.parts i))) Z).IsBipartite := by
    intro i
    by_cases hi : i ∈ sp.nonBipartitePieces
    · obtain ⟨Z, hZ, hZb⟩ := h i hi
      exact ⟨Z, hZ, hZb⟩
    · refine ⟨∅, Nat.zero_le m, ?_⟩
      rw [deleteFinset_empty]
      refine not_not.mp fun hn => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn⟩)
  set Z : Fin t → Finset V := fun i => (hex i).choose with hZdef
  have hZc : ∀ i : Fin t, Z i = (hex i).choose := fun i => hZdef ▸ rfl
  have hZcard : ∀ i : Fin t, (Z i).card ≤ m := by
    intro i
    rw [hZc i]
    exact ((hex i).choose_spec).1
  have hZhits : ∀ i : Fin t, HitsOddCycles (induceFinset G (insert v (sp.parts i))) (Z i) := by
    intro i
    rw [hZc i]
    exact hitsOddCycles_of_isBipartite_delete ((hex i).choose_spec).2
  set Y : Finset V := sp.nonBipartitePieces.biUnion Z with hYdef
  have hYsub : ∀ i ∈ sp.nonBipartitePieces, Z i ⊆ Y :=
    fun i hi x hx => Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
  have hYhits : HitsOddCycles G Y := by
    intro C hC hdis
    obtain ⟨i, hi, -⟩ := sp.oddCycle_piece hC
    by_cases hip : i ∈ sp.nonBipartitePieces
    · have hne : (C ∩ Z i) ≠ ∅ := hZhits i C hi
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty (s := C ∩ Z i) |>.mpr hne
      have hxm := Finset.mem_inter.mp hx
      have hne'' : (C ∩ Y).Nonempty :=
        ⟨x, Finset.mem_inter.mpr ⟨hxm.1, hYsub i hip hxm.2⟩⟩
      have hne' : C ∩ Y ≠ ∅ := Finset.nonempty_iff_ne_empty (s := C ∩ Y) |>.mp hne''
      rw [hdis] at hne'
      simp at hne'
    · have hb : (induceFinset G (insert v (sp.parts i))).IsBipartite :=
        not_not.mp fun hn => hip (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn⟩)
      exact (not_isOddCycle_of_isBipartite hb) ⟨C, hi⟩
  have hYcard : Y.card ≤ ∑ i ∈ sp.nonBipartitePieces, m := by
    have h1 : Y.card ≤ ∑ i ∈ sp.nonBipartitePieces, (Z i).card :=
      Finset.card_biUnion_le
    have h2 : (∑ i ∈ sp.nonBipartitePieces, (Z i).card) ≤ ∑ i ∈ sp.nonBipartitePieces, m :=
      Finset.sum_le_sum fun i hi => hZcard i
    omega
  exact (closeToBipartite_iff_hitsOddCycles (G := G)
    (m := ∑ i ∈ sp.nonBipartitePieces, m)).mpr ⟨Y, hYcard, hYhits⟩

end NonBipartitePieces

/-! ### Part 5 — new instances of the headline theorem along the piece axis -/

section Instances

variable {v : V} {t : ℕ} (sp : OneSplit G v t)

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM ALONG THE PIECE AXIS.**  If `LocIndep k` forces
`CloseToBipartite m` in every *piece* `T_i ∪ {v}` of a 1-cut of `G`, then it forces
`CloseToBipartite (m * t) G`.

Two things are new with respect to `JSPProblem/Connect.lean` `erdos73On_of_1split_of_bounded_pieces`
(`1 + m * k`, hypothesis on the **parts**):

* the hypothesis is on the **pieces** — the objects `OneDepth` and the block-cut reduction are
  actually about — and `LocIndep k` restricts to a piece (`LocIndep.of_induceFinset`) with no
  extra hypothesis;
* the constant has **no `+1`**: the cut vertex lives in every piece, so it is never charged. -/
theorem erdos73On_of_1split_of_bounded_PIECES (k m t : ℕ) [Fintype V] (sp : OneSplit G v t)
    (hpiece : ∀ i : Fin t, LocIndep k (induceFinset G (insert v (sp.parts i))) →
      CloseToBipartite m (induceFinset G (insert v (sp.parts i))))
    (hG : LocIndep k G) : CloseToBipartite (m * t) G :=
  closeToBipartite_of_1split_bounded_pieces sp fun i => hpiece i (hG.of_induceFinset _)

/-- **The same instance in the packing language, the form in which the research statement
(`JSP90.OddCycleErdosPosa`) lives.**  The packing bound restricts to every piece
(`IsOddCycleFamily.of_induceFinset`) and the pieces' transversal bounds compose with **no** charge
for the cut vertex. -/
theorem oddCycleErdosPosa_of_1split_of_bounded_PIECES {r m : ℕ} [Fintype V]
    (sp : OneSplit G v t)
    (hpiece : ∀ i : Fin t,
      (∀ C : Finset (Finset V),
        IsOddCycleFamily (G := induceFinset G (insert v (sp.parts i))) C → C.card ≤ r) →
        CloseToBipartite m (induceFinset G (insert v (sp.parts i))))
    (hpack : ∀ C : Finset (Finset V), IsOddCycleFamily (G := G) C → C.card ≤ r) :
    CloseToBipartite (m * t) G :=
  closeToBipartite_of_1split_bounded_pieces sp fun i => hpiece i
    (fun C hC => hpack C hC.of_induceFinset)

/-- **The hypothesis may be checked on `G` alone**: it is enough that `LocIndep k G` forces
`CloseToBipartite m` on every piece *as an induced subgraph*, and the pieces' bounds compose with
the constant `m * t`.  This is the form in which a cut-vertex decomposition is actually consumed. -/
theorem erdos73On_of_1split_pieces_of_locIndep_sub {k m t : ℕ} [Fintype V] (sp : OneSplit G v t)
    (hG : LocIndep k G)
    (hpiece : ∀ i : Fin t, CloseToBipartite m (induceFinset G (insert v (sp.parts i)))) :
    CloseToBipartite (m * t) G :=
  erdos73On_of_1split_of_bounded_PIECES (k := k) (m := m) (t := t) sp
    (fun i _ => hpiece i) hG

end Instances

/-! ### Part 6 — THE ONE-SIDED 1-CUT IS FREE -/

section OneSided

variable {v : V} {t : ℕ} (sp : OneSplit G v t)

local instance instDecidablePredNBP2 : DecidablePred fun i : Fin t =>
    ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite := fun _ => Classical.propDecidable _

/-- **THE ONE-SIDED 1-CUT IS FREE.**

> if the piece `T_{i₀} ∪ {v}` is the **only** non-bipartite piece of a 1-cut of `G`, then
> `CloseToBipartite m G ↔ CloseToBipartite m (T_{i₀} ∪ {v})`.

This is the statement that removes the *one-sided chains* — the object `policy.json` recorded as the
single remaining gap of the 1-cut axis after round 109, and the object for which it demanded the
block-cut tree or the short-`C`-path lemma.  **No tree and no path is needed:** by Part 2 every
odd cycle of `G` is an odd cycle of a piece, and the other pieces are bipartite, so they carry none;
the whole difficulty of `G` — and the whole of its odd-cycle structure — is the difficulty of the
single non-bipartite piece.  The bipartite side of the cut is simply deleted, at no cost.

Consequences: a triangle with a pendant path (the witness that one-sided chains are unbounded for
the *packing number*) is **`1`-close to bipartite, because its single triangle is**. -/
theorem closeToBipartite_iff_of_oneNonBipartitePiece {m : ℕ} {i₀ : Fin t} [Fintype V]
    (sp : OneSplit G v t)
    (huniq : ∀ i : Fin t, ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite → i = i₀)
    (hi₀ : ¬ (induceFinset G (insert v (sp.parts i₀))).IsBipartite) :
    CloseToBipartite m G ↔ CloseToBipartite m (induceFinset G (insert v (sp.parts i₀))) := by
  constructor
  · intro h
    exact closeToBipartite_piece_of_closeToBipartite sp (i := i₀) h
  · intro h
    obtain ⟨Z, hZ, hb⟩ := h
    refine (closeToBipartite_iff_hitsOddCycles (G := G) (m := m)).mpr ⟨Z, hZ, ?_⟩
    intro C hC hdis
    obtain ⟨i, hi, -⟩ := sp.oddCycle_piece hC
    have hnb : ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite :=
      fun hb' => (not_isOddCycle_of_isBipartite hb') ⟨C, hi⟩
    have heq : i = i₀ := huniq i hnb
    rw [heq] at hi
    have hne : (C ∩ Z) ≠ ∅ := hitsOddCycles_of_isBipartite_delete
      (G := induceFinset G (insert v (sp.parts i₀))) hb C hi
    rw [hdis] at hne
    simp at hne

/-- **THE REDUCTION LOSES NOTHING AT ALL: the odd cycles of `G` are the odd cycles of the single
non-bipartite piece.**  Not merely the transversal number but the whole odd-cycle structure — every
odd cycle, as the same finset — is preserved. -/
theorem isOddCycle_iff_of_oneNonBipartitePiece [Fintype V] {i₀ : Fin t} (sp : OneSplit G v t)
    (huniq : ∀ i : Fin t, ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite → i = i₀)
    (hi₀ : ¬ (induceFinset G (insert v (sp.parts i₀))).IsBipartite) {C : Finset V} :
    IsOddCycle G C ↔ IsOddCycle (induceFinset G (insert v (sp.parts i₀))) C := by
  constructor
  · intro hC
    obtain ⟨i, hi, -⟩ := sp.oddCycle_piece hC
    have hnb : ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite :=
      fun hb => (not_isOddCycle_of_isBipartite hb) ⟨C, hi⟩
    have heq : i = i₀ := huniq i hnb
    simpa [heq] using hi
  · intro hC
    exact hC.of_induceFinset

/-- **Bipartiteness is preserved by the reduction**: `G` is bipartite iff its single non-bipartite
piece is bipartite (in which case `G` is bipartite and the hypothesis `hi₀` fails; the statement
below is the useful direction, that a non-bipartite `G` is witnessed by `i₀`). -/
theorem not_isBipartite_of_oneNonBipartitePiece [Fintype V] {i₀ : Fin t} (sp : OneSplit G v t)
    (huniq : ∀ i : Fin t, ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite → i = i₀)
    (hnb : ¬ G.IsBipartite) :
    ¬ (induceFinset G (insert v (sp.parts i₀))).IsBipartite := by
  by_contra hb
  exact hnb (sp.isBipartite_of_bipartite_pieces fun i => by
    by_cases h : i = i₀
    · rw [h]
      exact hb
    · exact not_not.mp fun hn => absurd (huniq i hn) h)

/-- **Odd cycle transversals are preserved by the reduction**, as sets. -/
theorem hitsOddCycles_iff_of_oneNonBipartitePiece [Fintype V] {i₀ : Fin t} (sp : OneSplit G v t)
    (huniq : ∀ i : Fin t, ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite → i = i₀)
    (hi₀ : ¬ (induceFinset G (insert v (sp.parts i₀))).IsBipartite) {X : Finset V} :
    HitsOddCycles G X ↔ HitsOddCycles (induceFinset G (insert v (sp.parts i₀))) X := by
  constructor
  · intro h C hC
    exact h C ((isOddCycle_iff_of_oneNonBipartitePiece sp huniq hi₀).mpr hC)
  · intro h C hC
    exact h C ((isOddCycle_iff_of_oneNonBipartitePiece sp huniq hi₀).mp hC)

/-- **Erdős's hypothesis descends to the single non-bipartite piece.** -/
theorem locIndep_of_oneNonBipartitePiece {k : ℕ} {i₀ : Fin t} (sp : OneSplit G v t)
    (huniq : ∀ i : Fin t, ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite → i = i₀)
    (hi₀ : ¬ (induceFinset G (insert v (sp.parts i₀))).IsBipartite) (hG : LocIndep k G) :
    LocIndep k (induceFinset G (insert v (sp.parts i₀))) :=
  hG.of_induceFinset _

/-- **THE REDUCTION ITERATES: two successive one-sided cuts.**  `G` has a one-sided 1-cut at `v`
leaving the single non-bipartite piece `T_{i₀} ∪ {v}`; that piece has a one-sided 1-cut at `v'`
leaving its single non-bipartite piece `T'_{j₀} ∪ {v'}`.  Then

> `CloseToBipartite m G ↔ CloseToBipartite m (G'')`,

where `G''` is the induced subgraph of `G` on the second piece.  This is the classical block-cut
reduction, in the two-step form: a *chain* of one-sided cuts is peeled off at no cost, and the
argument is by composition of the one-step equivalence, so it extends to any finite chain. -/
theorem closeToBipartite_iff_of_twoSideCuts {m : ℕ} {v v' : V} {t t' : ℕ} {i₀ : Fin t}
    {j₀ : Fin t'} [Fintype V] (sp : OneSplit G v t) (sp' : OneSplit (induceFinset G
      (insert v (sp.parts i₀))) v' t')
    (huniq : ∀ i : Fin t, ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite → i = i₀)
    (hi₀ : ¬ (induceFinset G (insert v (sp.parts i₀))).IsBipartite)
    (huniq' : ∀ j : Fin t', ¬ (induceFinset (induceFinset G (insert v (sp.parts i₀)))
      (insert v' (sp'.parts j))).IsBipartite → j = j₀)
    (hj₀ : ¬ (induceFinset (induceFinset G (insert v (sp.parts i₀)))
      (insert v' (sp'.parts j₀))).IsBipartite) :
    CloseToBipartite m G ↔ CloseToBipartite m
      (induceFinset (induceFinset G (insert v (sp.parts i₀))) (insert v' (sp'.parts j₀))) :=
  (closeToBipartite_iff_of_oneNonBipartitePiece sp huniq hi₀).trans
    (closeToBipartite_iff_of_oneNonBipartitePiece sp' huniq' hj₀)

/-- **The one-sided reduction, in the `LocIndep` form used by the induction.**

`G` has a 1-cut at `v` whose only non-bipartite piece is `T_{i₀} ∪ {v}`; Erdős's hypothesis
forces the conclusion on that piece; then it forces the conclusion on `G`, **at the same constant
`m`**.  This is the one-step form of the classical induction along a one-sided chain: the
hypothesis is checked on a strictly smaller graph and the constant does not grow. -/
theorem closeToBipartite_of_oneSideCut {k m : ℕ} {v : V} {t : ℕ} {i₀ : Fin t} [Fintype V]
    (sp : OneSplit G v t)
    (huniq : ∀ i : Fin t, ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite → i = i₀)
    (hi₀ : ¬ (induceFinset G (insert v (sp.parts i₀))).IsBipartite)
    (hpiece : LocIndep k (induceFinset G (insert v (sp.parts i₀))) →
      CloseToBipartite m (induceFinset G (insert v (sp.parts i₀))))
    (hG : LocIndep k G) : CloseToBipartite m G :=
  (closeToBipartite_iff_of_oneNonBipartitePiece sp huniq hi₀).mpr
    (hpiece (locIndep_of_oneNonBipartitePiece sp huniq hi₀ hG))

/-- **THE ONE-SIDED 1-CUT IS FREE, IN THE PACKING LANGUAGE**: a packing bound `r` on `G` restricts to
the single non-bipartite piece, and a transversal of that piece is a transversal of `G` at the
same size. -/
theorem hitsOddCycles_of_oneSideCut {v : V} {t : ℕ} {i₀ : Fin t} [Fintype V] (sp : OneSplit G v t)
    (huniq : ∀ i : Fin t, ¬ (induceFinset G (insert v (sp.parts i))).IsBipartite → i = i₀)
    (hi₀ : ¬ (induceFinset G (insert v (sp.parts i₀))).IsBipartite)
    (hX : HitsOddCycles (induceFinset G (insert v (sp.parts i₀))) X) : HitsOddCycles G X :=
  (hitsOddCycles_iff_of_oneNonBipartitePiece sp huniq hi₀).mpr hX

end OneSided

/-! ### Part 7 — THE OBSTRUCTION, MACHINE-CHECKED: the number of non-bipartite PIECES is not
controlled by `k` -/

section Windmill

/-- Adjacency of `wf` is decidable (the instance of `JSPProblem/Windmill.lean` is local to that
file and does not leave it). -/
local instance instDecidableRelWf : DecidableRel wf.Adj :=
  fun v w => inferInstanceAs (Decidable (wfAdj v w))

/-- **The 1-cut of the windmill at its central vertex `0`**: the two triangles minus their common
vertex, and the isolated vertex `5`. -/
def wfPiece : Fin 3 → Finset (Fin 6) := fun i =>
  if i.val = 0 then ({1, 2} : Finset (Fin 6))
  else if i.val = 1 then ({3, 4} : Finset (Fin 6)) else ({5} : Finset (Fin 6))

theorem wfPiece_0 : wfPiece 0 = ({1, 2} : Finset (Fin 6)) := by decide

theorem wfPiece_1 : wfPiece 1 = ({3, 4} : Finset (Fin 6)) := by decide

theorem wfPiece_2 : wfPiece 2 = ({5} : Finset (Fin 6)) := by decide

/-- **THE WINDMILL HAS A 1-CUT AT `0`.**  `wf` is the bowtie of `JSPProblem/Windmill.lean`: two
triangles `0 1 2` and `0 3 4`, plus the isolated vertex `5`.  This is the first 1-cut of `wf`; the
2-cut `{0, 5}` used by that file is a *different* cut. -/
def wf_oneSplit : OneSplit wf 0 3 where
  parts := wfPiece
  ht := by decide
  hne := by decide
  hdisj := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [wfPiece] at hij ⊢
    all_goals
      apply Finset.ext
      intro z
      fin_cases z <;> simp
  hcov := by decide
  hanti := by
    intro i j hij x hx y hy
    fin_cases i <;> fin_cases j <;> simp [wfPiece] at hij hx hy <;>
      simp [wf_adj, wfAdj] <;> omega

/-- **The first triangle of the windmill is an odd cycle.** -/
theorem isOddCycle_wf_tri012 : IsOddCycle wf ({0, 1, 2} : Finset (Fin 6)) :=
  ⟨3, tri012, rfl, by decide, tri012_inj, tri012_cyc, by decide⟩

/-- **The second triangle of the windmill is an odd cycle.** -/
theorem isOddCycle_wf_tri034 : IsOddCycle wf ({0, 3, 4} : Finset (Fin 6)) :=
  ⟨3, tri034, rfl, by decide, tri034_inj, tri034_cyc, by decide⟩

/-- **THE FIRST PIECE `T_0 ∪ {0} = {0, 1, 2}` IS NOT BIPARTITE.** -/
theorem not_isBipartite_wf_piece_0 :
    ¬ (induceFinset wf (insert 0 (wfPiece 0))).IsBipartite := by
  have hsub : ({0, 1, 2} : Finset (Fin 6)) ⊆ insert 0 (wfPiece 0) := by decide
  intro hb
  exact (not_isOddCycle_of_isBipartite hb) ⟨_, isOddCycle_wf_tri012.induceFinset hsub⟩

/-- **THE SECOND PIECE `T_1 ∪ {0} = {0, 3, 4}` IS NOT BIPARTITE.** -/
theorem not_isBipartite_wf_piece_1 :
    ¬ (induceFinset wf (insert 0 (wfPiece 1))).IsBipartite := by
  have hsub : ({0, 3, 4} : Finset (Fin 6)) ⊆ insert 0 (wfPiece 1) := by decide
  intro hb
  exact (not_isOddCycle_of_isBipartite hb) ⟨_, isOddCycle_wf_tri034.induceFinset hsub⟩

/-- **AT LEAST TWO PIECES OF THE WINDMILL ARE NON-BIPARTITE**, witnessed by the two triangles. -/
theorem two_nonBipartitePieces_wf :
    ∃ i j : Fin 3, i ≠ j ∧ ¬ (induceFinset wf (insert 0 (wf_oneSplit.parts i))).IsBipartite ∧
      ¬ (induceFinset wf (insert 0 (wf_oneSplit.parts j))).IsBipartite :=
  ⟨0, 1, by decide, not_isBipartite_wf_piece_0, not_isBipartite_wf_piece_1⟩

/-- **THE OBSTRUCTION, MACHINE-CHECKED: Erdős's hypothesis does not control the number of
non-bipartite PIECES.**

`LocIndep 1 wf` holds (`JSPProblem/Windmill.lean` `locIndep_one_wf`), yet the 1-cut of `wf` at `0`
has **two** non-bipartite pieces — more than `k = 1`.  So the hypothesis
`|nonBipartitePieces| ≤ k` of the natural Erdős #73 instance along the piece axis is **false**.
This is precisely why Parts 3–6 buy the removal of the `+1` and the exact one-sided `iff`, but no
constant `f(k)`: the *parts* are controlled by the packing number
(`JSPProblem/Connect.lean` `OneSplit.card_nonBipartiteParts_le`), the *pieces* are not — the single
cut vertex alone can turn arbitrarily many bipartite parts into non-bipartite pieces.  (The windmill
is the smallest witness; the general witness is the windmill with `k` triangles.) -/
theorem wf_locIndep_one_two_nonBipartitePieces :
    LocIndep 1 wf ∧
      ∃ i j : Fin 3, i ≠ j ∧ ¬ (induceFinset wf (insert 0 (wfPiece i))).IsBipartite ∧
        ¬ (induceFinset wf (insert 0 (wfPiece j))).IsBipartite :=
  ⟨locIndep_one_wf, two_nonBipartitePieces_wf⟩

end Windmill

end

end JSP90
