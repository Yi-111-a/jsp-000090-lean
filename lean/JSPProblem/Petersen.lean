/-
# JSP-000090 — the deficiency-one axis: the Petersen graph with one vertex deleted

This file is the **twenty-fourth attack family** of the formalization, and the first one that
improves the *quantitative* answer to Erdős Problem #73 rather than reformulating it.

`JSPProblem/Sharp.lean` proved the lower bound `f(k) ≥ k` of Erdős #73, witnessed by `kTriangles k`
(`k` vertex-disjoint triangles): that graph satisfies Erdős's local hypothesis `LocIndep k` and its
least odd cycle transversal has exactly `k` elements.  The constant `k` cannot be beaten.

Here is a **better witness**.  Let `p9` be the Petersen graph with one vertex deleted: nine
vertices, twelve edges, triangle-free, with

* every induced subgraph carrying an independent set of size `≥ (|X| - 1) / 2`, i.e.
  `LocIndep 1 p9` — so its deficiency is **exactly one**;
* no single vertex meeting every odd cycle, while two vertices do (`¬ CloseToBipartite 1 p9` and
  `CloseToBipartite 2 p9`).

Taking the disjoint union of `k` copies of `p9` and using the additivity of the conclusion over an
anticomplete decomposition (`JSPProblem/Optimal.lean`, `JSPProblem/Additive.lean`) gives the
improved lower bound

> **`f(k) ≥ 2 k`** — no constant below `2 k` can work in the statement of Erdős #73

(`JSP90.erdos73_lower_bound_two`, `JSP90.no_constant_below_two_k`), together with the **exact** value
of the conclusion on that class of graphs,
`JSP90.closeToBipartite_p9Family_iff : CloseToBipartite m (p9Family k) ↔ 2 * k ≤ m`.

The witness is also **triangle-free** (`JSP90.triangleFree_p9`), so the improved lower bound already
holds inside the triangle-free class, the class in which the fan / boundary machinery of
`JSPProblem/Free.lean`, `JSPProblem/Class.lean`, `JSPProblem/Book.lean` and `JSPProblem/Touch.lean`
lives.  By `JSPProblem/Packing.lean` (`LocIndep.oddCyclePacking_le` at `k = 1`) `p9` has no two
vertex-disjoint odd cycles, and the case `k = 1` of Erdős #73 is exactly the packing-number-one
case of Erdős–Pósa for odd cycles; the matching **upper** bound
`LocIndep 1 G → CloseToBipartite 2 G` is *not* proved here (it is a case of the missing
`JSP90.OddCycleErdosPosa`; see `discovery/JSP-000090/policy.json`).

Nothing here is assumed: the deficiency of `p9` is verified by an exhaustive kernel decision over all
`2 ^ 9` vertex sets (`JSP90.locIndep_one_p9`, proved by `of_decide_eq_true` and therefore
independently of the compiler), and the transversal statements are proved from explicit 5-cycles.
-/

import JSPProblem.Definitions
import JSPProblem.Transversal
import JSPProblem.Optimal
import JSPProblem.Additive
import Mathlib.Data.Finset.SDiff
import Mathlib.Tactic.FinCases

namespace JSP90

noncomputable section

open Finset Fintype Set

/-- **One `DecidableEq (Fin 9)` for the whole file.**  Several earlier files of this development
install their own `DecidableEq (Fin n)` instance, and `Finset.inter` and friends are built from it,
so mixing two of them yields two syntactically different finsets of the same vertex set.  This
instance is *computable*, so that the finite checks of the file are kernel computations. -/
local instance instDecidableEqFinPetersen (n : ℕ) : DecidableEq (Fin n) := instDecidableEqFin n

/-! ### The witness graph `p9`: the Petersen graph with one outer vertex deleted

The Petersen graph is drawn as an outer 5-cycle `a₀ a₁ a₂ a₃ a₄`, an inner 5-pointed star
`b₀ b₁ b₂ b₃ b₄` and the five spokes `aᵢ bᵢ`.  Deleting `a₀` leaves nine vertices, which we number

```
a₁ = 0   a₂ = 1   a₃ = 2   a₄ = 3        (the outer cycle, now the path 0 – 1 – 2 – 3)
b₀ = 4   b₁ = 5   b₂ = 6   b₃ = 7   b₄ = 8
```

so the edges are the three outer ones `0 – 1 – 2 – 3`, the four spokes `0 – 5`, `1 – 6`, `2 – 7`,
`3 – 8`, and the five edges of the inner star `4 – 6 – 8 – 5 – 7 – 4`.  Twelve edges in total. -/

/-- The **edge set of `p9`**, as a finset of ordered pairs. -/
def p9Edge : Finset (Fin 9 × Fin 9) :=
  {(0, 1), (1, 0), (0, 5), (5, 0), (1, 2), (2, 1), (1, 6), (6, 1), (2, 3), (3, 2), (2, 7), (7, 2),
    (3, 8), (8, 3), (4, 6), (6, 4), (5, 7), (7, 5), (6, 8), (8, 6), (7, 4), (4, 7), (8, 5), (5, 8)}

theorem p9Edge_symm : ∀ v w : Fin 9, (v, w) ∈ p9Edge ↔ (w, v) ∈ p9Edge := by decide

theorem p9Edge_irrefl : ∀ v : Fin 9, (v, v) ∉ p9Edge := by decide

/-- **`p9`, the Petersen graph with one vertex deleted**: adjacency is membership in `p9Edge`. -/
def p9 : SimpleGraph (Fin 9) where
  Adj v w := (v, w) ∈ p9Edge
  symm := ⟨fun _ _ h => (p9Edge_symm _ _).mp h⟩
  loopless := ⟨fun _ h => p9Edge_irrefl _ h⟩

@[simp] theorem p9_adj {v w : Fin 9} : p9.Adj v w ↔ (v, w) ∈ p9Edge := Iff.rfl

/-- Adjacency of `p9` is decidable: this is what makes the finite checks below kernel computations. -/
local instance : DecidableRel p9.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ p9Edge))

/-! ### The deficiency of `p9` is exactly one

`LocIndep 1 p9` is the statement that **every** vertex set of `p9` carries an independent set of
size `≥ (|X| - 1) / 2`.  It is a finite statement — there are `2 ^ 9 = 512` vertex sets and `3 ^ 9`
candidate pairs `(X, S)` — and it is proved by exhaustive decision, which the kernel performs.

By `JSP90.locIndep_iff_maxDef_le` this says the maximum deficiency of `p9` is at most one, and
`JSP90.LocIndep.oddCycle_packing_le` at `k = 1` says that `p9` has no two vertex-disjoint odd cycles:
`p9` is a *packing-number-one* graph. -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
/-- **`LocIndep 1 p9`**, i.e. the maximum deficiency of `p9` is at most one — the reason `p9` is
admissible as a witness for Erdős #73 with the parameter `k = 1`.  The proof is the exhaustive
decision over the `512` vertex sets of `p9`. -/
theorem locIndep_one_p9 : LocIndep 1 p9 := by
  unfold LocIndep
  decide

set_option maxRecDepth 1000000 in
/-- `p9` satisfies no stronger local hypothesis: its deficiency is **exactly** one (it carries an
odd cycle, so `LocIndep 0 p9` fails). -/
theorem not_locIndep_zero_p9 : ¬ LocIndep 0 p9 := by
  unfold LocIndep
  decide

/-- **`p9` is triangle-free**: the improved lower bound of this file already holds in the class of
triangle-free graphs, the class on which `JSPProblem/Free.lean` and `JSPProblem/Touch.lean` work. -/
theorem triangleFree_p9 : ∀ v w : Fin 9, p9.Adj v w → ¬ ∃ u : Fin 9, p9.Adj v u ∧ p9.Adj u w := by
  decide

/-! ### Four odd cycles of `p9`, and the fact that no single vertex meets all of them -/

/-- A cyclic ordering of five vertices of `p9`. -/
def cyc5 (a b c d e : Fin 9) : Fin 5 → Fin 9 := fun j =>
  match j.val with
  | 0 => a | 1 => b | 2 => c | 3 => d | _ => e

/-- The 5-cycle `1 – 2 – 3 – 8 – 6 – 1`. -/
def Ca : Finset (Fin 9) := {1, 2, 3, 8, 6}

/-- The 5-cycle `2 – 3 – 8 – 5 – 7 – 2`. -/
def Cb : Finset (Fin 9) := {2, 3, 8, 5, 7}

/-- The 5-cycle `0 – 1 – 6 – 8 – 5 – 0`. -/
def Cc : Finset (Fin 9) := {0, 1, 6, 8, 5}

/-- The 5-cycle `0 – 1 – 2 – 7 – 5 – 0`. -/
def Cd : Finset (Fin 9) := {0, 1, 2, 7, 5}

theorem mem_Ca : ∀ x : Fin 9, x ∈ Ca ↔ ∃ j : Fin 5, cyc5 1 2 3 8 6 j = x := by
  decide

theorem mem_Cb : ∀ x : Fin 9, x ∈ Cb ↔ ∃ j : Fin 5, cyc5 2 3 8 5 7 j = x := by
  decide

theorem mem_Cc : ∀ x : Fin 9, x ∈ Cc ↔ ∃ j : Fin 5, cyc5 0 1 6 8 5 j = x := by
  decide

theorem mem_Cd : ∀ x : Fin 9, x ∈ Cd ↔ ∃ j : Fin 5, cyc5 0 1 2 7 5 j = x := by
  decide

theorem isOddCycle_Ca : IsOddCycle p9 Ca :=
  ⟨5, cyc5 1 2 3 8 6, by decide, by decide, by decide, by decide, mem_Ca⟩

theorem isOddCycle_Cb : IsOddCycle p9 Cb :=
  ⟨5, cyc5 2 3 8 5 7, by decide, by decide, by decide, by decide, mem_Cb⟩

theorem isOddCycle_Cc : IsOddCycle p9 Cc :=
  ⟨5, cyc5 0 1 6 8 5, by decide, by decide, by decide, by decide, mem_Cc⟩

theorem isOddCycle_Cd : IsOddCycle p9 Cd :=
  ⟨5, cyc5 0 1 2 7 5, by decide, by decide, by decide, by decide, mem_Cd⟩

/-- **Every vertex of `p9` is avoided by one of the four 5-cycles above.**  Consequently no single
vertex meets every odd cycle of `p9`. -/
theorem exists_oddCycle_av (v : Fin 9) : ∃ C : Finset (Fin 9), IsOddCycle p9 C ∧ v ∉ C := by
  fin_cases v <;>
    first
      | exact ⟨Ca, isOddCycle_Ca, by decide⟩
      | exact ⟨Cb, isOddCycle_Cb, by decide⟩
      | exact ⟨Cc, isOddCycle_Cc, by decide⟩
      | exact ⟨Cd, isOddCycle_Cd, by decide⟩

/-- **A 5-cycle of `p9` that avoids `v` survives in the residue `p9 - v`.** -/
theorem isOddCycle_delete_cyc5 (a b c d e v : Fin 9)
    (hv : ∀ j : Fin 5, cyc5 a b c d e j ≠ v)
    (hne : Function.Injective (cyc5 a b c d e))
    (hadj : ∀ j : Fin 5, p9.Adj ((cyc5 a b c d e) j) ((cyc5 a b c d e) (cycSucc j))) :
    IsOddCycle (deleteFinset p9 {v}) ({a, b, c, d, e} : Finset (Fin 9)) := by
  refine ⟨5, cyc5 a b c d e, by decide, by decide, hne, ?_, ?_⟩
  · intro j
    rw [deleteFinset_adj]
    exact ⟨by rw [Finset.mem_singleton]; exact hv j,
      by rw [Finset.mem_singleton]; exact hv (cycSucc j), hadj j⟩
  · intro x
    constructor
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨0, by omega⟩, by simp [cyc5]⟩
      · exact ⟨⟨1, by omega⟩, by simp [cyc5]⟩
      · exact ⟨⟨2, by omega⟩, by simp [cyc5]⟩
      · exact ⟨⟨3, by omega⟩, by simp [cyc5]⟩
      · exact ⟨⟨4, by omega⟩, by simp [cyc5]⟩
    · rintro ⟨j, hj⟩
      fin_cases j <;> simp only [cyc5] at hj <;> subst hj <;> simp

/-- **The residue of `p9` at any single vertex still carries an odd cycle** — the witness behind
`JSP90.not_closeToBipartite_one_p9`.  The four 5-cycles above are read off the table of
`JSP90.exists_oddCycle_av`: for each vertex one of them avoids it. -/
theorem exists_oddCycle_delete_av (v : Fin 9) :
    ∃ C : Finset (Fin 9), IsOddCycle (deleteFinset p9 {v}) C := by
  fin_cases v
  · exact ⟨{2, 3, 8, 5, 7}, isOddCycle_delete_cyc5 2 3 8 5 7 0 (by intro j; fin_cases j <;> decide) (by decide) (by decide)⟩
  · exact ⟨{2, 3, 8, 5, 7}, isOddCycle_delete_cyc5 2 3 8 5 7 1 (by intro j; fin_cases j <;> decide) (by decide) (by decide)⟩
  · exact ⟨{0, 1, 6, 8, 5}, isOddCycle_delete_cyc5 0 1 6 8 5 2 (by intro j; fin_cases j <;> decide) (by decide) (by decide)⟩
  · exact ⟨{0, 1, 2, 7, 5}, isOddCycle_delete_cyc5 0 1 2 7 5 3 (by intro j; fin_cases j <;> decide) (by decide) (by decide)⟩
  · exact ⟨{1, 2, 3, 8, 6}, isOddCycle_delete_cyc5 1 2 3 8 6 4 (by intro j; fin_cases j <;> decide) (by decide) (by decide)⟩
  · exact ⟨{1, 2, 3, 8, 6}, isOddCycle_delete_cyc5 1 2 3 8 6 5 (by intro j; fin_cases j <;> decide) (by decide) (by decide)⟩
  · exact ⟨{0, 1, 2, 7, 5}, isOddCycle_delete_cyc5 0 1 2 7 5 6 (by intro j; fin_cases j <;> decide) (by decide) (by decide)⟩
  · exact ⟨{0, 1, 6, 8, 5}, isOddCycle_delete_cyc5 0 1 6 8 5 7 (by intro j; fin_cases j <;> decide) (by decide) (by decide)⟩
  · exact ⟨{0, 1, 2, 7, 5}, isOddCycle_delete_cyc5 0 1 2 7 5 8 (by intro j; fin_cases j <;> decide) (by decide) (by decide)⟩


/-- **The same table, with the data of the cycle**: for every vertex of `p9` a 5-cycle of `p9`
avoiding it, given as five vertices. -/
theorem exists_oddCycle_data_av (v : Fin 9) :
    ∃ a b c d e : Fin 9, Function.Injective (cyc5 a b c d e) ∧
      (∀ j : Fin 5, p9.Adj ((cyc5 a b c d e) j) ((cyc5 a b c d e) (cycSucc j))) ∧
      v ∉ ({a, b, c, d, e} : Finset (Fin 9)) := by
  fin_cases v <;>
    first
      | exact ⟨2, 3, 8, 5, 7, by decide, by decide, by decide⟩
      | exact ⟨0, 1, 6, 8, 5, by decide, by decide, by decide⟩
      | exact ⟨0, 1, 2, 7, 5, by decide, by decide, by decide⟩
      | exact ⟨1, 2, 3, 8, 6, by decide, by decide, by decide⟩

/-- **`¬ CloseToBipartite 1 p9`**: no single vertex meets every odd cycle of `p9`, so `p9` is not one
vertex away from bipartite.  Together with `JSP90.closeToBipartite_two_p9` this says the least odd
cycle transversal of `p9` is **exactly** two. -/
theorem not_closeToBipartite_one_p9 : ¬ CloseToBipartite 1 p9 := by
  rintro ⟨X, hX, hb⟩
  have hsub : ∀ a ∈ X, ∀ b ∈ X, a = b := Finset.card_le_one.mp hX
  rcases X.eq_empty_or_nonempty with rfl | ⟨v, hvX⟩
  · rw [deleteFinset_empty] at hb
    exact not_isOddCycle_of_isBipartite hb ⟨Ca, isOddCycle_Ca⟩
  · have hX1 : X = {v} := by
      ext y
      constructor
      · intro hy
        exact Finset.mem_singleton.mpr (hsub y hy v hvX)
      · intro hy
        rw [Finset.mem_singleton] at hy
        rw [hy]
        exact hvX
    subst hX1
    obtain ⟨C, hC⟩ := exists_oddCycle_delete_av v
    exact not_isOddCycle_of_isBipartite hb ⟨C, hC⟩

/-- The 2-colouring of `p9` minus `{2, 6}`: part `0 = {0, 7, 8}` and part `1 = {1, 3, 4, 5}`. -/
def p9col : Fin 9 → Fin 2 := fun v => if v ∈ ({0, 7, 8} : Finset (Fin 9)) then 0 else 1

theorem p9col_valid : ∀ v w : Fin 9, p9.Adj v w → v ∉ ({2, 6} : Finset (Fin 9)) →
    w ∉ ({2, 6} : Finset (Fin 9)) → p9col v ≠ p9col w := by
  decide

/-- **`CloseToBipartite 2 p9`**: two vertices meet every odd cycle of `p9`, so its least odd cycle
transversal has **exactly** two elements. -/
theorem closeToBipartite_two_p9 : CloseToBipartite 2 p9 := by
  refine ⟨({2, 6} : Finset (Fin 9)), by decide, ?_⟩
  refine ⟨SimpleGraph.Coloring.mk p9col fun hadj => ?_⟩
  simp only [deleteFinset_adj] at hadj
  exact p9col_valid _ _ hadj.2.2 hadj.1 hadj.2.1


set_option maxHeartbeats 1000000

/-! ### The disjoint union of `k` copies of `p9`

`p9Family k` is the anticomplete union of the `k` fibres `Fin 9 × {i}`, each of which carries a copy
of `p9`.  Erdős's local hypothesis is satisfied with the parameter `k` (round 44's
`erdos73On_of_anticover_decomposition` made the same point for the conclusion), and the least odd
cycle transversal of `p9Family k` is **exactly** `2 * k`. -/

/-- **The disjoint union of `k` copies of `p9`**: `(a, i)` and `(b, j)` are adjacent exactly when
`i = j` and `a`, `b` are adjacent in `p9`. -/
def p9Family (k : ℕ) : SimpleGraph (Fin 9 × Fin k) where
  Adj p q := p.2 = q.2 ∧ p9.Adj p.1 q.1
  symm := ⟨fun _ _ ⟨h2, h1⟩ => ⟨h2.symm, h1.symm⟩⟩
  loopless := ⟨fun _ ⟨_, h1⟩ => p9Edge_irrefl _ h1⟩

@[simp] theorem p9Family_adj {k : ℕ} {p q : Fin 9 × Fin k} :
    (p9Family k).Adj p q ↔ p.2 = q.2 ∧ p9.Adj p.1 q.1 := Iff.rfl

/-- **The `i`-th fibre** of `p9Family k`, a copy of `p9`. -/
def p9Fibre {k : ℕ} (i : Fin k) : Finset (Fin 9 × Fin k) :=
  (Finset.univ : Finset (Fin 9)).image fun a => (a, i)

theorem mem_p9Fibre {k : ℕ} {i : Fin k} {p : Fin 9 × Fin k} : p ∈ p9Fibre i ↔ p.2 = i := by
  constructor
  · intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact (congrArg Prod.snd ha).symm
  · intro h
    exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, Prod.ext rfl h.symm⟩

theorem card_p9Fibre {k : ℕ} (i : Fin k) : (p9Fibre i).card = 9 := by
  have hinj : Function.Injective (fun a : Fin 9 => (a, i)) := fun a b h => congrArg Prod.fst h
  rw [p9Fibre, Finset.card_image_of_injective _ hinj]
  simp

theorem p9Fibre_disjoint {k : ℕ} {i j : Fin k} (h : i ≠ j) : Disjoint (p9Fibre i) (p9Fibre j) := by
  refine Finset.disjoint_left.mpr fun p hp hq => ?_
  exact h ((mem_p9Fibre.mp hp).symm.trans (mem_p9Fibre.mp hq))

/-- **The fibres of `p9Family k` are pairwise disjoint.** -/
theorem pairwiseDisjoint_fibre_pieces {k : ℕ} :
    ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint fun i => p9Fibre i := by
  intro x hx y hy hxy
  refine Finset.disjoint_left.mpr ?_
  intro p hp1 hp2
  exact hxy (((mem_p9Fibre (i := x) (p := p)).mp hp1).symm.trans
    ((mem_p9Fibre (i := y) (p := p)).mp hp2))

/-- **A vertex set of `p9Family k` is the disjoint union of its parts in the fibres.** -/
theorem inter_biUnion_fibre {k : ℕ} (X : Finset (Fin 9 × Fin k)) :
    X = (Finset.univ : Finset (Fin k)).biUnion fun i => X ∩ p9Fibre i := by
  ext p
  constructor
  · intro hx
    exact Finset.mem_biUnion.mpr
      ⟨p.2, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hx, mem_p9Fibre.mpr rfl⟩⟩
  · intro hx
    obtain ⟨i, -, hx'⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hx').1

/-! #### The local hypothesis on the disjoint union -/

/-- **`LocIndep k (p9Family k)`**: every vertex set of the disjoint union of `k` copies of `p9`
carries an independent set of size at least `(|X| - k) / 2`.  The proof is fibre-wise: inside the
`i`-th fibre use `JSP90.locIndep_one_p9`; the `k` fibres are pairwise disjoint, so the `k` independent
sets glue to a single one and their counting inequalities add up. -/
theorem locIndep_p9Family (k : ℕ) : LocIndep k (p9Family k) := by
  intro X
  have hstep : ∀ i : Fin k, ∃ A : Finset (Fin 9), (A ×ˢ ({i} : Finset (Fin k))) ⊆ X ∧
      (p9Family k).IsIndepSet (A ×ˢ ({i} : Finset (Fin k))) ∧
      2 * A.card + 1 ≥ (X ∩ p9Fibre i).card := by
    intro i
    have hYmem : ∀ a : Fin 9, a ∈ (X ∩ p9Fibre i).image Prod.fst ↔ (a, i) ∈ X := by
      intro a
      constructor
      · rw [Finset.mem_image]
        rintro ⟨z, hz, hza⟩
        rw [Finset.mem_inter] at hz
        have heq : (a, i) = (z.1, z.2) := Prod.ext hza.symm (mem_p9Fibre.mp hz.2).symm
        rw [heq]
        exact hz.1
      · intro hax
        rw [Finset.mem_image]
        exact ⟨(a, i), Finset.mem_inter.mpr ⟨hax, mem_p9Fibre.mpr rfl⟩, rfl⟩
    have hYcard : ((X ∩ p9Fibre i).image Prod.fst).card = (X ∩ p9Fibre i).card := by
      refine Finset.card_image_iff.mpr ?_
      intro a ha b hb hab
      obtain ⟨-, ha2⟩ := Finset.mem_inter.mp ha
      obtain ⟨-, hb2⟩ := Finset.mem_inter.mp hb
      have ha2' : a.2 = i := mem_p9Fibre.mp ha2
      have hb2' : b.2 = i := mem_p9Fibre.mp hb2
      exact Prod.ext_iff.mpr ⟨hab, ha2'.trans hb2'.symm⟩
    obtain ⟨A, hA, hAi, hAcard⟩ := locIndep_one_p9 ((X ∩ p9Fibre i).image Prod.fst)
    refine ⟨A, ?_, ?_, ?_⟩
    · intro p hp
      have hp' := Finset.mem_product.mp hp
      have hp2 : p.2 = i := Finset.mem_singleton.mp hp'.2
      have hp3 : p = (p.1, i) := Prod.ext rfl hp2
      rw [hp3]
      exact (hYmem p.1).mp (hA hp'.1)
    · intro a ha b hb hab hadj
      have ha' : a.1 ∈ A ∧ a.2 = i := by
        simpa only [Set.mem_prod, Finset.mem_coe, Finset.mem_singleton] using ha
      have hb' : b.1 ∈ A ∧ b.2 = i := by
        simpa only [Set.mem_prod, Finset.mem_coe, Finset.mem_singleton] using hb
      rw [p9Family_adj] at hadj
      have hab' : a.1 ≠ b.1 := fun h => hab (Prod.ext h hadj.1)
      exact hAi ha'.1 hb'.1 hab' hadj.2
    · rw [← hYcard]
      exact hAcard
  refine ⟨(Finset.univ : Finset (Fin k)).biUnion
      (fun i => (hstep i).choose ×ˢ ({i} : Finset (Fin k))), ?_, ?_, ?_⟩
  · refine (Finset.biUnion_subset (s := (Finset.univ : Finset (Fin k)))).2 fun i _ => ?_
    exact (hstep i).choose_spec.1
  · intro a ha b hb hab hadj
    obtain ⟨i, _, hia⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨j, _, hjb⟩ := Finset.mem_biUnion.mp hb
    have hidx' : a.1 ∈ (hstep i).choose ∧ a.2 = i := by
      simpa only [Finset.mem_product, Set.mem_prod, Finset.mem_coe, Finset.mem_singleton] using hia
    have hia' : a ∈ ((hstep i).choose ×ˢ ({i} : Finset (Fin k)) : Set (Fin 9 × Fin k)) :=
      Set.mem_prod.mpr
        ⟨Finset.mem_coe.mpr hidx'.1, Finset.mem_coe.mpr (Finset.mem_singleton.mpr hidx'.2)⟩
    have hidx : a.2 = i := by
      have hia' : a.1 ∈ (hstep i).choose ∧ a.2 = i := by
        simpa only [Finset.mem_product, Set.mem_prod, Finset.mem_coe, Finset.mem_singleton] using hia
      exact hia'.2
    have hjdx : b.2 = j := by
      have hjb' : b.1 ∈ (hstep j).choose ∧ b.2 = j := by
        simpa only [Finset.mem_product, Set.mem_prod, Finset.mem_coe, Finset.mem_singleton] using hjb
      exact hjb'.2
    rw [p9Family_adj] at hadj
    have hij : i = j := (hadj.1 ▸ hidx).symm.trans hjdx
    have hjdx' : b.1 ∈ (hstep j).choose ∧ b.2 = j := by
      simpa only [Finset.mem_product, Set.mem_prod, Finset.mem_coe, Finset.mem_singleton] using hjb
    have hjb' : b ∈ ((hstep j).choose ×ˢ ({j} : Finset (Fin k)) : Set (Fin 9 × Fin k)) :=
      Set.mem_prod.mpr
        ⟨Finset.mem_coe.mpr hjdx'.1, Finset.mem_coe.mpr (Finset.mem_singleton.mpr hjdx'.2)⟩
    subst hij
    exact (hstep i).choose_spec.2.1 hia' hjb' hab
      (p9Family_adj.mpr ⟨hidx.trans hjdx.symm, hadj.2⟩)
  · have hdisj : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        (fun i => (hstep i).choose ×ˢ ({i} : Finset (Fin k))) := by
      intro x hx y hy hxy
      refine Finset.disjoint_left.mpr fun z hz1 hz2 => ?_
      have h1' := Finset.mem_product.mp hz1
      have h2' := Finset.mem_product.mp hz2
      exact hxy ((Finset.mem_singleton.mp h1'.2).symm.trans (Finset.mem_singleton.mp h2'.2))
    have hcards : ∀ i, ((hstep i).choose ×ˢ ({i} : Finset (Fin k))).card
        = (hstep i).choose.card := by
      intro i
      rw [Finset.card_product]
      simp
    have hsum : ∑ i ∈ (Finset.univ : Finset (Fin k)),
          (2 * ((hstep i).choose ×ˢ ({i} : Finset (Fin k))).card + 1)
        = 2 * ((Finset.univ : Finset (Fin k)).biUnion
          (fun i => (hstep i).choose ×ˢ ({i} : Finset (Fin k)))).card + k := by
      calc (∑ i ∈ (Finset.univ : Finset (Fin k)),
            (2 * ((hstep i).choose ×ˢ ({i} : Finset (Fin k))).card + 1) : ℕ)
          = ∑ i ∈ (Finset.univ : Finset (Fin k)), ((hstep i).choose.card * 2 + 1) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [hcards i, Nat.mul_comm]
      _ = (∑ i ∈ (Finset.univ : Finset (Fin k)), (hstep i).choose.card) * 2
          + ∑ i ∈ (Finset.univ : Finset (Fin k)), 1 := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = 2 * ((Finset.univ : Finset (Fin k)).biUnion
          (fun i => (hstep i).choose ×ˢ ({i} : Finset (Fin k)))).card + k := by
        rw [Finset.card_biUnion hdisj]
        simp [Nat.mul_comm]
    have hle : (∑ i ∈ (Finset.univ : Finset (Fin k)), (X ∩ p9Fibre i).card)
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)),
          (2 * ((hstep i).choose ×ˢ ({i} : Finset (Fin k))).card + 1) :=
      Finset.sum_le_sum fun i _ => by
        rw [hcards i]
        exact (hstep i).choose_spec.2.2
    have hdecomp : X = (Finset.univ : Finset (Fin k)).biUnion fun i => X ∩ p9Fibre i := by
      ext p
      constructor
      · intro hx
        exact Finset.mem_biUnion.mpr
          ⟨p.2, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hx, mem_p9Fibre.mpr rfl⟩⟩
      · intro hx
        obtain ⟨i, -, hx'⟩ := Finset.mem_biUnion.mp hx
        exact (Finset.mem_inter.mp hx').1
    have hdisjX : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
        fun i => X ∩ p9Fibre i := by
      intro x hx y hy hxy
      refine Finset.disjoint_left.mpr ?_
      intro p hp1 hp2
      exact hxy
        (((mem_p9Fibre (i := x) (p := p)).mp (Finset.mem_inter.mp hp1).2).symm.trans
          ((mem_p9Fibre (i := y) (p := p)).mp (Finset.mem_inter.mp hp2).2))
    have hX : (∑ i ∈ (Finset.univ : Finset (Fin k)), (X ∩ p9Fibre i).card : ℕ) = X.card := by
      rw [← Finset.card_biUnion hdisjX]
      exact congrArg Finset.card hdecomp.symm
    omega

/-! #### Odd cycles of the disjoint union, and its odd cycle transversal -/

/-- **A 5-cycle of `p9`, in the `i`-th fibre, is an odd cycle of `p9Family k`.** -/
theorem isOddCycle_p9Family_cyc5 (k : ℕ) (a b c d e : Fin 9) (i : Fin k)
    (hne : Function.Injective (cyc5 a b c d e))
    (hadj : ∀ j : Fin 5, p9.Adj ((cyc5 a b c d e) j) ((cyc5 a b c d e) (cycSucc j))) :
    IsOddCycle (p9Family k) ((({a, b, c, d, e} : Finset (Fin 9)).image fun x => (x, i)) :
      Finset (Fin 9 × Fin k)) := by
  refine ⟨5, fun j => (cyc5 a b c d e j, i), by decide, by decide, ?_, ?_, ?_⟩
  · intro x y h
    exact hne (congrArg Prod.fst h)
  · intro j
    exact p9Family_adj.mpr ⟨rfl, hadj j⟩
  · intro p
    constructor
    · intro hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ⟨⟨0, by omega⟩, by simp [cyc5]⟩
      · exact ⟨⟨1, by omega⟩, by simp [cyc5]⟩
      · exact ⟨⟨2, by omega⟩, by simp [cyc5]⟩
      · exact ⟨⟨3, by omega⟩, by simp [cyc5]⟩
      · exact ⟨⟨4, by omega⟩, by simp [cyc5]⟩
    · rintro ⟨j, hj⟩
      obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hj
      have hx : cyc5 a b c d e j ∈ ({a, b, c, d, e} : Finset (Fin 9)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        fin_cases j <;> simp [cyc5]
      exact Finset.mem_image.mpr ⟨cyc5 a b c d e j, hx, Prod.ext h1 h2⟩

/-- **`Ca` in the `i`-th fibre is an odd cycle of `p9Family k`.** -/
theorem isOddCycle_p9Family_Ca (k : ℕ) (i : Fin k) :
    IsOddCycle (p9Family k) (Ca.image fun x => (x, i)) :=
  isOddCycle_p9Family_cyc5 k 1 2 3 8 6 i (by decide) (by decide)

/-- **Every odd cycle transversal of `p9Family k` meets each fibre in at least two vertices** — the
upper bound `2 * k` is forced by the two 5-cycles of `p9` that avoid any given vertex. -/
theorem card_inter_fibre_two {k : ℕ} (i : Fin k) {X : Finset (Fin 9 × Fin k)}
    (hX : HitsOddCycles (p9Family k) X) : 2 ≤ (X ∩ p9Fibre i).card := by
  by_contra hcon
  have hsub : ∀ a ∈ X ∩ p9Fibre i, ∀ b ∈ X ∩ p9Fibre i, a = b := Finset.card_le_one.mp (by omega)
  rcases (X ∩ p9Fibre i).eq_empty_or_nonempty with h | ⟨v, hv⟩
  · refine hX _ (isOddCycle_p9Family_Ca k i) ?_
    have hd : @Inter.inter (Finset (Fin 9 × Fin k))
        (@Finset.instInter (Fin 9 × Fin k) (Classical.decEq (Fin 9 × Fin k)))
        (Ca.image fun x => (x, i)) X = ∅ := by
      ext z
      constructor
      · intro hz
        obtain ⟨hzi, hzX⟩ := @Finset.mem_inter (Fin 9 × Fin k) (Classical.decEq _) _ _ |>.mp hz
        obtain ⟨x, hx, hx'⟩ := Finset.mem_image.mp hzi
        have hzm : z ∈ X ∩ p9Fibre i := Finset.mem_inter.mpr
          ⟨hzX, mem_p9Fibre.mpr (congrArg Prod.snd hx').symm⟩
        rw [h] at hzm
        simp at hzm
      · intro hz
        simp at hz
    exact hd
  · have hX1 : X ∩ p9Fibre i = {v} := by
      ext p
      constructor
      · intro hp
        exact Finset.mem_singleton.mpr (hsub p hp v hv)
      · intro hp
        rw [Finset.mem_singleton] at hp
        rw [hp]
        exact hv
    obtain ⟨a, b, c, d, e, hne, hadj, hvn⟩ := exists_oddCycle_data_av v.1
    have hd : @Inter.inter (Finset (Fin 9 × Fin k))
        (@Finset.instInter (Fin 9 × Fin k) (Classical.decEq (Fin 9 × Fin k)))
        (({a, b, c, d, e} : Finset (Fin 9)).image fun x => (x, i)) X = ∅ := by
      ext z
      constructor
      · intro hz
        obtain ⟨hzi, hzX⟩ := @Finset.mem_inter (Fin 9 × Fin k) (Classical.decEq _) _ _ |>.mp hz
        obtain ⟨x, hx, hx'⟩ := Finset.mem_image.mp hzi
        rw [← hx'] at hzX
        have hz'' : (x, i) ∈ X ∩ p9Fibre i := Finset.mem_inter.mpr
          ⟨hzX, mem_p9Fibre.mpr rfl⟩
        rw [hX1, Finset.mem_singleton] at hz''
        exact absurd ((congrArg Prod.fst hz'').symm ▸ hx) hvn
      · intro hz
        simp at hz
    exact hX _ (isOddCycle_p9Family_cyc5 k a b c d e i hne hadj) hd

/-- **The odd cycle transversal number of `p9Family k` is at least `2 * k`.** -/
theorem card_le_two_k_of_hitsOddCycles {k : ℕ} {X : Finset (Fin 9 × Fin k)}
    (hX : HitsOddCycles (p9Family k) X) : 2 * k ≤ X.card := by
  have hdisjX : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      fun i => X ∩ p9Fibre i := by
    intro x hx y hy hxy
    refine Finset.disjoint_left.mpr ?_
    intro p hp1 hp2
    exact hxy (((mem_p9Fibre (i := x) (p := p)).mp (Finset.mem_inter.mp hp1).2).symm.trans
      ((mem_p9Fibre (i := y) (p := p)).mp (Finset.mem_inter.mp hp2).2))
  have hXsum : (∑ i, (X ∩ p9Fibre i).card : ℕ) = X.card := by
    have hb := Finset.card_biUnion hdisjX
    rw [← hb]
    exact congrArg Finset.card (inter_biUnion_fibre X).symm
  calc 2 * k = ∑ i, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ i, (X ∩ p9Fibre i).card := Finset.sum_le_sum fun i _ => card_inter_fibre_two i hX
    _ = X.card := hXsum

/-! #### The exact value of the conclusion on the disjoint union, and the improved lower bound -/

/-- **`CloseToBipartite (2 * k) (p9Family k)`**: deleting the two vertices `{2, 6}` in each fibre
leaves a disjoint union of copies of `p9 - {2, 6}`, which is bipartite. -/
theorem closeToBipartite_p9Family_two (k : ℕ) : CloseToBipartite (2 * k) (p9Family k) := by
  refine ⟨({2, 6} : Finset (Fin 9)) ×ˢ (Finset.univ : Finset (Fin k)), ?_, ?_⟩
  · rw [Finset.card_product]
    simp
  · refine ⟨SimpleGraph.Coloring.mk
      (fun p : Fin 9 × Fin k => if p.1 ∈ ({2, 6} : Finset (Fin 9)) then 0 else p9col p.1) ?_⟩
    intro v w hadj
    have h4 := deleteFinset_adj.mp hadj
    obtain ⟨h1, h2, h3⟩ := h4
    rw [p9Family_adj] at h3
    have hv2 : v.1 ∉ ({2, 6} : Finset (Fin 9)) := by
      intro hv
      exact h1 (Finset.mem_product.mpr ⟨hv, Finset.mem_univ _⟩)
    have hw2 : w.1 ∉ ({2, 6} : Finset (Fin 9)) := by
      intro hw
      exact h2 (Finset.mem_product.mpr ⟨hw, Finset.mem_univ _⟩)
    simp only [if_neg hv2, if_neg hw2]
    exact p9col_valid _ _ h3.2 hv2 hw2

/-- **The exact value of the conclusion on the disjoint union of `k` copies of `p9`**: it is
`CloseToBipartite m` exactly when `2 * k ≤ m`. -/
theorem closeToBipartite_p9Family_iff {k m : ℕ} :
    CloseToBipartite m (p9Family k) ↔ 2 * k ≤ m := by
  constructor
  · rintro ⟨X, hX, hb⟩
    exact le_trans (card_le_two_k_of_hitsOddCycles (hitsOddCycles_of_isBipartite_delete hb)) hX
  · intro h
    exact closeToBipartite_mono h (closeToBipartite_p9Family_two k)

/-- **THE IMPROVED LOWER BOUND `f(k) ≥ 2 k` of Erdős Problem #73.**  For every `k` and every
`m < 2 k` there is a finite graph satisfying `LocIndep k` which is not `m`-close to bipartite:
the disjoint union of `k` copies of the Petersen graph with one vertex deleted.  This
*strictly improves* `JSP90.erdos73_lower_bound` (`f(k) ≥ k`) of `JSPProblem/Sharp.lean`. -/
theorem erdos73_lower_bound_two (k m : ℕ) (h : m < 2 * k) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G ∧ ¬ CloseToBipartite m G := by
  refine ⟨Fin 9 × Fin k, inferInstance, p9Family k, locIndep_p9Family k, ?_⟩
  intro hb
  have h' := closeToBipartite_p9Family_iff.mp hb
  omega

/-- **The same lower bound, in the shape of the theorem**: no constant below `2 * k` works for
Erdős #73 with the parameter `k`. -/
theorem no_constant_below_two_k (k : ℕ) :
    ¬ ∃ m, m < 2 * k ∧ ∀ (W : Type) (_ : Fintype W) (G : SimpleGraph W),
      LocIndep k G → CloseToBipartite m G := by
  rintro ⟨m, hm, h⟩
  obtain ⟨W, instW, G, hG, hnb⟩ := erdos73_lower_bound_two k m hm
  exact hnb (h W instW G hG)

end

end JSP90
