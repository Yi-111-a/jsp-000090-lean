/-
# JSP-000090, round 73 — **the double book of the fan, the two-cell counting lemma, and the
critical-cycle counting at the fan with the constant `c * (k - 1)`**

## Where the development stands

Rounds 69–72 reduced Erdős Problem #73 to **one** statement, `JSP90.FanErdős73 f` of
`JSPProblem/Free.lean`: for every triangle-free `G` with `LocIndep k G` and every odd cycle `C` of
`G`, a set `Z` of at most `f k` vertices meeting every odd cycle of `G` that meets the boundary of
`C`.  `JSP90.erdos73_iff_fanErdős73` proves the statement is *equivalent* to the whole problem, and
round 68 proves it equivalent to `JSP90.TriangleFreeOnly`.

Round 72 named the **disjoint book** of the fan: every fan vertex attaches to one point of `C` or to
a pair two steps apart (`JSP90.attachSet_eq_singleton_or_pair`), so the fan is the disjoint union of
the `m` *single* classes `singleClass G C f i` and the two-attachment part `doubleAttach G C`.  It
proved each single class is independent, that the classes are disjoint, and the counting lemma
`JSP90.card_le_boundary_sdiff_two_singleClass`.

This round does three things, all **on the critical path**.

## Part 1 — the double book: the two-attachment classes are ALSO independent cells

The two-attachment part of the fan was left as one opaque set `doubleAttach G C`.  It is not opaque:
it splits, like the one-attachment part, into **independent** classes, one per *pair* of attachment
points.

* **`JSP90.doubleClass`** — the fan vertices whose attachment set is exactly
  `{f i, f (cycSucc^[2] i)}`, i.e. the pair two steps apart with midpoint `f (cycSucc i)`.
* **`JSP90.isIndepSet_doubleClass`: a double class is an INDEPENDENT SET.**  In a triangle-free
  graph two vertices with a common neighbour are not adjacent, and the two vertices of a double
  class have `f i` as a common neighbour.  This is the first statement of the file: the classical
  fact is that the two-attachment part of the fan is *also* a book of independent cells, not an
  unstructured remainder.
* **`JSP90.disjoint_doubleClass_of_ne`: double classes are pairwise DISJOINT.**  If
  `{f i, f (i+2)} = {f j, f (j+2)}` then either `i = j` or `i = j + 2` and `i + 2 = j`, i.e. four
  steps around the cycle return to the start — impossible for `m ≥ 5`
  (`JSP90.cycSucc_pow_four_ne` of round 72, the arithmetic lemma that was needed exactly here).
* Together with round 72: **the fan is the disjoint union of `2m` independent cells**, the `m`
  single classes and the `m` double classes, and every fan vertex lies in exactly one of them
  (`JSP90.mem_singleClass_or_doubleClass`).

## Part 2 — the parity and the counting lemma for TWO ARBITRARY CELLS

Round 72's parity lemma was about two *single* classes.  The book now has `2m` cells, and the parity
lemma is uniform over **any two of them**, single or double:

* **`JSP90.fanCell`** — the cell of a pair `(i, b)`, `b = 0` the single class and `b = 1` the double
  class, with the key property **`JSP90.subset_fanCell_fanClass`**: every cell is contained in the
  *attachment class* of `f i`.  (A double class is contained in the attachment class of `f i`
  because it is adjacent to `f i`.)
* **`JSP90.not_isOddCycle_of_subset_two_cell`: an odd cycle of `G` is never contained in the union
  of two cells** — the single hypothesis `D ⊆ fanCell i b ∪ fanCell j c` feeding
  `JSP90.not_isOddCycle_of_subset_fanClass_union` of round 70.  So **every odd cycle of the fan meets
  at least three of the `2m` cells**, a strengthening of round 72's "at least three *single* classes"
  (it now also counts the double cells, and the two special cases are named:
  `JSP90.not_isOddCycle_of_subset_two_doubleClass`,
  `JSP90.not_isOddCycle_of_subset_singleClass_doubleClass`,
  `JSP90.not_isOddCycle_of_subset_doubleClass_singleClass`).
* **`JSP90.hitsOddCycles_boundary_sdiff_fanCell`** and
  **`JSP90.card_le_boundary_sdiff_twoCell`** — the counting lemma of the book for **all** pairs of
  the `2m` cells, not only pairs of single classes: a packing of `j` odd cycles inside the fan needs
  `j` vertices outside *every two cells*, and `∂C \ (cell ∪ cell)` is a transversal of the odd cycles
  inside the fan with `|cell| + |cell| + |Z| ≤ |∂C|` (`JSP90.exists_fanTransversal_le_card_fanCell`),
  where the two cells are *disjoint* — which needs the new disjointness lemmas of Part 1.

## Part 3 — a new instance of the headline theorem along the two-cell axis

* **`JSP90.fanErdős73_of_fan_twoCell`**, **`JSP90.erdos73On_of_fan_twoCell`**,
  **`JSP90.erdos73_of_fan_twoCell`** — if every odd cycle `C` of a triangle-free `G` has **two cells
  of the `2m`-cell book** (of *any* kinds) whose union is a transversal of all the odd cycles of `G`
  meeting `∂C`, and whose combined size is at most `q`, then `LocIndep k G` forces
  `CloseToBipartite (fanBound (fun _ => q) k) G`, and `Erdős73 k` for every `k`.  Round 72's instance
  `JSP90.erdos73On_of_fan_singleClassTwo` is the special case of two *single* cells; the new
  hypothesis is strictly larger, because the two-attachment cells are now usable.  No packing number,
  no odd girth, no packing weight, no bound on the number of branch vertices.

## Part 4 — THE CRITICAL-CYCLE COUNTING IN THE BOOK, WITH THE CONSTANT `c * (k - 1)`

This is the concrete next lemma named in `discovery/JSP-000090/policy.json`, and it is where the
constant of the fan statement comes from.

* **`JSP90.HitsFanOddCycles`**, **`JSP90.MinimalFanTransversal`**,
  `JSP90.fanTransversal_hits`, `JSP90.eq_of_fanTransversal_of_minimal`,
  **`JSP90.exists_minimalFanTransversal`**, **`JSP90.exists_criticalFanCycle_of_minimal`** and
  **`JSP90.FanCriticalTransversal`** / `JSP90.exists_criticalFanTransversal_of_minimal`: the whole
  minimal-transversal apparatus of `JSPProblem/Critical.lean`, *restricted to the odd cycles contained
  in the boundary of `C`*.  In particular **`JSP90.criticalFanCycle_hits_three_cells`**: the private
  cycle of `z` is an odd cycle of the fan, hence by Part 2 it meets at least three of the `2m` cells.
* **`JSP90.card_fanTransversal_le_of_colouring_pack` and
  `JSP90.card_fanTransversal_le_of_colouring`: `|Z| ≤ c * (k - 1)`.**  This is the fan version of
  round 53's `JSP90.card_X_le_of_colouring`, and the constant is **strictly better**: inside one
  colour class the private cycles are pairwise vertex-disjoint odd cycles *of the fan*, hence a
  packing disjoint from `C`, hence by `JSP90.oddCycleFamily_card_le_of_boundary` (round 69) at most
  `k - 1` of them — not `k`.  Round 72's descent `JSP90.locIndep_boundary` is what makes `k - 1`
  available at this point.
* **`JSP90.FanCriticalErdős73 c`** — every shortest odd cycle of a triangle-free `G` with
  `LocIndep k G` has a minimal transversal of the odd cycles inside its boundary whose critical
  intersection graph is `c`-colourable, and which meets every odd cycle that *touches* the
  boundary — and
  **`JSP90.fanErdős73_of_fanCritical`**, **`JSP90.erdos73On_of_fanCritical`**,
  **`JSP90.erdos73_of_fanCritical`**: the fan statement with the explicit constant
  `f k = c * (k - 1)`, hence Erdős Problem #73.  This is a *sharper* localisation of the missing
  statement than round 53's `JSP90.SpreadMinimalTransversal`, which quantified over minimal
  transversals of *all* the odd cycles of `G` and paid `c * k`.  The last conjunct of the
  hypothesis is the touching property: `JSP90.FanErdős73` asks for a set meeting every odd cycle
  `D` with `D ∩ ∂C ≠ ∅`, whereas a minimal transversal of the odd cycles *contained* in `∂C` need
  not meet a cycle that only touches it.  It is stated as a hypothesis, not inferred.

## What is *not* proved

Two things, both stated as hypotheses of `JSP90.FanCriticalErdős73` rather than assumed away:

1. **the colouring** — no bound on the chromatic number of `JSP90.FanIntGraph` in terms of `k`;
   everything downstream of it is proved, so this is the single remaining input of the counting
   half of the argument;
2. **the touching property** — the last conjunct of `JSP90.FanCriticalErdős73`, i.e. round 72's
   sub-goal (2), which is left open.

`JSP90.FanErdős73 f` for any `f`, and hence `jsp_000090_main`; behind it stands
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas, JCTA-B 2003).  What this round adds is
the exact place the constant is produced: the *critical intersection graph of a minimal transversal
of the fan of one odd cycle*, with the fan packing bound `k - 1`.  The remaining content of that
graph is its chromatic number; the classical shape of the argument (Reed–Robertson–Seymour–Thomas,
and the `ΔY`-structure of Campos–Griffiths–Morris–Sahasrabudhe) is that it is bounded by an absolute
constant times the packing number.  Not proved here.  The secondary blocker is untouched: the odd
cycles of `G` that MEET the fan from OUTSIDE it.
-/

import JSPProblem.Book
import Mathlib.Data.Finset.SDiff

namespace JSP90

universe u

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqDouble : DecidableEq V := Classical.decEq V

local instance instDecidableAdjDouble (G : SimpleGraph V) : ∀ (v w : V), Decidable (G.Adj v w) :=
  fun _ _ => Classical.propDecidable _

/-! ## Part 1 — the double book: the two-attachment classes -/

section DoubleBook

/-- **FOUR STEPS AROUND A CYCLE OF LENGTH AT LEAST FIVE NEVER RETURN TO THE STARTING POINT, IN THE
FORM `(cycSucc^[4] i) ≠ i`.**  This is `JSP90.cycSucc_pow_four_ne` of round 72, transported from
the underlying naturals to `Fin m`; it is the arithmetic behind the disjointness of the double
classes below. -/
theorem cycSucc_pow_four_ne' {m : ℕ} (hm : 5 ≤ m) (i : Fin m) :
    ((cycSucc^[4] : Fin m → Fin m) i) ≠ i := by
  intro h
  exact cycSucc_pow_four_ne hm i (congrArg Fin.val h)

/-- **TWO STEPS AROUND A CYCLE OF LENGTH AT LEAST THREE NEVER RETURN TO THE STARTING POINT.**  The
shorter companion of `JSP90.cycSucc_pow_four_ne'`; it is what makes the pair `{f i, f (i+2)}` a
genuine two-element set. -/
theorem cycSucc_two_ne_self {m : ℕ} (hm : 3 ≤ m) (i : Fin m) :
    ((cycSucc^[2] : Fin m → Fin m) i) ≠ i := by
  intro h
  have hne := cycSucc_pow_inj (m := m) i (p := 2) (q := 0) (by omega) (by omega) (by omega)
  rw [Function.iterate_zero_apply, h] at hne
  exact hne rfl

/-- **THE FAR POINT OF A TWO-STEP ARC IS NOT ITS START**: `f i ≠ f (cycSucc^[2] i)`. -/
theorem inj_f_twoStep {m : ℕ} (hm : 5 ≤ m) {f : Fin m → V} (hinj : Function.Injective f)
    (i : Fin m) : f i ≠ f ((cycSucc^[2] : Fin m → Fin m) i) := by
  intro h
  have h1 : i = (cycSucc^[2] : Fin m → Fin m) i := hinj h
  exact absurd h1.symm (cycSucc_two_ne_self (by omega) i)

/-- Membership in a two-element finset, as a disjunction. -/
theorem mem_pair {V : Type*} [DecidableEq V] {a b c : V} :
    c ∈ ({a, b} : Finset V) ↔ (c = a ∨ c = b) := by
  simp [Finset.mem_insert, Finset.mem_singleton]

theorem mem_pair_left {V : Type*} [DecidableEq V] (a b : V) : a ∈ ({a, b} : Finset V) :=
  (mem_pair.mpr (Or.inl rfl))

theorem mem_pair_right {V : Type*} [DecidableEq V] (a b : V) : b ∈ ({a, b} : Finset V) :=
  (mem_pair.mpr (Or.inr rfl))

/-- **MEMBERSHIP TRANSFERS ALONG AN EQUALITY OF FINSETS.** -/
theorem mem_of_mem_of_eq {V : Type*} [DecidableEq V] {s t : Finset V} {x : V} (h : s = t)
    (hx : x ∈ s) : x ∈ t := by
  rw [← h]
  exact hx

/-- **TWO TWO-ELEMENT FINSETS THAT ARE EQUAL MATCH EITHER DIRECTLY OR SWAPPED.** -/
theorem eq_pair {V : Type*} [DecidableEq V] {a b c d : V} (h : ({a, b} : Finset V) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have h1m : a ∈ ({c, d} : Finset V) := mem_of_mem_of_eq h (mem_pair_left a b)
  have h1 : a = c ∨ a = d := mem_pair.mp h1m
  have h2m : b ∈ ({c, d} : Finset V) := mem_of_mem_of_eq h (mem_pair_right a b)
  have h2 : b = c ∨ b = d := mem_pair.mp h2m
  rcases h1 with hac | had
  · rcases h2 with hbc | hbd
    · -- `a = c` and `b = c`, so `a = b`; and `d ∈ {a, b}` forces `d = a`: the swapped case
      have hdm : d ∈ ({a, b} : Finset V) := mem_of_mem_of_eq h.symm (mem_pair_right c d)
      rcases mem_pair.mp hdm with hx | hx
      · exact Or.inr ⟨hx.symm, hbc⟩
      · -- `d = b` and `a = b`
        have hab : a = b := (hbc.trans hac.symm).symm
        have hda : d = a := hx.trans hab.symm
        exact Or.inr ⟨hda.symm, hbc⟩
    · exact Or.inl ⟨hac, hbd⟩
  · rcases h2 with hbc | hbd
    · exact Or.inr ⟨had, hbc⟩
    · -- `a = d` and `b = d`, so `a = b`; and `c ∈ {a, b}` forces `c = a`: the direct case
      have hcm : c ∈ ({a, b} : Finset V) := mem_of_mem_of_eq h.symm (mem_pair_left c d)
      rcases mem_pair.mp hcm with hx | hx
      · exact Or.inl ⟨hx.symm, hbd⟩
      · -- `c = b` and `a = b`
        have hab : a = b := had.trans hbd.symm
        have hca : c = a := hx.trans hab.symm
        exact Or.inl ⟨hca.symm, hbd⟩

/-- **A DOUBLE CLASS OF THE BOOK**: the fan vertices whose attachment set on `C` is exactly the pair
`{f i, f (cycSucc^[2] i)}`, i.e. the two points two steps apart with midpoint `f (cycSucc i)`.

This is the object round 72 lacked: the two-attachment part of the fan, split the way the
one-attachment part is split.  `JSP90.attachSet_eq_singleton_or_pair` of round 72 says that the
union of the double classes *is* `doubleAttach G C`, and the lemmas below say the double classes are
independent and disjoint, so the whole fan is a book of `2m` independent cells. -/
noncomputable def doubleClass (G : SimpleGraph V) (C : Finset V) (f : Fin m → V) (i : Fin m) :
    Finset V :=
  (boundary G C).filter (fun x => attachSet G C x = {f i, f ((cycSucc^[2] : Fin m → Fin m) i)})

theorem mem_doubleClass {C : Finset V} {f : Fin m → V} {i : Fin m} {x : V} :
    x ∈ doubleClass G C f i ↔ x ∈ boundary G C ∧
      attachSet G C x = {f i, f ((cycSucc^[2] : Fin m → Fin m) i)} := by
  simp [doubleClass]

theorem subset_doubleClass_boundary (C : Finset V) (f : Fin m → V) (i : Fin m) :
    doubleClass G C f i ⊆ boundary G C :=
  fun _ hx => (mem_doubleClass.mp hx).1

/-- **A DOUBLE CLASS HAS EXACTLY TWO ATTACHMENT POINTS.** -/
theorem card_attachSet_doubleClass {m : ℕ} (hm : 5 ≤ m) {C : Finset V} {f : Fin m → V}
    (hinj : Function.Injective f) {i : Fin m} {x : V} (hx : x ∈ doubleClass G C f i) :
    (attachSet G C x).card = 2 := by
  rw [(mem_doubleClass.mp hx).2, Finset.card_pair_eq_two_iff]
  exact inj_f_twoStep hm hinj i

/-- **A DOUBLE CLASS IS AN INDEPENDENT SET — THE FIRST STATEMENT OF THIS FILE, AND NEW CONTENT.**

In a triangle-free graph two vertices with a common neighbour are not adjacent
(`JSP90.not_adj_of_common_neigh_of_cliqueFree3`, round 69), and the two members of a double class
have `f i` as a common neighbour.  So **the two-attachment part of the fan is a book of independent
cells too**, and not the opaque remainder it was in round 72. -/
theorem isIndepSet_doubleClass (hG3 : G.CliqueFree 3) {m : ℕ} {C : Finset V} {f : Fin m → V}
    (i : Fin m) : G.IsIndepSet (doubleClass G C f i) := by
  intro x hx y hy hxy
  have hA : attachSet G C x = {f i, f ((cycSucc^[2] : Fin m → Fin m) i)} :=
    (mem_doubleClass.mp hx).2
  have hB : attachSet G C y = {f i, f ((cycSucc^[2] : Fin m → Fin m) i)} :=
    (mem_doubleClass.mp hy).2
  have hfix : f i ∈ attachSet G C x := by rw [hA]; exact mem_pair_left _ _
  have hfix' : f i ∈ attachSet G C y := by rw [hB]; exact mem_pair_left _ _
  exact not_adj_of_common_neigh_of_cliqueFree3 hG3
    ((mem_attachSet.mp hfix).2.symm) ((mem_attachSet.mp hfix').2.symm)

/-- **THE TWO-STEP ARC PAIR DETERMINES ITS INDEX.**  If `{f i, f (i + 2)} = {f j, f (j + 2)}` then
`i = j`, for a cycle of length at least five.

The content: the only other possibility is that the pair is read the other way round, i.e.
`f i = f (j + 2)`; then either two steps send `i` to `j` and `j` to `i` — so two steps return to the
start — or two steps send `j` to `j`, which says the same thing.  Either way
`JSP90.cycSucc_two_ne_self` or `JSP90.cycSucc_pow_four_ne'` applies. -/
theorem inj_pair_twoStep {m : ℕ} (hm : 5 ≤ m) {f : Fin m → V} (hinj : Function.Injective f)
    {i j : Fin m} (h : ({f i, f ((cycSucc^[2] : Fin m → Fin m) i)} : Finset V)
      = {f j, f ((cycSucc^[2] : Fin m → Fin m) j)}) : i = j := by
  have h1m : f i ∈ ({f j, f ((cycSucc^[2] : Fin m → Fin m) j)} : Finset V) := by
    rw [← h]
    exact mem_pair_left _ _
  have h1 : f i = f j ∨ f i = f ((cycSucc^[2] : Fin m → Fin m) j) := mem_pair.mp h1m
  rcases h1 with h1 | h1
  · exact hinj h1
  · have hsteq : i = (cycSucc^[2] : Fin m → Fin m) j := hinj h1
    have h2m : f ((cycSucc^[2] : Fin m → Fin m) i)
        ∈ ({f j, f ((cycSucc^[2] : Fin m → Fin m) j)} : Finset V) := by
      rw [← h]
      exact mem_pair_right _ _
    have h2 : f ((cycSucc^[2] : Fin m → Fin m) i) = f j ∨
        f ((cycSucc^[2] : Fin m → Fin m) i) = f ((cycSucc^[2] : Fin m → Fin m) j) :=
      mem_pair.mp h2m
    rcases h2 with h2 | h2
    · -- two steps send `i` to `j` and `j` to `i`: four steps return to the start
      have h3 : (cycSucc^[2] : Fin m → Fin m) i = j := hinj h2
      have h4 : ((cycSucc^[4] : Fin m → Fin m) j) = j :=
        (congrArg (cycSucc^[2] : Fin m → Fin m) hsteq).symm.trans h3
      exact absurd h4 (cycSucc_pow_four_ne' hm j)
    · -- two steps send `j` to `j`: two steps return to the start
      have h3 : (cycSucc^[2] : Fin m → Fin m) i = (cycSucc^[2] : Fin m → Fin m) j := hinj h2
      have hfix : (cycSucc^[2] : Fin m → Fin m) ((cycSucc^[2] : Fin m → Fin m) j)
          = (cycSucc^[2] : Fin m → Fin m) j :=
        (congrArg (cycSucc^[2] : Fin m → Fin m) hsteq).symm.trans h3
      exact False.elim (cycSucc_two_ne_self (by omega) _ hfix)

/-- **TWO DISTINCT DOUBLE CLASSES ARE DISJOINT.**  The disjointness half of the double book: the
two-attachment part of the fan is a *disjoint* family of `m` cells. -/
theorem disjoint_doubleClass_of_ne {m : ℕ} (hm : 5 ≤ m) {C : Finset V} {f : Fin m → V}
    (hinj : Function.Injective f) {i j : Fin m} (hij : i ≠ j) :
    Disjoint (doubleClass G C f i) (doubleClass G C f j) := by
  refine Finset.disjoint_left.mpr fun x hx hcon => ?_
  have hA : attachSet G C x = {f i, f ((cycSucc^[2] : Fin m → Fin m) i)} :=
    (mem_doubleClass.mp hx).2
  have hB : attachSet G C x = {f j, f ((cycSucc^[2] : Fin m → Fin m) j)} :=
    (mem_doubleClass.mp hcon).2
  have hpair : ({f i, f ((cycSucc^[2] : Fin m → Fin m) i)} : Finset V)
      = {f j, f ((cycSucc^[2] : Fin m → Fin m) j)} := hA.symm.trans hB
  exact absurd (inj_pair_twoStep hm hinj hpair) hij

/-- **A DOUBLE CLASS LIES IN THE ATTACHMENT CLASS OF ITS OWN INDEX** (it is adjacent to `f i`). -/
theorem subset_doubleClass_fanClass {m : ℕ} {C : Finset V} {f : Fin m → V} (i : Fin m) :
    doubleClass G C f i ⊆ fanClass G C (f i) := by
  intro x hx
  have hA : attachSet G C x = {f i, f ((cycSucc^[2] : Fin m → Fin m) i)} :=
    (mem_doubleClass.mp hx).2
  have hmem : f i ∈ attachSet G C x := by rw [hA]; exact mem_pair_left _ _
  exact mem_fanClass.mpr ⟨(mem_doubleClass.mp hx).1, (mem_attachSet.mp hmem).2.symm⟩

/-- **A DOUBLE CLASS IS ADJACENT TO THE FAR POINT OF ITS PAIR**, so it also lies in that attachment
class: `x ~ f i` and `x ~ f (i + 2)`.  This is the second half of the two-attachment structure. -/
theorem subset_doubleClass_fanClass_far {m : ℕ} {C : Finset V} {f : Fin m → V} (i : Fin m) :
    doubleClass G C f i ⊆ fanClass G C (f ((cycSucc^[2] : Fin m → Fin m) i)) := by
  intro x hx
  have hA : attachSet G C x = {f i, f ((cycSucc^[2] : Fin m → Fin m) i)} :=
    (mem_doubleClass.mp hx).2
  have hmem : f ((cycSucc^[2] : Fin m → Fin m) i) ∈ attachSet G C x := by
    rw [hA]
    exact mem_pair_right _ _
  exact mem_fanClass.mpr ⟨(mem_doubleClass.mp hx).1, (mem_attachSet.mp hmem).2.symm⟩

/-- **A DOUBLE CLASS MEETS NO SINGLE CLASS**: the two kinds of cell are disjoint, cell by cell.  (For
round 72 this was `JSP90.disjoint_singleClass_double`, disjointness from the whole two-attachment
part; here it is cell by cell, which is what the two-cell counting lemma of Part 2 consumes.) -/
theorem disjoint_singleClass_doubleClass {m : ℕ} (hm : 5 ≤ m) {C : Finset V} {f : Fin m → V}
    (hinj : Function.Injective f) (i j : Fin m) :
    Disjoint (singleClass G C f i) (doubleClass G C f j) := by
  refine Finset.disjoint_left.mpr fun x hx hcon => ?_
  have hA : attachSet G C x = {f i} := (mem_singleClass.mp hx).2
  have hB : attachSet G C x = {f j, f ((cycSucc^[2] : Fin m → Fin m) j)} :=
    (mem_doubleClass.mp hcon).2
  have h1 : (attachSet G C x).card = 1 := by rw [hA]; simp
  have h2 : (attachSet G C x).card = 2 := by
    rw [hB, Finset.card_pair_eq_two_iff]
    exact inj_f_twoStep hm hinj j
  omega

/-- **THE WHOLE BOOK: EVERY FAN VERTEX LIES IN EXACTLY ONE OF THE `2m` CELLS.**  Together with
`JSP90.mem_singleClass_or_doubleAttach` of round 72 this says the fan is the *disjoint* union of the
`m` single classes and the `m` double classes. -/
theorem mem_singleClass_or_doubleClass {m : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {x : V} (hxb : x ∈ boundary G C) :
    (∃ i : Fin m, x ∈ singleClass G C f i) ∨ (∃ i : Fin m, x ∈ doubleClass G C f i) := by
  rcases mem_singleClass_or_doubleAttach hshort hm hm3 f hinj hcyc hCmem hxb with h | h
  · exact Or.inl h
  · obtain ⟨hxb', hcard⟩ := mem_doubleAttach.mp h
    rcases attachSet_eq_singleton_or_pair hshort hm hm3 f hinj hcyc hCmem hxb' with ⟨j, hj⟩ | ⟨j, hj⟩
    · have h' : ({f j} : Finset V).card = 2 := by rw [← hj]; exact hcard
      rw [Finset.card_singleton] at h'
      omega
    · exact Or.inr ⟨j, mem_doubleClass.mpr ⟨hxb', hj⟩⟩

/-- **THE DOUBLE PART OF THE FAN IS THE UNION OF THE DOUBLE CLASSES.**  The content is the *reverse*
direction: a two-attachment vertex lies in some double class, so the class is not lost by the
refinement — this is what makes the double cells a cover of `doubleAttach G C`. -/
theorem mem_doubleClass_of_mem_doubleAttach {m : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {x : V} (hxb : x ∈ doubleAttach G C) :
    ∃ i : Fin m, x ∈ doubleClass G C f i := by
  obtain ⟨hxb', hcard⟩ := mem_doubleAttach.mp hxb
  rcases mem_singleClass_or_doubleClass hshort hm hm3 f hinj hcyc hCmem hxb' with ⟨i, hi⟩ | ⟨i, hi⟩
  · exfalso
    have hA : attachSet G C x = {f i} := (mem_singleClass.mp hi).2
    have h' : ({f i} : Finset V).card = 2 := by rw [← hA]; exact hcard
    rw [Finset.card_singleton] at h'
    omega
  · exact ⟨i, hi⟩

/-- **THE DOUBLE CLASSES ARE A PARTITION OF THE TWO-ATTACHMENT PART**: a two-attachment vertex lies
in exactly one double class.  This is `JSP90.inj_pair_twoStep` applied to two memberships. -/
theorem unique_doubleClass_of_mem_doubleAttach {m : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {x : V} (hxb : x ∈ doubleAttach G C) {i j : Fin m}
    (hi : x ∈ doubleClass G C f i) (hj : x ∈ doubleClass G C f j) : i = j := by
  have hA : attachSet G C x = {f i, f ((cycSucc^[2] : Fin m → Fin m) i)} :=
    (mem_doubleClass.mp hi).2
  have hB : attachSet G C x = {f j, f ((cycSucc^[2] : Fin m → Fin m) j)} :=
    (mem_doubleClass.mp hj).2
  exact inj_pair_twoStep hm3 hinj (hA.symm.trans hB)

end DoubleBook

/-! ## Part 2 — the parity and the counting lemma for two arbitrary cells -/

section TwoCell

/-- **A CELL OF THE BOOK**, indexed by an index `i` and a flag `b`: `b = 0` is the single class of
`f i`, `b = 1` the double class of the pair `{f i, f (i+2)}`.

The point of the package is the next lemma, `JSP90.subset_fanCell_fanClass`: **every cell is
contained in the attachment class of `f i`**, which is what turns "two cells" into "two attachment
classes" in the parity lemma below. -/
noncomputable def fanCell (G : SimpleGraph V) (C : Finset V) (f : Fin m → V) (i : Fin m) (b : Bool) :
    Finset V :=
  if b then doubleClass G C f i else singleClass G C f i

theorem mem_fanCell {C : Finset V} {f : Fin m → V} {i : Fin m} {b : Bool} {x : V} :
    x ∈ fanCell G C f i b ↔ x ∈ boundary G C ∧
      (if b then attachSet G C x = {f i, f ((cycSucc^[2] : Fin m → Fin m) i)}
       else attachSet G C x = {f i}) := by
  by_cases hb : b
  · simp [fanCell, hb, mem_doubleClass]
  · simp [fanCell, hb, mem_singleClass]

/-- **EVERY CELL IS CONTAINED IN AN ATTACHMENT CLASS.**  For a single class this is round 72's
`JSP90.subset_singleClass_fanClass`; for a double class it is new (`JSP90.subset_doubleClass_fanClass`).
So the two cells lie in the two attachment classes of their indices, and the parity lemma of round 70
applies. -/
theorem subset_fanCell_fanClass {m : ℕ} {C : Finset V} {f : Fin m → V} (i : Fin m) (b : Bool) :
    fanCell G C f i b ⊆ fanClass G C (f i) := by
  by_cases hb : b
  · simpa [fanCell, hb] using (subset_doubleClass_fanClass (G := G) (C := C) (f := f) i)
  · simpa [fanCell, hb] using (subset_singleClass_fanClass (G := G) (C := C) (f := f) (i := i))

/-- **AN ODD CYCLE OF `G` IS NEVER CONTAINED IN TWO CELLS OF THE BOOK.**  In words: every odd cycle
of the fan meets at least three of the `2m` cells — round 72's statement, with the two-attachment
cells now counted as well.

The proof is round 70's parity lemma with the two hypotheses merged by
`JSP90.subset_fanCell_fanClass`. -/
theorem not_isOddCycle_of_subset_two_cell (hG3 : G.CliqueFree 3) {m : ℕ} {C D : Finset V}
    {f : Fin m → V} {i j : Fin m} {b c : Bool} (hD : IsOddCycle G D) :
    ¬ (D ⊆ fanCell G C f i b ∪ fanCell G C f j c) := by
  intro hsub
  refine not_isOddCycle_of_subset_fanClass_union hG3 (C := C) (D := D) (a := f i) (b := f j) ?_ hD
  intro y hy
  rcases Finset.mem_union.mp (hsub hy) with h | h
  · exact Finset.mem_union.mpr (Or.inl (subset_fanCell_fanClass i b h))
  · exact Finset.mem_union.mpr (Or.inr (subset_fanCell_fanClass j c h))

/-- Two *double* cells: an odd cycle of the fan meets at least three double classes, or is confined
to at most two of them. -/
theorem not_isOddCycle_of_subset_two_doubleClass (hG3 : G.CliqueFree 3) {m : ℕ} {C D : Finset V}
    {f : Fin m → V} {i j : Fin m} (hD : IsOddCycle G D) :
    ¬ (D ⊆ doubleClass G C f i ∪ doubleClass G C f j) := by
  intro hsub
  exact not_isOddCycle_of_subset_two_cell hG3 (C := C) (D := D) (f := f) (i := i) (j := j)
    hD (b := true) (c := true) hsub

/-- A *single* cell together with a *double* cell, in that order. -/
theorem not_isOddCycle_of_subset_singleClass_doubleClass (hG3 : G.CliqueFree 3) {m : ℕ}
    {C D : Finset V} {f : Fin m → V} {i j : Fin m} (hD : IsOddCycle G D) :
    ¬ (D ⊆ singleClass G C f i ∪ doubleClass G C f j) := by
  intro hsub
  exact not_isOddCycle_of_subset_two_cell hG3 (C := C) (D := D) (f := f) (i := i) (j := j)
    hD (b := false) (c := true) hsub

/-- A *double* cell together with a *single* cell, in that order. -/
theorem not_isOddCycle_of_subset_doubleClass_singleClass (hG3 : G.CliqueFree 3) {m : ℕ}
    {C D : Finset V} {f : Fin m → V} {i j : Fin m} (hD : IsOddCycle G D) :
    ¬ (D ⊆ doubleClass G C f i ∪ singleClass G C f j) := by
  intro hsub
  exact not_isOddCycle_of_subset_two_cell hG3 (C := C) (D := D) (f := f) (i := i) (j := j)
    hD (b := true) (c := false) hsub

/-- **AN ODD CYCLE INSIDE THE FAN MEETS AT LEAST THREE OF THE `2m` CELLS**, as a single statement:
for every pair of cells the cycle has a point outside their union. -/
theorem not_subset_two_fanCell_of_isOddCycle (hG3 : G.CliqueFree 3) {m : ℕ} {C D : Finset V}
    {f : Fin m → V} (hD : IsOddCycle G D) (hsub : D ⊆ boundary G C) {i j : Fin m} {b c : Bool} :
    ¬ (D ⊆ fanCell G C f i b ∪ fanCell G C f j c) := by
  intro hsub
  exact not_isOddCycle_of_subset_two_cell hG3 (C := C) (D := D) (f := f) (i := i) (j := j)
    hD (b := b) (c := c) hsub

/-- **THE FAN WITH TWO CELLS REMOVED IS A TRANSVERSAL OF THE ODD CYCLES INSIDE THE FAN**, of size
`|∂C| - |cell| - |cell|` for *any* two of the `2m` cells. -/
theorem hitsOddCycles_boundary_sdiff_fanCell (hG3 : G.CliqueFree 3) {m : ℕ} {C : Finset V}
    (f : Fin m → V) {i j : Fin m} {b c : Bool} {D : Finset V} (hD : IsOddCycle G D)
    (hsub : D ⊆ boundary G C) :
    D ∩ (boundary G C \ (fanCell G C f i b ∪ fanCell G C f j c)) ≠ ∅ := by
  by_contra hcon
  have hne : D ∩ (boundary G C \ (fanCell G C f i b ∪ fanCell G C f j c)) = ∅ := hcon
  refine not_isOddCycle_of_subset_two_cell hG3 (C := C) (D := D) (f := f) (i := i) (j := j)
    (b := b) (c := c) hD ?_
  intro y hy
  by_contra hcontra
  have hmem : y ∈ boundary G C \ (fanCell G C f i b ∪ fanCell G C f j c) :=
    Finset.mem_sdiff.mpr ⟨hsub hy, hcontra⟩
  have hnil : y ∈ (∅ : Finset V) := hne ▸ Finset.mem_inter.mpr ⟨hy, hmem⟩
  simp at hnil

/-- **THE COUNTING LEMMA OF THE BOOK, FOR ALL PAIRS OF CELLS**: a packing of `j` odd cycles inside
the fan of `C` needs `j` vertices outside **every two cells**.

This is round 72's `JSP90.card_le_boundary_sdiff_two_singleClass` with the two-attachment cells
admitted; the single hypothesis that the bound holds for *all* pairs of the `2m` cells simultaneously
is what forces a transversal of the fan to spread out over the book. -/
theorem card_le_boundary_sdiff_twoCell (hG3 : G.CliqueFree 3) {m : ℕ} {C : Finset V}
    (f : Fin m → V) {i j : Fin m} {b c : Bool} {𝒟 : Finset (Finset V)}
    (hfam : IsOddCycleFamily (G := G) 𝒟) (hsub : ∀ D ∈ 𝒟, D ⊆ boundary G C) :
    𝒟.card ≤ (boundary G C \ (fanCell G C f i b ∪ fanCell G C f j c)).card := by
  set Z : Finset V := boundary G C \ (fanCell G C f i b ∪ fanCell G C f j c) with hZdef
  have hne : ∀ D ∈ 𝒟, (D ∩ Z).Nonempty := by
    intro D hX
    rw [Finset.nonempty_iff_ne_empty]
    exact hitsOddCycles_boundary_sdiff_fanCell hG3 f (hfam.2 D hX) (hsub D hX)
  have hdis : ∀ (X : Finset V), X ∈ 𝒟 → ∀ (Y : Finset V), Y ∈ 𝒟 → X ≠ Y →
      ∀ (x : V), x ∈ X ∩ Z → x ∉ Y ∩ Z := by
    intro X hX Y hY hXY x hx
    rcases Finset.mem_inter.mp hx with ⟨hx1, hx2⟩
    intro hxY
    rcases Finset.mem_inter.mp hxY with ⟨hxY1, hxY2⟩
    have hz : x ∈ (∅ : Finset V) :=
      hfam.left X hX Y hY hXY ▸ Finset.mem_inter.mpr ⟨hx1, hxY1⟩
    simp at hz
  have hsub2 : 𝒟.biUnion (fun D : Finset V => D ∩ Z) ⊆ Z := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨D, hD, hzD⟩ := hz
    exact Finset.mem_inter.mp hzD |>.2
  exact (card_le_biUnion_of_disjoint_ne (fun D : Finset V => D ∩ Z) hne hdis).trans
    (Finset.card_le_card hsub2)

/-- **THE LEAST TRANSVERSAL OF THE ODD CYCLES INSIDE THE FAN, WITH THE EXPLICIT COUNT.**  Removing
any two disjoint cells of the book leaves a transversal of size at most
`|∂C| - |cell| - |cell|`.  The disjointness of the two cells (Part 1) is what turns the `sdiff` into
a difference of cardinalities, so choosing the two *largest* cells gives the smallest transversal of
this form. -/
theorem exists_fanTransversal_le_card_fanCell (hG3 : G.CliqueFree 3) {m : ℕ} {C : Finset V}
    (f : Fin m → V) {i j : Fin m} {b c : Bool} (hcells :
    Disjoint (fanCell G C f i b) (fanCell G C f j c)) :
    ∃ Z : Finset V,
      (∀ D : Finset V, IsOddCycle G D → D ⊆ boundary G C → D ∩ Z ≠ ∅) ∧
      (fanCell G C f i b).card + (fanCell G C f j c).card + Z.card ≤ (boundary G C).card := by
  refine ⟨boundary G C \ (fanCell G C f i b ∪ fanCell G C f j c), ?_, ?_⟩
  · intro D hD hsub
    exact hitsOddCycles_boundary_sdiff_fanCell hG3 f hD hsub
  · set s : Finset V := fanCell G C f i b with hsdef
    set t : Finset V := fanCell G C f j c with htdef
    have hst : Disjoint s t := hcells
    have hsub : s ∪ t ⊆ boundary G C := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact (mem_fanCell.mp h).1
      · exact (mem_fanCell.mp h).1
    have heq : (s ∪ t) ∩ boundary G C = s ∪ t :=
      Finset.Subset.antisymm Finset.inter_subset_left
        (fun x hx => Finset.mem_inter.mpr ⟨hx, hsub hx⟩)
    have hle : (s ∪ t).card ≤ (boundary G C).card := Finset.card_le_card hsub
    have hZ : (boundary G C \ (s ∪ t)).card = (boundary G C).card - (s ∪ t).card := by
      have h1 := Finset.card_sdiff (s := s ∪ t) (t := boundary G C)
      rwa [heq] at h1
    have hcard : s.card + t.card = (s ∪ t).card :=
      (Finset.card_union_of_disjoint hst).symm
    have hsub' := Nat.sub_add_cancel hle
    omega

/-- **THE TWO-CELL VERSION WITH THE CELLS NAMED**: a transversal of the odd cycles inside the fan of
size at most `|∂C| - |S_i| - |D_j|`, for a single class and a double class. -/
theorem exists_fanTransversal_le_card_single_double (hG3 : G.CliqueFree 3) {m : ℕ} (hm : 5 ≤ m)
    {C : Finset V} (f : Fin m → V) (hinj : Function.Injective f) (i j : Fin m) :
    ∃ Z : Finset V,
      (∀ D : Finset V, IsOddCycle G D → D ⊆ boundary G C → D ∩ Z ≠ ∅) ∧
      (singleClass G C f i).card + (doubleClass G C f j).card + Z.card ≤ (boundary G C).card := by
  obtain ⟨Z, hZ, hcard⟩ :=
    exists_fanTransversal_le_card_fanCell hG3 f (b := false) (c := true)
      (disjoint_singleClass_doubleClass (by omega) hinj i j)
  exact ⟨Z, hZ, by simpa [fanCell] using hcard⟩

/-- **THE DOUBLE-CELL VERSION WITH THE CELLS NAMED**: a transversal of the odd cycles inside the fan
of size at most `|∂C| - |D_i| - |D_j|`, for two double classes. -/
theorem exists_fanTransversal_le_card_double_double (hG3 : G.CliqueFree 3) {m : ℕ} {C : Finset V}
    (f : Fin m → V) (i j : Fin m) (hm : 5 ≤ m) (hinj : Function.Injective f) (hij : i ≠ j) :
    ∃ Z : Finset V,
      (∀ D : Finset V, IsOddCycle G D → D ⊆ boundary G C → D ∩ Z ≠ ∅) ∧
      (doubleClass G C f i).card + (doubleClass G C f j).card + Z.card ≤ (boundary G C).card := by
  obtain ⟨Z, hZ, hcard⟩ :=
    exists_fanTransversal_le_card_fanCell hG3 f (b := true) (c := true)
      (disjoint_doubleClass_of_ne hm hinj hij)
  exact ⟨Z, hZ, by simpa [fanCell] using hcard⟩

/-- **THE COUNTING LEMMA FOR A SINGLE CLASS AND A DOUBLE CLASS**: a packing of `j` odd cycles inside
the fan needs `j` vertices outside `S_i ∪ D_j`. -/
theorem card_le_boundary_sdiff_singleClass_doubleClass (hG3 : G.CliqueFree 3) {m : ℕ}
    {C : Finset V} (f : Fin m → V) {i j : Fin m} {𝒟 : Finset (Finset V)}
    (hfam : IsOddCycleFamily (G := G) 𝒟) (hsub : ∀ D ∈ 𝒟, D ⊆ boundary G C) :
    𝒟.card ≤ (boundary G C \ (singleClass G C f i ∪ doubleClass G C f j)).card :=
  card_le_boundary_sdiff_twoCell hG3 f (b := false) (c := true) hfam hsub

/-- **THE COUNTING LEMMA FOR TWO DOUBLE CLASSES**: a packing of `j` odd cycles inside the fan needs
`j` vertices outside `D_i ∪ D_j`. -/
theorem card_le_boundary_sdiff_two_doubleClass (hG3 : G.CliqueFree 3) {m : ℕ} {C : Finset V}
    (f : Fin m → V) {i j : Fin m} {𝒟 : Finset (Finset V)}
    (hfam : IsOddCycleFamily (G := G) 𝒟) (hsub : ∀ D ∈ 𝒟, D ⊆ boundary G C) :
    𝒟.card ≤ (boundary G C \ (doubleClass G C f i ∪ doubleClass G C f j)).card :=
  card_le_boundary_sdiff_twoCell hG3 f (b := true) (c := true) hfam hsub

end TwoCell

/-! ## Part 3 — a new instance of the headline theorem along the two-cell axis -/

section Instance

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM (ROUND 73), ALONG THE TWO-CELL AXIS OF THE BOOK.**

If every odd cycle `C` of a triangle-free `G` has **two cells of the `2m`-cell book** (single or
double, in any order) whose union is a transversal of all the odd cycles of `G` meeting `∂C`, and
whose combined size is at most `q`, then `LocIndep k G` forces
`CloseToBipartite (fanBound (fun _ => q) k) G`.

Round 72's `JSP90.erdos73On_of_fan_singleClassTwo` is the special case of two *single* classes; the
hypothesis here is strictly larger, because the two-attachment cells — the cells round 72 could not
use at all — are now available.  No packing number, no odd girth, no packing weight, no bound on
the number of branch vertices, no connectivity. -/
theorem fanErdős73_of_fan_twoCell (q : ℕ)
    (hP : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
      ∀ (m : ℕ) (C : Finset W) (f : Fin m → W), IsOddCycle G C →
      ∃ i j : Fin m, ∃ b c : Bool, (fanCell G C f i b).card + (fanCell G C f j c).card ≤ q ∧
        HitsOddCycles G (fanCell G C f i b ∪ fanCell G C f j c)) :
    FanErdős73.{u} (fun _ => q) := by
  intro k W instW G hG hG3 C hC
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  obtain ⟨i, j, b, c, hcard, hhits⟩ :=
    hP k W instW G hG hG3 m C f (show IsOddCycle G C from ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩)
  refine ⟨fanCell G C f i b ∪ fanCell G C f j c, ?_, fun D hD _ => hhits D hD⟩
  exact (card_union_le' _ _).trans hcard

/-- **ERDŐS PROBLEM #73 FOR THE TWO-CELL AXIS OF THE BOOK OF THE FAN.** -/
theorem erdos73On_of_fan_twoCell (q : ℕ)
    (hP : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
      ∀ (m : ℕ) (C : Finset W) (f : Fin m → W), IsOddCycle G C →
      ∃ i j : Fin m, ∃ b c : Bool, (fanCell G C f i b).card + (fanCell G C f j c).card ≤ q ∧
        HitsOddCycles G (fanCell G C f i b ∪ fanCell G C f j c))
    (k : ℕ) : Erdős73On.{u} k (fanBound (fun _ => q) k) :=
  erdos73On_of_fanErdős73 (fanErdős73_of_fan_twoCell q hP) k

/-- **ERDŐS PROBLEM #73 IN FULL FROM THE TWO-CELL AXIS OF THE BOOK.** -/
theorem erdos73_of_fan_twoCell (q : ℕ)
    (hP : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
      ∀ (m : ℕ) (C : Finset W) (f : Fin m → W), IsOddCycle G C →
      ∃ i j : Fin m, ∃ b c : Bool, (fanCell G C f i b).card + (fanCell G C f j c).card ≤ q ∧
        HitsOddCycles G (fanCell G C f i b ∪ fanCell G C f j c)) :
    ∀ k, Erdős73.{u} k :=
  erdos73_of_fanErdős73 (fanErdős73_of_fan_twoCell q hP)

/-- **ROUND 73 IS AT LEAST AS STRONG AS ROUND 72 ALONG THE SINGLE-CELL AXIS.**  The hypothesis of
`JSP90.erdos73On_of_fan_singleClassTwo` — two *single* classes forming a transversal of bounded size —
is the case `b = c = 0` of the two-cell axis, so the new instance covers it; the point of stating it
is that the two-cell version is not a restatement but a strictly larger class of graphs. -/
theorem erdos73On_of_fan_twoCell_of_singleClass (q : ℕ)
    (hP : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
      ∀ (m : ℕ) (C : Finset W) (f : Fin m → W), IsOddCycle G C →
      ∃ i j : Fin m, (singleClass G C f i).card + (singleClass G C f j).card ≤ q ∧
        HitsOddCycles G (singleClass G C f i ∪ singleClass G C f j))
    (k : ℕ) : Erdős73On.{u} k (fanBound (fun _ => q) k) := by
  refine erdos73On_of_fan_twoCell q (fun k W instW G hG hG3 m C f hC => ?_) k
  obtain ⟨i, j, hcard, hhits⟩ := hP k W instW G hG hG3 m C f hC
  exact ⟨i, j, false, false, hcard, hhits⟩

/-- **AND AT LEAST AS STRONG ALONG THE MIXED AXIS**: the single/double pair of round 72's successor
`JSP90.exists_fanTransversal_le_card_single_double` is the case `b = 0`, `c = 1`. -/
theorem erdos73On_of_fan_twoCell_of_single_double (q : ℕ)
    (hP : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
      ∀ (m : ℕ) (C : Finset W) (f : Fin m → W), IsOddCycle G C →
      ∃ i j : Fin m, (singleClass G C f i).card + (doubleClass G C f j).card ≤ q ∧
        HitsOddCycles G (singleClass G C f i ∪ doubleClass G C f j))
    (k : ℕ) : Erdős73On.{u} k (fanBound (fun _ => q) k) := by
  refine erdos73On_of_fan_twoCell q (fun k W instW G hG hG3 m C f hC => ?_) k
  obtain ⟨i, j, hcard, hhits⟩ := hP k W instW G hG hG3 m C f hC
  exact ⟨i, j, false, true, hcard, hhits⟩

end Instance


/-! ## Part 4 — the critical-cycle counting in the book, with the constant `c * (k - 1)`

This is the concrete next lemma named in `discovery/JSP-000090/policy.json` after round 72, and it
is where the constant of the fan statement comes from.  Everything here is the machinery of
`JSPProblem/Critical.lean` *restricted to the odd cycles contained in the boundary of one odd
cycle*; the payoff is that the packing bound available is `k - 1` rather than `k`, because a family
of odd cycles inside the fan is disjoint from `C` (round 69,
`JSP90.oddCycleFamily_card_le_of_boundary`). -/

section FanCritical

/-- **A TRANSVERSAL OF THE ODD CYCLES *INSIDE* THE FAN**: `X` meets every odd cycle of `G` contained
in `boundary G C`.  This is the object the fan statement is about, and it is what
`JSP90.FanErdős73` needs: the odd cycles of `G` that meet `∂C` include these, and the statement is
stated for the larger family. -/
noncomputable def HitsFanOddCycles (G : SimpleGraph V) (C X : Finset V) : Prop :=
  ∀ D : Finset V, IsOddCycle G D → D ⊆ boundary G C → D ∩ X ≠ ∅

/-- **A MINIMAL TRANSVERSAL OF THE ODD CYCLES INSIDE THE FAN**: `X` meets every odd cycle contained
in `∂C`, and no proper subset of `X` does.  This is `JSP90.MinimalTransversal` of round 53 with the
family "odd cycles contained in `∂C`" in place of "odd cycles of `G`". -/
noncomputable def MinimalFanTransversal (G : SimpleGraph V) (C X : Finset V) : Prop :=
  HitsFanOddCycles G C X ∧ ∀ Y : Finset V, Y ⊆ X → Y ≠ X → ¬ HitsFanOddCycles G C Y

/-- A minimal transversal of the fan's odd cycles meets every odd cycle of the fan. -/
theorem fanTransversal_hits {X : Finset V} (hX : MinimalFanTransversal G C X) :
    HitsFanOddCycles G C X :=
  hX.1

/-- A subset of a minimal transversal of the fan which is itself such a transversal is the whole
transversal. -/
theorem eq_of_fanTransversal_of_minimal {X Y : Finset V} (hX : MinimalFanTransversal G C X)
    (hYX : Y ⊆ X) (hY : HitsFanOddCycles G C Y) : Y = X := by
  by_cases hne : Y = X
  · exact hne
  · exact absurd hY (hX.2 Y hYX hne)

/-- **A MINIMAL TRANSVERSAL OF THE FAN'S ODD CYCLES EXISTS.**  The finitary argument of round 53
(`JSP90.exists_minimalTransversal_of_transversal`), transported: `boundary G C` itself is a
transversal of the odd cycles inside it, and a minimal one exists because `Finset` is finite. -/
theorem exists_minimalFanTransversal_of_transversal (X₀ : Finset V) (hX₀ : HitsFanOddCycles G C X₀) :
    ∃ X : Finset V, X ⊆ X₀ ∧ MinimalFanTransversal G C X := by
  classical
  have hsne : ((Finset.univ : Finset (Finset V)).filter
      (fun Y : Finset V => Y ⊆ X₀ ∧ HitsFanOddCycles G C Y)).Nonempty := by
    refine Finset.filter_nonempty_iff.mpr
      ⟨X₀, Finset.mem_univ _, Finset.Subset.refl _, hX₀⟩
  obtain ⟨X, hXs, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset V)).filter
      (fun Y : Finset V => Y ⊆ X₀ ∧ HitsFanOddCycles G C Y)) Finset.card hsne
  rw [Finset.mem_filter] at hXs
  obtain ⟨hXsub, hX⟩ := hXs.2
  refine ⟨X, hXsub, hX, fun Y hYX hne hY => ?_⟩
  have hmem : (Y : Finset V)
      ∈ (Finset.univ : Finset (Finset V)).filter
          (fun Z : Finset V => Z ⊆ X₀ ∧ HitsFanOddCycles G C Z) := by
    have hsub2 : Y ⊆ X₀ := fun a ha => hXsub (hYX ha)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hsub2, hY⟩
  have hlt : Y.card < X.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hYX, hne⟩)
  exact absurd hlt (Nat.not_lt.mpr (hmin Y hmem))

/-- **THE BOUNDARY OF AN ODD CYCLE IS A TRANSVERSAL OF THE ODD CYCLES *INSIDE* IT.**  Trivial but
recorded: it is what makes `JSP90.exists_minimalFanTransversal` go through. -/
theorem boundary_hits_fanOddCycles (C : Finset V) : HitsFanOddCycles G C (boundary G C) := by
  intro D hD hsub
  have h3 : 3 ≤ D.card := isOddCycle_card_ge_three hD
  have hDne : D ≠ ∅ := by
    intro hcon
    have hzero : D.card = 0 := Finset.card_eq_zero.mpr hcon
    omega
  obtain ⟨z, hz⟩ := (show D.Nonempty from Finset.nonempty_iff_ne_empty.mpr hDne)
  exact ne_inter_of_mem hz (hsub hz)

/-- **A MINIMAL TRANSVERSAL OF THE FAN'S ODD CYCLES EXISTS**, by the finitary argument of
`JSP90.exists_minimalTransversal_of_transversal`, applied to the transversal
`JSP90.boundary_hits_fanOddCycles`. -/
theorem exists_minimalFanTransversal {C : Finset V} :
    ∃ X : Finset V, MinimalFanTransversal G C X := by
  obtain ⟨X, -, hX⟩ :=
    exists_minimalFanTransversal_of_transversal (X₀ := boundary G C)
      (boundary_hits_fanOddCycles C)
  exact ⟨X, hX⟩

/-- **THE CRITICAL CYCLE OF A VERTEX OF A MINIMAL TRANSVERSAL OF THE FAN.**  If `X` is a minimal
transversal of the odd cycles *inside* `∂C` and `x ∈ X`, then there is an odd cycle `D` of `G`
**contained in `∂C`** meeting `X` in exactly `x`.

This is `JSP90.exists_criticalCycle_of_minimal` of round 53, and the difference is exactly the
point: the critical cycle is a cycle of the *fan*, so it is a candidate for the counting lemmas of
Part 2.  Minimality of `X` says `X \ {x}` is not a transversal of the fan's odd cycles, so some odd
cycle of the fan misses it. -/
theorem exists_criticalFanCycle_of_minimal {X : Finset V} (hX : MinimalFanTransversal G C X) {x : V}
    (hx : x ∈ X) :
    ∃ D : Finset V, IsOddCycle G D ∧ D ⊆ boundary G C ∧ D ∩ X = {x} := by
  have hsub : X \ {x} ⊆ X := Finset.sdiff_subset
  have hne : X \ {x} ≠ X := by
    intro h
    have hx' : x ∈ X \ {x} := by simpa [h] using hx
    rw [Finset.mem_sdiff] at hx'
    exact hx'.2 (Finset.mem_singleton.mpr rfl)
  have hnot : ¬ HitsFanOddCycles G C (X \ {x}) := hX.2 _ hsub hne
  simp only [HitsFanOddCycles, not_forall] at hnot
  obtain ⟨D, hD⟩ := hnot
  push Not at hD
  obtain ⟨hodd, hfan, hmiss⟩ := hD
  refine ⟨D, hodd, hfan, ?_⟩
  have hmiss' : ∀ z : V, z ∈ D → ¬ (z ∈ X \ {x}) := by
    intro z hzD hzX
    exact (Finset.not_nonempty_iff_eq_empty.mpr hmiss) ⟨z, Finset.mem_inter.mpr ⟨hzD, hzX⟩⟩
  have hsubX : ∀ w ∈ D, w ∈ X → w = x := by
    intro w hwD hwX
    have hw' : ¬ (w ∈ X \ {x}) := hmiss' w hwD
    refine Finset.mem_singleton.mp ?_
    by_contra hcon
    exact hw' (Finset.mem_sdiff.mpr ⟨hwX, fun hmem => hcon hmem⟩)
  have hxD : x ∈ D := by
    obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr (hX.1 D hodd hfan)
    have hwx : w = x := hsubX w (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2
    rw [← hwx]
    exact (Finset.mem_inter.mp hw).1
  ext w
  constructor
  · intro hw
    rcases Finset.mem_inter.mp hw with ⟨hCw, hXw⟩
    have hw' : ¬ (w ∈ X \ {x}) := hmiss' w hCw
    refine Finset.mem_singleton.mpr ?_
    by_contra hweq
    exact hw' (Finset.mem_sdiff.mpr ⟨hXw, fun hw2 => hweq (Finset.mem_singleton.mp hw2)⟩)
  · intro hw
    rw [Finset.mem_singleton.mp hw]
    exact Finset.mem_inter.mpr ⟨hxD, hx⟩

/-- **CRITICAL WITNESS DATA FOR THE FAN.**  `d.crit x` is the critical cycle of `x ∈ X`: an odd cycle of
`G` **contained in `∂C`** meeting `X` in exactly `x`, while `d.hits` says `X` meets every odd cycle
of the fan.  The `subBoundary` field is what the counting lemma of Part 4 consumes: it says each
critical cycle is a cycle of the fan, so a family of disjoint critical cycles is a family of odd
cycles *inside* `∂C`. -/
structure FanCriticalTransversal {V : Type*} [Fintype V] (G : SimpleGraph V) (C X : Finset V) where
  /-- the critical cycle of `x` -/
  crit : V → Finset V
  /-- every critical cycle is an odd cycle of `G` -/
  isOdd : ∀ x ∈ X, IsOddCycle G (crit x)
  /-- **every critical cycle is CONTAINED IN THE BOUNDARY** — the new content w.r.t. round 53 -/
  subBoundary : ∀ x ∈ X, (crit x) ⊆ boundary G C
  /-- the critical cycle of `x` meets `X` in exactly `x` -/
  single : ∀ x ∈ X, (crit x) ∩ X = {x}
  /-- `X` meets every odd cycle of the fan -/
  hits : HitsFanOddCycles G C X

/-- **EVERY MINIMAL TRANSVERSAL OF THE FAN CARRIES CRITICAL WITNESS DATA.** -/
theorem exists_criticalFanTransversal_of_minimal {X : Finset V} (hX : MinimalFanTransversal G C X) :
    ∃ d : FanCriticalTransversal G C X, ∀ x ∈ X, IsOddCycle G (d.crit x) := by
  have hall : ∀ x : V, ∃ D : Finset V, x ∉ X ∨
      (IsOddCycle G D ∧ D ⊆ boundary G C ∧ D ∩ X = {x}) := by
    intro x
    by_cases hx : x ∈ X
    · obtain ⟨D, hD, hfan, hDx⟩ := exists_criticalFanCycle_of_minimal hX hx
      exact ⟨D, Or.inr ⟨hD, hfan, hDx⟩⟩
    · exact ⟨∅, Or.inl hx⟩
  let d : FanCriticalTransversal G C X :=
    { crit := fun x => Classical.choose (hall x)
      isOdd := fun x hx => by
        rcases Classical.choose_spec (hall x) with h | ⟨h1, _, _⟩
        · exact absurd h (by simpa using hx)
        · exact h1
      subBoundary := fun x hx => by
        rcases Classical.choose_spec (hall x) with h | ⟨_, h2, _⟩
        · exact absurd h (by simpa using hx)
        · exact h2
      single := fun x hx => by
        rcases Classical.choose_spec (hall x) with h | ⟨_, _, h3⟩
        · exact absurd h (by simpa using hx)
        · exact h3
      hits := hX.1 }
  exact ⟨d, fun x hx => d.isOdd x hx⟩

/-- **THE CRITICAL INTERSECTION GRAPH OF THE FAN**, as in round 53: `x` and `y` are adjacent when both
lie in `X` and their critical cycles meet.  A proper colouring of this graph with `c` colours says
exactly that, inside each colour class, the critical cycles are pairwise vertex-disjoint. -/
def FanIntGraph {V : Type*} [Fintype V] {G : SimpleGraph V} {C X : Finset V}
    (d : FanCriticalTransversal G C X) : SimpleGraph V where
  Adj x y := x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ d.crit x ∩ d.crit y ≠ ∅
  symm := ⟨fun a b h => by
    have h' := h.2.2.2
    rw [Finset.inter_comm] at h'
    exact ⟨h.2.1, h.1, Ne.symm h.2.2.1, h'⟩⟩
  loopless := ⟨fun a h => h.2.2.1 rfl⟩

@[simp]
theorem mem_FanIntGraph {V : Type*} [Fintype V] {G : SimpleGraph V} {C X : Finset V}
    {d : FanCriticalTransversal G C X} {x y : V} :
    (FanIntGraph d).Adj x y ↔ x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ d.crit x ∩ d.crit y ≠ ∅ := Iff.rfl

/-- **INSIDE ONE COLOUR CLASS THE CRITICAL CYCLES ARE PAIRWISE VERTEX-DISJOINT** — the step that turns
a colouring into a packing of odd cycles of the fan. -/
theorem fanDisjoint_of_colour_eq {V : Type*} [Fintype V] {G : SimpleGraph V} {C X : Finset V}
    {d : FanCriticalTransversal G C X} {c : ℕ} {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, (FanIntGraph d).Adj x y → col x ≠ col y) {x y : V} (hne : x ≠ y)
    (hx : x ∈ X) (hy : y ∈ X) (hxy : col x = col y) : d.crit x ∩ d.crit y = ∅ := by
  by_contra hne'
  exact hcol ⟨hx, hy, hne, hne'⟩ hxy

/-- **THE COUNTING LEMMA IN THE BOOK, IN THE PACKING-BOUND FORM: `|X| ≤ c * (k - 1)`.**

`hpack` is the fan packing bound: a family of pairwise vertex-disjoint odd cycles *all contained in
`∂C`* has at most `k - 1` members.  The proof is round 53's `JSP90.card_X_le_of_colouring_pack` with
two changes, both essential:

* the critical cycles of a minimal transversal of the fan are **contained in `∂C`** (field
  `d.subBoundary`), so each colour class gives a packing of odd cycles of the *fan*;
* the bound for such a packing is `k - 1` (`JSP90.oddCycleFamily_card_le_of_boundary` of round 69),
  not `k`. -/
theorem card_fanTransversal_le_of_colouring_pack {X : Finset V} {d : FanCriticalTransversal G C X}
    {c k : ℕ} (hpack : ∀ 𝒟, IsOddCycleFamily (G := G) 𝒟 → (∀ D ∈ 𝒟, D ⊆ boundary G C) →
      𝒟.card ≤ k - 1) {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, (FanIntGraph d).Adj x y → col x ≠ col y) : X.card ≤ c * (k - 1) := by
  classical
  have hsep : ∀ (i : Fin c) (x y : V), x ≠ y → x ∈ X → y ∈ X → col x = i → col y = i →
      d.crit x ∩ d.crit y = ∅ :=
    fun i x y hne hx hy hix hiy => fanDisjoint_of_colour_eq hcol hne hx hy (hix.trans hiy.symm)
  have hle : ∀ i : Fin c, (X.filter (fun x : V => col x = i)).card ≤ k - 1 := by
    intro i
    have hfam : IsOddCycleFamily (G := G) ((X.filter (fun x : V => col x = i)).image d.crit) := by
      constructor
      · intro A hA B hB hAB
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hB
        have hne : x ≠ y := by
          intro h
          apply hAB
          rw [h]
        exact hsep i x y hne (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
          (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
      · intro A hA
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hA
        exact d.isOdd x (Finset.mem_filter.mp hx).1
    have hsub : ∀ A ∈ ((X.filter (fun x : V => col x = i)).image d.crit), A ⊆ boundary G C := by
      intro A hA
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hA
      exact d.subBoundary x (Finset.mem_filter.mp hx).1
    have hinj : Set.InjOn d.crit (X.filter (fun x : V => col x = i)) := by
      intro x hx y hy hxy
      have hxf : x ∈ X.filter (fun x : V => col x = i) := Finset.mem_coe.mp hx
      have hyf : y ∈ X.filter (fun x : V => col x = i) := Finset.mem_coe.mp hy
      have h1 : d.crit y ∩ X = {x} := by
        rw [← hxy]
        exact d.single x (Finset.mem_filter.mp hxf).1
      have h2 : d.crit y ∩ X = {y} := d.single y (Finset.mem_filter.mp hyf).1
      have heq : ({x} : Finset V) = {y} := h1.symm.trans h2
      have hmem : y ∈ ({x} : Finset V) := heq.symm ▸ Finset.mem_singleton_self y
      exact (Finset.mem_singleton.mp hmem).symm
    have hcard : (X.filter (fun x : V => col x = i)).card
        = ((X.filter (fun x : V => col x = i)).image d.crit).card :=
      Finset.card_image_iff.mpr hinj |>.symm
    rw [hcard]
    exact hpack _ hfam hsub
  have hmaps : (X : Set V).MapsTo col (Finset.univ : Finset (Fin c)) := fun _ _ => Finset.mem_univ _
  have hpart : X.card = ∑ b : Fin c, (X.filter (fun x : V => col x = b)).card :=
    Finset.card_eq_sum_card_fiberwise (s := X) (f := col) (t := Finset.univ) hmaps
  have hsum : ∑ b : Fin c, (X.filter (fun x : V => col x = b)).card ≤ ∑ _b : Fin c, (k - 1) :=
    Finset.sum_le_sum fun b _ => hle b
  calc X.card = ∑ b : Fin c, (X.filter (fun x : V => col x = b)).card := hpart
    _ ≤ ∑ _b : Fin c, (k - 1) := hsum
    _ = c * (k - 1) := by simp [Nat.mul_sub_left_distrib]

/-- **THE COUNTING LEMMA IN THE BOOK, UNDER ERDŐS'S HYPOTHESIS: `|X| ≤ c * (k - 1)`.**  The
fan packing bound is `JSP90.oddCycleFamily_card_le_of_boundary` of round 69, which is where the
improvement over round 53's `c * k` comes from. -/
theorem card_fanTransversal_le_of_colouring {X : Finset V} {d : FanCriticalTransversal G C X}
    {c k : ℕ} (hG : LocIndep k G) (hC : IsOddCycle G C) {col : V → Fin c}
    (hcol : ∀ ⦃x y : V⦄, (FanIntGraph d).Adj x y → col x ≠ col y) : X.card ≤ c * (k - 1) := by
  refine card_fanTransversal_le_of_colouring_pack (X := X) (d := d) ?_ hcol
  intro 𝒟 hD hsub
  exact oddCycleFamily_card_le_of_boundary hG hC hD hsub

/-- **THE PRIVATE CYCLE OF `z` MEETS AT LEAST THREE OF THE `2m` CELLS OF THE BOOK.**  The critical
cycle of `z` is an odd cycle contained in `∂C` (the field `subBoundary` and
`JSP90.exists_criticalFanCycle_of_minimal`), so by Part 2 it is not contained in the union of any
two cells.  This is the point where the minimal-transversal apparatus and the book meet. -/
theorem criticalFanCycle_hits_three_cells (hG3 : G.CliqueFree 3) {X : Finset V}
    {d : FanCriticalTransversal G C X} {m : ℕ} {f : Fin m → V} {z : V} (hz : z ∈ X) {i j : Fin m}
    {b c : Bool} : ¬ (d.crit z ⊆ fanCell G C f i b ∪ fanCell G C f j c) := by
  intro hsub
  exact not_isOddCycle_of_subset_two_cell hG3 (C := C) (D := d.crit z) (f := f) (i := i) (j := j)
    (b := b) (c := c) (d.isOdd z hz) hsub

/-- **EVERY CRITICAL CYCLE OF A MINIMAL TRANSVERSAL OF THE FAN IS AN ODD CYCLE OF THE FAN, AND IT
IS *NOT* CONTAINED IN ANY TWO CELLS OF THE BOOK** — the two facts the quantitative half of the
half-integral argument consumes, packaged together. -/
theorem criticalFanCycle_structure (hG3 : G.CliqueFree 3) {X : Finset V}
    {d : FanCriticalTransversal G C X} {m : ℕ} {f : Fin m → V} {z : V} (hz : z ∈ X) :
    IsOddCycle G (d.crit z) ∧ (d.crit z) ⊆ boundary G C ∧
      ∀ (i j : Fin m) (b c : Bool), ¬ (d.crit z ⊆ fanCell G C f i b ∪ fanCell G C f j c) := by
  refine ⟨d.isOdd z hz, d.subBoundary z hz, ?_⟩
  intro i j b c hsub
  exact criticalFanCycle_hits_three_cells hG3 (X := X) (d := d) (m := m) (f := f) (z := z) hz
    (i := i) (j := j) (b := b) (c := c) hsub

/-- **THE CRITICAL-CYCLE HYPOTHESIS AT THE FAN.**  For every triangle-free `G` with `LocIndep k G`,
every odd cycle `C` of `G` has a minimal transversal `X` of the odd cycles *contained in* `∂C` such
that

* the critical intersection graph of `X` is `c`-colourable (which is what makes `|X| ≤ c * (k - 1)`,
  by `JSP90.card_fanTransversal_le_of_colouring` and `JSP90.oddCycleFamily_card_le_of_boundary`); and
* `X` meets **every odd cycle of `G` that touches `∂C`** — the "touching" property, i.e. the
  difference between the family the critical cycles live in (contained in `∂C`) and the family
  `JSP90.FanErdős73` asks about (meets `∂C`).

This is round 53's `JSP90.SpreadMinimalTransversal` restricted to the fan of one odd cycle: the
quantifier over all minimal transversals of all odd cycles of `G` is replaced by the much smaller
requirement of one minimal transversal of one fan, and the bound produced is `c * (k - 1)` rather
than `c * k`.  The touching property is *not* automatic — a minimal transversal of the odd cycles
inside `∂C` need not meet an odd cycle that only touches `∂C` from the outside — and it is stated
here explicitly rather than assumed away.  What is left of JSP-000090 after round 73 is exactly
this: bound the chromatic number of the fan critical intersection graph, and cover the touching
cycles. -/
noncomputable def FanCriticalErdős73 (c : ℕ) : Prop :=
  ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
    ∀ C : Finset W, IsOddCycle G C →
      ∃ X : Finset W, MinimalFanTransversal G C X ∧
        ∃ d : FanCriticalTransversal G C X, Nonempty ((FanIntGraph d).Coloring (Fin c)) ∧
          ∀ D : Finset W, IsOddCycle G D → D ∩ boundary G C ≠ ∅ → D ∩ X ≠ ∅

/-- **THE FAN STATEMENT WITH THE EXPLICIT CONSTANT `f k = c * (k - 1)`, FROM THE CRITICAL-CYCLE
HYPOTHESIS AT THE FAN.**  The two conjuncts of the hypothesis are consumed one by one: the
colouring gives the cardinality bound `c * (k - 1)`, the touching property gives the hitting
property. -/
theorem fanErdős73_of_fanCritical {c : ℕ} (h : FanCriticalErdős73.{u} c) :
    FanErdős73.{u} (fun k => c * (k - 1)) := by
  intro k W instW G hG hG3 C hC
  obtain ⟨X, hX, d, ⟨col, hcol⟩, htouch⟩ := h k W instW G hG hG3 C hC
  have hcol' : ∀ ⦃x y : W⦄, (FanIntGraph d).Adj x y → col x ≠ col y := fun _ _ h => by
    simpa using hcol h
  exact ⟨X, card_fanTransversal_le_of_colouring hG hC (d := d) (c := c) (col := col) hcol', htouch⟩

/-- **ERDŐS PROBLEM #73, WITH THE EXPLICIT CONSTANT `fanBound (fun _ => c * (k - 1)) k`, FROM THE
CRITICAL-CYCLE HYPOTHESIS AT THE FAN.** -/
theorem erdos73On_of_fanCritical {c : ℕ} (h : FanCriticalErdős73.{u} c) (k : ℕ) :
    Erdős73On.{u} k (fanBound (fun j => c * (j - 1)) k) := by
  show ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G →
    CloseToBipartite (fanBound (fun j => c * (j - 1)) k) G
  exact erdos73On_of_fanErdős73 (f := fun j => c * (j - 1)) (fanErdős73_of_fanCritical h) k

/-- **ERDŐS PROBLEM #73 IN FULL FROM THE CRITICAL-CYCLE HYPOTHESIS AT THE FAN.** -/
theorem erdos73_of_fanCritical {c : ℕ} (h : FanCriticalErdős73.{u} c) :
    ∀ k, Erdős73.{u} k :=
  erdos73_of_fanErdős73 (fanErdős73_of_fanCritical h)

/-- **THE FAN CRITICAL HYPOTHESIS FOR `c = 1`: the private cycles of a minimal transversal of the
fan are pairwise vertex-disjoint, so `|X| ≤ k - 1`.**  The classical shape of the argument, with the
strict improvement over the global `k` of round 53. -/
theorem card_fanTransversal_le_one (hG : LocIndep k G) {X : Finset V}
    {d : FanCriticalTransversal G C X}
    (hC : IsOddCycle G C)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (d.crit x) ∩ d.crit y = ∅) : X.card ≤ k - 1 := by
  have hcol : ∀ ⦃x y : V⦄, (FanIntGraph d).Adj x y → (0 : Fin 1) ≠ (0 : Fin 1) := by
    intro x y h
    obtain ⟨hx, hy, hne, hxy⟩ := h
    exact absurd (hsep x hx y hy hne) hxy
  have h1 := card_fanTransversal_le_of_colouring hG hC (d := d) (c := 1)
    (col := fun _ => (0 : Fin 1)) hcol
  simpa using h1

end FanCritical

end

end JSP90
