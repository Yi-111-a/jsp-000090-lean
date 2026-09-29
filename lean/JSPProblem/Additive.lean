/-
# JSP-000090, round 47 — **strong additivity over anticomplete decompositions**

## What this file is

`JSPProblem/Optimal.lean` (round 46) supplied the composition lemma that was missing from every
earlier round — `closeToBipartite_of_anticover`: the conclusion of Erdős #73 is *additive over an
anticomplete decomposition* of the vertex set.  This file is the eighth attack family and develops
that lemma into an **exact** statement, in both directions, over a whole family of pieces.  It is
the first reduction in this development along the **connectivity** axis (round 43 reduced along the
2-cut axis, and the classical Erdős–Pósa proof restricts to connected — in fact 2-connected —
graphs).

* `isOddCycle_sub_anticover` / `isOddCycle_sub_anticoverIn` — **a cycle never crosses an anticomplete
  split**.  Consecutive vertices of a cycle are adjacent, hence on the same side of the split, and
  the predicate "`x ∈ A`" is preserved by the cyclic successor, so it holds at one vertex of the
  cycle iff it holds at all of them (`mem_all_of_congr`).  This is the structural fact everything
  else rests on: the odd cycles of a graph decompose over an anticomplete family exactly as the
  graph does.
* `closeToBipartite_iff_add_anticover` and `closeToBipartite_of_anticover_restrict` — **exact
  additivity, both directions**.  The budget `m₁ + m₂` works for `G` **iff** it splits between the
  two sides of an anticomplete split, and a budget for `G` restricts to *both* sides.  So the odd
  cycle transversal number of `G` lies between `max(m₁, m₂)` and `m₁ + m₂` for the two sides: the
  difficulty of a graph is attained on, and created by, the pieces of every anticomplete split
  (`not_closeToBipartite_of_anticover_left` is the "hard side ⇒ hard graph" form).
* `AnticoverFamily` and `closeToBipartite_of_anticoverFamily_cost` — **strong additivity over a
  family of pieces**: if a family of pairwise disjoint, pairwise anticomplete pieces, each carrying
  an odd cycle, has each piece `X` costing `c X` vertices, then the graph induced on their union
  costs `∑ X ∈ 𝒬, c X`.  This is the anticomplete analogue of round 43's
  `erdos73On_of_split_of_bounded_pieces` with **no `+ 2`** (the 2-cut version has to pay for the two
  shared cut vertices) and, with the counting lemma, **no dependence on the number of pieces**.
* `card_le_of_pieces`, `card_nonBipartiteParts_le`, `card_nonBipartiteParts_le'` and
  `card_nonBipartiteParts_le_cover` — the **counting lemma**: under `LocIndep k G`, at most `k`
  members of a family of pieces (or of an anticomplete cover of the vertices) induce a non-bipartite
  graph.  Each such piece carries an odd cycle, and one odd cycle per piece is a packing because the
  pieces are disjoint.
* `AnticoverCoverFamily`, `isOddCycle_sub_anticoverCover`, `AnticoverDecomposition` — a cover of
  the vertices by pairwise anticomplete pieces (no odd-cycle condition), and the odd cycles of the
  covered set lie in single pieces.  A *decomposition* additionally says that no edge joins a piece
  to a vertex outside the union — the property the families of connected components have, and the
  one that makes the union and its complement an `Anticover`.
* **`erdos73On_of_anticover_decomposition` — A NEW INSTANCE OF THE HEADLINE THEOREM.**  If the
  vertices of `G` are partitioned into pairwise anticomplete pieces (the shape of the connected
  components) and every *non-bipartite* piece is `m`-close to bipartite, then `LocIndep k G` forces
  `CloseToBipartite (k * m) G`: a constant independent of the number of pieces, with no bound on
  the odd girth, on the packing weight or on the number of branch vertices.  The proof is the three
  counting/additivity lemmas above: the non-bipartite pieces are a family of pieces costing `m`
  each, at most `k` of them, the rest of the graph is bipartite because every odd cycle of it lies
  in a piece, and the two halves are added by `closeToBipartite_of_anticover`.

## Relation to the blocker

`jsp_000090_main` is still not proved; the missing statement remains
`JSP90.OddCycleErdosPosa r` for arbitrary `r` (Erdős–Pósa for odd cycles, Reed–Robertson–Seymour–
Thomas 2002).  What this file adds is (a) the *exact* additivity of the conclusion over anticomplete
decompositions, in both directions, (b) the counting lemma which makes the constant independent of
the number of pieces, and (c) a new instance of the headline theorem for every graph whose vertex
set splits into anticomplete pieces.  The next step it makes possible is explicit: instantiate
(c) with the family of **connected components** of `G` — a connected graph is irreducible (any
anticomplete split of a connected graph has a bipartite side), so the hypothesis needed is exactly
"every *connected* `LocIndep k` graph which is `m`-close-to-bipartite-irreducible is `m`-close",
i.e. the classical reduction of Erdős–Pósa to connected (then 2-connected, then 3-connected)
graphs, at the price of one factor `k`.

## A negative result found on the way (worth recording)

A *cover* by pairwise anticomplete pieces is **not** enough for the composition argument: a cover
says nothing about the edges from a piece to the vertices outside the union, so the union and its
complement need not be an `Anticover` and the odd cycle transversal number need not be the sum of
the piece numbers.  This is why `AnticoverDecomposition` (not `AnticoverCoverFamily`) is the
hypothesis of the instance above.  For the same reason the "maximal family of pieces" does **not**
have its union as a transversal: an odd cycle missing the union generally has edges to the union,
so it cannot be added as a new piece, and maximality carries no information.  The transversal
statement of the development remains `JSPProblem.Transversal.hitsOddCycles_of_maxCardFamily` (a
maximum *packing*, where only disjointness is required).
-/
import JSPProblem.Optimal
import JSPProblem.Chord
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqAdditive : DecidableEq V := Classical.decEq V


/-! ### Part 1 — a cycle never crosses an anticomplete split -/

section NoCross

/-- **`A` and `B` split a vertex set `s` anticompletely**: they are disjoint, they cover `s`, and no
edge of `G` joins them.  `Anticover G A B` of `JSPProblem/Optimal.lean` is
`AnticoverIn G univ A B`, the case in which `s` is the whole vertex set. -/
def AnticoverIn (G : SimpleGraph V) (s A B : Finset V) : Prop :=
  (∀ ⦃x : V⦄, x ∈ A → x ∉ B) ∧ A ∪ B = s ∧ ∀ v ∈ A, ∀ w ∈ B, ¬ G.Adj v w

theorem Anticover.anticoverIn (h : Anticover G A B) :
    AnticoverIn G (Finset.univ : Finset V) A B :=
  ⟨h.1, h.2.1, h.2.2⟩

theorem anticover_of_anticoverIn_univ (h : AnticoverIn G (Finset.univ : Finset V) A B) :
    Anticover G A B := h

/-- A vertex of `s` lies on one of the two sides. -/
theorem mem_union_anticoverIn (h : AnticoverIn G s A B) {x : V} (hx : x ∈ s) : x ∈ A ∪ B :=
  h.2.1 ▸ hx

theorem mem_B_of_not_mem_A_anticoverIn (h : AnticoverIn G s A B) {x : V} (hx : x ∈ s)
    (hnx : x ∉ A) : x ∈ B := (Finset.mem_union.mp (mem_union_anticoverIn h hx)).resolve_left hnx

theorem mem_A_of_not_mem_B_anticoverIn (h : AnticoverIn G s A B) {x : V} (hx : x ∈ s)
    (hnx : x ∉ B) : x ∈ A := (Finset.mem_union.mp (mem_union_anticoverIn h hx)).resolve_right hnx

/-- **A predicate preserved by the cyclic successor is invariant under going around the cycle.** -/
theorem cycSucc_pow_congr {m : ℕ} {P : Fin m → Prop} (hstep : ∀ j : Fin m, P (cycSucc j) ↔ P j)
    (j : Fin m) : ∀ k : ℕ, P ((cycSucc^[k] : Fin m → Fin m) j) = P j := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : P (cycSucc ((cycSucc^[k] : Fin m → Fin m) j)) = P j :=
      propext ((hstep ((cycSucc^[k] : Fin m → Fin m) j)).trans (Iff.of_eq ih))
    rw [cycSucc_succ_pow, h1]

/-- **A cycle is connected: a predicate preserved by the cyclic successor which holds at one vertex
holds at every vertex of the cycle.**  The `m` iterates `cycSucc^[k] j`, `k < m`, are pairwise
distinct, so one of them is the given `i` (`exists_arc`). -/
theorem mem_all_of_congr {m : ℕ} (hm : 0 < m) {P : Fin m → Prop}
    (hstep : ∀ j : Fin m, P (cycSucc j) ↔ P j) {i j : Fin m} (hPi : P i) : P j := by
  by_cases hji : j = i
  · rw [hji]
    exact hPi
  · by_contra hn
    obtain ⟨d, hd0, hdm, hdij⟩ := exists_arc hm hji
    have h1 := cycSucc_pow_congr hstep j d
    rw [hdij] at h1
    exact hn (h1 ▸ hPi)

/-- **Adjacent vertices of `s` lie on the same side of an anticomplete split of `s`.** -/
theorem adjacent_side_anticoverIn (h : AnticoverIn G s A B) {x y : V} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : G.Adj x y) : (x ∈ A ↔ y ∈ A) ∧ (x ∈ B ↔ y ∈ B) := by
  constructor
  · constructor
    · intro hxA
      by_contra hnyA
      exact h.2.2 x hxA y (mem_B_of_not_mem_A_anticoverIn h hy hnyA) hxy
    · intro hyA
      by_contra hnxA
      exact h.2.2 y hyA x (mem_B_of_not_mem_A_anticoverIn h hx hnxA) hxy.symm
  · constructor
    · intro hxB
      by_contra hnyB
      exact h.2.2 y (mem_A_of_not_mem_B_anticoverIn h hy hnyB) x hxB hxy.symm
    · intro hyB
      by_contra hnxB
      exact h.2.2 x (mem_A_of_not_mem_B_anticoverIn h hx hnxB) y hyB hxy

/-- **A cycle never crosses an anticomplete split.**  An odd cycle (in fact *any* cycle) of `G[s]`
whose two sides of an anticomplete split of `s` are `A` and `B` lies entirely in `A` or entirely
in `B`.  This is the structural fact behind the whole file. -/
theorem isOddCycle_sub_anticoverIn {s A B C : Finset V} (h : AnticoverIn G s A B)
    (hC : IsOddCycle (induceFinset G s) C) : C ⊆ A ∨ C ⊆ B := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hstepA : ∀ j : Fin m, (f (cycSucc j) ∈ A) ↔ (f j ∈ A) :=
    fun j => (adjacent_side_anticoverIn h ((induce_adj.mp (hcyc j)).1) ((induce_adj.mp (hcyc j)).2.1)
      (hcyc j).2.2).1.symm
  have hstepB : ∀ j : Fin m, (f (cycSucc j) ∈ B) ↔ (f j ∈ B) :=
    fun j => (adjacent_side_anticoverIn h ((induce_adj.mp (hcyc j)).1) ((induce_adj.mp (hcyc j)).2.1)
      (hcyc j).2.2).2.symm
  have h0 : Fin m := ⟨0, by omega⟩
  by_cases hA0 : f h0 ∈ A
  · refine Or.inl fun x hx => ?_
    obtain ⟨j, hj⟩ := (hCmem x).mp hx
    subst x
    exact mem_all_of_congr (m := m) (P := fun j : Fin m => f j ∈ A) (by omega) hstepA hA0
  · refine Or.inr fun x hx => ?_
    obtain ⟨j, hj⟩ := (hCmem x).mp hx
    subst x
    have hB0 : f h0 ∈ B :=
      mem_B_of_not_mem_A_anticoverIn h ((induce_adj.mp (hcyc h0)).1) hA0
    exact mem_all_of_congr (m := m) (P := fun j : Fin m => f j ∈ B) (by omega) hstepB hB0

/-- An odd cycle of `G` is an odd cycle of the graph induced by all of `V`. -/
theorem isOddCycle_of_induceFinset_univ {C : Finset V} (hC : IsOddCycle G C) :
    IsOddCycle (induceFinset G (Finset.univ : Finset V)) C := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  refine ⟨m, f, hm, hm3, hinj, fun j => ?_, hCmem⟩
  exact ⟨Finset.mem_univ _, Finset.mem_univ _, hcyc j⟩

/-- **A cycle never crosses an anticomplete split of the whole vertex set.** -/
theorem isOddCycle_sub_anticover {A B C : Finset V} (h : Anticover G A B) (hC : IsOddCycle G C) :
    C ⊆ A ∨ C ⊆ B :=
  isOddCycle_sub_anticoverIn h.anticoverIn (isOddCycle_of_induceFinset_univ hC)

end NoCross

/-! ### Part 2 — the two directions of the additivity -/

section Add

/-- **`CloseToBipartite` is monotone in its bound.** -/
theorem closeToBipartite_mono {m m' : ℕ} (h : m ≤ m') (hG : CloseToBipartite m G) :
    CloseToBipartite m' G := by
  obtain ⟨X, hX, hb⟩ := hG
  exact ⟨X, Nat.le_trans hX h, hb⟩

/-- **A bipartite induced subgraph of a bipartite graph is bipartite.** -/
theorem isBipartite_induceFinset_of_isBipartite {s t : Finset V} (h : (induceFinset G s).IsBipartite)
    (ht : t ⊆ s) : (induceFinset G t).IsBipartite := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun {v w} hv => ?_⟩
  exact hc (by
    rw [induce_adj] at hv
    exact ⟨ht hv.1, ht hv.2.1, hv.2.2⟩)

/-- A nonempty finset is not empty. -/
theorem ne_empty_of_nonempty {s : Finset V} (h : s.Nonempty) : s ≠ ∅ := h.ne_empty

/-- **The vertices of an odd cycle of `G[s]` lie in `s`.** -/
theorem isOddCycle_sub_induceFinset {s C : Finset V} (hC : IsOddCycle (induceFinset G s) C) :
    C ⊆ s := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  intro x hx
  obtain ⟨j, hj⟩ := (hCmem x).mp hx
  subst x
  exact (induce_adj.mp (hcyc j)).1

/-- **A transversal restricts to a transversal of each side of an anticomplete split.** -/
theorem hitsOddCycles_iff_anticover {A B X : Finset V} (h : Anticover G A B) :
    HitsOddCycles G X ↔
      HitsOddCycles (induceFinset G A) (X ∩ A) ∧ HitsOddCycles (induceFinset G B) (X ∩ B) := by
  constructor
  · intro hX
    refine ⟨fun C hC => ?_, fun C hC => ?_⟩
    · have hGC : IsOddCycle G C := IsOddCycle.of_induceFinset hC
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr (hX C hGC)
      have hxCX : x ∈ C ∧ x ∈ X := Finset.mem_inter.mp hx
      have hxAX : x ∈ A := isOddCycle_sub_induceFinset hC hxCX.1
      exact Finset.nonempty_iff_ne_empty (s := C ∩ (X ∩ A)).mp
        ⟨x, Finset.mem_inter.mpr ⟨hxCX.1, Finset.mem_inter.mpr ⟨hxCX.2, hxAX⟩⟩⟩
    · have hGC : IsOddCycle G C := IsOddCycle.of_induceFinset hC
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr (hX C hGC)
      have hxCX : x ∈ C ∧ x ∈ X := Finset.mem_inter.mp hx
      have hxBX : x ∈ B := isOddCycle_sub_induceFinset hC hxCX.1
      exact Finset.nonempty_iff_ne_empty (s := C ∩ (X ∩ B)).mp
        ⟨x, Finset.mem_inter.mpr ⟨hxCX.1, Finset.mem_inter.mpr ⟨hxCX.2, hxBX⟩⟩⟩
  · rintro ⟨hA, hB⟩ C hC
    have hne : (C ∩ X).Nonempty := by
      rcases isOddCycle_sub_anticover h hC with hCA | hCB
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr (hA C (hC.induceFinset (s := A) hCA))
        have hxCXCXA : x ∈ C ∧ x ∈ X ∩ A := Finset.mem_inter.mp hx
        have hxXA : x ∈ X ∧ x ∈ A := Finset.mem_inter.mp hxCXCXA.2
        exact ⟨x, Finset.mem_inter.mpr ⟨hxCXCXA.1, hxXA.1⟩⟩
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr (hB C (hC.induceFinset (s := B) hCB))
        have hxCXCXB : x ∈ C ∧ x ∈ X ∩ B := Finset.mem_inter.mp hx
        have hxXB : x ∈ X ∧ x ∈ B := Finset.mem_inter.mp hxCXCXB.2
        exact ⟨x, Finset.mem_inter.mpr ⟨hxCXCXB.1, hxXB.1⟩⟩
    exact Finset.nonempty_iff_ne_empty (s := C ∩ X).mp hne

/-- **The converse direction of `closeToBipartite_of_anticover`: a transversal bound for `G`
restricts to both sides.**  Together with the composition lemma of `JSPProblem/Optimal.lean` this
says that the odd cycle transversal number of `G` is the *sum* of the two of its sides, up to the
resolution of the two bounds. -/
theorem closeToBipartite_of_anticover_restrict {m : ℕ} {A B : Finset V} (h : Anticover G A B)
    (hG : CloseToBipartite m G) :
    CloseToBipartite m (induceFinset G A) ∧ CloseToBipartite m (induceFinset G B) := by
  obtain ⟨X, hX, hXhits⟩ := (closeToBipartite_iff_hitsOddCycles (G := G) (m := m)).mp hG
  have hhits : HitsOddCycles (induceFinset G A) (X ∩ A) ∧ HitsOddCycles (induceFinset G B) (X ∩ B) :=
    (hitsOddCycles_iff_anticover (X := X) h).mp hXhits
  refine ⟨(closeToBipartite_iff_hitsOddCycles (G := induceFinset G A) (m := m)).mpr
      ⟨X ∩ A, ?_, hhits.1⟩,
    (closeToBipartite_iff_hitsOddCycles (G := induceFinset G B) (m := m)).mpr
      ⟨X ∩ B, ?_, hhits.2⟩⟩
  · exact le_trans (Finset.card_le_card (Finset.inter_subset_left : X ∩ A ⊆ X)) hX
  · exact le_trans (Finset.card_le_card (Finset.inter_subset_left : X ∩ B ⊆ X)) hX

/-- **A hard side makes the whole graph hard**: a vertex set which is not `m`-close to bipartite
on one side of an anticomplete split is not `m`-close to bipartite at all.  (This is the
contrapositive of `closeToBipartite_of_anticover_restrict`: the difficulty of a graph is at least
the difficulty of each of the pieces of every anticomplete split.) -/
theorem not_closeToBipartite_of_anticover {m : ℕ} {A B : Finset V} (h : Anticover G A B)
    (hn : ¬ CloseToBipartite m (induceFinset G A) ∧ ¬ CloseToBipartite m (induceFinset G B)) :
    ¬ CloseToBipartite m G := by
  rintro hG
  rcases closeToBipartite_of_anticover_restrict h hG with ⟨h1, h2⟩
  exact hn.1 h1

/-- The one-sided form: a hard left side is enough. -/
theorem not_closeToBipartite_of_anticover_left {m : ℕ} {A B : Finset V} (h : Anticover G A B)
    (hnA : ¬ CloseToBipartite m (induceFinset G A)) : ¬ CloseToBipartite m G :=
  fun hG => hnA ((closeToBipartite_of_anticover_restrict h hG).1)

/-- ... and symmetrically for the right side. -/
theorem not_closeToBipartite_of_anticover_right {m : ℕ} {A B : Finset V} (h : Anticover G A B)
    (hnB : ¬ CloseToBipartite m (induceFinset G B)) : ¬ CloseToBipartite m G :=
  fun hG => hnB ((closeToBipartite_of_anticover_restrict h hG).2)

/-- **Both sides `m`-close ⟹ the whole graph `2 * m`-close** (the equal-constant instance of the
composition lemma of `JSPProblem/Optimal.lean`). -/
theorem closeToBipartite_of_anticover_twice {m : ℕ} {A B : Finset V} (h : Anticover G A B)
    (h1 : CloseToBipartite m (induceFinset G A)) (h2 : CloseToBipartite m (induceFinset G B)) :
    CloseToBipartite (2 * m) G := by
  have h := closeToBipartite_of_anticover h h1 h2
  rwa [← Nat.two_mul] at h

end Add

/-! ### Part 3 — strong additivity over an anticomplete family of pieces -/

section Family

/-- **A family of pieces of `G`**: its members are pairwise vertex-disjoint, pairwise anticomplete
(no edge of `G` joins two different members), and **every member carries an odd cycle** of `G`.
The odd-cycle condition is what makes a family of pieces *relevant* to Erdős #73: a family of
pairwise disjoint pieces carrying odd cycles is a packing of odd cycles, so `LocIndep k` bounds its
cardinality by `k`. -/
def AnticoverFamily (G : SimpleGraph V) (𝒬 : Finset (Finset V)) : Prop :=
  (∀ X ∈ 𝒬, ∀ Y ∈ 𝒬, X ≠ Y → X ∩ Y = ∅) ∧
    (∀ X ∈ 𝒬, ∀ Y ∈ 𝒬, X ≠ Y → ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y) ∧
    (∀ X ∈ 𝒬, ∃ C, IsOddCycle G C ∧ C ⊆ X)

theorem AnticoverFamily.disjoint {𝒬 : Finset (Finset V)} (h : AnticoverFamily G 𝒬)
    {X Y : Finset V} (hX : X ∈ 𝒬) (hY : Y ∈ 𝒬) (hne : X ≠ Y) : X ∩ Y = ∅ :=
  h.1 X hX Y hY hne

theorem AnticoverFamily.anticomplete {𝒬 : Finset (Finset V)} (h : AnticoverFamily G 𝒬)
    {X Y : Finset V} (hX : X ∈ 𝒬) (hY : Y ∈ 𝒬) (hne : X ≠ Y) {x : V} (hx : x ∈ X) {y : V}
    (hy : y ∈ Y) : ¬ G.Adj x y :=
  h.2.1 X hX Y hY hne x hx y hy

theorem AnticoverFamily.oddCycle {𝒬 : Finset (Finset V)} (h : AnticoverFamily G 𝒬)
    {X : Finset V} (hX : X ∈ 𝒬) : ∃ C, IsOddCycle G C ∧ C ⊆ X :=
  h.2.2 X hX

/-- **Every piece splits off anticompletely from the rest of the covered set.**  A member `X` of a
family of pieces which covers `s`, together with the *complement* `s \ X`, is an `AnticoverIn G s`:
the two sides are disjoint, they cover `s`, and no edge of `G` joins them, because every vertex of
`s \ X` lies in another piece, which is anticomplete to `X`. -/
theorem anticoverIn_of_anticoverFamily {𝒬 : Finset (Finset V)} {s X : Finset V}
    (h : AnticoverFamily G 𝒬) (hX : X ∈ 𝒬) (hsub : ∀ Y ∈ 𝒬, Y ⊆ s)
    (hcov : ∀ ⦃x : V⦄, x ∈ s → ∃ Y ∈ 𝒬, x ∈ Y) : AnticoverIn G s X (s \ X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hxA hxB
    exact absurd hxA (Finset.mem_sdiff.mp hxB).2
  · ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hsub X hX hx
      · exact (Finset.mem_sdiff.mp hx).1
    · intro hxs
      by_cases hxX : x ∈ X
      · exact Finset.mem_union.mpr (Or.inl hxX)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxs, hxX⟩))
  · intro v hvA w hwB hAdj
    obtain ⟨Y, hY, hvY⟩ := hcov (Finset.mem_sdiff.mp hwB).1
    have hne : X ≠ Y := by
      rintro rfl
      exact absurd hvY (Finset.mem_sdiff.mp hwB).2
    exact h.2.1 X hX Y hY hne v hvA w hvY hAdj

/-- **Every odd cycle of a graph covered by a family of pieces lies in one of the pieces.**  This
is the "cycles do not cross an anticomplete split" lemma for a family of pieces, and it is what
makes the conclusion of Erdős #73 add up over the family. -/
theorem isOddCycle_sub_anticoverFamily {𝒬 : Finset (Finset V)} {s C : Finset V}
    (h : AnticoverFamily G 𝒬) (hsub : ∀ Y ∈ 𝒬, Y ⊆ s)
    (hcov : ∀ ⦃x : V⦄, x ∈ s → ∃ Y ∈ 𝒬, x ∈ Y) (hC : IsOddCycle (induceFinset G s) C) :
    ∃ X ∈ 𝒬, C ⊆ X := by
  have h3 := isOddCycle_card_ge_three (IsOddCycle.of_induceFinset hC)
  have hCsub : C ⊆ s := isOddCycle_sub_induceFinset hC
  have h3pos : 0 < C.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h3pos
  obtain ⟨X, hX, hxX⟩ := hcov (hCsub hx)
  rcases isOddCycle_sub_anticoverIn (anticoverIn_of_anticoverFamily h hX hsub hcov) hC
    with hCX | hCX
  · exact ⟨X, hX, hCX⟩
  · have hx' := hCX hx
    exact absurd hxX (Finset.mem_sdiff.mp hx').2

/-- **Cardinality of a union is bounded by the sum of the cardinalities of pairwise disjoint
pieces.** -/
theorem card_biUnion_le_sum (𝒬 : Finset (Finset V)) (g : Finset V → Finset V)
    (hdis : ∀ (X : Finset V), X ∈ 𝒬 → ∀ (Y : Finset V), Y ∈ 𝒬 → X ≠ Y →
      ∀ (x : V), x ∈ g X → x ∉ g Y) :
    (𝒬.biUnion g).card ≤ ∑ X ∈ 𝒬, (g X).card := by
  classical
  induction 𝒬 using Finset.induction_on with
  | empty => simp
  | @insert X t hX ih =>
      have hne : ∀ (Y : Finset V), Y ∈ t → X ≠ Y := fun Y hY hXY => by
        subst hXY
        exact hX hY
      have hdis' : ∀ (Y : Finset V), Y ∈ t → ∀ (x : V), x ∈ g X → x ∉ g Y :=
        fun Y hY x hx hx2 => absurd hx2
          (hdis X (Finset.mem_insert_self X t) Y (Finset.mem_insert_of_mem hY) (hne Y hY) x hx)
      have hle : (t.biUnion g).card ≤ ∑ Y ∈ t, (g Y).card :=
        ih fun Y hY Z hZ hYZ x hx hx2 => absurd hx2
          (hdis Y (Finset.mem_insert_of_mem hY) Z (Finset.mem_insert_of_mem hZ) hYZ x hx)
      rw [Finset.biUnion_insert, Finset.sum_insert hX]
      exact Nat.le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left hle _)

/-- The graph induced on the empty set is bipartite. -/
theorem isBipartite_induceFinset_empty : (induceFinset G (∅ : Finset V)).IsBipartite := by
  refine ⟨fun _ => 0, fun {v w} hv => ?_⟩
  rw [induce_adj] at hv
  exact absurd hv.1 (by simp)

/-- **A bound on `G[X]` gives a bound on `G[t]` for `t ⊆ X`.** -/
theorem closeToBipartite_induceFinset_of_sub {m : ℕ} {X t : Finset V} (ht : t ⊆ X)
    (h : CloseToBipartite m (induceFinset G X)) : CloseToBipartite m (induceFinset G t) := by
  obtain ⟨Z, hZ, hb⟩ := h
  rw [deleteFinset_induceFinset] at hb
  refine ⟨Z, hZ, ?_⟩
  rw [deleteFinset_induceFinset]
  exact isBipartite_induceFinset_of_isBipartite hb fun x hx =>
    Finset.mem_sdiff.mpr ⟨ht (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩

/-- **The conclusion adds up over an anticomplete split of a vertex set**: if `s` splits
anticompletely into `A` and `B`, `G[A]` is `m₁`-close and `G[B]` is `m₂`-close, then `G[s]` is
`m₁ + m₂`-close.  For `s = univ` this is `closeToBipartite_of_anticover` of
`JSPProblem/Optimal.lean`, and the transversal argument works verbatim. -/
theorem closeToBipartite_induceFinset_of_anticoverIn {m₁ m₂ : ℕ} {s A B : Finset V}
    (h : AnticoverIn G s A B) (h1 : CloseToBipartite m₁ (induceFinset G A))
    (h2 : CloseToBipartite m₂ (induceFinset G B)) :
    CloseToBipartite (m₁ + m₂) (induceFinset G s) := by
  obtain ⟨X₁, hX₁, hb₁⟩ := h1
  obtain ⟨X₂, hX₂, hb₂⟩ := h2
  obtain ⟨Y₁, hY₁, hb₁'⟩ :=
    (closeToBipartite_iff_hitsOddCycles (G := induceFinset G A) (m := m₁)).mp ⟨X₁, hX₁, hb₁⟩
  obtain ⟨Y₂, hY₂, hb₂'⟩ :=
    (closeToBipartite_iff_hitsOddCycles (G := induceFinset G B) (m := m₂)).mp ⟨X₂, hX₂, hb₂⟩
  refine (closeToBipartite_iff_hitsOddCycles (G := induceFinset G s) (m := m₁ + m₂)).mpr
    ⟨Y₁ ∪ Y₂, le_trans (Finset.card_union_le _ _) (Nat.add_le_add hY₁ hY₂), ?_⟩
  intro C hC
  have hC' : IsOddCycle G C := hC.of_induceFinset
  rcases isOddCycle_sub_anticoverIn h hC with hCA | hCB
  · have hne : C ∩ Y₁ ≠ ∅ := hb₁' C (hC'.induceFinset (s := A) hCA)
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hx' : x ∈ C ∧ x ∈ Y₁ := Finset.mem_inter.mp hx
    exact ne_empty_of_nonempty
      ⟨x, Finset.mem_inter.mpr ⟨hx'.1, Finset.mem_union.mpr (Or.inl hx'.2)⟩⟩
  · have hne : C ∩ Y₂ ≠ ∅ := hb₂' C (hC'.induceFinset (s := B) hCB)
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hx' : x ∈ C ∧ x ∈ Y₂ := Finset.mem_inter.mp hx
    exact ne_empty_of_nonempty
      ⟨x, Finset.mem_inter.mpr ⟨hx'.1, Finset.mem_union.mpr (Or.inr hx'.2)⟩⟩

/-- **STRONG ADDITIVITY OF THE CONCLUSION OVER A FAMILY OF PIECES.**  If `𝒬` is a family of
pairwise disjoint, pairwise anticomplete pieces, each of which costs `c X` vertices to make
bipartite, then the graph induced on the **union** of the pieces costs at most
`∑ X ∈ 𝒬, c X` — the sum over the family.

This is the anticomplete analogue of round 43's `erdos73On_of_split_of_bounded_pieces`, with no
`+ 2` (there the two sides of a 2-cut share the two cut vertices) and, combined with
`card_nonBipartiteParts_le` below, **no dependence on the number of pieces**.  The induction peels
one piece off at a time, using `closeToBipartite_induceFinset_of_anticoverIn`; the reason a piece
peels off anticompletely from the rest is `anticoverIn_of_anticoverFamily`, and the reason an odd
cycle of the union is accounted for once is `isOddCycle_sub_anticoverFamily`. -/
theorem closeToBipartite_of_anticoverFamily_cost {𝒬 : Finset (Finset V)} {c : Finset V → ℕ}
    (h : AnticoverFamily G 𝒬)
    (hm : ∀ (X : Finset V), X ∈ 𝒬 → CloseToBipartite (c X) (induceFinset G X)) :
    CloseToBipartite (∑ X ∈ 𝒬, c X) (induceFinset G (𝒬.biUnion id)) := by
  classical
  induction 𝒬 using Finset.induction_on with
  | empty =>
      rw [Finset.biUnion_empty]
      refine ⟨∅, by simp, ?_⟩
      rw [deleteFinset_induceFinset, Finset.sdiff_self]
      exact isBipartite_induceFinset_empty
  | @insert X 𝒬' hX ih =>
      have hfam' : AnticoverFamily G 𝒬' := by
        refine ⟨fun Y hY Z hZ hne => h.disjoint (Finset.mem_insert_of_mem hY)
            (Finset.mem_insert_of_mem hZ) hne, fun Y hY Z hZ hne x hx y hy => ?_, fun Y hY => ?_⟩
        · exact h.2.1 Y (Finset.mem_insert_of_mem hY) Z (Finset.mem_insert_of_mem hZ) hne x hx y hy
        · obtain ⟨C, hC, hCY⟩ := h.2.2 Y (Finset.mem_insert_of_mem hY)
          exact ⟨C, hC, fun x hx => hCY hx⟩
      have hrest : CloseToBipartite (∑ Y ∈ 𝒬', c Y) (induceFinset G (𝒬'.biUnion id)) :=
        ih hfam' (fun Y hY => hm Y (Finset.mem_insert_of_mem hY))
      have hpiece : CloseToBipartite (c X) (induceFinset G X) :=
        hm X (Finset.mem_insert_self X 𝒬')
      have hsplit : AnticoverIn G ((insert X 𝒬').biUnion id) X (𝒬'.biUnion id) := by
        refine ⟨?_, ?_, ?_⟩
        · intro x hxA hxB
          obtain ⟨Y, hY, hxY⟩ := Finset.mem_biUnion.mp hxB
          have hmem : x ∈ X ∩ Y := Finset.mem_inter.mpr ⟨hxA, hxY⟩
          rw [h.disjoint (Finset.mem_insert_self X 𝒬') (Finset.mem_insert_of_mem hY)
            (fun hXY => hX (hXY ▸ hY))] at hmem
          exact absurd hmem (by simp)
        · rw [Finset.biUnion_insert]
          rfl
        · intro v hvA w hwB
          obtain ⟨Y, hY, hwY⟩ := Finset.mem_biUnion.mp hwB
          have hne : X ≠ Y := fun hXY => hX (hXY ▸ hY)
          exact h.2.1 X (Finset.mem_insert_self X 𝒬') Y (Finset.mem_insert_of_mem hY) hne v hvA w hwY
      have hsum := closeToBipartite_induceFinset_of_anticoverIn hsplit hpiece hrest
      simpa only [Finset.sum_insert hX] using hsum

end Family


/-! ### Part 4 — the counting lemma, and the maximal decomposition -/

section Counting

/-- **THE COUNTING STEP.**  Let `𝒬'` be a family of pairwise disjoint, pairwise anticomplete
pieces of `G`, each carrying an odd cycle of `G`.  Then `𝒬'` is a packing of odd cycles, so under
`LocIndep k G` it has at most `k` members. -/
theorem card_le_of_pieces [Fintype V] {k : ℕ} (hG : LocIndep k G) {𝒬' : Finset (Finset V)}
    (hdis : ∀ (X : Finset V), X ∈ 𝒬' → ∀ (Y : Finset V), Y ∈ 𝒬' → X ≠ Y → X ∩ Y = ∅)
    (hanti : ∀ (X : Finset V), X ∈ 𝒬' → ∀ (Y : Finset V), Y ∈ 𝒬' → X ≠ Y →
      ∀ (x : V), x ∈ X → x ∉ Y)
    (hodd : ∀ (X : Finset V), X ∈ 𝒬' → ∃ C, IsOddCycle (induceFinset G X) C) :
    𝒬'.card ≤ k := by
  classical
  have hmem : ∀ a : ↥𝒬', (a : Finset V) ∈ 𝒬' := fun a => a.property
  have hdis' : ∀ a b : ↥𝒬', (a : Finset V) ≠ (b : Finset V) → (a : Finset V) ∩ (b : Finset V) = ∅ :=
    fun a b hne => hdis (a : Finset V) (hmem a) (b : Finset V) (hmem b) hne
  have hsub' : ∀ a : ↥𝒬', (hodd a (hmem a)).choose ⊆ (a : Finset V) :=
    fun a => isOddCycle_sub_induceFinset (hodd a (hmem a)).choose_spec
  have hInj : ∀ a b : ↥𝒬', (a : Finset V) ≠ (b : Finset V) →
      (hodd a (hmem a)).choose ≠ (hodd b (hmem b)).choose := by
    intro a b hne hab
    have hpos : 0 < (hodd a (hmem a)).choose.card := by
      have h3 := isOddCycle_card_ge_three (hodd a (hmem a)).choose_spec
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    have hxC : x ∈ (hodd a (hmem a)).choose := hx
    have hxA : x ∈ (a : Finset V) := hsub' a hxC
    have hxB : x ∈ (b : Finset V) := hsub' b (hab ▸ hxC)
    exact absurd (Finset.mem_inter.mpr ⟨hxA, hxB⟩) (by rw [hdis' a b hne]; simp)
  have hInj' : Set.InjOn (fun a : ↥𝒬' => (hodd a (hmem a)).choose) (↑(𝒬'.attach) : Set ↥𝒬') := by
    intro a _ b _ hab
    by_cases hne : (a : Finset V) = (b : Finset V)
    · apply Subtype.ext
      exact hne
    · exact absurd hab (hInj a b hne)
  set 𝒬'' : Finset (Finset V) :=
    (𝒬'.attach).image fun a : ↥𝒬' => (hodd a (hmem a)).choose with h𝒬''def
  have hfam : IsOddCycleFamily (G := G) 𝒬'' := by
    refine ⟨?_, ?_⟩
    · intro C hC D hD hne
      obtain ⟨a, ha, hval⟩ := Finset.mem_image.mp hC
      obtain ⟨b, hb, hval'⟩ := Finset.mem_image.mp hD
      have hne' : (a : Finset V) ≠ (b : Finset V) := by
        intro h
        have hab : a = b := Subtype.ext h
        subst hab
        exact hne (hval.symm.trans hval')
      have hmemc := hsub' a
      have hmemD := hsub' b
      rw [hval] at hmemc
      rw [hval'] at hmemD
      refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have hx' : x ∈ C ∧ x ∈ D := Finset.mem_inter.mp hx
      exact absurd (Finset.mem_inter.mpr ⟨hmemc hx'.1, hmemD hx'.2⟩)
        (by rw [hdis' a b hne']; simp)
    · intro C hC
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
      exact (hodd a (hmem a)).choose_spec.of_induceFinset
  have hle := hG.oddCycleFamily_card_le hfam
  rw [h𝒬''def, Finset.card_image_of_injOn hInj', Finset.card_attach] at hle
  exact hle

/-- **THE COUNTING LEMMA.**  Under `LocIndep k G`, at most `k` members of a family of pieces
induce a non-bipartite graph: each such piece carries an odd cycle, and choosing one per piece
gives a packing, because the pieces are pairwise disjoint.  This is the anticomplete analogue of
`JSPProblem.Count.VertexSplit.card_nonBipartiteParts_le`, and it is what makes the constant of
`erdos73On_of_anticover_cover` below independent of the number of pieces. -/
theorem card_nonBipartiteParts_le [Fintype V] {k : ℕ} (hG : LocIndep k G)
    {𝒬 : Finset (Finset V)} (h : AnticoverFamily G 𝒬)
    (𝒬' : Finset (Finset V)) (hsub : 𝒬' ⊆ 𝒬)
    (hnb : ∀ (X : Finset V), X ∈ 𝒬' → ¬ (induceFinset G X).IsBipartite) : 𝒬'.card ≤ k := by
  classical
  refine card_le_of_pieces hG (fun X hX Y hY hne => h.1 X (hsub hX) Y (hsub hY) hne)
    (fun X hX Y hY hne x hx => ?_) ?_
  · have hxy : X ∩ Y = ∅ := h.1 X (hsub hX) Y (hsub hY) hne
    intro hy
    exact absurd (Finset.mem_inter.mpr ⟨hx, hy⟩) (by rw [hxy]; simp)
  · intro X hX
    by_contra hcon
    exact hnb X hX (isBipartite_of_no_oddCycle hcon)

/-- **THE COUNTING LEMMA, in its `filter` form.** -/
theorem card_nonBipartiteParts_le' [Fintype V] {k : ℕ} (hG : LocIndep k G)
    {𝒬 : Finset (Finset V)} (h : AnticoverFamily G 𝒬)
    [DecidablePred fun X => ¬ (induceFinset G X).IsBipartite] :
    (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).card ≤ k := by
  classical
  refine card_nonBipartiteParts_le hG h _ ?_ ?_
  · intro X hX
    exact (Finset.mem_filter.mp hX).1
  · intro X hX
    exact (Finset.mem_filter.mp hX).2

/-! ### Part 5 — a new instance of the headline theorem, and where the difficulty can sit -/

/-- A bipartite graph is `0`-close to bipartite. -/
theorem closeToBipartite_zero_of_isBipartite {X : Finset V} (h : (induceFinset G X).IsBipartite) :
    CloseToBipartite 0 (induceFinset G X) :=
  ⟨∅, Nat.zero_le _, by rw [deleteFinset_empty]; exact h⟩

section Instance

/-- **A cover of the vertices by pairwise disjoint, pairwise anticomplete pieces**, with no
odd-cycle condition (a piece may be bipartite; only the non-bipartite ones will cost anything). -/
def AnticoverCoverFamily (G : SimpleGraph V) (𝒬 : Finset (Finset V)) : Prop :=
  (∀ X ∈ 𝒬, ∀ Y ∈ 𝒬, X ≠ Y → X ∩ Y = ∅) ∧
    (∀ X ∈ 𝒬, ∀ Y ∈ 𝒬, X ≠ Y → ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y)

/-- **Every odd cycle of a graph covered by pieces lies in one of the pieces.** -/
theorem isOddCycle_sub_anticoverCoverFamily {𝒬 : Finset (Finset V)} {s C : Finset V}
    (h : AnticoverCoverFamily G 𝒬) (hsub : ∀ Y ∈ 𝒬, Y ⊆ s)
    (hcov : ∀ ⦃x : V⦄, x ∈ s → ∃ Y ∈ 𝒬, x ∈ Y) (hC : IsOddCycle (induceFinset G s) C) :
    ∃ X ∈ 𝒬, C ⊆ X := by
  have h3 := isOddCycle_card_ge_three (IsOddCycle.of_induceFinset hC)
  have hCsub : C ⊆ s := isOddCycle_sub_induceFinset hC
  have h3pos : 0 < C.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h3pos
  obtain ⟨X, hX, hxX⟩ := hcov (hCsub hx)
  have hsplit : AnticoverIn G s X (s \ X) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y hyA hyB
      exact absurd hyA (Finset.mem_sdiff.mp hyB).2
    · ext y
      constructor
      · intro hy
        rcases Finset.mem_union.mp hy with hy' | hy'
        · exact hsub X hX hy'
        · exact (Finset.mem_sdiff.mp hy').1
      · intro hy
        by_cases hyX : y ∈ X
        · exact Finset.mem_union.mpr (Or.inl hyX)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hy, hyX⟩))
    · intro v hvA w hwB
      obtain ⟨Y, hY, hwY⟩ := hcov (Finset.mem_sdiff.mp hwB).1
      have hwY' : w ∈ Y :=
        ((Finset.mem_inter.mp (Finset.mem_inter.mpr ⟨hwB, hwY⟩)) : w ∈ s \ X ∧ w ∈ Y).2
      have hne : X ≠ Y := by
        intro hXY
        exact absurd hwY' (hXY.symm ▸ (Finset.mem_sdiff.mp hwB).2)
      exact h.2 X hX Y hY hne v hvA w hwY'
  rcases isOddCycle_sub_anticoverIn hsplit hC with hCX | hCX
  · exact ⟨X, hX, hCX⟩
  · have hx' := hCX hx
    exact absurd hxX (Finset.mem_sdiff.mp hx').2

/-- **Every odd cycle of a graph covered by pieces lies in one of the pieces** (no containment
hypothesis needed: the pieces only have to *cover* the vertex set, because the edge out of a piece
joins two different pieces and is therefore excluded). -/
theorem isOddCycle_sub_anticoverCover {𝒬 : Finset (Finset V)} {C : Finset V} (s : Finset V)
    (h : AnticoverCoverFamily G 𝒬) (hcov : ∀ (x : V), x ∈ s → ∃ X ∈ 𝒬, x ∈ X)
    (hC : IsOddCycle G C) (hsub : C ⊆ s) : ∃ X ∈ 𝒬, C ⊆ X := by
  have h3 := isOddCycle_card_ge_three hC
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hCmem⟩ := hC
  have hpos : 0 < C.card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨j0, hj0⟩ := (hCmem x).mp hx
  obtain ⟨X, hX, hxX⟩ := hcov (f j0) (hsub ((hCmem (f j0)).mpr ⟨j0, rfl⟩))
  have hj0X : f j0 ∈ X := hxX
  have hstep : ∀ j : Fin m, (f j ∈ X) ↔ (f (cycSucc j) ∈ X) := by
    intro j
    constructor
    · intro hj
      by_contra hn
      obtain ⟨Y, hY, hnY⟩ := hcov (f (cycSucc j))
        (hsub ((hCmem (f (cycSucc j))).mpr ⟨cycSucc j, rfl⟩))
      have hne : X ≠ Y := by
        intro hXY
        exact absurd (hXY ▸ hnY) hn
      exact absurd (hcyc j) (h.2 X hX Y hY hne (f j) hj (f (cycSucc j)) hnY)
    · intro hj
      by_contra hn
      obtain ⟨Y, hY, hnY⟩ := hcov (f j) (hsub ((hCmem (f j)).mpr ⟨j, rfl⟩))
      have hne : X ≠ Y := by
        intro hXY
        exact absurd (hXY ▸ hnY) hn
      exact absurd (hcyc j).symm (fun hAdj =>
        (h.2 X hX Y hY hne (f (cycSucc j)) hj (f j) hnY) hAdj)
  refine ⟨X, hX, fun y hy => ?_⟩
  obtain ⟨j, hj⟩ := (hCmem y).mp hy
  subst y
  exact mem_all_of_congr (m := m) (P := fun j : Fin m => f j ∈ X) (by omega) (fun j => (hstep j).symm) hj0X

/-- **THE COUNTING LEMMA FOR A COVER**: under `LocIndep k G`, at most `k` pieces of an
anticomplete cover of the vertices induce a non-bipartite graph. -/
theorem card_nonBipartiteParts_le_cover [Fintype V] {k : ℕ} (hG : LocIndep k G)
    {𝒬 : Finset (Finset V)} (h : AnticoverCoverFamily G 𝒬)
    [DecidablePred fun X => ¬ (induceFinset G X).IsBipartite] :
    (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).card ≤ k := by
  classical
  have hdis' : ∀ X ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite),
      ∀ Y ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite), X ≠ Y → X ∩ Y = ∅ := by
    intro X hX Y hY hne
    exact h.1 X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hne
  refine card_le_of_pieces hG hdis' ?_ ?_
  · intro X hX Y hY hne x hx hy
    exact absurd (Finset.mem_inter.mpr ⟨hx, hy⟩) (by rw [hdis' X hX Y hY hne]; simp)
  · intro X hX
    by_contra hcon
    exact (Finset.mem_filter.mp hX).2 (isBipartite_of_no_oddCycle hcon)

/-- **A partition of the vertices into pairwise anticomplete pieces** — the shape of the connected
components: the pieces are pairwise disjoint, pairwise anticomplete, they cover `V`, and no edge
joins a piece to a vertex outside their union.  (The families of `AnticoverCoverFamily` alone need
not have the last property: a cover does not say anything about edges to vertices outside the
union.  The families of connected components do.) -/
def AnticoverDecomposition (G : SimpleGraph V) (𝒬 : Finset (Finset V)) : Prop :=
  AnticoverCoverFamily G 𝒬 ∧
    (∀ (X : Finset V), X ∈ 𝒬 → ∀ (x : V), x ∈ X →
      ∀ (y : V), y ∉ 𝒬.biUnion id → ¬ G.Adj x y)

/-- **NEW INSTANCE OF THE HEADLINE THEOREM: a partition into anticomplete pieces.**  If the vertices
of `G` are partitioned into pairwise anticomplete pieces (the shape of the connected components)
and every *non-bipartite* piece is `m`-close to bipartite, then `LocIndep k G` forces
`CloseToBipartite (k * m) G`.

The constant is **independent of the number of pieces** (by `card_nonBipartiteParts_le_cover`: at
most `k` of them are non-bipartite, the others cost nothing), and no bound is assumed on the odd
girth, on the packing weight or on the number of branch vertices.  The proof is: the non-bipartite
pieces are a family of pieces (`hfam`), their union costs `m` each by
`closeToBipartite_of_anticoverFamily_cost`, the rest of the graph is bipartite because every odd
cycle of it lies in a piece, and the two halves are then added by
`closeToBipartite_of_anticover`. -/
theorem erdos73On_of_anticover_decomposition {k m : ℕ} (hG : LocIndep k G) (𝒬 : Finset (Finset V))
    (h : AnticoverDecomposition G 𝒬) (hcov : ∀ (x : V), ∃ X ∈ 𝒬, x ∈ X)
    (hm : ∀ X ∈ 𝒬, ¬ (induceFinset G X).IsBipartite → CloseToBipartite m (induceFinset G X))
    [DecidablePred fun X => ¬ (induceFinset G X).IsBipartite] :
    CloseToBipartite (k * m) G := by
  classical
  have hcover := h.1
  have hcard : (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).card ≤ k := card_nonBipartiteParts_le_cover hG hcover
  have hdis' : ∀ X ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite), ∀ Y ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite), X ≠ Y → X ∩ Y = ∅ := by
    intro X hX Y hY hne
    exact hcover.1 X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hne
  have hedge' : ∀ X ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite), ∀ Y ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite), X ≠ Y →
      ∀ (x : V), x ∈ X → ∀ (y : V), y ∈ Y → ¬ G.Adj x y := by
    intro X hX Y hY hne x hx y hy
    exact hcover.2 X (Finset.mem_filter.mp hX).1 Y (Finset.mem_filter.mp hY).1 hne x hx y hy
  have hfam : AnticoverFamily G (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite) :=
    ⟨hdis', hedge',
      fun X hX => by
        have hnb : ¬ (induceFinset G X).IsBipartite := (Finset.mem_filter.mp hX).2
        have hex2 : ∃ C, IsOddCycle (induceFinset G X) C := by
          by_contra hcon2
          exact hnb (isBipartite_of_no_oddCycle hcon2)
        obtain ⟨C, hC⟩ := hex2
        exact ⟨C, hC.of_induceFinset, isOddCycle_sub_induceFinset hC⟩⟩
  have hm' : ∀ (X : Finset V), X ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite) → CloseToBipartite m (induceFinset G X) :=
    fun X hX => hm X (Finset.mem_filter.mp hX).1 (Finset.mem_filter.mp hX).2
  have h1 := closeToBipartite_of_anticoverFamily_cost hfam hm'
  have h1' : CloseToBipartite (m * (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).card)
      (induceFinset G ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) := by
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm] at h1
    exact h1
  clear h1
  have hrest : (induceFinset G ((Finset.univ : Finset V) \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id))).IsBipartite := by
    refine isBipartite_of_no_oddCycle ?_
    rintro ⟨C, hC⟩
    have hC' : IsOddCycle G C := hC.of_induceFinset
    have hsubX : ∃ X ∈ 𝒬, C ⊆ X := isOddCycle_sub_anticoverCover
      ((Finset.univ : Finset V) \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id))
      hcover (fun x hx => hcov x) hC'
        (isOddCycle_sub_induceFinset
          (s := (Finset.univ : Finset V) \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) hC)
    obtain ⟨X, hX, hCX⟩ := hsubX
    have hCX' : IsOddCycle (induceFinset G X) C := hC'.induceFinset (s := X) hCX
    have hCsub : C ⊆ (Finset.univ : Finset V) \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id) :=
      isOddCycle_sub_induceFinset
        (s := (Finset.univ : Finset V) \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) hC
    by_cases hXbip : (induceFinset G X).IsBipartite
    · exact absurd ⟨C, hCX'⟩ (JSP90.not_isOddCycle_of_isBipartite hXbip)
    · have hXU : X ⊆ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id) :=
        fun x hx => Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, hXbip⟩, hx⟩
      have h3 := isOddCycle_card_ge_three hCX'
      have hpos : 0 < C.card := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      exact absurd (hXU (hCX hx)) (Finset.mem_sdiff.mp (hCsub hx)).2
  have hAB : Anticover G ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id) (Finset.univ \ ((𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hxA hxB
      exact absurd hxA (Finset.mem_sdiff.mp hxB).2
    · ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    · intro v hvA w hwB hv
      have hvX : ∃ X ∈ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite), v ∈ X :=
        Finset.mem_biUnion.mp hvA
      obtain ⟨X, hX', hvX'⟩ := hvX
      by_cases hwU : w ∈ 𝒬.biUnion id
      · have hwW : ∃ Y ∈ 𝒬, w ∈ Y := Finset.mem_biUnion.mp hwU
        obtain ⟨Y, hY, hwY⟩ := hwW
        have hXU : X ⊆ (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).biUnion id :=
          fun x hx => Finset.mem_biUnion.mpr ⟨X, hX', hx⟩
        have hne : X ≠ Y := by
          intro hXY
          subst hXY
          exact absurd (hXU hwY) (Finset.mem_sdiff.mp hwB).2
        exact absurd hv
          (hcover.2 X (Finset.mem_filter.mp hX').1 Y hY hne v hvX' w hwY)
      · exact absurd hv (h.2 X (Finset.mem_filter.mp hX').1 v hvX' w hwU)
  have h2 := closeToBipartite_of_anticover hAB h1' (closeToBipartite_zero_of_isBipartite hrest)
  have h2' : CloseToBipartite (m * (𝒬.filter fun X => ¬ (induceFinset G X).IsBipartite).card) G := by
    convert h2 using 1 <;> omega
  exact closeToBipartite_mono (m' := k * m)
    (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right m hcard) h2'

end Instance

end Counting

end
end JSP90
