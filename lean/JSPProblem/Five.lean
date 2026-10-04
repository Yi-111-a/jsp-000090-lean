import JSPProblem.OneK
import JSPProblem.AttachErase
import JSPProblem.Chord
import JSPProblem.CrossThree
import JSPProblem.HubSharp
import JSPProblem.FiniteSharp

/-!
# JSP-000090, round 148 — `JSPProblem/Five.lean`: **THE FIVE-VERTEX AXIS** — Erdős #73 at `k = 1`
## with the OPTIMAL constant `1`, proved structurally

Attack family 75.  Round 146 built a *computable mirror* of Erdős #73 and closed the in-kernel range
at **three** vertices with `decide`; it could not decide `|V| ≤ 4` or `|V| ≤ 5`, because the kernel
memory of `decide` on `Finset`-quantified graph statements is `≈ 55 MB` per enumerated graph on this
shared machine.  `policy.json` proposed two routes past that barrier, the second being
*structural*: prove the small-order instances by hand, after the reusable small lemma "a graph on at
most four vertices with no triangle is bipartite".

**The measured barrier is not the interesting obstacle: the structural proof is short, and the
lemma the policy named is not needed at all.**  The development already has
`JSP90.isBipartite_of_no_oddCycle` (`JSPProblem/Transversal.lean`), so "a triangle-free graph on at
most four vertices is bipartite" is *not* a colouring problem: on at most four vertices an odd cycle
has odd cardinality `≥ 3`, hence cardinality `3`, hence is a triangle.  Everything below is counting
on vertex sets.

## What is proved

* **Part 1 — the local structure at a triangle.**  `JSP90.exists_not_adj_of_notMem_of_isNClique_three`:
  at `LocIndep 1`, every vertex outside a triangle has a **non-neighbour in it**, i.e. it meets the
  triangle in at most two vertices (`LocIndep 1` on `T ∪ {x}` gives an independent `2`-set of four
  vertices; a triangle holds at most one element of an independent set, so `x` is in it and the
  other element is a non-neighbour of `x`), and
  `JSP90.card_adjIn_le_two_of_isNClique_three`, the `Finset` form.
* **Part 2 — counting in a three-element set.**  `JSP90.card_inter_pos_of_card_two_of_card_two`: two
  `2`-subsets of a `3`-set which differ as finsets meet; `JSP90.exists_mem_T_of_card_le_two`
  (Lemma A1); and `JSP90.card_inter_le_one_and_exists_mem_T` (Lemma A2), which turns that into the
  choice of a point of a three-element set meeting every one of two small subsets and controlling
  their intersection.  All three statements are about finsets; no graph appears in them.
* **Part 3 — the shape of a triangle, and the choice of one vertex.**  `JSP90.AdjIn G x T` is the
  set of neighbours of `x` lying in `T`.  `JSP90.exists_mem_D_shapes` classifies every triangle of a
  graph whose vertex set is a triangle `T` together with at most two further vertices: it is `T`
  itself, two vertices of `T` plus one further vertex, or one vertex of `T` plus both further
  vertices.  `JSP90.exists_mem_T_setup` then chooses the vertex of `T` meeting all the triangles
  (Lemma A2, with the `K₄`-exclusion `JSP90.not_adjIn_eq_card_two_of_locIndep_one` as its only
  graph-theoretic input), and `JSP90.exists_common_mem_triangle_of_card_le_five` concludes:

  > **at `LocIndep 1`, `|V| ≤ 5` and a triangle `T` of `G`, the triangles of `G` have a common
  > vertex, and it lies in `T`.**

* **Part 4 — the instance.**

  > **`JSP90.closeToBipartite_one_of_locIndep_one_card_le_five`: `LocIndep 1 G → |V| ≤ 5 →
  > CloseToBipartite 1 G`** — a **new instance of the headline theorem with the OPTIMAL constant
  > `1`** on the class of graphs on at most five vertices, with no hypothesis beyond Erdős's own (no
  > odd girth, no packing weight, no degree bound, no decomposition).  Its `Erdős73On` form is
  > `JSP90.erdos73On_one_one_of_card_le_five`; it **strictly extends round 146's
  > `erdos73On_one_one_card_le_three`**, which was verified by `decide` at `≈ 2 GB` per instance,
  > and the intermediate `|V| ≤ 4` instance is
  > `JSP90.closeToBipartite_one_of_locIndep_one_card_le_four`.

  The proof: a shortest odd cycle of `G` has `3` or `5` vertices; in the `5`-case it spans `V`, so
  every odd cycle of `G` is the whole vertex set; in the `3`-case it is a triangle and Part 3 gives a
  **single vertex meeting every triangle of `G`**, while every odd cycle of `G` is a triangle.
* **Part 5 — optimality, and the transversal form.**  `JSP90.optimal_smallOrder_five`: the constant
  `1` cannot be lowered — `K₃` is `LocIndep 1` and is not `0`-close to bipartite, so instances at
  five vertices need one vertex.  `JSP90.tauOdd_le_one_of_locIndep_one_card_le_five`: the odd cycle
  transversal number is at most `1`, i.e. the deleted vertex **is** an odd cycle transversal.

## What is *not* proved

The general case.  `f(1) = 2` (`JSP90.Erdős73On 1 2`) is out of reach: that statement is
`JSP90.TraceCoverResidual` of `JSPProblem/TraceComplex.lean`, and behind it
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas).  `jsp_000090_main` is deliberately
**not** declared, so `harness/score.py --strict-prize` keeps reporting
`missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 800000

local instance fiveDecidableEq : DecidableEq V := Classical.decEq V

local instance fiveDecidableAdjRel (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

/-! ## Part 0 — the neighbours of a vertex inside a vertex set, and small `Finset` helpers

`AdjIn G x T` is the one new object of this file: the set of neighbours of `x` lying in `T`, i.e. the
vertices of a triangle `T` to which an outside vertex `x` is adjacent. -/

/-- **`AdjIn G x T` is the set of neighbours of `x` lying in `T`.** -/
def AdjIn (G : SimpleGraph V) (x : V) (T : Finset V) : Finset V := T.filter (fun z => G.Adj x z)

theorem mem_adjIn {x : V} {T : Finset V} {z : V} : z ∈ AdjIn G x T ↔ z ∈ T ∧ G.Adj x z :=
  Finset.mem_filter

theorem subset_adjIn (x : V) (T : Finset V) : AdjIn G x T ⊆ T := Finset.filter_subset _ _

theorem card_adjIn_le (x : V) (T : Finset V) : (AdjIn G x T).card ≤ T.card :=
  Finset.card_le_card (subset_adjIn x T)

theorem adj_of_mem_adjIn {x : V} {T : Finset V} {z : V} (hz : z ∈ AdjIn G x T) : G.Adj x z :=
  (mem_adjIn.mp hz).2

theorem mem_adjIn_of_adj {x : V} {T : Finset V} {z : V} (hz : z ∈ T) (hadj : G.Adj x z) :
    z ∈ AdjIn G x T := mem_adjIn.mpr ⟨hz, hadj⟩

/-- **A nonempty finset of positive cardinality.** -/
theorem nonempty_of_card_pos {s : Finset V} (h : 0 < s.card) : s.Nonempty := Finset.card_pos.mp h

/-- **Every element of `D` either lies in `T` and in `D`, or outside `T` and in `D`.** -/
theorem mem_inter_or_sdiff (D T : Finset V) (z : V) (hzD : z ∈ D) :
    (z ∈ D ∩ T) ∨ (z ∈ D \ T) := by
  by_cases hzT : z ∈ T
  · exact Or.inl (Finset.mem_inter.mpr ⟨hzD, hzT⟩)
  · exact Or.inr (Finset.mem_sdiff.mpr ⟨hzD, hzT⟩)

/-- **The `|univ \ T| ≤ 1` hypothesis forbids two distinct vertices outside `T`.** -/
theorem three_le_card_sdiff_univ_of_two {T : Finset V}
    (hEc : ((Finset.univ : Finset V) \ T).card ≤ 1) {z w : V} (hzT : z ∉ T) (hwT : w ∉ T)
    (hzw : z ≠ w) : False := by
  have h1 : z ∈ ((Finset.univ : Finset V) \ T) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzT⟩
  have h2 : w ∈ ((Finset.univ : Finset V) \ T) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwT⟩
  have hsub : {z, w} ⊆ ((Finset.univ : Finset V) \ T) := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact h1
    · exact h2
  have hle := Finset.card_le_card hsub
  have h2card : ({z, w} : Finset V).card = 2 := Finset.card_eq_two.mpr ⟨z, w, hzw, rfl⟩
  omega

/-- **At most two vertices lie outside a triangle on at most five vertices.** -/
theorem card_sdiff_univ_le_two {T : Finset V} (hT3 : T.card = 3) (hV : Fintype.card V ≤ 5) :
    ((Finset.univ : Finset V) \ T).card ≤ 2 := by
  have h1 := Finset.card_sdiff_of_subset (Finset.subset_univ T)
  have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  omega

/-! ## Part 1 — the local structure at a triangle: a vertex outside it has a non-neighbour in it -/

/-- **AT `LocIndep 1` A VERTEX OUTSIDE A TRIANGLE HAS A NON-NEIGHBOUR IN IT.**

```lean
LocIndep 1 G → G.IsNClique 3 T → x ∉ T → ∃ u ∈ T, ¬ G.Adj x u
```

This is the local structure of the three-sun (`sun3`, `JSPProblem/Sun.lean`) and of every "petal"
configuration of rounds 122–130: outside a triangle, a vertex sees **at most two** of its three
vertices. -/
theorem exists_not_adj_of_notMem_of_isNClique_three (hG : LocIndep 1 G) {T : Finset V}
    (hT : G.IsNClique 3 T) {x : V} (hx : x ∉ T) : ∃ u ∈ T, ¬ G.Adj x u := by
  obtain ⟨_, hTcard⟩ := G.isNClique_iff.mp hT
  have hodd : IsOddCycle G T := isOddCycle_of_isNClique_three hT
  obtain ⟨S, hSsub, hSi, hcard⟩ := hG (insert x T)
  have h4 : (insert x T).card = 4 := by
    rw [Finset.card_insert_of_notMem hx, hTcard]
  have hS2 : 2 ≤ S.card := by omega
  have hxS : x ∈ S := by
    by_contra hn
    have hST : S ⊆ T := by
      intro z hz
      rcases Finset.mem_insert.mp (hSsub hz) with hz' | hz'
      · exact absurd (hz' ▸ hz) hn
      · exact hz'
    have h1 := card_le_one_of_isIndepSet_sub_of_card_C_eq_three hodd hSi hST hTcard
    omega
  obtain ⟨u, huS, hune⟩ := Finset.exists_mem_ne (s := S) (by omega) x
  have huT : u ∈ T := by
    rcases Finset.mem_insert.mp (hSsub huS) with h | h
    · exact absurd h hune
    · exact h
  refine ⟨u, huT, fun hadj => ?_⟩
  exact IsIndepSet.apply' hSi huS hxS hune hadj.symm

/-- **The `Finset` form used in Part 3: the neighbours of `x` in a triangle are at most two.** -/
theorem card_adjIn_le_two_of_isNClique_three (hG : LocIndep 1 G) {T : Finset V}
    (hT : G.IsNClique 3 T) {x : V} (hx : x ∉ T) : (AdjIn G x T).card ≤ 2 := by
  obtain ⟨u, huT, hu⟩ := exists_not_adj_of_notMem_of_isNClique_three hG hT hx
  have hsub : AdjIn G x T ⊆ T \ {u} := by
    intro z hz
    have hzT : z ∈ T := (mem_adjIn.mp hz).1
    have hzne : z ≠ u := fun h => hu (h ▸ (adj_of_mem_adjIn hz))
    refine Finset.mem_sdiff.mpr ⟨hzT, ?_⟩
    rw [Finset.mem_singleton]
    exact hzne
  have hle := Finset.card_le_card hsub
  have h2 : (T \ {u} : Finset V).card = 2 := by
    rw [Finset.card_sdiff_of_subset (by
          intro z hz
          rw [Finset.mem_singleton] at hz
          subst hz
          exact huT),
      Finset.card_singleton, (G.isNClique_iff.mp hT).2]
  omega

/-! ## Part 2 — counting in a three-element set -/

/-- **TWO `2`-SUBSETS OF A `3`-SET WHICH DIFFER AS FINSETS MEET.** -/
theorem card_inter_pos_of_card_two_of_card_two {T A B : Finset V} (hT : T.card = 3)
    (hA : A ⊆ T) (hB : B ⊆ T) (hA2 : A.card = 2) (hB2 : B.card = 2) (hne : A ≠ B) :
    1 ≤ (A ∩ B).card := by
  by_cases h0 : (A ∩ B).card = 0
  · exfalso
    have hempty : A ∩ B = ∅ := Finset.card_eq_zero.mp h0
    have h1 : A ⊆ T \ B := by
      intro z hzA
      have hzB : z ∉ B := by
        intro hzB
        have hmem : z ∈ A ∩ B := Finset.mem_inter.mpr ⟨hzA, hzB⟩
        rw [hempty] at hmem
        simp at hmem
      exact Finset.mem_sdiff.mpr ⟨hA hzA, hzB⟩
    have hle := Finset.card_le_card h1
    rw [Finset.card_sdiff_of_subset hB, hT, hB2] at hle
    omega
  · omega

/-- **LEMMA A1 — the common point of two small subsets of a three-element set.**  There is a point of
`T` lying in each of `A`, `B` which has two elements; nothing is assumed about `A ∩ B`. -/
theorem exists_mem_T_of_card_le_two {T A B : Finset V} (hT : T.card = 3) (hA : A ⊆ T)
    (hA2 : A.card ≤ 2) (hB : B ⊆ T) (hB2 : B.card ≤ 2) :
    ∃ v ∈ T, (A.card = 2 → v ∈ A) ∧ (B.card = 2 → v ∈ B) := by
  by_cases hAc2 : A.card = 2
  · by_cases hBc2 : B.card = 2
    · -- two `2`-subsets of a `3`-set always meet
      by_cases heq : A = B
      · obtain ⟨v, hv⟩ := nonempty_of_card_pos (s := A) (by rw [hAc2]; omega)
        refine ⟨v, hA hv, fun _ => hv, fun _ => ?_⟩
        rw [← heq]
        exact hv
      · have h1 := card_inter_pos_of_card_two_of_card_two hT hA hB hAc2 hBc2 heq
        obtain ⟨v, hv⟩ := nonempty_of_card_pos (s := A ∩ B) (by omega)
        exact ⟨v, hA (Finset.mem_inter.mp hv).1, fun _ => (Finset.mem_inter.mp hv).1,
          fun _ => (Finset.mem_inter.mp hv).2⟩
    · obtain ⟨v, hv⟩ := nonempty_of_card_pos (s := A) (by rw [hAc2]; omega)
      exact ⟨v, hA hv, fun _ => hv, fun h => absurd h hBc2⟩
  · by_cases hBc2 : B.card = 2
    · obtain ⟨v, hv⟩ := nonempty_of_card_pos (s := B) (by rw [hBc2]; omega)
      exact ⟨v, hB hv, fun h => absurd h hAc2, fun _ => hv⟩
    · obtain ⟨v, hv⟩ := nonempty_of_card_pos (s := T) (by rw [hT]; omega)
      exact ⟨v, hv, fun h => absurd h hAc2, fun h => absurd h hBc2⟩

/-- **LEMMA A2 — the common point, with control of the intersection.**  If `A`, `B` are subsets of a
three-element set, each of size at most two, and they are not two presentations of the same
`2`-subset, then they meet in at most one point, and there is a point of `T` lying in both of them
whenever their intersection is nonempty. -/
theorem card_inter_le_one_and_exists_mem_T {T A B : Finset V} (hT : T.card = 3) (hA : A ⊆ T)
    (hA2 : A.card ≤ 2) (hB : B ⊆ T) (hB2 : B.card ≤ 2) (hne : ¬ (A = B ∧ A.card = 2)) :
    (A ∩ B).card ≤ 1 ∧
      ∃ v ∈ T, (A.card = 2 → v ∈ A) ∧ (B.card = 2 → v ∈ B) ∧
        (v ∈ A ∩ B ∨ (A ∩ B).card = 0) := by
  have hinter : (A ∩ B).card ≤ 1 := by
    by_cases hAc2 : A.card = 2
    · by_cases hBc2 : B.card = 2
      · have hne' : A ≠ B := fun he => hne ⟨he, hAc2⟩
        have h1 := card_inter_pos_of_card_two_of_card_two hT hA hB hAc2 hBc2 hne'
        have hle2 : (A ∩ B).card ≤ 2 := by
          have hle' : (A ∩ B).card ≤ A.card :=
            Finset.card_le_card (fun z hz => (Finset.mem_inter.mp hz).1)
          rw [hAc2] at hle'
          exact hle'
        by_contra hcon
        have h2 : (A ∩ B).card = 2 := by omega
        have hEq : A ∩ B = A := Finset.eq_of_subset_of_card_le
          (fun z hz => (Finset.mem_inter.mp hz).1) (by rw [h2, hAc2])
        have hsubAB : A ⊆ B := fun z hz => (Finset.mem_inter.mp (hEq ▸ hz)).2
        have hEq2 : A = B := Finset.eq_of_subset_of_card_le hsubAB (by omega)
        exact hne ⟨hEq2, hAc2⟩
      · have hle : (A ∩ B).card ≤ B.card :=
          Finset.card_le_card (fun z hz => (Finset.mem_inter.mp hz).2)
        omega
    · have hle : (A ∩ B).card ≤ A.card :=
        Finset.card_le_card (fun z hz => (Finset.mem_inter.mp hz).1)
      omega
  refine ⟨hinter, ?_⟩
  by_cases h1 : (A ∩ B).card = 1
  · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h1
    have huAB : u ∈ A ∩ B := by rw [hu]; simp
    have huA : u ∈ A := (Finset.mem_inter.mp huAB).1
    have huB : u ∈ B := (Finset.mem_inter.mp huAB).2
    exact ⟨u, hA huA, fun _ => huA, fun _ => huB, Or.inl huAB⟩
  · have hnot : ¬ (A.card = 2 ∧ B.card = 2) := by
      rintro ⟨hac, hbc⟩
      have hne' : A ≠ B := fun he => hne ⟨he, hac⟩
      have h2 := card_inter_pos_of_card_two_of_card_two hT hA hB hac hbc hne'
      omega
    by_cases hAc2 : A.card = 2
    · have hBne : ¬ B.card = 2 := fun h => hnot ⟨hAc2, h⟩
      obtain ⟨v, hv⟩ := nonempty_of_card_pos (s := A) (by rw [hAc2]; omega)
      exact ⟨v, hA hv, fun _ => hv, fun h => absurd h hBne, Or.inr (by omega)⟩
    · by_cases hBc2 : B.card = 2
      · obtain ⟨v, hv⟩ := nonempty_of_card_pos (s := B) (by rw [hBc2]; omega)
        exact ⟨v, hB hv, fun h => absurd h hAc2, fun _ => hv, Or.inr (by omega)⟩
      · obtain ⟨v, hv⟩ := nonempty_of_card_pos (s := T) (by rw [hT]; omega)
        exact ⟨v, hv, fun h => absurd h hAc2, fun h => absurd h hBc2, Or.inr (by omega)⟩

/-! ## Part 3 — the shape of a triangle in a graph on at most five vertices -/

/-- **THE THREE SHAPES OF A TRIANGLE IN A GRAPH WHOSE VERTEX SET IS A TRIANGLE `T` TOGETHER WITH AT
MOST TWO FURTHER VERTICES.**  Every `3`-clique `D` of such a graph is

* contained in `T` (hence equal to `T`), or
* two vertices `a, b` of `T` together with one further vertex `z`, or
* one vertex `a` of `T` together with two further vertices `z ≠ w`.

No finset equality is reconstructed: the statement carries the elements themselves, which is what
the counting of Part 3 consumes. -/
theorem exists_mem_D_shapes {T D : Finset V} (hT : G.IsNClique 3 T) (hD : G.IsNClique 3 D)
    (hV : Fintype.card V ≤ 5) :
    D ⊆ T ∨
      (∃ z : V, z ∈ D ∧ z ∉ T ∧ ∃ a b : V, a ∈ D ∧ b ∈ D ∧ a ∈ T ∧ b ∈ T ∧ a ≠ b) ∨
      (∃ z w a : V, z ∈ D ∧ w ∈ D ∧ a ∈ D ∧ z ∉ T ∧ w ∉ T ∧ z ≠ w ∧ G.Adj z w ∧ a ∈ T) := by
  obtain ⟨_, hTcard⟩ := G.isNClique_iff.mp hT
  obtain ⟨hclD, hDcard⟩ := G.isNClique_iff.mp hD
  have hEc : ((Finset.univ : Finset V) \ T).card ≤ 2 := card_sdiff_univ_le_two hTcard hV
  have hsub2 : D \ T ⊆ ((Finset.univ : Finset V) \ T) := fun z hz =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, (Finset.mem_sdiff.mp hz).2⟩
  have hlt : (D \ T).card ≤ 2 := le_trans (Finset.card_le_card hsub2) hEc
  have hunion : (D ∩ T) ∪ (D \ T) = D := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact (Finset.mem_inter.mp hz).1
      · exact (Finset.mem_sdiff.mp hz).1
    · intro hz
      exact Finset.mem_union.mpr (mem_inter_or_sdiff D T z hz)
  have hinterEmpty : (D ∩ T) ∩ (D \ T) = ∅ := by
    ext z
    constructor
    · intro hz
      have h1 := Finset.mem_inter.mp hz
      exact absurd ((Finset.mem_inter.mp h1.1).2) ((Finset.mem_sdiff.mp h1.2).2)
    · intro hz
      simp at hz
  have hsum : (D ∩ T).card + (D \ T).card = 3 := by
    have h1 := Finset.card_union_add_card_inter (D ∩ T) (D \ T)
    rw [hunion, hinterEmpty, Finset.card_empty, hDcard] at h1
    omega
  have hcases : (D ∩ T).card = 1 ∨ (D ∩ T).card = 2 ∨ (D ∩ T).card = 3 := by omega
  rcases hcases with hcard | hcard | hcard
  · -- exactly two vertices of `D` lie outside `T`: one vertex of `D` lies in `T`
    have h2c : (D \ T).card = 2 := by omega
    obtain ⟨z, w, hzw, hDzw⟩ := Finset.card_eq_two.mp h2c
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have hzwmem : z ∈ D \ T := by rw [hDzw]; simp
    have hDwmem : w ∈ D \ T := by rw [hDzw]; simp
    have hamem : a ∈ D ∩ T := by rw [ha]; simp
    have hzwadj : G.Adj z w := hclD (Finset.mem_sdiff.mp hzwmem).1
      (Finset.mem_sdiff.mp hDwmem).1 hzw
    refine Or.inr (Or.inr ⟨z, w, a, (Finset.mem_sdiff.mp hzwmem).1,
      (Finset.mem_sdiff.mp hDwmem).1, (Finset.mem_inter.mp hamem).1,
      (Finset.mem_sdiff.mp hzwmem).2, (Finset.mem_sdiff.mp hDwmem).2, hzw, hzwadj,
      (Finset.mem_inter.mp hamem).2⟩)
  · -- exactly one vertex of `D` lies outside `T`: two vertices of `D` lie in `T`
    have h1c : (D \ T).card = 1 := by omega
    obtain ⟨z, hzS⟩ := Finset.card_eq_one.mp h1c
    have hzmem : z ∈ D \ T := by rw [hzS]; simp
    obtain ⟨a, b, hab, hDab⟩ := Finset.card_eq_two.mp hcard
    have habD : a ∈ D := by
      have hmem : a ∈ ({a, b} : Finset V) := by simp
      rw [← hDab] at hmem
      exact (Finset.mem_inter.mp hmem).1
    have hbbD : b ∈ D := by
      have hmem : b ∈ ({a, b} : Finset V) := by simp
      rw [← hDab] at hmem
      exact (Finset.mem_inter.mp hmem).1
    have habT : a ∈ T := by
      have hmem : a ∈ ({a, b} : Finset V) := by simp
      rw [← hDab] at hmem
      exact (Finset.mem_inter.mp hmem).2
    have hbbT : b ∈ T := by
      have hmem : b ∈ ({a, b} : Finset V) := by simp
      rw [← hDab] at hmem
      exact (Finset.mem_inter.mp hmem).2
    refine Or.inr (Or.inl ⟨z, (Finset.mem_sdiff.mp hzmem).1, (Finset.mem_sdiff.mp hzmem).2, a, b,
      habD, hbbD, habT, hbbT, hab⟩)
  · -- all three vertices of `D` lie in `T`, so `D ⊆ T`
    have hzero : (D \ T).card = 0 := by omega
    refine Or.inl fun z hzD => ?_
    rcases mem_inter_or_sdiff D T z hzD with h | h
    · exact (Finset.mem_inter.mp h).2
    · exact absurd hzero (Finset.card_ne_zero_of_mem h)

/-- **THE `K₄` EXCLUSION, IN THE FORM THE CHOICE NEEDS.**  Two distinct vertices outside a triangle,
adjacent to each other, with the same two neighbours in it, would form a `K₄` with it.  This is
`JSP90.not_isNClique_four_of_locIndep_one` written for `AdjIn`. -/
theorem not_adjIn_eq_card_two_of_locIndep_one (hG : LocIndep 1 G) {T : Finset V}
    (hT : G.IsNClique 3 T) {z w : V} (hzT : z ∉ T) (hwT : w ∉ T) (hzw : z ≠ w)
    (hadj : G.Adj z w) : ¬ (AdjIn G z T = AdjIn G w T ∧ (AdjIn G z T).card = 2) := by
  rintro ⟨heq, hcard⟩
  obtain ⟨hcl, _⟩ := G.isNClique_iff.mp hT
  obtain ⟨a, b, hab, hAB⟩ := Finset.card_eq_two.mp hcard
  have haZ : a ∈ AdjIn G z T := by rw [hAB]; simp
  have hbZ : b ∈ AdjIn G z T := by rw [hAB]; simp
  have haT : a ∈ T := (mem_adjIn.mp haZ).1
  have hbT : b ∈ T := (mem_adjIn.mp hbZ).1
  have haz : G.Adj z a := (mem_adjIn.mp haZ).2
  have hbz : G.Adj z b := (mem_adjIn.mp hbZ).2
  have haW : a ∈ AdjIn G w T := by rw [← heq]; exact haZ
  have hbW : b ∈ AdjIn G w T := by rw [← heq]; exact hbZ
  have haw : G.Adj w a := (mem_adjIn.mp haW).2
  have hbw : G.Adj w b := (mem_adjIn.mp hbW).2
  have hab' : G.Adj a b := hcl haT hbT hab
  exact not_isClique_card_four_of_locIndep_one hG hab' haz.symm haw.symm hbz.symm hbw.symm hadj

/-- **THE CHOICE OF THE VERTEX, IN THE FORM THE CLASSIFICATION NEEDS.**  Under the local hypothesis of
Part 1 and the `K₄`-exclusion there is a point `v` of the triangle `T` lying in the neighbour set of
*every* further vertex whose neighbour set in `T` has two elements, and lying in the intersection of
the neighbour sets of two adjacent further vertices whenever that intersection is a single point. -/
theorem exists_mem_T_setup {T : Finset V} (hT3 : T.card = 3)
    (hEc : ((Finset.univ : Finset V) \ T).card ≤ 2)
    (hA : ∀ z : V, z ∉ T → (AdjIn G z T).card ≤ 2)
    (hxy : ∀ z w : V, z ∉ T → w ∉ T → z ≠ w → G.Adj z w →
      ¬ (AdjIn G z T = AdjIn G w T ∧ (AdjIn G z T).card = 2)) :
    ∃ v ∈ T,
      (∀ z : V, z ∉ T → (AdjIn G z T).card = 2 → v ∈ AdjIn G z T) ∧
      (∀ z w : V, z ∉ T → w ∉ T → z ≠ w → G.Adj z w →
        (AdjIn G z T ∩ AdjIn G w T).card ≤ 1 ∧
          (v ∈ AdjIn G z T ∩ AdjIn G w T ∨ (AdjIn G z T ∩ AdjIn G w T).card = 0)) := by
  have hcases : ((Finset.univ : Finset V) \ T).card = 0 ∨ ((Finset.univ : Finset V) \ T).card = 1 ∨
      ((Finset.univ : Finset V) \ T).card = 2 := by omega
  rcases hcases with hE0 | hE1 | hE2
  · -- the vertex set is `T` itself
    obtain ⟨v, hv⟩ := nonempty_of_card_pos (s := T) (by rw [hT3]; omega)
    refine ⟨v, hv, ?_, ?_⟩
    · intro z hz hcard2
      have h1 : z ∈ ((Finset.univ : Finset V) \ T) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
      have hne0 : ((Finset.univ : Finset V) \ T) = ∅ := Finset.card_eq_zero.mp hE0
      have hne : ¬ z ∈ ((Finset.univ : Finset V) \ T) := by rw [hne0]; simp
      exact absurd h1 hne
    · intro z w hz hw hzw hadjz
      exact False.elim (three_le_card_sdiff_univ_of_two (by omega) hz hw hzw)
  · -- one further vertex
    obtain ⟨x, hxE⟩ := Finset.card_eq_one.mp hE1
    have hxmems : x ∈ ({x} : Finset V) := by simp
    have hxmem : x ∈ ((Finset.univ : Finset V) \ T) := hxE.symm ▸ hxmems
    have hxT : x ∉ T := (Finset.mem_sdiff.mp hxmem).2
    obtain ⟨v, hvT, hvAx, _⟩ := exists_mem_T_of_card_le_two hT3 (subset_adjIn x T) (hA x hxT)
      (subset_adjIn x T) (hA x hxT)
    refine ⟨v, hvT, ?_, ?_⟩
    · intro z hz hcard2
      have hzE : z ∈ ((Finset.univ : Finset V) \ T) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
      have hz' : z ∈ ({x} : Finset V) := hxE ▸ hzE
      have hzx : z = x := Finset.mem_singleton.mp hz'
      rw [hzx] at hcard2 ⊢
      exact hvAx hcard2
    · intro z w hz hw hzw hadjz
      exact False.elim (three_le_card_sdiff_univ_of_two (by omega) hz hw hzw)
  · -- two further vertices
    obtain ⟨x, y, hxne, hxyE⟩ := Finset.card_eq_two.mp hE2
    have hxmems : x ∈ ({x, y} : Finset V) := by simp
    have hymems : y ∈ ({x, y} : Finset V) := by simp
    have hxmem : x ∈ ((Finset.univ : Finset V) \ T) := hxyE.symm ▸ hxmems
    have hymem : y ∈ ((Finset.univ : Finset V) \ T) := hxyE.symm ▸ hymems
    have hxT : x ∉ T := (Finset.mem_sdiff.mp hxmem).2
    have hyT : y ∉ T := (Finset.mem_sdiff.mp hymem).2
    have hof (z : V) (hzE : z ∈ ((Finset.univ : Finset V) \ T)) : z = x ∨ z = y := by
      have hz' : z ∈ ({x, y} : Finset V) := hxyE ▸ hzE
      rcases Finset.mem_insert.mp hz' with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    by_cases hadj : G.Adj x y
    · obtain ⟨hinter, v, hvT, hvAx, hvAy, hvint⟩ := card_inter_le_one_and_exists_mem_T hT3
        (subset_adjIn x T) (hA x hxT) (subset_adjIn y T) (hA y hyT)
        (fun h => hxy x y hxT hyT hxne hadj h)
      refine ⟨v, hvT, ?_, ?_⟩
      · intro z hz hcard2
        have hzE : z ∈ ((Finset.univ : Finset V) \ T) :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
        rcases hof z hzE with h | h
        · rw [h] at hcard2 ⊢
          exact hvAx hcard2
        · rw [h] at hcard2 ⊢
          exact hvAy hcard2
      · have hres : (AdjIn G x T ∩ AdjIn G y T).card ≤ 1 ∧
            (v ∈ AdjIn G x T ∩ AdjIn G y T ∨ (AdjIn G x T ∩ AdjIn G y T).card = 0) :=
          ⟨hinter, hvint⟩
        have hres' : (AdjIn G y T ∩ AdjIn G x T).card ≤ 1 ∧
            (v ∈ AdjIn G y T ∩ AdjIn G x T ∨ (AdjIn G y T ∩ AdjIn G x T).card = 0) := by
          constructor
          · rw [← Finset.inter_comm (AdjIn G x T) (AdjIn G y T)]
            exact hinter
          · rcases hvint with hv | hv
            · rw [← Finset.inter_comm (AdjIn G x T) (AdjIn G y T)]
              exact Or.inl hv
            · rw [← Finset.inter_comm (AdjIn G x T) (AdjIn G y T)]
              exact Or.inr hv
        intro z w hz hw hzw hadjz
        have hzE : z ∈ ((Finset.univ : Finset V) \ T) :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
        have hwE : w ∈ ((Finset.univ : Finset V) \ T) :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩
        have hzx' : z = x ∨ z = y := hof z hzE
        have hwy' : w = x ∨ w = y := hof w hwE
        rcases hzx' with hzx' | hzx'
        · rcases hwy' with hwy' | hwy'
          · exact absurd (hzx'.trans hwy'.symm) hzw
          · rw [hzx', hwy']
            exact hres
        · rcases hwy' with hwy' | hwy'
          · rw [hzx', hwy']
            exact hres'
          · exact absurd (hzx'.trans hwy'.symm) hzw
    · obtain ⟨v, hvT, hvAx, hvAy⟩ := exists_mem_T_of_card_le_two hT3 (subset_adjIn x T) (hA x hxT)
        (subset_adjIn y T) (hA y hyT)
      refine ⟨v, hvT, ?_, ?_⟩
      · intro z hz hcard2
        have hzE : z ∈ ((Finset.univ : Finset V) \ T) :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
        rcases hof z hzE with h | h
        · rw [h] at hcard2 ⊢
          exact hvAx hcard2
        · rw [h] at hcard2 ⊢
          exact hvAy hcard2
      · intro z w hz hw hzw hadjz
        have hzE : z ∈ ((Finset.univ : Finset V) \ T) :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩
        have hwE : w ∈ ((Finset.univ : Finset V) \ T) :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩
        have hzx' : z = x ∨ z = y := hof z hzE
        have hwy' : w = x ∨ w = y := hof w hwE
        rcases hzx' with hzx' | hzx'
        · rcases hwy' with hwy' | hwy'
          · exact absurd (hzx'.trans hwy'.symm) hzw
          · exact absurd (hzx' ▸ hwy' ▸ hadjz) hadj
        · rcases hwy' with hwy' | hwy'
          · exact absurd (hzx' ▸ hwy' ▸ hadjz) (fun h => hadj h.symm)
          · exact absurd (hzx'.trans hwy'.symm) hzw

/-- **AT `LocIndep 1`, `|V| ≤ 5` AND A TRIANGLE `T` OF `G`, THE TRIANGLES OF `G` HAVE A COMMON
VERTEX, AND IT LIES IN `T`.**  No bound on the odd girth, the degrees or the packing number is used. -/
theorem exists_common_mem_triangle_of_card_le_five (hG : LocIndep 1 G) {T : Finset V}
    (hT : G.IsNClique 3 T) (hV : Fintype.card V ≤ 5) :
    ∃ v ∈ T, ∀ D : Finset V, G.IsNClique 3 D → v ∈ D := by
  obtain ⟨_, hT3⟩ := G.isNClique_iff.mp hT
  obtain ⟨v, hvT, hv1, hv2⟩ := exists_mem_T_setup hT3 (card_sdiff_univ_le_two hT3 hV)
    (fun z hz => card_adjIn_le_two_of_isNClique_three hG hT hz)
    (fun z w hz hw hzw hadj => not_adjIn_eq_card_two_of_locIndep_one hG hT hz hw hzw hadj)
  refine ⟨v, hvT, ?_⟩
  intro D hD
  obtain ⟨hclD, hDcard⟩ := G.isNClique_iff.mp hD
  rcases exists_mem_D_shapes hT hD hV with hsub | hshape | hshape
  · -- `D ⊆ T`, so `D = T`
    have hDeq : D = T := Finset.eq_of_subset_of_card_le hsub (by rw [hDcard, hT3])
    rw [hDeq]
    exact hvT
  · -- `D` has two vertices in `T` and one outside: the neighbour set of the latter is a `2`-set
    obtain ⟨z, hzD, hzT, a, b, haD, hbD, haT, hbT, hab⟩ := hshape
    have hza : z ≠ a := fun h => hzT (h ▸ haT)
    have hzb : z ≠ b := fun h => hzT (h ▸ hbT)
    have haz : G.Adj z a := hclD hzD haD hza
    have hzb' : G.Adj z b := hclD hzD hbD hzb
    have h3 : ({a, b} : Finset V) ⊆ AdjIn G z T := by
      intro u hu
      rcases Finset.mem_insert.mp hu with hu' | hu'
      · subst hu'
        exact mem_adjIn.mpr ⟨haT, haz⟩
      · have hu'' := Finset.mem_singleton.mp hu'
        subst hu''
        exact mem_adjIn.mpr ⟨hbT, hzb'⟩
    have h2card : ({a, b} : Finset V).card = 2 := Finset.card_eq_two.mpr ⟨a, b, hab, rfl⟩
    have hAz : (AdjIn G z T).card = 2 := by
      have h1 : (AdjIn G z T).card ≤ 2 := card_adjIn_le_two_of_isNClique_three hG hT hzT
      have hle := Finset.card_le_card h3
      omega
    have hvz : v ∈ AdjIn G z T := hv1 z hzT hAz
    have hEq : ({a, b} : Finset V) = AdjIn G z T :=
      Finset.eq_of_subset_of_card_le (s := ({a, b} : Finset V)) (t := AdjIn G z T) h3
        (by rw [hAz, h2card])
    have hvab : v = a ∨ v = b := by
      have hv' := hEq.symm ▸ hvz
      rcases Finset.mem_insert.mp hv' with hv' | hv'
      · exact Or.inl hv'
      · exact Or.inr (Finset.mem_singleton.mp hv')
    rcases hvab with rfl | rfl
    · exact haD
    · exact hbD
  · -- `D` has one vertex in `T` and two outside
    obtain ⟨z, w, a, hzD, hwD, haD, hzT, hwT, hzw, hzwadj, haT⟩ := hshape
    have hza : a ≠ z := fun h => hzT (h ▸ haT)
    have hwa : a ≠ w := fun h => hwT (h ▸ haT)
    have haz : G.Adj a z := hclD haD hzD hza
    have haw : G.Adj a w := hclD haD hwD hwa
    have h1 := hv2 z w hzT hwT hzw hzwadj
    have hazw : a ∈ AdjIn G z T ∩ AdjIn G w T :=
      Finset.mem_inter.mpr ⟨mem_adjIn.mpr ⟨haT, haz.symm⟩, mem_adjIn.mpr ⟨haT, haw.symm⟩⟩
    have hne : (AdjIn G z T ∩ AdjIn G w T).Nonempty := ⟨a, hazw⟩
    have hge1 : 1 ≤ (AdjIn G z T ∩ AdjIn G w T).card := by
      have hpos : 0 < (AdjIn G z T ∩ AdjIn G w T).card := Finset.card_pos.mpr hne
      omega
    have hcard1 : (AdjIn G z T ∩ AdjIn G w T).card = 1 := by omega
    rcases h1.2 with hv | hv
    · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard1
      have hau' : a ∈ ({u} : Finset V) := hu ▸ hazw
      have hau : a = u := Finset.mem_singleton.mp hau'
      subst hau
      have hv' : v ∈ ({a} : Finset V) := hu ▸ hv
      have hva : v = a := Finset.mem_singleton.mp hv'
      rw [hva]
      exact haD
    · omega

/-! ## Part 4 — the instance at five vertices -/

/-- **A COMMON VERTEX OF THE ODD CYCLES WHEN A SHORTEST ODD CYCLE HAS FIVE VERTICES.**  Such a cycle
spans the vertex set (`|V| ≤ 5`), so every odd cycle of `G` has five vertices and is the vertex set
itself. -/
theorem hitsOddCycles_of_card_C_five (hV : Fintype.card V ≤ 5) {C : Finset V}
    (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (hC5 : C.card = 5) :
    ∃ v, HitsOddCycles G {v} := by
  obtain ⟨c, hc⟩ := nonempty_of_card_pos (s := C) (by rw [hC5]; omega)
  refine ⟨c, ?_⟩
  intro D hD
  have hD3 : 3 ≤ D.card := isOddCycle_card_ge_three hD
  have hDeq : D = (Finset.univ : Finset V) :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ D) (by
      have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
      have h1 := hshort D hD
      rw [hC5] at h1
      have h2 : D.card ≤ 5 := by
        have h3 : D.card ≤ (Finset.univ : Finset V).card := Finset.card_le_univ D
        rw [huv] at h3
        exact le_trans h3 hV
      omega)
  refine Finset.nonempty_iff_ne_empty.mp ?_
  exact ⟨c, Finset.mem_inter.mpr ⟨hDeq ▸ Finset.mem_univ c, Finset.mem_singleton.mpr rfl⟩⟩

/-- **A COMMON VERTEX OF THE ODD CYCLES WHEN A SHORTEST ODD CYCLE IS A TRIANGLE.**  An odd cycle of
`G` is a triangle, which Part 3 handles, or a five-cycle, which is the whole vertex set and hence
contains the vertex of Part 3. -/
theorem hitsOddCycles_of_card_C_three (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 5)
    {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (hC3 : C.card = 3) :
    ∃ v, HitsOddCycles G {v} := by
  obtain ⟨v, hvT, hvT3⟩ := exists_common_mem_triangle_of_card_le_five hG
    (isNClique_three_of_isOddCycle hC hC3) hV
  refine ⟨v, ?_⟩
  intro D hD
  have hD3 : 3 ≤ D.card := isOddCycle_card_ge_three hD
  have hDodd : D.card % 2 = 1 := card_mod_two_of_isOddCycle hD
  have hge : 3 ≤ D.card := by
    have h1 := hshort D hD
    rw [hC3] at h1
    omega
  have hle : D.card ≤ 5 := by
    have h3 : D.card ≤ (Finset.univ : Finset V).card := Finset.card_le_univ D
    rw [Finset.card_univ] at h3
    exact le_trans h3 hV
  have hcases : D.card = 3 ∨ D.card = 5 := by omega
  rcases hcases with hD3' | hD5'
  · refine Finset.nonempty_iff_ne_empty.mp ⟨v, ?_⟩
    exact Finset.mem_inter.mpr ⟨hvT3 D (isNClique_three_of_isOddCycle hD hD3'),
      Finset.mem_singleton.mpr rfl⟩
  · have hDeq : D = (Finset.univ : Finset V) :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ D) (by
        have hle : D.card ≤ (Finset.univ : Finset V).card := Finset.card_le_univ D
        have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
        omega)
    refine Finset.nonempty_iff_ne_empty.mp ⟨v, ?_⟩
    exact Finset.mem_inter.mpr ⟨hDeq ▸ Finset.mem_univ v, Finset.mem_singleton.mpr rfl⟩

/-- **AT `LocIndep 1` AND `|V| ≤ 5` THE ODD CYCLES OF `G` HAVE A COMMON VERTEX.**  Either `G` has no
odd cycle at all, or a shortest odd cycle has three or five vertices. -/
theorem hitsOddCycles_of_locIndep_one_card_le_five (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 5)
    (hne : Nonempty V) : ∃ v, HitsOddCycles G {v} := by
  by_cases hodd : ∃ D : Finset V, IsOddCycle G D
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle hodd
    have hC3 : 3 ≤ C.card := isOddCycle_card_ge_three hC
    have hCodd : C.card % 2 = 1 := card_mod_two_of_isOddCycle hC
    have hCle : C.card ≤ 5 := by
      have h3 : C.card ≤ (Finset.univ : Finset V).card := Finset.card_le_univ C
      rw [Finset.card_univ] at h3
      exact le_trans h3 hV
    have hcases : C.card = 3 ∨ C.card = 5 := by omega
    rcases hcases with hC3' | hC5'
    · exact hitsOddCycles_of_card_C_three hG hV hC hshort hC3'
    · exact hitsOddCycles_of_card_C_five hV hC hshort hC5'
  · have v : V := Classical.choice hne
    refine ⟨v, fun D hD => absurd ⟨D, hD⟩ hodd⟩

/-- **ERDŐS #73 AT `k = 1`, `m = 1`, ON GRAPHS WITH AT MOST FIVE VERTICES — A NEW INSTANCE OF THE
HEADLINE THEOREM WITH THE OPTIMAL CONSTANT.**

```lean
LocIndep 1 G → |V| ≤ 5 → CloseToBipartite 1 G
```

The hypothesis is Erdős's own and nothing else: no odd girth, no packing weight, no degree bound, no
bound on the number of branch vertices, no decomposition.  The deleted vertex is exhibited by
`JSP90.hitsOddCycles_of_locIndep_one_card_le_five`. -/
theorem closeToBipartite_one_of_locIndep_one_card_le_five (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 5) : CloseToBipartite 1 G := by
  by_cases hne : Nonempty V
  · obtain ⟨v, hv⟩ := hitsOddCycles_of_locIndep_one_card_le_five hG hV hne
    exact ⟨{v}, by simp, isBipartite_delete_of_hitsOddCycles hv⟩
  · refine ⟨∅, by simp, isBipartite_of_no_oddCycle fun h => ?_⟩
    obtain ⟨D, hD⟩ := h
    obtain ⟨z, -⟩ := nonempty_of_card_pos (s := D) (by
      have := isOddCycle_card_ge_three hD; omega)
    exact absurd ⟨z⟩ hne

/-- **The `|V| ≤ 4` instance, contained in the `|V| ≤ 5` one.** -/
theorem closeToBipartite_one_of_locIndep_one_card_le_four (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 4) : CloseToBipartite 1 G :=
  closeToBipartite_one_of_locIndep_one_card_le_five hG (le_trans hV (by omega))

/-- **The class of Part 4 in the `Erdős73On` shape** (compare
`JSP90.LocIndepOneHasTriangle` of `JSPProblem/OneK.lean`): the statement of Erdős #73 at `k = 1`
restricted to graphs of bounded order. -/
def LocIndepOneSmallOrder.{w} (m n : ℕ) : Prop :=
  ∀ (W : Type w) (_ : Fintype W) (G : SimpleGraph W), Fintype.card W ≤ n → LocIndep 1 G →
    CloseToBipartite m G

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM IN THE `Erdős73On` SHAPE, WITH THE OPTIMAL CONSTANT
`1`, ON GRAPHS OF ORDER AT MOST `5`.**  It strictly extends round 146's
`JSP90.erdos73On_one_one_card_le_three`, which was verified by `decide`. -/
theorem erdos73On_one_one_of_card_le_five : LocIndepOneSmallOrder.{u} 1 5 :=
  fun _ _ G hV hG => closeToBipartite_one_of_locIndep_one_card_le_five hG hV

/-- **The same instance at order `4`.** -/
theorem erdos73On_one_one_of_card_le_four : LocIndepOneSmallOrder.{u} 1 4 :=
  fun _ _ G hV hG => closeToBipartite_one_of_locIndep_one_card_le_four hG hV

/-! ## Part 5 — optimality, and the transversal form -/

/-- **THE CONSTANT `1` OF THE FIVE-VERTEX INSTANCE IS OPTIMAL.**  `K₃` is `LocIndep 1`
(`JSP90.completeGraph_locIndep`) and is not `0`-close to bipartite
(`JSP90.closeToBipartite_iff_completeGraph_add_two`), so no instance of Erdős #73 at `k = 1` on
graphs of order at most five can have constant `0`. -/
theorem optimal_smallOrder_five :
    LocIndep 1 (SimpleGraph.completeGraph (Fin 3)) ∧
      ¬ CloseToBipartite 0 (SimpleGraph.completeGraph (Fin 3)) :=
  optimal_smallOrder 1 (by omega) (by omega)

/-- **NO INSTANCE AT `k = 1` AND CONSTANT `0` HOLDS AT ORDER FIVE.**  The negative form of
`JSP90.erdos73On_one_one_of_card_le_five`. -/
theorem not_erdos73On_one_zero_of_card_le_five : ¬ LocIndepOneSmallOrder.{0} 0 5 := by
  rintro h
  exact (optimal_smallOrder_five).2 (h (Fin 3) inferInstance (SimpleGraph.completeGraph (Fin 3))
    (by simp) (optimal_smallOrder_five).1)

/-- **THE ODD CYCLE TRANSVERSAL NUMBER IS AT MOST `1` AT `LocIndep 1` AND `|V| ≤ 5`.**  So the deleted
vertex of `JSP90.closeToBipartite_one_of_locIndep_one_card_le_five` *is* an odd cycle transversal:
the odd cycles of `G` have a common vertex. -/
theorem tauOdd_le_one_of_locIndep_one_card_le_five (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 5) :
    tauOdd G ≤ 1 :=
  (closeToBipartite_iff_tauOdd_le (G := G) (m := 1)).mp
    (closeToBipartite_one_of_locIndep_one_card_le_five hG hV)

end

end JSP90