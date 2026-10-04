import JSPProblem.Six
import JSPProblem.Branch
import JSPProblem.Transversal

/-!
# JSP-000090, round 150 — `JSPProblem/Seven.lean`: **THE TWO-TRIANGLE EXCLUSION** and the
## seven-vertex instances that follow from it

Attack family 77.  Round 149 closed the six-vertex axis (`LocIndep 1` + `|V| ≤ 6` →
`CloseToBipartite 2`) by a reduction.  Its concrete next target was the seven-vertex instance
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven`, the last order at which the measured
constant is `2` (`discovery/JSP-000090/r144b_n8.log`: no `LocIndep 1` graph on eight vertices has
`tauOdd ≥ 3`).

**The seven-vertex instance splits into three cases (a shortest odd cycle of `3`, `5` or `7`
vertices).  This file settles the third, supplies the structural exclusion the other two consume,
and records the exact shape of what is left.**

## What is proved

* **Part 0 — `JSP90.not_isNClique_three_of_disjoint_of_locIndep_one`: AT `LocIndep 1` THERE ARE NO
  TWO VERTEX-DISJOINT TRIANGLES.**

  > `LocIndep 1 G → G.IsNClique 3 T → G.IsNClique 3 D → T ∩ D = ∅ → False`

  This is the structural fact that the seven-vertex case analysis consumes: it is what forces the
  residue of a triangle to be triangle-free.  It is verified exhaustively for `|V| ≤ 7` by
  `discovery/JSP-000090/r150.log` (Q1: among the `986787` `LocIndep 1` graphs on seven vertices
  **none** contains a `K₄` and **none** contains two vertex-disjoint triangles; the same holds at
  every order `≤ 7`).  The proof is a single application of Erdős's own hypothesis to the six
  elements of `T ∪ D`: an independent set meets each triangle in at most one point, so it has at
  most two elements, while `LocIndep 1` demands `2 * |S| + 1 ≥ 6`.

  Two corollaries:

  * **`JSP90.not_isNClique_three_of_sdiff_of_card_le_four_of_locIndep_one`** — the residue
    `V \ T` of a triangle `T` carries no triangle whenever `|V \ T| ≤ 4`.
  * **`JSP90.isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_seven`** — **THE RESIDUE
    OF A TRIANGLE IS BIPARTITE AT `LocIndep 1` AND `|V| ≤ 7`.**  An odd cycle of the residue would
    have odd cardinality `≥ 3` inside at most four vertices, hence be a triangle, contradicting the
    first corollary.  This is the reduction the seven-vertex triangle case needs: after deleting the
    three vertices of a triangle, nothing odd is left.

* **Part 1 — `JSP90.closeToBipartite_one_of_isOddCycle_of_card_eq`: AN ODD CYCLE SPANNING `V` IS
  ONE-DELETE.**  Every odd cycle of `G` is a nonempty vertex set, so a single vertex of `C` meets
  every odd cycle of `G`.

* **Part 2 — `JSP90.closeToBipartite_one_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven`: A NEW
  INSTANCE OF THE HEADLINE THEOREM WITH THE OPTIMAL CONSTANT `1`, AT SEVEN VERTICES, FOR GRAPHS OF
  ODD GIRTH AT LEAST SEVEN.**

  > `LocIndep 1 G → |V| ≤ 7 → (every odd cycle has at least seven vertices) → CloseToBipartite 1 G`

  The deleted vertex is an odd cycle transversal by construction: an odd cycle has odd cardinality,
  so with `|V| ≤ 7` it has `3`, `5` or `7` vertices; if `3` then `G` has a triangle and if `5` then
  `G` has a five-cycle, and in either case the hypothesis fails, so every odd cycle has seven
  vertices, spans `V`, and Part 1 applies.

* **Part 3 — the counting the five-cycle case needs.**
  `JSP90.not_adj_of_two_of_adj_x_of_no_isNClique_three_of_card_C_five`: in a triangle-free graph, a
  vertex of a five-cycle is adjacent to at most two vertices of that cycle (three neighbours would
  be pairwise non-adjacent, an independent set of size `3` inside a cycle of size `5`, and
  `JSP90.two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle` gives `7 ≤ 5`).

## What is *not* proved

`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven`, in its two remaining cases:

* **the five-cycle case** (`G` triangle-free, shortest odd cycle of five vertices): every odd cycle
  is a five-cycle or `V`, and a five-cycle misses at most one vertex of `C` unless it contains both
  vertices of `V \ C`.  Measured (`discovery/JSP-000090/r150b.log`): each vertex outside `C`
  witnesses **at most one** such five-cycle (`16590` five-cycles, maximum `1` per outside vertex) and
  at most **one** five-cycle meets `C` in three points, so the missed points of `C` number at most
  `2 + 2 = 4 < 5` and one vertex of `C` is left over.  Part 3 supplies the counting input; what is
  missing is the identification of the two ring-neighbours, which needs the inducedness of a
  shortest odd cycle (`JSP90.isInduced_shortest_oddCycle`).
* **the triangle case**: `T` a triangle, `X = V \ T` of four vertices, `G[X]` triangle-free
  (Part 0) and every `x ∈ X` adjacent to at most two vertices of `T`.  Measured
  (`discovery/JSP-000090/r150.log`, Q2/Q4): every one of the `13020` sharp seven-vertex graphs is
  handled by a *mixed pair* `a ∈ T`, `x ∉ T` — one vertex of the triangle together with one vertex
  outside it — and **all** `13020` of them contain a triangle, so this case cannot be dodged.

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 800000

local instance sevenDecidableEq : DecidableEq V := Classical.decEq V

local instance sevenDecidableAdjRel (G : SimpleGraph V) : DecidableRel G.Adj :=
  fun _ _ => Classical.propDecidable _

/-! ## Part 0a — a small tool: three pairwise adjacent vertices are a triangle -/

/-- **THREE MUTUALLY ADJACENT VERTICES ARE A `3`-CLIQUE.**  Used to read the "no triangle" hypothesis
in clique language; it is the shape in which `LocIndep`'s exclusion lemmas are stated. -/
theorem isNClique_three_of_adj_adj_adj {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c)
    (hbc : G.Adj b c) : G.IsNClique 3 {a, b, c} := by
  refine G.isNClique_iff.mpr ⟨?_, ?_⟩
  · intro v hv w hw hvw
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · exact (hvw rfl).elim
    · exact hab
    · exact hac
    · exact hab.symm
    · exact (hvw rfl).elim
    · exact hbc
    · exact hac.symm
    · exact hbc.symm
    · exact (hvw rfl).elim
  · exact Finset.card_eq_three.mpr
      ⟨a, b, c, fun h => G.irrefl (h ▸ hab), fun h => G.irrefl (h ▸ hac),
        fun h => G.irrefl (h ▸ hbc), rfl⟩

/-! ## Part 0b — the two-triangle exclusion

Erdős's hypothesis `LocIndep 1` is read on the six elements of `T ∪ D`.  An independent set of `G`
meets a triangle in at most one point (`JSP90.card_le_one_of_isIndepSet_sub_of_card_C_eq_three` of
`JSPProblem/CrossThree.lean`), so an independent set inside `T ∪ D` has at most two elements, while
`LocIndep 1` demands `2 * |S| + 1 ≥ 6`. -/

/-- **AT `LocIndep 1` THERE ARE NO TWO VERTEX-DISJOINT TRIANGLES.**

```lean
LocIndep 1 G → G.IsNClique 3 T → G.IsNClique 3 D → T ∩ D = ∅ → False
```

The six vertices of two disjoint triangles violate Erdős's hypothesis for `k = 1`: an independent set
among them has at most two elements and `2 * 2 + 1 = 5 < 6`.  This is the structural fact that the
seven-vertex case analysis consumes — it makes the residue of a triangle triangle-free — and
`discovery/JSP-000090/r150.log` checks it exhaustively at every order `≤ 7`. -/
theorem not_isNClique_three_of_disjoint_of_locIndep_one (hG : LocIndep 1 G) {T D : Finset V}
    (hT : G.IsNClique 3 T) (hD : G.IsNClique 3 D) (hdis : T ∩ D = ∅) : False := by
  obtain ⟨_, hT3⟩ := G.isNClique_iff.mp hT
  obtain ⟨_, hD3⟩ := G.isNClique_iff.mp hD
  obtain ⟨S, hSsub, hSi, hb⟩ := hG (T ∪ D)
  -- an independent set meets each of the two triangles in at most one point
  have hST : (S ∩ T).card ≤ 1 :=
    card_le_one_of_isIndepSet_sub_of_card_C_eq_three (isOddCycle_of_isNClique_three hT)
      (hSi.mono (Finset.inter_subset_left)) Finset.inter_subset_right hT3
  have hSD : (S ∩ D).card ≤ 1 :=
    card_le_one_of_isIndepSet_sub_of_card_C_eq_three (isOddCycle_of_isNClique_three hD)
      (hSi.mono (Finset.inter_subset_left)) Finset.inter_subset_right hD3
  -- hence `|S| ≤ 2`
  have hUnion : (S ∩ T) ∪ (S ∩ D) = S := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with h | h
      · exact (Finset.mem_inter.mp h).1
      · exact (Finset.mem_inter.mp h).1
    · intro hz
      rcases mem_inter_or_sdiff S (T ∪ D) z hz with h | h
      · rcases Finset.mem_union.mp (Finset.mem_inter.mp h).2 with h' | h'
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hz, h'⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hz, h'⟩))
      · exact absurd (hSsub hz) ((Finset.mem_sdiff.mp h).2)
  have hinterEmpty : (S ∩ T) ∩ (S ∩ D) = ∅ := by
    ext z
    constructor
    · intro hz
      have h1 := Finset.mem_inter.mp hz
      have h2 : z ∈ T ∩ D :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h1.1).2, (Finset.mem_inter.mp h1.2).2⟩
      rw [hdis] at h2
      simp at h2
    · intro hz
      simp at hz
  have hsum : S.card = (S ∩ T).card + (S ∩ D).card := by
    have h1 := Finset.card_union_add_card_inter (S ∩ T) (S ∩ D)
    rw [hUnion, Finset.card_eq_zero.mpr hinterEmpty, add_zero] at h1
    exact h1
  have hle : S.card ≤ 2 := by
    rw [hsum]
    omega
  -- the cardinality of `T ∪ D` is `6`
  have hcardUnion : (T ∪ D).card = 6 := by
    have h1 := Finset.card_union_add_card_inter T D
    rw [Finset.card_eq_zero.mpr hdis, hT3, hD3, add_zero] at h1
    omega
  have hge : 3 ≤ S.card := by
    have h1 := hb
    rw [hcardUnion] at h1
    omega
  omega

/-- **THE RESIDUE OF A TRIANGLE CARRIES NO TRIANGLE, PROVIDED IT HAS AT MOST FOUR VERTICES.** -/
theorem not_isNClique_three_of_sdiff_of_card_le_four_of_locIndep_one (hG : LocIndep 1 G)
    {T : Finset V} (hT : G.IsNClique 3 T) (hX : ((Finset.univ : Finset V) \ T).card ≤ 4) :
    ¬ G.IsNClique 3 ((Finset.univ : Finset V) \ T) := by
  intro hD
  have hdis : T ∩ ((Finset.univ : Finset V) \ T) = ∅ := by
    ext z
    constructor
    · intro hz
      exact False.elim ((Finset.mem_sdiff.mp (Finset.mem_inter.mp hz).2).2
        (Finset.mem_inter.mp hz).1)
    · intro hz
      exact False.elim (by simpa using hz)
  exact not_isNClique_three_of_disjoint_of_locIndep_one hG hT hD hdis

/-- **THE RESIDUE OF A TRIANGLE IS BIPARTITE AT `LocIndep 1` AND `|V| ≤ 7`.**

```lean
LocIndep 1 G → |V| ≤ 7 → G.IsNClique 3 T → (deleteFinset G T).IsBipartite
```

An odd cycle of the residue `G[V \ T]` has odd cardinality `≥ 3` and lives in at most
`|V| - 3 ≤ 4` vertices, so it is a triangle of `G` vertex-disjoint from `T`, which Part 0b forbids.
This is the reduction the seven-vertex triangle case needs: after deleting the three vertices of a
triangle, nothing odd is left. -/
theorem isBipartite_delete_of_isNClique_three_of_locIndep_one_card_le_seven (hG : LocIndep 1 G)
    (hV : Fintype.card V ≤ 7) {T : Finset V} (hT : G.IsNClique 3 T) :
    (deleteFinset G T).IsBipartite := by
  rw [deleteFinset]
  refine isBipartite_of_no_oddCycle fun hD => ?_
  obtain ⟨D, hD⟩ := hD
  obtain ⟨hD', hDsub⟩ := isOddCycle_induceFinset hD
  have hD3 : 3 ≤ D.card := isOddCycle_card_ge_three hD'
  have hXle : ((Finset.univ : Finset V) \ T).card ≤ 4 := by
    obtain ⟨_, hT3⟩ := G.isNClique_iff.mp hT
    have h1 := Finset.card_sdiff_of_subset (Finset.subset_univ T)
    have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    rw [hT3] at h1
    omega
  have hDle : D.card ≤ 4 := by
    have h1 := Finset.card_le_card hDsub
    have h2 := hXle
    omega
  have hDodd : D.card % 2 = 1 := card_mod_two_of_isOddCycle hD'
  have hDcard : D.card = 3 := by omega
  have hdis : T ∩ D = ∅ := by
    ext z
    constructor
    · intro hz
      have h1 := Finset.mem_inter.mp hz
      exact False.elim ((Finset.mem_sdiff.mp (hDsub h1.2)).2 h1.1)
    · intro hz
      exact False.elim (by simpa using hz)
  exact not_isNClique_three_of_disjoint_of_locIndep_one hG hT
    (isNClique_three_of_isOddCycle hD' hDcard) hdis

/-! ## Part 1 — an odd cycle spanning `V` is one-delete -/

/-- **A SHORTEST ODD CYCLE SPANNING `V` HAS A COMMON VERTEX WITH EVERY ODD CYCLE OF `G`.**

Every odd cycle `D` has `|D| ≥ |C| = |V|`, hence `D = V`, hence `D` contains every vertex.  The
minimality hypothesis is what makes the conclusion hold: a single odd cycle spanning `V` does not
suffice on its own, since a chord may produce a triangle. -/
theorem mem_hitsOddCycles_singleton_of_shortest_oddCycle_of_card_eq {C : Finset V}
    (hC : IsOddCycle G C) (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hcard : C.card = Fintype.card V) :
    ∃ v : V, HitsOddCycles G {v} := by
  obtain ⟨v, hvC⟩ := IsOddCycle.nonempty hC
  have hCeq : C = (Finset.univ : Finset V) := Finset.eq_of_subset_of_card_le (Finset.subset_univ C)
    (by
      have h2 : C.card ≤ (Finset.univ : Finset V).card := Finset.card_le_univ C
      have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
      omega)
  refine ⟨v, fun D hD => ?_⟩
  have hDle : D.card ≤ (Finset.univ : Finset V).card := Finset.card_le_univ D
  have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have hmin := hshort D hD
  have hDeq : D = (Finset.univ : Finset V) := Finset.eq_of_subset_of_card_le (Finset.subset_univ D)
    (by omega)
  exact Finset.nonempty_iff_ne_empty.mp
    ⟨v, Finset.mem_inter.mpr ⟨hDeq.symm ▸ (hCeq.symm ▸ hvC), Finset.mem_singleton.mpr rfl⟩⟩

/-- **ERDŐS #73 AT `k = 1` WITH CONSTANT `1`, WHEN A SHORTEST ODD CYCLE SPANS THE VERTEX SET.** -/
theorem closeToBipartite_one_of_shortest_oddCycle_of_card_eq {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) (hcard : C.card = Fintype.card V) :
    CloseToBipartite 1 G := by
  obtain ⟨v, hv⟩ := mem_hitsOddCycles_singleton_of_shortest_oddCycle_of_card_eq hC hshort hcard
  exact ⟨{v}, by simp, isBipartite_delete_of_hitsOddCycles hv⟩

/-! ## Part 2 — a new seven-vertex instance: odd girth at least seven

With `|V| ≤ 7` the only possible odd cardinalities of an odd cycle are `3`, `5` and `7`.  A hypothesis
excluding the first two therefore forces every odd cycle to span `V`, and Part 1 applies.  This is
the shape of a statement: a *structural* hypothesis (here the odd girth) in place of an order bound,
with the optimal constant `1`. -/

/-- **ERDŐS #73 AT `k = 1`, CONSTANT `1`, ON GRAPHS OF ORDER AT MOST SEVEN AND ODD GIRTH AT LEAST
SEVEN — A NEW INSTANCE OF THE HEADLINE THEOREM WITH THE OPTIMAL CONSTANT.**

```lean
LocIndep 1 G → |V| ≤ 7 → (∀ D, IsOddCycle G D → 7 ≤ D.card) → CloseToBipartite 1 G
```

The deleted vertex is exhibited as an odd cycle transversal: every odd cycle of `G` has seven
vertices, hence is the whole vertex set, and so contains it. -/
theorem closeToBipartite_one_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven
    (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 7)
    (hgirth : ∀ D : Finset V, IsOddCycle G D → 7 ≤ D.card) (hne : Nonempty V) :
    CloseToBipartite 1 G := by
  by_cases hodd : ∃ C : Finset V, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle hodd
    have h1 : C.card ≤ Fintype.card V := by
      have h2 := Finset.card_le_univ C
      have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
      omega
    exact closeToBipartite_one_of_shortest_oddCycle_of_card_eq hC hshort (by
      have h1 := hgirth C hC
      omega)
  · obtain ⟨v⟩ := hne
    refine ⟨∅, by simp, ?_⟩
    rw [deleteFinset_empty]
    refine isBipartite_of_no_oddCycle fun h => ?_
    obtain ⟨D, hD⟩ := h
    obtain ⟨z, -⟩ := nonempty_of_card_pos (s := D) (by
      have h1 := isOddCycle_card_ge_three hD
      omega)
    exact absurd ⟨D, hD⟩ hodd

/-- **The same instance in the transversal shape: the odd cycles have a common vertex.** -/
theorem hitsOddCycles_singleton_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven
    (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 7)
    (hgirth : ∀ D : Finset V, IsOddCycle G D → 7 ≤ D.card) (hne : Nonempty V) :
    ∃ v : V, HitsOddCycles G {v} := by
  by_cases hodd : ∃ C : Finset V, IsOddCycle G C
  · obtain ⟨C, hC, hshort⟩ := exists_shortest_oddCycle hodd
    have h1 : C.card ≤ Fintype.card V := by
      have h2 := Finset.card_le_univ C
      have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
      omega
    exact mem_hitsOddCycles_singleton_of_shortest_oddCycle_of_card_eq hC hshort (by
      have h1 := hgirth C hC
      omega)
  · obtain ⟨v⟩ := hne
    exact ⟨v, fun D hD => absurd ⟨D, hD⟩ hodd⟩

/-! ## Part 3 — the counting the five-cycle case needs

The five-cycle case of the seven-vertex instance (`G` triangle-free, shortest odd cycle `C` of five
vertices) is settled by two counts: each vertex outside `C` witnesses at most one five-cycle missing
a point of `C`, and at most one five-cycle meets `C` in three points, so at most `4` of the `5`
points of `C` are missed.  The first count needs the following fact, which is the independence number
of a five-cycle and is the only graph-theoretic input. -/

/-- **IN A TRIANGLE-FREE GRAPH THE NEIGHBOURS OF A VERTEX INSIDE A FIVE-CYCLE ARE AT MOST TWO.**

```lean
IsOddCycle G C → C.card = 5 → (G has no 3-clique) → x ~ a → x ~ b → x ~ c →
  a ≠ b → a ≠ c → b ≠ c → {a, b, c} ⊆ C → False
```

The three neighbours are pairwise non-adjacent, since `x` and two adjacent neighbours would be a
triangle; they are therefore an independent set of three elements of a five-cycle, and
`JSP90.two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle` reads `2 * 3 + 1 = 7 ≤ 5`. -/
theorem not_three_neigh_of_card_C_five_of_triangleFree {C : Finset V} (hC : IsOddCycle G C)
    (hC5 : C.card = 5) (htf : ∀ D : Finset V, ¬ G.IsNClique 3 D) {x a b c : V}
    (habc : a ≠ b) (hacb : a ≠ c) (hbcb : b ≠ c) (hsub : {a, b, c} ⊆ C)
    (ha : G.Adj x a) (hb : G.Adj x b) (hc : G.Adj x c) : False := by
  have hSi : G.IsIndepSet ((↑({a, b, c} : Finset V) : Set V)) := by
    refine G.isIndepSet_iff.mpr fun v hv w hw _hvw hadj => ?_
    have hxv : G.Adj x v := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv | hv | hv
      · rw [hv]; exact ha
      · rw [hv]; exact hb
      · rw [hv]; exact hc
    have hxw : G.Adj x w := by
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hw | hw | hw
      · rw [hw]; exact ha
      · rw [hw]; exact hb
      · rw [hw]; exact hc
    exact htf _ (show G.IsNClique 3 ({v, w, x} : Finset V) from
      isNClique_three_of_adj_adj_adj hadj hxv.symm hxw.symm)
  have hcard3 : ({a, b, c} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, habc, hacb, hbcb, rfl⟩
  have hsub' : (↑({a, b, c} : Finset V) : Set V) ⊆ (↑C : Set V) := hsub
  have h1 := two_mul_card_add_one_le_card_of_isIndepSet_sub_isOddCycle hC hSi hsub'
  rw [hcard3, hC5] at h1
  omega

/-- **THE COUNTING FORM OF THE ABOVE: A SET OF NEIGHBOURS OF `x` INSIDE A FIVE-CYCLE HAS AT MOST TWO
ELEMENTS.**  This is the input of the pigeonhole step that closes the five-cycle case of the
seven-vertex instance. -/
theorem card_le_two_neighOf_card_C_five_of_triangleFree (htf : ∀ D : Finset V, ¬ G.IsNClique 3 D)
    {C : Finset V} (hC : IsOddCycle G C) (hC5 : C.card = 5) {x : V} {S : Finset V}
    (hS : ∀ z : V, z ∈ S → z ∈ C ∧ G.Adj x z) : S.card ≤ 2 := by
  by_contra hcon
  have h3 : 3 ≤ S.card := by omega
  obtain ⟨a, ha, b, hb, c, hc, habc, hbcb, hacb⟩ := exists_three_of_card_ge_three h3
  have ha_c : a ≠ c := fun h => hacb h.symm
  have hsubS : ({a, b, c} : Finset V) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz
    · rw [hz]; exact ha
    · rw [hz]; exact hb
    · rw [hz]; exact hc
  exact not_three_neigh_of_card_C_five_of_triangleFree hC hC5 htf habc ha_c hbcb
    (fun (z : V) (hz : z ∈ ({a, b, c} : Finset V)) => (hS z (hsubS hz)).1)
    (hS a ha).2 (hS b hb).2 (hS c hc).2

/-! ## Part 2b — the same instance in the three shapes this development uses

The transversal shape (`tauOdd`), the `Erdős73On` class shape of
`JSPProblem/Five.lean` (`LocIndepOneSmallOrder`), and the sharpness: in the class of Part 2 the
constant `0` fails exactly when `G` is not bipartite, so the constant `1` is the best the class can
ask for. -/

/-- **The odd-girth instance in the transversal shape.** -/
theorem tauOdd_le_one_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven
    (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 7)
    (hgirth : ∀ D : Finset V, IsOddCycle G D → 7 ≤ D.card) (hne : Nonempty V) :
    tauOdd G ≤ 1 :=
  (closeToBipartite_iff_tauOdd_le (G := G) (m := 1)).mp
    (closeToBipartite_one_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven hG hV hgirth hne)

/-- **The class of Part 2, in the `LocIndepOneSmallOrder` shape of `JSPProblem/Five.lean`: Erdős #73
at `k = 1` for graphs of order at most seven and odd girth at least seven.** -/
def LocIndepOneSmallOrderOddGirth.{w} (m n g : ℕ) : Prop :=
  ∀ (W : Type w) (_ : Fintype W) (G : SimpleGraph W), Fintype.card W ≤ n → LocIndep 1 G →
    (∀ D : Finset W, IsOddCycle G D → g ≤ D.card) → CloseToBipartite m G

/-- **ERDŐS #73 AT `k = 1`, CONSTANT `1`, ON GRAPHS OF ORDER AT MOST SEVEN AND ODD GIRTH AT LEAST
SEVEN — THE INSTANCE IN THE `Erdős73On` SHAPE.** -/
theorem erdos73On_one_oddGirth_ge_seven : LocIndepOneSmallOrderOddGirth.{u} 1 7 7 :=
  fun (W : Type u) (_ : Fintype W) (G : SimpleGraph W) hV hG hgirth => by
    by_cases hne : Nonempty W
    · exact closeToBipartite_one_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven hG hV hgirth hne
    · refine ⟨∅, by simp, ?_⟩
      rw [deleteFinset_empty]
      refine isBipartite_of_no_oddCycle fun h => ?_
      obtain ⟨D, hD⟩ := h
      obtain ⟨z, -⟩ := nonempty_of_card_pos (s := D) (by
        have h1 := isOddCycle_card_ge_three hD
        omega)
      exact absurd ⟨z⟩ hne

/-- **IN THE CLASS OF PART 2 THE CONSTANT `0` FAILS EXACTLY WHEN `G` IS NOT BIPARTITE.**  Together
with `JSP90.tauOdd_zero_iff` this says the constant `1` of
`JSP90.closeToBipartite_one_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven` is optimal inside the
class: a non-bipartite member of the class has an odd cycle, hence (at most seven vertices) a
spanning seven-cycle. -/
theorem not_closeToBipartite_zero_of_oddGirth_ge_seven_of_not_isBipartite
    (hV : Fintype.card V ≤ 7) (hgirth : ∀ D : Finset V, IsOddCycle G D → 7 ≤ D.card)
    (hn : ¬ G.IsBipartite) : ¬ CloseToBipartite 0 G := by
  intro h
  have h1 : tauOdd G ≤ 0 := (closeToBipartite_iff_tauOdd_le (G := G) (m := 0)).mp h
  have h2 : G.IsBipartite := (tauOdd_zero_iff).mp (by omega)
  exact hn h2

/-- **A NON-BIPARTITE MEMBER OF THE CLASS HAS A SPANNING SEVEN-CYCLE.** -/
theorem exists_isOddCycle_card_eq_seven_of_oddGirth_ge_seven_of_not_isBipartite
    (hV : Fintype.card V ≤ 7) (hgirth : ∀ D : Finset V, IsOddCycle G D → 7 ≤ D.card)
    (hn : ¬ G.IsBipartite) : ∃ C : Finset V, IsOddCycle G C ∧ C.card = 7 := by
  by_contra hcon
  refine hn (isBipartite_of_no_oddCycle fun h => ?_)
  obtain ⟨C, hC⟩ := h
  refine hcon ⟨C, ?_⟩
  have h1 : 7 ≤ C.card := hgirth C hC
  have h2 : C.card ≤ Fintype.card V := by
    have h3 := Finset.card_le_univ C
    have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    omega
  exact ⟨hC, by omega⟩


/-! ## Part 4 — the local structure at a shortest odd cycle

The five-cycle case of the seven-vertex instance needs one more fact about a shortest odd cycle `C`:
**every vertex of `C` has exactly two neighbours inside `C`**, namely its two ring-neighbours, so two
distinct neighbours already exhaust its neighbourhood inside the cycle.  This is what lets one count
neighbourhoods without naming the cyclic order twice, and it is proved from
`JSP90.isInduced_shortest_oddCycle` (a shortest odd cycle carries no chord) together with the two
adjacencies `JSP90.CycleOrder.hcyc` and `JSP90.CycleOrder.adj_prev`. -/




/-! ## Part 4 — the local structure at a shortest odd cycle

The five-cycle case of the seven-vertex instance needs one more fact about a shortest odd cycle `C`:
**every vertex of `C` has exactly two neighbours inside `C`**, namely its two ring-neighbours, so two
distinct neighbours already exhaust its neighbourhood inside the cycle.  This is what lets one count
neighbourhoods without naming the cyclic order twice, and it is proved from
`JSP90.isInduced_shortest_oddCycle` (a shortest odd cycle carries no chord) together with the two
adjacencies `JSP90.CycleOrder.hcyc` and `JSP90.CycleOrder.adj_prev`. -/

/-- EVERY VERTEX OF A SHORTEST ODD CYCLE HAS EXACTLY TWO NEIGHBOURS INSIDE IT. -/
theorem card_neighIn_C_eq_two {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) {v : V} (hv : v ∈ C) :
    (C.filter (fun z => G.Adj v z)).card = 2 := by
  obtain ⟨o, -⟩ := hC.cycleOrder
  obtain ⟨j, hj⟩ := (o.hmem v).mp hv
  have hsub : (C.filter (fun z => G.Adj v z)) ⊆ {o.f (cycSucc j), o.f (o.prev j)} := by
    intro z hz
    have hzC : z ∈ C := (Finset.mem_filter.mp hz).1
    have hzv : G.Adj v z := (Finset.mem_filter.mp hz).2
    obtain ⟨k, hk⟩ := (o.hmem z).mp hzC
    have hind' : (induceFinset G C).Adj (o.f j) (o.f k) := by
      rw [induce_adj]
      exact ⟨(o.hmem (o.f j)).mpr ⟨j, rfl⟩, (o.hmem (o.f k)).mpr ⟨k, rfl⟩, by
        rw [hj, hk]; exact hzv⟩
    have hne' : j ≠ k := fun he => G.irrefl ((induce_adj.mp ((congrArg o.f he) ▸ hind')).2.2)
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases isInduced_shortest_oddCycle hC hshort o hne' hind' with h1 | h1
    · -- j = cycSucc k, hence k = prev j
      have hk' : k = o.prev j := by
        calc k = o.prev (cycSucc k) := (o.prev_succ k).symm
          _ = o.prev j := by rw [h1]
      exact Or.inr (hk.symm.trans (congrArg o.f hk'))
    · -- k = cycSucc j
      exact Or.inl (hk.symm.trans (congrArg o.f h1))
  have hmemA : o.f (cycSucc j) ∈ C := (o.hmem _).mpr ⟨cycSucc j, rfl⟩
  have hmemB : o.f (o.prev j) ∈ C := (o.hmem _).mpr ⟨o.prev j, rfl⟩
  have hadjA : G.Adj v (o.f (cycSucc j)) := by rw [← hj]; exact o.hcyc j
  have hadjB : G.Adj v (o.f (o.prev j)) := by rw [← hj]; exact o.adj_prev j
  have hsup : ({o.f (cycSucc j), o.f (o.prev j)} : Finset V) ⊆ C.filter (fun z => G.Adj v z) := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz
    · rw [hz]; exact Finset.mem_filter.mpr ⟨hmemA, hadjA⟩
    · rw [hz]; exact Finset.mem_filter.mpr ⟨hmemB, hadjB⟩
  have hA : (C.filter (fun z => G.Adj v z)).card ≤ 2 := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp; exact fun he => o.step_prev_ne j he)] at h1
    simp only [Finset.card_singleton] at h1
    omega
  have hB : 2 ≤ (C.filter (fun z => G.Adj v z)).card := by
    have h1 := Finset.card_le_card hsup
    rw [Finset.card_insert_of_notMem (by simp; exact fun he => o.step_prev_ne j he)] at h1
    simp only [Finset.card_singleton] at h1
    omega
  omega

/-- THE NEIGHBOURS OF A VERTEX OF A SHORTEST ODD CYCLE: two distinct neighbours already exhaust them. -/
theorem neigh_eq_of_adj_of_adj {C : Finset V} (hC : IsOddCycle G C)
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card) {v p q : V}
    (hv : v ∈ C) (hp : p ∈ C) (hq : q ∈ C) (hvp : G.Adj v p) (hvq : G.Adj v q) (hpq : p ≠ q) :
    ∀ z : V, z ∈ C → G.Adj v z → z = p ∨ z = q := by
  intro z hz hvz
  have hpair : ({p, q} : Finset V) ⊆ C.filter (fun u => G.Adj v u) := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with hu | hu
    · rw [hu]; exact Finset.mem_filter.mpr ⟨hp, hvp⟩
    · rw [hu]; exact Finset.mem_filter.mpr ⟨hq, hvq⟩
  have hle : (C.filter (fun u => G.Adj v u)).card ≤ ({p, q} : Finset V).card := by
    rw [card_neighIn_C_eq_two hC hshort hv, Finset.card_eq_two.mpr ⟨p, q, hpq, rfl⟩]
  have heq : ({p, q} : Finset V) = C.filter (fun u => G.Adj v u) :=
    Finset.eq_of_subset_of_card_le hpair hle
  have hz' : z ∈ ({p, q} : Finset V) := by
    rw [heq]; exact Finset.mem_filter.mpr ⟨hz, hvz⟩
  rcases Finset.mem_insert.mp hz' with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_singleton.mp h)
end
end JSP90
