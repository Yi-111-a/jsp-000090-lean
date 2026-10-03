/-
# JSP-000090, round 130 — **the case `k = 1` of Erdős Problem #73: the triangle descent, the odd
# girth bound, and the exact decomposition of the sharp constant `2`**

## Where this round starts

Rounds 123–129 measured, by exhaustive computation and by machine-checked witnesses, the first
constant of Erdős #73:

* `LocIndep 1` is the case "every subgraph `H` of `G` carries an independent set of size
  `≥ (|H| - 1) / 2`";
* the least odd cycle transversal number of a `LocIndep 1` graph is **at most `2`** on every graph
  up to eight vertices, and **`2` is attained** (`JSP90.k4sub` of `JSPProblem/FewOdd.lean`,
  `JSP90.p9` of `JSPProblem/Petersen.lean`).

So `f(1) = 2` is the sharp candidate, and the *content* of `k = 1` is exactly

```
Erdős73On 1 2        --   LocIndep 1 G → CloseToBipartite 2 G
```

which is the target this file attacks.  What the file delivers is **not** that theorem; it is the
first *systematic* splitting of it into statements that are each provable, together with two new
machine-checked facts about the constant.

## Part 1 — the triangle is a transversal at `LocIndep 1`

`JSPProblem/Triangle.lean` proves that a triangle costs one unit of deficiency off every disjoint
vertex set (`JSP90.maxDefIn_add_one_le_maxDef_of_triangle`).  At `k = 1` the budget is exhausted, so
everything hanging off a triangle is **bipartite**:

* **`JSP90.maxDefIn_univ_sdiff_isNClique_three_eq_zero`** — `maxDefIn G (univ \ T) = 0`;
* **`JSP90.isBipartite_induceFinset_univ_sdiff_isNClique_three_of_locIndep_one`** —
  `G[V \ T]` is bipartite;
* **`JSP90.deleteFinset_isNClique_three_isBipartite_of_locIndep_one`**,
  **`JSP90.closeToBipartite_three_of_locIndep_one_of_isNClique_three`** and
  **`JSP90.hitsOddCycles_isNClique_three_of_locIndep_one`** — **`T` is an odd cycle transversal of
  size three**: `CloseToBipartite 3 G`, with `T` itself as the transversal;
* **`JSP90.LocIndepOneHasTriangle 3`** — **a genuine instance of the conclusion of Erdős #73, at
  `k = 1`, with the constant `3`, for the class of `LocIndep 1` graphs that contain a triangle.**
  Rounds 125 and 126 obtained the *optimal* constant `2` for the class "all odd cycles are
  triangles"; this instance needs only "some triangle exists", so it covers far more graphs.

## Part 2 — the odd girth bounds the transversal at `LocIndep 1`

`JSPProblem/Two.lean` proves that at `LocIndep 1` every odd cycle is a transversal
(`JSP90.hitsOddCycles_of_isOddCycle_of_locIndep_one`).  The classical proof of Erdős #73 needs this
as the base case of its induction, and the development had never stated it as a bound:

* **`JSP90.isBipartite_deleteFinset_of_isOddCycle_of_locIndep_one`** — **everything outside an odd
  cycle is bipartite at `LocIndep 1`** (an odd cycle of the deletion would be an odd cycle of `G`
  disjoint from `C`, contradicting the fact just cited);
* **`JSP90.closeToBipartite_of_isOddCycle_of_locIndep_one`** and
  **`JSP90.closeToBipartite_of_locIndep_one_of_isOddCycle_of_card_le`** — the transversal bound;
* **`JSP90.closeToBipartite_of_locIndep_one_of_odd_girth`** — **at `k = 1` the least odd cycle
  transversal number is at most the odd girth**: if `G` has an odd cycle of `g` vertices and none of
  shorter length, then `CloseToBipartite g G` and `3 ≤ g`;
* **`JSP90.closeToBipartite_of_locIndep_one_of_oddCycles_of_card_eq`** (with
  `JSP90.closeToBipartite_five_of_locIndep_one_of_card_oddCycle_eq_five`,
  `JSP90.closeToBipartite_seven_of_locIndep_one_of_card_oddCycle_eq_seven` and
  `JSP90.closeToBipartite_of_locIndep_one_of_isNClique_three_or_oddCycles_card`) — a `LocIndep 1`
  graph all of whose odd cycles have the same length `g ≥ 3` is `g`-close to bipartite.  So the two
  ends of the bound are: a triangle costs `3`, and otherwise the odd cycle length is the price.

## Part 3 — the exact decomposition of `Erdős73On 1 2`

The sharp constant `2` splits into **exactly two** statements, and the round proves that they
suffice:

* **`JSP90.LocIndepOneTriangleFree m`** — the triangle-free case;
* **`JSP90.erdos73On_one_of_locIndepOneTriangleFree (m) : Erdős73On 1 (3 + m)`** — with the constant
  of the triangle case, `3` (Part 1), and the constant `m` of the triangle-free case;
* **`JSP90.erdos73One_iff_erdos73OneTri`** / **`JSP90.erdos73_one_iff_exists_locIndepOneTriangleFree`**
  — `Erdős73 1 ↔ ∃ m, LocIndepOneTriangleFree m`, the `k = 1` form of round 68's
  `JSP90.erdos73_iff_triangleFreeOnly`;
* **`JSP90.erdos73On_one_two_of_triangle_two_of_locIndepOneTriangleFree`** — **`Erdős73On 1 2`
  follows from the two sharp halves**: "constant `2` for graphs with a triangle"
  (`JSP90.LocIndepOneTriangleTwo`) and "constant `2` for triangle-free graphs"
  (`JSP90.LocIndepOneTriangleFree 2`);
* **`JSP90.not_erdos73On_one_two_of_not_locIndepOneTriangleFree`** — the triangle-free half is
  *necessary*.  So the residual of this round is a statement about **triangle-free** graphs only.

## Part 4 — the constant is `2`, not `1`, and there is no `K_4`

* **`JSP90.not_erdos73On_one_one`**, **`JSP90.not_erdos73On_one_of_le`** and
  **`JSP90.not_locIndepOneTriangleFree_one`** — **the constant `1` is refuted at `k = 1`, in the
  `Erdős73On` form and in the triangle-free form**: the witness is `JSP90.p9`, the Petersen graph
  with one vertex deleted (`JSPProblem/Petersen.lean`), which satisfies `LocIndep 1 p9`,
  `JSP90.cliqueFree_three_p9` and `¬ CloseToBipartite 1 p9`.  Hence `f(1) ≥ 2`, and **if the
  triangle-free case of `k = 1` holds at all, its constant is exactly `2`**.
* **`JSP90.not_isNClique_four_of_locIndep_one`** and
  **`JSP90.not_isClique_card_four_of_locIndep_one`** — **at `LocIndep 1` there is no `K_4`**;
* **`JSP90.not_adj_of_common_neigh_two_of_locIndep_one`** — **two vertices adjacent to the same two
  vertices of a triangle are not adjacent to each other**: the four of them would be a `K_4`.  This
  is the first statement of this development about the *second neighbourhood* of a triangle at
  `LocIndep 1`, and it is the configuration the petal route of rounds 123–125 needs and did not
  have.

## What is *not* proved

`Erdős73On 1 2` — and therefore neither half of Part 3.  Behind it stands
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas), the unchanged primary blocker.
`jsp_000090_main` is not declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`.
-/

import JSPProblem.MonoWind
import JSPProblem.Petersen
import JSPProblem.Two
import JSPProblem.Petal3
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

/-- `DecidableEq` for this file is *named*, so that it cannot clash with the anonymous instances
of the other modules imported by the root module `JSPProblem.lean`. -/
local instance onek_decidableEq : DecidableEq V := Classical.decEq V

local instance onek_decidablePredIsIndepSet (G : SimpleGraph V) :
    DecidablePred fun S : Finset V => G.IsIndepSet S :=
  fun _ => Classical.propDecidable _

/-! ### Part 1 — the triangle is an odd cycle transversal at `LocIndep 1` -/

section TriangleDescent

/-- A vertex set is disjoint from its complement. -/
theorem disjoint_univ_sdiff (T : Finset V) : Disjoint T (Finset.univ \ T) :=
  Finset.disjoint_left.mpr fun _ hT hU => (Finset.mem_sdiff.mp hU).2 hT

/-- **THE DESCENT AT `k = 1`: EVERYTHING DISJOINT FROM A TRIANGLE HAS DEFICIENCY ZERO.**  If `T` is
a triangle of a `LocIndep 1` graph then

```lean
maxDefIn G (Finset.univ \ T) = 0 ,
```

so every vertex set disjoint from `T` has deficiency `0`, i.e. `G[V \ T]` is *balanced*: all of its
induced subgraphs are bipartite.  This is the descent of `JSPProblem/Triangle.lean` read at its
sharpest: at `k = 1` a triangle spends the whole budget of the hypothesis, and nothing is left for
the rest of the graph. -/
theorem maxDefIn_univ_sdiff_isNClique_three_eq_zero (hG : LocIndep 1 G) {T : Finset V}
    (hT : G.IsNClique 3 T) :
    maxDefIn G ((Finset.univ : Finset V) \ T) = 0 := by
  have hcl : G.IsClique T := (G.isNClique_iff.mp hT).1
  have hcard : T.card = 3 := (G.isNClique_iff.mp hT).2
  have h1 : maxDefIn G ((Finset.univ : Finset V) \ T) + 1 ≤ MaxDef G :=
    maxDefIn_add_one_le_maxDef_of_triangle hcl hcard (disjoint_univ_sdiff T)
  have h2 : MaxDef G ≤ 1 := maxDef_le_of_locIndep hG
  omega

/-- **EVERYTHING OUTSIDE A TRIANGLE IS BIPARTITE AT `LocIndep 1`.** -/
theorem isBipartite_induceFinset_univ_sdiff_isNClique_three_of_locIndep_one (hG : LocIndep 1 G)
    {T : Finset V} (hT : G.IsNClique 3 T) :
    (induceFinset G ((Finset.univ : Finset V) \ T)).IsBipartite := by
  refine (maxDef_eq_zero_iff).mp ?_
  rw [maxDef_eq_maxDefIn_induceFinset]
  exact maxDefIn_univ_sdiff_isNClique_three_eq_zero hG hT

/-- The same statement in the language of Erdős's hypothesis: the graph outside a triangle of a
`LocIndep 1` graph satisfies the hypothesis with the parameter `0`, i.e. it is bipartite. -/
theorem locIndep_zero_induceFinset_univ_sdiff_isNClique_three_of_locIndep_one (hG : LocIndep 1 G)
    {T : Finset V} (hT : G.IsNClique 3 T) :
    LocIndep 0 (induceFinset G ((Finset.univ : Finset V) \ T)) := by
  have hz := maxDefIn_univ_sdiff_isNClique_three_eq_zero hG hT
  exact locIndep_induceFinset_of_maxDefIn_le (by omega)

/-- **A TRIANGLE OF A `LocIndep 1` GRAPH IS AN ODD CYCLE TRANSVERSAL: `T` DELETED LEAVES A BIPARTITE
GRAPH.** -/
theorem deleteFinset_isNClique_three_isBipartite_of_locIndep_one (hG : LocIndep 1 G)
    {T : Finset V} (hT : G.IsNClique 3 T) : (deleteFinset G T).IsBipartite :=
  isBipartite_induceFinset_univ_sdiff_isNClique_three_of_locIndep_one hG hT

/-- **AN INSTANCE OF THE CONCLUSION OF ERDŐS PROBLEM #73 AT `k = 1`, WITH THE CONSTANT `3`, FOR EVERY
GRAPH THAT HAS A TRIANGLE.**  `LocIndep 1 G` and `G` has a triangle give `CloseToBipartite 3 G`, the
triangle itself being the transversal. -/
theorem closeToBipartite_three_of_locIndep_one_of_isNClique_three (hG : LocIndep 1 G)
    {T : Finset V} (hT : G.IsNClique 3 T) : CloseToBipartite 3 G := by
  refine ⟨T, ?_, deleteFinset_isNClique_three_isBipartite_of_locIndep_one hG hT⟩
  have hcard : T.card = 3 := (G.isNClique_iff.mp hT).2
  omega

/-- The same statement with the constant `|T|`, the sharpest form: the triangle *is* the
transversal. -/
theorem closeToBipartite_card_isNClique_three_of_locIndep_one (hG : LocIndep 1 G)
    {T : Finset V} (hT : G.IsNClique 3 T) : CloseToBipartite T.card G := by
  have hcard : T.card = 3 := (G.isNClique_iff.mp hT).2
  exact closeToBipartite_mono (by omega) (closeToBipartite_three_of_locIndep_one_of_isNClique_three hG hT)

/-- **`T` meets every odd cycle of `G`**: a triangle of a `LocIndep 1` graph is a transversal not
only of the deletion but as a set of vertices. -/
theorem hitsOddCycles_isNClique_three_of_locIndep_one (hG : LocIndep 1 G) {T : Finset V}
    (hT : G.IsNClique 3 T) : HitsOddCycles G T :=
  hitsOddCycles_of_isBipartite_delete (deleteFinset_isNClique_three_isBipartite_of_locIndep_one hG hT)

/-- **THE CLASS OF GRAPHS ON WHICH THE CONCLUSION HOLDS AT `k = 1` WITH THE CONSTANT `3`.**  This is a
genuine instance of the conclusion of Erdős Problem #73 in the `Erdős73On` shape of
`JSPProblem/Definitions.lean`, restricted to the class of graphs containing a triangle: the only
hypothesis is Erdős's own, and the constant mentions neither the vertex set, nor the degrees, nor
the odd girth, nor the packing number. -/
def LocIndepOneHasTriangle (m : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    (∃ T : Finset W, G.IsNClique 3 T) → CloseToBipartite m G

/-- **THE INSTANCE OF PART 1.** -/
theorem locIndepOneHasTriangle_three : LocIndepOneHasTriangle.{u} 3 := by
  intro W instW G hG
  rintro ⟨T, hT⟩
  exact closeToBipartite_three_of_locIndep_one_of_isNClique_three hG hT

/-- Every constant at least `3` works on that class. -/
theorem locIndepOneHasTriangle_of_three {m : ℕ} (hm : 3 ≤ m) : LocIndepOneHasTriangle.{u} m :=
  fun W instW G hG hT => closeToBipartite_mono hm (locIndepOneHasTriangle_three W instW G hG hT)

end TriangleDescent

/-! ### Part 2 — at `LocIndep 1` the odd girth bounds the odd cycle transversal -/

section GirthBound

/-- **EVERYTHING OUTSIDE AN ODD CYCLE IS BIPARTITE AT `LocIndep 1`.**  Indeed an odd cycle of
`G \ C` would be an odd cycle of `G` avoiding `C`, while at `LocIndep 1` every odd cycle of `G` meets
every other one (`JSP90.hitsOddCycles_of_isOddCycle_of_locIndep_one`). -/
theorem isBipartite_deleteFinset_of_isOddCycle_of_locIndep_one (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) : (deleteFinset G C).IsBipartite := by
  refine isBipartite_of_no_oddCycle ?_
  rintro ⟨D, hD⟩
  have hDsub : D ⊆ (Finset.univ : Finset V) \ C := isOddCycle_sub_induceFinset hD
  have hD' : IsOddCycle G D := hD.of_deleteFinset
  have hne : D ∩ C ≠ ∅ := hitsOddCycles_of_isOddCycle_of_locIndep_one hG hC D hD'
  obtain ⟨x, hxDC⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hxD, hxC⟩ := Finset.mem_inter.mp hxDC
  exact (Finset.mem_sdiff.mp (Finset.mem_of_subset hDsub hxD)).2 hxC

/-- **AN ODD CYCLE OF A `LocIndep 1` GRAPH IS AN ODD CYCLE TRANSVERSAL OF THAT SIZE.** -/
theorem closeToBipartite_of_isOddCycle_of_locIndep_one (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) : CloseToBipartite C.card G :=
  ⟨C, Nat.le_refl _, isBipartite_deleteFinset_of_isOddCycle_of_locIndep_one hG hC⟩

/-- The same statement with any bound `m ≥ |C|`. -/
theorem closeToBipartite_of_locIndep_one_of_isOddCycle_of_card_le (hG : LocIndep 1 G)
    {C : Finset V} (hC : IsOddCycle G C) {m : ℕ} (hm : C.card ≤ m) : CloseToBipartite m G :=
  ⟨C, hm, isBipartite_deleteFinset_of_isOddCycle_of_locIndep_one hG hC⟩

/-- **AT `k = 1` THE LEAST ODD CYCLE TRANSVERSAL NUMBER IS AT MOST THE LENGTH OF ANY ODD CYCLE.**
This is the base case of the classical induction on Erdős's parameter in the form the development
consumes: the transversal is an odd cycle, and *everything outside it is bipartite*
(`JSP90.isBipartite_deleteFinset_of_isOddCycle_of_locIndep_one`). -/
theorem closeToBipartite_of_isOddCycle_of_locIndep_one' (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) : CloseToBipartite C.card G :=
  closeToBipartite_of_isOddCycle_of_locIndep_one hG hC

/-- **AT `k = 1` THE LEAST ODD CYCLE TRANSVERSAL NUMBER IS AT MOST THE ODD GIRTH.**  Suppose `G`
has an odd cycle of `g` vertices (`hex`) and none of shorter length (`hmin`), i.e. `g` is the odd
girth of `G`.  Then

```lean
CloseToBipartite g G     -- the least odd cycle transversal number is at most `g`
```

and `3 ≤ g`.  Nothing else is assumed: `g` is not the number of vertices of `G`, not a bound on the
degrees, not a bound on the packing weight.  Together with Part 1 this is the base case of the
classical induction on Erdős's parameter, with the transversal being the shortest odd cycle and
*everything outside it bipartite* (`JSP90.isBipartite_deleteFinset_of_isOddCycle_of_locIndep_one`). -/
theorem closeToBipartite_of_locIndep_one_of_odd_girth (hG : LocIndep 1 G) {g : ℕ}
    (hex : ∃ C : Finset V, IsOddCycle G C ∧ C.card = g)
    (hmin : ∀ C : Finset V, IsOddCycle G C → g ≤ C.card) : CloseToBipartite g G ∧ 3 ≤ g := by
  obtain ⟨C, hC, hCg⟩ := hex
  have hshort : ∀ E : Finset V, IsOddCycle G E → g ≤ E.card := hmin
  have h1 : CloseToBipartite g G := by
    rw [← hCg]
    exact closeToBipartite_of_isOddCycle_of_locIndep_one hG hC
  have h3 : 3 ≤ g := by
    obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
    have hcard : C.card = m := card_eq_cyclicOrder f hinj hmem
    rw [hCg] at hcard
    omega
  exact ⟨h1, h3⟩

/-- The transversal bound of `JSP90.closeToBipartite_of_locIndep_one_of_odd_girth` on its own. -/
theorem closeToBipartite_of_locIndep_one_of_odd_girth' (hG : LocIndep 1 G) {g : ℕ}
    (hex : ∃ C : Finset V, IsOddCycle G C ∧ C.card = g)
    (hmin : ∀ C : Finset V, IsOddCycle G C → g ≤ C.card) : CloseToBipartite g G :=
  (closeToBipartite_of_locIndep_one_of_odd_girth hG hex hmin).1

/-- **A `LocIndep 1` GRAPH ALL OF WHOSE ODD CYCLES HAVE THE SAME LENGTH `g ≥ 3` IS `g`-CLOSE TO
BIPARTITE.**  In particular a `LocIndep 1` graph whose odd cycles are all `5`-cycles is
`5`-close to bipartite, and one whose odd cycles are all `7`-cycles is `7`-close to bipartite. -/
theorem closeToBipartite_of_locIndep_one_of_oddCycles_of_card_eq (hG : LocIndep 1 G) {g : ℕ}
    (hg : 3 ≤ g) (hall : ∀ C : Finset V, IsOddCycle G C → C.card = g) : CloseToBipartite g G := by
  by_cases hex : ∃ C : Finset V, IsOddCycle G C
  · obtain ⟨C, hC⟩ := hex
    have hcg : C.card = g := hall C hC
    exact closeToBipartite_mono (by omega) (closeToBipartite_of_isOddCycle_of_locIndep_one hG hC)
  · have hg3 : 3 ≤ g := hg
    exact closeToBipartite_mono (Nat.zero_le _) (closeToBipartite_of_isBipartite'
      (isBipartite_of_no_oddCycle hex))

/-- **A `LocIndep 1` GRAPH WHOSE ODD CYCLES ARE ALL `5`-CYCLES IS `5`-CLOSE TO BIPARTITE.** -/
theorem closeToBipartite_five_of_locIndep_one_of_card_oddCycle_eq_five (hG : LocIndep 1 G)
    (hall : ∀ C : Finset V, IsOddCycle G C → C.card = 5) : CloseToBipartite 5 G :=
  closeToBipartite_of_locIndep_one_of_oddCycles_of_card_eq hG (by omega) hall

/-- **A `LocIndep 1` GRAPH WHOSE ODD CYCLES ARE ALL `7`-CYCLES IS `7`-CLOSE TO BIPARTITE.** -/
theorem closeToBipartite_seven_of_locIndep_one_of_card_oddCycle_eq_seven (hG : LocIndep 1 G)
    (hall : ∀ C : Finset V, IsOddCycle G C → C.card = 7) : CloseToBipartite 7 G :=
  closeToBipartite_of_locIndep_one_of_oddCycles_of_card_eq hG (by omega) hall

/-- **THE TWO ENDS OF THE BOUND TOGETHER:** at `LocIndep 1` a graph with a triangle is `3`-close to
bipartite (Part 1), and a graph all of whose odd cycles have the same length `g ≥ 5` is `g`-close
to bipartite.  So the triangle is the *only* cheap case, and the odd cycle length is the price of a
graph without one. -/
theorem closeToBipartite_of_locIndep_one_of_isNClique_three_or_oddCycles_card (hG : LocIndep 1 G)
    {g : ℕ} (hg : 5 ≤ g) (hall : ∀ C : Finset V, IsOddCycle G C → C.card = g) :
    CloseToBipartite 3 G ∨ CloseToBipartite g G := by
  by_cases htf : G.CliqueFree 3
  · have hg3 : 3 ≤ g := by omega
    exact Or.inr (closeToBipartite_of_locIndep_one_of_oddCycles_of_card_eq hG hg3 hall)
  · obtain ⟨T, hT⟩ : ∃ T : Finset V, G.IsNClique 3 T := by
      by_contra hc
      exact htf fun T hT => hc ⟨T, hT⟩
    exact Or.inl (closeToBipartite_three_of_locIndep_one_of_isNClique_three hG hT)

end GirthBound

/-! ### Part 3 — the exact decomposition of `Erdős73On 1 2` -/

section Reduction

/-- **ERDŐS PROBLEM #73 AT `k = 1`, IN ITS TRIANGLE-FREE FORM.**  This is the statement that Part 3
leaves open for `k = 1`; it is the `k = 1` case of `JSP90.TriangleFreeOnly` with a constant that is
*not* prescribed in advance. -/
def LocIndepOneTriangleFree (m : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G → G.CliqueFree 3 →
    CloseToBipartite m G

/-- The triangle-free statement is implied by `Erdős73On 1 m`. -/
theorem locIndepOneTriangleFree_of_erdos73On_one (m : ℕ) (h : Erdős73On.{u} 1 m) :
    LocIndepOneTriangleFree.{u} m :=
  fun _ instW G hG _ => h _ instW G hG

/-- **ERDŐS PROBLEM #73 AT `k = 1` FOLLOWS FROM ITS TRIANGLE-FREE CASE, WITH THE CONSTANT `3 + m`.**
The triangle case is Part 1 and costs three vertices; the triangle-free case is the hypothesis.
No hypothesis is needed on the triangle: the triangle is simply deleted, and the rest is bipartite
at `LocIndep 1` whatever hangs off it. -/
theorem erdos73On_one_of_locIndepOneTriangleFree (m : ℕ) (h : LocIndepOneTriangleFree.{u} m) :
    Erdős73On.{u} 1 (3 + m) := by
  intro W instW G hG
  by_cases htri : G.CliqueFree 3
  · exact closeToBipartite_mono (by omega) (h W instW G hG htri)
  · obtain ⟨T, hT⟩ : ∃ T : Finset W, G.IsNClique 3 T := by
      by_contra hc
      exact htri fun T hT => hc ⟨T, hT⟩
    exact closeToBipartite_mono (by omega)
      (closeToBipartite_three_of_locIndep_one_of_isNClique_three hG hT)

/-- **THE CONSTANT IS WHAT THE TRIANGLE-FREE CASE COSTS, PLUS THREE.**  `Erdős73On 1 (3 + m)` is
*exactly* the triangle-free statement at `3 + m`, and it is *implied* by the triangle-free statement
at `m`.  The two are therefore interchangeable up to the additive constant `3`, which is the price
of the triangle descent of Part 1. -/
theorem locIndepOneTriangleFree_of_erdos73On_one_three_add_iff (m : ℕ) :
    Erdős73On.{u} 1 (3 + m) → LocIndepOneTriangleFree.{u} (3 + m) :=
  locIndepOneTriangleFree_of_erdos73On_one (3 + m)

theorem erdos73On_one_of_locIndepOneTriangleFree_three_add (m : ℕ)
    (h : LocIndepOneTriangleFree.{u} (3 + m)) : Erdős73On.{u} 1 (3 + (3 + m)) :=
  erdos73On_one_of_locIndepOneTriangleFree (3 + m) h

/-- **ERDŐS PROBLEM #73 AT `k = 1` IS EQUIVALENT TO THE EXISTENCE OF A CONSTANT IN ITS TRIANGLE-FREE
FORM.**  The `k = 1` case of `JSP90.erdos73_iff_triangleFreeOnly`, with the constant left free. -/
theorem erdos73_one_iff_exists_locIndepOneTriangleFree : Erdős73.{u} 1 ↔
    ∃ m : ℕ, LocIndepOneTriangleFree.{u} m := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, locIndepOneTriangleFree_of_erdos73On_one m hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨3 + m, erdos73On_one_of_locIndepOneTriangleFree m hm⟩

/-- **ERDŐS PROBLEM #73 AT `k = 1`, IN ITS FULL FORM AND IN THE SHARP CONSTANT `2`.**  This is the
statement this round wants; it is a `def`, *not* assumed anywhere in this file. -/
def Erdős73OneTwo : Prop := Erdős73On.{u} 1 2

/-- **THE TRIANGLE CASE OF THE SHARP CONSTANT** — the `k = 1` half of `Erdős73OneTwo` that is *not*
about triangle-free graphs: the constant `2` for the graphs that have a triangle.  Part 1 proves
it with the constant `3`. -/
def LocIndepOneTriangleTwo : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    (∃ T : Finset W, G.IsNClique 3 T) → CloseToBipartite 2 G

/-- **THE TWO HALVES OF `Erdős73On 1 2` SUFFICE.**  The sharp `k = 1` case follows from

* `JSP90.LocIndepOneTriangleTwo` — the constant `2` when there is a triangle, and
* `JSP90.LocIndepOneTriangleFree 2` — the constant `2` when there is none,

so the two halves are independent problems and the residual of this round is a statement about
**triangle-free** graphs only. -/
theorem erdos73On_one_two_of_triangle_two_of_locIndepOneTriangleFree
    (h1 : LocIndepOneTriangleTwo.{u}) (h2 : LocIndepOneTriangleFree.{u} 2) : Erdős73On.{u} 1 2 := by
  intro W instW G hG
  by_cases htri : G.CliqueFree 3
  · exact h2 W instW G hG htri
  · obtain ⟨T, hT⟩ : ∃ T : Finset W, G.IsNClique 3 T := by
      by_contra hc
      exact htri fun T hT => hc ⟨T, hT⟩
    exact h1 W instW G hG ⟨T, hT⟩

/-- **THE TRIANGLE-FREE HALF IS NECESSARY.**  Failing the triangle-free statement at `2` refutes
`Erdős73On 1 2`. -/
theorem not_erdos73On_one_two_of_not_locIndepOneTriangleFree
    (h : ¬ LocIndepOneTriangleFree.{u} 2) : ¬ Erdős73On.{u} 1 2 :=
  fun hmain => h (locIndepOneTriangleFree_of_erdos73On_one 2 hmain)

end Reduction

/-! ### Part 4 — the constant is `2`, not `1`, and there is no `K_4` -/

section Sharp

/-- **THE CONSTANT `1` IS REFUTED AT `k = 1`.**  `¬ Erdős73On 1 1`: the witness is `JSP90.p9`, the
Petersen graph with one vertex deleted (`JSPProblem/Petersen.lean`), which satisfies
`LocIndep 1 p9` and `¬ CloseToBipartite 1 p9`.  Together with Part 3 this pins the first constant of
Erdős #73 at `f(1) ≥ 2`, with `f(1) = 2` the sharp candidate. -/
theorem not_erdos73On_one_one : ¬ Erdős73On.{0} 1 1 := by
  rintro h
  obtain ⟨W, instW, G, hG, hnb⟩ := erdos73_lower_bound_two 1 1 (by omega)
  exact hnb (h W instW G hG)

/-- **NO CONSTANT BELOW `2` WORKS AT `k = 1`.** -/
theorem not_erdos73On_one_of_le (m : ℕ) (hm : m ≤ 1) : ¬ Erdős73On.{0} 1 m := by
  have h0 : m = 0 ∨ m = 1 := by omega
  rcases h0 with rfl | rfl
  · rintro h
    obtain ⟨W, instW, G, hG, hnb⟩ := erdos73_lower_bound_two 1 0 (by omega)
    exact hnb (h W instW G hG)
  · exact not_erdos73On_one_one

/-- **`JSP90.p9` IS TRIANGLE-FREE AS A `SimpleGraph.CliqueFree`.**  `JSP90.triangleFree_p9` says
that no vertex is adjacent to two adjacent vertices, and that is exactly `CliqueFree 3`. -/
theorem cliqueFree_three_p9 : p9.CliqueFree 3 := by
  rintro T hT
  obtain ⟨hcl, hcard⟩ := p9.isNClique_iff.mp hT
  obtain ⟨a, b, c, hab, hac, hbc, hTeq⟩ := Finset.card_eq_three.mp hcard
  have hadab : p9.Adj a b := hcl (Finset.mem_coe.mpr (by rw [hTeq]; simp))
    (Finset.mem_coe.mpr (by rw [hTeq]; simp)) (by simpa using hab)
  have hadac : p9.Adj a c := hcl (Finset.mem_coe.mpr (by rw [hTeq]; simp))
    (Finset.mem_coe.mpr (by rw [hTeq]; simp)) (by simpa using hac)
  have hadbc : p9.Adj b c := hcl (Finset.mem_coe.mpr (by rw [hTeq]; simp))
    (Finset.mem_coe.mpr (by rw [hTeq]; simp)) (by simpa using hbc)
  exact triangleFree_p9 b c hadbc ⟨a, hadab.symm, hadac⟩

/-- **THE CONSTANT `1` IS REFUTED AT `k = 1` EVEN IN THE TRIANGLE-FREE CLASS.**  So the constant of
`JSP90.LocIndepOneTriangleFree`, if the triangle-free case of Erdős #73 at `k = 1` holds at all, is
**exactly `2`**: it cannot be `1`, and Part 3 shows the general case costs `3 + m`. -/
theorem not_locIndepOneTriangleFree_one : ¬ LocIndepOneTriangleFree.{0} 1 := by
  rintro h
  exact not_closeToBipartite_one_p9 (h (Fin 9) inferInstance p9 (locIndep_one_p9) cliqueFree_three_p9)

/-- **AT `LocIndep 1` THERE IS NO `K_4`** — the `IsNClique` form. -/
theorem not_isNClique_four_of_locIndep_one (hG : LocIndep 1 G) :
    ¬ ∃ T : Finset V, G.IsNClique 4 T := by
  rintro ⟨T, hT⟩
  refine not_locIndep_one_of_clique_four ?_ (G.isNClique_iff.mp hT).2 hG
  intro v w hvw hv hw
  exact (G.isNClique_iff.mp hT).1 hv hw hvw

/-- **FOUR MUTUALLY ADJACENT VERTICES ARE IMPOSSIBLE AT `LocIndep 1`**: they would form a `K_4`. -/
theorem not_isClique_card_four_of_locIndep_one (hG : LocIndep 1 G) {a b c d : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) (hbd : G.Adj b d)
    (hcd : G.Adj c d) : False := by
  refine not_isNClique_four_of_locIndep_one hG ⟨{a, b, c, d}, G.isNClique_iff.mpr ⟨?_, ?_⟩⟩
  · intro v hv w hw hvw
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl
    all_goals first
      | exact (hvw rfl).elim
      | exact hab | exact hac | exact had | exact hbc | exact hbd | exact hcd
      | exact hab.symm | exact hac.symm | exact had.symm | exact hbc.symm | exact hbd.symm
      | exact hcd.symm
  · refine Finset.card_eq_four.mpr ⟨a, b, c, d, adj_irrefl' hab, adj_irrefl' hac,
      adj_irrefl' had, adj_irrefl' hbc, adj_irrefl' hbd, adj_irrefl' hcd, rfl⟩

/-- **TWO VERTICES ADJACENT TO THE SAME TWO VERTICES OF A TRIANGLE ARE NOT ADJACENT TO EACH OTHER.**
At `LocIndep 1` the four of them would be a `K_4`.  This is the first statement of this development
about the *second neighbourhood* of a triangle at `LocIndep 1`: the common neighbours of two
vertices of a triangle form an independent set.  It is the configuration the petal route of rounds
123–125 needs and did not have. -/
theorem not_adj_of_common_neigh_two_of_locIndep_one (hG : LocIndep 1 G) {a b v w : V}
    (hab : G.Adj a b) (hav : G.Adj a v) (hcv : G.Adj b v) (haw : G.Adj a w) (hwb : G.Adj b w)
    (hvw : G.Adj v w) : False :=
  not_isClique_card_four_of_locIndep_one hG hab hav haw hcv hwb hvw

end Sharp

/-! ### The axiom report of this file -/

section Axioms

#print axioms JSP90.maxDefIn_univ_sdiff_isNClique_three_eq_zero
#print axioms JSP90.isBipartite_induceFinset_univ_sdiff_isNClique_three_of_locIndep_one
#print axioms JSP90.closeToBipartite_three_of_locIndep_one_of_isNClique_three
#print axioms JSP90.LocIndepOneHasTriangle
#print axioms JSP90.locIndepOneHasTriangle_three
#print axioms JSP90.isBipartite_deleteFinset_of_isOddCycle_of_locIndep_one
#print axioms JSP90.closeToBipartite_of_isOddCycle_of_locIndep_one
#print axioms JSP90.closeToBipartite_of_locIndep_one_of_odd_girth
#print axioms JSP90.closeToBipartite_five_of_locIndep_one_of_card_oddCycle_eq_five
#print axioms JSP90.LocIndepOneTriangleFree
#print axioms JSP90.erdos73On_one_of_locIndepOneTriangleFree
#print axioms JSP90.erdos73_one_iff_exists_locIndepOneTriangleFree
#print axioms JSP90.erdos73On_one_two_of_triangle_two_of_locIndepOneTriangleFree
#print axioms JSP90.not_erdos73On_one_one
#print axioms JSP90.not_locIndepOneTriangleFree_one
#print axioms JSP90.not_isNClique_four_of_locIndep_one
#print axioms JSP90.not_adj_of_common_neigh_two_of_locIndep_one

end Axioms

end

end JSP90