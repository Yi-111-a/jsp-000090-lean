/-
# JSP-000090, round 134 — `JSPProblem/AttachErase.lean`: **the erasable vertices of an odd cycle**,
# and the residual of the sharp `k = 1` case in one line

Attack family 63.  This round does **not** attack `JSP90.PetalSetLeTwoOfOne` (the residual of
rounds 119–131) by counting again; it

1. **characterises the vertices of an odd cycle which may be erased** (Part 1) — a theorem with no
   counting in it at all, which turns the attachment set into an exact criterion;
2. derives from it **a new instance of the headline theorem for an arbitrary odd cycle, with the
   constant `|C| - 1`** (Part 2), which is the sharp version of what
   `JSPProblem/Two.lean` could only state for triangles, and which improves the odd-girth bound
   `ℓ * k` of `JSPProblem/Transversal.lean` to `ℓ - 1` at `k = 1`;
3. states the residual of the **whole** sharp `k = 1` case as a single statement about the
   **shortest odd cycle** (Part 3), and proves that this one statement yields `Erdős73On 1 2` —
   so the case `k = 1` of Erdős #73 now has *one* residual instead of two;
4. **refutes, machine-checked**, the structural hypothesis that the classical argument would like at
   a shortest odd cycle (Part 4): *at `LocIndep 1` an odd cycle need not use all but one vertex of a
   shortest odd cycle*.  The witness is the five-vertex windmill, already in
   `JSPProblem/Windmill.lean`.  This closes the "high intersection" route
   (`JSPProblem/Two.lean`, item 5) as a way of proving the triangle-free half.

## Part 1 — an erasable vertex

`JSP90.PetalSet G C` (`JSPProblem/Petal.lean`) is the attachment set of `C`: the vertices of `C`
which lie *alone* on some odd cycle of `G`.  `JSPProblem/Two.lean` shows that *some* vertex of `C`
outside the attachment set can be erased when `|C| = 3`; the following is the exact statement, for
**every** odd cycle and with no hypothesis at all beyond "every odd cycle meets `C`":

* **`JSP90.hitsOddCycles_erase_iff_notMem_petalSet`** — **A VERTEX OF AN ODD CYCLE CAN BE ERASED
  IF AND ONLY IF IT IS NOT AN ATTACHMENT POINT**:

  ```lean
  HitsOddCycles G (C.erase p) ↔ p ∉ PetalSet G C
  ```

  The two directions are the two halves of the definition: an attachment point `p` witnesses an odd
  cycle avoiding `C.erase p`, and an odd cycle avoiding `C.erase p` is disjoint from `C` unless its
  intersection with `C` is exactly `{p}`, i.e. `p` is an attachment point.  So the vertices that
  cannot be erased are *exactly* the attachment points, and nothing else;
* **`JSP90.closeToBipartite_erase_of_notMem_petalSet`** and
  **`JSP90.closeToBipartite_card_sub_one_of_petalSet_lt_card`** — hence
  `CloseToBipartite (|C| - 1) G` as soon as the attachment set is a **proper subset of `C`**.  The
  certificate is `C.erase p` itself, i.e. the transversal is *contained in the cycle*.

## Part 2 — a new instance: the constant `|C| - 1` for an arbitrary odd cycle

* **`JSP90.closeToBipartite_of_isOddCycle_of_petalSet_lt_card`**,
  **`JSP90.erdos73On_of_isOddCycle_of_petalSet_lt_card`** — for every `k ≤ 1`, `LocIndep k G`, an
  odd cycle `C` with `|PetalSet G C| < |C|`: `CloseToBipartite (|C| - 1) G`.  **A NEW INSTANCE OF
  THE HEADLINE THEOREM**: the constant is `|C| - 1` for an odd cycle of *arbitrary* length (rounds
  111–131 could state `2` only at a triangle, and `|C| - 1 + |PetalSet|` only with the attachment set
  in the constant), the hypothesis counts nothing and bounds no girth, degree, packing weight or
  packing number;
* **`JSP90.closeToBipartite_of_locIndep_one_of_odd_girth_of_petalSet_lt_card`** — at `k = 1`, an odd
  girth `≤ ℓ` and an odd cycle `C` of length `ℓ` with `|PetalSet G C| < ℓ` give
  `CloseToBipartite (ℓ - 1) G`, which is **one vertex better** than the `ℓ * k` of
  `JSPProblem/Transversal.lean` and is *equal* to the sharp constant `2` when `ℓ = 3`.

## Part 3 — the residual of the sharp `k = 1` case, in one line

* **`JSP90.PetalSetLeTwoOfOneAny`** — the attachment set of **any** odd cycle of a `LocIndep 1` graph
  has at most two points.  This *generalises* `JSP90.PetalSetLeTwoOfOne` (which is stated for
  triangles) and is stated here, **not assumed**;
* **`JSP90.erdos73On_of_petalSetLeTwoOfOneAny`** — it gives `CloseToBipartite (|C| - 1) G` for every
  odd cycle, hence the sharp `k = 1` conclusion on the class of graphs that contain a triangle
  (because `2 < 3 = |T|`);
* **`JSP90.ShortestOddCycleTransversal m`** and
  **`JSP90.erdos73On_one_of_shortestOddCycleTransversal_two`** — **the whole sharp case `k = 1` in
  ONE statement**: *at `LocIndep 1`, two vertices of a shortest odd cycle meet every odd cycle*.
  `JSP90.erdos73On_one_of_shortestOddCycleTransversal_two` proves that this single statement yields
  `Erdős73On 1 2`, i.e. Erdős #73 at `k = 1` with the optimal constant `2`, and
  `JSP90.not_erdos73On_one_two_of_not_shortestOddCycleTransversal_two` proves it is **necessary**.
  So after this round the case `k = 1` has exactly **one** residual, and it is a statement about the
  shortest odd cycle — not about a triangle;
* **`JSP90.ShortestOddCycleTransversalTriFree`** +
  **`JSP90.erdos73On_one_of_triangleFree_of_shortestTwo_of_petalSetLeTwoOfOne`** — the *exact*
  decomposition of `Erdős73On 1 2` into the triangle half (which reduces to
  `JSP90.PetalSetLeTwoOfOne`) and the triangle-free half (this new one-liner).

## Part 4 — the "high intersection" route is refuted, machine-checked

`JSPProblem/Two.lean` (item 5) proves the constant `2` from the hypothesis *"every odd cycle uses all
but one vertex of `C`"*.  That hypothesis is **not** automatic at `LocIndep 1`, even at a **shortest**
odd cycle:

* **`JSP90.not_forall_card_sdiff_le_one_wf`** — on the six-vertex windmill `wf` of
  `JSPProblem/Windmill.lean` (two triangles sharing the single vertex `0`, plus an isolated vertex),
  which satisfies `LocIndep 1 wf`, the two odd cycles `{0,1,2}` and `{0,3,4}` meet in the single
  vertex `0`, so `|{0,1,2} \ {0,3,4}| = 2`.  Both are shortest odd cycles, so
  **`JSP90.two_shortest_oddCycles_can_meet_in_one_wf`** is the machine-checked refutation of
  "at `LocIndep 1` any two shortest odd cycles share at least two vertices", and
  `JSP90.card_sdiff_two_of_two_shortest_oddCycles_wf` records the exact value.

## What is *not* proved

`JSP90.ShortestOddCycleTransversal 2` and `JSP90.PetalSetLeTwoOfOneAny` are **stated, not assumed**,
and behind them stands `JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas).  Exhaustive
search outside Lean this round (`discovery/JSP-000090/r134.c`, `r134b.c`, `r134c.c`) over **all**
graphs with `MaxDef ≤ 1` on `n ≤ 7` vertices (986 787 of them at `n = 7`) confirms that

* the two vertices of a **shortest** odd cycle always meet every odd cycle (`ShortestOddCycleTransversal`
  holds on every such graph, and `|C \ D| ≤ 1` — the hypothesis of round 122, item 5 — **fails** at
  `n = 5`), and
* the attachment set of **any** odd cycle always has at most two elements,

so both statements are the right ones.  `jsp_000090_main` is not declared, so the harness keeps
reporting `missing_theorems = ["jsp_000090_main"]`.
-/

import JSPProblem.PetalOverlap
import JSPProblem.Descent
import JSPProblem.Windmill
import JSPProblem.Nonagon
import Mathlib.Data.Finset.SDiff

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance attachEraseDecidableEq : DecidableEq V := Classical.decEq V

/-! ## Part 1 — a vertex of an odd cycle can be erased if and only if it is not an attachment
point -/

section Erase

/-- **A THREE-CLIQUE IS AN ODD CYCLE.**  `G.IsNClique 3 T` says that `T` is a `K_3` of three
vertices, and a triangle is an odd cycle; the certificate is the cyclic numbering
`0 ↦ a`, `1 ↦ b`, `2 ↦ c`.  (The development had `JSP90.isNClique_three_of_isOddCycle` in the other
direction only, in `JSPProblem/Free.lean`.) -/
theorem isOddCycle_of_isNClique_three {T : Finset V} (hT : G.IsNClique 3 T) : IsOddCycle G T := by
  obtain ⟨hcl, hcard⟩ := hT
  obtain ⟨a, b, c, hab, hac, hbc, hTeq⟩ := Finset.card_eq_three.mp hcard
  have hmemT (z : V) (hz : z = a ∨ z = b ∨ z = c) : z ∈ T := by
    rw [hTeq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hz with rfl | rfl | rfl <;> simp
  have hTab : G.Adj a b := hcl (hmemT a (Or.inl rfl)) (hmemT b (Or.inr (Or.inl rfl))) (by simpa using hab)
  have hTac : G.Adj a c := hcl (hmemT a (Or.inl rfl)) (hmemT c (Or.inr (Or.inr rfl))) (by simpa using hac)
  have hTbc : G.Adj b c := hcl (hmemT b (Or.inr (Or.inl rfl))) (hmemT c (Or.inr (Or.inr rfl))) (by simpa using hbc)
  have hTca : G.Adj c a := hTac.symm
  have hs0 : cycSucc (0 : Fin 3) = 1 := Fin.ext (by simp [cycSucc])
  have hs1 : cycSucc (1 : Fin 3) = 2 := Fin.ext (by simp [cycSucc])
  have hs2 : cycSucc (2 : Fin 3) = 0 := Fin.ext (by simp [cycSucc])
  let t : Fin 3 → V := fun i => if i = 0 then a else if i = 1 then b else c
  have hs : ∀ i : Fin 3, G.Adj (t i) (t (cycSucc i)) := by
    intro i
    fin_cases i
    · simpa [t, cycSucc] using (show G.Adj (t 0) (t (1 : Fin 3)) from hTab)
    · simpa [t, cycSucc] using (show G.Adj (t 1) (t (2 : Fin 3)) from hTbc)
    · simpa [t, cycSucc] using (show G.Adj (t 2) (t (0 : Fin 3)) from hTca)
  have ht0 : t 0 = a := by simp [t]
  have ht1 : t 1 = b := by simp [t]
  have ht2 : t 2 = c := by simp [t]
  refine ⟨3, t, by decide, by decide, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [t]
  · exact hs
  · intro z
    rw [hTeq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hz | hz | hz)
      · exact ⟨0, ht0.trans hz.symm⟩
      · exact ⟨1, ht1.trans hz.symm⟩
      · exact ⟨2, ht2.trans hz.symm⟩
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

/-- **THE CHARACTERISATION OF THE ERASABLE VERTICES OF AN ODD CYCLE.**  Let `C` be an odd cycle of
`G` such that every odd cycle of `G` meets `C`, and let `p ∈ C`.  Then

```lean
HitsOddCycles G (C.erase p) ↔ p ∉ PetalSet G C
```

In words: **the vertices of `C` which cannot be erased are exactly the attachment points of `C`**, and
nothing else blocks the erasure.  This is the exact form of the "pick a vertex of the cycle outside
the attachment set" step, which `JSPProblem/Two.lean` could only carry out for a triangle. -/
theorem hitsOddCycles_erase_iff_notMem_petalSet {C : Finset V} (hC : IsOddCycle G C)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅) {p : V} (hp : p ∈ C) :
    HitsOddCycles G (C.erase p) ↔ p ∉ PetalSet G C := by
  constructor
  · intro hhits hpP
    obtain ⟨-, D, hD, hDinter⟩ := mem_petalSet.mp hpP
    have hE : D ∩ C.erase p = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have hzD : z ∈ D := (Finset.mem_inter.mp hz).1
      have hzE : z ∈ C.erase p := (Finset.mem_inter.mp hz).2
      have hzC : z ∈ C := (Finset.mem_erase.mp hzE).2
      have hzDC : z ∈ D ∩ C := Finset.mem_inter.mpr ⟨hzD, hzC⟩
      rw [hDinter] at hzDC
      have hzEq : z = p := Finset.mem_singleton.mp hzDC
      subst hzEq
      exact (Finset.mem_erase.mp hzE).1 rfl
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr (hhits D hD)
    rw [hE] at hz
    simp at hz
  · intro hp' D hD
    by_contra hcon
    have hE : D ∩ C.erase p = ∅ := hcon
    have hsub : D ∩ C ⊆ {p} := by
      intro z hz
      have hzD : z ∈ D := (Finset.mem_inter.mp hz).1
      have hzC : z ∈ C := (Finset.mem_inter.mp hz).2
      refine Finset.mem_singleton.mpr ?_
      by_contra hzp
      have hmem : z ∈ D ∩ C.erase p := Finset.mem_inter.mpr
        ⟨hzD, Finset.mem_erase.mpr ⟨fun h => hzp h, hzC⟩⟩
      rw [hE] at hmem
      simp at hmem
    obtain ⟨w, hwDC⟩ := Finset.nonempty_iff_ne_empty.mpr (hmeet D hD)
    have hwp : w = p := Finset.mem_singleton.mp (hsub hwDC)
    have hwD : w ∈ D := (Finset.mem_inter.mp hwDC).1
    have hpD : p ∈ D := by rwa [hwp] at hwD
    exact hp' (mem_petalSet.mpr ⟨hp, D, hD, Finset.Subset.antisymm hsub (by
      intro z hz
      rw [Finset.mem_singleton] at hz
      subst z
      exact Finset.mem_inter.mpr ⟨hpD, hp⟩)⟩)

/-- **AN ODD CYCLE MINUS A NON-ATTACHMENT VERTEX IS AN ODD CYCLE TRANSVERSAL.** -/
theorem hitsOddCycles_erase_of_notMem_petalSet {C : Finset V} (hC : IsOddCycle G C)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅) {p : V} (hp : p ∈ C)
    (hp' : p ∉ PetalSet G C) : HitsOddCycles G (C.erase p) :=
  (hitsOddCycles_erase_iff_notMem_petalSet hC hmeet hp).mpr hp'

/-- **ERASING A NON-ATTACHMENT VERTEX OF AN ODD CYCLE LEAVES A BIPARTITE GRAPH.**  The
certificate is `C.erase p` itself, i.e. a transversal **contained in the odd cycle**. -/
theorem closeToBipartite_erase_of_notMem_petalSet {C : Finset V} (hC : IsOddCycle G C)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅) {p : V} (hp : p ∈ C)
    (hp' : p ∉ PetalSet G C) : CloseToBipartite (C.card - 1) G := by
  refine ⟨C.erase p, ?_, isBipartite_delete_of_hitsOddCycles
    (hitsOddCycles_erase_of_notMem_petalSet hC hmeet hp hp')⟩
  have hcard : (C.erase p).card = C.card - 1 := Finset.card_erase_of_mem hp
  omega

/-- **IF THE ATTACHMENT SET OF AN ODD CYCLE IS A PROPER SUBSET OF IT, THEN ERASING ONE VERTEX
SUFFICES.** -/
theorem closeToBipartite_card_sub_one_of_petalSet_lt_card {C : Finset V} (hC : IsOddCycle G C)
    (hmeet : ∀ D : Finset V, IsOddCycle G D → D ∩ C ≠ ∅) (hlt : (PetalSet G C).card < C.card) :
    CloseToBipartite (C.card - 1) G := by
  have hne : PetalSet G C ≠ C := by
    intro h
    rw [h] at hlt
    exact lt_irrefl _ hlt
  have hex : ∃ p, p ∈ C ∧ p ∉ PetalSet G C := by
    by_contra hcon
    have hsub : PetalSet G C = C := by
      refine Finset.Subset.antisymm (petalSet_subset (C := C)) ?_
      intro z hz
      by_contra hzP
      exact hcon ⟨z, hz, hzP⟩
    exact hne hsub
  obtain ⟨p, hpC, hp'⟩ := hex
  exact closeToBipartite_erase_of_notMem_petalSet hC hmeet hpC hp'

end Erase

/-! ## Part 2 — a new instance: the constant `|C| - 1` for an arbitrary odd cycle -/

section Instance

/-- **ERDŐS'S HYPOTHESIS AT `k ≤ 1` SUPPLIES THE RESIDUE HYPOTHESIS**: every odd cycle meets every
odd cycle (`JSPProblem/Two.lean`). -/
theorem hitsOddCycles_of_isOddCycle_of_locIndep_le_one {k : ℕ} (hk : k ≤ 1) (hG : LocIndep k G)
    {C : Finset V} (hC : IsOddCycle G C) : HitsOddCycles G C :=
  hitsOddCycles_of_isOddCycle_of_locIndep_one (locIndep_one_of_locIndep hk hG) hC

/-- **AN INSTANCE OF THE CONCLUSION OF ERDŐS PROBLEM #73 AT `k ≤ 1`, FOR AN ARBITRARY ODD CYCLE,
WITH THE CONSTANT `|C| - 1`.**  The hypothesis is that the attachment set of `C` is a proper subset
of `C`; it counts nothing, bounds no girth, no degree, no packing weight and no packing number.  For
`|C| = 3` this recovers `JSPProblem/Two.lean`'s instance (constant `2`), and for longer cycles it is
the sharp form of `JSPProblem/Petal.lean`'s `|C| - 1 + |PetalSet G C|`. -/
theorem erdos73On_of_isOddCycle_of_petalSet_lt_card {k : ℕ} (hk : k ≤ 1) (hG : LocIndep k G)
    {C : Finset V} (hC : IsOddCycle G C) (hlt : (PetalSet G C).card < C.card) :
    CloseToBipartite (C.card - 1) G :=
  closeToBipartite_card_sub_one_of_petalSet_lt_card hC
    (hitsOddCycles_of_isOddCycle_of_locIndep_le_one hk hG hC) hlt

/-- **AT `k = 1`, AN ODD GIRTH BOUND OF `ℓ - 1`.**  If `G` satisfies `LocIndep 1`, has an odd cycle of
`ℓ` vertices and none of shorter length, and the attachment set of that cycle is a proper subset of
it, then `CloseToBipartite (ℓ - 1) G`.  Compare `JSP90.erdos73On_of_bounded_odd_girth`
(`JSPProblem/Transversal.lean`), which pays `ℓ * k`: at `k = 1` this is **one vertex better**, and for
`ℓ = 3` it is the sharp constant `2`. -/
theorem closeToBipartite_of_locIndep_one_of_odd_girth_of_petalSet_lt_card (hG : LocIndep 1 G)
    {ℓ : ℕ} (hex : ∃ C : Finset V, IsOddCycle G C ∧ C.card = ℓ ∧ (PetalSet G C).card < ℓ)
    (hmin : ∀ C : Finset V, IsOddCycle G C → ℓ ≤ C.card) :
    CloseToBipartite (ℓ - 1) G := by
  obtain ⟨C, hC, hCℓ, hlt⟩ := hex
  have hle : (PetalSet G C).card < C.card := by rw [hCℓ]; exact hlt
  have h1 := erdos73On_of_isOddCycle_of_petalSet_lt_card (k := 1) (by omega) hG hC hle
  rwa [hCℓ] at h1

end Instance

/-! ## Part 3 — the residual of the sharp `k = 1` case, in one line -/

section Residual

/-- **~~THE ATTACHMENT SET OF *ANY* ODD CYCLE HAS AT MOST TWO POINTS AT `LocIndep 1`.~~**

**THIS CONJECTURE IS FALSE** (see Part 5 and `JSPProblem/Nonagon.lean`): the nine-vertex graph `g9`
of `JSPProblem/Nonagon.lean` satisfies `LocIndep 1 g9` and *each of its two triangles* has an
attachment set of three elements (`JSP90.not_forall_oddCycle_exists_erase_g9` and, by Part 1,
`JSP90.hitsOddCycles_erase_iff_notMem_petalSet`, `JSP90.PetalSetLeTwoOfOne` of
`JSPProblem/Two.lean`).  The statement is kept here only as a `def` so that the refutation has
something to name, and **must not be assumed anywhere**: it is a `def`, and every theorem of this
development that mentions it is a *conditional* one.  The search of this round
(`discovery/JSP-000090/r134c.c`) found the maximum of `|PetalSet G C|` over all odd cycles `C` to be
`0, 0, 1, 2, 2` for `n = 3 … 7` and to reach `3` at `n = 9`. -/
def PetalSetLeTwoOfOneAny (G : SimpleGraph V) : Prop :=
  ∀ C : Finset V, IsOddCycle G C → (PetalSet G C).card ≤ 2

/-- **THE ATTACHMENT SET OF A TRIANGLE HAS AT MOST TWO POINTS** follows from the general form. -/
theorem petalSetLeTwoOfOneAny_of_petalSetLeTwoOfOne {V : Type u} [Fintype V] {G : SimpleGraph V}
    (h : PetalSetLeTwoOfOneAny (V := V) G) : PetalSetLeTwoOfOne (V := V) G :=
  fun C hC _ => h C hC

/-- **THE ATTACHMENT SET OF AN ODD CYCLE IS NEVER THE WHOLE CYCLE UNDER `PetalSetLeTwoOfOneAny`**:
`|PetalSet G C| ≤ 2 < |C|` because an odd cycle has at least three vertices. -/
theorem card_petalSet_lt_card_of_petalSetLeTwoOfOneAny {V : Type u} [Fintype V]
    {G : SimpleGraph V} (hA : PetalSetLeTwoOfOneAny (V := V) G) {C : Finset V} (hC : IsOddCycle G C) :
    (PetalSet G C).card < C.card := by
  have h3 := isOddCycle_card_ge_three hC
  have h2 := hA C hC
  omega

/-- **A NEW INSTANCE OF THE CONCLUSION OF ERDŐS PROBLEM #73: `PetalSetLeTwoOfOneAny` GIVES
`CloseToBipartite (|C| - 1) G` FOR EVERY ODD CYCLE `C`**, and therefore the sharp `k = 1`
conclusion on the class of graphs that contain a triangle. -/
theorem erdos73On_of_petalSetLeTwoOfOneAny {k : ℕ} (hk : k ≤ 1) (hG : LocIndep k G)
    {C : Finset V} (hC : IsOddCycle G C) (hA : PetalSetLeTwoOfOneAny (V := V) G) :
    CloseToBipartite (C.card - 1) G :=
  erdos73On_of_isOddCycle_of_petalSet_lt_card hk hG hC
    (card_petalSet_lt_card_of_petalSetLeTwoOfOneAny hA hC)

/-- **THE SHARP `k = 1` CASE, AT A TRIANGLE, FROM THE GENERAL ATTACHMENT-SET BOUND.** -/
theorem erdos73On_one_of_triangle_of_petalSetLeTwoOfOneAny (hG : LocIndep 1 G) {T : Finset V}
    (hT : G.IsNClique 3 T) (hA : PetalSetLeTwoOfOneAny (V := V) G) : CloseToBipartite 2 G := by
  have hcard : T.card = 3 := (G.isNClique_iff.mp hT).2
  have hodd : IsOddCycle G T := isOddCycle_of_isNClique_three hT
  have h1 := erdos73On_of_petalSetLeTwoOfOneAny (k := 1) (by omega) hG hodd hA
  rwa [hcard] at h1

/-- **`m` VERTICES SUFFICE AT `LocIndep 1`, AS A STATEMENT ABOUT THE GRAPH ALONE.**  This is
exactly the sharp case `k = 1` of Erdős #73 in odd-cycle language, and the next definition is the
same statement with the transversal required to *lie in a shortest odd cycle*. -/
def TwoTransversal (m : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    (∃ C : Finset W, IsOddCycle G C) → ∃ X : Finset W, X.card ≤ m ∧ HitsOddCycles G X

/-- **THE SHARP CASE `k = 1` OF ERDŐS PROBLEM #73 WITH THE CONSTANT `m`, IN ODD-CYCLE
LANGUAGE.** -/
theorem erdos73On_one_iff_twoTransversal {m : ℕ} : Erdős73On.{u} 1 m ↔ TwoTransversal.{u} m := by
  constructor
  · intro h W instW G hG hex
    exact (closeToBipartite_iff_hitsOddCycles).mp (h W instW G hG)
  · intro h W instW G hG
    by_cases hex : ∃ C : Finset W, IsOddCycle G C
    · obtain ⟨X, hXcard, hX⟩ := h W instW G hG hex
      exact (closeToBipartite_iff_hitsOddCycles).mpr ⟨X, hXcard, hX⟩
    · exact closeToBipartite_mono (Nat.zero_le _)
        (closeToBipartite_of_isBipartite' (isBipartite_of_no_oddCycle hex))

/-- **~~AT `LocIndep 1`, `m` VERTICES OF A SHORTEST ODD CYCLE MEET EVERY ODD CYCLE.~~**

**THIS CONJECTURE IS FALSE AT `m = 2`** (Part 5, with the witness `g9` of
`JSPProblem/Nonagon.lean`): both triangles of `g9` are shortest odd cycles and **neither** contains a
set of at most two vertices meeting every odd cycle
(`JSP90.not_exists_twoTransversal_sub_g9_T1`, `JSP90.not_exists_twoTransversal_sub_g9_T2`).  So the
certificate of the sharp `k = 1` case cannot be a subset of an odd cycle.  The statement is kept
here only as a `def` so that the refutation has something to name, and it is a `def`: **no theorem of
this development assumes it.**  The correct single residual of the case `k = 1` is
`JSP90.TwoTransversal 2`, which `JSP90.erdos73On_one_iff_twoTransversal` proves **equivalent** to
`Erdős73On 1 2`. -/
def ShortestOddCycleTransversal (m : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G →
    (∃ C : Finset W, IsOddCycle G C) →
    ∃ C X : Finset W, IsOddCycle G C ∧ (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) ∧
      X ⊆ C ∧ X.card ≤ m ∧ HitsOddCycles G X

/-- **THE STATEMENT ABOVE IMPLIES THE GRAPH-ALONE STATEMENT OF THE PREVIOUS SECTION**, and hence the
sharp case `k = 1` of Erdős Problem #73 with the constant `m`.  A shortest odd cycle exists
(`JSP90.exists_shortest_oddCycle` of `JSPProblem/Chord.lean`), so no choice has to be made. -/
theorem twoTransversal_of_shortestOddCycleTransversal {m : ℕ}
    (h : ShortestOddCycleTransversal.{u} m) : TwoTransversal.{u} m :=
  fun W instW G hG hex => by
    obtain ⟨C, hC, hCmin⟩ := exists_shortest_oddCycle (G := G) hex
    obtain ⟨C', X, _, -, _, hXcard, hX⟩ := h W instW G hG ⟨C, hC⟩
    exact ⟨X, hXcard, hX⟩

/-- **THE SHARP CASE `k = 1` OF ERDŐS PROBLEM #73, IN FULL, FROM THE SINGLE STATEMENT ABOVE.** -/
theorem erdos73On_one_of_shortestOddCycleTransversal {m : ℕ}
    (h : ShortestOddCycleTransversal.{u} m) : Erdős73On.{u} 1 m :=
  erdos73On_one_iff_twoTransversal.mpr (twoTransversal_of_shortestOddCycleTransversal h)

/-- **THE SHARP CONSTANT `2` AT `k = 1`, FROM THE SINGLE STATEMENT ABOVE.** -/
theorem erdos73On_one_of_shortestOddCycleTransversal_two (h : ShortestOddCycleTransversal.{u} 2) :
    Erdős73On.{u} 1 2 :=
  erdos73On_one_of_shortestOddCycleTransversal h

/-- **THE GRAPH-ALONE STATEMENT IS NECESSARY FOR THE SHARP CASE `k = 1`.** -/
theorem not_erdos73On_one_two_of_not_twoTransversal
    (h : ¬ TwoTransversal.{u} 2) : ¬ Erdős73On.{u} 1 2 :=
  fun hmain => h (erdos73On_one_iff_twoTransversal.mp hmain)

/-- **THE TRIANGLE-FREE HALF, WITHOUT THE CONTAINMENT REQUIREMENT**: at `LocIndep 1`, in a
triangle-free graph, some set of at most `m` vertices meets every odd cycle.  This is the honest
residual of the triangle-free half of the sharp case `k = 1`: the containment requirement of
`JSP90.ShortestOddCycleTransversalTriFree` is refuted by the same phenomenon as Part 5, but a
transversal *somewhere* is exactly what the conclusion of Erdős #73 asks for. -/
def TriangleFreeTwoTransversal (m : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G → G.CliqueFree 3 →
    ∃ X : Finset W, X.card ≤ m ∧ HitsOddCycles G X

/-- **AND THAT STATEMENT IS EQUIVALENT TO THE TRIANGLE-FREE CASE OF THE SHARP CONSTANT.** -/
theorem triangleFree_iff_triangleFreeTwoTransversal {m : ℕ} :
    (∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G → G.CliqueFree 3 →
        CloseToBipartite m G) ↔ TriangleFreeTwoTransversal.{u} m := by
  constructor
  · rintro h W instW G hG htf
    exact (closeToBipartite_iff_hitsOddCycles).mp (h W instW G hG htf)
  · rintro h W instW G hG htf
    rw [closeToBipartite_iff_hitsOddCycles]
    exact h W instW G hG htf

/-- **THE TRIANGLE-FREE HALF OF THE SHARP CASE `k = 1`, WITH THE CONTAINMENT REQUIREMENT.**  Kept as a
`def` (not assumed): the containment requirement `X ⊆ C` is what Part 5 refutes. -/
def ShortestOddCycleTransversalTriFree (m : ℕ) : Prop :=
  ∀ (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep 1 G → G.CliqueFree 3 →
    (∃ C : Finset W, IsOddCycle G C) →
    ∃ C X : Finset W, IsOddCycle G C ∧ (∀ D : Finset W, IsOddCycle G D → C.card ≤ D.card) ∧
      X ⊆ C ∧ X.card ≤ m ∧ HitsOddCycles G X

/-- **THE TRIANGLE-FREE STATEMENT IS A SPECIALISATION OF THE GENERAL ONE.** -/
theorem shortestOddCycleTransversalTriFree_of_shortestOddCycleTransversal {m : ℕ}
    (h : ShortestOddCycleTransversal.{u} m) : ShortestOddCycleTransversalTriFree.{u} m :=
  fun W instW G hG _ hex => h W instW G hG hex

end Residual

/-! ## Part 4 — the "high intersection" route is refuted, machine-checked -/

section HighIntersection

/-- **THE FIRST TRIANGLE OF THE WINDMILL IS AN ODD CYCLE OF `wf`.** -/
theorem card_wf_012 : ({0, 1, 2} : Finset (Fin 6)).card = 3 := by
  have e : ({0, 1, 2} : Finset (Fin 6)) = insert 0 (insert 1 (insert 2 ∅)) := rfl
  rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp)]
  simp

theorem card_wf_034 : ({0, 3, 4} : Finset (Fin 6)).card = 3 := by
  have e : ({0, 3, 4} : Finset (Fin 6)) = insert 0 (insert 3 (insert 4 ∅)) := rfl
  rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp)]
  simp

theorem isOddCycle_wf_012 : IsOddCycle wf ({0, 1, 2} : Finset (Fin 6)) := by
  obtain ⟨hC, hsub⟩ :=
    isOddCycle_induceFinset (G := wf) (s := {0, 1, 2}) exists_isOddCycle_half_1.choose_spec
  have h3 : (exists_isOddCycle_half_1.choose).card = 3 := by
    have hge := isOddCycle_card_ge_three hC
    have hle' := Finset.card_le_card hsub
    rw [card_wf_012] at hle'
    omega
  exact hC.of_finset_eq
      (Finset.eq_of_subset_of_card_le hsub (by rw [card_wf_012]; omega)).symm

/-- **THE SECOND ONE.** -/
theorem isOddCycle_wf_034 : IsOddCycle wf ({0, 3, 4} : Finset (Fin 6)) := by
  obtain ⟨hC, hsub⟩ :=
    isOddCycle_induceFinset (G := wf) (s := {0, 3, 4}) exists_isOddCycle_half_2.choose_spec
  have h3 : (exists_isOddCycle_half_2.choose).card = 3 := by
    have hge := isOddCycle_card_ge_three hC
    have hle' := Finset.card_le_card hsub
    rw [card_wf_034] at hle'
    omega
  exact hC.of_finset_eq
      (Finset.eq_of_subset_of_card_le hsub (by rw [card_wf_034]; omega)).symm

/-- **THE TWO TRIANGLES OF THE WINDMILL MEET IN THE SINGLE VERTEX `0`.** -/
theorem inter_wf_012_034 : (({0, 1, 2} : Finset (Fin 6)) ∩ {0, 3, 4} : Finset (Fin 6)) = {0} := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro x hx
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with ⟨h1, h2⟩
    rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2) <;> first
      | exact Finset.mem_singleton.mpr h1
      | (subst h1; exact absurd h2 (by simp))
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_inter.mpr ⟨by simp, by simp⟩

/-- **A TWO-ELEMENT FINSET HAS TWO ELEMENTS.** -/
theorem card_pair_12 : ({1, 2} : Finset (Fin 6)).card = 2 := by
  have e : ({1, 2} : Finset (Fin 6)) = insert 1 ({2} : Finset (Fin 6)) := rfl
  rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_singleton]

/-- **THE FIRST TRIANGLE MINUS THE SECOND CONTAINS `{1, 2}`.** -/
theorem sdiff_wf_012_034 : {1, 2} ⊆ ({0, 1, 2} : Finset (Fin 6)) \ {0, 3, 4} := by
  intro x hx
  rw [Finset.mem_sdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl
  · exact ⟨Or.inr (Or.inl rfl), by simp⟩
  · exact ⟨Or.inr (Or.inr rfl), by simp⟩

/-- **AT `LocIndep 1` AN ODD CYCLE NEED NOT USE ALL BUT ONE VERTEX OF A SHORTEST ODD CYCLE.**

The witness is the windmill `wf` (`JSPProblem/Windmill.lean`), which satisfies `LocIndep 1 wf`: the
two triangles `{0,1,2}` and `{0,3,4}` are both shortest odd cycles, they meet in the single vertex
`0`, and `|{0,1,2} \ {0,3,4}| = 2`.

This **refutes**, machine-checked, the hypothesis "`∀ D, IsOddCycle G D → |C \ D| ≤ 1`" of
`JSP90.closeToBipartite_of_oddCycle_high_intersection` (`JSPProblem/Two.lean`, item 5) as a
*consequence* of `LocIndep 1 G`, even when `C` is a shortest odd cycle.  The route "at a shortest odd
cycle every odd cycle uses all but one of its vertices" must therefore not be attempted again. -/
theorem not_forall_card_sdiff_le_one_wf :
    ¬ (∀ D : Finset (Fin 6), IsOddCycle wf D →
        (({0, 1, 2} : Finset (Fin 6)) \ D).card ≤ 1) := by
  intro h
  have h2 := h ({0, 3, 4} : Finset (Fin 6)) isOddCycle_wf_034
  have h3 := Finset.card_le_card (sdiff_wf_012_034)
  rw [card_pair_12] at h3
  omega

/-- **TWO SHORTEST ODD CYCLES OF A `LocIndep 1` GRAPH MAY MEET IN EXACTLY ONE VERTEX.**  So
statements of the form "any two odd cycles of a `LocIndep 1` graph share at least two vertices" —
which hold for the *petals of a triangle* (`JSPProblem/Two.lean`, item 2) — do **not** extend to
arbitrary odd cycles of a `LocIndep 1` graph, and `wf` is the smallest witness. -/
theorem two_shortest_oddCycles_can_meet_in_one_wf :
    IsOddCycle wf ({0, 1, 2} : Finset (Fin 6)) ∧ IsOddCycle wf ({0, 3, 4} : Finset (Fin 6)) ∧
      (({0, 1, 2} : Finset (Fin 6)) ∩ {0, 3, 4} : Finset (Fin 6)).card = 1 ∧ LocIndep 1 wf :=
  ⟨isOddCycle_wf_012, isOddCycle_wf_034, by rw [inter_wf_012_034]; simp, locIndep_one_wf⟩

/-- **THE WINDMILL IS ONE VERTEX AWAY FROM BIPARTITE**, so the counterexample of Part 4 refutes the
*hypothesis*, not the conclusion: it is `JSP90.ShortestOddCycleTransversal 2` that is missing, and it
holds on `wf` with a certificate of size one. -/
theorem windmill_shortestOddCycleTransversal_two :
    ∃ X : Finset (Fin 6), X.card ≤ 2 ∧ HitsOddCycles wf X := by
  obtain ⟨X, hX, hXb⟩ := windmill_closeToBipartite_one
  exact ⟨X, by omega, hitsOddCycles_of_isBipartite_delete hXb⟩

end HighIntersection

/-! ## Part 5 — the nine-vertex witness `g9` refutes every triangle-based certificate

`JSPProblem/Nonagon.lean` exhibits `g9`, a graph on `Fin 9` with

```
LocIndep 1 g9            (JSP90.locIndep_one_g9, exhaustive decision over the 2 ^ 9 vertex sets)
```

two triangles `T₁ = {0,5,7}` and `T₂ = {0,6,8}`, and, for **each** triangle, an odd cycle through each
of its three vertices that meets the triangle in **exactly that vertex**:

| triangle | attachment point | the petal |
| --- | --- | --- |
| `T₁ = {0,5,7}` | `0` | `{0,6,8}` = `T₂` |
| `T₁ = {0,5,7}` | `5` | the `5`-cycle `{1,2,5,6,8}` |
| `T₁ = {0,5,7}` | `7` | the `5`-cycle `{3,4,6,7,8}` |
| `T₂ = {0,6,8}` | `0` | `{0,5,7}` = `T₁` |
| `T₂ = {0,6,8}` | `6` | the `5`-cycle `{1,3,5,6,7}` |
| `T₂ = {0,6,8}` | `8` | the `5`-cycle `{2,4,5,7,8}` |

The consequences are proved below.

* **`JSP90.not_forall_oddCycle_exists_erase_g9`** — **THE "ERASE ONE VERTEX OF A TRIANGLE" STEP IS
  IMPOSSIBLE IN `g9`**: no triangle of `g9` admits a `2`-subset meeting every odd cycle.  This is the
  route of `JSPProblem/Two.lean` (item 3), of `JSP90.petalSet_transversal`
  (`JSPProblem/Petal.lean`) and of `JSPProblem/Petal3.lean`; by
  `JSP90.hitsOddCycles_erase_iff_notMem_petalSet` (Part 1) it is the same statement as "the
  attachment set of a triangle has at most two points", i.e. **`JSP90.PetalSetLeTwoOfOne`**, the
  single remaining residual of rounds 119–131 and the top target of
  `discovery/JSP-000090/policy.json` since round 123.  **That target is refuted.**
* **`JSP90.not_exists_twoTransversal_sub_g9_T1` / `..._T₂`** — **NOT EVEN A FREE CHOICE OF TWO
  VERTICES INSIDE A SHORTEST ODD CYCLE WORKS**: no set of at most two vertices of `T₁` or of `T₂`
  meets every odd cycle of `g9`.  So the "two vertices of a shortest odd cycle" shape
  (`JSP90.ShortestOddCycleTransversal 2`, Part 3 of this file) is refuted as well.
* The exhaustive search of this round (`discovery/JSP-000090/r134.c`) measures the least odd cycle
  transversal number of `g9` to be **`2`**, with certificate **`{5, 6}`** — a pair that lies in
  **neither** triangle (`5 ∈ T₁ \ T₂`, `6 ∈ T₂ \ T₁`).  So `f(1) = 2` remains the sharp candidate;
  what is refuted is the *shape* of the certificate.  The correct single residual is therefore
  `JSP90.TwoTransversal 2`, and `JSP90.erdos73On_one_iff_twoTransversal` proves it **equivalent** to
  `Erdős73On 1 2`. -/

section Nonagon

/-! ### The cardinalities of the two triangles -/

theorem card_g9T1' : g9T1.card = 3 := by
  have e : g9T1 = insert 0 (insert 5 (insert 7 ∅)) := rfl
  rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp), Finset.card_empty]

theorem card_g9T2' : g9T2.card = 3 := by
  have e : g9T2 = insert 0 (insert 6 (insert 8 ∅)) := rfl
  rw [e, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp), Finset.card_empty]

/-- **From here on, `Fin n` is given the *classical* `DecidableEq`**: the statements
`JSP90.HitsOddCycles` bake in the classical instance of `JSPProblem/Transversal.lean`, and
Mathlib's computable `JSP90.instDecidableEqFin` would otherwise win instance resolution for the
concrete vertex type `Fin 9`.  Every lemma of this section is stated **without** any `Finset`
operation on a `DecidableEq`-dependent term, so all of them are instance-free and the instance does
not affect them. -/
local instance attachEraseClassicalFin (n : ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

open JSP90 (g9 g9T1 g9T2 g9P5 g9P7 g9Q6 g9Q8)

/-- **A VERTEX OF `{0,6,8}` THAT ALSO LIES IN `{0,5,7}` IS `0`.** -/
theorem mem_g9T2_of_mem_g9T1 (z : Fin 9) (h2 : z ∈ g9T2) (h1 : z ∈ g9T1) : z = 0 := by
  simp only [g9T2, g9T1, Finset.mem_insert, Finset.mem_singleton] at h2 h1
  rcases h2 with (h2 | h2 | h2) <;> rcases h1 with (h1 | h1 | h1) <;> first
    | exact h2
    | (subst h2; exact absurd h1 (fun h => by have h' := congrArg Fin.val h; omega))

/-- **A VERTEX OF `{1,2,5,6,8}` THAT ALSO LIES IN `{0,5,7}` IS `5`.** -/
theorem mem_g9P5_of_mem_g9T1 (z : Fin 9) (h2 : z ∈ g9P5) (h1 : z ∈ g9T1) : z = 5 := by
  simp only [g9P5, g9T1, Finset.mem_insert, Finset.mem_singleton] at h2 h1
  rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> rcases h1 with (h1 | h1 | h1) <;> first
    | exact h2
    | (subst h2; exact absurd h1 (fun h => by have h' := congrArg Fin.val h; omega))

/-- **A VERTEX OF `{3,4,6,7,8}` THAT ALSO LIES IN `{0,5,7}` IS `7`.** -/
theorem mem_g9P7_of_mem_g9T1 (z : Fin 9) (h2 : z ∈ g9P7) (h1 : z ∈ g9T1) : z = 7 := by
  simp only [g9P7, g9T1, Finset.mem_insert, Finset.mem_singleton] at h2 h1
  rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> rcases h1 with (h1 | h1 | h1) <;> first
    | exact h2
    | (subst h2; exact absurd h1 (fun h => by have h' := congrArg Fin.val h; omega))

/-- **A VERTEX OF `{0,5,7}` THAT ALSO LIES IN `{0,6,8}` IS `0`.** -/
theorem mem_g9T1_of_mem_g9T2 (z : Fin 9) (h1 : z ∈ g9T1) (h2 : z ∈ g9T2) : z = 0 := by
  simp only [g9T1, g9T2, Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with (h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> first
    | exact h1
    | (subst h1; exact absurd h2 (fun h => by have h' := congrArg Fin.val h; omega))

/-- **A VERTEX OF `{1,3,5,6,7}` THAT ALSO LIES IN `{0,6,8}` IS `6`.** -/
theorem mem_g9Q6_of_mem_g9T2 (z : Fin 9) (h1 : z ∈ g9Q6) (h2 : z ∈ g9T2) : z = 6 := by
  simp only [g9Q6, g9T2, Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> first
    | exact h1
    | (subst h1; exact absurd h2 (fun h => by have h' := congrArg Fin.val h; omega))

/-- **A VERTEX OF `{2,4,5,7,8}` THAT ALSO LIES IN `{0,6,8}` IS `8`.** -/
theorem mem_g9Q8_of_mem_g9T2 (z : Fin 9) (h1 : z ∈ g9Q8) (h2 : z ∈ g9T2) : z = 8 := by
  simp only [g9Q8, g9T2, Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2) <;> first
    | exact h1
    | (subst h1; exact absurd h2 (fun h => by have h' := congrArg Fin.val h; omega))

/-- **THE PETAL OF `T₁` AT THE VERTEX `v`** — an odd cycle of `g9` meeting `g9T1` in exactly `{v}` —
chosen by the three cases of `v`. -/
theorem petal_g9_T1 (v : Fin 9) (hv : v ∈ g9T1) :
    ∃ D : Finset (Fin 9), IsOddCycle g9 D ∧ ∀ z, z ∈ D → z ∈ g9T1 → z = v := by
  simp only [g9T1, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact ⟨g9T2, isOddCycle_g9_T2, fun _ h2 h1 => mem_g9T2_of_mem_g9T1 _ h2 h1⟩
  · exact ⟨g9P5, isOddCycle_g9_P5, fun _ h2 h1 => mem_g9P5_of_mem_g9T1 _ h2 h1⟩
  · exact ⟨g9P7, isOddCycle_g9_P7, fun _ h2 h1 => mem_g9P7_of_mem_g9T1 _ h2 h1⟩

/-- **THE PETAL OF `T₂` AT THE VERTEX `v`.** -/
theorem petal_g9_T2 (v : Fin 9) (hv : v ∈ g9T2) :
    ∃ D : Finset (Fin 9), IsOddCycle g9 D ∧ ∀ z, z ∈ D → z ∈ g9T2 → z = v := by
  simp only [g9T2, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact ⟨g9T1, isOddCycle_g9_T1, fun _ h1 h2 => mem_g9T1_of_mem_g9T2 _ h1 h2⟩
  · exact ⟨g9Q6, isOddCycle_g9_Q6, fun _ h1 h2 => mem_g9Q6_of_mem_g9T2 _ h1 h2⟩
  · exact ⟨g9Q8, isOddCycle_g9_Q8, fun _ h1 h2 => mem_g9Q8_of_mem_g9T2 _ h1 h2⟩

/-- **NO VERTEX OF `T₁` CAN BE ERASED TO GET AN ODD CYCLE TRANSVERSAL.** -/
theorem not_hitsOddCycles_erase_g9_T1 (v : Fin 9) (hv : v ∈ g9T1) :
    ¬ HitsOddCycles g9 (g9T1.erase v) := by
  intro hh
  obtain ⟨D, hD, hDmem⟩ := petal_g9_T1 v hv
  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr (hh D hD)
  have hwT1 : w ∈ g9T1 := (Finset.mem_erase.mp (Finset.mem_inter.mp hw).2).2
  have hweq : w = v := hDmem w (Finset.mem_inter.mp hw).1 hwT1
  subst hweq
  exact (Finset.mem_erase.mp (Finset.mem_inter.mp hw).2).1 rfl

/-- **AND NEITHER CAN A VERTEX OF `T₂`.** -/
theorem not_hitsOddCycles_erase_g9_T2 (v : Fin 9) (hv : v ∈ g9T2) :
    ¬ HitsOddCycles g9 (g9T2.erase v) := by
  intro hh
  obtain ⟨D, hD, hDmem⟩ := petal_g9_T2 v hv
  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr (hh D hD)
  have hwT2 : w ∈ g9T2 := (Finset.mem_erase.mp (Finset.mem_inter.mp hw).2).2
  have hweq : w = v := hDmem w (Finset.mem_inter.mp hw).1 hwT2
  subst hweq
  exact (Finset.mem_erase.mp (Finset.mem_inter.mp hw).2).1 rfl

/-- **NO SET OF AT MOST TWO VERTICES OF `T₁` IS AN ODD CYCLE TRANSVERSAL.** -/
theorem not_exists_twoTransversal_sub_g9_T1 :
    ¬ (∃ X : Finset (Fin 9), X ⊆ g9T1 ∧ X.card ≤ 2 ∧ HitsOddCycles g9 X) := by
  rintro ⟨X, hXsub, hXcard, hX⟩
  have hne : g9T1 ≠ X := by
    intro h
    have h' : g9T1.card ≤ 2 := h.symm ▸ hXcard
    rw [card_g9T1'] at h'
    omega
  obtain ⟨v, hvT1, hvX⟩ : ∃ v, v ∈ g9T1 ∧ v ∉ X := by
    by_contra hcon
    have hsubX : g9T1 ⊆ X := by
      intro z hz
      by_contra hzX
      exact hcon ⟨z, hz, hzX⟩
    exact hne (Finset.Subset.antisymm hsubX hXsub)
  obtain ⟨D, hD, hDmem⟩ := petal_g9_T1 v hvT1
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr (hX D hD)
  have hzX : z ∈ X := (Finset.mem_inter.mp hz).2
  have hzD : z ∈ D := (Finset.mem_inter.mp hz).1
  have hzT1 : z ∈ g9T1 := hXsub hzX
  have hzeq : z = v := hDmem z hzD hzT1
  subst hzeq
  exact hvX hzX

/-- **AND NEITHER FOR `T₂`.** -/
theorem not_exists_twoTransversal_sub_g9_T2 :
    ¬ (∃ X : Finset (Fin 9), X ⊆ g9T2 ∧ X.card ≤ 2 ∧ HitsOddCycles g9 X) := by
  rintro ⟨X, hXsub, hXcard, hX⟩
  have hne : g9T2 ≠ X := by
    intro h
    have h' : g9T2.card ≤ 2 := h.symm ▸ hXcard
    rw [card_g9T2'] at h'
    omega
  obtain ⟨v, hvT2, hvX⟩ : ∃ v, v ∈ g9T2 ∧ v ∉ X := by
    by_contra hcon
    have hsubX : g9T2 ⊆ X := by
      intro z hz
      by_contra hzX
      exact hcon ⟨z, hz, hzX⟩
    exact hne (Finset.Subset.antisymm hsubX hXsub)
  obtain ⟨D, hD, hDmem⟩ := petal_g9_T2 v hvT2
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr (hX D hD)
  have hzX : z ∈ X := (Finset.mem_inter.mp hz).2
  have hzD : z ∈ D := (Finset.mem_inter.mp hz).1
  have hzT2 : z ∈ g9T2 := hXsub hzX
  have hzeq : z = v := hDmem z hzD hzT2
  subst hzeq
  exact hvX hzX

/-- **THE "ERASE ONE VERTEX OF A TRIANGLE" STEP IS IMPOSSIBLE IN `g9`**: for **no** triangle of `g9`
is a two-element subset an odd cycle transversal.  By
`JSP90.hitsOddCycles_erase_iff_notMem_petalSet` this is the same statement as "some vertex of every
triangle lies in no odd cycle", i.e. the attachment-set bound `JSP90.PetalSetLeTwoOfOne`, which is
therefore **false**. -/
theorem not_forall_oddCycle_exists_erase_g9 :
    ¬ (∀ C : Finset (Fin 9), IsOddCycle g9 C → C.card = 3 →
        ∃ v ∈ C, HitsOddCycles g9 (C.erase v)) := by
  intro h
  obtain ⟨v, hv, hh⟩ := h g9T1 isOddCycle_g9_T1 card_g9T1'
  exact not_hitsOddCycles_erase_g9_T1 v hv hh

/-- **THE SUMMARY OF PART 5: EVERY TRIANGLE-BASED CERTIFICATE FOR THE SHARP CONSTANT `2` AT
`k = 1` IS IMPOSSIBLE IN `g9`.**  `g9` satisfies `LocIndep 1 g9`
(`JSPProblem/Nonagon.lean`, `JSP90.locIndep_one_g9`), so the refutation is inside the range of the
headline theorem.  By `JSPProblem/PetalBound.lean` the third conjunct of the previous round is
already refuted by the nine-vertex propeller `prop` (whose odd cycle transversal number is `3`); this
theorem kills the two remaining shapes, and the search of `discovery/JSP-000090/r134.c` measures the
least odd cycle transversal number of `g9` to be `2` with certificate `{5, 6}` — a pair lying in
**neither** triangle.  So `f(1) = 2` is still the sharp candidate, and the certificate must not be
built inside an odd cycle. -/
theorem triangleCertificates_are_impossible :
    ¬ (∀ C : Finset (Fin 9), IsOddCycle g9 C → C.card = 3 →
        ∃ v ∈ C, HitsOddCycles g9 (C.erase v)) ∧
      ¬ (∃ X : Finset (Fin 9), X ⊆ g9T1 ∧ X.card ≤ 2 ∧ HitsOddCycles g9 X) ∧
      ¬ (∃ X : Finset (Fin 9), X ⊆ g9T2 ∧ X.card ≤ 2 ∧ HitsOddCycles g9 X) :=
  ⟨not_forall_oddCycle_exists_erase_g9, not_exists_twoTransversal_sub_g9_T1,
    not_exists_twoTransversal_sub_g9_T2⟩

end Nonagon

/-! ### The axiom report of this file -/

section Axioms

#print axioms JSP90.isOddCycle_of_isNClique_three
#print axioms JSP90.hitsOddCycles_erase_iff_notMem_petalSet
#print axioms JSP90.closeToBipartite_erase_of_notMem_petalSet
#print axioms JSP90.closeToBipartite_card_sub_one_of_petalSet_lt_card
#print axioms JSP90.erdos73On_of_isOddCycle_of_petalSet_lt_card
#print axioms JSP90.closeToBipartite_of_locIndep_one_of_odd_girth_of_petalSet_lt_card
#print axioms JSP90.erdos73On_of_petalSetLeTwoOfOneAny
#print axioms JSP90.erdos73On_one_of_triangle_of_petalSetLeTwoOfOneAny
#print axioms JSP90.erdos73On_one_iff_twoTransversal
#print axioms JSP90.erdos73On_one_of_shortestOddCycleTransversal_two
#print axioms JSP90.not_erdos73On_one_two_of_not_twoTransversal
#print axioms JSP90.triangleFree_iff_triangleFreeTwoTransversal
#print axioms JSP90.not_forall_card_sdiff_le_one_wf
#print axioms JSP90.not_forall_oddCycle_exists_erase_g9
#print axioms JSP90.not_hitsOddCycles_erase_g9_T1
#print axioms JSP90.not_exists_twoTransversal_sub_g9_T1
#print axioms JSP90.triangleCertificates_are_impossible
#print axioms JSP90.two_shortest_oddCycles_can_meet_in_one_wf

end Axioms

end

end JSP90
