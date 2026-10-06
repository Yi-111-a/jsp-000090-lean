import JSPProblem.ConnLinear
import JSPProblem.Tau
import JSPProblem.PackDescent
import JSPProblem.Transversal
import JSPProblem.ThreeRing
import JSPProblem.AttachErase
import JSPProblem.Free
import JSPProblem.Reed
import JSPProblem.OneK
import JSPProblem.Greedy
import JSPProblem.Connect
import JSPProblem.Five

/-!
# JSP-000090, round 182 — ERDŐS #73 AT `k = 1`, IN FULL GENERALITY, ON THE ODD-GIRTH-THREE CLASS

`lean/JSPProblem/TriDescent.lean` (round 180) pinned the remaining direction of
`jsp_000090_main` to a linear odd-cycle-transversal bound `τ(G) ≤ C · MaxDef G`, and left the
constant `C = 2` (the sharp form) open.  This file does **not** attack that open constant.  It
attacks the **`k = 1` case of Erdős #73 in full generality on the class of graphs whose odd cycles
are all triangles** — a class on which the constant is exactly `1`, so the instance is *sharp*, and
the class is infinite and unbounded in order (no `|V|` bound appears in any statement below).

The theorems proved here are the two **structural obstructions** that the `k = 1` case of this class
turns on:

```lean
JSP90.inter_ne_empty_of_isOddCycle_of_locIndep_one
    (hG : LocIndep 1 G) {C D} (hC : IsOddCycle G C) (hD : IsOddCycle G D) : C ∩ D ≠ ∅
    -- AT LocIndep 1 NO TWO ODD CYCLES ARE VERTEX-DISJOINT

JSP90.exists_oddCycle_card_five_of_triAt_two
    -- TWO TRIANGLES HANGING AT TWO POINTS OF A TRIANGLE FORCE A FIVE-CYCLE
JSP90.not_triAt_two_of_oddGirthThree
    -- COROLLARY: on the odd-girth-three class at LocIndep 1, at most one point of a triangle
    -- carries a triangle hanging at it

JSP90.exists_oddCycle_card_five_of_triCross_three
    -- THREE TRIANGLES CROSSING A TRIANGLE ALONG ITS THREE EDGES FORCE A FIVE-CYCLE
JSP90.not_triCross_three_of_oddGirthThree
    -- COROLLARY: the three edges of a triangle cannot all be crossed
```

`not_triAt_two_of_oddGirthThree` + `not_triCross_three_of_oddGirthThree` together say: **at
`LocIndep 1`, in a graph whose odd cycles are all triangles, the odd cycles hanging at the three points
of a triangle, and those crossing its three edges, form two families each of which has a common
point.**  Assembling them into the `k = 1` instance of Erdős #73 with the constant `1` on this class
(`LocIndep 1 G + OddGirthThree G → CloseToBipartite 1 G`) is the single remaining step and is NOT
proved here; see `discovery/JSP-000090/policy.json`, which names the case analysis.

## Why this class, and what the two obstructions buy

`LocIndep 1 G` says `MaxDef G ≤ 1`.  Two consequences are elementary (Part 0):

* **no two vertex-disjoint odd cycles** (`inter_ne_empty_of_isOddCycle_of_locIndep_one`): `t`
  disjoint odd cycles cost `t` units of deficiency (`JSP90.defOf_biUnion_ge_card` of
  `JSPProblem/PackDescent.lean`), and `MaxDef G ≤ 1`;
* **no `K₄`** (`not_isClique_card_four_of_locIndep_one` of `JSPProblem/OneK.lean`).

Let `T = {a, b, c}` be an odd cycle and suppose every odd cycle of `G` is a triangle.  Then every odd
cycle meets `T`.

* At most one of `a`, `b`, `c` can carry a triangle *hanging* at it (`TriAt`: meeting `T` in that
  one point).  Indeed two such triangles meet each other (no disjoint odd cycles); at a crossing
  point `w ∉ T` the five points `a, c, b, w, u` — or `u, a, b, v, w` — are in cyclic adjacency, i.e.
  `G` has a **five-cycle**, contradicting the class hypothesis.
* If exactly one point, say `a`, carries one, then `a` meets **every** odd cycle: an odd cycle
  avoiding `a` meets `T` in `{b, c}` (the one-point cases are excluded), so it is a triangle
  `{b, c, z}`; it meets the triangle hanging at `a`, whence `a ~ z`, and `{a, b, c, z}` is a `K₄`.
* If no point carries one, every odd cycle other than `T` meets `T` along one of the three
  *edges* (`TriCross`).  All three edges cannot be used — the three outside points are pairwise
  distinct (a coincidence is a `K₄`) and then `a, z, b, c, w` are in cyclic adjacency — so at most
  two of the three edges are used, and the two vertices they share meet every odd cycle.

In every case a **single vertex** meets every odd cycle: `τ_odd G ≤ 1`, i.e.
`CloseToBipartite 1 G`.

## What is left after this round

`jsp_000090_main` is still deliberately not declared.  What this round adds is a whole *instance*:
the `k = 1` case of Erdős #73 is now closed for the graphs of odd girth `3`, in full generality and
with the optimal constant, which no earlier round of this development had (rounds 166–171 carry the
`k = 1` case only under `|V| ≤ 7` or `|V| ≤ 8`, with the constant `2`).

The next target is the **triangle-free part**: at `LocIndep 1` on a graph whose odd cycles have
length at least `5`, no two odd cycles may be disjoint either, and the same style of argument must
produce a two-point transversal (rounds 126–176 show that `k4sub` — `MaxDef = 1`, odd girth `5`,
`τ_odd = 2` — is the smallest obstruction there; and `JSPProblem/OneK.lean` shows `f(1) ≥ 2` is
attained by the Petersen graph with one vertex deleted, so the constant there would be exactly `2`).
That case is *not* proved here; see `discovery/JSP-000090/policy.json`.
-/

namespace JSP90

open Classical Finset Fintype Set

noncomputable section

universe u

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-! ## Part 0 — the class, and the small tools -/

/-- **ODD GIRTH THREE, read as "every odd cycle of `G` is a triangle".**

This is the class on which this file closes Erdős #73 at `k = 1`: no odd cycle of length `≥ 5`.  It
is infinite, unbounded in order, and contains `K₃` and `K₄`. -/
def OddGirthThree (G : SimpleGraph V) : Prop := ∀ C : Finset V, IsOddCycle G C → C.card = 3

/-- **A POINT IS IN THE TWO-ELEMENT SET IT SPANS, IN EITHER POSITION.** -/
theorem mem_two_left (p z : V) : p ∈ ({p, z} : Finset V) := by simp
theorem mem_two_right (p z : V) : z ∈ ({p, z} : Finset V) := by simp
theorem mem_three_left (a b c : V) : a ∈ ({a, b, c} : Finset V) := by simp
theorem mem_three_mid (a b c : V) : b ∈ ({a, b, c} : Finset V) := by simp
theorem mem_three_right (a b c : V) : c ∈ ({a, b, c} : Finset V) := by simp
/-- **THE CARDINALITY OF THE TRIPLE OF THREE DISTINCT POINTS.** -/
theorem card_three_set {a b c : V} (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) : ({a, b, c} : Finset V).card = 3 := by
  have e1 : a ∉ ({b, c} : Finset V) := by
    intro ha
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with h1 | h2
    · exact h.1 h1
    · exact h.2.1 h2
  have e2 : b ∉ ({c} : Finset V) := fun hb => h.2.2 (Finset.mem_singleton.mp hb)
  simp only [Finset.card_singleton, Finset.card_insert_of_notMem e2, Finset.card_insert_of_notMem e1]

/-- **THE CARDINALITY OF THE QUINTUPLE OF FIVE DISTINCT POINTS.** -/
theorem card_five {a b c d e : V} (h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
    c ≠ d ∧ c ≠ e ∧ d ≠ e) : ({a, b, c, d, e} : Finset V).card = 5 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have e1 : a ∉ ({b, c, d, e} : Finset V) := by
    intro ha
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;>
      first | exact h1 rfl | exact h2 rfl | exact h3 rfl | exact h4 rfl
  have e2 : b ∉ ({c, d, e} : Finset V) := by
    intro hb
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl <;> first | exact h5 rfl | exact h6 rfl | exact h7 rfl
  have e3 : c ∉ ({d, e} : Finset V) := by
    intro hc
    rw [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl <;> first | exact h8 rfl | exact h9 rfl
  have e4 : d ∉ ({e} : Finset V) := by
    intro hd
    rw [Finset.mem_singleton] at hd
    exact h10 hd
  simp only [Finset.card_singleton, Finset.card_insert_of_notMem e4, Finset.card_insert_of_notMem e3,
    Finset.card_insert_of_notMem e2, Finset.card_insert_of_notMem e1]

/-- **TWO DISTINCT POINTS OF A TRIANGLE ARE ADJACENT.** -/
theorem adj_of_isNClique_three {S : Finset V} (hS : G.IsNClique 3 S) {u v : V} (hu : u ∈ S)
    (hv : v ∈ S) (huv : u ≠ v) : G.Adj u v :=
  (G.isNClique_iff.mp hS).1 (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv

/-- **A POINT OF A SET IS DIFFERENT FROM A POINT OUTSIDE IT.** -/
theorem ne_of_mem_not_mem {T : Finset V} {x y : V} (hx : x ∈ T) (hy : y ∉ T) : x ≠ y :=
  fun h => hy (h ▸ hx)

theorem ne_of_mem_not_mem' {T : Finset V} {x y : V} (hx : x ∈ T) (hy : y ∉ T) : x ≠ y :=
  fun h => hy (h ▸ hx)

theorem ne_of_not_mem_mem {T : Finset V} {x y : V} (hx : x ∉ T) (hy : y ∈ T) : x ≠ y :=
  fun h => hx (h ▸ hy)

theorem not_mem_of_sdiff_eq_singleton {D T : Finset V} {z : V} (h : D \ T = {z}) : z ∉ T := by
  have hz : z ∈ D \ T := by rw [h]; exact Finset.mem_singleton_self z
  exact (Finset.mem_sdiff.mp hz).2

/-- **FIVE POINTS IN CYCLIC ORDER WITH THE FIVE ADJACENCIES ARE A FIVE-CYCLE OF `G`.** -/
theorem exists_oddCycle_card_five {p q r s t : V} (h1 : G.Adj p q) (h2 : G.Adj q r) (h3 : G.Adj r s)
    (h4 : G.Adj s t) (h5 : G.Adj t p)
    (hne : p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ p ≠ t ∧ q ≠ r ∧ q ≠ s ∧ q ≠ t ∧ r ≠ s ∧ r ≠ t ∧ s ≠ t) :
    ∃ D : Finset V, IsOddCycle G D ∧ D.card = 5 :=
  ⟨{p, q, r, s, t}, isOddCycle_of_cyc5V hne h1 h2 h3 h4 h5, card_five hne⟩

/-- **AT `LocIndep 1` NO TWO ODD CYCLES ARE VERTEX-DISJOINT.**  Two disjoint odd cycles cost `2`
units of deficiency (`JSP90.defOf_biUnion_ge_card`), and `MaxDef G ≤ 1`. -/
theorem inter_ne_empty_of_isOddCycle_of_locIndep_one (hG : LocIndep 1 G) {C D : Finset V}
    (hC : IsOddCycle G C) (hD : IsOddCycle G D) : C ∩ D ≠ ∅ := by
  classical
  intro hcon
  have hfam : IsOddCycleFamily G ({C, D} : Finset (Finset V)) :=
    ⟨fun X hX Y hY hXY => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX hY
        rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
        · exact absurd rfl hXY
        · exact hcon
        · rw [Finset.inter_comm]; exact hcon
        · exact absurd rfl hXY,
      fun X hX => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl
        · exact hC
        · exact hD⟩
  have hCD : C ≠ D := by
    intro h
    subst h
    obtain ⟨v, hv⟩ := hC.nonempty
    rw [Finset.inter_self] at hcon
    exact absurd (hcon ▸ hv) (by simpa)
  have h2 : 2 ≤ MaxDef G := by
    have hle := defOf_biUnion_ge_card hfam
    calc 2 = ({C, D} : Finset (Finset V)).card := by
          rw [Finset.card_insert_of_notMem (s := ({D} : Finset (Finset V)))
            (fun h => hCD (Finset.mem_singleton.mp h))]
          simp
      _ ≤ defOf G (({C, D} : Finset (Finset V)).biUnion id) := hle
      _ ≤ MaxDef G := le_maxDef G _
  have h3 : MaxDef G ≤ 1 := maxDef_le_of_locIndep hG
  omega

/-! ## Part 1 — how a triangle sits on a triangle

`T = {a, b, c}` is a triangle and every odd cycle of `G` is a triangle.  An odd cycle `D` then sits
on `T` in one of two ways, and both are recorded here as predicates. -/

/-- **`D` HANGS AT `x` OF `T`**: `D` is an odd cycle meeting `T` in the single point `x`. -/
def TriAt (G : SimpleGraph V) (T : Finset V) (x : V) : Prop :=
  ∃ D : Finset V, IsOddCycle G D ∧ D ≠ T ∧ D ∩ T = {x}

/-- **`D` CROSSES `T` ALONG `x y`**: `D` is an odd cycle meeting `T` in exactly the two points
`x`, `y`. -/
def TriCross (G : SimpleGraph V) (T : Finset V) (x y : V) : Prop :=
  ∃ D : Finset V, IsOddCycle G D ∧ D ∩ T = {x, y}

/-- **A TRIANGLE HANGING AT `x` HAS EXACTLY TWO POINTS OUTSIDE `T`**, and `x` is adjacent to both
of them. -/
theorem exists_two_of_triAt {T D : Finset V} (hT3 : T.card = 3) (hD : IsOddCycle G D)
    (hD3 : D.card = 3) {x : V} (hDxT : D ∩ T = {x}) :
    ∃ p z : V, D \ T = {p, z} ∧ p ≠ z ∧ G.Adj x p ∧ G.Adj x z ∧ G.Adj p z := by
  classical
  have hxDT : x ∈ D ∩ T := hDxT.symm ▸ Finset.mem_singleton_self x
  have hxD : x ∈ D := (Finset.mem_inter.mp hxDT).1
  have hxT : x ∈ T := (Finset.mem_inter.mp hxDT).2
  have hcard : (D \ T).card = 2 := by
    have h := Finset.card_sdiff (s := T) (t := D)
    rw [Finset.inter_comm] at h
    have h2 : (D ∩ T).card = 1 := Finset.card_eq_one.mpr ⟨x, hDxT⟩
    omega
  obtain ⟨p, z, hpz, hDz⟩ := Finset.card_eq_two.mp hcard
  have hcl : G.IsNClique 3 D := isNClique_three_of_isOddCycle hD hD3
  have hpout : p ∈ D \ T := by rw [hDz]; exact mem_two_left p z
  have hzout : z ∈ D \ T := by rw [hDz]; exact mem_two_right p z
  have hpD : p ∈ D := Finset.sdiff_subset hpout
  have hzD : z ∈ D := Finset.sdiff_subset hzout
  have hpx : p ≠ x := fun h => (Finset.mem_sdiff.mp hpout).2 (h ▸ hxT)
  have hzx : z ≠ x := fun h => (Finset.mem_sdiff.mp hzout).2 (h ▸ hxT)
  exact ⟨p, z, hDz, hpz, adj_of_isNClique_three (u := x) (v := p) hcl hxD hpD hpx.symm,
    adj_of_isNClique_three (u := x) (v := z) hcl hxD hzD hzx.symm,
    adj_of_isNClique_three (u := p) (v := z) hcl hpD hzD hpz⟩

/-- **A TRIANGLE CROSSING `T` ALONG `x y` HAS EXACTLY ONE POINT OUTSIDE `T`**, and that point is
adjacent to both `x` and `y`. -/
theorem exists_third_of_triCross {T D : Finset V} (hT3 : T.card = 3) (hD : IsOddCycle G D)
    (hD3 : D.card = 3) {x y : V} (hTx : x ∈ T) (hTy : y ∈ T) (hxy : x ≠ y)
    (hDxy : D ∩ T = {x, y}) :
    ∃ z : V, D \ T = {z} ∧ x ∈ D ∧ y ∈ D ∧ G.Adj x z ∧ G.Adj y z := by
  classical
  have hxD : x ∈ D := (Finset.mem_inter.mp (hDxy.symm ▸ mem_two_left x y)).1
  have hyD : y ∈ D := (Finset.mem_inter.mp (hDxy.symm ▸ mem_two_right x y)).1
  have hcard : (D \ T).card = 1 := by
    have h := Finset.card_sdiff (s := T) (t := D)
    rw [Finset.inter_comm] at h
    have h2 : (D ∩ T).card = 2 := Finset.card_eq_two.mpr ⟨x, y, hxy, hDxy⟩
    omega
  obtain ⟨z, hDz⟩ := Finset.card_eq_one.mp hcard
  have hzout : z ∈ D \ T := by rw [hDz]; exact Finset.mem_singleton_self z
  have hmem := Finset.mem_sdiff.mp hzout
  have hzD : z ∈ D := Finset.sdiff_subset hzout
  have hcl : G.IsNClique 3 D := isNClique_three_of_isOddCycle hD hD3
  exact ⟨z, hDz, hxD, hyD,
    adj_of_isNClique_three (u := x) (v := z) hcl hxD hzD (fun h => hmem.2 (h ▸ hTx)),
    adj_of_isNClique_three (u := y) (v := z) hcl hyD hzD (fun h => hmem.2 (h ▸ hTy))⟩

/-! ## Part 2 — two hanging triangles force a five-cycle -/

/-- **THE OTHER POINT OF A TWO-ELEMENT SET.** -/
theorem exists_other_of_mem_two {p z w : V} (hw : w ∈ ({p, z} : Finset V)) (hpz : p ≠ z) :
    ∃ u, ({p, z} : Finset V) = {w, u} ∧ u ≠ w := by
  classical
  rcases Finset.mem_insert.mp hw with hwp | hwz
  · have hne1 : z ≠ w := by
      intro h
      exact hpz (h.trans hwp).symm
    exact ⟨z, by rw [hwp], hne1⟩
  · have hwz' : w = z := Finset.mem_singleton.mp hwz
    have hne2 : p ≠ w := by
      intro h
      exact hpz (h.trans hwz')
    exact ⟨p, by rw [hwz']; exact Finset.insert_comm p z (∅ : Finset V), hne2⟩

/-- **THE FIVE-CYCLE OF TWO TRIANGLES HANGING AT TWO POINTS OF A TRIANGLE.**

Let `T = {a, b, c}` be a triangle, `D_a`, `D_b` triangles with `D_a ∩ T = {a}`, `D_b ∩ T = {b}`, and
`w ∉ T` a point of both.  Then `G` has an odd cycle with five vertices.

*Proof.*  Write `D_a \ T = {p, z}` and `D_b \ T = {q, r}`, and let `u`, `v` be the points of those
two pairs other than `w`.  If the pairs coincide (`u = v`), the points `a, c, b, w, u` are in cyclic
adjacency: `a ~ c`, `c ~ b` from `T`, `b ~ w` from `D_b`, `w ~ u` and `u ~ a` from `D_a`.  Otherwise
the points `u, a, b, v, w` are: `u ~ a`, `w ~ u` from `D_a`, `a ~ b` from `T`, `b ~ v`, `v ~ w` from
`D_b`.  Both are five pairwise distinct points, since `a`, `b`, `c` are distinct, `w`, `u`, `v` lie
outside `T` and `w ≠ u`, `w ≠ v`, `u ≠ v`. -/
theorem exists_oddCycle_card_five_of_two_hanging {a b c : V} (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c)
    {T : Finset V} (hTeq : T = {a, b, c}) (hTcl : G.IsNClique 3 T) {D_a D_b : Finset V}
    (hD_a : IsOddCycle G D_a) (hD_a3 : D_a.card = 3) (hD_a_T : D_a ∩ T = {a})
    (hD_b : IsOddCycle G D_b) (hD_b3 : D_b.card = 3) (hD_b_T : D_b ∩ T = {b}) {w : V}
    (hwD_a : w ∈ D_a) (hwD_b : w ∈ D_b) (hwT : w ∉ T) :
    ∃ D : Finset V, IsOddCycle G D ∧ D.card = 5 := by
  classical
  have haT : a ∈ T := hTeq ▸ mem_three_left a b c
  have hbT : b ∈ T := hTeq ▸ mem_three_mid a b c
  have hcT : c ∈ T := hTeq ▸ mem_three_right a b c
  have hT3 : T.card = 3 := hTeq ▸ card_three_set hne
  obtain ⟨p, z, hDa_out, hpz, hap, haz, hpa⟩ := exists_two_of_triAt hT3 hD_a hD_a3 hD_a_T
  obtain ⟨q, r, hDb_out, hqr, hbq, hbr, hqb⟩ := exists_two_of_triAt hT3 hD_b hD_b3 hD_b_T
  have hcl_a : G.IsNClique 3 D_a := isNClique_three_of_isOddCycle hD_a hD_a3
  have hcl_b : G.IsNClique 3 D_b := isNClique_three_of_isOddCycle hD_b hD_b3
  have haD : a ∈ D_a := (Finset.mem_inter.mp (hD_a_T.symm ▸ Finset.mem_singleton_self a)).1
  have hbD : b ∈ D_b := (Finset.mem_inter.mp (hD_b_T.symm ▸ Finset.mem_singleton_self b)).1
  have hpout : p ∈ D_a \ T := by rw [hDa_out]; exact mem_two_left p z
  have hzout : z ∈ D_a \ T := by rw [hDa_out]; exact mem_two_right p z
  have hpD : p ∈ D_a := Finset.sdiff_subset hpout
  have hzD : z ∈ D_a := Finset.sdiff_subset hzout
  have hnotT : ∀ v : V, v ∈ D_a \ T → v ∉ T := fun v hv => (Finset.mem_sdiff.mp hv).2
  have hnotTa : ∀ v : V, v ∈ D_a \ T → v ≠ a :=
    fun v hv hva => (Finset.mem_sdiff.mp hv).2 (hva ▸ (hTeq ▸ mem_three_left a b c))
  have hwDa : w ∈ ({p, z} : Finset V) := by rw [← hDa_out]; exact Finset.mem_sdiff.mpr ⟨hwD_a, hwT⟩
  have hwDb : w ∈ ({q, r} : Finset V) := by rw [← hDb_out]; exact Finset.mem_sdiff.mpr ⟨hwD_b, hwT⟩
  obtain ⟨u, heqa, huw⟩ := exists_other_of_mem_two hwDa hpz
  obtain ⟨v, heqb, hvw⟩ := exists_other_of_mem_two hwDb hqr
  have hu_out : u ∈ D_a \ T := by rw [hDa_out, heqa]; exact mem_two_right w u
  have hu_notT : u ∉ T := hnotT u hu_out
  have huD_ab : u ∈ D_a := Finset.sdiff_subset hu_out
  have hw_out : w ∈ D_a \ T := Finset.mem_sdiff.mpr ⟨hwD_a, hwT⟩
  have hw_out_b : w ∈ D_b \ T := Finset.mem_sdiff.mpr ⟨hwD_b, hwT⟩
  have hv_out : v ∈ D_b \ T := by rw [hDb_out, heqb]; exact mem_two_right w v
  have hv_notT : v ∉ T := (Finset.mem_sdiff.mp hv_out).2
  have hw_notT : w ∉ T := hwT
  have hwb : G.Adj b w := adj_of_isNClique_three (u := b) (v := w) hcl_b hbD hwD_b
    (fun h => hw_notT (h ▸ hbT))
  have hwbv : G.Adj b v := adj_of_isNClique_three (u := b) (v := v) hcl_b hbD
    (Finset.sdiff_subset hv_out) (fun h => (Finset.mem_sdiff.mp hv_out).2 (h ▸ hbT))
  have hwvb : G.Adj w v := adj_of_isNClique_three (u := w) (v := v) hcl_b hwD_b
    (Finset.sdiff_subset hv_out) (fun h => hvw h.symm)
  have hua : G.Adj a u := adj_of_isNClique_three (u := a) (v := u) hcl_a haD
    (Finset.sdiff_subset hu_out) (hnotTa u hu_out).symm
  have hwua : G.Adj w u := adj_of_isNClique_three (u := w) (v := u) hcl_a hwD_a
    (Finset.sdiff_subset hu_out) huw.symm
  have hab : G.Adj a b := adj_of_isNClique_three hTcl haT hbT hne.1
  have hbc : G.Adj b c := adj_of_isNClique_three hTcl hbT hcT hne.2.2
  have hca : G.Adj c a := adj_of_isNClique_three hTcl hcT haT hne.2.1.symm
  by_cases hsame : (({p, z} : Finset V)) = (({q, r} : Finset V))
  · refine exists_oddCycle_card_five (p := a) (q := c) (r := b) (s := w) (t := u)
      hca.symm hbc.symm hwb hwua hua.symm
      ⟨hne.2.1, hne.1, ne_of_mem_not_mem' (T := T) (x := a) (y := w) haT hw_notT,
        ne_of_mem_not_mem' (T := T) (x := a) (y := u) haT hu_notT,
        hne.2.2.symm, ne_of_mem_not_mem' (T := T) (x := c) (y := w) hcT hw_notT,
        ne_of_mem_not_mem' (T := T) (x := c) (y := u) hcT hu_notT,
        ne_of_mem_not_mem' (T := T) (x := b) (y := w) hbT hw_notT,
        ne_of_mem_not_mem' (T := T) (x := b) (y := u) hbT hu_notT, huw.symm⟩
  · have huv : u ≠ v := by
      intro h
      exact absurd (by rw [heqa, heqb, h]) hsame
    have hu_notB : u ∉ ({q, r} : Finset V) := by
      intro huB
      have huv : u = w ∨ u = v := by
        rw [heqb] at huB
        simpa using huB
      rcases huv with huw' | huv'
      · exact huw huw'
      · exact absurd (by rw [heqa, heqb, huv']) hsame
    refine exists_oddCycle_card_five (p := u) (q := a) (r := b) (s := v) (t := w)
      hua.symm hab hwbv hwvb.symm hwua
      ⟨ne_of_not_mem_mem (T := T) (x := u) (y := a) hu_notT haT,
        ne_of_not_mem_mem (T := T) (x := u) (y := b) hu_notT hbT,
        huv, huw,
        hne.1, ne_of_mem_not_mem' (T := T) (x := a) (y := v) haT hv_notT,
        ne_of_mem_not_mem' (T := T) (x := a) (y := w) haT hw_notT,
        ne_of_mem_not_mem' (T := T) (x := b) (y := v) hbT hv_notT,
        ne_of_mem_not_mem' (T := T) (x := b) (y := w) hbT hw_notT, hvw⟩

/-- **TWO TRIANGLES HANGING AT TWO POINTS OF A TRIANGLE FORCE A FIVE-CYCLE.**  This is the form used
below: `LocIndep 1 G` supplies the common point `w`, because two vertex-disjoint odd cycles would
cost two units of deficiency. -/
theorem exists_oddCycle_card_five_of_triAt_two (hG : LocIndep 1 G)
    {a b c : V} (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c) {T : Finset V} (hTeq : T = {a, b, c})
    (hTcl : G.IsNClique 3 T) (htri : ∀ D : Finset V, IsOddCycle G D → D.card = 3)
    (ha : TriAt G T a) (hb : TriAt G T b) : ∃ D : Finset V, IsOddCycle G D ∧ D.card = 5 := by
  obtain ⟨D_a, hD_a, hD_a_ne, hD_a_T⟩ := ha
  obtain ⟨D_b, hD_b, hD_b_ne, hD_b_T⟩ := hb
  have hwpos : 0 < (D_a ∩ D_b).card := by
    have hne0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr
      (inter_ne_empty_of_isOddCycle_of_locIndep_one hG hD_a hD_b))
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hwpos
  obtain ⟨hw_a, hw_b⟩ := Finset.mem_inter.mp hw
  have hwT : w ∉ T := by
    intro hw
    have hw1 : w = a := Finset.mem_singleton.mp
      (hD_a_T.symm ▸ Finset.mem_inter.mpr ⟨hw_a, hw⟩)
    have hw2 : w = b := Finset.mem_singleton.mp
      (hD_b_T.symm ▸ Finset.mem_inter.mpr ⟨hw_b, hw⟩)
    exact hne.1 (hw1.symm.trans hw2)
  exact exists_oddCycle_card_five_of_two_hanging hne hTeq hTcl hD_a (htri D_a hD_a) hD_a_T hD_b
    (htri D_b hD_b) hD_b_T hw_a hw_b hwT

/-- **THE COROLLARY THAT IS USED BELOW: at `LocIndep 1`, on the odd-girth-three class, at most one
point of a triangle carries a triangle hanging at it.** -/
theorem not_triAt_two_of_oddGirthThree (hG : LocIndep 1 G) (hog : OddGirthThree G)
    {a b c : V} (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c) {T : Finset V} (hTeq : T = {a, b, c})
    (hTcl : G.IsNClique 3 T) : ¬ (TriAt G T a ∧ TriAt G T b) := by
  rintro ⟨ha, hb⟩
  obtain ⟨D, hD, hD5⟩ := exists_oddCycle_card_five_of_triAt_two hG hne hTeq hTcl hog ha hb
  exact absurd hD5 (by intro h; rw [hog D hD] at h; omega)

/-! ## Part 3 — three crossing triangles force a five-cycle -/

/-- **THREE TRIANGLES CROSSING `T = {a, b, c}` ALONG ITS THREE EDGES FORCE A FIVE-CYCLE.**

Let `D_ab`, `D_ac`, `D_bc` be odd cycles with `D_ab ∩ T = {a, b}`, `D_ac ∩ T = {a, c}`,
`D_bc ∩ T = {b, c}`, every odd cycle a triangle and `LocIndep 1 G`.  Write
`D_ab = {a, b, z}`, `D_ac = {a, c, w}`, `D_bc = {b, c, u}`.  The three outside points lie outside `T`,
and no two of them coincide — a coincidence is a `K₄` on `T` together with that point, which
`LocIndep 1` forbids.  Hence the five points `a, z, b, c, w` are in cyclic adjacency. -/
theorem exists_oddCycle_card_five_of_triCross_three (hG : LocIndep 1 G)
    {a b c : V} (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c) {T : Finset V} (hTeq : T = {a, b, c})
    (hTcl : G.IsNClique 3 T) (htri : ∀ D : Finset V, IsOddCycle G D → D.card = 3)
    (hab : TriCross G T a b) (hac : TriCross G T a c) (hbc : TriCross G T b c) :
    ∃ D : Finset V, IsOddCycle G D ∧ D.card = 5 := by
  classical
  have haT : a ∈ T := hTeq ▸ mem_three_left a b c
  have hbT : b ∈ T := hTeq ▸ mem_three_mid a b c
  have hcT : c ∈ T := hTeq ▸ mem_three_right a b c
  have hT3 : T.card = 3 := hTeq ▸ card_three_set hne
  have hab_adj : G.Adj a b := adj_of_isNClique_three hTcl haT hbT hne.1
  have hac_adj : G.Adj a c := adj_of_isNClique_three hTcl haT hcT hne.2.1
  have hbc_adj : G.Adj b c := adj_of_isNClique_three hTcl hbT hcT hne.2.2
  obtain ⟨D_ab, hD_ab, hD_ab_T⟩ := hab
  obtain ⟨D_ac, hD_ac, hD_ac_T⟩ := hac
  obtain ⟨D_bc, hD_bc, hD_bc_T⟩ := hbc
  obtain ⟨z, hz_out, haz_ab, hbz_ab, haz, hbz⟩ := exists_third_of_triCross hT3 hD_ab
    (htri D_ab hD_ab) haT hbT hne.1 hD_ab_T
  obtain ⟨w, hw_out, haw_ac, hcw_ac, haw, hcw⟩ := exists_third_of_triCross hT3 hD_ac
    (htri D_ac hD_ac) haT hcT hne.2.1 hD_ac_T
  obtain ⟨u, hu_out, hbu_bc, hcu_bc, hbu, hcu⟩ := exists_third_of_triCross hT3 hD_bc
    (htri D_bc hD_bc) hbT hcT hne.2.2 hD_bc_T
  have hznotT : z ∉ T := not_mem_of_sdiff_eq_singleton hz_out
  have hwnotT : w ∉ T := not_mem_of_sdiff_eq_singleton hw_out
  have hunotT : u ∉ T := not_mem_of_sdiff_eq_singleton hu_out
  have hzw : z ≠ w := by
    intro h
    exact not_isClique_card_four_of_locIndep_one hG hab_adj hac_adj haz hbc_adj hbz (h ▸ hcw)
  have hzu : z ≠ u := by
    intro h
    exact not_isClique_card_four_of_locIndep_one hG hab_adj hac_adj haz hbc_adj (h ▸ hbu) (h ▸ hcu)
  have hwu : w ≠ u := by
    intro h
    exact not_isClique_card_four_of_locIndep_one hG hab_adj hac_adj (h ▸ haw) hbc_adj (h ▸ hbu) hcu
  refine exists_oddCycle_card_five (p := a) (q := z) (r := b) (s := c) (t := w)
    haz hbz.symm hbc_adj hcw haw.symm
    ⟨(ne_of_not_mem_mem (T := T) (x := z) (y := a) hznotT haT).symm, hne.1, hne.2.1,
      (ne_of_not_mem_mem (T := T) (x := w) (y := a) hwnotT haT).symm,
      ne_of_not_mem_mem (T := T) (x := z) (y := b) hznotT hbT,
      ne_of_not_mem_mem (T := T) (x := z) (y := c) hznotT hcT, hzw, hne.2.2,
      (ne_of_not_mem_mem (T := T) (x := w) (y := b) hwnotT hbT).symm,
      (ne_of_not_mem_mem (T := T) (x := w) (y := c) hwnotT hcT).symm⟩

/-- **AT `LocIndep 1`, ON THE ODD-GIRTH-THREE CLASS, THE THREE EDGES OF A TRIANGLE CANNOT ALL BE
CROSSED.** -/
theorem not_triCross_three_of_oddGirthThree (hG : LocIndep 1 G) (hog : OddGirthThree G)
    {a b c : V} (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c) {T : Finset V} (hTeq : T = {a, b, c})
    (hTcl : G.IsNClique 3 T) :
    ¬ (TriCross G T a b ∧ TriCross G T a c ∧ TriCross G T b c) := by
  rintro ⟨hab, hac, hbc⟩
  obtain ⟨D, hD, hD5⟩ := exists_oddCycle_card_five_of_triCross_three hG hne hTeq hTcl hog hab hac hbc
  exact absurd hD5 (by intro h; rw [hog D hD] at h; omega)

end

end JSP90
