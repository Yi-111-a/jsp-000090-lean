/-
# JSP-000090, round 72 — **the descent at the boundary of an odd cycle (no separation hypothesis),
and the disjoint book of the fan**

## Where the development stands

Rounds 64–69 reduced Erdős Problem #73 to **one** statement, `JSP90.FanErdős73 f` of
`JSPProblem/Free.lean`: for every triangle-free `G` with `LocIndep k G` and every odd cycle `C` of
`G`, a set `Z` of at most `f k` vertices meeting every odd cycle of `G` that meets the boundary of
`C`.  `JSP90.erdos73_iff_fanErdős73` proves that this statement is *equivalent* to the whole
problem, and round 68 proves it equivalent to `JSP90.TriangleFreeOnly`.  Round 70 named the classes
of the fan and the classical "no short cut" lemma.

This round does two things, both **on the critical path** and neither of which needs Menger, the
block-cut tree, connectivity, or any new decomposition axis.

## Part 1 — the descent at the boundary, with **no** separation hypothesis

Rounds 59 and 44 proved `1 + MaxDef G[X] ≤ MaxDef G` for vertex sets `X` *separated* from an odd
cycle (the canonical such set being the outer layer).  The fan of `C` is in general **not**
separated from `C` — that is the whole point of the fan — and rounds 59–70 had therefore no descent
available at the fan.  This round proves it with no hypothesis at all:

* **`JSP90.maxDef_ge_one_add_maxDef_boundary`**, `JSP90.locIndep_boundary`,
  `JSP90.maxDef_boundary_le`: for every odd cycle `C`,

  ```lean
  1 + MaxDef (G[boundary G C]) ≤ MaxDef G,        i.e.     LocIndep (k - 1) (G[∂C])
  ```

  The proof is a counting argument: for `Y ⊆ ∂C` attaining `maxDefIn G ∂C`, the vertex set `Y ∪ C`
  has `|Y| + |C|` vertices while `α(G[Y ∪ C]) ≤ α(G[Y]) + α(G[C])` and `2 α(G[C]) + 1 ≤ |C|`
  (`JSP90.indepCard_union_le`, `JSP90.two_indepCard_add_one_le_card_oddCycle`).  In words: **the
  fan of an odd cycle always spends at least one unit less of Erdős's hypothesis than the whole
  graph.**
* The statement is a statement about the **maximum** over `Y ⊆ ∂C`, not about each `Y`; the
  second case of the proof (where `2 α(Y) > |Y|`) is exactly why, and it is recorded in the
  docstring together with a counterexample to the pointwise version (an independent triple and a
  triangle, disjoint: both `defOf` are `0`).
* **`JSP90.isBipartite_fan_of_locIndep_one'`** is a second, independent route to round 69's
  `JSP90.isBipartite_fan_of_locIndep_one`, now read off `MaxDef = 0 ↔ bipartite`.

## Part 2 — the disjoint book of the fan

`JSPProblem/Class.lean` named the *attachment classes* `fanClass G C a`; they **overlap**, because a
fan vertex attached to a pair `{c − 1, c + 1}` belongs to the classes of `c − 1` *and* of `c + 1`.
This round refines them to a **disjoint** family:

* `JSP90.attachSet`, `JSP90.mem_attachSet` — the attachment set of a vertex on `C`;
* **`JSP90.card_attachSet_le_two`** — `|N(x) ∩ C| ≤ 2` in the language of *vertices* rather than of
  indices (`JSP90.card_inter_neigh_le_two` transferred through the bijection `j ↦ f j`);
* `JSP90.singleClass G C f i` = the fan vertices whose **only** attachment point is `f i`, and
  `JSP90.doubleAttach G C` = the fan vertices with two attachment points;
* **`JSP90.mem_singleClass_or_doubleAttach`**, `JSP90.disjoint_singleClass_of_ne`,
  `JSP90.disjoint_singleClass_double` — the fan is the disjoint union of the `m` single classes and
  of the double-attachment part;
* `JSP90.subset_singleClass_fanClass`, **`JSP90.isIndepSet_singleClass`** — each single class lies
  in the attachment class of its index and is an independent set;
* `JSP90.cycSucc_pow_four_ne` — four steps around a cycle of length at least five never return to
  the start, the arithmetic behind the disjointness of the *double* classes.

## Part 3 — the parity of two single classes, and the counting lemma

* **`JSP90.not_isOddCycle_of_subset_two_singleClass`: an odd cycle of the fan meets at least three
  single classes.**  This is the disjoint refinement of round 70's
  `JSP90.not_isOddCycle_of_subset_fanClass_union`, and it is the exact place where the
  *disjointness* of the book is used: the two cells are disjoint sets of vertices, the attachment
  classes of round 70 are not.
* **`JSP90.hitsOddCycles_boundary_sdiff_two_singleClass`** — the fan with two single classes
  removed is a transversal of the odd cycles inside the fan.  Because the classes are disjoint this
  is a **strictly smaller** transversal than round 70's `JSP90.hitsOddCycles_farFan`.
* **`JSP90.card_le_boundary_sdiff_two_singleClass` — the counting lemma of the book**: a packing of
  `j` odd cycles inside the fan of `C` needs `j` vertices outside every two single classes, for
  *every* pair of indices `i, j`.  The content is that the bound holds for all `binom m 2` pairs
  simultaneously, which is what forces a transversal of the fan to spread out over the classes.
* **`JSP90.exists_fanTransversal_le_card`** — the explicit form: `|S_i| + |S_j| + |Z| ≤ |∂C|` where
  `Z` is the transversal above.

## Part 4 — a new instance of the headline theorem along the book axis

* **`JSP90.fanErdős73_of_fan_singleClassTwo`**, **`JSP90.erdos73On_of_fan_singleClassTwo`**,
  **`JSP90.erdos73_of_fan_singleClassTwo`** — if every odd cycle `C` of a triangle-free `G` has two
  single classes `S_i`, `S_j` of its book whose union is a transversal of all the odd cycles of `G`
  meeting `∂C` and whose combined size is at most `q`, then `LocIndep k G` forces
  `CloseToBipartite (fanBound (fun _ => q) k) G`, and `Erdős73 k` for every `k`.  The transversal now
  lives **in the fan** and is a union of two *disjoint* pieces of the book of `C`, so its size is
  bounded; round 70's instance used a pair of vertices of `C` outside the fan.  No packing number,
  no odd girth, no packing weight, no bound on the number of branch vertices.

## What is *not* proved

`JSP90.FanErdős73 f` for any `f`, and hence `jsp_000090_main`; behind it stands
`JSP90.OddCycleErdosPosa r` (Reed–Robertson–Seymour–Thomas, JCTA-B 2003).  What Part 1 adds is the
descent at the fan, which was missing until now, and Part 3 the *disjoint* counting system; the
quantitative half of the half-integral argument (turning "a transversal of size `t` forces a
packing of `≳ t / |C|` odd cycles" into a bound on the least transversal of the fan) is still open,
and the odd cycles of `G` that merely *touch* the fan from outside it are still not covered by the
class structure.
-/

import JSPProblem.Class

namespace JSP90

universe u

open Finset Fintype Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance instDecidableEqBook : DecidableEq V := Classical.decEq V

local instance instDecidableAdjBook (G : SimpleGraph V) : ∀ (v w : V), Decidable (G.Adj v w) :=
  fun _ _ => Classical.propDecidable _

/-! ## Part 1 — the descent at the boundary of an odd cycle, with no separation hypothesis -/

section Descent

/-- An independent subset of one set is independent in a superset. -/
theorem isIndepSet_sub {s t : Finset V} (hs : G.IsIndepSet (s : Set V)) (ht : t ⊆ s) :
    G.IsIndepSet (t : Set V) :=
  Set.Pairwise.mono (s := (s : Set V)) (t := (t : Set V))
    (fun a ha => Finset.mem_coe.mpr (ht (Finset.mem_coe.mp ha))) hs

/-- **AN ODD CYCLE SPENDS AT LEAST ONE UNIT OF INDEPENDENCE.**  `2 * α(G[C]) + 1 ≤ |C|`.

`JSP90.two_indepCard_add_one_le_card_of_oddCycle` of `JSPProblem/OffCycle.lean` is the same
statement for `induceFinset G C`, which agrees with `G` on subsets of `C`; this is the form the
counting below needs. -/
theorem two_indepCard_add_one_le_card_oddCycle {C : Finset V} (hC : IsOddCycle G C) :
    2 * indepCard G C + 1 ≤ C.card := by
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  obtain ⟨S, hSsub, hSi, hScard⟩ := exists_indepCard G C
  have hSin : ∀ ⦃x : V⦄, x ∈ (S : Set V) → ∃ i : Fin m, f i = x := by
    intro x hx
    obtain ⟨i, hi⟩ := (hmem x).mp (Finset.mem_coe.mpr (hSsub (Finset.mem_coe.mp hx)))
    exact ⟨i, hi⟩
  have h1 := indep_card_le_of_odd_cycle hm f hinj hcyc S hSi hSin
  have hcard : C.card = m := card_eq_cyclicOrder f hinj hmem
  rw [← hScard]
  omega

/-- **`α` IS ADDITIVE OVER A DISJOINT UNION, IN THE DIRECTION SUFFICIENT FOR COUNTING.**  An
independent set of `G[s ∪ t]` splits into an independent set of `G[s]` and one of `G[t]`. -/
theorem indepCard_union_le {s t : Finset V} (hst : Disjoint s t) :
    indepCard G (s ∪ t) ≤ indepCard G s + indepCard G t := by
  obtain ⟨S, hSsub, hSi, hScard⟩ := exists_indepCard G (s ∪ t)
  have hSi1 : G.IsIndepSet ((S ∩ s : Finset V) : Set V) :=
    isIndepSet_sub (s := S) (t := S ∩ s) hSi Finset.inter_subset_left
  have hSi2 : G.IsIndepSet ((S ∩ t : Finset V) : Set V) :=
    isIndepSet_sub (s := S) (t := S ∩ t) hSi Finset.inter_subset_left
  have h1 : (S ∩ s).card ≤ indepCard G s :=
    le_indepCard_of_isIndepSet (G := G) (X := s) (S := S ∩ s) Finset.inter_subset_right hSi1
  have h2 : (S ∩ t).card ≤ indepCard G t :=
    le_indepCard_of_isIndepSet (G := G) (X := t) (S := S ∩ t) Finset.inter_subset_right hSi2
  have h3 : (S ∩ s).card + (S ∩ t).card = S.card := by
    have hkey : (S ∩ s) ∪ (S ∩ t) = S := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with h | h
        · exact show x ∈ S from (Finset.mem_inter.mp h).1
        · exact show x ∈ S from (Finset.mem_inter.mp h).1
      · intro hx
        rcases Finset.mem_union.mp (hSsub hx) with h | h
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hx, h⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hx, h⟩))
    have h4 : (S ∩ s) ∩ (S ∩ t) = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have h1x : x ∈ s := Finset.inter_subset_right ((Finset.mem_inter.mp hx).1)
      have h2x : x ∈ t := Finset.inter_subset_right ((Finset.mem_inter.mp hx).2)
      exact (Finset.disjoint_left.mp hst) h1x h2x
    rw [← Finset.card_union_add_card_inter, hkey, h4]
    simp
  rw [← hScard]
  omega

/-- **THE INDEPENDENCE NUMBER OF `Y ∪ C` EXCEEDS THAT OF `Y` BY LESS THAN THE WHOLE OF `C`.**  This
is the counting core of Part 1: what an independent set of `G[Y ∪ C]` must waste on `C` costs less
than `|C|`, because an odd cycle wastes one unit on itself. -/
theorem two_indepCard_add_one_sub_le_card_add {C Y : Finset V} (hC : IsOddCycle G C)
    (hYC : Disjoint Y C) :
    2 * indepCard G (Y ∪ C) + 1 ≤ 2 * indepCard G Y + C.card := by
  have h1 := indepCard_union_le (G := G) hYC
  have h2 := two_indepCard_add_one_le_card_oddCycle hC
  have hm : 2 * indepCard G (Y ∪ C) ≤ 2 * indepCard G Y + 2 * indepCard G C := by
    simpa [Nat.mul_comm, Nat.add_mul] using Nat.mul_le_mul h1 (le_refl 2)
  have hc : 2 * indepCard G C ≤ C.card - 1 := Nat.le_sub_of_add_le h2
  omega

/-- **THE MAXIMUM DEFICIENCY OF THE FAN IS AT LEAST ONE BELOW THE MAXIMUM DEFICIENCY OF THE GRAPH.**

```lean
1 + maxDefIn G (boundary G C) ≤ MaxDef G .
```

The proof is the counting of Part 1, and it is worth spelling out the two cases, because the
second one shows why the statement is stated for the **maximum** over `Y ⊆ ∂C` and not for each
`Y` separately.  Let `Y` attain the maximum, `p = 2 α(Y)`, `n = |Y|`, `q = α(Y ∪ C)`, `c = |C|`.
Then `maxDef = n - p` and `defOf (Y ∪ C) = (n + c) - q`, with `q + 1 ≤ p + c`.

* if `p ≤ n`, then `defOf (Y ∪ C) ≥ n + c - (p + c - 1) = n - p + 1 = maxDef + 1`;
* if `p > n`, then `maxDef = 0` and an odd cycle already spends one unit, so
  `MaxDef G ≥ defOf G C ≥ 1`.

The point of the second case: for a *non-maximal* `Y` the analogous inequality is false — in the
disjoint union of an independent triple and a triangle, with `Y` the triple, both `defOf G Y` and
`defOf G (Y ∪ C)` are `0`.  So the descent is a statement about the fan, not about each of its
vertex sets, and it is exactly the statement the fan argument needs. -/
theorem maxDef_ge_one_add_maxDef_boundary {C : Finset V} (hC : IsOddCycle G C) :
    1 + MaxDef (induceFinset G (boundary G C)) ≤ MaxDef G := by
  rw [maxDef_eq_maxDefIn_induceFinset]
  obtain ⟨Y, hYC, hY⟩ := exists_eq_maxDefIn G (boundary G C)
  have hdisj : Disjoint Y C := Finset.disjoint_left.mpr fun x hx hxC =>
    (mem_boundary.mp (hYC hx)).1 hxC
  have hcard : (Y ∪ C).card = Y.card + C.card := Finset.card_union_of_disjoint hdisj
  have hq := two_indepCard_add_one_sub_le_card_add hC hdisj
  have h2 := le_maxDef G (Y ∪ C)
  have h3 : 1 ≤ defOf G C := by
    rw [← defOf_induceFinset_of_subset (G := G) (U := C) (Y := C) (fun _ h => h)]
    exact defOf_oddCycle_ge_one hC
  by_cases hp : 2 * indepCard G Y ≤ Y.card
  · have hA : 2 * indepCard G (Y ∪ C) + 1 ≤ 2 * indepCard G Y + C.card := hq
    have hB : (Y.card - 2 * indepCard G Y) + 2 * indepCard G Y = Y.card :=
      Nat.sub_add_cancel hp
    have hC : 2 * indepCard G (Y ∪ C) + 1 ≤ Y.card + C.card :=
      le_trans hA (Nat.add_le_add_right hp _)
    have hD : (Y.card - 2 * indepCard G Y) + 1 + 2 * indepCard G (Y ∪ C)
        ≤ Y.card + C.card := by omega
    have hstep : maxDefIn G (boundary G C) + 1 ≤ defOf G (Y ∪ C) := by
      simp only [defOf, ← hY, hcard]
      exact Nat.le_sub_of_add_le hD
    have htot : maxDefIn G (boundary G C) + 1 ≤ MaxDef G := le_trans hstep h2
    omega
  · have hz : maxDefIn G (boundary G C) = 0 := by
      rw [← hY]
      simp only [defOf]
      omega
    have h4 : 1 ≤ MaxDef G := le_trans h3 (le_maxDef G C)
    omega

/-- **ERDŐS'S HYPOTHESIS IS INHERITED BY THE FAN OF AN ODD CYCLE, WITH THE PARAMETER DROPPED BY
ONE, WITH NO SEPARATION HYPOTHESIS.**  This is the induction step of the classical argument at an
odd cycle in its most local form. -/
theorem locIndep_boundary {k : ℕ} (hk : 1 ≤ k) (hG : LocIndep k G) {C : Finset V}
    (hC : IsOddCycle G C) : LocIndep (k - 1) (induceFinset G (boundary G C)) :=
  locIndep_of_maxDef_le (by
    have h1 := maxDef_ge_one_add_maxDef_boundary hC
    have h2 := maxDef_le_of_locIndep hG
    omega)

/-- **THE FAN SPENDS AT LEAST ONE UNIT LESS OF ERDŐS'S HYPOTHESIS THAN THE WHOLE GRAPH.** -/
theorem maxDef_boundary_le {k : ℕ} (hk : 1 ≤ k) (hG : LocIndep k G) {C : Finset V}
    (hC : IsOddCycle G C) : MaxDef (induceFinset G (boundary G C)) ≤ k - 1 := by
  have h1 := maxDef_ge_one_add_maxDef_boundary hC
  have h2 := maxDef_le_of_locIndep hG
  omega

end Descent

/-! ## Part 2 — the disjoint book of the fan

`JSPProblem/Class.lean` named the *attachment classes* `fanClass G C a` — the fan vertices attached to
`a` — and proved they are independent.  Those classes **overlap**: a fan vertex attached to a pair
`{c − 1, c + 1}` belongs to the class of `c − 1` *and* to that of `c + 1`.  Part 2 refines them to a
**disjoint** family, which is the "book, not web" picture the classical argument needs: each fan
vertex is either attached to a *single* point of `C` — in which case it belongs to exactly one
class — or attached to a *pair* of points of `C`, and the two cases partition the fan. -/

section Book

/-- **THE ATTACHMENT SET OF `x` ON `C`**: the vertices of `C` adjacent to `x`. -/
noncomputable def attachSet (G : SimpleGraph V) (C : Finset V) (x : V) : Finset V :=
  C.filter (G.Adj x)

theorem mem_attachSet {C : Finset V} {x y : V} :
    y ∈ attachSet G C x ↔ y ∈ C ∧ G.Adj x y := by
  simp [attachSet]

/-- **A FAN VERTEX HAS A NONEMPTY ATTACHMENT SET.** -/
theorem attachSet_nonempty_of_mem_boundary {C : Finset V} {x : V} (hxb : x ∈ boundary G C) :
    (attachSet G C x).Nonempty := by
  obtain ⟨w, hw, hadj⟩ := (mem_boundary.mp hxb).2
  exact ⟨w, mem_attachSet.mpr ⟨hw, hadj⟩⟩

/-- **FOUR STEPS AROUND A CYCLE OF LENGTH AT LEAST FIVE NEVER RETURN TO THE STARTING POINT.** -/
theorem cycSucc_pow_four_ne {m : ℕ} (hm : 5 ≤ m) (i : Fin m) :
    ((cycSucc^[4] : Fin m → Fin m) i).val ≠ i.val := by
  intro h
  have hv : (i.val + 4) % m = i.val := by
    simpa only [cycSucc_pow_val] using h
  have hd : m * ((i.val + 4) / m) = 4 := by
    have hh := Nat.mod_add_div (i.val + 4) m
    omega
  rcases Nat.eq_zero_or_pos ((i.val + 4) / m) with hz | hp
  · rw [hz, Nat.mul_zero] at hd
    omega
  · have hq : 1 ≤ (i.val + 4) / m := by omega
    have h4 : m ≤ 4 := by
      calc m = m * 1 := (Nat.mul_one m).symm
        _ ≤ (i.val + 4) / m * m := by simpa using Nat.mul_le_mul hq (le_refl m)
        _ = m * ((i.val + 4) / m) := Nat.mul_comm _ _
        _ = 4 := hd
    omega

/-- **A FAN VERTEX HAS AT MOST TWO ATTACHMENT POINTS**, read on vertex sets rather than on indices:
`JSP90.card_inter_neigh_le_two` of `JSPProblem/Fan.lean` is transferred from the set of attachment
*indices* to the set of attachment *vertices* by the bijection `j ↦ f j`. -/
theorem card_attachSet_le_two {m : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {x : V} (hxb : x ∈ boundary G C) :
    (attachSet G C x).card ≤ 2 := by
  have hxC : x ∉ C := (mem_boundary.mp hxb).1
  set S : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun j => G.Adj x (f j)) with hSdef
  have hSsub : ∀ j ∈ S, G.Adj x (f j) := fun _ hj => (Finset.mem_filter.mp hj).2
  have hScard : S.card ≤ 2 := card_inter_neigh_le_two hshort hm hm3 f hinj hcyc hCmem hxC S hSsub
  have hsub : S.image f ⊆ attachSet G C x := by
    intro y hy
    obtain ⟨j, hj, hfy⟩ := Finset.mem_image.mp hy
    rw [← hfy]
    exact mem_attachSet.mpr ⟨(hCmem (f j)).mpr ⟨j, rfl⟩, hSsub j hj⟩
  have hsup : attachSet G C x ⊆ S.image f := by
    intro y hy
    have hy' : y ∈ C ∧ G.Adj x y := mem_attachSet.mp hy
    rcases hy' with ⟨hw, hxw⟩
    obtain ⟨j, hj⟩ := (hCmem y).mp hw
    refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ hxw⟩, hj⟩
  have heq : attachSet G C x = S.image f := Finset.Subset.antisymm hsup hsub
  calc (attachSet G C x).card = (S.image f).card := by rw [heq]
    _ = S.card := Finset.card_image_of_injective S hinj
    _ ≤ 2 := hScard

/-- **A FAN VERTEX ATTACHES TO A SINGLE POINT OF `C`, OR TO A PAIR OF POINTS TWO STEPS APART.**

This is the classical content of the book, stated on attachment *vertices*: at a shortest odd cycle
of length at least `5`, a vertex outside `C` has one attachment point or two, and in the latter
case the two are exactly two steps apart along the cycle.  Round 35
(`JSPProblem/Fan.lean`) has this on attachment *indices* (`JSP90.shortArc_of_shortest`); the
disjoint book needs it on vertices, because the cells of the book are sets of vertices. -/
theorem attachSet_eq_singleton_or_pair {m : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {x : V} (hxb : x ∈ boundary G C) :
    (∃ j : Fin m, attachSet G C x = {f j}) ∨
      (∃ j : Fin m, attachSet G C x = {f j, f ((cycSucc^[2] : Fin m → Fin m) j)}) := by
  have hxC : x ∉ C := (mem_boundary.mp hxb).1
  have hne := attachSet_nonempty_of_mem_boundary hxb
  have hcardle := card_attachSet_le_two hshort hm hm3 f hinj hcyc hCmem hxb
  set S : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun j => G.Adj x (f j)) with hSdef
  have hSsub : ∀ j ∈ S, G.Adj x (f j) := fun _ hj => (Finset.mem_filter.mp hj).2
  have hScard : S.card ≤ 2 := card_inter_neigh_le_two hshort hm hm3 f hinj hcyc hCmem hxC S hSsub
  have hSne : S.Nonempty := by
    obtain ⟨w, hw, hadj⟩ := (mem_boundary.mp hxb).2
    obtain ⟨j, hj⟩ := (hCmem w).mp hw
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ hadj⟩⟩
  have hsub : S.image f ⊆ attachSet G C x := by
    intro y hy
    obtain ⟨j, hj, hfy⟩ := Finset.mem_image.mp hy
    rw [← hfy]
    exact mem_attachSet.mpr ⟨(hCmem (f j)).mpr ⟨j, rfl⟩, hSsub j hj⟩
  have hsup : attachSet G C x ⊆ S.image f := by
    intro y hy
    have hy' : y ∈ C ∧ G.Adj x y := mem_attachSet.mp hy
    rcases hy' with ⟨hw, hxw⟩
    obtain ⟨j, hj⟩ := (hCmem y).mp hw
    refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ hxw⟩, hj⟩
  have heq : attachSet G C x = S.image f := Finset.Subset.antisymm hsup hsub
  have hcq (i : Fin m) : ((cycSucc^[2] : Fin m → Fin m) i) = cycSucc (cycSucc i) := by
    have h := Function.iterate_succ_apply' cycSucc 1 i
    simpa using h
  have hSne' : 0 < S.card := Finset.card_pos.mpr hSne
  rcases Nat.lt_or_ge S.card 2 with hlt | hge
  · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
    have hsub2 : S.image f ⊆ {f j} := by
      rw [hj]
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨a, ha, hfa⟩ := hy
      have hae : a = j := by simpa only [Finset.mem_singleton] using ha
      rw [← hfa, hae]
      exact Finset.mem_singleton_self _
    have hsup2 : {f j} ⊆ S.image f := by
      rw [hj]
      intro y hy
      rw [Finset.mem_singleton.mp hy]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_singleton_self j, rfl⟩
    have hfull : attachSet G C x = {f j} := heq.symm ▸ Finset.Subset.antisymm hsub2 hsup2
    exact Or.inl ⟨j, hfull⟩
  · obtain ⟨j, k, hjk, hj⟩ := Finset.card_eq_two.mp (show S.card = 2 by omega)
    have hjk2 : j ≠ k := by
      intro h
      subst h
      exact absurd hjk (by simp)
    have hadj_j : G.Adj x (f j) := hSsub j (by rw [hj]; simp)
    have hadj_k : G.Adj x (f k) := hSsub k (by rw [hj]; simp)
    have hsub2 : S.image f ⊆ {f j, f k} := by
      rw [hj]
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨a, ha, hfa⟩ := hy
      have hae : a = j ∨ a = k := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using ha
      rw [← hfa]
      rcases hae with h | h
      · rw [← h]
        simp
      · rw [← h]
        simp
    have hsup2 : {f j, f k} ⊆ S.image f := by
      rw [hj]
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with h | h
      · rw [h]
        exact Finset.mem_image.mpr ⟨j, by simp, rfl⟩
      · rw [h]
        exact Finset.mem_image.mpr ⟨k, by simp, rfl⟩
    have himg : S.image f = {f j, f k} := Finset.Subset.antisymm hsub2 hsup2
    have hcomm : ∀ p q : V, ({p, q} : Finset V) = {q, p} := by
      intro p q
      ext y
      simp [or_comm]
    rcases shortArc_of_shortest hshort hm hm3 f hinj hcyc hCmem hjk2 hxC hadj_j hadj_k with hs | hs
    · have hfk : f k = f ((cycSucc^[2] : Fin m → Fin m) j) := by
        rw [hcq]
        exact congrArg f hs.symm
      refine Or.inr ⟨j, ?_⟩
      rw [heq, himg, hcomm (f j) (f k), hfk, hcomm (f ((cycSucc^[2] : Fin m → Fin m) j)) (f j)]
    · have hfj : f j = f ((cycSucc^[2] : Fin m → Fin m) k) := by
        rw [hcq]
        exact congrArg f hs.symm
      refine Or.inr ⟨k, ?_⟩
      rw [heq, himg, hcomm (f j) (f k), hfj]

/-- **A SINGLE CLASS OF THE BOOK**: the fan vertices whose *only* attachment point is `f i`. -/
noncomputable def singleClass (G : SimpleGraph V) (C : Finset V) (f : Fin m → V) (i : Fin m) : Finset V :=
  (boundary G C).filter (fun x => attachSet G C x = {f i})

theorem mem_singleClass {C : Finset V} {f : Fin m → V} {i : Fin m} {x : V} :
    x ∈ singleClass G C f i ↔ x ∈ boundary G C ∧ attachSet G C x = {f i} := by
  simp [singleClass]

/-- **THE DOUBLE-ATTACHMENT PART OF THE FAN**: the fan vertices with two attachment points.  Part 2
shows the fan is the disjoint union of the single classes and of this set. -/
noncomputable def doubleAttach (G : SimpleGraph V) (C : Finset V) : Finset V :=
  (boundary G C).filter (fun x => (attachSet G C x).card = 2)

theorem mem_doubleAttach {C : Finset V} {x : V} :
    x ∈ doubleAttach G C ↔ x ∈ boundary G C ∧ (attachSet G C x).card = 2 := by
  simp [doubleAttach]

/-- **THE FAN IS COVERED BY THE SINGLE CLASSES AND THE DOUBLE-ATTACHMENT PART.**  Each fan vertex
has one or two attachment points, and in the first case it lies in exactly one single class. -/
theorem mem_singleClass_or_doubleAttach {m : ℕ} {C : Finset V}
    (hshort : ∀ D : Finset V, IsOddCycle G D → C.card ≤ D.card)
    (hm : m % 2 = 1) (hm3 : 5 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hcyc : ∀ j : Fin m, G.Adj (f j) (f (cycSucc j)))
    (hCmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) {x : V} (hxb : x ∈ boundary G C) :
    (∃ i : Fin m, x ∈ singleClass G C f i) ∨ x ∈ doubleAttach G C := by
  have hne := attachSet_nonempty_of_mem_boundary hxb
  have hcard := card_attachSet_le_two hshort hm hm3 f hinj hcyc hCmem hxb
  by_cases h2 : (attachSet G C x).card = 2
  · exact Or.inr (mem_doubleAttach.mpr ⟨hxb, h2⟩)
  · obtain ⟨w, hw⟩ := hne
    have hpos : 0 < (attachSet G C x).card := Finset.card_pos.mpr ⟨w, hw⟩
    have h1 : (attachSet G C x).card = 1 := by omega
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
    have hyC : y ∈ C := by
      have : y ∈ attachSet G C x := by rw [hy]; exact Finset.mem_singleton_self y
      exact (mem_attachSet.mp this).1
    obtain ⟨i, hi⟩ := (hCmem y).mp hyC
    refine Or.inl ⟨i, mem_singleClass.mpr ⟨hxb, ?_⟩⟩
    rw [hy, hi]

/-- **SINGLE CLASSES ARE DISJOINTLY PACKED.** -/
theorem disjoint_singleClass_of_ne {m : ℕ} {C : Finset V} {f : Fin m → V} (hinj : Function.Injective f)
    {i j : Fin m} (hij : i ≠ j) : Disjoint (singleClass G C f i) (singleClass G C f j) := by
  refine Finset.disjoint_left.mpr fun x hx => ?_
  have hxi : attachSet G C x = {f i} := (mem_singleClass.mp hx).2
  by_contra hcon
  have hxj : attachSet G C x = {f j} := (mem_singleClass.mp hcon).2
  have h1 : f i ∈ attachSet G C x := by rw [hxi]; exact Finset.mem_singleton_self _
  rw [hxj] at h1
  have heq : f i = f j := Finset.mem_singleton.mp h1
  exact absurd (hinj heq) hij

/-- **NO SINGLE CLASS MEETS THE DOUBLE-ATTACHMENT PART.** -/
theorem disjoint_singleClass_double {m : ℕ} {C : Finset V} {f : Fin m → V} {i : Fin m} :
    Disjoint (singleClass G C f i) (doubleAttach G C) := by
  refine Finset.disjoint_left.mpr fun x hx => ?_
  have hxi : attachSet G C x = {f i} := (mem_singleClass.mp hx).2
  by_contra hcon
  have hxd : (attachSet G C x).card = 2 := (mem_doubleAttach.mp hcon).2
  have hbad : ({f i} : Finset V).card = 2 := by rw [← hxi]; exact hxd
  rw [Finset.card_singleton] at hbad
  omega

/-- **A SINGLE CLASS LIES IN THE ATTACHMENT CLASS OF ITS OWN INDEX.**  This is the only fact about
`JSP90.fanClass` of `JSPProblem/Class.lean` that the rest of this file needs. -/
theorem subset_singleClass_fanClass {m : ℕ} {C : Finset V} {f : Fin m → V} {i : Fin m} :
    singleClass G C f i ⊆ fanClass G C (f i) := by
  intro x hx
  have hxb : x ∈ boundary G C := (mem_singleClass.mp hx).1
  have hA : attachSet G C x = {f i} := (mem_singleClass.mp hx).2
  have hmem : f i ∈ attachSet G C x := hA ▸ Finset.mem_singleton_self _
  exact mem_fanClass.mpr ⟨hxb, (mem_attachSet.mp hmem).2.symm⟩

/-- **A SINGLE CLASS IS AN INDEPENDENT SET** — no new content, but the disjoint packaging makes it
usable as one of `m` *disjoint* independent pieces of the fan. -/
theorem isIndepSet_singleClass (hG3 : G.CliqueFree 3) {m : ℕ} {C : Finset V} {f : Fin m → V}
    (i : Fin m) : G.IsIndepSet (singleClass G C f i) := by
  intro x hx y hy hxy
  have hA : attachSet G C x = {f i} := (mem_singleClass.mp (Finset.mem_coe.mp hx)).2
  have hB : attachSet G C y = {f i} := (mem_singleClass.mp (Finset.mem_coe.mp hy)).2
  have hax : G.Adj (f i) x := (mem_attachSet.mp (hA ▸ Finset.mem_singleton_self _)).2.symm
  have hay : G.Adj (f i) y := (mem_attachSet.mp (hB ▸ Finset.mem_singleton_self _)).2.symm
  exact not_adj_of_common_neigh_of_cliqueFree3 hG3 hax hay

end Book

/-! ## Part 3 — the parity of two single classes, and the counting lemma -/

section TwoSingle

/-- **AN ODD CYCLE OF `G` IS NEVER CONTAINED IN TWO SINGLE CLASSES.**  In words: an odd cycle of the
fan meets at least three of the `m` single classes of `C`.  This is the disjoint refinement of
`JSP90.not_isOddCycle_of_subset_fanClass_union` of `JSPProblem/Class.lean`, and it is the exact
place where the *disjointness* of the book is used: the two cells are disjoint sets of vertices,
whereas the attachment classes of round 70 overlap. -/
theorem not_isOddCycle_of_subset_two_singleClass (hG3 : G.CliqueFree 3) {m : ℕ} {C D : Finset V}
    {f : Fin m → V} (hD : IsOddCycle G D) {i j : Fin m} :
    ¬ (D ⊆ singleClass G C f i ∪ singleClass G C f j) := by
  intro h
  refine not_isOddCycle_of_subset_fanClass_union hG3 (C := C) (D := D) (a := f i) (b := f j) ?_ hD
  intro y hy
  rcases Finset.mem_union.mp (h hy) with h1 | h2
  · exact Finset.mem_union.mpr (Or.inl (subset_singleClass_fanClass h1))
  · exact Finset.mem_union.mpr (Or.inr (subset_singleClass_fanClass h2))

/-- **THE FAN WITH TWO SINGLE CLASSES REMOVED IS A TRANSVERSAL OF THE ODD CYCLES INSIDE THE FAN.**
A *smaller* set than the transversal of round 70, because the single classes are disjoint and
contained in the attachment classes. -/
theorem hitsOddCycles_boundary_sdiff_two_singleClass (hG3 : G.CliqueFree 3) {m : ℕ} {C : Finset V}
    (f : Fin m → V) {i j : Fin m} {D : Finset V} (hD : IsOddCycle G D) (hsub : D ⊆ boundary G C) :
    D ∩ (boundary G C \ (singleClass G C f i ∪ singleClass G C f j)) ≠ ∅ := by
  by_contra hcon
  have hne : D ∩ (boundary G C \ (singleClass G C f i ∪ singleClass G C f j)) = ∅ := hcon
  refine not_isOddCycle_of_subset_two_singleClass hG3 (f := f) (C := C) (D := D) (hD := hD)
    (i := i) (j := j) ?_
  intro y hy
  by_contra hcontra
  have hmem : y ∈ boundary G C \ (singleClass G C f i ∪ singleClass G C f j) :=
    Finset.mem_sdiff.mpr ⟨hsub hy, hcontra⟩
  have hnil : y ∈ (∅ : Finset V) := hne ▸ Finset.mem_inter.mpr ⟨hy, hmem⟩
  simp at hnil

/-- **THE COUNTING LEMMA OF THE BOOK: a packing of `j` odd cycles inside the fan of `C` needs `j`
vertices outside every two single classes**, for *every* pair of indices `i, j`.  The content is
that the bound holds for all `binom m 2` pairs simultaneously, which is what forces a transversal of
the fan to spread out over the classes. -/
theorem card_le_boundary_sdiff_two_singleClass (hG3 : G.CliqueFree 3) {m : ℕ} {C : Finset V}
    (f : Fin m → V) {i j : Fin m} {𝒟 : Finset (Finset V)} (hfam : IsOddCycleFamily (G := G) 𝒟)
    (hsub : ∀ D ∈ 𝒟, D ⊆ boundary G C) :
    𝒟.card ≤ (boundary G C \ (singleClass G C f i ∪ singleClass G C f j)).card := by
  set Z : Finset V := boundary G C \ (singleClass G C f i ∪ singleClass G C f j) with hZdef
  have hne : ∀ D ∈ 𝒟, (D ∩ Z).Nonempty := by
    intro D hX
    rw [Finset.nonempty_iff_ne_empty]
    exact hitsOddCycles_boundary_sdiff_two_singleClass hG3 f (i := i) (j := j) (hfam.2 D hX)
      (hsub D hX)
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

/-- **THE LEAST TRANSVERSAL OF THE ODD CYCLES INSIDE THE FAN IS BOUNDED BY THE COMPLEMENT OF ANY
TWO SINGLE CLASSES.**  In explicit form: `boundary G C \ (singleClass G C f i ∪ singleClass G C f j)`
is such a transversal, and the two classes being disjoint this is a bound of
`|∂C| − |S_i| − |S_j|`. -/
theorem exists_fanTransversal_le_card (hG3 : G.CliqueFree 3) {m : ℕ} {C : Finset V} (f : Fin m → V)
    {i j : Fin m} :
    ∃ Z : Finset V,
      (∀ D : Finset V, IsOddCycle G D → D ⊆ boundary G C → D ∩ Z ≠ ∅) ∧
      (singleClass G C f i ∪ singleClass G C f j).card + Z.card ≤ (boundary G C).card := by
  refine ⟨boundary G C \ (singleClass G C f i ∪ singleClass G C f j), ?_, ?_⟩
  · intro D hD hsub
    exact hitsOddCycles_boundary_sdiff_two_singleClass hG3 f hD hsub
  · have hsub : singleClass G C f i ∪ singleClass G C f j ⊆ boundary G C := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact (mem_singleClass.mp h).1
      · exact (mem_singleClass.mp h).1
    have hdis : Disjoint (singleClass G C f i ∪ singleClass G C f j)
        (boundary G C \ (singleClass G C f i ∪ singleClass G C f j)) :=
      Finset.disjoint_left.mpr fun _ hx hx2 => (Finset.mem_sdiff.mp hx2 |>.2) hx
    have heq : (singleClass G C f i ∪ singleClass G C f j) ∩ boundary G C
        = singleClass G C f i ∪ singleClass G C f j :=
      Finset.Subset.antisymm Finset.inter_subset_left
        (fun x hx => Finset.mem_inter.mpr ⟨hx, hsub hx⟩)
    have hle : (singleClass G C f i ∪ singleClass G C f j).card ≤ (boundary G C).card :=
      Finset.card_le_card hsub
    have hZ : (boundary G C \ (singleClass G C f i ∪ singleClass G C f j)).card
        = (boundary G C).card - (singleClass G C f i ∪ singleClass G C f j).card := by
      have h1 := Finset.card_sdiff (s := singleClass G C f i ∪ singleClass G C f j)
        (t := boundary G C)
      rwa [heq] at h1
    have hstep : (singleClass G C f i ∪ singleClass G C f j).card
        + (boundary G C \ (singleClass G C f i ∪ singleClass G C f j)).card
        ≤ (singleClass G C f i ∪ singleClass G C f j).card
          + ((boundary G C).card - (singleClass G C f i ∪ singleClass G C f j).card) :=
      hZ ▸ Nat.le_refl _
    refine le_trans hstep ?_
    calc (singleClass G C f i ∪ singleClass G C f j).card
        + ((boundary G C).card - (singleClass G C f i ∪ singleClass G C f j).card)
        ≤ (boundary G C).card - (singleClass G C f i ∪ singleClass G C f j).card
            + (singleClass G C f i ∪ singleClass G C f j).card := by
          have hsub' := Nat.sub_add_cancel hle
          omega
      _ = (boundary G C).card := Nat.sub_add_cancel hle

end TwoSingle

/-! ## Part 4 — a new instance of the headline theorem along the book axis -/

section Instance

/-- **A NEW INSTANCE OF THE HEADLINE THEOREM ALONG THE BOOK AXIS OF THE FAN.**  If every odd cycle
`C` of a triangle-free `G` has two single classes `S_i`, `S_j` whose union is a transversal of all
the odd cycles of `G` meeting the boundary of `C`, and whose combined size is at most `q`, then
`LocIndep k G` forces `CloseToBipartite (fanBound (fun _ => q) k) G`.

The difference from `JSP90.erdos73On_of_fan_twoClass` of `JSPProblem/Class.lean` is that the
transversal now lives **in the fan** and is a union of two *disjoint* pieces of the book of `C`, so
its size is bounded, whereas round 70's transversal was a pair of vertices of `C` outside the fan.
No packing number, no odd girth, no packing weight, no bound on the number of branch vertices. -/
theorem fanErdős73_of_fan_singleClassTwo (q : ℕ)
    (hP : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
      ∀ (m : ℕ) (C : Finset W) (f : Fin m → W), IsOddCycle G C →
      ∃ i j : Fin m, (singleClass G C f i ∪ singleClass G C f j).card ≤ q ∧
        HitsOddCycles G (singleClass G C f i ∪ singleClass G C f j)) :
    FanErdős73.{u} (fun _ => q) := by
  intro k W instW G hG hG3 C hC
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hC
  obtain ⟨i, j, hcard, hhits⟩ :=
    hP k W instW G hG hG3 m C f (show IsOddCycle G C from ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩)
  exact ⟨singleClass G C f i ∪ singleClass G C f j, hcard, fun D hD _ => hhits D hD⟩

/-- **ERDŐS PROBLEM #73 FOR THE CLASSES OF THE BOOK OF THE FAN.** -/
theorem erdos73On_of_fan_singleClassTwo (q : ℕ)
    (hP : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
      ∀ (m : ℕ) (C : Finset W) (f : Fin m → W), IsOddCycle G C →
      ∃ i j : Fin m, (singleClass G C f i ∪ singleClass G C f j).card ≤ q ∧
        HitsOddCycles G (singleClass G C f i ∪ singleClass G C f j))
    (k : ℕ) : Erdős73On.{u} k (fanBound (fun _ => q) k) :=
  erdos73On_of_fanErdős73 (fanErdős73_of_fan_singleClassTwo q hP) k

/-- **ERDŐS PROBLEM #73 IN FULL FROM THE BOOK AXIS.** -/
theorem erdos73_of_fan_singleClassTwo (q : ℕ)
    (hP : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
      ∀ (m : ℕ) (C : Finset W) (f : Fin m → W), IsOddCycle G C →
      ∃ i j : Fin m, (singleClass G C f i ∪ singleClass G C f j).card ≤ q ∧
        HitsOddCycles G (singleClass G C f i ∪ singleClass G C f j)) :
    ∀ k, Erdős73.{u} k :=
  erdos73_of_fanErdős73 (fanErdős73_of_fan_singleClassTwo q hP)

/-- **THE BOOK VERSION IS AT LEAST AS STRONG AS THE ATTACHMENT-CLASS VERSION OF ROUND 70.**  A pair
of vertices of `C` whose union of attachment classes is a transversal is *not* assumed here, but
the fan itself may be empty, and then the conclusion is trivial: with `∂C = ∅` the instance holds
with the empty transversal. -/
theorem fanErdős73_of_fan_twoClassSingle (q : ℕ)
    (hP : ∀ (k : ℕ) (W : Type u) (_ : Fintype W) (G : SimpleGraph W), LocIndep k G → G.CliqueFree 3 →
      ∀ (m : ℕ) (C : Finset W) (f : Fin m → W), IsOddCycle G C →
      ∃ i j : Fin m, (singleClass G C f i ∪ singleClass G C f j).card ≤ q ∧
        HitsOddCycles G (singleClass G C f i ∪ singleClass G C f j))
    (k : ℕ) : Erdős73On.{u} k (fanBound (fun _ => q) k) :=
  erdos73On_of_fan_singleClassTwo q hP k

end Instance

end

end JSP90
