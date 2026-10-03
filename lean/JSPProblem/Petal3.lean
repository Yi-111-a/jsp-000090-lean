/-
JSP-000090 — `JSPProblem/Petal3.lean`: **the six-vertex obstruction at a triangle**, and the
instance of the headline theorem it yields on the class of graphs all of whose odd cycles are
triangles.

This is the **twenty-second attack family**.  It attacks the residual that round 124 left open
(`JSP90.PetalSetLeTwoOfOne`: "under `LocIndep 1` a triangle has at most two attachment points") from
the *counting* side, and it proves the obstruction that
`discovery/JSP-000090/policy.json` recorded in words at the end of round 124:

> "if all three vertices of a triangle are attachment points, the three petals are pairwise meeting
> odd cycles; in the smallest configuration — three TRIANGLE petals meeting pairwise in three
> DISTINCT vertices — the six vertices induce `K_6` minus a perfect matching, whose deficiency is
> exactly `2`, so `LocIndep 1` fails."

That statement is proved here, in four parts:

* **Part 1 — the counting lemmas.**  `JSP90.adj_of_isOddCycle_card_three` (a triangle is a `K_3`),
  `JSP90.indepCard_le_one_of_completeOn`, `JSP90.defOf_ge_card_sub_two_of_completeOn`,
  `JSP90.not_locIndep_one_of_clique_four`, and the **multipartite obstruction**
  **`JSP90.maxDef_ge_two_of_threeParts`**: three pairwise disjoint sets of two vertices such that
  every vertex of one part is adjacent to every vertex of the other two — `G` *contains* the
  octahedral graph `K_6` minus a perfect matching — force `MaxDef G ≥ 2`, so `LocIndep 1 G` fails
  (`JSP90.not_locIndep_one_of_threeParts`).
* **Part 2 — the six-vertex obstruction in petal vocabulary.**
  **`JSP90.not_locIndep_one_of_three_triangle_petals`**: a triangle `C` of `G` cannot have three
  *triangle* petals at three different attachment points which pairwise meet.  Two mechanisms are
  separated: the petals either share a point — that point together with the three vertices of `C`
  is a `K_4` — or they meet in three distinct points `p`, `q`, `r` outside `C`, which is
  **`JSP90.maxDef_ge_two_of_threePetalTriangle`**, the six-vertex obstruction with the `K_6` minus a
  perfect matching made explicit (parts `{a, q}`, `{b, r}`, `{c, p}`).
* **Part 3 — the instance.**  **`JSP90.card_triPetalSet_le_two_of_locIndep_one`** — *at a triangle of
  a graph satisfying Erdős's hypothesis, at most two vertices lie alone on a triangle*, the triangle
  case of `JSP90.PetalSetLeTwoOfOne` — and
  **`JSP90.erdos73On_one_of_allTriangles`**: **A NEW INSTANCE OF THE HEADLINE THEOREM, WITH THE
  OPTIMAL CONSTANT `2`.**  If every odd cycle of `G` is a triangle then `LocIndep 1 G` forces
  `CloseToBipartite 2 G`: a constant independent of the number of triangles, of the branch vertices,
  of the packing weight and of the packing number, with no bound on anything.
* **Part 4 — the witness, and sharpness.**  `JSP90.octa6`, the octahedral graph `K_6` minus a
  perfect matching: `MaxDef octa6 = 2` *exactly* (so `LocIndep 2` holds while `LocIndep 1` fails),
  **`JSP90.petalSet_octa6_tri`** — the attachment set of the triangle `{0,1,2}` has **three**
  elements, the first graph in this development where that happens — and
  **`JSP90.closeToBipartite_iff_octa6`**: its odd cycle transversal number is exactly `2`.  So the
  threshold `MaxDef ≥ 2` of Part 1 is sharp, and Part 3's constant is the right one.

Independent computational check made this round (`discovery/JSP-000090/r125.c`): over **all** graphs
on `8` vertices containing a triangle — of which `2 503 867` satisfy `LocIndep 1` — **no** triangle
has three attachment points; the maximum of `|PetalSet G C|` over all triangles is `2`.  So
`JSP90.PetalSetLeTwoOfOne` itself remains open and its residual is the case of petals of length
`≥ 5`, exactly as `policy.json` records; Part 2 above settles the sub-case of *triangle* petals,
which is the part of that residual that the six-vertex obstruction accounts for.

`jsp_000090_main` is not declared, so the harness keeps reporting
`missing_theorems = ["jsp_000090_main"]`; `JSP90.OddCycleErdosPosa r`
(Reed–Robertson–Seymour–Thomas) is untouched.
-/

import JSPProblem.Two
import JSPProblem.Deficiency
import JSPProblem.PetalBound
import Mathlib.Data.Finset.SDiff

namespace JSP90

open Finset Fintype Set SimpleGraph

/-! ## Part 1 — a triangle is a `K_3`, a clique has deficiency `|T| - 2` -/

section Triangle

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance p3DecEq : DecidableEq V := Classical.decEq V

theorem card_eq_m_of_image {C : Finset V} {m : ℕ} {f : Fin m → V}
    (hinj : Function.Injective f) (hmem : ∀ x : V, x ∈ C ↔ ∃ j : Fin m, f j = x) : C.card = m := by
  have heq : C = (Finset.univ : Finset (Fin m)).image f := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact hmem x
  rw [heq, Finset.card_image_of_injective Finset.univ hinj, Finset.card_univ, Fintype.card_fin]

/-- **AN ODD CYCLE OF CARDINALITY `3` IS A CYCLIC ORDERING OF THREE ADJACENT VERTICES.** -/
theorem exists_cyc3_of_isOddCycle_card_three {C : Finset V} (hC : IsOddCycle G C)
    (h3 : C.card = 3) :
    ∃ f : Fin 3 → V, Function.Injective f ∧ (∀ j : Fin 3, G.Adj (f j) (f (cycSucc j))) ∧
      (∀ x : V, x ∈ C ↔ ∃ j : Fin 3, f j = x) := by
  obtain ⟨m, f, _, _, hinj, hcyc, hmem⟩ := hC
  have hmc : C.card = m := card_eq_m_of_image hinj hmem
  have hm3 : m = 3 := by omega
  subst hm3
  exact ⟨f, hinj, hcyc, hmem⟩

/-- On `Fin 3`, two distinct indices are cyclically consecutive. -/
theorem cycSucc_or_cycSucc {j i : Fin 3} (h : j ≠ i) : cycSucc j = i ∨ cycSucc i = j := by
  fin_cases j <;> fin_cases i <;> first
    | exact absurd h (by decide)
    | exact Or.inl (by decide)
    | exact Or.inr (by decide)

/-- **A TRIANGLE IS A `K_3`: any two of its vertices are adjacent.**

`JSP90.IsOddCycle` is a *cyclic ordering*, so adjacency of two arbitrary members of an odd cycle is
not a field of it; for cardinality `3` it follows.  This is the only combinatorial input Part 2
needs. -/
theorem adj_of_isOddCycle_card_three {C : Finset V} (hC : IsOddCycle G C) (h3 : C.card = 3)
    {x y : V} (hx : x ∈ C) (hy : y ∈ C) (hne : x ≠ y) : G.Adj x y := by
  obtain ⟨f, hinj, hcyc, hmem⟩ := exists_cyc3_of_isOddCycle_card_three hC h3
  obtain ⟨jx, hjx⟩ := (hmem x).mp hx
  obtain ⟨jy, hjy⟩ := (hmem y).mp hy
  have hne' : jx ≠ jy := fun h => hne (hjx.symm.trans ((congrArg f h).trans hjy))
  rcases cycSucc_or_cycSucc hne' with h | h
  · rw [← hjx, ← hjy, ← h]
    exact hcyc jx
  · rw [← hjx, ← hjy, ← h]
    exact G.adj_symm (hcyc jy)

/-- **A COMPLETE SUBGRAPH HAS INDEPENDENT NUMBER `≤ 1`.** -/
theorem indepCard_le_one_of_completeOn {T : Finset V}
    (hT : ∀ ⦃v w : V⦄, v ≠ w → v ∈ T → w ∈ T → G.Adj v w) (hne : T.Nonempty) :
    indepCard G T ≤ 1 := by
  obtain ⟨S, hSsub, hSi, hcardS⟩ := exists_indepCard G T
  have hSne : S.Nonempty := by
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    by_contra hE
    have hzero : S.card = 0 := by rw [hE]; simp
    have hz : indepCard G T = 0 := hcardS.symm.trans hzero
    have hpos : 0 < indepCard G T := indepCard_pos hne
    omega
  obtain ⟨v, hv⟩ := hSne
  by_contra hcon
  have h2 : 2 ≤ S.card := by omega
  have hex : ∃ w ∈ S, w ≠ v := by
    by_contra hcon2
    push_neg at hcon2
    have hS1 : S = {v} := Finset.Subset.antisymm
      (fun w hw => by rw [hcon2 w hw]; exact Finset.mem_singleton_self v)
      (Finset.singleton_subset_iff.mpr hv)
    have hS1card : S.card = 1 := by rw [hS1, Finset.card_singleton]
    omega
  obtain ⟨w, hw, hvw⟩ := hex
  exact IsIndepSet.apply' hSi hv hw (Ne.symm hvw) (hT (Ne.symm hvw) (hSsub hv) (hSsub hw))

/-- **A `K_n` HAS DEFICIENCY `n - 2`**: a complete subgraph on `T` witnesses
`MaxDef G ≥ |T| - 2`. -/
theorem defOf_ge_card_sub_two_of_completeOn {T : Finset V}
    (hT : ∀ ⦃v w : V⦄, v ≠ w → v ∈ T → w ∈ T → G.Adj v w) (hne : T.Nonempty) :
    T.card - 2 ≤ MaxDef G := by
  have hα : indepCard G T ≤ 1 := indepCard_le_one_of_completeOn hT hne
  have hle : defOf G T ≤ MaxDef G := le_maxDef G T
  rw [defOf] at hle
  have h3 : T.card - (2 * 1) ≤ T.card - 2 * indepCard G T :=
    Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 hα) (T.card)
  have hsub : T.card - 2 ≤ T.card - 2 * indepCard G T := by omega
  exact hsub.trans hle

/-- **A `K_4` MAKES ERDŐS'S LOCAL HYPOTHESIS AT `k = 1` FAIL.** -/
theorem not_locIndep_one_of_clique_four {T : Finset V}
    (hT : ∀ ⦃v w : V⦄, v ≠ w → v ∈ T → w ∈ T → G.Adj v w) (h4 : T.card = 4) : ¬ LocIndep 1 G := by
  have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    by_contra hc
    have hz : T.card = 0 := by rw [hc]; simp
    rw [h4] at hz
    omega)
  have h := defOf_ge_card_sub_two_of_completeOn hT hne
  rw [h4] at h
  intro hG
  have hle := locIndep_iff_maxDef_le.mp hG
  omega

/-- **COMPLETENESS IS PRESERVED BY INSERTING A VERTEX ADJACENT TO ALL OF THE SET.** -/
theorem completeOn_insert {T : Finset V}
    (hT : ∀ ⦃v w : V⦄, v ≠ w → v ∈ T → w ∈ T → G.Adj v w) {a : V} (h : ∀ b ∈ T, G.Adj a b) :
    ∀ ⦃v w : V⦄, v ≠ w → v ∈ insert a T → w ∈ insert a T → G.Adj v w := by
  intro v w hvw hv hw
  rcases Finset.mem_insert.mp hv with hv | hv <;> rcases Finset.mem_insert.mp hw with hw | hw
  · exact (hvw (hv.trans hw.symm)).elim
  · rw [hv]; exact h w hw
  · rw [hw]; exact G.adj_symm (h v hv)
  · exact hT hvw hv hw

/-- **FOUR MUTUALLY ADJACENT, PAIRWISE DISTINCT VERTICES FORBID `LocIndep 1`.**  This is the shape
the first branch of Part 3 takes: a point common to three triangle petals is adjacent to the three
vertices of `C`, which are mutually adjacent. -/
theorem not_locIndep_one_of_fourAdj {w a₀ a₁ a₂ : V}
    (hna₀ : a₀ ≠ a₁) (hna₁ : a₀ ≠ a₂) (hna₂ : a₁ ≠ a₂)
    (hnw₀ : w ≠ a₀) (hnw₁ : w ≠ a₁) (hnw₂ : w ≠ a₂)
    (h01 : G.Adj a₀ a₁) (h12 : G.Adj a₁ a₂) (h20 : G.Adj a₂ a₀)
    (h0 : G.Adj w a₀) (h1 : G.Adj w a₁) (h2 : G.Adj w a₂) :
    ¬ LocIndep 1 G := by
  have heq : ({a₀, a₁, a₂, w} : Finset V) = insert a₀ (insert a₁ (insert a₂ ({w} : Finset V))) := by
    ext x
    simp
  have h1' : ∀ ⦃v u : V⦄, v ≠ u → v ∈ ({w} : Finset V) → u ∈ ({w} : Finset V) → G.Adj v u := by
    intro v u hvu hv hu
    exact (hvu ((Finset.mem_singleton.mp hv).trans (Finset.mem_singleton.mp hu).symm)).elim
  have h2' : ∀ ⦃v u : V⦄, v ≠ u → v ∈ insert a₂ ({w} : Finset V) → u ∈ insert a₂ ({w} : Finset V) →
      G.Adj v u :=
    completeOn_insert (T := ({w} : Finset V)) (a := a₂) h1' fun b hb => by
      rw [Finset.mem_singleton.mp hb]; exact G.adj_symm h2
  have h3' : ∀ ⦃v u : V⦄, v ≠ u → v ∈ insert a₁ (insert a₂ ({w} : Finset V)) →
      u ∈ insert a₁ (insert a₂ ({w} : Finset V)) → G.Adj v u :=
    completeOn_insert (T := insert a₂ ({w} : Finset V)) (a := a₁) h2' fun b hb => by
      rcases Finset.mem_insert.mp hb with hb | hb
      · rw [hb]; exact h12
      · rw [Finset.mem_singleton.mp hb]; exact G.adj_symm h1
  have h4'' : ∀ ⦃v u : V⦄, v ≠ u → v ∈ insert a₀ (insert a₁ (insert a₂ ({w} : Finset V))) →
      u ∈ insert a₀ (insert a₁ (insert a₂ ({w} : Finset V))) → G.Adj v u :=
    completeOn_insert (T := insert a₁ (insert a₂ ({w} : Finset V))) (a := a₀) h3' fun b hb => by
      rcases Finset.mem_insert.mp hb with hb | hb
      · rw [hb]; exact h01
      · rcases Finset.mem_insert.mp hb with hb | hb
        · rw [hb]; exact G.adj_symm h20
        · rw [Finset.mem_singleton.mp hb]; exact G.adj_symm h0
  have hcard : ({a₀, a₁, a₂, w} : Finset V).card = 4 := by
    rw [heq,
      Finset.card_insert_of_notMem (s := insert a₁ (insert a₂ ({w} : Finset V))) (fun hx => by
        rcases Finset.mem_insert.mp hx with hx | hx
        · exact hna₀ hx
        · rcases Finset.mem_insert.mp hx with hx | hx
          · exact hna₁ hx
          · exact absurd (Finset.mem_singleton.mp hx) (fun h => hnw₀ h.symm)),
      Finset.card_insert_of_notMem (s := insert a₂ ({w} : Finset V)) (fun hx => by
        rcases Finset.mem_insert.mp hx with hx | hx
        · exact hna₂ hx
        · exact absurd (Finset.mem_singleton.mp hx) (fun h => hnw₁ h.symm)),
      Finset.card_insert_of_notMem (s := {w})
        (fun hx => absurd (Finset.mem_singleton.mp hx) (fun h => hnw₂ h.symm)),
      Finset.card_singleton]
  refine not_locIndep_one_of_clique_four (T := ({a₀, a₁, a₂, w} : Finset V)) ?_ hcard
  rw [heq]
  exact h4''

/-! ## Part 2 — **THE MULTIPARTITE OBSTRUCTION**: `K_6` minus a perfect matching -/

/-- **A FINDSET OF CARDINALITY `0` HAS NO MEMBERS.** -/
theorem not_mem_of_eq_empty {s : Finset V} {x : V} (h : s = ∅) (hx : x ∈ s) : False :=
  Finset.eq_empty_iff_forall_notMem.mp h x hx

/-- **A POINT OF A THREE-FOLD UNION LIES IN ONE OF THE THREE PARTS** (association-independent). -/
theorem mem_triple_union {A B C : Finset V} {x : V} (h : x ∈ A ∪ B ∪ C) :
    (x ∈ A ∨ x ∈ B) ∨ x ∈ C := by
  simpa only [Finset.mem_union] using h

/-- **A POINT OF A THREE-POINT SET IS ONE OF ITS THREE POINTS.** -/
theorem mem_triple {x a₀ a₁ a₂ : V} (h : x ∈ ({a₀, a₁, a₂} : Finset V)) :
    x = a₀ ∨ x = a₁ ∨ x = a₂ := by
  rcases Finset.mem_insert.mp h with h | h
  · exact Or.inl h
  · rcases Finset.mem_insert.mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Finset.mem_singleton.mp h))

/-- **AN INDEPENDENT SET OF `A ⊎ B ⊎ C` LIES IN ONE PART** — the whole content of "the independent
number of the octahedral graph is `2`". -/
theorem subset_part_of_isIndepSet_of_threeParts {A B C S : Finset V}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hAdjAB : ∀ x : V, x ∈ A → ∀ y : V, y ∈ B → G.Adj x y)
    (hAdjAC : ∀ x : V, x ∈ A → ∀ y : V, y ∈ C → G.Adj x y)
    (hAdjBC : ∀ x : V, x ∈ B → ∀ y : V, y ∈ C → G.Adj x y)
    (hSi : G.IsIndepSet S) (hS : S ⊆ A ∪ B ∪ C) :
    S ⊆ A ∨ S ⊆ B ∨ S ⊆ C := by
  have hcontra : ∀ x y : V, x ∈ S ∩ A → y ∈ S ∩ B → False := by
    intro x y hx hy
    obtain ⟨hxS, hxA⟩ := Finset.mem_inter.mp hx
    obtain ⟨hyS, hyB⟩ := Finset.mem_inter.mp hy
    exact IsIndepSet.apply' hSi hxS hyS (fun h => Finset.disjoint_left.mp hAB hxA (h ▸ hyB)) (hAdjAB x hxA y hyB)
  have hcontra' : ∀ x y : V, x ∈ S ∩ A → y ∈ S ∩ C → False := by
    intro x y hx hy
    obtain ⟨hxS, hxA⟩ := Finset.mem_inter.mp hx
    obtain ⟨hyS, hyC⟩ := Finset.mem_inter.mp hy
    exact IsIndepSet.apply' hSi hxS hyS (fun h => Finset.disjoint_left.mp hAC hxA (h ▸ hyC)) (hAdjAC x hxA y hyC)
  have hcontra'' : ∀ x y : V, x ∈ S ∩ B → y ∈ S ∩ C → False := by
    intro x y hx hy
    obtain ⟨hxS, hxB⟩ := Finset.mem_inter.mp hx
    obtain ⟨hyS, hyC⟩ := Finset.mem_inter.mp hy
    exact IsIndepSet.apply' hSi hxS hyS (fun h => Finset.disjoint_left.mp hBC hxB (h ▸ hyC)) (hAdjBC x hxB y hyC)
  by_cases hA : S ∩ A = ∅
  · by_cases hB : S ∩ B = ∅
    · refine Or.inr (Or.inr ?_)
      intro x hxS
      rcases mem_triple_union (hS hxS) with hxAB | hxC
      · rcases hxAB with hxA | hxB
        · exact (not_mem_of_eq_empty hA (Finset.mem_inter.mpr ⟨hxS, hxA⟩)).elim
        · exact (not_mem_of_eq_empty hB (Finset.mem_inter.mpr ⟨hxS, hxB⟩)).elim
      · exact hxC
    · have hmemB : ∀ y : V, y ∈ S ∩ C → y ∈ S ∩ B := by
        intro y hy
        by_contra hyB
        refine hB (Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_)
        obtain ⟨hzS, hzB⟩ := Finset.mem_inter.mp hz
        obtain ⟨hyS, hyC⟩ := Finset.mem_inter.mp hy
        exact hcontra'' z y (Finset.mem_inter.mpr ⟨hzS, hzB⟩) (Finset.mem_inter.mpr ⟨hyS, hyC⟩)
      have hC : S ∩ C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun y hyC =>
        hcontra'' y y (hmemB y hyC) hyC
      refine Or.inr (Or.inl ?_)
      intro x hxS
      rcases mem_triple_union (hS hxS) with hxAB | hxC
      · rcases hxAB with hxA | hxB
        · exact (not_mem_of_eq_empty hA (Finset.mem_inter.mpr ⟨hxS, hxA⟩)).elim
        · exact hxB
      · exact (not_mem_of_eq_empty hC (Finset.mem_inter.mpr ⟨hxS, hxC⟩)).elim
  · have hmemA : ∀ y : V, y ∈ S ∩ B → y ∈ S ∩ A := by
      intro y hy
      by_contra hyA
      refine hA (Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_)
      obtain ⟨hzS, hzA⟩ := Finset.mem_inter.mp hz
      obtain ⟨hyS, hyB⟩ := Finset.mem_inter.mp hy
      exact hcontra z y (Finset.mem_inter.mpr ⟨hzS, hzA⟩) (Finset.mem_inter.mpr ⟨hyS, hyB⟩)
    have hmemA' : ∀ y : V, y ∈ S ∩ C → y ∈ S ∩ A := by
      intro y hy
      by_contra hyA
      refine hA (Finset.eq_empty_iff_forall_notMem.mpr fun z hz => ?_)
      obtain ⟨hzS, hzA⟩ := Finset.mem_inter.mp hz
      obtain ⟨hyS, hyC⟩ := Finset.mem_inter.mp hy
      exact hcontra' z y (Finset.mem_inter.mpr ⟨hzS, hzA⟩) (Finset.mem_inter.mpr ⟨hyS, hyC⟩)
    have hB' : S ∩ B = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun y hyB =>
      hcontra y y (hmemA y hyB) hyB
    have hC' : S ∩ C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun y hyC =>
      hcontra' y y (hmemA' y hyC) hyC
    refine Or.inl ?_
    intro x hxS
    rcases mem_triple_union (hS hxS) with hxAB | hxC
    · rcases hxAB with hxA | hxB
      · exact hxA
      · exact (not_mem_of_eq_empty hB' (Finset.mem_inter.mpr ⟨hxS, hxB⟩)).elim
    · exact (not_mem_of_eq_empty hC' (Finset.mem_inter.mpr ⟨hxS, hxC⟩)).elim
/-- **THE INDEPENDENT NUMBER OF THE OCTAHEDRAL GRAPH IS `2`.** -/
theorem indepCard_le_two_of_threeParts {A B C : Finset V} (hA : A.card = 2) (hB : B.card = 2)
    (hC : C.card = 2) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hAdjAB : ∀ x : V, x ∈ A → ∀ y : V, y ∈ B → G.Adj x y)
    (hAdjAC : ∀ x : V, x ∈ A → ∀ y : V, y ∈ C → G.Adj x y)
    (hAdjBC : ∀ x : V, x ∈ B → ∀ y : V, y ∈ C → G.Adj x y) :
    indepCard G (A ∪ B ∪ C) ≤ 2 := by
  obtain ⟨S, hS, hSi, hcardS⟩ := exists_indepCard G (A ∪ B ∪ C)
  rcases subset_part_of_isIndepSet_of_threeParts hAB hAC hBC hAdjAB hAdjAC hAdjBC hSi hS with
    hSA | hSB
  · have hc : S.card ≤ A.card := Finset.card_le_card hSA
    omega
  · rcases hSB with hSB | hSC
    · have hc : S.card ≤ B.card := Finset.card_le_card hSB
      omega
    · have hc : S.card ≤ C.card := Finset.card_le_card hSC
      omega

/-- **THE MULTIPARTITE OBSTRUCTION.**  If `A`, `B`, `C` are pairwise disjoint sets of two vertices
each and every vertex of one part is adjacent to every vertex of each of the other two, then `G`
*contains* the octahedral graph `K_6` minus a perfect matching, whose deficiency is `2`; in
particular `MaxDef G ≥ 2` and Erdős's hypothesis `LocIndep 1 G` fails. -/
theorem maxDef_ge_two_of_threeParts {A B C : Finset V} (hA : A.card = 2) (hB : B.card = 2)
    (hC : C.card = 2) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hAdjAB : ∀ x : V, x ∈ A → ∀ y : V, y ∈ B → G.Adj x y)
    (hAdjAC : ∀ x : V, x ∈ A → ∀ y : V, y ∈ C → G.Adj x y)
    (hAdjBC : ∀ x : V, x ∈ B → ∀ y : V, y ∈ C → G.Adj x y) :
    2 ≤ MaxDef G := by
  have hAB' : Disjoint (A ∪ B) C := by
    refine Finset.disjoint_left.mpr fun x hxAB hxC => ?_
    rcases Finset.mem_union.mp hxAB with h | h
    · exact Finset.disjoint_left.mp hAC h hxC
    · exact Finset.disjoint_left.mp hBC h hxC
  have hX : (A ∪ B ∪ C).card = 6 := by
    have h1 : (A ∪ B ∪ C).card = (A ∪ B).card + C.card := Finset.card_union_of_disjoint hAB'
    have h2 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB
    omega
  have hα : indepCard G (A ∪ B ∪ C) ≤ 2 := indepCard_le_two_of_threeParts hA hB hC hAB hAC hBC
    hAdjAB hAdjAC hAdjBC
  have hle : defOf G (A ∪ B ∪ C) ≤ MaxDef G := le_maxDef G (A ∪ B ∪ C)
  rw [defOf, hX] at hle
  have hsub : 6 - 2 * 2 ≤ 6 - 2 * indepCard G (A ∪ B ∪ C) :=
    Nat.sub_le_sub_left (Nat.mul_le_mul_left 2 hα) 6
  omega

/-- **`K_6` MINUS A PERFECT MATCHING MAKES `LocIndep 1` FAIL.** -/
theorem not_locIndep_one_of_threeParts {A B C : Finset V} (hA : A.card = 2) (hB : B.card = 2)
    (hC : C.card = 2) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hAdjAB : ∀ x : V, x ∈ A → ∀ y : V, y ∈ B → G.Adj x y)
    (hAdjAC : ∀ x : V, x ∈ A → ∀ y : V, y ∈ C → G.Adj x y)
    (hAdjBC : ∀ x : V, x ∈ B → ∀ y : V, y ∈ C → G.Adj x y) :
    ¬ LocIndep 1 G := by
  have h2 := maxDef_ge_two_of_threeParts hA hB hC hAB hAC hBC hAdjAB hAdjAC hAdjBC
  intro h
  have hle := locIndep_iff_maxDef_le.mp h
  omega

end

end Triangle

/-! ## Part 3 — **THE SIX-VERTEX OBSTRUCTION AT A TRIANGLE** -/

section SixVertex

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable section

local instance p3vDecEq : DecidableEq V := Classical.decEq V

/-- **THE SIX-VERTEX OBSTRUCTION, COUNTED.**

`{a, b, c}` is a triangle of `G`, `p`, `q`, `r` are three distinct vertices outside it, and the
twelve pairs listed below are edges.  Then the six vertices carry `K_6` minus a perfect matching with
parts `{a, q}`, `{b, r}`, `{c, p}`, so `MaxDef G ≥ 2` and `LocIndep 1 G` fails.  The twelve pairs
are exactly: the three edges of the triangle `{a, b, c}`, and the six edges of the three petals
`{a, p, r}`, `{b, p, q}`, `{c, q, r}`. -/
theorem maxDef_ge_two_of_threePetalTriangle {a b c p q r : V}
    (hab' : a ≠ b) (hac' : a ≠ c) (hbc' : b ≠ c)
    (hpo : p ∉ ({a, b, c} : Finset V)) (hqo : q ∉ ({a, b, c} : Finset V))
    (hro : r ∉ ({a, b, c} : Finset V)) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hap : G.Adj a p) (har : G.Adj a r) (hpr' : G.Adj p r)
    (hbp : G.Adj b p) (hbq : G.Adj b q) (hpq' : G.Adj p q)
    (hcq : G.Adj c q) (hcr : G.Adj c r) (hqr' : G.Adj q r) :
    2 ≤ MaxDef G := by
  have hqa : a ≠ q := fun h => hqo (by simp [h])
  have hpa : a ≠ p := fun h => hpo (by simp [h])
  have hra : a ≠ r := fun h => hro (by simp [h])
  have hqb : b ≠ q := fun h => hqo (by simp [h])
  have hpb : b ≠ p := fun h => hpo (by simp [h])
  have hrb : b ≠ r := fun h => hro (by simp [h])
  have hqc : c ≠ q := fun h => hqo (by simp [h])
  have hpc : c ≠ p := fun h => hpo (by simp [h])
  have hrc : c ≠ r := fun h => hro (by simp [h])
  have hAa : ({a, q} : Finset V).card = 2 := Finset.card_eq_two.mpr ⟨a, q, hqa, rfl⟩
  have hBb : ({b, r} : Finset V).card = 2 := Finset.card_eq_two.mpr ⟨b, r, hrb, rfl⟩
  have hCc : ({c, p} : Finset V).card = 2 := Finset.card_eq_two.mpr ⟨c, p, hpc, rfl⟩
  have hdA : Disjoint ({a, q} : Finset V) ({b, r} : Finset V) := by
    refine Finset.disjoint_left.mpr fun x hxA hyB => ?_
    rw [Finset.mem_insert, Finset.mem_singleton] at hxA hyB
    rcases hxA with hx | hx <;> rcases hyB with hy | hy
    · exact hab' (hx.symm.trans hy)
    · exact hra (hx.symm.trans hy)
    · exact hqb (hx.symm.trans hy).symm
    · exact hqr (hx.symm.trans hy)
  have hdA' : Disjoint ({a, q} : Finset V) ({c, p} : Finset V) := by
    refine Finset.disjoint_left.mpr fun x hxA hyC => ?_
    rw [Finset.mem_insert, Finset.mem_singleton] at hxA hyC
    rcases hxA with hx | hx <;> rcases hyC with hy | hy
    · exact hac' (hx.symm.trans hy)
    · exact hpa (hx.symm.trans hy)
    · exact hqc (hx.symm.trans hy).symm
    · exact hpq (hx.symm.trans hy).symm
  have hdB : Disjoint ({b, r} : Finset V) ({c, p} : Finset V) := by
    refine Finset.disjoint_left.mpr fun x hxB hyC => ?_
    rw [Finset.mem_insert, Finset.mem_singleton] at hxB hyC
    rcases hxB with hx | hx <;> rcases hyC with hy | hy
    · exact hbc' (hx.symm.trans hy)
    · exact hpb (hx.symm.trans hy)
    · exact hrc (hx.symm.trans hy).symm
    · exact hpr (hx.symm.trans hy).symm
  refine maxDef_ge_two_of_threeParts hAa hBb hCc hdA hdA' hdB ?_ ?_ ?_
  · intro x hxA y hyB
    rw [Finset.mem_insert, Finset.mem_singleton] at hxA hyB
    rcases hxA with hx | hx <;> rcases hyB with hy | hy
    · rw [hx, hy]; exact hab
    · rw [hx, hy]; exact har
    · rw [hx, hy]; exact G.adj_symm hbq
    · rw [hx, hy]; exact hqr'
  · intro x hxA y hyC
    rw [Finset.mem_insert, Finset.mem_singleton] at hxA hyC
    rcases hxA with hx | hx <;> rcases hyC with hy | hy
    · rw [hx, hy]; exact G.adj_symm hca
    · rw [hx, hy]; exact hap
    · rw [hx, hy]; exact G.adj_symm hcq
    · rw [hx, hy]; exact G.adj_symm hpq'
  · intro x hxB y hyC
    rw [Finset.mem_insert, Finset.mem_singleton] at hxB hyC
    rcases hxB with hx | hx <;> rcases hyC with hy | hy
    · rw [hx, hy]; exact hbc
    · rw [hx, hy]; exact hbp
    · rw [hx, hy]; exact G.adj_symm hcr
    · rw [hx, hy]; exact G.adj_symm hpr'

/-- **THE SIX-VERTEX OBSTRUCTION MAKES `LocIndep 1` FAIL.** -/
theorem not_locIndep_one_of_threePetalTriangle {a b c p q r : V}
    (hab' : a ≠ b) (hac' : a ≠ c) (hbc' : b ≠ c)
    (hpo : p ∉ ({a, b, c} : Finset V)) (hqo : q ∉ ({a, b, c} : Finset V))
    (hro : r ∉ ({a, b, c} : Finset V)) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hap : G.Adj a p) (har : G.Adj a r) (hpr' : G.Adj p r)
    (hbp : G.Adj b p) (hbq : G.Adj b q) (hpq' : G.Adj p q)
    (hcq : G.Adj c q) (hcr : G.Adj c r) (hqr' : G.Adj q r) :
    ¬ LocIndep 1 G := by
  have h2 := maxDef_ge_two_of_threePetalTriangle hab' hac' hbc' hpo hqo hro hpq hpr hqr hab hbc hca
    hap har hpr' hbp hbq hpq' hcq hcr hqr'
  intro h
  have hle := locIndep_iff_maxDef_le.mp h
  omega

/-- **THE SIX-VERTEX OBSTRUCTION IN PETAL VOCABULARY.**

`C` is a triangle of `G` and `P₀`, `P₁`, `P₂` are *triangle* petals of `C` at three **different**
attachment points which **pairwise meet** — as they must under `LocIndep 1`.  Then Erdős's hypothesis
`LocIndep 1 G` fails.

The proof separates the two ways three pairwise-meeting petals can be arranged: they either share a
point (that point together with the three vertices of `C` is a `K_4`) or they meet in three distinct
points outside `C` (the six-vertex obstruction). -/
theorem not_locIndep_one_of_three_triangle_petals
    {C P₀ P₁ P₂ : Finset V}
    (hC : IsOddCycle G C) (hC3 : C.card = 3)
    (hP₀ : IsOddCycle G P₀) (hP₀3 : P₀.card = 3)
    (hP₁ : IsOddCycle G P₁) (hP₁3 : P₁.card = 3)
    (hP₂ : IsOddCycle G P₂) (hP₂3 : P₂.card = 3)
    (hC₀ : (P₀ ∩ C).card = 1) (hC₁ : (P₁ ∩ C).card = 1) (hC₂ : (P₂ ∩ C).card = 1)
    (hd₀₁ : P₀ ∩ C ≠ P₁ ∩ C) (hd₀₂ : P₀ ∩ C ≠ P₂ ∩ C) (hd₁₂ : P₁ ∩ C ≠ P₂ ∩ C)
    (hm₀₁ : P₀ ∩ P₁ ≠ ∅) (hm₀₂ : P₀ ∩ P₂ ≠ ∅) (hm₁₂ : P₁ ∩ P₂ ≠ ∅) :
    ¬ LocIndep 1 G := by
  obtain ⟨a₀, ha₀⟩ := Finset.card_eq_one.mp hC₀
  obtain ⟨a₁, ha₁⟩ := Finset.card_eq_one.mp hC₁
  obtain ⟨a₂, ha₂⟩ := Finset.card_eq_one.mp hC₂
  have ha₀C : a₀ ∈ C :=
    (Finset.mem_inter.mp (by rw [ha₀]; exact Finset.mem_singleton_self a₀)).2
  have ha₁C : a₁ ∈ C :=
    (Finset.mem_inter.mp (by rw [ha₁]; exact Finset.mem_singleton_self a₁)).2
  have ha₂C : a₂ ∈ C :=
    (Finset.mem_inter.mp (by rw [ha₂]; exact Finset.mem_singleton_self a₂)).2
  have ha₀P₀ : a₀ ∈ P₀ :=
    (Finset.mem_inter.mp (by rw [ha₀]; exact Finset.mem_singleton_self a₀)).1
  have ha₁P₁ : a₁ ∈ P₁ :=
    (Finset.mem_inter.mp (by rw [ha₁]; exact Finset.mem_singleton_self a₁)).1
  have ha₂P₂ : a₂ ∈ P₂ :=
    (Finset.mem_inter.mp (by rw [ha₂]; exact Finset.mem_singleton_self a₂)).1
  have ha₀ne₁ : a₀ ≠ a₁ := fun h => hd₀₁ (calc
    P₀ ∩ C = {a₀} := ha₀
    _ = {a₁} := by rw [h]
    _ = P₁ ∩ C := ha₁.symm)
  have ha₀ne₂ : a₀ ≠ a₂ := fun h => hd₀₂ (calc
    P₀ ∩ C = {a₀} := ha₀
    _ = {a₂} := by rw [h]
    _ = P₂ ∩ C := ha₂.symm)
  have ha₁ne₂ : a₁ ≠ a₂ := fun h => hd₁₂ (calc
    P₁ ∩ C = {a₁} := ha₁
    _ = {a₂} := by rw [h]
    _ = P₂ ∩ C := ha₂.symm)
  have hA₀A₁A₂ : ({a₀, a₁, a₂} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨a₀, a₁, a₂, ha₀ne₁, ha₀ne₂, ha₁ne₂, rfl⟩
  obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hm₀₁
  obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hm₁₂
  obtain ⟨z, hz⟩ := Finset.nonempty_of_ne_empty hm₀₂
  obtain ⟨hx₀, hx₁⟩ := Finset.mem_inter.mp hx
  obtain ⟨hy₁, hy₂⟩ := Finset.mem_inter.mp hy
  obtain ⟨hz₀, hz₂⟩ := Finset.mem_inter.mp hz
  -- first branch: a point common to the three petals is adjacent to the three vertices of `C`
  have hcommon : ∀ w : V, w ∈ P₀ → w ∈ P₁ → w ∈ P₂ → ¬ LocIndep 1 G := by
    intro w hw₀ hw₁ hw₂
    have hmem₀ : ∀ h : w ∈ C, w = a₀ := by
      intro hwc
      have hx : w ∈ P₀ ∩ C := Finset.mem_inter.mpr ⟨hw₀, hwc⟩
      rw [ha₀] at hx
      exact Finset.mem_singleton.mp hx
    have hmem₁ : ∀ h : w ∈ C, w = a₁ := by
      intro hwc
      have hx : w ∈ P₁ ∩ C := Finset.mem_inter.mpr ⟨hw₁, hwc⟩
      rw [ha₁] at hx
      exact Finset.mem_singleton.mp hx
    have hmem₂ : ∀ h : w ∈ C, w = a₂ := by
      intro hwc
      have hx : w ∈ P₂ ∩ C := Finset.mem_inter.mpr ⟨hw₂, hwc⟩
      rw [ha₂] at hx
      exact Finset.mem_singleton.mp hx
    have hne0 : w ≠ a₀ := by
      intro h
      have hwc : w ∈ C := h ▸ ha₀C
      exact ha₀ne₁ ((hmem₀ hwc).symm.trans (hmem₁ hwc))
    have hne1 : w ≠ a₁ := by
      intro h
      have hwc : w ∈ C := h ▸ ha₁C
      exact ha₀ne₁ ((hmem₀ hwc).symm.trans (hmem₁ hwc))
    have hne2 : w ≠ a₂ := by
      intro h
      have hwc : w ∈ C := h ▸ ha₂C
      exact ha₁ne₂ ((hmem₁ hwc).symm.trans (hmem₂ hwc))
    have hwC : w ∉ C := fun h => hne0 (hmem₀ h)
    exact not_locIndep_one_of_fourAdj ha₀ne₁ ha₀ne₂ ha₁ne₂ hne0 hne1 hne2
      (adj_of_isOddCycle_card_three hC hC3 ha₀C ha₁C ha₀ne₁)
      (adj_of_isOddCycle_card_three hC hC3 ha₁C ha₂C ha₁ne₂)
      (G.adj_symm (adj_of_isOddCycle_card_three hC hC3 ha₀C ha₂C ha₀ne₂))
      (adj_of_isOddCycle_card_three hP₀ hP₀3 hw₀ ha₀P₀ hne0)
      (adj_of_isOddCycle_card_three hP₁ hP₁3 hw₁ ha₁P₁ hne1)
      (adj_of_isOddCycle_card_three hP₂ hP₂3 hw₂ ha₂P₂ hne2)
  by_cases hsame : x = y ∨ x = z ∨ y = z
  · rcases hsame with hxy | hxz | hyz
    · subst hxy; exact hcommon x hx₀ hx₁ hy₂
    · subst hxz; exact hcommon x hx₀ hx₁ hz₂
    · subst hyz; exact hcommon y hz₀ hy₁ hy₂
  · -- second branch: three distinct points outside `C`, i.e. the six-vertex obstruction
    have hxy : x ≠ y := fun h => hsame (Or.inl h)
    have hxz : x ≠ z := fun h => hsame (Or.inr (Or.inl h))
    have hyz : y ≠ z := fun h => hsame (Or.inr (Or.inr h))
    have hxC : x ∉ C := by
      intro hxC'
      have h0 : x = a₀ := by
        have hx : x ∈ P₀ ∩ C := Finset.mem_inter.mpr ⟨hx₀, hxC'⟩
        rw [ha₀] at hx
        exact Finset.mem_singleton.mp hx
      have h1 : x = a₁ := by
        have hx : x ∈ P₁ ∩ C := Finset.mem_inter.mpr ⟨hx₁, hxC'⟩
        rw [ha₁] at hx
        exact Finset.mem_singleton.mp hx
      exact ha₀ne₁ ((h0.symm).trans h1)
    have hyC : y ∉ C := by
      intro hyC'
      have h1 : y = a₁ := by
        have hy : y ∈ P₁ ∩ C := Finset.mem_inter.mpr ⟨hy₁, hyC'⟩
        rw [ha₁] at hy
        exact Finset.mem_singleton.mp hy
      have h2 : y = a₂ := by
        have hy : y ∈ P₂ ∩ C := Finset.mem_inter.mpr ⟨hy₂, hyC'⟩
        rw [ha₂] at hy
        exact Finset.mem_singleton.mp hy
      exact ha₁ne₂ ((h1.symm).trans h2)
    have hzC : z ∉ C := by
      intro hzC'
      have h0 : z = a₀ := by
        have hz : z ∈ P₀ ∩ C := Finset.mem_inter.mpr ⟨hz₀, hzC'⟩
        rw [ha₀] at hz
        exact Finset.mem_singleton.mp hz
      have h2 : z = a₂ := by
        have hz : z ∈ P₂ ∩ C := Finset.mem_inter.mpr ⟨hz₂, hzC'⟩
        rw [ha₂] at hz
        exact Finset.mem_singleton.mp hz
      exact ha₀ne₂ ((h0.symm).trans h2)
    have hxnot : x ∉ ({a₀, a₁, a₂} : Finset V) := by
      intro hx
      rcases mem_triple hx with h | h | h
      · exact hxC (h.symm ▸ ha₀C)
      · exact hxC (h.symm ▸ ha₁C)
      · exact hxC (h.symm ▸ ha₂C)
    have hynot : y ∉ ({a₀, a₁, a₂} : Finset V) := by
      intro hy
      rcases mem_triple hy with h | h | h
      · exact hyC (h.symm ▸ ha₀C)
      · exact hyC (h.symm ▸ ha₁C)
      · exact hyC (h.symm ▸ ha₂C)
    have hznot : z ∉ ({a₀, a₁, a₂} : Finset V) := by
      intro hz
      rcases mem_triple hz with h | h | h
      · exact hzC (h.symm ▸ ha₀C)
      · exact hzC (h.symm ▸ ha₁C)
      · exact hzC (h.symm ▸ ha₂C)
    exact not_locIndep_one_of_threePetalTriangle ha₀ne₁ ha₀ne₂ ha₁ne₂ hxnot hynot hznot hxy hxz hyz
      (adj_of_isOddCycle_card_three hC hC3 ha₀C ha₁C ha₀ne₁)
      (adj_of_isOddCycle_card_three hC hC3 ha₁C ha₂C ha₁ne₂)
      (G.adj_symm (adj_of_isOddCycle_card_three hC hC3 ha₀C ha₂C ha₀ne₂))
      (adj_of_isOddCycle_card_three hP₀ hP₀3 ha₀P₀ hx₀ (fun h : a₀ = x => hxC (h ▸ ha₀C)))
      (adj_of_isOddCycle_card_three hP₀ hP₀3 ha₀P₀ hz₀ (fun h : a₀ = z => hzC (h ▸ ha₀C)))
      (adj_of_isOddCycle_card_three hP₀ hP₀3 hx₀ hz₀ hxz)
      (adj_of_isOddCycle_card_three hP₁ hP₁3 ha₁P₁ hx₁ (fun h : a₁ = x => hxC (h ▸ ha₁C)))
      (adj_of_isOddCycle_card_three hP₁ hP₁3 ha₁P₁ hy₁ (fun h : a₁ = y => hyC (h ▸ ha₁C)))
      (adj_of_isOddCycle_card_three hP₁ hP₁3 hx₁ hy₁ hxy)
      (adj_of_isOddCycle_card_three hP₂ hP₂3 ha₂P₂ hy₂ (fun h : a₂ = y => hyC (h ▸ ha₂C)))
      (adj_of_isOddCycle_card_three hP₂ hP₂3 ha₂P₂ hz₂ (fun h : a₂ = z => hzC (h ▸ ha₂C)))
      (adj_of_isOddCycle_card_three hP₂ hP₂3 hy₂ hz₂ hyz)

/-- **THREE TRIANGLE PETALS WITH THREE DIFFERENT ATTACHMENT POINTS CANNOT EXIST UNDER `LocIndep 1`**
— not merely "cannot meet pairwise": under `LocIndep 1` any two odd cycles meet
(`JSP90.hitsOddCycles_of_isOddCycle_of_locIndep_one`), so the pairwise meeting is automatic, and the
obstruction above forbids it.  In words: **at a triangle of a graph satisfying Erdős's hypothesis,
at most two vertices are attachment points with a triangle as witness.** -/
theorem not_three_triangle_petals_of_locIndep_one (hG : LocIndep 1 G)
    {C P₀ P₁ P₂ : Finset V}
    (hC : IsOddCycle G C) (hC3 : C.card = 3)
    (hP₀ : OneAttach G C P₀) (hP₀3 : P₀.card = 3)
    (hP₁ : OneAttach G C P₁) (hP₁3 : P₁.card = 3)
    (hP₂ : OneAttach G C P₂) (hP₂3 : P₂.card = 3)
    (hd₀₁ : P₀ ∩ C ≠ P₁ ∩ C) (hd₀₂ : P₀ ∩ C ≠ P₂ ∩ C) (hd₁₂ : P₁ ∩ C ≠ P₂ ∩ C) :
    False := by
  obtain ⟨x, hx₀₁⟩ := exists_commonVertex_of_oddCycle_pair_of_locIndep_one hG hP₀.1 hP₁.1
  obtain ⟨y, hy₁₂⟩ := exists_commonVertex_of_oddCycle_pair_of_locIndep_one hG hP₁.1 hP₂.1
  obtain ⟨z, hz₀₂⟩ := exists_commonVertex_of_oddCycle_pair_of_locIndep_one hG hP₀.1 hP₂.1
  exact not_locIndep_one_of_three_triangle_petals hC hC3 hP₀.1 hP₀3 hP₁.1 hP₁3 hP₂.1 hP₂3
    hP₀.2 hP₁.2 hP₂.2 hd₀₁ hd₀₂ hd₁₂
    (ne_empty_of_mem (Finset.mem_inter.mpr hx₀₁)) (ne_empty_of_mem (Finset.mem_inter.mpr hz₀₂))
    (ne_empty_of_mem (Finset.mem_inter.mpr hy₁₂)) hG

/-- **THE TRIANGLE ATTACHMENT SET** `TriPetalSet G C`: the vertices of `C` lying *alone* on a
**triangle** of `G` — the attachment points whose witness is short. -/
noncomputable def TriPetalSet (G : SimpleGraph V) (C : Finset V) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter fun v =>
    ∃ D : Finset V, IsOddCycle G D ∧ D.card = 3 ∧ D ∩ C = {v}

theorem mem_triPetalSet {C : Finset V} {v : V} :
    v ∈ TriPetalSet G C ↔
      v ∈ C ∧ ∃ D : Finset V, IsOddCycle G D ∧ D.card = 3 ∧ D ∩ C = {v} := by
  simp only [TriPetalSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨D, hD, hD3, hDinter⟩
    have hvD : v ∈ ({v} : Finset V) := Finset.mem_singleton_self v
    rw [← hDinter] at hvD
    exact ⟨(Finset.mem_inter.mp hvD).2, D, hD, hD3, hDinter⟩
  · rintro ⟨-, D, hD, hD3, hDinter⟩
    exact ⟨D, hD, hD3, hDinter⟩

theorem triPetalSet_subset {C : Finset V} : TriPetalSet G C ⊆ C :=
  fun v hv => (mem_triPetalSet.mp hv).1

/-- **IF EVERY ODD CYCLE OF `G` IS A TRIANGLE, THE ATTACHMENT SET IS THE TRIANGLE ATTACHMENT
SET.**  This is the bridge to Part 4 of the file header. -/
theorem petalSet_subset_triPetalSet_of_allTriangles {C : Finset V}
    (h : ∀ D : Finset V, IsOddCycle G D → D.card = 3) : PetalSet G C ⊆ TriPetalSet G C := by
  intro v hv
  obtain ⟨hvC, D, hD, hDinter⟩ := mem_petalSet.mp hv
  exact mem_triPetalSet.mpr ⟨hvC, D, hD, h D hD, hDinter⟩

/-- **AT MOST TWO VERTICES OF A TRIANGLE OF A `LocIndep 1` GRAPH LIE ALONE ON A TRIANGLE.**

This is the case of `JSP90.PetalSetLeTwoOfOne` in which the witness petals are triangles — the part of
that statement accounted for by the six-vertex obstruction of Part 3.  The remaining content of
`JSP90.PetalSetLeTwoOfOne` is the case in which some attachment point is witnessed by a petal of
length `≥ 5`. -/
theorem card_triPetalSet_le_two_of_locIndep_one (hG : LocIndep 1 G) {C : Finset V}
    (hC : IsOddCycle G C) (hC3 : C.card = 3) : (TriPetalSet G C).card ≤ 2 := by
  by_contra hcon
  have h3 : 3 ≤ (TriPetalSet G C).card := by omega
  have hne : (TriPetalSet G C) ≠ ∅ := by
    intro hc
    rw [hc] at h3
    simp at h3
  obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty hne
  by_cases he1 : TriPetalSet G C \ {a} = ∅
  · have hc1 : (TriPetalSet G C).card ≤ 1 := by
      have hsub : TriPetalSet G C ⊆ {a} := by
        intro v hv
        by_contra hne2
        have hmem : v ∈ TriPetalSet G C \ {a} := Finset.mem_sdiff.mpr ⟨hv, hne2⟩
        rw [he1] at hmem
        simp at hmem
      have hc := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hc
      exact hc
    omega
  · obtain ⟨b, hb⟩ := Finset.nonempty_of_ne_empty he1
    have hba : b ≠ a := fun h =>
      (Finset.mem_sdiff.mp hb).2 (by rw [← h]; exact Finset.mem_singleton_self b)
    have hab : a ≠ b := Ne.symm hba
    by_cases he2 : TriPetalSet G C \ {a, b} = ∅
    · have hc2 : (TriPetalSet G C).card ≤ 2 := by
        have hsub : TriPetalSet G C ⊆ {a, b} := by
          intro v hv
          by_contra hne2
          have hmem : v ∈ TriPetalSet G C \ {a, b} := Finset.mem_sdiff.mpr
            ⟨hv, hne2⟩
          rw [he2] at hmem
          simp at hmem
        have hc := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (fun hx => hab (Finset.mem_singleton.mp hx)),
          Finset.card_singleton] at hc
        exact hc
      omega
    · obtain ⟨d, hd⟩ := Finset.nonempty_of_ne_empty he2
      have hdb : d ≠ b := fun h =>
        (Finset.mem_sdiff.mp hd).2 (by
          rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inr h)
      have hbd : b ≠ d := Ne.symm hdb
      have hda : d ≠ a := fun h =>
        (Finset.mem_sdiff.mp hd).2 (by
          rw [Finset.mem_insert, Finset.mem_singleton]; exact Or.inl h)
      have haT : a ∈ TriPetalSet G C := ha
      have hbT : b ∈ TriPetalSet G C := (Finset.mem_sdiff.mp hb |>.1)
      have hdT : d ∈ TriPetalSet G C := (Finset.mem_sdiff.mp hd |>.1)
      obtain ⟨haC', P₀, hP₀, hP₀3, hC₀⟩ := (mem_triPetalSet.mp haT)
      obtain ⟨hbC', P₁, hP₁, hP₁3, hC₁⟩ := (mem_triPetalSet.mp hbT)
      obtain ⟨hdC', P₂, hP₂, hP₂3, hC₂⟩ := (mem_triPetalSet.mp hdT)
      have hd01 : (P₀ ∩ C ≠ P₁ ∩ C) := by
        intro h
        have heq : ({a} : Finset V) = {b} := hC₀.symm.trans (h.trans hC₁)
        have hmem : a ∈ ({a} : Finset V) := Finset.mem_singleton_self a
        rw [heq] at hmem
        have hab' : a = b := Finset.mem_singleton.mp hmem
        exact hab hab'
      have hd02 : (P₀ ∩ C ≠ P₂ ∩ C) := by
        intro h
        have heq : ({a} : Finset V) = {d} := hC₀.symm.trans (h.trans hC₂)
        have hmem : a ∈ ({a} : Finset V) := Finset.mem_singleton_self a
        rw [heq] at hmem
        have had : a = d := Finset.mem_singleton.mp hmem
        exact hda had.symm
      have hd12 : (P₁ ∩ C ≠ P₂ ∩ C) := by
        intro h
        have heq : ({b} : Finset V) = {d} := hC₁.symm.trans (h.trans hC₂)
        have hmem : b ∈ ({b} : Finset V) := Finset.mem_singleton_self b
        rw [heq] at hmem
        have hbd' : b = d := Finset.mem_singleton.mp hmem
        exact hbd hbd'
      exact not_three_triangle_petals_of_locIndep_one hG hC hC3 ⟨hP₀, Finset.card_eq_one.mpr ⟨a, hC₀⟩⟩
        hP₀3 ⟨hP₁, Finset.card_eq_one.mpr ⟨b, hC₁⟩⟩ hP₁3
        ⟨hP₂, Finset.card_eq_one.mpr ⟨d, hC₂⟩⟩ hP₂3 hd01 hd02 hd12
theorem erdos73On_one_of_allTriangles (h : ∀ D : Finset V, IsOddCycle G D → D.card = 3)
    (hG : LocIndep 1 G) (hC : IsOddCycle G C) (hC3 : C.card = 3) : CloseToBipartite 2 G :=
  closeToBipartite_two_of_triangle_petalSet_le_two hC hC3
    (hitsOddCycles_of_isOddCycle_of_locIndep_one hG hC)
    ((Finset.card_le_card (petalSet_subset_triPetalSet_of_allTriangles h)).trans
      (card_triPetalSet_le_two_of_locIndep_one hG hC hC3))

/-- **THE INSTANCE AS A STATEMENT ABOUT A CLASS**: if `G` has an odd cycle and all its odd cycles are
triangles, then `LocIndep 1 G` forces `CloseToBipartite 2 G`. -/
theorem erdos73On_one_of_allTriangles_of_exists
    (h : ∀ D : Finset V, IsOddCycle G D → D.card = 3) (hG : LocIndep 1 G)
    (hex : ∃ C : Finset V, IsOddCycle G C ∧ C.card = 3) : CloseToBipartite 2 G := by
  obtain ⟨C, hC, hC3⟩ := hex
  exact erdos73On_one_of_allTriangles h hG hC hC3

end
end SixVertex

/-! ## Part 4 — **THE WITNESS**: the octahedral graph `K_6` minus a perfect matching -/

section OctaSix

/-- **The adjacency relation of the octahedral graph**: two vertices are adjacent exactly when they
lie in different parts of the partition `{0, 3}`, `{1, 4}`, `{2, 5}`. -/
def octa6Edge : Finset (Fin 6 × Fin 6) :=
  (Finset.univ : Finset (Fin 6 × Fin 6)).filter fun p =>
    p.1 ≠ p.2 ∧ ¬ (p.1 = 3 ∧ p.2 = 0) ∧ ¬ (p.1 = 0 ∧ p.2 = 3) ∧ ¬ (p.1 = 4 ∧ p.2 = 1) ∧
      ¬ (p.1 = 1 ∧ p.2 = 4) ∧ ¬ (p.1 = 5 ∧ p.2 = 2) ∧ ¬ (p.1 = 2 ∧ p.2 = 5)

theorem octa6Edge_symm : ∀ v w : Fin 6, (v, w) ∈ octa6Edge ↔ (w, v) ∈ octa6Edge := by decide

theorem octa6Edge_irrefl : ∀ v : Fin 6, (v, v) ∉ octa6Edge := by decide

/-- **The octahedral graph `K_6` minus a perfect matching.** -/
def octa6 : SimpleGraph (Fin 6) where
  Adj v w := (v, w) ∈ octa6Edge
  symm := ⟨fun _ _ h => (octa6Edge_symm _ _).mp h⟩
  loopless := ⟨fun _ h => octa6Edge_irrefl _ h⟩

@[simp] theorem octa6_adj {v w : Fin 6} : octa6.Adj v w ↔ (v, w) ∈ octa6Edge := Iff.rfl

local instance : DecidableRel octa6.Adj :=
  fun v w => inferInstanceAs (Decidable ((v, w) ∈ octa6Edge))

/-- **`octa6` IS THE COMPLETE TRIPARTITE GRAPH WITH PARTS `{0,3}`, `{1,4}`, `{2,5}`.** -/
theorem octa6_adj_iff {v w : Fin 6} :
    octa6.Adj v w ↔
      ((v = 0 ∧ w ≠ 3) ∨ (v = 1 ∧ w ≠ 4) ∨ (v = 2 ∧ w ≠ 5) ∨ (v = 3 ∧ w ≠ 0) ∨
        (v = 4 ∧ w ≠ 1) ∨ (v = 5 ∧ w ≠ 2)) ∧ v ≠ w := by
  revert v w
  decide

theorem octa6_parts_card : ({0, 3} : Finset (Fin 6)).card = 2 ∧ ({1, 4} : Finset (Fin 6)).card = 2 ∧
    ({2, 5} : Finset (Fin 6)).card = 2 := ⟨by decide, by decide, by decide⟩

theorem octa6_parts_disjoint :
    Disjoint ({0, 3} : Finset (Fin 6)) ({1, 4} : Finset (Fin 6)) ∧
      Disjoint ({0, 3} : Finset (Fin 6)) ({2, 5} : Finset (Fin 6)) ∧
      Disjoint ({1, 4} : Finset (Fin 6)) ({2, 5} : Finset (Fin 6)) :=
  ⟨by decide, by decide, by decide⟩

theorem octa6_adj_part₁₂ : ∀ x ∈ ({0, 3} : Finset (Fin 6)), ∀ y ∈ ({1, 4} : Finset (Fin 6)),
    octa6.Adj x y := by decide

theorem octa6_adj_part₁₃ : ∀ x ∈ ({0, 3} : Finset (Fin 6)), ∀ y ∈ ({2, 5} : Finset (Fin 6)),
    octa6.Adj x y := by decide

theorem octa6_adj_part₂₃ : ∀ x ∈ ({1, 4} : Finset (Fin 6)), ∀ y ∈ ({2, 5} : Finset (Fin 6)),
    octa6.Adj x y := by decide

/-- **`MaxDef octa6 ≥ 2` BY THE MULTIPARTITE OBSTRUCTION**: `octa6` contains `K_6` minus a perfect
matching on all six vertices. -/
theorem maxDef_ge_two_octa6 : 2 ≤ MaxDef octa6 :=
  maxDef_ge_two_of_threeParts octa6_parts_card.1 octa6_parts_card.2.1 octa6_parts_card.2.2
    octa6_parts_disjoint.1 octa6_parts_disjoint.2.1 octa6_parts_disjoint.2.2 octa6_adj_part₁₂
    octa6_adj_part₁₃ octa6_adj_part₂₃

/-- **`LocIndep 2 octa6`**: on six vertices the deficiency `2` is the only content of the hypothesis.
This is a kernel decision over the `2 ^ 6` vertex sets. -/
theorem locIndep_two_octa6 : LocIndep 2 octa6 := by
  unfold LocIndep
  decide

/-- **THE DEFICIENCY OF THE OCTAHEDRAL GRAPH IS EXACTLY `2`.**  So `octa6` satisfies `LocIndep 2`
and fails `LocIndep 1`: it is a graph on which the bound of `JSP90.maxDef_ge_two_of_threeParts` is
attained, and all six vertices of the six-vertex obstruction are vertices of `V`. -/
theorem maxDef_octa6 : MaxDef octa6 = 2 := by
  have hle : MaxDef octa6 ≤ 2 :=
    (locIndep_iff_maxDef_le.mp (show LocIndep 2 octa6 from locIndep_two_octa6))
  exact le_antisymm hle maxDef_ge_two_octa6

theorem not_locIndep_one_octa6 : ¬ LocIndep 1 octa6 := by
  intro h
  have hle := locIndep_iff_maxDef_le.mp h
  rw [maxDef_octa6] at hle
  omega

/-- **`octa6` IS `2`-CLOSE TO BIPARTITE**: deleting the non-adjacent pair `{0, 3}` leaves the
complete bipartite graph `K_{2,2}` on the parts `{1, 4}` and `{2, 5}`. -/
theorem closeToBipartite_two_octa6 : CloseToBipartite 2 octa6 := by
  refine ⟨{0, 3}, by decide, ?_⟩
  rw [isBipartite_iff_color2]
  refine ⟨fun v => if v = 1 ∨ v = 4 then (0 : Fin 2) else 1, ?_⟩
  intro u v hadj
  have hadj' := deleteFinset_adj.mp hadj
  have huv : u ≠ v := by
    intro h
    have hvv : octa6.Adj v v := h ▸ hadj'.2.2
    exact octa6.irrefl hvv
  fin_cases u <;> fin_cases v <;> simp_all [octa6Edge]

/-- **THE EXACT VALUE OF `CloseToBipartite m octa6`: IT HOLDS EXACTLY WHEN `m ≥ 2`.**  Together with
`not_locIndep_one_octa6` this says that on `octa6` two vertices must be deleted and that two
suffice: the threshold `MaxDef ≥ 2` of `JSP90.maxDef_ge_two_of_threeParts` is sharp. -/
theorem closeToBipartite_iff_octa6 (m : ℕ) : CloseToBipartite m octa6 ↔ 2 ≤ m := by
  constructor
  · intro h
    have h1 : MaxDef octa6 ≤ m := maxDef_le_closeToBipartite h
    rw [maxDef_octa6] at h1
    omega
  · intro h
    obtain ⟨X, hX, hb⟩ := closeToBipartite_two_octa6
    exact ⟨X, by omega, hb⟩

/-! ### The three attachment points of `{0, 1, 2}` in `octa6` -/

/-- A cyclic ordering of three vertices of `Fin 6`. -/
def cyc3octa (a b c : Fin 6) : Fin 3 → Fin 6 := fun j =>
  match j.val with
  | 0 => a | 1 => b | _ => c

theorem cyc3octa_inj (a b c : Fin 6) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Function.Injective (cyc3octa a b c) := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [cyc3octa]

theorem cyc3octa_adj (a b c : Fin 6) (hab : octa6.Adj a b) (hbc : octa6.Adj b c)
    (hca : octa6.Adj c a) :
    ∀ j : Fin 3, octa6.Adj (cyc3octa a b c j) (cyc3octa a b c (cycSucc j)) := by
  intro j
  fin_cases j <;> first
    | simpa [cyc3octa] using hab
    | simpa [cyc3octa] using hbc
    | simpa [cyc3octa] using hca

/-- **A TRIANGLE OF `octa6` IS AN ODD CYCLE.** -/
theorem isOddCycle_octa6_tri (a b c : Fin 6) (hab : octa6.Adj a b) (hbc : octa6.Adj b c)
    (hca : octa6.Adj c a) (hab' : a ≠ b) (hbc' : b ≠ c) (hca' : c ≠ a) :
    IsOddCycle octa6 {a, b, c} := by
  have h := isOddCycle_triple octa6 (a := a) (b := b) (c := c) (t := cyc3octa a b c)
    (cyc3octa_inj a b c hab' hbc' hca') (cyc3octa_adj a b c hab hbc hca) rfl rfl rfl
  refine IsOddCycle.of_finset_ext h (fun x => ?_)
  simp

theorem isOddCycle_octa6_tri_045 : IsOddCycle octa6 {0, 4, 5} :=
  isOddCycle_octa6_tri 0 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem isOddCycle_octa6_tri_315 : IsOddCycle octa6 {3, 1, 5} :=
  isOddCycle_octa6_tri 3 1 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem isOddCycle_octa6_tri_342 : IsOddCycle octa6 {3, 4, 2} :=
  isOddCycle_octa6_tri 3 4 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem isOddCycle_octa6_tri_012 : IsOddCycle octa6 {0, 1, 2} :=
  isOddCycle_octa6_tri 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **THE ATTACHMENT SET OF THE TRIANGLE `{0, 1, 2}` OF `octa6` HAS THREE ELEMENTS.**

This is the witness that the configuration of `JSP90.maxDef_ge_two_of_threePetalTriangle` is a real
one: it is the first graph in this development in which the attachment set of a triangle is not a
proper subset of it.  The witnesses are the three petals `{0,4,5}`, `{3,1,5}`, `{3,4,2}`, each meeting
`{0,1,2}` in exactly one vertex. -/
theorem mem_petalSet_octa6_0 : (0 : Fin 6) ∈ PetalSet octa6 ({0, 1, 2} : Finset (Fin 6)) := by
  refine mem_petalSet.mpr ⟨?_, {0, 4, 5}, isOddCycle_octa6_tri_045, ?_⟩
  · simp
  · ext y
    fin_cases y <;> simp [Finset.mem_inter]

theorem mem_petalSet_octa6_1 : (1 : Fin 6) ∈ PetalSet octa6 ({0, 1, 2} : Finset (Fin 6)) := by
  refine mem_petalSet.mpr ⟨?_, {3, 1, 5}, isOddCycle_octa6_tri_315, ?_⟩
  · simp
  · ext y
    fin_cases y <;> simp [Finset.mem_inter]

theorem mem_petalSet_octa6_2 : (2 : Fin 6) ∈ PetalSet octa6 ({0, 1, 2} : Finset (Fin 6)) := by
  refine mem_petalSet.mpr ⟨?_, {3, 4, 2}, isOddCycle_octa6_tri_342, ?_⟩
  · simp
  · ext y
    fin_cases y <;> simp [Finset.mem_inter]

theorem petalSet_octa6_tri :
    PetalSet octa6 ({0, 1, 2} : Finset (Fin 6)) = ({0, 1, 2} : Finset (Fin 6)) := by
  apply Finset.ext
  intro v
  constructor
  · intro hv
    exact (mem_petalSet.mp hv).1
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv | hv
    · rw [hv]; exact mem_petalSet_octa6_0
    · rw [hv]; exact mem_petalSet_octa6_1
    · rw [hv]; exact mem_petalSet_octa6_2

/-- ... and its cardinality is `3`, so the hypothesis of `JSP90.PetalSetLeTwoOfOne` — "under
`LocIndep 1` a triangle has at most two attachment points" — is *not* available on `octa6`, which is
consistent with `not_locIndep_one_octa6` and with the six-vertex obstruction of Part 3. -/
theorem card_petalSet_octa6_tri : (PetalSet octa6 ({0, 1, 2} : Finset (Fin 6))).card = 3 := by
  rw [petalSet_octa6_tri]
  decide

end OctaSix

end JSP90
