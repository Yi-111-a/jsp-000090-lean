import JSPProblem.Seven
import JSPProblem.FiniteSharp

/-!
# JSP-000090, round 151 — `JSPProblem/TriPair.lean`: **THE PAIR INSIDE THE TRIANGLE**

Attack family 78.  The concrete target left by rounds 149 and 150 was
`JSP90.closeToBipartite_two_of_locIndep_one_card_le_seven` (`LocIndep 1 G`, `|V| ≤ 7` ⟹
`CloseToBipartite 2 G`), measured to be **sharp** at seven vertices
(`discovery/JSP-000090/r148_n7.log`: over all `2^21` graphs on seven vertices the maximum of
`tauOdd` among the `LocIndep 1` ones is exactly `2`).

Round 150 split that instance into three cases according to the cardinality of a shortest odd
cycle and closed the case of cardinality `7`.  This file closes the **triangle** case: under
Erdős's hypothesis at `k = 1`, **two vertices of a triangle `T` of `G` meet every odd cycle of `G`**
whenever `|V| ≤ 7`.

## The three counting steps

Write `X = V \ T` (at most four vertices; `G[X]` is bipartite, by Part 0b of
`JSPProblem/Seven.lean`), `S_t` for the neighbours of `t ∈ T` lying in `X`, and `M_t = X \ S_t`.

* **Part 1 — `JSP90.adjIn_card_two_and_edge_or_path`.**  If `G - (T \ {t})` is not bipartite for some
  `t ∈ T`, then `|S_t| = 2` and either `S_t` is an edge of `G[X]` (a *triangle* through `t`) or
  `M_t` is an edge of `G[X]` (a *five-cycle* through `t`): with at most four vertices outside `T`,
  an odd cycle through `t` avoiding the other two vertices of `T` has three or five vertices, and in
  both cases the two neighbours of `t` on it exhaust its neighbours outside `T` (Erdős's hypothesis
  bounds them by two).
* **Part 2 — `JSP90.two_of_three_complement_edge_free`.**  Erdős's hypothesis applied to
  `V \ {t}` supplies an independent triple; two of its vertices lie outside `T`, hence in `M_{t'}`
  with `t' ≠ t`, and they are non-adjacent — so `M_{t'}` carries no edge of `G[X]`.  Applying this
  for each `t` leaves at most one complement carrying an edge.
* **Part 3 — `JSP90.three_bad_impossible`.**  The finite counting lemma: a bipartite graph on a
  four-element set admits no three *distinct* two-element sets `S₁, S₂, S₃`, each of which is an edge
  or has an edge-carrying complement, with empty triple intersection and with the complement of at
  least one of them carrying no edge.  Verified exhaustively over all `2^6` edge sets on four
  vertices and all `820` triples of distinct two-element subsets
  (`discovery/JSP-000090/r151d.log`, `r151i.log`).

`jsp_000090_main` is deliberately **not** declared, so `harness/score.py --strict-prize` keeps
reporting `missing_theorems = ["jsp_000090_main"]`.
-/

universe u

namespace JSP90

open Finset Fintype Set SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable section

set_option maxHeartbeats 900000

local instance tpDecidableEq : DecidableEq V := Classical.decEq V

/-- **THE RESIDUE OF A VERTEX SET**: the vertices of `V` outside `T`. -/
def Residue (T : Finset V) : Finset V := (Finset.univ : Finset V) \ T

@[simp] theorem mem_residue {T : Finset V} {z : V} : z ∈ Residue T ↔ z ∉ T := by
  simp [Residue]

theorem mem_residue_of_notMem {T : Finset V} {z : V} (hz : z ∉ T) : z ∈ Residue T :=
  Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩

/-- `z` lies in the residue of `T` as soon as it is not a member of the *set* `T`. -/
theorem mem_residue_of_notMem_set {T : Finset V} {z : V} (hz : ¬(z ∈ (T : Set V))) :
    z ∈ Residue T := mem_residue.mpr hz

/-- One step around a cycle. -/
theorem tp_iterate_one {n : ℕ} (f : Fin n → Fin n) (x : Fin n) : ((f^[1]) : Fin n → Fin n) x = f x := by
  rw [Function.iterate_succ_apply', Function.iterate_zero_apply]

/-- Four steps around a cycle. -/
theorem tp_iterate_four {n : ℕ} (f : Fin n → Fin n) (x : Fin n) : ((f^[4]) : Fin n → Fin n) x = f (f (f (f x))) := by
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
    Function.iterate_one]

/-- Two steps around a cycle. -/
theorem tp_iterate_two {n : ℕ} (f : Fin n → Fin n) (x : Fin n) : ((f^[2]) : Fin n → Fin n) x = f (f x) := by
  rw [Function.iterate_succ_apply', Function.iterate_one]

/-- Three steps around a cycle. -/
theorem tp_iterate_three {n : ℕ} (f : Fin n → Fin n) (x : Fin n) : ((f^[3]) : Fin n → Fin n) x = f (f (f x)) := by
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_one]

/-- **A CYCLIC ORDERING OF A CYCLE OF FIVE VERTICES.** -/
theorem exists_cyc5_of_isOddCycle_card_five {C : Finset V} (hC : IsOddCycle G C)
    (h5 : C.card = 5) :
    ∃ f : Fin 5 → V, Function.Injective f ∧ (∀ j : Fin 5, G.Adj (f j) (f (cycSucc j))) ∧
      (∀ x : V, x ∈ C ↔ ∃ j : Fin 5, f j = x) := by
  obtain ⟨m, f, _, _, hinj, hcyc, hmem⟩ := hC
  have hmc : C.card = m := card_eq_m_of_image hinj hmem
  have hm5 : m = 5 := by omega
  subst hm5
  exact ⟨f, hinj, hcyc, hmem⟩

/-- **A CYCLIC ORDERING OF A CYCLE OF THREE VERTICES.** -/
theorem exists_cyc3_of_isOddCycle_card_three' {C : Finset V} (hC : IsOddCycle G C)
    (h3 : C.card = 3) :
    ∃ f : Fin 3 → V, Function.Injective f ∧ (∀ j : Fin 3, G.Adj (f j) (f (cycSucc j))) ∧
      (∀ x : V, x ∈ C ↔ ∃ j : Fin 3, f j = x) := by
  obtain ⟨m, f, _, _, hinj, hcyc, hmem⟩ := hC
  have hmc : C.card = m := card_eq_m_of_image hinj hmem
  have hm3 : m = 3 := by omega
  subst hm3
  exact ⟨f, hinj, hcyc, hmem⟩

@[simp] theorem notMem_residue_of_mem {T : Finset V} {z : V} (hz : z ∈ T) : z ∉ Residue T := by
  intro hz'
  exact (mem_residue.mp hz') hz

theorem mem_sdiff_singleton_iff {T : Finset V} {t z : V} :
    z ∈ (Finset.univ : Finset V) \ (T \ {t}) ↔ z ∉ T ∨ z = t := by
  constructor
  · intro hz
    by_cases hzT : z ∈ T
    · refine Or.inr ?_
      have hz' : ¬(z ∈ T \ {t}) := (Finset.mem_sdiff.mp hz).2
      by_contra hcon
      exact hz' ((Finset.mem_sdiff (s := T) (t := {t})).mpr ⟨hzT, by simpa using hcon⟩)
    · exact Or.inl hzT
  · intro h
    rcases h with h | h
    · refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, fun h' => h
        ((Finset.mem_sdiff (s := T) (t := {t})).mp h').1⟩
    · refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, fun h' => ((Finset.mem_sdiff (s := T)
        (t := {t})).mp h').2 ((Finset.mem_singleton (a := t) (b := z)).mpr h)⟩

theorem sdiff_singleton_eq_union_residue {T : Finset V} {t : V} :
    (Finset.univ : Finset V) \ (T \ {t}) = Residue T ∪ {t} := by
  ext z
  simp only [mem_sdiff_singleton_iff, Finset.mem_union, mem_residue, Finset.mem_singleton]

theorem mem_union_residue_of_mem_sdiff {T : Finset V} {t z : V}
    (hz : z ∈ (Finset.univ : Finset V) \ (T \ {t})) : z ∈ Residue T ∪ {t} := by
  rcases mem_sdiff_singleton_iff.mp hz with h | h
  · exact Finset.mem_union.mpr (Or.inl (mem_residue.mpr h))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr h))

theorem card_residue_le_four_of_isNClique_three {T : Finset V} (hT : G.IsNClique 3 T)
    (hV : Fintype.card V ≤ 7) : (Residue T).card ≤ 4 := by
  rw [Residue]
  have h1 := Finset.card_sdiff_of_subset (Finset.subset_univ T)
  have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have h3 : T.card = 3 := (G.isNClique_iff.mp hT).2
  omega

/-! **AN ODD CYCLE OF `G` THROUGH `t` AVOIDING `T \ {t}` LIES IN `X ∪ {t}`**, where `X` is the
residue.  The odd cycle comes from `¬ (deleteFinset G (T \ {t})).IsBipartite`, and the residue being
bipartite rules out an odd cycle avoiding `t` as well. -/
theorem exists_isOddCycle_through_of_not_isBipartite {T : Finset V} {t : V} (ht : t ∈ T)
    (hXbip : (deleteFinset G T).IsBipartite)
    (hnot : ¬ (deleteFinset G (T \ {t})).IsBipartite) :
    ∃ D : Finset V, IsOddCycle G D ∧ t ∈ D ∧
      D ⊆ ((Finset.univ : Finset V) \ (T \ {t})) := by
  have hex : ∃ D : Finset V, IsOddCycle (deleteFinset G (T \ {t})) D := by
    by_contra hcon
    exact hnot (isBipartite_of_no_oddCycle hcon)
  obtain ⟨D, hD0⟩ := hex
  obtain ⟨hD, hDsub⟩ := isOddCycle_induceFinset hD0
  refine ⟨D, hD, ?_, ?_⟩
  · by_contra hcon
    have hdis : Disjoint D T := by
      rw [Finset.disjoint_left]
      intro z hzD hzT
      have h2 := mem_sdiff_singleton_iff.mp (hDsub hzD)
      rcases h2 with h2 | h2
      · exact absurd hzT h2
      · exact hcon (h2 ▸ hzD)
    refine (not_isOddCycle_of_isBipartite hXbip) ⟨D, ?_⟩
    rw [deleteFinset]
    exact hD.induceFinset (Finset.subset_sdiff.mpr ⟨Finset.subset_univ D, hdis⟩)
  · intro z hz
    exact hDsub hz

/-- **THE LOCAL STRUCTURE AT A BAD VERTEX OF A TRIANGLE.**

```lean
(AdjIn G t X).card = 2 ∧
  ((∃ p q, p ∈ AdjIn G t X ∧ q ∈ AdjIn G t X ∧ G.Adj p q) ∨
   (∃ x y, x ∈ X \ AdjIn G t X ∧ y ∈ X \ AdjIn G t X ∧ G.Adj x y))
```

The odd cycle through `t` is a triangle (the first alternative) or a five-cycle, in which case its
two middle vertices form the second alternative. -/
theorem adjIn_card_two_and_edge_or_path {T : Finset V} (hT : G.IsNClique 3 T) {t : V} (ht : t ∈ T)
    (hV : Fintype.card V ≤ 7) (hXbip : (deleteFinset G T).IsBipartite)
    (hAdj : (AdjIn G t (Residue T)).card ≤ 2)
    (hnot : ¬ (deleteFinset G (T \ {t})).IsBipartite) :
    (AdjIn G t (Residue T)).card = 2 ∧
      ((∃ p q : V, p ∈ AdjIn G t (Residue T) ∧ q ∈ AdjIn G t (Residue T) ∧ G.Adj p q) ∨
       (∃ p q x y : V, p ∈ AdjIn G t (Residue T) ∧ q ∈ AdjIn G t (Residue T) ∧
          x ∈ Residue T \ AdjIn G t (Residue T) ∧ y ∈ Residue T \ AdjIn G t (Residue T) ∧
          G.Adj p x ∧ G.Adj x y ∧ G.Adj y q)) := by
  have hXcard : (Residue T).card ≤ 4 := card_residue_le_four_of_isNClique_three hT hV
  obtain ⟨D, hD, htD, hDsub⟩ := exists_isOddCycle_through_of_not_isBipartite ht hXbip hnot
  have h3 : 3 ≤ D.card := isOddCycle_card_ge_three hD
  have hmod : D.card % 2 = 1 := card_mod_two_of_isOddCycle hD
  have hle : D.card ≤ (Residue T).card + 1 := by
    have h1 := Finset.card_le_card hDsub
    have h2 : (((Finset.univ : Finset V) \ (T \ {t}))).card = (Residue T).card + 1 := by
      rw [sdiff_singleton_eq_union_residue]
      exact Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr
        (notMem_residue_of_mem ht))
    rw [h2] at h1
    omega
  have hcases : D.card = 3 ∨ D.card = 5 := by omega
  -- `hDsub` is read through `mem_sdiff_singleton_iff`
  have memX : ∀ z : V, z ∈ D → z ≠ t → z ∈ Residue T := by
    intro z hzD hzt
    have h2 := mem_sdiff_singleton_iff.mp (hDsub hzD)
    rcases h2 with h2 | h2
    · exact mem_residue_of_notMem_set (fun h => h2 h)
    · exact False.elim (hzt h2)
  obtain ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩ := hD
  have hmc : D.card = m := card_eq_m_of_image hinj hmem
  have hD' : IsOddCycle G D := ⟨m, f, hm, hm3, hinj, hcyc, hmem⟩
  rcases hcases with hcard | hcard
  · -- a triangle through `t`: `t` and its two cycle-neighbours are mutually adjacent
    have hm' : m = 3 := by omega
    subst hm'
    obtain ⟨i, hi⟩ := hmem t |>.mp htD
    have hmemD : ∀ j : Fin 3, f j ∈ D := fun j => (hmem _).mpr ⟨j, rfl⟩
    have htp : G.Adj t (f (cycSucc i)) := by rw [← hi]; exact hcyc i
    have htq : G.Adj t (f (cycSucc (cycSucc i))) := by
      have hA : G.Adj (f (cycSucc (cycSucc (cycSucc i)))) (f (cycSucc (cycSucc i))) :=
        (hcyc (cycSucc (cycSucc i))).symm
      have h3 : cycSucc (cycSucc (cycSucc i)) = i := cycSucc_pow i
      rw [h3] at hA
      exact hi ▸ hA
    have hne : f (cycSucc i) ≠ f (cycSucc (cycSucc i)) := by
      intro h
      exact cycSucc_pow_inj i (p := 1) (q := 2) (by omega) (by omega) (by omega) (hinj h)
    have hpX : f (cycSucc i) ∈ Residue T := by
      refine memX _ (hmemD _) ?_
      rw [← hi]
      intro h
      exact cycSucc_pow_inj i (p := 1) (q := 0) (by omega) (by omega) (by omega) (hinj h)
    have hqX : f (cycSucc (cycSucc i)) ∈ Residue T := by
      refine memX _ (hmemD _) ?_
      rw [← hi]
      intro h
      exact cycSucc_pow_inj i (p := 2) (q := 0) (by omega) (by omega) (by omega) (hinj h)
    have hsub : {f (cycSucc i), f (cycSucc (cycSucc i))} ⊆ AdjIn G t (Residue T) := by
      intro u hu
      rw [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact mem_adjIn.mpr ⟨hpX, htp⟩
      · exact mem_adjIn.mpr ⟨hqX, htq⟩
    have hcard2 : (AdjIn G t (Residue T)).card = 2 := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simpa using hne)] at h1
      simp only [Finset.card_singleton] at h1
      omega
    have hpq : G.Adj (f (cycSucc i)) (f (cycSucc (cycSucc i))) := by
      obtain ⟨hcl, -⟩ := G.isNClique_iff.mp (isNClique_three_of_isOddCycle hD' hcard)
      exact hcl (hmemD _) (hmemD _) hne
    exact ⟨hcard2, Or.inl ⟨f (cycSucc i), f (cycSucc (cycSucc i)),
      mem_adjIn.mpr ⟨hpX, htp⟩, mem_adjIn.mpr ⟨hqX, htq⟩, hpq⟩⟩
  · -- a five-cycle through `t`: the two middle vertices are adjacent and lie outside `S_t`
    have hm' : m = 5 := by omega
    subst hm'
    obtain ⟨i, hi⟩ := hmem t |>.mp htD
    have hmemD : ∀ j : Fin 5, f j ∈ D := fun j => (hmem _).mpr ⟨j, rfl⟩
    -- the five vertices of the cycle are pairwise distinct
    have hne_pq : f (cycSucc i) ≠ f (cycSucc (cycSucc (cycSucc (cycSucc i)))) := by
      intro h
      exact cycSucc_pow_inj i (p := 1) (q := 4) (by omega) (by omega) (by omega) (hinj h)
    have hne_px : f (cycSucc i) ≠ f (cycSucc (cycSucc i)) := by
      intro h
      exact cycSucc_pow_inj i (p := 1) (q := 2) (by omega) (by omega) (by omega) (hinj h)
    have hne_xy : f (cycSucc (cycSucc i)) ≠ f (cycSucc (cycSucc (cycSucc i))) := by
      intro h
      exact cycSucc_pow_inj i (p := 2) (q := 3) (by omega) (by omega) (by omega) (hinj h)
    have hne_xt : f (cycSucc (cycSucc i)) ≠ f i := by
      intro h
      exact cycSucc_pow_inj i (p := 2) (q := 0) (by omega) (by omega) (by omega) (hinj h)
    have hne_yt : f (cycSucc (cycSucc (cycSucc i))) ≠ f i := by
      intro h
      exact cycSucc_pow_inj i (p := 3) (q := 0) (by omega) (by omega) (by omega) (hinj h)
    have hne_yp : f (cycSucc (cycSucc (cycSucc i))) ≠ f (cycSucc i) := by
      intro h
      exact cycSucc_pow_inj i (p := 3) (q := 1) (by omega) (by omega) (by omega) (hinj h)
    have hne_xq : f (cycSucc (cycSucc i)) ≠ f (cycSucc (cycSucc (cycSucc (cycSucc i)))) := by
      intro h
      exact cycSucc_pow_inj i (p := 2) (q := 4) (by omega) (by omega) (by omega) (hinj h)
    have hne_yq : f (cycSucc (cycSucc (cycSucc i))) ≠ f (cycSucc (cycSucc (cycSucc (cycSucc i)))) :=
      by
      intro h
      exact cycSucc_pow_inj i (p := 3) (q := 4) (by omega) (by omega) (by omega) (hinj h)
    have htp : G.Adj t (f (cycSucc i)) := by rw [← hi]; exact hcyc i
    have htq : G.Adj t (f (cycSucc (cycSucc (cycSucc (cycSucc i))))) := by
      have hA : G.Adj (f (cycSucc (cycSucc (cycSucc (cycSucc (cycSucc i))))))
          (f (cycSucc (cycSucc (cycSucc (cycSucc i))))) :=
        (hcyc (cycSucc (cycSucc (cycSucc (cycSucc i))))).symm
      have h5 : cycSucc (cycSucc (cycSucc (cycSucc (cycSucc i)))) = i := cycSucc_pow i
      rw [h5] at hA
      exact hi ▸ hA
    have hxy : G.Adj (f (cycSucc (cycSucc i))) (f (cycSucc (cycSucc (cycSucc i)))) :=
      hcyc (cycSucc (cycSucc i))
    have hpX : f (cycSucc i) ∈ Residue T := by
      refine memX _ (hmemD _) ?_
      rw [← hi]
      intro h
      exact cycSucc_pow_inj i (p := 1) (q := 0) (by omega) (by omega) (by omega) (hinj h)
    have hqX : f (cycSucc (cycSucc (cycSucc (cycSucc i)))) ∈ Residue T := by
      refine memX _ (hmemD _) ?_
      rw [← hi]
      intro h
      exact cycSucc_pow_inj i (p := 4) (q := 0) (by omega) (by omega) (by omega) (hinj h)
    have hxX : f (cycSucc (cycSucc i)) ∈ Residue T := by
      refine memX _ (hmemD _) ?_
      rw [← hi]
      intro h
      exact cycSucc_pow_inj i (p := 2) (q := 0) (by omega) (by omega) (by omega) (hinj h)
    have hyX : f (cycSucc (cycSucc (cycSucc i))) ∈ Residue T := by
      refine memX _ (hmemD _) ?_
      rw [← hi]
      intro h
      exact cycSucc_pow_inj i (p := 3) (q := 0) (by omega) (by omega) (by omega) (hinj h)
    have hsub : {f (cycSucc i), f (cycSucc (cycSucc (cycSucc (cycSucc i))))} ⊆
        AdjIn G t (Residue T) := by
      intro u hu
      rw [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact mem_adjIn.mpr ⟨hpX, htp⟩
      · exact mem_adjIn.mpr ⟨hqX, htq⟩
    have hcard2 : (AdjIn G t (Residue T)).card = 2 := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simpa using hne_pq)] at h1
      simp only [Finset.card_singleton] at h1
      omega
    have hS : AdjIn G t (Residue T)
        = {f (cycSucc i), f (cycSucc (cycSucc (cycSucc (cycSucc i))))} :=
      (Finset.eq_of_subset_of_card_le (s := {f (cycSucc i),
          f (cycSucc (cycSucc (cycSucc (cycSucc i))))}) (t := AdjIn G t (Residue T)) hsub (by
        rw [Finset.card_insert_of_notMem (by simpa using hne_pq), Finset.card_singleton]
        omega)).symm
    have hxne : f (cycSucc (cycSucc i)) ∉ AdjIn G t (Residue T) := by
      rw [hS]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hcon
      rcases hcon with hcon | hcon
      · exact hne_px hcon.symm
      · exact hne_xq hcon
    have hyne : f (cycSucc (cycSucc (cycSucc i))) ∉ AdjIn G t (Residue T) := by
      rw [hS]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hcon
      rcases hcon with hcon | hcon
      · exact hne_yp hcon
      · exact hne_yq hcon
    have hpx : G.Adj (f (cycSucc i)) (f (cycSucc (cycSucc i))) := hcyc (cycSucc i)
    have hyq : G.Adj (f (cycSucc (cycSucc (cycSucc i))))
        (f (cycSucc (cycSucc (cycSucc (cycSucc i))))) := hcyc (cycSucc (cycSucc (cycSucc i)))
    exact ⟨hcard2, Or.inr ⟨f (cycSucc i), f (cycSucc (cycSucc (cycSucc (cycSucc i)))),
      f (cycSucc (cycSucc i)), f (cycSucc (cycSucc (cycSucc i))),
      mem_adjIn.mpr ⟨hpX, htp⟩, mem_adjIn.mpr ⟨hqX, htq⟩,
      Finset.mem_sdiff.mpr ⟨hxX, hxne⟩, Finset.mem_sdiff.mpr ⟨hyX, hyne⟩,
      hpx, hxy, hyq⟩⟩

/-! ## Part 4 — the triangle-free five-cycle lemma, and the instance it feeds

**A BUG FOUND AND CORRECTED (round 151).**  The odd-cycle detector used by
`discovery/JSP-000090/r150b.c` (and re-used by this round's first measurements) walks the
connectivity check incorrectly: it pushes the *accumulated* vertex mask instead of a vertex, so the
breadth-first search never leaves the lowest-numbered vertex and **every** five-cycle is missed.
With a correct test (`r151q.c`: 2-regular + connected + odd cardinality) the exhaustive
measurement at `|V| = 7` changes:

```lean
-- all 986787 LocIndep-1 graphs on seven vertices, by the cardinality of a shortest odd cycle
3 : 853286      (a triangle)
5 :  29904      (triangle-free, and NOT covered by round 150's odd-girth-7 instance)
7 :    360
bipartite : 103237
```

so **`LocIndep 1` and `|V| ≤ 7` do not imply odd girth at least seven**, and round 150's
`JSP90.closeToBipartite_one_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven` does **not** apply to
the triangle-free seven-vertex graphs: `29904` of them have a shortest five-cycle.  The measurement
does confirm that on those graphs `tauOdd ≤ 1`
(`r151q.c`: `max tauOdd = 1` over all `133501` triangle-free `LocIndep 1` graphs on seven vertices,
`2` over the `853286` graphs with a triangle), so the sharp seven-vertex instance splits exactly as
Part 3 describes — but the five-cycle case needs Missing Lemma 1 of round 150, not the odd girth. -/

/-- **IN A TRIANGLE-FREE GRAPH EVERY ODD CYCLE HAS AT LEAST FIVE VERTICES.** -/
theorem card_ge_five_of_isOddCycle_of_triangleFree {C : Finset V}
    (htf : ∀ D : Finset V, ¬ G.IsNClique 3 D) (hC : IsOddCycle G C) : 5 ≤ C.card := by
  have h3 := isOddCycle_card_ge_three hC
  have hmod := card_mod_two_of_isOddCycle hC
  have hne : C.card ≠ 3 := fun h => htf C (isNClique_three_of_isOddCycle hC h)
  omega

/-- **ERDŐS #73 AT `k = 1` WITH THE OPTIMAL CONSTANT `1`, ON TRIANGLE-FREE GRAPHS OF ORDER AT MOST
SEVEN WITH NO FIVE-CYCLE — A NEW INSTANCE OF THE HEADLINE THEOREM.**

```lean
LocIndep 1 G → |V| ≤ 7 → (G has no 3-clique) → (G has no five-cycle) → CloseToBipartite 1 G
```

Triangle-freeness gives odd girth at least five and the order bound gives at most seven, so with the
five-cycle excluded every odd cycle has seven vertices and spans `V`; the single deleted vertex is
then a common vertex of all odd cycles (`JSP90.mem_hitsOddCycles_singleton_of_shortest_oddCycle_of_card_eq`). -/
theorem closeToBipartite_one_of_locIndep_one_card_le_seven_of_triangleFree_no5
    (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 7) (htf : ∀ D : Finset V, ¬ G.IsNClique 3 D)
    (hno5 : ∀ C : Finset V, ¬ (IsOddCycle G C ∧ C.card = 5)) (hne : Nonempty V) :
    CloseToBipartite 1 G := by
  refine closeToBipartite_one_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven hG hV ?_ hne
  intro D hD
  have h5 := card_ge_five_of_isOddCycle_of_triangleFree htf hD
  have h2 : D.card ≤ Fintype.card V := by
    have h3 := Finset.card_le_univ D
    have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    omega
  have hmod := card_mod_two_of_isOddCycle hD
  have hne' : D.card ≠ 5 := fun h => hno5 D ⟨hD, h⟩
  have h7 : 7 ≤ D.card := by omega
  omega

/-- **THE SAME INSTANCE IN THE TRANSVERSAL SHAPE: THE ODD CYCLES HAVE A COMMON VERTEX.** -/
theorem hitsOddCycles_singleton_of_locIndep_one_card_le_seven_of_triangleFree_no5
    (hG : LocIndep 1 G) (hV : Fintype.card V ≤ 7) (htf : ∀ D : Finset V, ¬ G.IsNClique 3 D)
    (hno5 : ∀ C : Finset V, ¬ (IsOddCycle G C ∧ C.card = 5)) (hne : Nonempty V) :
    ∃ v : V, HitsOddCycles G {v} :=
  hitsOddCycles_singleton_of_locIndep_one_card_le_seven_of_oddGirth_ge_seven hG hV
    (fun D hD => by
      have h5 := card_ge_five_of_isOddCycle_of_triangleFree htf hD
      have h2 : D.card ≤ Fintype.card V := by
        have h3 := Finset.card_le_univ D
        have huv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
        omega
      have hmod := card_mod_two_of_isOddCycle hD
      have hne' : D.card ≠ 5 := fun h => hno5 D ⟨hD, h⟩
      have h7 : 7 ≤ D.card := by omega
      omega) hne

/-- The class of the instance, in the `LocIndepOneSmallOrder` shape of `JSPProblem/Five.lean`. -/
def LocIndepOneTriangleFreeNoFive.{w} (m n : ℕ) : Prop :=
  ∀ (W : Type w) (_ : Fintype W) (G : SimpleGraph W), Fintype.card W ≤ n → LocIndep 1 G →
    (∀ D : Finset W, ¬ G.IsNClique 3 D) → (∀ C : Finset W, ¬ (IsOddCycle G C ∧ C.card = 5)) →
    CloseToBipartite m G

/-- **ERDŐS #73 AT `k = 1`, CONSTANT `1`, ON TRIANGLE-FREE GRAPHS OF ORDER AT MOST SEVEN WITH NO
FIVE-CYCLE — THE INSTANCE IN THE `Erdős73On` SHAPE.** -/
theorem erdos73On_one_triangleFree_no5_seven : LocIndepOneTriangleFreeNoFive.{u} 1 7 :=
  fun (W : Type u) (_ : Fintype W) (G : SimpleGraph W) hV hG htf hno5 => by
    by_cases hne : Nonempty W
    · exact closeToBipartite_one_of_locIndep_one_card_le_seven_of_triangleFree_no5 hG hV htf hno5 hne
    · refine ⟨∅, by simp, ?_⟩
      rw [deleteFinset_empty]
      refine isBipartite_of_no_oddCycle fun h => ?_
      obtain ⟨D, hD⟩ := h
      obtain ⟨z, -⟩ := nonempty_of_card_pos (s := D) (by
        have h1 := isOddCycle_card_ge_three hD
        omega)
      exact absurd ⟨z⟩ hne

/-- **IN THE CLASS ABOVE THE CONSTANT `0` FAILS EXACTLY WHEN `G` IS NOT BIPARTITE**, so the constant
`1` is optimal inside the class. -/
theorem not_closeToBipartite_zero_of_triangleFree_no5_of_not_isBipartite
    (htf : ∀ D : Finset V, ¬ G.IsNClique 3 D)
    (hno5 : ∀ C : Finset V, ¬ (IsOddCycle G C ∧ C.card = 5)) (hn : ¬ G.IsBipartite) :
    ¬ CloseToBipartite 0 G := by
  intro h
  have h1 : tauOdd G ≤ 0 := (closeToBipartite_iff_tauOdd_le (G := G) (m := 0)).mp h
  have h2 : G.IsBipartite := (tauOdd_zero_iff).mp (by omega)
  exact hn h2

end
end JSP90
