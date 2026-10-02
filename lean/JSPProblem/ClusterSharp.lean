/-
# JSP-000090 — the cluster-graph instance of round 104, with its **sharpness certificate**

`JSPProblem/Cluster.lean` proved a new instance of the headline theorem:

* `erdos73On_of_cluster` — if `G` is a disjoint union of complete graphs (`ClusterDecomposition
  G 𝒬`) and `G` satisfies Erdős's hypothesis `LocIndep k`, then `G` is the union of a bipartite
  graph and at most `k` vertices.

That instance is only useful if its constant is known to be right, so this file attaches the
**same witness that rounds 47–54 used for the lower bound** — the disjoint union of `k` triangles
`kTriangles k` of `JSPProblem/Sharp.lean` — to the new class, and checks that

* `kTriangles k` *is* a cluster graph: its fibres are a `ClusterDecomposition`
  (`cluster_kTriangles`), so the new instance applies to it;
* the deficiency of `kTriangles k` is exactly `k` (`maxDef_kTriangles_eq`, from the cluster
  formula `maxDef_cluster` and `card_tri`), which also *recovers* the value computed by the
  transversal route of round 47 (`closeToBipartite_iff_hitsOddCycles`);
* the implication of the new instance is an **equivalence** on this witness, with `k` exactly:
  `erdos73On_of_cluster_optimal` — `(LocIndep k (kTriangles k) → CloseToBipartite m (kTriangles k))
  ↔ k ≤ m` — and no smaller constant works (`erdos73_cluster_notBelowK`).

Two remarks about the development, both worth recording:

* the class of this file, *disjoint unions of complete graphs*, is **strictly larger** than the
  class of `JSPProblem/DegColour.lean` (disjoint unions of odd cycles): `K_5 ⊔ K_5` is a cluster
  graph which is not a disjoint union of odd cycles (`not_oddCyclesDisjoint_completeGraph_five`
  in `JSPProblem/DegColour.lean`).  So the new instance is a genuine extension, not a repackaging;
* `LocIndep k (kTriangles k)` holds **with equality** (`locIndep_kTriangles` and
  `not_locIndep_kTriangles` in `JSPProblem/Sharp.lean`), so the new instance is attained at every
  `k`.

This file deliberately declares **no local `DecidableEq` instance**: all vertex types here are
concrete (`Fin 3 × Fin k`, whose `DecidableEq` is the computable instance), and a file that mixes a
local `Classical.decEq` with concrete statements runs into instance mismatches elsewhere in this
development.  That is why `JSPProblem/Cluster.lean`, which does declare such an instance, keeps
concrete vertex types out of its statements.

The headline theorem `jsp_000090_main` (`Erdős73` for every `k`) is still out of reach: it needs the
constant `k` for **arbitrary** graphs, and nothing here removes that restriction.  What this file
adds is a complete, sharp instance on a class on which hypothesis and conclusion coincide.
-/
import JSPProblem.Cluster
import JSPProblem.Sharp

namespace JSP90

/-! ## 1. The family of fibres of `kTriangles k` -/

/-- **The fibres of `kTriangles k`**: the `k` triangles `tri i`, `i < k`. -/
noncomputable def fibreFamily (k : ℕ) : Finset (Finset (Fin 3 × Fin k)) :=
  (Finset.univ : Finset (Fin k)).image (fun i => tri i)

theorem mem_fibreFamily {k : ℕ} {C : Finset (Fin 3 × Fin k)} :
    C ∈ fibreFamily k ↔ ∃ i : Fin k, C = tri i := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem mem_fibreFamily_of_mem_tri {k : ℕ} {i : Fin k} : tri i ∈ fibreFamily k :=
  mem_fibreFamily.mpr ⟨i, rfl⟩

/-- Distinct fibres are distinct triangles. -/
theorem fibreFamily_inj {k : ℕ} {i j : Fin k} (h : tri i = tri j) : i = j := by
  have h1 : (0, i) ∈ tri j := by rw [← h]; exact mem_tri.mpr rfl
  exact (show (0, i).2 = i from rfl).symm.trans (mem_tri.mp h1)

theorem fibreFamily_injective {k : ℕ} : Function.Injective (fun i : Fin k => tri i) := by
  intro i j h
  exact fibreFamily_inj h

theorem card_fibreFamily (k : ℕ) : (fibreFamily k).card = k := by
  rw [fibreFamily, Finset.card_image_of_injective (Finset.univ : Finset (Fin k))
    (fibreFamily_injective (k := k))]
  simp

/-! ## 2. `kTriangles k` is a cluster graph -/

/-- **Two adjacent vertices lie in the same fibre**: the `Adj` clause of `kTriangles` compares the
second coordinate, so adjacency forces the fibres to agree.  This is what makes distinct fibres
anticomplete. -/
theorem eq_fibre_of_adj {k : ℕ} {i j : Fin k} {p q : Fin 3 × Fin k} (hi : p ∈ tri i)
    (hj : q ∈ tri j) (h : (kTriangles k).Adj p q) : i = j := by
  have h2 := (kTriangles_adj).mp h
  exact (mem_tri.mp hi).symm.trans (h2.1.trans (mem_tri.mp hj))

/-- **The fibres of `kTriangles k` are pairwise disjoint and pairwise anticomplete.** -/
theorem anticover_fibreFamily (k : ℕ) :
    AnticoverCoverFamily (kTriangles k) (fibreFamily k) := by
  refine ⟨?_, ?_⟩
  · rintro X hX Y hY hne
    obtain ⟨i, rfl⟩ := mem_fibreFamily.mp hX
    obtain ⟨j, rfl⟩ := mem_fibreFamily.mp hY
    have hij : i ≠ j := fun h => hne (by rw [h])
    simp only [← Finset.disjoint_iff_inter_eq_empty]
    exact tri_disjoint hij
  · rintro X hX Y hY hne p hp q hq h'
    obtain ⟨i, rfl⟩ := mem_fibreFamily.mp hX
    obtain ⟨j, rfl⟩ := mem_fibreFamily.mp hY
    have hij : i ≠ j := fun h => hne (by rw [h])
    exact hij (eq_fibre_of_adj hp hq h')

/-- **`kTriangles k` is a cluster graph**: its fibre family is a `ClusterDecomposition`.  The three
components of the hypothesis are `anticover_fibreFamily`, `card_tri` (each fibre is a triangle, so
has three vertices), the fact that a triangle is a clique, and the fact that the fibres cover. -/
theorem cluster_kTriangles (k : ℕ) :
    ClusterDecomposition (kTriangles k) (fibreFamily k) := by
  refine ⟨anticover_fibreFamily k, ?_, ?_, ?_⟩
  · rintro X hX
    obtain ⟨i, rfl⟩ := mem_fibreFamily.mp hX
    rw [card_tri]
    omega
  · rintro X hX p q hp hq hne
    obtain ⟨i, rfl⟩ := mem_fibreFamily.mp hX
    have hpf : p.2 = i := mem_tri.mp hp
    have hqf : q.2 = i := mem_tri.mp hq
    have hp1 : p.1 ≠ q.1 := fun h1 => hne (Prod.ext_iff.mpr (And.intro h1 (by rw [hpf, hqf])))
    exact (kTriangles_adj).mpr ⟨hpf.trans hqf.symm, hp1⟩
  · intro p
    exact ⟨tri p.2, mem_fibreFamily_of_mem_tri, mem_tri.mpr rfl⟩

/-! ## 3. The deficiency of the witness is exactly `k`, computed by the cluster formula -/

theorem sum_cost_fibreFamily (k : ℕ) :
    (∑ C ∈ fibreFamily k, (C.card - 2)) = k := by
  have hinjOn : Set.InjOn (fun i : Fin k => tri i)
      ((Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
    rw [Finset.coe_univ]
    exact (Set.injOn_univ).mpr (fibreFamily_injective (k := k))
  calc (∑ C ∈ fibreFamily k, (C.card - 2))
      = ∑ i ∈ (Finset.univ : Finset (Fin k)), ((tri i).card - 2) := by
        rw [fibreFamily, Finset.sum_image hinjOn]
    _ = ∑ _i ∈ (Finset.univ : Finset (Fin k)), (3 - 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [card_tri]
    _ = k := by simp

/-- **`MaxDef (kTriangles k) = k`**, computed by the cluster formula of `JSPProblem/Cluster.lean`:
each of the `k` fibres contributes `3 - 2 = 1`. -/
theorem maxDef_kTriangles_cluster (k : ℕ) :
    MaxDef (kTriangles k) = ∑ C ∈ fibreFamily k, (C.card - 2) :=
  maxDef_cluster (cluster_kTriangles k)

theorem maxDef_kTriangles_eq (k : ℕ) : MaxDef (kTriangles k) = k := by
  rw [maxDef_kTriangles_cluster, sum_cost_fibreFamily]

/-- The value `MaxDef (kTriangles k) = k` is the one the transversal route of round 47 computes:
`maxDef_eq_iff` turns the odd-cycle-transversal formula into the same equation. -/
theorem maxDef_kTriangles_transversal (k : ℕ) (D : Finset (Fin 3 × Fin k))
    (hD : D.card = MaxDef (kTriangles k)) (_hDhit : HitsOddCycles (kTriangles k) D) :
    D.card = k := by
  rw [hD, maxDef_kTriangles_eq]

/-- **The exact value of the conclusion of Erdős #73 on `kTriangles k`**, now with the cluster
formulation: `kTriangles k` is `m`-close to bipartite **iff** `k ≤ m`. -/
theorem closeToBipartite_iff_cluster_cost_kTriangles (k m : ℕ) :
    CloseToBipartite m (kTriangles k) ↔ (∑ C ∈ fibreFamily k, (C.card - 2)) ≤ m :=
  closeToBipartite_iff_cluster_cost (cluster_kTriangles k)

/-! ## 4. The new instance, attained and optimal -/

/-- **The new instance of the headline theorem, on the witness of the lower bound**: `kTriangles k`
satisfies Erdős's hypothesis with parameter `k`, and is the union of a bipartite graph and at most
`k` vertices. -/
theorem erdos73On_cluster_kTriangles (k : ℕ) : CloseToBipartite k (kTriangles k) :=
  erdos73On_of_cluster (cluster_kTriangles k) (locIndep_kTriangles (k := k))

/-- **The new instance is an equivalence with the optimal constant**: for every `m`, the
implication `LocIndep k (kTriangles k) → CloseToBipartite m (kTriangles k)` holds **iff** `k ≤ m`.
So on the class of disjoint unions of complete graphs the whole content of Erdős #73 is the
comparison `k ≤ m`, and the constant `f(k) = k` of `erdos73On_of_cluster` is attained. -/
theorem erdos73On_of_cluster_optimal (k m : ℕ) :
    (LocIndep k (kTriangles k) → CloseToBipartite m (kTriangles k)) ↔ k ≤ m := by
  constructor
  · intro h
    have h1 : MaxDef (kTriangles k) ≤ m :=
      maxDef_le_closeToBipartite (h (locIndep_kTriangles (k := k)))
    exact le_trans (le_of_eq (maxDef_kTriangles_eq (k := k)).symm) h1
  · intro hkm _
    refine (closeToBipartite_iff_maxDef_cluster (cluster_kTriangles k)).mpr ?_
    have h1 : MaxDef (kTriangles k) ≤ m := by
      rw [maxDef_kTriangles_eq]
      exact hkm
    exact h1

/-- **No constant below `k` works even on the class of cluster graphs.**  For every `k` and every
`m < k` there is a disjoint union of complete graphs — `kTriangles k` — satisfying Erdős's
hypothesis with parameter `k` which is not the union of a bipartite graph and `m` vertices.  This
is `erdos73_lower_bound` re-proved *through* the new instance, so the new instance is sharp. -/
theorem erdos73_cluster_notBelowK (k m : ℕ) (h : m < k) :
    LocIndep k (kTriangles k) ∧ ¬ CloseToBipartite m (kTriangles k) :=
  ⟨locIndep_kTriangles (k := k), not_closeToBipartite_kTriangles h⟩

/-- The lower bound of Erdős #73 restricted to the hypothesis `LocIndep k` **and** the class of
disjoint unions of complete graphs: for every `m < k` there is such a graph which is not `m`-close
to bipartite.  Equivalently, on that class `f(k) = k`. -/
theorem cluster_lower_bound (k m : ℕ) (h : m < k) :
    ¬ (∀ (G : SimpleGraph (Fin 3 × Fin k)) (𝒬 : Finset (Finset (Fin 3 × Fin k))),
      ClusterDecomposition G 𝒬 → LocIndep k G → CloseToBipartite m G) := by
  rintro hall
  exact not_closeToBipartite_kTriangles h (hall _ _ (cluster_kTriangles k)
    (locIndep_kTriangles (k := k)))

/-- A one-line corollary: on the class of cluster graphs the maximum deficiency is exactly the
`k` of Erdős's hypothesis, and the graph is `m`-close to bipartite exactly when `k ≤ m`. -/
theorem cluster_defect_equals_budget (k m : ℕ) :
    CloseToBipartite m (kTriangles k) ↔ MaxDef (kTriangles k) ≤ m :=
  closeToBipartite_iff_maxDef_cluster (cluster_kTriangles k)

end JSP90