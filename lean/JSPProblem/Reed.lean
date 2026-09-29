/-
# JSP-000090 — proved results for Erdős Problem #73

This file proves the structural facts about the two notions of `JSPProblem.Definitions`
that are currently within reach of a formalization, in particular:

* heredity and monotonicity of Erdős's local hypothesis `LocIndep k`;
* the clique obstruction `|C| ≤ k + 2` for every clique `C`, with matching sharpness examples
  (`K_{k+2}` satisfies the hypothesis, `K_{k+3}` does not);
* the **easy direction** of the theorem: every bipartite graph satisfies the hypothesis for every
  `k`, with the sharp bound `2 * |S| ≥ |X| + 1`;
* the basic API of the conclusion `CloseToBipartite m G`, including
  `CloseToBipartite 0 G ↔ G.IsBipartite`;
* monotonicity of the theorem statement itself in `k`.

The **hard direction** — that the hypothesis forces `G` to be `m`-close to bipartite — is Reed's
1999 theorem and is *not* proved here.  The exact missing statement is recorded in
`policy.json` and in `JSPProblem.lean`.
-/

import JSPProblem.Definitions

namespace JSP90

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {s t : Set V}

section Basic

/-- An independent set of `G` stays independent in a subgraph of `G`. -/
theorem IsIndepSet.mono_le {H : SimpleGraph V} {S : Finset V} (hH : H ≤ G) (hS : G.IsIndepSet S) :
    H.IsIndepSet S := by
  rw [SimpleGraph.isIndepSet_iff] at hS ⊢
  intro a ha b hb hne
  exact fun h => hS ha hb hne (hH h)

/-- An independent set stays independent when restricted to a subset of its vertices. -/
theorem IsIndepSet.subset {S T : Finset V} (hS : G.IsIndepSet S) (hT : T ⊆ S) :
    G.IsIndepSet T := by
  rw [SimpleGraph.isIndepSet_iff] at hS ⊢
  intro a ha b hb hne
  exact fun h => hS (hT ha) (hT hb) hne h

/-- **Heredity of Erdős's local hypothesis.**  A subgraph of a graph satisfying `LocIndep k`
satisfies it as well; this is what makes the condition a statement about *all* subgraphs. -/
theorem LocIndep.mono_le {k : ℕ} {H : SimpleGraph V} (hG : LocIndep k G) (hH : H ≤ G) :
    LocIndep k H := by
  intro X
  obtain ⟨S, hS, hSi, hb⟩ := hG X
  exact ⟨S, hS, IsIndepSet.mono_le hH hSi, hb⟩

/-- **Monotonicity in `k`.**  The local hypothesis `α ≥ (n - k) / 2` gets weaker as `k` grows, so
`LocIndep k` implies `LocIndep k'` for every `k' ≥ k`.  Equivalently it suffices to prove the
theorem for the *smallest* `k` in question. -/
theorem LocIndep.mono_k {k k' : ℕ} (hG : LocIndep k G) (hk : k ≤ k') : LocIndep k' G := by
  intro X
  obtain ⟨S, hS, hSi, hb⟩ := hG X
  exact ⟨S, hS, hSi, by omega⟩

/-- An independent set contained in a clique has at most one vertex. -/
theorem indep_card_le_one_of_clique {C S : Finset V} (hC : G.IsClique C) (hS : G.IsIndepSet S)
    (hsub : S ⊆ C) : S.card ≤ 1 := by
  classical
  by_contra hcon
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hne
  have hne0 : (S.erase a).Nonempty := by
    have hcard := Finset.card_erase_of_mem ha
    exact Finset.card_pos.mp (by omega)
  obtain ⟨b, hb⟩ := hne0
  obtain ⟨hne', hbS⟩ := Finset.mem_erase.mp hb
  have hne'' : a ≠ b := Ne.symm hne'
  exact absurd (hC (hsub ha) (hsub hbS) hne'') (hS ha hbS hne'')

/-- **The clique obstruction.**  Erdős's local hypothesis rules out every clique of size
`k + 3` or more: an independent set inside a clique has size at most `1`, so the hypothesis
applied to a clique of size `|C|` reads `2 * 1 + k ≥ |C|`. -/
theorem LocIndep.clique_card_le {k : ℕ} (hG : LocIndep k G) {C : Finset V} (hC : G.IsClique C) :
    C.card ≤ k + 2 := by
  obtain ⟨S, hS, hSi, hb⟩ := hG C
  have h1 : S.card ≤ 1 := indep_card_le_one_of_clique hC hSi hS
  omega

end Basic

section Bipartite

/-- A side of a bipartition is an independent set. -/
theorem IsBipartiteWith.isIndepSet_left (h : G.IsBipartiteWith s t) : G.IsIndepSet s := by
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hne
  refine fun hadj => ?_
  rcases h.2 hadj with ⟨-, hbt⟩ | ⟨hat, -⟩
  · exact (Set.disjoint_left.mp h.disjoint hb) hbt
  · exact (Set.disjoint_left.mp h.disjoint ha) hat

/-- A side of a bipartition is an independent set. -/
theorem IsBipartiteWith.isIndepSet_right (h : G.IsBipartiteWith s t) : G.IsIndepSet t :=
  IsBipartiteWith.isIndepSet_left h.symm

/-- The complement of a side of a bipartition is an independent set. -/
theorem IsBipartiteWith.isIndepSet_univ_compl (h : G.IsBipartiteWith s t) :
    G.IsIndepSet (Set.univ \ t) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hne
  refine fun hadj => ?_
  rcases h.2 hadj with ⟨-, hbt⟩ | ⟨hat, -⟩
  · exact hb.2 hbt
  · exact ha.2 hat

/-- The "split" of a bipartition: `s ∪ (univ \ t)` is independent, disjoint from `t`, and together
with `t` covers all of `V`.  This is the standard way of turning a bipartition (which need not be
onto) into a genuine two-colouring of every vertex. -/
theorem bipartition_split (bip : G.IsBipartiteWith s t) :
    G.IsIndepSet (s ∪ (Set.univ \ t : Set V))
      ∧ Disjoint (s ∪ (Set.univ \ t : Set V)) t
      ∧ (s ∪ (Set.univ \ t : Set V)) ∪ t = (Set.univ : Set V) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hne
    refine fun hadj => ?_
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact IsBipartiteWith.isIndepSet_left bip ha hb hne hadj
    · exact hb.2 (bip.mem_of_mem_adj ha hadj)
    · exact ha.2 (bip.mem_of_mem_adj hb (G.adj_symm hadj))
    · rcases bip.2 hadj with ⟨-, hbt⟩ | ⟨hat, -⟩
      · exact hb.2 hbt
      · exact ha.2 hat
  · refine Set.disjoint_left.mpr fun a ha => ?_
    rcases ha with ha | ha
    · exact fun hat => (Set.disjoint_left.mp bip.disjoint ha) hat
    · exact ha.2
  · refine Set.eq_univ_of_forall fun a => ?_
    by_cases h : a ∈ t
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨Set.mem_univ a, h⟩)

/-- The two-sided cover of a vertex set by independent sets induced by a bipartition: the
intersections of `X` with the two (completed) parts of the bipartition are independent, disjoint,
and together account for all `|X|` vertices. -/
theorem exists_indep_cover_of_isBipartiteWith (bip : G.IsBipartiteWith s t) (X : Finset V) :
    ∃ A B : Finset V,
      A ⊆ X ∧ B ⊆ X ∧ Disjoint A B ∧ A.card + B.card = X.card ∧
        G.IsIndepSet A ∧ G.IsIndepSet B := by
  classical
  obtain ⟨hind, hdis, hcover⟩ := bipartition_split bip
  set A : Finset V := X.filter (fun v => v ∈ s ∪ (Set.univ \ t : Set V)) with hAdef
  set B : Finset V := X.filter (fun v => v ∈ t) with hBdef
  have hAmem (v : V) : v ∈ A ↔ v ∈ X ∧ v ∈ s ∪ (Set.univ \ t : Set V) := by
    rw [hAdef, Finset.mem_filter]
  have hBmem (v : V) : v ∈ B ↔ v ∈ X ∧ v ∈ t := by
    rw [hBdef, Finset.mem_filter]
  have hsplit : ∀ v ∈ X, v ∈ s ∪ (Set.univ \ t : Set V) ∨ v ∈ t := by
    intro v _
    have h1 : v ∈ (s ∪ (Set.univ \ t : Set V)) ∪ t := by
      rw [hcover]
      exact Set.mem_univ v
    exact h1
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr fun a ha hb => ?_
    rcases (hAmem a).mp ha with ⟨haX, haA⟩
    rcases (hBmem a).mp hb with ⟨_, hbB⟩
    exact (Set.disjoint_left.mp hdis haA) hbB
  have hunion : A ∪ B = X := by
    ext v
    simp only [hAmem v, hBmem v, Finset.mem_union]
    constructor
    · intro h
      rcases h with h | h
      · exact h.1
      · exact h.1
    · intro h
      by_cases hA : v ∈ s ∪ (Set.univ \ t : Set V)
      · exact Or.inl ⟨h, hA⟩
      · rcases hsplit v h with h' | h'
        · exact absurd h' hA
        · exact Or.inr ⟨h, h'⟩
  have hAi : G.IsIndepSet A := by
    rw [SimpleGraph.isIndepSet_iff] at hind ⊢
    intro v hv w hw hne hadj
    exact hind ((hAmem v).mp hv).2 ((hAmem w).mp hw).2 hne hadj
  have hBi : G.IsIndepSet B := by
    rw [SimpleGraph.isIndepSet_iff] at ⊢
    intro v hv w hw hne hadj
    exact IsBipartiteWith.isIndepSet_right bip ((hBmem v).mp hv).2
      ((hBmem w).mp hw).2 hne hadj
  refine ⟨A, B, ?_, ?_, hAB, ?_, hAi, hBi⟩
  · rw [hAdef]; exact Finset.filter_subset _ _
  · rw [hBdef]; exact Finset.filter_subset _ _
  · rw [← Finset.card_union_of_disjoint hAB, hunion]

/-- **The easy direction of Erdős Problem #73.**
A bipartite graph satisfies Erdős's local hypothesis for *every* `k`: the larger of the two parts
of the induced subgraph on `X` is an independent set of size at least `⌈|X| / 2⌉ ≥ |X| / 2`. -/
theorem isBipartite_locIndep {k : ℕ} (h : G.IsBipartite) : LocIndep k G := by
  obtain ⟨s, t, bip⟩ := h.exists_isBipartiteWith
  intro X
  obtain ⟨A, B, hAX, hBX, _, hcard, hAi, hBi⟩ := exists_indep_cover_of_isBipartiteWith bip X
  by_cases hle : 2 * A.card ≥ 2 * B.card
  · refine ⟨A, hAX, hAi, by omega⟩
  · refine ⟨B, hBX, hBi, by omega⟩

/-- The quantitative form of the witness used above: a bipartite graph has an independent set
inside every vertex set `X` whose size is at least `|X| / 2` — this is exactly the bound
`LocIndep k` asks for, and it is the largest one that holds for all `X`. -/
theorem isBipartite_indepSet_card_half (h : G.IsBipartite) (X : Finset V) :
    ∃ S : Finset V, S ⊆ X ∧ G.IsIndepSet S ∧ X.card ≤ 2 * S.card := by
  obtain ⟨s, t, bip⟩ := h.exists_isBipartiteWith
  obtain ⟨A, B, hAX, hBX, _, hcard, hAi, hBi⟩ := exists_indep_cover_of_isBipartiteWith bip X
  by_cases hle : 2 * A.card ≥ 2 * B.card
  · refine ⟨A, hAX, hAi, by omega⟩
  · refine ⟨B, hBX, hBi, by omega⟩

end Bipartite

section Conclusion

/-- Enlarging one side of a bipartition by the vertices outside the other side turns it into a
bipartition of the whole vertex set. -/
theorem isBipartiteWith_univ (bip : G.IsBipartiteWith s t)
    (hdis : Disjoint (s ∪ (Set.univ \ t : Set V)) t) :
    G.IsBipartiteWith (s ∪ (Set.univ \ t : Set V)) t := by
  refine { disjoint := hdis, mem_of_adj := ?_ }
  intro v w hadj
  rcases bip.2 hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨Or.inl h1, h2⟩
  · exact Or.inr ⟨h1, Or.inl h2⟩

/-- **A bipartite graph needs no modifications at all.** -/
theorem isBipartite_closeToBipartite {m : ℕ} (h : G.IsBipartite) : CloseToBipartite m G := by
  refine ⟨∅, Nat.zero_le _, ?_⟩
  rw [deleteFinset_empty]
  exact h

/-- **Monotonicity of the conclusion**: "close to bipartite after `m` modifications" is monotone
in `m`. -/
theorem CloseToBipartite.mono {m m' : ℕ} (h : CloseToBipartite m G) (hm : m ≤ m') :
    CloseToBipartite m' G := by
  obtain ⟨X, hX, hb⟩ := h
  exact ⟨X, le_trans hX hm, hb⟩

/-- **No modifications at all means bipartite.** -/
theorem closeToBipartite_zero_iff : CloseToBipartite 0 G ↔ G.IsBipartite := by
  constructor
  · rintro ⟨X, hX, hb⟩
    have hX0 : X = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hX)
    have : deleteFinset G X = G := by
      rw [hX0, deleteFinset_empty]
    rw [this] at hb
    exact hb
  · exact isBipartite_closeToBipartite (m := 0)

/-- **Monotonicity of the theorem.**  The local hypothesis weakens as `k` grows, so proving
`Erdős73 k` for a given `k` proves it for every `k' ≥ k`, and the same witness `m` works. -/
theorem Erdős73.mono.{u} {k k' : ℕ} (hk : k ≤ k') (h : Erdős73.{u} k') : Erdős73.{u} k := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, fun W instW G hG => hm W instW G (hG.mono_k hk)⟩

end Conclusion

section Sharpness

/-- A singleton is an independent set of a loopless graph. -/
private theorem isIndepSet_singleton (a : V) (G : SimpleGraph V) : G.IsIndepSet ({a} : Finset V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro x hx y hy hne
  have hxa : x = a := by simpa using hx
  have hya : y = a := by simpa using hy
  exact fun hadj => hne (hxa.trans hya.symm)

/-- **The local bound `k` is exactly tight: `K_{k+2}` satisfies `LocIndep k`.**
The largest independent set of a complete graph has size `1`, and the hypothesis for `K_{k+2}`
reads `2 * 1 + k = k + 2 ≥ k + 2`. -/
theorem completeGraph_locIndep (k : ℕ) :
    LocIndep k (SimpleGraph.completeGraph (Fin (k + 2))) := by
  classical
  intro X
  have hXle : X.card ≤ k + 2 := by
    refine le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
  by_cases hX : X = ∅
  · have hcard0 : X.card = 0 := by rw [hX, Finset.card_empty]
    refine ⟨∅, Finset.empty_subset X, ?_, by omega⟩
    rw [SimpleGraph.isIndepSet_iff]
    intro x hx
    exact fun y hy => absurd hx (by simp)
  · have hne0 : X.card ≠ 0 := fun h => hX (Finset.card_eq_zero.mp h)
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.pos_iff_ne_zero.mpr hne0)
    refine ⟨{a}, Finset.singleton_subset_iff.mpr ha, isIndepSet_singleton a _, ?_⟩
    have hcard1 : ({a} : Finset _).card = 1 := Finset.card_singleton a
    omega

/-- **One clique larger already breaks the hypothesis: `K_{k+3}` does not satisfy `LocIndep k`.**
This matches the bound `|C| ≤ k + 2` of `LocIndep.clique_card_le`. -/
theorem not_completeGraph_locIndep (k : ℕ) :
    ¬ LocIndep k (SimpleGraph.completeGraph (Fin (k + 3))) := by
  classical
  intro h
  have hcl : (SimpleGraph.completeGraph (Fin (k + 3)) : SimpleGraph (Fin (k + 3))).IsClique
      (Finset.univ : Finset (Fin (k + 3))) := by
    rw [SimpleGraph.isClique_iff]
    intro x _ y _ hne
    show (⊤ : SimpleGraph (Fin (k + 3))).Adj x y
    exact (SimpleGraph.top_adj x y).mpr hne
  have hle := h.clique_card_le hcl
  rw [Finset.card_univ, Fintype.card_fin] at hle
  omega

end Sharpness

end JSP90
